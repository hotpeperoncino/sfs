#ifndef _VARINFO_H
#define _VARINFO_H

#include "../common/common.h"
#include "../common/cg.h"
#include "../common/data.h"
#include "../common/extinfo.h"

extern ExtInfo *ext;

// variable information class used to translate Value* to u32 and to
// distinguish between strong and weak variables
//
class VarInfo
{
public:

#define I2P    (Value*)1            // IntToPtr value
#define FIELD  (Value*)2            // struct field
#define ART(v) (v && v < (Value*)3) // artificial value?

#define REP(x) (pe[x] < 0)       // pointer equivalence set rep
#define RNK(x) ((u32)-1 - pe[x]) // pointer equivalence set rank
  
   VarInfo() {}
  ~VarInfo() {}
  
  // translate all the Value*'s to u32's and mark weak variables
  //
  void translate(Module&,CG&);

  // union the two top-level variable arguments; uses union-by-rank
  //
  u32 unite(u32,u32);

  // return the top-level variable corresponding to the Value*
  //
  u32 operator[](Value *v) { u32 r = top[strip(v)]; assert(r); return find(r); }

  // same as operator[] except returns 0 if there is no translation
  //
  u32 getTrans(Value *v)
  {
    v2u_it i = top.find(strip(v));
    return (i == top.end()) ? 0 : find(i->second);
  }

  // return the set rep of variable i
  //
  u32 operator[](u32 i) { return find(i); }

  // return the bottom-level variable corresponding to the Value*
  //
  u32 operator()(Value *v) { u32 r = btm[strip(v)]; assert(r); return r; }

  // return the Value* corresponding to the u32
  //
  Value* inverse(u32 v) { assert(v && v < inv.size()); return inv[v]; }

  // true iff v is weak
  //
  bool weakp(u32 v) { return weak.count(v); }

  vector<u32>& structOffsets(const StructType* t)
  {
    if (!struct_off.count(t)) { //OPT: kludge to compute struct_off[t]
      vector<u32> info;
      processStructType(t,info,false);
    }

    return struct_off[t];
  }

  // return the number of fields associated with struct v (0 if v is
  // not a struct or is a struct with a single field)
  //
  u32 numf(u32 v)
  {
    u2u_it i = nsf.find(v);
    return (i == nsf.end()) ? 0 : i->second;
  }

  // given the set of struct offsets used by the program fill in vso
  // s.t. each offset is mapped to the set of variables that contain
  // at least that number of fields (note: this must be called before
  // varf is used)
  //
  void set_vso(bitmap&);

  // for a given offset return the set of variables that contain at
  // least that many fields
  //
  bitmap& varf(u32 off) { return vso[off]; }

  // true iff v has at least o fields
  //
  bool varfp(u32 o, u32 v) { return vso[o].test(v); }

  // external variables that need to be initialized (main's argv and
  // envp, any has_static2 vars)
  //
  set<Value*> ext_vars;

  // constant GEP expressions that need to be initialized once the
  // globals themselves have been initialized
  //
  set<ConstantExpr*> const_exps;

  // print top and btm translations (*'d if weak) -- remember that
  // struct fields aren't recorded in btm, so they aren't printed
  //
  void print();

  // print out PE stats
  //
  void stats();

  // strip off any ConstantExpr's off of the given value (except for
  // constant GEPs)
  //
  static Value* strip(Value*);

  map<Value*,u32> pp;  // program points (for metrics)
  map<u32,u32> reason; // reaons for weakness (for precision analysis)

private:

  //// DATA STRUCTURES

  set<u32> weak;            // weak variables
  map<u32,u32> nsf;         // number of struct fields for each struct
  vector<Value*> inv;       // u32 -> Value* inverse mapping
  map<Value*,u32> top, btm; // top-level, addr-taken Value* -> u32 mapping
  map<string,u32> has_stat; // external call name -> idx

  vector<int> pe; // pointer equivalence union-find graph

  // information about struct types: the size of the vector is the
  // number of fields and each bool is true iff the corresponding
  // field is always weak
  //
  // largest_struct is the largest struct type (for use when
  // processing dynamic allocations)
  //
  map<const Type*,vector<u32> > struct_info;
  const Type* largest_struct;

  // information about struct indices: the offset for each field in
  // terms of the number of fields from the beginning of the struct
  //
  map<const Type*,vector<u32> > struct_off;

  // for each possible offset > 0 record the set of variables that
  // have at least that number of fields
  //
  map<u32,bitmap> vso;

  //// METHODS

  u32 find(u32);
  void processStructs(Module&);
  u32 processStructType(const StructType*,vector<u32>&,bool);
  const Type* findPossibleType(Instruction*);

#if PRECIS == 0
#define PREC4(a,b,c,d)
#else
#define PREC4(idx,wk_heap,wk_rec,wk_array) {                     \
    if (wk_heap)  { reason[idx] |= HEAP; }                       \
    if (wk_rec)   { reason[idx] |= REC; }                        \
    if (wk_array) { reason[idx] |= ARRAY; }}
#endif
};

//// PUBLIC METHODS

void VarInfo::translate(Module &M, CG &cg)
{
  u32 s, idx = 1;    // variable index generator
  processStructs(M); // fill in struct_info

  // translate global variables (all globals in LLVM are pointers)
  //
  for (glob_it i = M.global_begin(), e = M.global_end(); i != e; ++i) {
    top[i] = idx; idx++; // the top-level global pointer

    // what type does this global point to?
    //
    const Type *typ = i->getType()->getContainedType(0);

    // we treat arrays of structs as a single struct with weak fields
    // (since we ignore array offsets during the analysis)
    //
    bool array = isa<ArrayType>(*typ);
    if (array) { typ = cast<ArrayType>(typ)->getElementType(); }

    // the memory location pointed to by the global (the first field
    // if this is a struct)
    //
    u32 start_idx = idx; 

    // for structs we need to assign indices to all fields of the
    // struct; only the very first field of a struct is mapped to by
    // btm[] (which is taken care of after the following if/else)
    //
    if (isa<StructType>(*typ)) { // struct or array of structs
      if (!struct_info.count(typ)) { // unnamed struct type
	vector<u32>& info = struct_info[typ];
	processStructType(cast<StructType>(typ),info,false);
      }
      
      vector<u32>& info = struct_info[typ];
      if ((s = info.size()) > 1) { nsf[start_idx] = s; }
      
      for (uv_it j = info.begin(), e = info.end(); j != e; ++j) {
	if ((s = (*j >> 16)) && idx != start_idx) { nsf[idx] = s; }
	if (array || (*j & 0xffff)) {
	  PREC4(idx,false,false,true);
	  weak.insert(idx);
	}
	idx++;
      }

      // look for and process constant GEP expressions that use this
      // global struct pointer: we need to assign them top-level
      // indices just like a top-level variable
      //
      for (use_it j = i->use_begin(), e = i->use_end(); j != e; ++j) {
	if (ConstantExpr *C = dyn_cast<ConstantExpr>(*j)) {
	  switch (C->getOpcode()) {
	  case Instruction::GetElementPtr:
	    assert(!top.count(C));
	    top[C] = idx; idx++;
	    const_exps.insert(C);
	    break;
	  case Instruction::BitCast:
	    for (use_it k = C->use_begin(), e = C->use_end(); k != e; ++k) {
	      if (ConstantExpr *C2 = dyn_cast<ConstantExpr>(*k)) {
		if (C2->getOpcode() == Instruction::GetElementPtr) {
		  assert(!top.count(C2));
		  top[C2] = idx; idx++;
		  const_exps.insert(C2);
		}
	      }
	    }
	    break;
	  default: break;
	  }
	}
      }
    }
    else { // not a struct or array of structs
      if (array) { // still need to look for constant GEP expressions
	for (use_it j = i->use_begin(), e = i->use_end(); j != e; ++j) {
	  if (ConstantExpr *C = dyn_cast<ConstantExpr>(*j)) {
	    switch (C->getOpcode()) {
	    case Instruction::GetElementPtr:
	      assert(!top.count(C));
	      top[C] = idx; idx++;
	      const_exps.insert(C);
	      break;
	    case Instruction::BitCast:
	      for (use_it k = C->use_begin(), e = C->use_end(); k != e; ++k) {
		if (ConstantExpr *C2 = dyn_cast<ConstantExpr>(*k)) {
		  if (C2->getOpcode() == Instruction::GetElementPtr) {
		    assert(!top.count(C2));
		    top[C2] = idx; idx++;
		    const_exps.insert(C2);
		  }
		}
	      }
	      break;
	    default: break;
	    }
	  }
	}
      }
      
      idx++;
    } 

    btm[i] = start_idx; // the memory location pointed to by the global
    if (array) {
      PREC4(start_idx,false,false,true);
      weak.insert(start_idx);
    }
  }

  // translate functions and function parameters
  //
  for (fmod_it i = M.begin(), e = M.end(); i != e; ++i) {
    //
    // we only need to translate global function pointers for
    // functions whose address is taken (including external functions)
    //
    if (cg.adrp(i)) {
      top[i] = idx; idx++;
      btm[i] = idx; idx++;
    }
    
    // we don't need to translate external or preserving functions
    //
    if (ext->is_ext(i)) { continue; }
    if (cg[&*i]->psv) { continue; }

    // translate this function's parameters; we treat main specially
    // because its parameters' values are coming from outside the
    // program
    //
    if (i->getNameStr() == "main") {
      //
      // main's pointer-valued parameters (argv and envp) each
      // need two bottom values since they are double pointers
      // (note: second bottom value not mapped in btm[])
      //
      prm_it pi = i->arg_begin(), pe = i->arg_end();
      u32 prm_num = 0; // the 0th parameter would be argc

      while (pi != pe) {
	if (prm_num == 1) { // ARGV
	  top[pi] = idx; idx++;
	  ext_vars.insert(pi);

	  nsf[idx] = 2;
	  btm[pi] = idx; idx++; idx++;
	}
	else if (prm_num == 2) { // ENVP	  
	  top[pi] = idx; idx++;
	  ext_vars.insert(pi);

	  nsf[idx] = 2;
	  btm[pi] = idx; idx++; idx++;
	}

	++prm_num; ++pi;
      }
    }
    else { // function isn't main
      for (prm_it pi = i->arg_begin(), pe = i->arg_end(); pi != pe; ++pi) {
	if (isa<PointerType>(pi->getType())) { top[pi] = idx; idx++; }
      }
    }

    // translate all pointer-related instructions in this function
    //
    for (inst_iterator j = inst_begin(i), e = inst_end(i); j != e; ++j) {
      if (isa<PointerType>(j->getType())) {
        //
        // an instruction with pointer type; note that we don't care
        // about CallInst, ReturnInst, and StoreInst that manipulate
        // pointers because the appropriate Value*'s will be
        // translated elsewhere
        //
	top[&*j] = idx; idx++;
	bool wk_rec = cg[&*i]->rec;

	// allocations require indices for the returned memory locations
	//
	if (AllocationInst *a = dyn_cast<AllocationInst>(&*j)) {
	  bool wk_heap = isa<MallocInst>(a);
          bool wk_array = false;

	  const Type *typ = a->getAllocatedType();

	  // for malloc try to figure out what type it will be cast to
          //
          if (isa<MallocInst>(a)) { typ = findPossibleType(&*j); }
	  
	  // we treat an array of structs as a single struct with weak
	  // fields, since we ignore array offsets during the analysis
	  //
	  if (isa<ArrayType>(*typ)) {
	    wk_array = true;
	    typ = cast<ArrayType>(typ)->getElementType();
	  }

	  // the memory location pointed to by the pointer (the first
	  // field if this is a struct)
	  //
	  u32 start_idx = idx;

	  if (isa<StructType>(*typ)) { // struct or array of structs
	    if (!struct_info.count(typ)) { // unnamed struct type
	      vector<u32>& info = struct_info[typ];
	      processStructType(cast<StructType>(typ),info,false);
	    }

	    vector<u32>& info = struct_info[typ];	    
	    if ((s = info.size()) > 1) { nsf[start_idx] = s; }

	    for (uv_it k = info.begin(), e = info.end(); k != e; ++k) {
	      if ((s = (*k >> 16)) && idx != start_idx) { nsf[idx] = s; }
	      if (wk_heap || wk_rec || wk_array || (*k & 0xffff)) {
		PREC4(idx,wk_heap,wk_rec,(wk_array||(*k&0xffff)));
		weak.insert(idx);
	      }
	      idx++;
	    }
	  }
	  else { idx++; }

	  btm[&*j] = start_idx;

          if (wk_heap || wk_rec || wk_array) {
            PREC4(start_idx,wk_heap,wk_rec,wk_array);
            weak.insert(start_idx);
          }
	}
	else if (CallInst *ci = dyn_cast<CallInst>(&*j)) {
          Function *c = calledFunction(ci);
          if (!c) {
	    // an indirect call could call an is_alloc() external
	    // function so we need to create indices just in case
	    //
	    const Type *typ = findPossibleType(&*j);
	    
	    bool wk_array = isa<ArrayType>(*typ);
	    if (wk_array) { typ = cast<ArrayType>(typ)->getElementType(); }

	    btm[&*j] = idx;
	    
	    if (isa<StructType>(*typ)) {
	      if (!struct_info.count(typ)) { // unnamed struct type
		vector<u32>& info = struct_info[typ];
		processStructType(cast<StructType>(typ),info,false);
	      }
	      
	      vector<u32>& info = struct_info[typ];
	      if ((s = info.size()) > 1) { nsf[idx] = s; }
	      
	      u32 si = idx;
	      
	      for (uv_it k = info.begin(), e = info.end(); k != e; ++k) {
		if ((s = (*k >> 16)) && idx != si) { nsf[idx] = s; }
		PREC4(idx,true,wk_rec,(wk_array||(*k&0xffff)));
		weak.insert(idx); idx++;
	      }
	    }
	    else {
	      PREC4(idx,true,wk_rec,wk_array);
	      weak.insert(idx); idx++;
	    }
	    
	    continue;
	  }

          // we need to translate Value*'s for any external functions
          // that act like allocations or have internal static vars
          //
          if (ext->is_ext(c)) {
            if (ext->is_alloc(c) || ext->get_type(c) == EFT_REALLOC) { 
	      // allocation function

	      if (ext->no_struct_alloc(c)) {
		btm[&*j] = idx;
		weak.insert(idx);
		PREC4(idx,true,wk_rec,isa<ArrayType>(findPossibleType(&*j)));
		idx++;
	      }
	      else { // just like the alloc inst above, except always weak
		const Type *typ = findPossibleType(&*j);

		bool wk_array = isa<ArrayType>(*typ);
		if (wk_array) { typ = cast<ArrayType>(typ)->getElementType(); }

		btm[&*j] = idx;

		if (isa<StructType>(*typ)) {
		  if (!struct_info.count(typ)) { // unnamed struct type
		    vector<u32>& info = struct_info[typ];
		    processStructType(cast<StructType>(typ),info,false);
		  }

		  vector<u32>& info = struct_info[typ];
		  if ((s = info.size()) > 1) { nsf[idx] = s; }

		  u32 si = idx;

		  for (uv_it k = info.begin(), e = info.end(); k != e; ++k) {
		    if ((s = (*k >> 16)) && idx != si) { nsf[idx] = s; }
		    PREC4(idx,true,wk_rec,(wk_array||(*k&0xffff)));
		    weak.insert(idx); idx++;
		  }
		}
	      }
            }
            else if (ext->has_static(c)) { // function returning statics
	      if (has_stat.count(c->getNameStr())) {
                btm[&*j] = has_stat[c->getNameStr()];
              }
              else {
		u32 start_idx = idx;

		// some external calls access two static variables,
		// with one pointing to the other; others return
		// struct pointers for which we need to allocate
		// memory location indices
		//
		if (isa<StructType>(j->getType()->getContainedType(0))) {
		  const Type *t = j->getType()->getContainedType(0);

		  if (!struct_info.count(t)) { // unnamed struct type
		    vector<u32>& info = struct_info[t];
		    processStructType(cast<StructType>(t),info,false);
		  }

		  vector<u32>& info = struct_info[t];	    
		  if ((s = info.size()) > 1) { nsf[start_idx] = s; }

		  for (uv_it k = info.begin(), e = info.end(); k != e; ++k) {
		    if ((s = (*k >> 16)) && idx != start_idx) { nsf[idx] = s; }
		    if (*k & 0xffff) {
		      PREC4(idx,false,false,true);
		      weak.insert(idx);
		    }
		    idx++;
		  }
		}
		else { 
		  idx++;
		  if (ext->has_static2(c)) {
		    idx++;
		    nsf[start_idx] = 2;
		    ext_vars.insert(&*j);
		  }
		}
		
		btm[&*j] = start_idx;
		has_stat[c->getNameStr()] = start_idx;
              }
	    }
          }
	}
      }
    }
  }

  // insert value for IntToPtr
  //
  top[I2P] = idx; idx++;
  btm[I2P] = idx; idx++;

  weak.insert(idx-1);
  PREC4((idx-1),true,false,false);

  // clean up unnecessary data
  //
  has_stat.clear();
  struct_info.clear();
  
  //
  // compress the btm values together to increase the efficiency of
  // SparseBitVectors and BDDs; fill in inverse[]
  //

  set<u32> wk;
  u2u_it j, k;
  u32 curr = 1;
  map<u32,u32> redir, nsf2;
  map<Value*,u32> top2, btm2;

  inv.push_back((Value*)0); // 0 index reserved to detect errors

  for (v2u_it i = btm.begin(), e = btm.end(); i != e; ++i){
    j = redir.find(i->second);

    if (j != redir.end()) { btm2[i->first] = j->second; }
    else {
      u32 sz = 1, idx = i->second;

      k = nsf.find(idx);
      if (k != nsf.end()) { sz = k->second; nsf2[curr] = sz; }

      btm2[i->first] = redir[i->second] = curr;
      inv.push_back(i->first);
      if (weak.count(idx)) { wk.insert(curr); }

      idx++; curr++;

      for (u32 ii = 1; ii < sz; ++ii) {
	inv.push_back(FIELD);
	if (weak.count(idx)) {
	  wk.insert(curr);
	}
	
	k = nsf.find(idx);
	if (k != nsf.end()) { nsf2[curr] = k->second; }

	idx++; curr++;
      }
    }
  }

  weak.swap(wk);
  btm.swap(btm2);
  nsf.swap(nsf2);

  wk.clear();
  nsf2.clear();
  btm2.clear();

  Data::num_btm = curr;

  for (v2u_it i = top.begin(), e = top.end(); i != e; ++i) {
    top2[i->first] = curr;
    inv.push_back(i->first);
    ++curr;
  }

  top.swap(top2);
  top2.clear();

  // prepare the union/find vector
  //
  pe.insert(pe.end(),curr,-1);

  Data::num_top = curr - Data::num_btm;
  Data::num_vars = Data::num_top + Data::num_btm;
}

u32 VarInfo::unite(u32 a, u32 b)
{
  assert(a < pe.size() && b < pe.size() && REP(a) && REP(b));
  assert(top[inv[a]] == a && top[inv[b]] == b);
  
  if (a == b) { return a; }

  u32 ra = RNK(a), rb = RNK(b);
  
  if (ra < rb) { u32 t = a; a = b; b = t; }
  else if (ra == rb) { --pe[a]; }

  pe[b] = a;

  return a;
}

void VarInfo::set_vso(bitmap &off)
{
  for (bm_it o = off.begin(), e = off.end(); o != e; ++o) {
    bool found = false;

    for (u2u_it i = nsf.begin(), e = nsf.end(); i != e; ++i) {
      if (i->second > *o) { vso[*o].set(i->first); found = true; }
    }

    STT(if (!found) { Data::nulloff++; });
  }
}

void VarInfo::print()
{
  cout << "TOP-LEVEL VARIABLES" << endl;

  for (v2u_it i = top.begin(), e = top.end(); i != e; ++i) {
    string s;
    
    if (ART(i->first)) {
      assert(i->first == I2P);
      s = "I2P";
    }
    else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(i->first)) {
      Value *g = strip(CE->getOperand(0));
      assert(!ART(g) && isa<GlobalVariable>(g) && g->getNameStr() != "");
      s = "GEP#" + g->getNameStr();
    }
    else if (Instruction *ins = dyn_cast<Instruction>(i->first)) {
      //FIX: assert(ins->getNameStr() != "");
      Function *F = ins->getParent()->getParent();
      s = F->getNameStr() + "#" + ins->getNameStr();

      if (ins->getNameStr() == "") { s += "unnamed"; }//!!
    }
    else if (Argument *a = dyn_cast<Argument>(i->first)) {
      assert(a->getNameStr() != "");
      Function *F = a->getParent();
      s = F->getNameStr() + "#" + a->getNameStr();
    }
    else {
      assert(isa<GlobalValue>(i->first) && i->first->getNameStr() != "");
      s = i->first->getNameStr();
    }

    cout << i->second << " -> " << s << endl;
  }

  cout << endl << "ADDRESS-TAKEN VARIABLES" << endl;

  for (v2u_it i = btm.begin(), e = btm.end(); i != e; ++i) {
    string s;

    if (ART(i->first)) {
      if      (i->first == I2P)   { s = "I2P"; }
      else if (i->first == FIELD) { s = "FIELD"; }
      else                        { assert(0); }
    }
    else if (Instruction *ins = dyn_cast<Instruction>(i->first)) {
      //FIX: assert(ins->getNameStr() != "");
      Function *F = ins->getParent()->getParent();
      s = F->getNameStr() + "#" + ins->getNameStr();

      if (ins->getNameStr() == "") { s += "unnamed"; }//!!
    }
    else if (Argument *a = dyn_cast<Argument>(i->first)) {
      assert(a->getNameStr() != "");
      Function *F = a->getParent();
      s = F->getNameStr() + "#" + a->getNameStr();
    }
    else {
      assert(isa<GlobalValue>(i->first) && i->first->getNameStr() != "");
      s = i->first->getNameStr();
    }
    
    cout << i->second << " -> " << s << endl;

    if (nsf.count(i->second)) {
      for (u32 j = 1, e = nsf[i->second]; j < e; ++j) {
	assert(inv[i->second+j] == FIELD);

	ostringstream o; o << j;
	cout << i->second+j << " -> " << s + "#field" + o.str() << endl;
      }
    }
  }
}

void VarInfo::stats()
{
  v2u_it j;
  set<u32> eq;

  for (u32 i = 1; i < inv.size(); ++i) {
    Value *v = inv[i];
    if ((j = top.find(v)) != top.end()) {
      if (j->second == i) { eq.insert(find(i)); }
    }
  }
  
  cout << "number of top-level ptr eq classes == " << eq.size() << endl;
}

// strip off constant expressions encapsulating the real Value, except
// return constant GEP expressions (because they're treated the same
// as top-level variables)
//
Value* VarInfo::strip(Value *v)
{
  bool exp = false;

  while (!ART(v) && !exp && isa<ConstantExpr>(v)) {
    ConstantExpr *C = cast<ConstantExpr>(v);

    switch (C->getOpcode()) {
    case Instruction::BitCast:       v = C->getOperand(0); break;
    case Instruction::GetElementPtr: v = C; exp = true;    break;
    case Instruction::IntToPtr:      v = I2P;              break;
    default: assert(0 && "constant expr not handled");
    }
  }

  //!!FIXME: we need to handle a GEP of a GEP; this comes up for
  //         ConstantExpr (eg, like those used for global variables)
  //         for now, ignore the outer GEPs
  //
  if (exp) {
    Value *t = v, *old = v;
    while (!ART(v) && isa<ConstantExpr>(v)) {
      ConstantExpr *C = cast<ConstantExpr>(v);
      switch (C->getOpcode()) {
      case Instruction::BitCast:       v = C->getOperand(0);        break;      
      case Instruction::GetElementPtr: t = v; v = C->getOperand(0); break;      
      case Instruction::IntToPtr:      v = I2P;                     break; 
      default: assert(0 && "constant expr not handled");
      }
    }

    if (ART(v) || !isa<ConstantExpr>(v) || 
	(isa<ConstantExpr>(v) &&
	 cast<ConstantExpr>(v)->getOpcode() != Instruction::GetElementPtr)) {
      v = t;
      assert(isa<ConstantExpr>(t) &&                                           
	     cast<ConstantExpr>(t)->getOpcode() == Instruction::GetElementPtr);
    }

    if (v != old) { cerr << "!!!!" << endl; }
  }

  return v;
}

//// PRIVATE METHODS

// return the eq class rep of the set containing x; uses path
// compression.
//
u32 VarInfo::find(u32 x)
{
  assert(x < pe.size());

  if (REP(x)) { return x; }
  else { return (pe[x] = find(pe[x])); }
}

// process all the named struct types declared in the module and store
// their information in struct_info: for each struct type we create a
// u32 vector s.t. the lower 16 bits is either 0 (a non-weak field) or
// 1 (a weak field) and for nested structs the upper 16 bits of the
// first field of the nested struct is the number of fields in that
// nested struct
//
// unnamed structs will be processed as they are encountered; it's ok
// to set largest_struct here because types can't be cast to unnamed
// struct types
//
void VarInfo::processStructs(Module& M)
{
  u32 sz = 0;
  TypeSymbolTable& tst = M.getTypeSymbolTable();

  largest_struct = 0;

  for (type_it i = tst.begin(), e = tst.end(); i != e; ++i) {
    if (const StructType* st = dyn_cast<StructType>(i->second)) {
      if (struct_info.count(st)) { continue; }
      vector<u32>& info = struct_info[st];
      processStructType(st,info,false);
      if (info.size() > sz) { sz = info.size(); largest_struct = st; }
    }
  }

  // if there are no named structs then make the largest struct
  // equivalent to a single char field
  //
  if (largest_struct == 0) {
    largest_struct = Type::Int8Ty;
    struct_info[largest_struct].push_back(false);
    struct_off[largest_struct].push_back(0);
    struct_off[largest_struct].push_back(1);
  }
}

u32 VarInfo::processStructType(const StructType* typ, vector<u32>& info, 
			       bool wk)
{
  u32 prev_sz;
  bool w = wk, seen = false;
  vector<u32>& off = struct_off[typ];

  if (off.empty()) { off.push_back(0); }
  else             { seen = true; }

  prev_sz = info.size();

  for (struct_it i = typ->element_begin(),e = typ->element_end(); i != e; ++i){
    const Type* et = *i;

    if (isa<ArrayType>(*et)) {
      w = true;
      et = cast<ArrayType>(et)->getElementType();
    }

    if (const StructType* st = dyn_cast<StructType>(et)) {
      u32 nf = processStructType(st,info,w);
      
      if (nf > 1) {
	assert(((nf << 16) >> 16 == nf) && info.size() >= nf);
	info[info.size()-nf] |= (nf << 16);
      }
    }
    else { info.push_back(w); }

    if (!seen) { off.push_back(info.size() - prev_sz); }
    w = wk;
  }

  return (info.size() - prev_sz);
}

// look at the uses of the return values from allocation instructions
// and see if they are bitcast into another type; if they are bitcast
// into multiple types we return the largest one (in terms of number
// of struct fields, where non-structs count as a single field)
//
// if the return value isn't immediately cast to another type and is
// either an integer* or void* then we conservatively assume it can be
// cast to any type (which in practice means make it the type of the
// largest struct in the program)
//
// OPT: note that we are a bit optimistic here in assuming that if the
//      return value is immediately cast then it won't be cast to a
//      larger type later on
//
const Type* VarInfo::findPossibleType(Instruction *inst)
{
  u32 sz = 1;
  bool cast = false;

  assert(isa<PointerType>(inst->getType()));
  const Type *r = inst->getType()->getContainedType(0);

  if (const ArrayType *at = dyn_cast<const ArrayType>(r)) { 
    r = at->getElementType();
  }

  if (const StructType * st = dyn_cast<const StructType>(r)) {
    if (!struct_info.count(st)) { // unnamed struct type
      vector<u32>& info = struct_info[st];
      processStructType(st,info,false);
    }

    sz = struct_info[st].size();
  }

  for (use_it i = inst->use_begin(), e = inst->use_end(); i != e; ++i) {
    if (isa<CastInst>(*i) && isa<PointerType>((*i)->getType())) {
      cast = true;
      const Type *t = (*i)->getType()->getContainedType(0);

      if (const ArrayType *at = dyn_cast<const ArrayType>(t)) { 
	t = at->getElementType();
      }
      
      if (const StructType * st = dyn_cast<const StructType>(t)) {
	if (!struct_info.count(st)) { // unnamed struct type
	  vector<u32>& info = struct_info[st];
	  processStructType(st,info,false);
	}

	u32 nsz = struct_info[st].size();
	if (nsz > sz) { sz = nsz; r = t; }
      }
    }
  }

  if (!cast && (r->isInteger() || r == Type::VoidTy)) { r = largest_struct; }

  return r;
}

#endif // _VARINFO_H
