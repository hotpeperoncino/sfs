#ifndef _CG_H
#define _CG_H

#include "common.h"
#include "extinfo.h"

extern ExtInfo *ext;

// function info
//
struct FunInfo
{
  u32 dfs;       // for tarjan's scc algorithm
  bool vst, del; //

  u32 topo;            // topological order
  bool psv, rec, idr;  // preserving? recursive? contains indirect calls?
  set<Function*> succ; // call-graph successors

  // the set of globals that this function directly or indirectly
  // accesses, and therefore need to be passed during binding
  //
  set<GlobalValue*> globs;

  FunInfo() : dfs(0), vst(false), del(false), topo(0), psv(true), 
	      rec(false), idr(false) {}
};

// call-graph (CG)
//
// - we use our own call-graph instead of LLVM's because (1) LLVM's
//   doesn't account for indirect calls, and (2) LLVM's doesn't use
//   our whole-program assumption
//
// - we assume that any indirect call can target any address-taken
//   function when computing the call-graph (we can't soundly rely on
//   function signatures to narrow this down)
//
// OPT: can we safely filter indirect targets by matching signature
//      prefixes? (accounting for varargs as well, of course)
//
class CG
{
public:
  
   CG() {}
  ~CG() { clear(); }
  
  // compute conservative call-graph, find address-taken functions,
  // number functions topologically, and mark them as preserving or
  // recursive as appropriate
  //
  // IMPORTANT: this should be the first method ever called; all the
  // others depend on the information computed by this method
  //
  void computeInfo(Module&);

  // return the function information for the given function
  //
  FunInfo* operator[](Function *F) { assert(info[F]); return info[F]; }

  // true iff the function has its address taken
  //
  bool adrp(Function *F) { return my_search<Function*>(adr,F); }

  typedef map<Function*,FunInfo*>::iterator cg_it;
  typedef vector<Function*>::iterator       adr_it;

  // return iterators over the set of FunInfos
  //
  cg_it begin() { return info.begin(); }
  cg_it end()   { return info.end();   }

  // return iterators over the set of address-taken functions
  //
  adr_it adr_begin() { return adr.begin(); }
  adr_it adr_end()   { return adr.end();   }

  // clear the information when it's no longer needed
  //
  void clear();

  // report statistics about the call-graph
  //
  void stats(Module&);

  // print call-graph to a graphviz dot file (with the filename given
  // as an argument)
  //
  void print(const string&);

  // mark functions reachable from the given function using direct
  // calls; only marked functions are output by print()
  //
  void mark_reach(set<Function*>&);

private:

  vector<Function*> adr;        // address-taken functions
  map<Function*,FunInfo*> info; // function info

  stack<Function*> st;  // for tarjan's scc algorithm
  u32 dfs_num, top_num; //

  void computeInitInfo(Module&);
  void computeFinalInfo();

  void visit(Function*);
  bool escapes(Value*);
  void getInst(Value*,set<Instruction*>&);

  void mark_visit(Function*);

  CG(CG &c) {} // prevent shallow copy problems
};

//// PUBLIC METHODS

void CG::computeInfo(Module& M)
{
  computeInitInfo(M);
  computeFinalInfo();
}

void CG::clear()
{
  for (cg_it i = info.begin(), e = info.end(); i != e; ++i) { 
    delete i->second;
  }

  info.clear();
  adr.clear();
}

void CG::stats(Module &M)
{
  u32 num_int = 0;
  u32 num_ext = 0;
  u32 num_rec = 0;
  u32 num_adr = 0;
  u32 num_psv = 0;
  u32 num_glob = 0;
  u32 num_int_adr = 0;

  for (fmod_it i = M.begin(), e = M.end(); i != e; ++i) {
    if (adrp(&*i)) {
      num_adr++;
      if (!ext->is_ext(&*i)) { num_int_adr++; }
    }

    if (ext->is_ext(&*i)) { num_ext++; continue; }

    num_int++;

    assert(info[&*i]);
    FunInfo *fi = info[&*i];

    if (fi->rec) { num_rec++; }
    if (fi->psv) { num_psv++; }

    num_glob += fi->globs.size();
  }

  double glob_avg = (double)num_glob/num_int;

  dbgs() << "   internal functions == " << num_int << "\n"
       << "   external functions == " << num_ext << "\n"
       << "  recursive functions == " << num_rec << "\n"
       << " addr-taken functions == " << num_adr
       << " [internal == " << num_int_adr << "]" << "\n"
       << " preserving functions == " << num_psv << "\n"
       << "  avg global pointers == " << glob_avg << "\n" << "\n";
}

void CG::print(const string& file)
{
  std::string s("");
  llvm::raw_string_ostream out(s);

  out << "digraph CG {" << "\n"
      << "\tgraph [ label=\"CG\",size=\"8.5,11\" ];" << "\n" << "\n";

  for (cg_it i = info.begin(), e = info.end(); i != e; ++i) {
    Function *F = i->first;
    FunInfo *fi = i->second;

    if (!fi->vst) { continue; }

    out << "\t" << fi->topo << " [label=\"" << F->getName() 
        << "\"];" << "\n";

    for (funs_it j = fi->succ.begin(), e = fi->succ.end(); j != e; ++j) {
      FunInfo *fi2 = info[*j];
      assert(fi2);

      out << "\t" << fi->topo << " -> " << fi2->topo << ";" << "\n";
    }
  }

  out << "}" << "\n";
}

void CG::mark_reach(set<Function*>& Fs)
{
  // unmark all functions
  //
  for (cg_it i = info.begin(), e = info.end(); i != e; ++i) {
    i->second->dfs = 0;
    i->second->vst = false;
    i->second->del = false;
  }

  dfs_num = 0;

  for (funs_it i = Fs.begin(), e = Fs.end(); i != e; ++i) {
    if (info.count(*i)) { mark_visit(*i); }
  }
}

//// PRIVATE METHODS

// go through all the call instructions to construct the call-graph;
// find address-taken functions and mark functions as non-preserving
// and/or recursive as appropriate; collect the set of global
// variables referenced directly or transitively by each function
//
void CG::computeInitInfo(Module& M)
{
  for (fmod_it i = M.begin(), e = M.end(); i != e; ++i) {
    if (escapes(&*i)) { adr.push_back(&*i); }
    if (ext->is_ext(&*i)) { continue; }

    FunInfo *fi = new FunInfo;
    info[&*i] = fi;
    
    for (inst_iterator k = inst_begin(&*i); k != inst_end(&*i); ++k) {
      if (CallInst *ci = dyn_cast<CallInst>(&*k)) { // call instruction
        if (Function *callee = calledFunction(ci)) { // direct call
          if (!ext->is_ext(callee)) { // not external
            fi->succ.insert(callee);
            if (callee == &*i) { fi->rec = true; } // self-recursive
          }
        }
        else if (!isa<InlineAsm>(ci->getCalledValue())) { // indirect call
          fi->idr = true;
        } 

	// a function is non-preserving if it operates on pointer-type
	// variables or passes them to another function

        if (isa<PointerType>(k->getType())) { fi->psv = false; }
        else if (fi->psv) {
          arg_it ai = CallSite(ci).arg_begin(), ae = CallSite(ci).arg_end();
          
          for ( ; ai != ae; ++ai) {
            if (isa<PointerType>((*ai)->getType()) &&
                !isa<ConstantPointerNull>(*ai)) { fi->psv = false; break; }
          }
        }
      }
      else if (isa<PointerType>(k->getType())) { fi->psv = false; }
      else if (fi->psv && isa<StoreInst>(&*k)) {
        StoreInst *si = cast<StoreInst>(&*k);
        if (isa<PointerType>(si->getOperand(0)->getType())) {fi->psv = false;}
      }
    }
  }

  sort<adr_it>(adr.begin(),adr.end()); // sort adr for adrp()

  //
  // for each global variable that has or contains a pointer type,
  // determine the functions that use it
  //

  set<Instruction*> inst;

  for (glob_it i = M.global_begin(), e = M.global_end(); i != e; ++i) {
    if (hasPtr(i->getType()->getContainedType(0))) {
      for (use_it j = i->use_begin(), e = i->use_end(); j != e; ++j) {
	inst.clear();
        getInst(*j,inst);

        for (inss_it k = inst.begin(), e = inst.end(); k != e; ++k) {
          Function *F = (*k)->getParent()->getParent();
          if (ext->is_ext(F)) { continue; } // malloc, etc

          assert(info[F]);
          info[F]->globs.insert(&*i);
        }
      }
    }
  }
}

// mark mutually recursive functions, propagate globs and false psv
// flags, and number functions in topological order
//
void CG::computeFinalInfo()
{
  dfs_num = 0;
  top_num = 0;

  for (cg_it i = info.begin(), e = info.end(); i != e; ++i) {
    if (!i->second->vst) { visit(i->first); }
  }

  assert(st.empty());
}

// nuutila's variant of tarjan's algorithm, used to find SCCs in the
// call-graph
//
void CG::visit(Function *F)
{
  FunInfo *pi = info[F];
  assert(pi);

  u32 my_dfs = dfs_num; dfs_num++;

  pi->dfs = my_dfs;
  pi->vst = true;

  // look at all successors of F
  //
  for (funs_it i = pi->succ.begin(), e = pi->succ.end(); i != e; ++i) {
    FunInfo *pi2 = info[*i];
    assert(pi2);

    if (!pi2->del) {
      if (!pi2->vst) { visit(*i); }
      if (pi->dfs > pi2->dfs) { pi->dfs = pi2->dfs; }
    }

    pi->psv &= pi2->psv;
    pi->globs.insert(pi2->globs.begin(),pi2->globs.end());
  }

  // if F contains an indirect call, look at all address-taken
  // functions
  //
  if (pi->idr) {
    for (adr_it j = adr.begin(), e = adr.end(); j != e; ++j) {
      if (ext->is_ext(*j)) { continue; }
      
      FunInfo *pi2 = info[*j];
      assert(pi2);
      
      if (!pi2->del) {
        if (!pi2->vst) { visit(*j); }
        if (pi->dfs > pi2->dfs) { pi->dfs = pi2->dfs; }
      } 
      
      pi->psv &= pi2->psv;
      // globs are propagated below
    }
  }

  // if this is a root node, process it
  //
  if (my_dfs == pi->dfs) {
    bool idr = pi->idr;
    vector<Function*> scc;

    while (!st.empty() && info[st.top()]->dfs >= my_dfs) {
      Function *f = st.top(); st.pop();
      FunInfo *fi = info[f];

      scc.push_back(f);

      idr |= fi->idr;
      fi->del = true;

      fi->topo = top_num;
      top_num++;
    }

    pi->del = true;
    pi->topo = top_num;
    top_num++;

    // for SCCs that contain an indirect call, collect global roots
    // from all address-taken functions (done here rather than the for
    // loop above for efficiency)
    //
    if (idr) {
      for (adr_it j = adr.begin(), e = adr.end(); j != e; ++j) {
        if (ext->is_ext(*j)) { continue; }

        FunInfo *pi2 = info[*j];
        pi->globs.insert(pi2->globs.begin(),pi2->globs.end());
      }
    }

    if (!scc.empty()) {
      scc.push_back(F);

      for (funv_it i = scc.begin(), e = scc.end(); i != e; ++i) {
        FunInfo *fi = info[*i];
	
	fi->psv = pi->psv;
        fi->rec = true;
        fi->globs.insert(pi->globs.begin(),pi->globs.end());

        assert(pi->globs == info[*i]->globs);
      }
    }
  }
  else { st.push(F); }
}

// analyze the uses of a function to find out if it escapes into
// another value (in essence its address is taken)
//
bool CG::escapes(Value *v)
{
  for (use_it i = v->use_begin(), e = v->use_end(); i != e; ++i) {
    if (CallInst *ci = dyn_cast<CallInst>(*i)) {
      for (u32 k = 1; k < ci->getNumOperands(); ++k) {
        if (ci->getOperand(k) == v) { return true; }
      }
    }
    else if (InvokeInst *ii = dyn_cast<InvokeInst>(*i)) {
      for (u32 k = 3; k < ii->getNumOperands(); ++k) {
        if (ii->getOperand(k) == v) { return true; }
      }
    }
    else if (isa<ConstantExpr>(*i)) {
      if (escapes(*i)) { return true; }
    }
    else if (!isa<CmpInst>(*i)) { return true; }
  }
  
  return false;
}

// if v is an instruction insert v, else if v is a constant expression
// insert the instructions that use v
//
void CG::getInst(Value *v, set<Instruction*>& inst)
{
  if (Instruction *i = dyn_cast<Instruction>(v)) { inst.insert(i); }
  else if (ConstantExpr *C = dyn_cast<ConstantExpr>(v)) {
    for (use_it k = C->use_begin(), e = C->use_end(); k != e; ++k) { 
      getInst(*k,inst);
    }
  }
}

// nuutila's variant of tarjan's algorithm, used to mark reachable
// functions in the call-graph
//
void CG::mark_visit(Function *F)
{
  FunInfo *pi = info[F];
  assert(pi);

  u32 my_dfs = dfs_num; dfs_num++;

  pi->dfs = my_dfs;
  pi->vst = true;

  // look at all successors of F
  //
  for (funs_it i = pi->succ.begin(), e = pi->succ.end(); i != e; ++i) {
    FunInfo *pi2 = info[*i];
    assert(pi2);

    if (!pi2->del) {
      if (!pi2->vst) { mark_visit(*i); }
      if (pi->dfs > pi2->dfs) { pi->dfs = pi2->dfs; }
    }
  }

  // if this is a root node, process it
  //
  if (my_dfs == pi->dfs) {
    while (!st.empty() && info[st.top()]->dfs >= my_dfs) {
      Function *f = st.top(); st.pop();
      info[f]->del = true;
    }
    pi->del = true;
  }
  else { st.push(F); }
}

#endif // _CG_H
