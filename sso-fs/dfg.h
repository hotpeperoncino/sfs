#ifndef _DFG_H
#define _DFG_H

#include "../common/common.h"
#include "../common/cg.h"
#include "../common/pqueue.h"
#include "../common/ptrinst.h"
#include "../common/extinfo.h"
#include "../common/exttrans.h"
#include "varinfo.h"
#include PTRINFO_H

extern ExtInfo *ext;

// a node of the DFG
//
struct DFnode
{
  // common node elements
  // 
  u32 topo;    // topological order
  PtrInst pi;  // instruction
  VarInfo *vi; // variable info, only needed for print()

  // SEG info, used for NOOP, [I]CALL, RET, LOAD, STORE[2]
  // instructions to propagate local ptr info
  //
  PtrInfo *in;              // incoming local pointer info
  PtrInfo *out;             // outgoing info for [I]CALL, STORE[2]
  vector<DFnode*> seg_succ; // SEG successors

  // def-use chains, used for all ops to process users of the
  // top-level info produced by an instruction
  //
  vector<DFnode*> use_succ; // uses of this instruction

  //
  // methods
  //

  DFnode() : topo(0), vi(0), in(0), out(0) {}

  DFnode(VarInfo *_vi) : topo(0), vi(_vi), in(0), out(0) {}

  DFnode(VarInfo *_vi, PtrInst &_pi) : topo(0), pi(_pi), vi(_vi), 
				       in(0), out(0) {}

  ~DFnode()
  {
    // in and out are shared between nodes so we need to ensure we
    // don't double-free them; therefore we do this in DFG::clear()
  }

  void print()
  {
    CallInst *ci = 0;
    cout << "[" << topo << "] ";

    switch (pi.op) {
    case NOOP:
      if (!pi.inst) { cout << "NOOP " << this << endl; }
      else          { cout << "PRM "  << this << endl; }

      break;
    case CALL:
      ci = cast<CallInst>(pi.inst);

      if (pi.lhs) { cout << pi.lhs << " = "; }
      cout << calledFunction(ci)->getNameStr() << " ( ";

      for (uv_it i = pi.rhs.begin(), e = pi.rhs.end(); i != e; ++i) {
	cout << *i << " ";
      }
      cout << ")" << endl;

      break;
    case ICALL:
      ci = cast<CallInst>(pi.inst);

      if (pi.lhs) { cout << pi.lhs << " = "; }
      cout << "(*" << (*vi)[ci->getCalledValue()] << ") ( ";

      for (uv_it i = pi.rhs.begin(), e = pi.rhs.end(); i != e; ++i) {
	cout << *i << " ";
      }
      cout << ")" << endl;

      break;
    case RET:
      cout << "RET ";
      if (!pi.rhs.empty()) { cout << pi.rhs[0] << endl; }
      else { cout << "null" << endl; }

      break;
    case COPY:
      cout << pi.lhs << " =";
      for (uv_it i = pi.rhs.begin(), e = pi.rhs.end(); i != e; ++i) {
	cout << " " << *i;
      }
      cout << endl;

      break;
    case ALLOC:
      assert(!pi.rhs.empty());
      cout << pi.lhs << " = &" << pi.rhs[0] << endl;

      break;
    case LOAD:
      assert(!pi.rhs.empty());
      cout << pi.lhs << " = *" << pi.rhs[0] << endl;

      break;
    case STORE:
      assert(!pi.rhs.empty());
      cout << "*" << pi.lhs << " = " << pi.rhs[0] << endl;

      break;
    case STORE2:
      assert(!pi.rhs.empty());
      cout << "*" << pi.lhs << " = *" << pi.rhs[0] 
	   << " + " << pi.off << endl;

      break;
    case GEP:
      assert(!pi.rhs.empty());
      cout << pi.lhs << " = GEP " << pi.rhs[0] << " " << pi.off << endl;

      break;
    default: assert(0 && "unknown opcode");
    }
  }
};

// DFG info for each function
//
struct DFinfo
{
  u32 topo; // function's topological order

  DFnode *ret;      // function's return node
  DFnode *seg_root; // function's SEG root node

  // the roots of the def-use graph
  //
  map<u32,DFnode*> prms; // parameter --> DFnodes
  vector<DFnode*> roots; // other root DFnodes 

  set<DFnode*> cs;     // function's callsites
  set<DFnode*> new_cs; // new callsites discovered from indirect calls

  bitmap glob_roots; // the globals that this function needs to keep
		     // during binding as a callee

  PQ_1<DFnode> worklist; // function's DFG worklist

  DFinfo() : topo(0), ret(0), seg_root(0) {}
};

typedef set<DFnode*>::iterator dfns_it;
typedef vector<DFnode*>::iterator dfnv_it;
typedef map<u32,DFnode*>::iterator u2dfn_it;

// DFG (data-flow graph): combines a def-use graph for top-level
// variables with a sparse evaluation graph for the rest
//
class DFG
{
public:

   DFG() : vi(0), ti(0) {}
  ~DFG() { clear(); }

  // initialize vi and ti (this needs to be done before anything else)
  //
  void init(VarInfo *v, PtrInfo *t) { vi = v; ti = t; }

  // construct the data-flow graph for the given module using the
  // given call-graph information
  //
  void construct(Module&,CG&);

  // return the DFinfo for a given function
  //
  DFinfo* operator[](Function *F) { assert(info[F]); return info[F]; }

  // same as operator[] except return NULL if there is no DFinfo
  //
  DFinfo* getInfo(Function *F)
  {
    dfg_it i = info.find(F);
    return (i == info.end()) ? 0 : i->second;
  }

  // given a GEP instruction or expression, compute the offset
  //
  u32 compute_gep_off(User*);

  // return the set of GEP offsets used by this program
  //
  bitmap& getGEPOffsets() { return gep_off; }

  // place pointers to all of the DFnodes reachable from the given
  // DFinfo into the given vector
  //
  void getDFnodes(DFinfo*,vector<DFnode*>&);

  // report on the number of equivalent local PtrInfos
  //
  void compute_eq();

  // return the sum of the sizes of the PtrInfos for all DFnodes
  //
  u32 compute_sz();

  // report statistics about the DFG
  //
  void stats(Module&);

  typedef map<Function*,DFinfo*> info_type;
  typedef info_type::iterator dfg_it;

  // return iterators over the functions' DFinfos
  //
  dfg_it begin() { return info.begin(); }
  dfg_it end()   { return info.end();   }

  // print the DFG to a graphviz dot file (with the filename given as
  // an argument)
  //
  void print(const string&);

  void clear();

private:

#define ELIM(n) ((n)->pi.op == COPY && !(n)->pi.inst) // for PE

  //// TYPES

  // for tarjan's algorithm
  //
  struct TarjanInfo
  {
    u32 dfs;       // depth-first number
    bool vst, del; // visited? deleted?
    
    TarjanInfo() : dfs(0), vst(false), del(false) {}
  };

  // basic block info
  //
  struct BBinfo
  {
    u32 scc;       // SCC this basic block belongs to
    bool psv;      // preserving?
    TarjanInfo ti; // for finding SCCs

    BBinfo() : scc(0), psv(true) {}
  };
  
  // SCC info (of basic blocks)
  //
  struct SCCinfo
  {
    set<u32> pred;        // predecessor SCCs
    DFnode *first, *last; // first and last DFnodes for this SCC

    SCCinfo() : first(0), last(0) {}
  };

  //// DATA STRUCTURES

  VarInfo *vi;    // variable info
  PtrInfo *ti;    // top-level pointer info
  info_type info; // function --> DFinfo
  
  u32 top_num; // topological number
  u32 dfs_num; // depth-first search number

  bitmap gep_off; // set of GEP offsets

  // for tarjan's
  //
  stack<DFnode*> dfg_st;
  stack<BasicBlock*> bb_st;

  // for constructing a DFG for a function
  //
  map<u32,SCCinfo> sccInfo;
  map<Value*,DFnode*> du_i2n;
  map<Value*,DFnode*> seg_i2n;
  map<BasicBlock*,BBinfo> bbInfo;
  map<DFnode*,TarjanInfo> dfgInfo;

  // for P2I->I2P copies
  //
  map<Value*,vector<u32> > i2p;
  map<Value*,vector<Instruction*> > p2i;

  // for detecting local equivalence
  //
  map<DFnode*,bitmap> lbls;
  hash_map<bitmap,PtrInfo*> ptrs;

  //// METHODS

  void functionDFG(Function*,CG&);

  bool globalRHS(Instruction*);
  void computeSuccs(DFnode*,vector<DFnode*>&,set<DFnode*>&);

  void dfg_visit(DFnode*);
  void bb_visit(BasicBlock*);
  void hu_visit(DFnode*,u32);
  DFnode* du_visit(Value*);

  DFnode* handleLoad(Instruction*);
  DFnode* handleStore(Instruction*);
  DFnode* handleCall(Instruction*,CG&,vector<Instruction*>&);
  DFnode* handleRet(Instruction*,DFinfo*);
  DFnode* handleExt(Instruction*,Function*);
  DFnode* handleCast(Instruction*);
  DFnode* handlePhi(Instruction*);
  DFnode* handleSelect(Instruction*);
  DFnode* handleGEP(Instruction*);
  DFnode* handleAlloc(Instruction*);
  DFnode* handleI2P(Instruction*);
  
  void traceI2P(Instruction*,set<Value*>&,set<Value*>&);
  void traceExp(ConstantExpr*,set<Value*>&,set<Value*>&);

  DFG(DFG &c) {} // prevent shallow copy problems
};

//// PUBLIC METHODS

void DFG::construct(Module &M, CG& cg)
{
  // give each non-preserving internal function an entry in info
  //
  for (fmod_it i = M.begin(), e = M.end(); i != e; ++i) {
    if (!ext->is_ext(i) && !cg[i]->psv) { info[i] = new DFinfo; }
  }

  // construct a DFG for each function that meets the above citeria
  // (we do this separately from above because when processing call
  // instructions we need to be sure the DFinfo for the callee has
  // already been created)
  //
  for (dfg_it i = info.begin(); i != info.end(); ++i) {
    functionDFG(i->first,cg);
  }

  // compute the offsets used by the constant GEP expressions in order
  // for gep_off to be complete; offsets of 0 are collapsed
  //
  set<ConstantExpr*>::iterator i, e, k;

  for (i = vi->const_exps.begin(), e = vi->const_exps.end(); i != e; ) {
    if (!compute_gep_off(*i)) {
      Value *v = VarInfo::strip((*i)->getOperand(0));
      assert(!ART(v) && isa<GlobalVariable>(v));

      vi->unite((*vi)[v],(*vi)[*i]);
      k = i; ++i; vi->const_exps.erase(k);
    }
    else { ++i; }
  }

  // store the globals each function needs to keep during binding and
  // update the instructions to use variable reps
  //
  vector<DFnode*> nodes;

  for (dfg_it i = info.begin(); i != info.end(); ++i) {
    Function *F = i->first;
    DFinfo *di = i->second;

    // get the globals used (perhaps transitively) by this function
    //
    for (gvs_it i = cg[F]->globs.begin(), e = cg[F]->globs.end(); i != e; ++i){
      di->glob_roots.set((*vi)[*i]);
    }
    di->glob_roots.set((*vi)[I2P]);

    // the ext_vars also need to be included just in case
    //
    for (vals_it j = vi->ext_vars.begin(), e = vi->ext_vars.end(); j != e; ++j){
      di->glob_roots.set((*vi)[*j]);
    }
    
    // now update the instructions of this function

    getDFnodes(di,nodes);

    for (dfnv_it j = nodes.begin(), e = nodes.end(); j != e; ++j) {
      PtrInst &pi = (*j)->pi;

      if (pi.lhs) { pi.lhs = (*vi)[pi.lhs]; }

      if (pi.op != ALLOC) {
	for (uv_it k = pi.rhs.begin(), e = pi.rhs.end(); k != e; ++k) {
	  if (*k) { *k = (*vi)[*k]; }
	}
      }
    }

    nodes.clear();
  }
}

u32 DFG::compute_gep_off(User *gep)
{
  u32 off = 0;

  for (gept_it i = gep_type_begin(*gep), e = gep_type_end(*gep); i != e; ++i) {
    if (isa<StructType>(*i)) {
      u32 idx = cast<ConstantInt>(i.getOperand())->getZExtValue();
      vector<u32>& struct_offs = vi->structOffsets(cast<StructType>(*i));

      assert(idx < struct_offs.size());
      off += struct_offs[idx];
    }
  }

  if (off) { gep_off.set(off); }
  return off;
}

void DFG::getDFnodes(DFinfo *di, vector<DFnode*>& nodes)
{
  deque<DFnode*> q;
  set<DFnode*> vst;

  q.push_back(di->seg_root);

  for (u2dfn_it i = di->prms.begin(), e = di->prms.end(); i != e; ++i) { 
    q.push_back(i->second);
  }

  for (dfnv_it i = di->roots.begin(), e = di->roots.end(); i != e; ++i) {
    q.push_back(*i);
  }

  while (!q.empty()) {
    DFnode *n = q.front(); q.pop_front();

    if (vst.count(n)) { continue; }
    vst.insert(n);

    nodes.push_back(n);

    for (dfnv_it i = n->seg_succ.begin(), e = n->seg_succ.end(); i != e; ++i) {
      q.push_back(*i);
    }

    for (dfnv_it i = n->use_succ.begin(), e = n->use_succ.end(); i != e; ++i) {
      q.push_back(*i);
    }
  }
}

// for hashing PtrInfos
//
namespace __gnu_cxx {
  template<> struct hash<PtrInfo> {
    size_t operator()(const PtrInfo& s) const { return s.getHash(); }};
}

void DFG::compute_eq()
{
  u32 num_empty = 0;
  set<PtrInfo*> seen;
  vector<DFnode*> nodes;
  hash_map<PtrInfo,bool> eq;
  
  for (dfg_it i = info.begin(), e = info.end(); i != e; ++i) {
    getDFnodes(i->second,nodes);

    for (dfnv_it j = nodes.begin(), e = nodes.end(); j != e; ++j) {
      DFnode *n = *j;

      if (n->in && !seen.count(n->in)) {
        seen.insert(n->in);
        eq[*(n->in)] = true;
        if (n->in->empty()) { num_empty++; }
      }

      if (n->out && !seen.count(n->out)) {
        seen.insert(n->out);
        eq[*(n->out)] = true;
        if (n->out->empty()) { num_empty++; }
      }
    }

    seen.clear();
    nodes.clear();
  }

  cout << "   number of local-pts eq == " << eq.size() << endl
       << "number of empty local-pts == " << num_empty << endl;
}

u32 DFG::compute_sz()
{
  u32 tot = 0;
  set<PtrInfo*> seen;
  vector<DFnode*> nodes;

  for (dfg_it i = info.begin(), e = info.end(); i != e; ++i) {
    getDFnodes(i->second,nodes);

    for (dfnv_it j = nodes.begin(), e = nodes.end(); j != e; ++j) {
      DFnode *n = *j;

      if (n->in && !seen.count(n->in)) {
	seen.insert(n->in);
	tot += n->in->size();
      }

      if (n->out && !seen.count(n->out)) {
        seen.insert(n->out);
        tot += n->out->size();
      }
    }

    seen.clear();
    nodes.clear();
  }

  return tot;
}

void DFG::stats(Module &M)
{
  set<PtrInfo*> num_pts;
  vector<DFnode*> nodes;
  u32 num_inst = 0, num_call = 0, num_icall = 0, num_ret = 0, 
    num_copy = 0, num_alloc = 0, num_load = 0, num_store= 0, 
    num_store2 = 0, num_gep = 0, num_mn = 0, num_pn = 0, 
    num_sin = 0, num_prm = 0;
  
  for (fmod_it i = M.begin(); i != M.end(); ++i) {
    if (ext->is_ext(i)) { continue; }
    for (inst_iterator j = inst_begin(i), e = inst_end(i); j != e; ++j) {
      num_inst++;
    }
  }

  for (dfg_it i = info.begin(), e = info.end(); i != e; ++i) {
    getDFnodes(i->second,nodes);

    for (dfnv_it j = nodes.begin(), e = nodes.end(); j != e; ++j) {
      DFnode *n = *j;

      if (n->in)  { num_pts.insert(n->in);  }
      if (n->out) { num_pts.insert(n->out); }

      switch (n->pi.op) {
      case NOOP:
	num_pn++;
	if (n->pi.inst) { num_prm++; }
	break;
      case CALL:   num_mn++; num_call++;   break;
      case ICALL:  num_mn++; num_icall++;  break;
      case RET:    num_mn++; num_ret++;    break;
      case COPY:
	num_mn++; num_copy++;
	sort<uv_it>(n->pi.rhs.begin(),n->pi.rhs.end());
        unique<uv_it>(n->pi.rhs.begin(),n->pi.rhs.end());
        if (n->pi.rhs.size() == 1) { num_sin++; }
	break;
      case ALLOC:  num_mn++; num_alloc++;  break;
      case LOAD:   num_mn++; num_load++;   break;
      case STORE:  num_mn++; num_store++;  break;
      case STORE2: num_mn++; num_store2++; break;
      case GEP:    num_mn++; num_gep++;    break;
      default: assert(0 && "unknown opcode");
      }
    }

    nodes.clear();
  }

  cout << "    functions == " << info.size() << endl
       << " instructions == " << num_inst << endl
       << "pointer insts == " << num_mn << endl
       << "  --   CALL == " << num_call << endl
       << "  --  ICALL == " << num_icall << endl
       << "  --    RET == " << num_ret << endl
       << "  --  ALLOC == " << num_alloc << endl
       << "  --   LOAD == " << num_load << endl
       << "  --  STORE == " << num_store << endl
       << "  -- STORE2 == " << num_store2 << endl
       << "  --    GEP == " << num_gep
       << " (" << gep_off.count() << " offsets)" << endl
       << "  --   COPY == " << num_copy
    STT(<< " [singletons == " << num_sin << "]" << endl) << endl << endl;

  cout << "      m-nodes == " << num_mn << endl
       << "      p-nodes == " << num_pn 
       << " [params == " << num_prm << "]" << endl
       << "  total nodes == " << num_mn+num_pn 
       << " (- params == " << num_mn+num_pn-num_prm << ")" << endl << endl;

  cout << "  num PtrInfo == " << num_pts.size() << endl << endl;
}

void DFG::print(const string& file)
{
  deque<DFnode*> q;
  set<DFnode*> vst;
  ofstream out(file.c_str(),ios_base::trunc);

  out.setf(ios::dec);

  // alphabetize output of functions
  //
  map<string,Function*> alpha;
  for (dfg_it i = info.begin(), e = info.end(); i != e; ++i) {
    assert(!alpha.count(i->first->getNameStr()));
    alpha[i->first->getNameStr()] = i->first;
  }

  for (map<string,Function*>::iterator i = alpha.begin(), e = alpha.end();
       i != e; ++i) {
    DFinfo *di = info[i->second];
    vst.clear();

    q.push_back(di->seg_root);

    for (u2dfn_it j = di->prms.begin(), e = di->prms.end(); j != e; ++j) { 
      q.push_back(j->second);
    }

    for (dfnv_it k = di->roots.begin(), e = di->roots.end(); k != e; ++k) {
      q.push_back(*k);
    }

    out << "digraph FUN_" << i->first << " {" << endl
        << "\tgraph [ label=\"" << i->first << "\","
        << " labelloc=t, size=\"8.5,11\" ];" << endl << endl;

    while (!q.empty()) {
      DFnode *n = q.front(); q.pop_front();

      if (vst.count(n)) { continue; }
      vst.insert(n);

      out << "\t" << (u32)n << " [label=\"" << n->topo << "_";

      if (n->pi.op == NOOP && n->pi.inst) { out << "prm\""; }
      else {
	out << PtrInst::StrOp(n->pi.op);
	if (n->pi.op == CALL) {
	  out << "(" 
	      << calledFunction(cast<CallInst>(n->pi.inst))->getNameStr()
	      << ")";
	}

	out << "\"";
      }

      out << "];" << endl;

      for (dfnv_it j = n->seg_succ.begin(), e = n->seg_succ.end(); 
	   j != e; ++j) {
        out << "\t" << (u32)n << " -> " << (u32)*j << ";" << endl;
        q.push_back(*j);
      }

      for (dfnv_it j = n->use_succ.begin(), e = n->use_succ.end();
           j != e; ++j) {
        out << "\t" << (u32)n << " -> " << (u32)*j 
	    << " [color=blue];" << endl;
        q.push_back(*j);
      }
    }

    out << "}" << endl << endl;
  }

  out.close();
}

void DFG::clear()
{
  set<PtrInfo*> pts;
  vector<DFnode*> nodes;

  for (dfg_it i = info.begin(), e = info.end(); i != e; ++i) {
    getDFnodes(i->second,nodes);

    for (dfnv_it j = nodes.begin(),e = nodes.end(); j != e; ++j) {
      if ((*j)->in) { pts.insert((*j)->in); }
      if ((*j)->out) { pts.insert((*j)->out); }
      delete *j;
    }
    nodes.clear();

    delete i->second;
  }

  info.clear();

  for (set<PtrInfo*>::iterator i = pts.begin(), e = pts.end(); i != e; ++i) {
    delete *i;
  }
}

//// PRIVATE METHODS

// create the data-flow graph for a function. the graph actually
// consists of two intermingling graphs: the sparse evaluation graph
// (SEG) for instructions that use or modify local pointer info
// (i.e. from variables that aren't top-level); and the def-use graph
// for instructions that use or modify top-level pointer info
//
// the SEG portion uses the linear-time algorithm from ramanlingam's
// paper 'on sparse evaluation representation'
//
// remember that globals are never top-level variables, so new pointer
// info can only come from the function parameters or the function's
// seg_root node
//
void DFG::functionDFG(Function *F, CG &cg)
{
  DFinfo *di = info[F];
  assert(di);

  di->topo = cg[F]->topo;

  // instructions that are relevant to building the def-use graph
  // (i.e. potential sources of pointer info)
  //
  vector<Instruction*> du_rel;

  // instructions that are relevant to detecting local equivalence
  //
  vector<DFnode*> hu_roots;

  // for creating P2I->I2P copies
  //
  set<Value*> vst, src;

  //
  // create the SEG portion of the DFgraph, with nodes for LOAD,
  // STORE[2], [I]CALL, and RET instructions, and edges following the
  // control-flow of the program
  //

  top_num = 0;
  dfs_num = 0;

  // find relevant basic blocks and translate the instructions; also
  // store the relevant statements for use in constructing the def-use
  // graph later
  //
  for (bb_it i = F->begin(); i != F->end(); ++i) {
    BBinfo &bi = bbInfo[i];
    SCCinfo &scci = sccInfo[top_num];
      
    for (ibb_it j = i->begin(); j != i->end(); ++j) {
      DFnode *n = 0;

      switch (j->getOpcode()) {
	//
	// SEG nodes
	//
      case Instruction::Load:  n = handleLoad(j);           break;
      case Instruction::Store: n = handleStore(j);          break;
      case Instruction::Call:  n = handleCall(j,cg,du_rel); break;
      case Instruction::Ret:   n = handleRet(j,di);         break;

	//
	// potentially relevant instructions for the def-use graph
	//

      case Instruction::IntToPtr:
	traceI2P(j,src,vst); // try to connect I2P with source pointers
	
	// for each I2P instruction save the set of pointers its info
	// comes from; for each instruction whose info goes to a I2P
	// instruction save the set of I2P instructions its info goes
	// to (in order to compute the new def-use chains)
	//
        for (vals_it k = src.begin(), e = src.end(); k != e; ++k) {
          i2p[j].push_back((*vi)[*k]);
	  Value *v = VarInfo::strip(*k);

          if (!ART(v) && !isa<GlobalValue>(v) && !isa<ConstantExpr>(v)) {
            p2i[v].push_back(j);
          }
        }
	
        src.clear();
        vst.clear();

        // lack of 'break' deliberate

      case Instruction::Alloca:
      case Instruction::Malloc:
      case Instruction::PHI:
      case Instruction::Select:
      case Instruction::BitCast:
      case Instruction::GetElementPtr:	
	if (isa<PointerType>(j->getType())) { du_rel.push_back(j); }
	break;
	
      default: break; // don't care
      }

      if (!n) { continue; }
      assert(n->pi.op != NOOP);

      // some instructions in the SEG are also potentially source
      // nodes in the def-use graph
      //
      if ((isa<LoadInst>(j) || isa<CallInst>(j)) &&
	  isa<PointerType>(j->getType())) { du_rel.push_back(j); }

      // see if this node is relevant to detecting local equivalence
      //
      switch (n->pi.op) {
#if SSO_OPT != 1
      case CALL:
      case ICALL:
#endif
      case STORE:
      case STORE2: hu_roots.push_back(n); break;
      default:                            break;
      }

      // register the new DFnode for the def-use graph
      //
      seg_i2n[j] = n;

      // if this is the first non-preserving instruction in the basic
      // block modify sccInfo and bbInfo, otherwise just plug in the
      // new DFnode
      //
      if (bi.psv) {
	bi.psv = false;
	bi.scc = top_num;
	
	scci.first = n;
	scci.last = n;
      }
      else {
	assert(scci.last && !my_find<DFnode*>(scci.last->seg_succ,n));
	scci.last->seg_succ.push_back(n);
	scci.last = n;
      }
    }

    // increment the topological numbering
    //
    if (!bi.psv) { top_num++; }
  }

  // evidently there are weird cases where a function will not have a
  // return instruction. the only example i've seen is where the
  // function ends in an 'unreachable' instruction instead; i'm not
  // sure what other circumstances would made this true.
  //
  // we'll place the Function* in pi.inst instead of a Instruction* in
  // order to distinguish the artificial node from a real return node
  // while still giving a way to find the parent function easily
  //
  if (!di->ret) { PtrInst pi(RET,F); di->ret = new DFnode(vi,pi); }

  // compute preserving SCCs; note that this does not identify SCCs
  // that contain both preserving and non-preserving nodes, so the
  // SCCs are not maximal in the CFG
  //
  for (bb_it i = F->begin(), e = F->end(); i != e; ++i) {
    BBinfo& bi = bbInfo[i];
    if (bi.psv && !bi.ti.vst) { bb_visit(i); }
  }

  assert(bb_st.empty());

  // compute predecessors for each SCC
  //
  for (bb_it i = F->begin(), e = F->end(); i != e; ++i) {
    BBinfo& bi = bbInfo[i];
    SCCinfo& si = sccInfo[bi.scc];

    for (pred_iterator j = pred_begin(i), e = pred_end(i); j != e; ++j) {
      BBinfo& bi2 = bbInfo[*j];

      if (bi2.scc != bi.scc) {
        assert(!bi2.psv || bi.scc < bi2.scc);
        si.pred.insert(bi2.scc);
      }
    }
  }

  bbInfo.clear();

  // used for the NOOP SEG nodes created below
  //
  PtrInst pi;

  set<DFnode*> preds;

  // construct SEG in topological order, except all preserving SCCs
  // before all non-preserving SCCs
  //
  for (int i = top_num-1; i >= 0; --i) {
    SCCinfo& scci = sccInfo[i];
    preds.clear();

    // collect DFnode predecessors (getting rid of repeats)
    //
    for (us_it j = scci.pred.begin(), e = scci.pred.end(); j != e; ++j) {
      assert(sccInfo[*j].last);
      preds.insert(sccInfo[*j].last);
    }

    if (preds.empty()) {
      //
      // there should be only one entry node to the function
      //
      assert(di->seg_root == 0 && "multiple entry nodes");
      if (!scci.first) { scci.first = scci.last = new DFnode(vi,pi); }
      di->seg_root = scci.first;
    }
    else if (!scci.first && preds.size() == 1) {
      //
      // merge this NOOP node with previous SEG node
      //
      scci.first = scci.last = *(preds.begin());
    }
    else { // scci.first || preds.size() > 1
      if (!scci.first) { scci.first = scci.last = new DFnode(vi,pi); }

      // connect predecessor SEG nodes
      //
      for (dfns_it j = preds.begin(), e = preds.end(); j != e; ++j) {
	assert(!my_find<DFnode*>((*j)->seg_succ,scci.first));
	(*j)->seg_succ.push_back(scci.first);
      }
    }
  }

  sccInfo.clear();
  dfgInfo.clear();

  // if we created an artificial return node, we need to place an edge
  // from the SEG root node to the return node so callers can get
  // their pointer info back
  //
  if (isa<Function>(di->ret->pi.inst)) { 
    di->seg_root->seg_succ.push_back(di->ret);
  }

  //
  // compute the def-use graph, using the function parameters and
  // relevant statements
  //

  // build the def-use graph starting from the relevant instrucions
  //
  for (insv_it i = du_rel.begin(), e = du_rel.end(); i != e; ++i) { 
    du_visit(*i);
  }

  // build the def-use graph starting from the function parameters
  //
  for (prm_it i = F->arg_begin(), e = F->arg_end(); i != e; ++i) {
    if (isa<PointerType>(i->getType())) { di->prms[(*vi)[i]] = du_visit(i); }
  }

  // make sure all of the parameters are reps
  //
  DBX(for (u2dfn_it i = di->prms.begin(), e = di->prms.end(); i != e; ++i) {
      assert((*vi)[i->first] == i->first); });

  i2p.clear();
  seg_i2n.clear();
  dfgInfo.clear();
  assert(p2i.empty());

  //
  // remove superfluous nodes (due to pointer equivalence) from the
  // graph -- all nodes x s.t. ELIM(x)
  //
  set<DFnode*> vst2;
  vector<DFnode*> col, succ;

  for (insv_it i = du_rel.begin(), e = du_rel.end(); i != e; ++i) {
    DFnode *n = du_i2n[*i];
    if (n) { col.push_back(n); }
  }

  for (u2dfn_it i = di->prms.begin(), e = di->prms.end(); i != e; ++i) { 
    col.push_back(i->second);
  }

  for (dfnv_it i = col.begin(), e = col.end(); i != e; ++i) {
    DFnode *n = *i;
    computeSuccs(n,succ,vst2);
    
    DBX(for (u32 j = 0; j < succ.size(); ++j) { assert(!ELIM(succ[j])); });
    
    n->use_succ.clear();
    n->use_succ.swap(succ);

    vst2.clear();
  }

  col.clear();

  //
  // detect local equivalence
  //

  u32 idx = 0;
  if (!my_find<DFnode*>(hu_roots,di->seg_root)) {
    hu_roots.push_back(di->seg_root);
  }

  for (dfnv_it i = hu_roots.begin(), e = hu_roots.end(); i != e; ++i) {
    //
    // the SEG root should be labeled to represent the pointer info it
    // receives from its callers; however if the root contains a call
    // or store that label shouldn't be propagated further -- instead
    // a new label should be used to represent the result of the call
    // or store
    //
    if (*i == di->seg_root) {
      lbls[*i].set(idx);
      switch ((*i)->pi.op) {
#if SSO_OPT != 1
      case CALL:
      case ICALL:
#endif
      case STORE:
      case STORE2: ++idx; break;
      default:            break;	
      }
    }

    hu_visit(*i,idx);

    ++idx;
    dfgInfo.clear();
  }

  //
  // compute topological ordering for nodes in the DFgraph and create
  // their PtrInfo's (sharing according to HU)
  //

  top_num = 0;
  dfs_num = 0;
  
  // starting from the SEG's root node
  //
  dfg_visit(di->seg_root);

  // starting from the function parameters
  //
  for (u2dfn_it i = di->prms.begin(), e = di->prms.end(); i != e; ++i) { 
    dfg_visit(i->second);
  }

  // starting from the relevant statements
  //
  // we rely on the assumption that the elements of du_rel are in
  // something approximating topological order already in order to
  // discover the true roots (i.e. those nodes necessary to make the
  // entire DFG reachable) -- these are saved in di->roots
  //
  for (insv_it i = du_rel.begin(), e = du_rel.end(); i != e; ++i) {
    DFnode *n = du_i2n[*i];
    if (!n) { continue; }

    if (!ELIM(n)) {
      TarjanInfo& info = dfgInfo[n];

      if (!info.vst) { dfg_visit(n); di->roots.push_back(n); }
      else if (n->pi.op == ALLOC && !my_find<DFnode*>(di->roots,n)) {
	// ALLOCS should always be roots, but sometimes they are part
	// of a cycle and so have already been visited
	//
	di->roots.push_back(n);
      }

      // instructions with globals on the right-hand side should be
      // used to initialize the worklist even though they aren't roots
      // of the DFG
      //
      if (globalRHS(*i)) { di->worklist.insert(n,n->topo); }
    }
    else { // ELIM(n) == true
      //
      // if the instruction has a global on the right-hand side then
      // all of the def-use successors should go on the worklist
      // (since the node itself was eliminated and therefore can't go
      // on the worklist)
      //
      if (globalRHS(*i)) {
	for (dfnv_it k = n->use_succ.begin(), e = n->use_succ.end();
	     k != e; ++k) {
	  DFnode *x = *k; assert(!ELIM(x));
	  di->worklist.insert(x,x->topo);
	}
      }
      
      // n isn't part of the DFG, so we delete it here
      //
      delete n;
      du_i2n[*i] = 0;      
    }
  }

  assert(dfg_st.empty() && "stack not empty");

  DBX(vector<DFnode*> nodes; getDFnodes(di,nodes);
      for (insv_it i = du_rel.begin(), e = du_rel.end(); i != e; ++i) {
	DFnode *n = du_i2n[*i];
	assert(!n || my_find<DFnode*>(nodes,n));
      }
      for (dfnv_it i = nodes.begin(), e = nodes.end(); i != e; ++i) {
	switch ((*i)->pi.op) {
	case STORE:
	case STORE2:
	case CALL:
	case ICALL:  assert((*i)->out);  break;
	default:     assert(!(*i)->out); break;
	}
      }
      nodes.clear());

  lbls.clear();
  ptrs.clear();
  du_rel.clear();
  du_i2n.clear();
  dfgInfo.clear();

  // initialize the function's worklist to contain the root statements
  //
  // note that we don't add the seg_root or the parameters; it doesn't
  // do any good to add them yet because there is no pointer info
  // associated with them -- they'll be added during the analysis when
  // the function is called and binding is done
  //
  for (dfnv_it i = di->roots.begin(), e = di->roots.end(); i != e; ++i) {
    di->worklist.insert(*i,(*i)->topo);
  }

  // the exception is 'main': if it has the argv and/or envp
  // parameters then they need to be placed on the worklist
  //
  if (F->getNameStr() == "main") {
    for (u2dfn_it i = di->prms.begin(), e = di->prms.end(); i != e; ++i) {
      DFnode *p = i->second;

      // the parameter node is just a noop; we actually want to add
      // its successors in the def-use graph
      //
      for (dfnv_it j = p->use_succ.begin(),e = p->use_succ.end(); j != e; ++j){
	di->worklist.insert(*j,(*j)->topo);
      }
    }
  }
}

// return true iff right-hand side of instruction has a global value
// (which includes I2P)
//
bool DFG::globalRHS(Instruction *i)
{
  Value *op;
  bool r = false;

#define GLOBAL(x) (ART(x) || isa<GlobalValue>(x) || isa<ConstantExpr>(x))

  switch (i->getOpcode()) {
  case Instruction::IntToPtr:
    r = true;
    break;
  case Instruction::PHI:
    for (u32 k = 0; k < cast<PHINode>(i)->getNumIncomingValues(); ++k) {
      op = VarInfo::strip(cast<PHINode>(i)->getIncomingValue(k));
      if (GLOBAL(op)) { r = true; break; }
    }
    break;
  case Instruction::Select:
    for (u32 k = 1; k < 3; ++k) {
      op = VarInfo::strip(i->getOperand(k));
      if (GLOBAL(op)) { r = true; break; }
    }
    break;
  case Instruction::Load:
  case Instruction::BitCast:
  case Instruction::GetElementPtr:
    op = VarInfo::strip(i->getOperand(0));
    if (GLOBAL(op)) { r = true; }
    break;
  case Instruction::Call:
  case Instruction::Alloca:
  case Instruction::Malloc:
    //
    // these don't matter
    //
    break;
  default:
    DBX(cout << "==>>" << *i);
    assert(0 && "bad instruction");
  }

  return r;
}

// we use Nuutila's variant of Tarjan's algorithms to find SCCs in the
// DFG and topologically number the nodes; we also create their
// PtrInfo's according to HU
//
void DFG::dfg_visit(DFnode *n)
{
  assert(n && !ELIM(n));
  u32 my_dfs = dfs_num; dfs_num++;

  TarjanInfo& ni = dfgInfo[n];

  ni.dfs = my_dfs;
  ni.vst = true;

  // look at all SEG successors of n
  //
  for (dfnv_it i = n->seg_succ.begin(), e = n->seg_succ.end(); i != e; ++i) {
    TarjanInfo& ni2 = dfgInfo[*i];

    if (!ni2.del) {
      if (!ni2.vst) { dfg_visit(*i); }
      if (ni.dfs > ni2.dfs) { ni.dfs = ni2.dfs; }
    }
  }

  // look at all def-use successors of n
  //
  for (dfnv_it i = n->use_succ.begin(), e = n->use_succ.end(); i != e; ++i) {
    TarjanInfo& ni2 = dfgInfo[*i];

    if (!ni2.del) {
      if (!ni2.vst) { dfg_visit(*i); }
      if (ni.dfs > ni2.dfs) { ni.dfs = ni2.dfs; }
    }
  }

  // if this is a root node, process it
  //
  if (my_dfs == ni.dfs) {
    vector<DFnode*> scc;
    map<DFnode*,bitmap>::iterator l;
    hash_map<bitmap,PtrInfo*>::iterator p;

    while (!dfg_st.empty() && dfgInfo[dfg_st.top()].dfs >= my_dfs) {
      DFnode *x = dfg_st.top(); dfg_st.pop();

      scc.push_back(x);
      dfgInfo[x].del = true;

      // give local-equivalent SEG nodes the same PtrInfo
      //
      if ((l = lbls.find(x)) != lbls.end()) {
        p = ptrs.find(l->second);
        if (p != ptrs.end()) { x->in = p->second; assert(x->in); }
        else { ptrs[l->second] = x->in = new PtrInfo(ti,vi); }
      }
    }

    // topologically number the nodes in decreasing order as we go
    // around the loop
    //
    for (int i = scc.size()-1; i >= 0; --i) {
      scc[i]->topo = top_num;
      top_num++;
    }

    n->topo = top_num;
    top_num++;

    ni.del = true;

    // same as in the above loop w.r.t. local equivalence
    //
    if ((l = lbls.find(n)) != lbls.end()) {
      p = ptrs.find(l->second);
      if (p != ptrs.end()) { n->in = p->second; assert(n->in); }
      else { ptrs[l->second] = n->in = new PtrInfo(ti,vi); }
    }

    //
    // look for opportunities to share a node's out PtrInfo with its
    // successors' in PtrInfo
    //

    scc.push_back(n);

    for (dfnv_it i = scc.begin(), e = scc.end(); i != e; ++i) {
      DFnode *x = *i;
      PtrOp op = x->pi.op;

      // these are the only types of nodes that have a non-NULL out
      //
      if (op == CALL || op == ICALL || op == STORE || op == STORE2) {
        PtrInfo *pts = 0;

        // we can only share a node's out PtrInfo if it has a single
        // in PtrInfo among all its successors
        //
        for (dfnv_it j = x->seg_succ.begin(), e = x->seg_succ.end(); 
	     j != e; ++j) {
	  assert((*j)->in);
          
          if      (!pts)            { pts = (*j)->in; }
          else if ((*j)->in != pts) { pts = 0; break; }
        }
        
        if (pts) { x->out = pts; }
        else     { x->out = new PtrInfo(ti,vi); }
      }
    }
  }
  else { dfg_st.push(n); }  
}

// we use Nuutila's variant of Tarjan's algorithms to find SCCs in the
// basic blocks, excluding edges to and from non-preserving blocks
//
void DFG::bb_visit(BasicBlock *bb)
{
  u32 my_dfs = dfs_num; dfs_num++;

  BBinfo& bi = bbInfo[bb];

  bi.ti.dfs = my_dfs;
  bi.ti.vst = true;

  // look at all successors of bb
  //
  for (succ_iterator i = succ_begin(bb), e = succ_end(bb); i != e; ++i) {
    BBinfo& bi2 = bbInfo[*i];

    if (bi2.psv && !bi2.ti.del) {
      if (!bi2.ti.vst) { bb_visit(*i); }
      if (bi.ti.dfs > bi2.ti.dfs) { bi.ti.dfs = bi2.ti.dfs; }
    }
  }

  // if this is a root node, process it
  //
  if (my_dfs == bi.ti.dfs) {
    while (!bb_st.empty() && bbInfo[bb_st.top()].ti.dfs >= my_dfs) {
      BasicBlock *s = bb_st.top(); bb_st.pop();

      BBinfo& bi2 = bbInfo[s];

      bi2.scc = top_num;
      bi2.ti.del = true;
    }

    bi.scc = top_num;
    bi.ti.del = true;

    top_num++;
  }
  else { bb_st.push(bb); }
}

DFnode* DFG::du_visit(Value *v)
{
  // ignore irrelevant instructions
  //
  if (!isa<PointerType>(v->getType()) &&
      !isa<CallInst>(v)               &&
      !isa<ReturnInst>(v)             &&
      !isa<StoreInst>(v))
    { return 0; }

  map<Value*,DFnode*>::iterator i2n = du_i2n.find(v);
  if (i2n != du_i2n.end()) { assert(i2n->second); return i2n->second; }

  DFnode *n = 0;
  i2n = seg_i2n.find(v);

  if (i2n != seg_i2n.end()) { n = i2n->second; assert(n); }
  else if (Instruction *i = dyn_cast<Instruction>(v)) {
    switch (i->getOpcode()) {
    case Instruction::BitCast:       n = handleCast(i);      break;
    case Instruction::PHI:           n = handlePhi(i);       break;
    case Instruction::Select:        n = handleSelect(i);    break;
    case Instruction::GetElementPtr: n = handleGEP(i);       break;
    case Instruction::Alloca:
    case Instruction::Malloc:        n = handleAlloc(i);     break;
    case Instruction::IntToPtr:      n = handleI2P(i);       break;

    case Instruction::Load:
    case Instruction::Store:
    case Instruction::Call:
    case Instruction::Ret:
      //
      // since the instruction wasn't in seg_i2n, it must not be
      // pointer related
      //
      break;

    default:
      DBX(cout << "==>>" << *i << endl);
      assert(0 && "unknown instruction");
    }
  }
  else {
    assert(isa<Argument>(v));
    
    PtrInst pi(NOOP,v);
    n = new DFnode(vi,pi);
  }

  if (!n) { return 0; }

  du_i2n[v] = n;

  // look for pointer equivalence (except for function pointers; if we
  // unite them then we'll have problems resolving indirect calls)
  //
  if (n->pi.op == COPY && n->pi.rhs.size() == 1) {
    u32 rhs = n->pi.rhs.front();
    Value *inv = vi->inverse(rhs);

    if (ART(inv) || !isa<Function>(inv)) {
      n->pi.inst = 0; // mark as ELIM
      vi->unite((*vi)[n->pi.lhs],(*vi)[rhs]);
    }
  }

  if (isa<PointerType>(v->getType())) {
    vector<Instruction*> uses;
    map<Value*,vector<Instruction*> >::iterator k = p2i.find(v);

    //
    // collect the uses (which include any I2P instructions this
    // pointer reaches)
    //

    if (k != p2i.end()) {
      uses.insert(uses.end(),k->second.begin(),k->second.end());
      p2i.erase(k);
    }

    for (use_it i = v->use_begin(), e = v->use_end(); i != e; ++i) {
      assert(isa<Instruction>(*i));
      uses.push_back(cast<Instruction>(*i));
    }

    // add the def-use successor nodes
    //
    for (insv_it i = uses.begin(), e = uses.end(); i != e; ++i) {
      if (DFnode *s = du_visit(*i)) {
	if (!my_find<DFnode*>(n->use_succ,s)) { n->use_succ.push_back(s); }
      }
    }
  }

  return n;
}

// compute the successors of a node, skipping over ELIM nodes; we do
// it this way to make sure that every ELIM node in a cycle of ELIM
// nodes gets the right successors
//
void DFG::computeSuccs(DFnode *n, vector<DFnode*>& succ, set<DFnode*>& vst)
{
  vst.insert(n);

  for (dfnv_it i = n->use_succ.begin(), e = n->use_succ.end(); i != e; ++i) {
    if (!ELIM(*i)) { succ.push_back(*i); }
    else if (!vst.count(*i)) { computeSuccs(*i,succ,vst); }
  }
}

void DFG::hu_visit(DFnode *n, u32 idx)
{
  for (dfnv_it i = n->seg_succ.begin(), e = n->seg_succ.end(); i != e; ++i) {
    TarjanInfo &info = dfgInfo[*i];

    if (!info.vst) {
      info.vst = true;
      lbls[*i].set(idx);

      switch ((*i)->pi.op) {
#if SSO_OPT != 1
      case CALL:
      case ICALL:
#endif
      case STORE:
      case STORE2:               break;
      default: hu_visit(*i,idx); break;
      }
    }
  }
}

DFnode* DFG::handleLoad(Instruction *i)
{
  if (!isa<PointerType>(i->getType())) { return 0; }

  LoadInst *si = dyn_cast<LoadInst>(i);
  assert(si);
  
  Value *op0 = si->getOperand(0);
  
  if (!isa<PointerType>(si->getType()) ||
       isa<ConstantPointerNull>(op0)   ||
       isa<UndefValue>(op0))
    { return 0; }
  
  u32 lhs = (*vi)[si];
  u32 rhs = vi->getTrans(op0);

  if (!rhs) { return 0; }
  
  PtrInst pi(LOAD,lhs,i);
  pi.rhs.push_back(rhs);

  return (new DFnode(vi,pi));
}

DFnode* DFG::handleStore(Instruction *i)
{
  StoreInst *si = dyn_cast<StoreInst>(i);
  assert(si);
  
  Value *op0 = si->getOperand(0);
  Value *op1 = si->getOperand(1);
  
  if (!isa<PointerType>(op0->getType()) ||
       isa<ConstantPointerNull>(op0)    ||
       isa<UndefValue>(op0)             ||
       isa<ConstantPointerNull>(op1)    || 
       isa<UndefValue>(op1))
    { return 0; }
  
  u32 lhs = (*vi)[op1];
  u32 rhs = (*vi)[op0];
  
  PtrInst pi(STORE,lhs,i);
  pi.rhs.push_back(rhs); 

  return (new DFnode(vi,pi));
}

DFnode* DFG::handleCall(Instruction *i, CG &cg, vector<Instruction*>& du_rel)
{
  CallInst *ci = dyn_cast<CallInst>(i);
  assert(ci);

  PtrInst pi;
  pi.inst = i;

  DFnode *r = 0;
  
  if (Function *c = calledFunction(ci)) { // direct call
    if (ext->is_ext(c)) {
      DFnode *n = handleExt(i,c);

      if (n) {
	switch (n->pi.op) {
	case LOAD:
	case STORE:
	case STORE2:
	  r = n;
	  break;
	case CALL:
	case ICALL:
	case RET:
	  // shouldn't happen
	  DBX(cout << "==>> " << c->getNameStr() << endl);
	  assert(0 && "mistranslated external call");
	  break;
	case ALLOC:
	case COPY:
	  // save node for def-use graph
	  seg_i2n[i] = n;
	  du_rel.push_back(i);
	  break;
	default: assert(0 && "unknown op");
	}
      }
    }
    else { // internal call
      if (!cg[c]->psv) { // not a preserving call
        pi.op = CALL;
        if (isa<PointerType>(ci->getType())) { pi.lhs = (*vi)[ci]; }

	// for calls we subvert the meaning of pi.rhs by using it to
	// hold the function arguments; non-pointer arguments are
	// converted to I2P, NULL arguments are converted to 0
	//
	for (u32 k = 1; k < ci->getNumOperands(); ++k) {
	  Value *v = ci->getOperand(k);

	  if (isa<PointerType>(v->getType())) {
	    if (isa<ConstantPointerNull>(v)) { pi.rhs.push_back(0); }
	    else { pi.rhs.push_back((*vi)[v]); }
	  }
	  else { pi.rhs.push_back((*vi)[I2P]); }
	}

	r = new DFnode(vi,pi);
	
	assert(info[c]);
        info[c]->cs.insert(r);
      }
    }
  }
  else { // indirect call
    Value *v = ci->getCalledValue();

    // we ignore inline assembly
    //
    if (!isa<InlineAsm>(v)) {
      pi.op = ICALL;
      if (isa<PointerType>(ci->getType())) { pi.lhs = (*vi)[ci]; }
      
      // same note about pi.rhs here as for direct calls
      //
      for (u32 k = 1; k < ci->getNumOperands(); ++k) {
	Value *v = ci->getOperand(k);

	if (isa<PointerType>(v->getType())) {
	  if (isa<ConstantPointerNull>(v)) { pi.rhs.push_back(0); }
	  else { pi.rhs.push_back((*vi)[v]); }
	}
	else { pi.rhs.push_back((*vi)[I2P]); }
      }
      
      r = new DFnode(vi,pi);
    }
  }

  return r;
}

DFnode* DFG::handleRet(Instruction *i, DFinfo *di)
{
  ReturnInst *ri = dyn_cast<ReturnInst>(i);
  assert(ri);
  
  PtrInst pi(RET,i);  
  Value *ret = ri->getReturnValue();

  if ( ret                              &&
       isa<PointerType>(ret->getType()) &&
      !isa<ConstantPointerNull>(ret))
    { pi.rhs.push_back((*vi)[ret]); }
  
  DFnode *r = new DFnode(vi,pi);

  assert(!di->ret && "multiple return statements");
  di->ret = r;

  return r;
}

DFnode* DFG::handleExt(Instruction *i, Function *cle)
{
  DFnode *r = 0;
  PtrInst pi = ExtTrans::translate(cast<CallInst>(i),cle,vi);

  if (pi.op != NOOP) { r = new DFnode(vi,pi); }
  return r;
}

DFnode* DFG::handleCast(Instruction *i)
{
  BitCastInst *si = dyn_cast<BitCastInst>(i);
  assert(si);
  
  Value *op0 = si->getOperand(0);

  if (isa<ConstantPointerNull>(op0) ||
      isa<UndefValue>(op0)) { return 0; }
  
  u32 lhs = (*vi)[si];
  u32 rhs = (*vi)[op0];

  PtrInst pi(COPY,lhs,i);
  pi.rhs.push_back(rhs);

  return (new DFnode(vi,pi));
}

DFnode* DFG::handlePhi(Instruction *i)
{
  PHINode *si = dyn_cast<PHINode>(i);
  assert(si);
  
  vector<u32> rhs;
  u32 lhs = (*vi)[si];
  
  for (u32 k = 0; k < si->getNumIncomingValues(); ++k) {
    Value *opk = si->getIncomingValue(k);

    if (isa<ConstantPointerNull>(opk) ||
        isa<UndefValue>(opk)) { continue; }
    
    u32 r = (*vi)[opk];
    if (!my_find<u32>(rhs,r)) { rhs.push_back((*vi)[opk]); }
  }

  DFnode *r = 0;

  if (!rhs.empty()) {
    PtrInst pi(COPY,lhs,i);
    pi.rhs.insert(pi.rhs.begin(),rhs.begin(),rhs.end());

    r = new DFnode(vi,pi);
  }

  return r;
}

DFnode* DFG::handleSelect(Instruction *i)
{
  SelectInst *si = dyn_cast<SelectInst>(i);
  assert(si);

  vector<u32> rhs;
  u32 lhs  = (*vi)[si];
  
  Value *op1 = si->getOperand(1);
  if (!isa<ConstantPointerNull>(op1) &&
      !isa<UndefValue>(op1))
    { rhs.push_back((*vi)[op1]); }
  
  Value *op2 = si->getOperand(2);
  if (!isa<ConstantPointerNull>(op2) &&
      !isa<UndefValue>(op2)) {
    u32 r = (*vi)[op2];
    if (!my_find<u32>(rhs,r)) { rhs.push_back(r); }
  }
  
  DFnode *r = 0;
  
  if (!rhs.empty()) {
    PtrInst pi(COPY,lhs,i);
    pi.rhs.insert(pi.rhs.begin(),rhs.begin(),rhs.end());

    r = new DFnode(vi,pi);
  }

  return r;
}

DFnode* DFG::handleGEP(Instruction *i)
{
  GetElementPtrInst *si = dyn_cast<GetElementPtrInst>(i);
  assert(si);
  
  Value *op0 = si->getOperand(0);
  
  if (isa<ConstantPointerNull>(op0) ||
      isa<UndefValue>(op0)) { return 0; }

  u32 lhs = (*vi)[si];
  u32 rhs = (*vi)[op0];

  PtrInst pi;

  pi.inst = i;
  pi.lhs = lhs;
  pi.rhs.push_back(rhs);

  u32 off = compute_gep_off(si);

  if (off == 0) { pi.op = COPY; }
  else          { pi.op = GEP; pi.off = off; }

  return (new DFnode(vi,pi));
}

DFnode* DFG::handleAlloc(Instruction *i)
{
  AllocationInst *si = dyn_cast<AllocationInst>(i);
  assert(si);
  
  u32 lhs = (*vi)[si];
  u32 rhs = (*vi)(si);

  PtrInst pi(ALLOC,lhs,i);
  pi.rhs.push_back(rhs);

  return (new DFnode(vi,pi));
}

DFnode* DFG::handleI2P(Instruction *i)
{
  IntToPtrInst *si = dyn_cast<IntToPtrInst>(i);
  assert(si);
  
  u32 lhs = (*vi)[si];
  PtrInst pi(COPY,lhs,i);

  map<Value*,vector<u32> >::iterator k = i2p.find(i);

  if (k != i2p.end()) {
    vector<u32>& rhs = k->second;

    for (uv_it j = rhs.begin(), e = rhs.end(); j != e; ++j) {
      if (!my_find<u32>(pi.rhs,*j)) { pi.rhs.push_back(*j); }
    }
  }
  else { pi.rhs.push_back((*vi)[I2P]); }

  return (new DFnode(vi,pi));
}

void DFG::traceI2P(Instruction *i, set<Value*>& src, set<Value*>& vst)
{
  vst.insert(i);

  PHINode *x = 0;
  vector<Value*> ops;

  switch (i->getOpcode()) {
  case Instruction::Load:
  case Instruction::Call:
  case Instruction::ExtractElement:
    src.insert(I2P);
    break;

  case Instruction::PtrToInt:
    src.insert(i->getOperand(0));
    break;

  case Instruction::Select:
    ops.push_back(i->getOperand(1));
    ops.push_back(i->getOperand(2));
    break;

  case Instruction::PHI:
    x = cast<PHINode>(i);
    for (u32 k = 0, e = x->getNumIncomingValues(); k < e; ++k) {
      ops.push_back(x->getIncomingValue(k));
    }
    break;

  default:
    if (!isa<CmpInst>(i)) {
      for (op_it j = i->op_begin(), e = i->op_end(); j != e; ++j) {
        ops.push_back(*j);
      }
    }
  }

  for (valv_it k = ops.begin(), e = ops.end(); k != e; ++k) {
    Value *v = *k;

    if (ConstantExpr *C = dyn_cast<ConstantExpr>(v)) {
      if (!vst.count(C)) { traceExp(C,src,vst); }
    }
    else if (Instruction *ii = dyn_cast<Instruction>(v)) {
      if (!vst.count(ii)) { traceI2P(ii,src,vst); }
    }
    else if (isa<Argument>(v)) { src.insert(I2P); }
  }
}

void DFG::traceExp(ConstantExpr *C, set<Value*>& src, set<Value*>& vst)
{
  vst.insert(C);
  vector<Value*> ops;

  switch (C->getOpcode()) {
  case Instruction::Load:
  case Instruction::Call:
  case Instruction::ExtractElement:
    src.insert(I2P);
    break;

  case Instruction::PtrToInt:
    src.insert(C->getOperand(0));
    break;

  case Instruction::Select:
    ops.push_back(C->getOperand(1));
    ops.push_back(C->getOperand(2));
    break;

  default:
    for (op_it j = C->op_begin(), e = C->op_end(); j != e; ++j) {
      ops.push_back(*j);
    }
  }

  for (valv_it k = ops.begin(), e = ops.end(); k != e; ++k) {
    Value *v = *k;

    if (ConstantExpr *C = dyn_cast<ConstantExpr>(v)) {
      if (!vst.count(C)) { traceExp(C,src,vst); }
    }
    else if (Instruction *ii = dyn_cast<Instruction>(v)) {
      if (!vst.count(ii)) { traceI2P(ii,src,vst); }
    }
    else if (isa<Argument>(v)) { src.insert(I2P); }
  }
}


#endif // _DFG_H
