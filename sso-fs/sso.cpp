// DESCRIPTION
//
// semi-sparse interprocedural flow-sensitive, context-insensitive,
// field-sensitive pointer analysis
//
// see 'Semi-Sparse Flow-Sensitive Pointer Analysis' by Ben Hardekopf
// and Calvin Lin
//
// NOTES:
//
// - NULL values aren't tracked
//
// - we assume (conforming to the C standard): 
//
//   -- that pointers are not cast and accessed in such a way as to
//      convert a pointer to an int or vice-versa without going
//      through the LLVM PtrToInt and IntToPtr instructions
//
//   -- that structs are not indexed via an incompatible pointer
//      (i.e. a pointer to a struct that is not structurally
//      equivalent)
//
// - this is a research prototype, and while it handles most things
//   correctly there are a few corner cases where it can be unsound
//
//   -- some IntToPtr casts are not handled soundly and are assumed to
//      point to a unique location in memory distinct from any
//      declared variables; these are the casts that could not be
//      resolved to a corresponding PtrToInt cast when constructing
//      the DFG
//
//   -- some of the external call stubs in exttrans.h might not be
//      completely correct, in particular we make some guesses when
//      processing memcpy/memmove instructions
//
//   -- customized allocation functions might give some problems
//      depending on how they are implemented

#include "../common/common.h"
#include "../common/cg.h"
#include "../common/data.h"
#include "../common/stats.h"
#include "../common/pqueue.h"
#include "../common/ptrinst.h"
#include "../common/extinfo.h"
#include "../common/exttrans.h"
#include "dfg.h"
#include "varinfo.h"
#include PTRINFO_H

using llvm::errs;
using llvm::dbgs;

// for PtrInfo implemented with bitmaps use forward and backward
// filtered binding, but not for PtrInfo implemented with BDDs
//
#ifdef PTRINFO_BIT
#define FORW_FILT
#define BACK_FILT
#endif

ExtInfo *ext;

// convenience wrapper around std::find
//
template<class T>
bool my_find(vector<T>& v, T x)
{
  return (find<typename vector<T>::iterator,T>(v.begin(),v.end(),x)!=v.end());
}

// convenience wrapper around std::binary_search
//
template<class T>
bool my_search(vector<T>& v, T x)
{
  return binary_search<typename vector<T>::iterator,T>(v.begin(),v.end(),x);
}

// true iff t is a pointer or is a type that contains a pointer
//
bool hasPtr(const Type *t)
{
  bool r = false;

  if (isa<PointerType>(t)) { r = true; }
  else if (const SequentialType *ta = dyn_cast<const SequentialType>(t)) {
    r = hasPtr(ta->getElementType());
  }
  else if (const StructType *tt = dyn_cast<const StructType>(t)) {
    for (u32 j = 0; j < tt->getNumElements(); ++j) {
      if (hasPtr(tt->getElementType(j))) { r = true; break; }
    }
  }
  
  return r;
}

// get the callee of a CallInst (0 if indirect call)
//
Function* calledFunction(CallInst *ci)
{
  if (Function *F = ci->getCalledFunction()) { return F; }
  
  Value *v = ci->getCalledValue();

  if (ConstantExpr *C = dyn_cast<ConstantExpr>(v)) {
    if (C->getOpcode() == Instruction::BitCast) {
      if (Function *F = dyn_cast<Function>(C->getOperand(0))) { return F; }
    }
  }

  return 0;
}

namespace
{
  class SSaa : public ModulePass {
  public:
    
    static char ID;
    SSaa() : ModulePass(ID) {}

    bool runOnModule(Module&);
    void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
    }
    
  private:
    
    //// DATA STRUCTURES

    CG cg;      // call-graph
    DFG dfg;    // data-flow graph
    VarInfo vi; // variable info
    PtrInfo ti; // top-level pointer info

    // pointer-valued globals that should be included in the roots for
    // filtered binding
    //
    bitmap glob_roots;

    PQ_2<Function> fun_worklist; // worklist of functions
    PQ_1<DFnode> *dfg_worklist;  // current worklist of DFnodes

    //// METHODS

    void initGlobals(Module&,Function*);
    u32  processGlobalInit(DFnode*,u32,Constant*);
    void processConstGEP(ConstantExpr*,DFnode*);

    bool handleAlloc(PtrInst&);
    bool handleCopy(PtrInst&);
    bool handleGEP(PtrInst&);
    bool handleLoad(DFnode*,PtrInst&);
    void handleStore(DFnode*,PtrInst&);
    void handleStore2(DFnode*,PtrInst&);
    void handleCall(DFnode*);
    bool handleICall(DFnode*);
    void handleRet(DFnode*);

    bool forwardBind(DFnode*,PtrInfo*,Function*);
    bool backwardBind(DFnode*,DFnode*,u32);

    void printTop();
    void listExtCalls(Module&);
  };

  char SSaa::ID = 0;
  RegisterPass<SSaa> X("ss-aa","FS Alias Analysis");
}

//// PUBLIC METHODS

bool SSaa::runOnModule(Module &M)
{ 
  dbgs() << ">> USING SSO-FS <<" << "\n";
  CPU_PROFILE_START("cpu.setup");

  //// INITIALIZATION AND PRE-PROCESSING

  ext = new ExtInfo;

  ti.set_vi(&vi);
  dfg.init(&vi,&ti);

  cg.computeInfo(M);
  vi.translate(M,cg);
  dfg.construct(M,cg);

  vi.set_vso(dfg.getGEPOffsets());
  PtrInfo::init(Data::num_btm+1,dfg.getGEPOffsets(),&vi);

  Function *root = M.getFunction("main");
  assert(root && "no main function");
  
  initGlobals(M,root);

  STT(Stats::print_pre(M,cg,vi,dfg));

  cg.clear();

  CPU_PROFILE_STOP();

  //// MAIN ANALYSIS LOOP

  CPU_PROFILE_START("cpu.main");

  // initialize the function worklist to contain all functions with a
  // DFG (we start with all functions rather than just the root
  // function to make sure they're all processed at least once)
  //
  for (DFG::dfg_it i = dfg.begin(), e = dfg.end(); i != e; ++i) {
    fun_worklist.insert(i->first,i->second->topo);
  }

  vector<PtrInfo*> seen; // for propagating points-to graphs 

  while (!fun_worklist.empty()) {
    Function *F = fun_worklist.select();
    DFinfo *di = dfg[F];

    STT(Data::fun_proc++);
    dfg_worklist = &di->worklist;

    while (!dfg_worklist->empty()) {
      DFnode *n = dfg_worklist->select();
  
      assert(n);
      STT(Data::dfg_proc++; Data::uniq_dfg.insert(n));

      bool c = false; // whether the top-level pointer info has changed

      switch (n->pi.op) {
      case NOOP:   /* do nothing */           break;
      case ALLOC:  c = handleAlloc(n->pi);    break;
      case COPY:   c = handleCopy(n->pi);     break;
      case GEP:    c = handleGEP(n->pi);      break;
      case LOAD:   c = handleLoad(n,n->pi);   break;
      case STORE:      handleStore(n,n->pi);  break;
      case STORE2:     handleStore2(n,n->pi); break;
      case CALL:       handleCall(n);         break;
      case ICALL:  c = handleICall(n);        break;
      case RET:    /* wait for it */          break;
      default: assert(0 && "unknown opcode");
      }

      if (c) { // add def-use successors to the worklist
	STT(Data::dfg_change++);
	for (dfnv_it i = n->use_succ.begin(),e = n->use_succ.end();i != e;++i){
	  dfg_worklist->insert(*i,(*i)->topo);
	}
      }

      PtrInfo *out = n->in;
      if (n->out && n->out != n->in) { out = n->out; n->in->rstc(n); }

      if (out && out->changed(n) && n->pi.op != RET) { // add SEG succs
	seen.clear();

	for (dfnv_it i = n->seg_succ.begin(),e = n->seg_succ.end();i != e;++i){
	  assert(*i && (*i)->in);
	  
	  if ((*i)->in != out && !my_find<PtrInfo*>(seen,(*i)->in)) {
	    (*i)->in->unite(out);
	    seen.push_back((*i)->in);
	  }
	  
	  if ((*i)->in == out || (*i)->in->changed(*i)) { 
	    dfg_worklist->insert(*i,(*i)->topo);
	  }
	}

	out->rstc(n);
      }
    }
    
    // once the function has been processed propagate the info
    // backwards to the function's callers
    //
    handleRet(di->ret);
  }

  CPU_PROFILE_STOP();

  MEM_USAGE();
  PRECISION_REPORT();
  STT(Stats::print_post(dfg,ti));

  dfg.clear();
  glob_roots.clear();
 
  REPORT_METRICS();

  return false;
}

//// PRIVATE METHODS

void SSaa::initGlobals(Module &M, Function *root)
{
  // initialize the special IntToPtr value
  //
  ti.alloc(vi[I2P],vi(I2P));
  glob_roots.set(vi[I2P]);

  // initialize global function pointers for those functions whose
  // address is taken
  //
  for (CG::adr_it i = cg.adr_begin(), e = cg.adr_end(); i != e; ++i) {
    ti.alloc(vi[*i],vi(*i));
  }

  // initialize global variables part 1 -- in LLVM globals are always
  // pointers to objects, so first we need to connect each global
  // pointer to its corresponding object
  //
  for (glob_it i = M.global_begin(), e = M.global_end(); i != e; ++i) {
    ti.alloc(vi[&*i],vi(&*i));

    // if the global is a pointer or contains a pointer then put it
    // in glob_roots (for filtered binding)
    //
    if (hasPtr((&*i)->getType()->getContainedType(0))) { glob_roots.set(vi[&*i]); }
  }

  //
  // initialize global variables part 2 -- this has to be done after
  // the above step because we're not guaranteed to initialize a
  // global variable before it is used to initialize another global
  // variable
  //

  DFnode *r = dfg[root]->seg_root;
  assert(r && r->in);

  // process the global initializers
  //
  for (glob_it i = M.global_begin(), e = M.global_end(); i != e; ++i) {
    if (i->hasInitializer() && r->in->null(vi(&*i))) { // internal global
      processGlobalInit(r, vi(&*i), i->getInitializer());
    }
    // we assume external globals are initialized to null
  }

  // initialize the constant global expressions
  //
  for (set<ConstantExpr*>::iterator i = vi.const_exps.begin(),
	 e = vi.const_exps.end(); i != e; ++i) {
    if (ti.null(vi[*i])) { processConstGEP(*i,r); }
  }

  // initialize the external address-taken pointers identified by
  // VarInfo
  //
  // technically only argv and envp belong in the root node, the
  // others should be initialized at the corresponding allocation
  // node, but since the allocation nodes don't have local pointer
  // info we kludge a fix by making these all global roots so we're
  // sure they'll get where they need to go
  //
  for (vals_it i = vi.ext_vars.begin(), e = vi.ext_vars.end(); i != e; ++i) {
    glob_roots.set(vi[*i]);
    r->in->loc_alloc(vi(*i),vi(*i)+1);
  }

  // finally, add main's SEG root node to the worklist
  //
  dfg[root]->worklist.insert(r,r->topo);
}

u32 SSaa::processGlobalInit(DFnode *r, u32 lhs, Constant *C)
{
  Value *v = VarInfo::strip(C);

  if (v == I2P) { r->in->loc_alloc(lhs,vi(I2P)); return 1; }
  assert(!ART(v));

  C = dyn_cast<Constant>(v);
  assert(C);

  if (C->isNullValue() || isa<UndefValue>(C)) { return 1; }

  u32 off = 0;

  if (C->getType()->isSingleValueType()) { // not struct or array
    if (isa<PointerType>(C->getType())) { 
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
	if (ti.null(vi[CE])) { processConstGEP(CE,r); }
	r->in->loc_copy(lhs,vi[CE]);
      }
      else { r->in->loc_alloc(lhs,vi(C));  }
    }
    off = 1;
  }
  else if (isa<ConstantStruct>(C)) {
    for (u32 i = 0, e = C->getNumOperands(); i < e; ++i) {
      off += processGlobalInit(r,lhs+off,cast<Constant>(C->getOperand(i)));
    }
  }
  else {
    assert(isa<ConstantArray>(C));
    for (u32 i = 0, e = C->getNumOperands(); i < e; ++i) {
      off = processGlobalInit(r,lhs,cast<Constant>(C->getOperand(i)));
    }
  }

  return off;
}

void SSaa::processConstGEP(ConstantExpr *C, DFnode *n)
{
  assert(C->getOpcode() == Instruction::GetElementPtr);
  u32 lhs = vi[C], rhs = vi[C->getOperand(0)], off = dfg.compute_gep_off(C);

  if (ti.null(rhs)) {
    GlobalVariable *gv = dyn_cast<GlobalVariable>(C->getOperand(0));
    assert(gv);
    
    if (gv->hasInitializer()) { processGlobalInit(n,rhs,gv->getInitializer()); }
  }

  if (off == 0) { ti.copy(lhs,rhs);    }
  else          { ti.gep(lhs,rhs,off); }
}

bool SSaa::handleAlloc(PtrInst &pi)
{
  STT(Data::num_alloc++);
  return ti.alloc(pi.lhs,pi.rhs.front());
}

bool SSaa::handleCopy(PtrInst &pi)
{
  STT(Data::num_copy++);
  bool c = false;

  for (uv_it i = pi.rhs.begin(), e = pi.rhs.end(); i != e; ++i) {
    c |= ti.copy(pi.lhs,*i);
  }

  return c;
}

bool SSaa::handleGEP(PtrInst &pi)
{
  STT(Data::num_gep++);
  return ti.gep(pi.lhs,pi.rhs.front(),pi.off);
}

bool SSaa::handleLoad(DFnode *n, PtrInst &pi)
{
  STT(Data::num_load++);
  assert(n && n->in);
  return n->in->load(pi.lhs,pi.rhs.front());
}

void SSaa::handleStore(DFnode *n, PtrInst &pi)
{
  STT(Data::num_store++);
  assert(n && n->in && n->out);
  if (n->in->storeInto(n->out,pi.lhs,pi.rhs.front())) { 
    STT(Data::dfg_change++);
  }
}

void SSaa::handleStore2(DFnode *n, PtrInst &pi)
{
  STT(Data::num_store2++);
  assert(n && n->in && n->out);
  if (n->in->storeInto2(n->out,pi.lhs,pi.rhs.front(),pi.off)) {
    STT(Data::dfg_change++);
  }
}

void SSaa::handleCall(DFnode *n)
{
  STT(Data::num_call++);
  assert(n && n->in && n->out);

  Function *cle = calledFunction(cast<CallInst>(n->pi.inst));
  assert(cle);

#ifdef FORW_FILT
  PtrInfo *filt = new PtrInfo(&ti,&vi);
  PtrInfo *diff = (n->out != n->in) ? n->out : 0;
  
  // collect roots for filtered binding (remember that for calls
  // pi.rhs is the set of pointer-related arguments)
  //
  bitmap roots(dfg[cle]->glob_roots);
  for (uv_it i = n->pi.rhs.begin(), e = n->pi.rhs.end(); i != e; ++i) {
    roots.set(*i);
  }
  
  n->in->filter(roots,filt,diff);
#else
  // if we're not filtering then we'll send all the local pointer
  // info to the callee. in this case we deliberately do not
  // propagate n->in into n->out because it will be propagated back
  // by the callee's return instruction
  //
  PtrInfo *filt = n->in;
#endif

  if (forwardBind(n,filt,cle)) { STT(Data::dfg_change++); }
  
#ifdef FORW_FILT
  delete filt;
#endif
}

bool SSaa::handleICall(DFnode *n)
{
  STT(Data::num_icall++);
  assert(n && n->in && n->out);

  bool c = false; // whether the top-level info changed
  vector<Function*> internal, external; // call targets
  u32 fp = vi[cast<CallInst>(n->pi.inst)->getCalledValue()]; // function ptr

  // compute the possible targets
  //
  for (PtrInfo::ptr_it j = ti.begin(fp), e = ti.end(fp); j != e; ++j) {
    Value *v = vi.inverse(*j);
    if (ART(v)) { continue; } // not a function

    Function *cle = dyn_cast<Function>(v);
    if (!cle) { continue; } // also not a function

    if (ext->is_ext(cle)) { external.push_back(cle); }
    else                     { internal.push_back(cle); }
  }

  // if we can't resolve the indirect call yet we don't propagate any
  // pointer info at all, trusting that eventually we'll get the info
  // we need to resolve the call (and if not, the program can't
  // progress past this point anyway)
  //
  if (external.empty() && internal.empty()) {
    STT(Data::icall_nores.insert(n));
    return false;
  }
  else { STT(Data::icall_res.insert(n)); }

  bool all_psv = true;
    
  if (!external.empty()) {
    CallInst *ci = cast<CallInst>(n->pi.inst);
    
    for (funv_it i = external.begin(), e = external.end(); i != e; ++i) {
      //
      // FIX: if we indirectly call an external function that is
      //      hasStatic() then we have a problem, because
      //      VarInfo::translate() didn't know that we needed the btm
      //      variables for this instruction that correspond to the
      //      hasStatic() function called; for now we just skip these
      //      calls (unsoundly)
      //
      if (ext->has_static(*i)) {
	STT(Data::idr_alloc.insert(*i));
	continue;
      }

      PtrInst p = ExtTrans::translate(ci,*i,&vi);
      
      switch (p.op) {
      case NOOP:   /* do nothing */        break;
      case ALLOC:  c |= handleAlloc(p);    break;
      case COPY:   c |= handleCopy(p);     break;
      case LOAD:   c |= handleLoad(n,p);   break;
      case STORE:       handleStore(n,p);  all_psv = false; break;
      case STORE2:      handleStore2(n,p); all_psv = false; break;
      default: assert(0 && "opcode not handled");
      }
    }
  }
  
  if (!internal.empty()) {
#ifdef FORW_FILT
    PtrInfo *filt = new PtrInfo(&ti,&vi);
    PtrInfo *diff = (n->out != n->in) ? n->out : 0;
    
    // collect roots for filtered binding (remember that for calls
    // pi.rhs is the set of pointer-related arguments)
    //      
    bitmap roots(glob_roots);
    for (uv_it i = n->pi.rhs.begin(), e = n->pi.rhs.end(); i != e; ++i) {
      roots.set(*i);
    }
    
    n->in->filter(roots,filt,diff);
#else
    // if we're not filtering then we'll send all the local pointer
    // info to the callee. in this case we deliberately do not
    // propagate n->in into n->out because it will be propagated back
    // by the callee's return instruction
    //
    PtrInfo *filt = n->in;
#endif
    
    bool change = false;

    for (funv_it i = internal.begin(), e = internal.end(); i != e; ++i) {
      DFinfo *ci = dfg.getInfo(*i);
      if (!ci) { continue; } // a preserving function
      else { all_psv = false; }

      if (!ci->cs.count(n)) { ci->new_cs.insert(n); }
      change |= forwardBind(n,filt,*i);
    }

    STT(if (!c && change) { Data::dfg_change++; });

#ifdef FORW_FILT
    delete filt;
#endif
  }

  // if the external calls were all LOAD and COPY and all the internal
  // calls were preserving then we need to propagate the pointer info
  // (note that this can lose precision if later this node does call
  // an external STORE[2] or non-preserving function, but since we
  // don't know whether this will happen better to play it safe)
  //
  // OPT: figure out how often this is done unnecessarily, and if it
  //      turns out to happen a lot figure out a better way
  //
  if (all_psv && n->out != n->in) {
    STT(Data::psv_icalls.insert(n));
    n->out->unite(n->in);
  }
  else { STT(if (Data::psv_icalls.count(n)) { Data::not_psv.insert(n); }); }
  
  return c;
}

void SSaa::handleRet(DFnode *n)
{
  STT(Data::num_ret++);
  assert(n && n->in);

  bool c = false;
  DFinfo *di = 0;
  u32 r = !n->pi.rhs.empty() ? n->pi.rhs[0] : 0; // retval

  // see DFG::functionDFG() for why the if/else is necessary
  //
  if (Instruction *I = dyn_cast<Instruction>(n->pi.inst)) {
    di = dfg[I->getParent()->getParent()];
  }
  else if (Function *F = dyn_cast<Function>(n->pi.inst)) { di = dfg[F]; }
  assert(di);

  // move new_cs over to cs
  //
  di->cs.insert(di->new_cs.begin(),di->new_cs.end());
  di->new_cs.clear();

  // propagate pointer info back to the callers
  //
  for (dfns_it i = di->cs.begin(), e = di->cs.end(); i != e; ++i) {
    c |= backwardBind(n,*i,r);
  }

  STT(if (c) { Data::dfg_change++; });

  n->in->rstc(n);
}

bool SSaa::forwardBind(DFnode *n, PtrInfo *p, Function *cle)
{
  bool change = false;
  DFinfo *di = dfg[cle];

  prm_it i = cle->arg_begin(), ie = cle->arg_end();
  uv_it k = n->pi.rhs.begin(), ke = n->pi.rhs.end();

  // compute the bindings between arguments and parameters (note that
  // the number of arguments and parameters may not match, due to
  // VarArgs and to indirect calls whose signatures don't match the
  // target signatures)
  //
  for ( ; i != ie && k != ke; ++i, ++k) {
    if (isa<PointerType>(i->getType()) && *k) {
      bool c = ti.copy(vi[i],*k);
      
      // if the parameter gets new info add it to the worklist
      //
      if (c) {
        change = true;
        DFnode *p = di->prms[vi[i]];
        assert(p);

        // the parameter node is just a noop; we actually want to add
        // its successors in the def-use graph
        //
        for (dfnv_it j = p->use_succ.begin(),e = p->use_succ.end();j != e;++j) {
          di->worklist.insert(*j,(*j)->topo);
        }
      }
    }
  }

  // propagate the filtered local pointer info to the callee's seg
  // root node; if it changes add it to the worklist
  //
  if (p && p != di->seg_root->in && di->seg_root->in->unite(p)) {
    change = true;
    di->worklist.insert(di->seg_root,di->seg_root->topo);
  }

  // if there was any change to the function's pointer info add the
  // function to the function worklist, also if this is a new
  // call-site even if the info hasn't changed
  //
  if (change || di->new_cs.count(n)) { fun_worklist.insert(cle,di->topo); }
  return change;
}

bool SSaa::backwardBind(DFnode *n, DFnode *clr, u32 ret)
{
  bool change = false;
  Function *cf = cast<Instruction>(clr->pi.inst)->getParent()->getParent();
  DFinfo *di = dfg[cf];

  // propagate the return value
  //
  if (ret && clr->pi.lhs && ti.copy(clr->pi.lhs,ret)) {
    change = true;
    for (dfnv_it k = clr->use_succ.begin(),e = clr->use_succ.end();k != e;++k) {
      di->worklist.insert(*k,(*k)->topo);
    }
  }

  PtrInfo *filt = n->in;

#ifdef BACK_FILT
  filt = new PtrInfo(&ti,&vi);

  // we don't know which global roots were used in the call (because
  // this function might have been called indirectly, which uses all
  // global roots), so we need to filter using all global roots just
  // in case
  //
  bitmap roots(glob_roots);
  if (ret) { roots.set(ret); }
  for (uv_it i = clr->pi.rhs.begin(), e = clr->pi.rhs.end(); i != e; ++i) {
    roots.set(*i);
  }
    
  n->in->filter(roots,filt,0);
#endif
  
  vector<PtrInfo*> seen;

  // same rationale for diff and nodiff here as in the main loop
  //
  for (dfnv_it k = clr->seg_succ.begin(),e = clr->seg_succ.end();k != e;++k) {
    assert(*k && (*k)->in);
    if ((*k)->in == filt) { continue; }

    if (!my_find<PtrInfo*>(seen,(*k)->in)) {
      (*k)->in->unite(filt);
      seen.push_back((*k)->in);
    }
    
    if ((*k)->in->changed(*k)) { 
      change = true;
      di->worklist.insert(*k,(*k)->topo);
    }
  }
  
#ifdef BACK_FILT
  delete filt;
#endif

  // if there was any change to the caller's pointer info add the
  // function to the function worklist
  //
  if (change) { fun_worklist.insert(cf,di->topo); }
  return change;
}

// print out the pointer info in ti, including all pointer-equivalent
// variables (requires Data::num_vars to be set by VarInfo)
//
void SSaa::printTop()
{
  for (u32 i = Data::num_btm; i < Data::num_vars; ++i) {
    dbgs() << i << " :";
    for (PtrInfo::ptr_it j = ti.begin(vi[i]), e = ti.end(vi[i]); j != e; ++j) {
      dbgs() << " " << *j;
    }
    dbgs() << "\n";
  }
}

void SSaa::listExtCalls(Module &M)
{
  set<GlobalValue*> glob;
  set<Function*> decl, intr;

  for (fmod_it i = M.begin(), e = M.end(); i != e; ++i) {
    if (i->isDeclaration()) { decl.insert(&*i); }
    else if (i->isIntrinsic()) { intr.insert(&*i); }
  }

  for (glob_it i = M.global_begin(), e = M.global_end(); i != e; ++i) {
    if (!i->hasInitializer()) { glob.insert(&*i); }
  }

  dbgs() << "number of intrinsic functions == " << intr.size() << "\n"
       << " number of declared functions == " << decl.size() << "\n"
       << "   number of declared globals == " << glob.size() << "\n";

  if (!intr.empty()) {
    dbgs() << "\n" << "INTRINSIC" << "\n" << "\n";
    for (funs_it i = intr.begin(), e = intr.end(); i != e; ++i) {
      if (isa<PointerType>((*i)->getReturnType())) { dbgs() << "(*) "; }
      else { 
        bool pts = false;

        for (prm_it j = (*i)->arg_begin(), e = (*i)->arg_end(); j != e; ++j) {
          if (isa<PointerType>(j->getType())) { pts = true; break; }
        }

        if (!pts) { dbgs() << "(-) "; }
        else { dbgs() << "    "; }
      }

      dbgs() << (*i)->getName() << "\n";
    }
  }

  if (!decl.empty()) {
    dbgs() << "\n" << "DECLARED FUNCTIONS" << "\n" << "\n";
    for (funs_it i = decl.begin(), e = decl.end(); i != e; ++i) {
      if (isa<PointerType>((*i)->getReturnType())) { dbgs() << "(*) "; }
      else { 
        bool pts = false;
	
        for (prm_it j = (*i)->arg_begin(), e = (*i)->arg_end(); j != e; ++j) {
          if (isa<PointerType>(j->getType())) { pts = true; break; }
        }

        if (!pts) { dbgs() << "(-) "; }
        else { dbgs() << "    "; }
      }

      dbgs() << (*i)->getName() << "\n";
    }
  }

  if (!glob.empty()) {
    dbgs() << "\n" << "DECLARED GLOBALS" << "\n" << "\n";
    for (gvs_it i = glob.begin(), e = glob.end(); i != e; ++i) {
      if (hasPtr((*i)->getType()->getContainedType(0))) { dbgs() << "(*) "; }
      else { dbgs() << "    "; }

      dbgs() << (*i)->getName() << "\n" ;
    }
  }
}
