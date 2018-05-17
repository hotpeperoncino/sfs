/*  [main.cpp] LLVM interface impl, some helper methods
 *  v. 014, 2008-09-14
 *------------------------------------------------------------------------------
 *  Changes from 013:
 *  - run_cleanup() merges remaining pointer-equivalent nodes
 *  - get_mem_usage() subtracts the initial data size
 *  - pointsToSet() supports offset
 *------------------------------------------------------------------------------
 *  Copyright 2008 Andrey Petrov
 *  - apetrov87@gmail.com, apetrov@cs.utexas.edu
 *
 *  Permission is hereby granted, free of charge, to any person
 *  obtaining a copy of this software and associated documentation
 *  files (the "Software"), to deal in the Software without
 *  restriction, including without limitation the rights to use, copy,
 *  modify, merge, publish, distribute, sublicense, and/or sell copies
 *  of the Software, and to permit persons to whom the Software is
 *  furnished to do so, subject to the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 *  HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 *  WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 *  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 *  DEALINGS IN THE SOFTWARE.
 *------------------------------------------------------------------------------
 */

#include "../include/anders.h"

//------------------------------------------------------------------------------
//Initialize all data before starting the run.
void Anders::run_init(Module *M){
  releaseMemory();
  curr_module= M;
  extinfo= new ExtInfo;
  if(USE_STATS){
    if(!stats)
      stats= (u32*)malloc(num_stats*4);
    //Clear stats before each run.
    memset(stats, 0, num_stats*4);
  }
}

//------------------------------------------------------------------------------
//Delete what the optimizations and solver won't need.
void Anders::pre_opt_cleanup(){
  struct_info.clear();
  gep_ce.clear();
  global_init_done.clear();
  stat_ret_node.clear();
  at_args.clear();
}

//------------------------------------------------------------------------------
//Delete anything not needed to get the analysis results.
void Anders::run_cleanup(){
  pre_opt_cleanup();
  curr_module= 0;
  constraints.clear();
  ind_calls.clear();
  icall_cons.clear();
  hcd_var.clear();
  off_mask.clear();
  ext_func_nodes= bddfalse;
  ext_func_node_set.clear();
  func_node_set.clear();
  if(extinfo){
    delete extinfo;
    extinfo= 0;
  }
  if(WL){
    delete WL;
    WL= 0;
  }
  lcd_edges.clear();
  lcd_starts.clear();
  lcd_dfs_id.clear();
  while(!lcd_stk.empty())
    lcd_stk.pop();
  lcd_roots.clear();
  ext_seen.clear();
  node_vars.clear();
  ext_failed.clear();
  cplx_cons.clear();
  //Delete the constraint graph and prev_points_to.
  FORN(i, nodes.size()){
    Node *N= nodes[i];
    N->prev_points_to= bddfalse;
    N->copy_to.clear();
    N->load_to.clear();
    N->store_from.clear();
    N->gep_to.clear();
  }
}

//------------------------------------------------------------------------------
//Delete the points-to sets not needed by the clients.
void Anders::pts_cleanup(){
  //BDD id -> first ptr-eq. node.
  hash_map<u32, u32> eq;

  FORN(i, nodes.size()){
    Node *N= nodes[i];
    if(N->obj_sz){
      //Skip Argument objects, which contain top-level pointers
      //  (i.e. the parameters used directly in the function body).
      //Note that an obj. node may have no value if it was merged into
      //  an artificial node.
      if(!N->get_val() || !isa<Argument>(N->get_val()))
        N->points_to= bddfalse;
    }

    if (N->points_to != bddfalse) {
      u32 idp= N->points_to.id();
      hash_map<u32, u32>::iterator j= eq.find(idp);
      if (j == eq.end()) { eq[idp] = i; }
      else { merge_nodes(get_node_rep(i),get_node_rep(j->second)); }
    }
  }
}

//------------------------------------------------------------------------------
//Return the current size of our data segment (in KB) minus baseline size,
//  by reading the line "VmData: # kB" from /proc/self/status.
//If (init) is 1, record the baseline.
u32 Anders::get_mem_usage(bool init) const{
  static u32 base= 0;
  u32 x= 0;
  ifstream in("/proc/self/status");
  while(in){
    string line, tag;
    getline(in, line);
    istringstream iss(line);
    iss>>tag;
    if(tag == "VmData:"){
      iss>>x;
      break;
    }
  }
  in.close();
  if(init){
    base= x;
    if(USE_MEM_TIME)
      fprintf(stderr, "Memory baseline: %u MB\n", (x+512)/1024);
  }
  return x - base;
}

//------------------------------------------------------------------------------
//Return the CPU time we have used so far, in microseconds.
u64 Anders::get_cpu_time() const{
#define MICRO(x) (x.tv_sec*1000000LL + x.tv_usec)
  static struct rusage r;

  getrusage(RUSAGE_SELF,&r);
  return (MICRO(r.ru_utime) + MICRO(r.ru_stime));
}

//------------------------------------------------------------------------------
//Print the CPU time used since start_time and reset start_time to now.
void Anders::print_time(const char *label){
  u64 t= get_cpu_time();
  u64 dt= t - start_time;
  fprintf(stderr, "Time for %s: %0.6f s\n", label, dt/1000000.0);
  start_time= t;
}

//------------------------------------------------------------------------------
//This is what LLVM calls to actually run the pass.
bool Anders::runOnModule(Module &M){
  DPUTS("***** Anders::runOnModule starting\n");
#if USE_PROFILER == 1
  ProfilerStart("/tmp/anders.prof");
#endif
  if(USE_MEM_TIME){
    start_time= get_cpu_time();
    //1 means init the baseline size (LLVM rather than our analysis)
    get_mem_usage(1);
  }
  run_init(&M);
  if(LIST_EXT_UNKNOWN)
    list_ext_unknown(M);
  obj_cons_id();
  //This is required for some of the optimizations.
  clump_addr_taken();
  if(USE_MEM_TIME)
    print_time("obj_cons_id");
  pre_opt_cleanup();

  if(!OCI_ONLY){
    cons_opt();
    if(USE_MEM_TIME){
      print_time("cons_opt");
      fprintf(stderr, "Memory used: %u MB\n", (get_mem_usage()+512)/1024);
    }
    if(!NO_SOLVE){
      pts_init();
      if(USE_MEM_TIME){
        print_time("pts_init");
        fprintf(stderr, "Memory used: %u MB\n", (get_mem_usage()+512)/1024);
      }
      solve_init();
      solve();
      if(USE_MEM_TIME){
        print_time("solve");
        fprintf(stderr, "Memory used: %u MB\n", (get_mem_usage()+512)/1024);
      }
      //points-to graph only, not sorted (sorting may run out of memory)
      if(DEBUG_SOLVE)
        DEBUG(print_cons_graph(1, 0));
    }
  }

  if(USE_STATS)
    print_stats();
  if(USE_METRICS)
    print_metrics();
  run_cleanup();
  pts_cleanup();
#if USE_PROFILER == 1
  ProfilerStop();
#endif
  DPUTS("***** Anders::runOnModule exiting\n");
  return 0;                           //module not changed
}

//------------------------------------------------------------------------------
//Delete all remaining data when our results are no longer needed.
void Anders::releaseMemory(){
  run_cleanup();
  FORN(i, nodes.size()){
    delete nodes[i];
    nodes[i]= 0;
  }
  nodes.clear();
  val_node.clear();
  obj_node.clear();
  ret_node.clear();
  vararg_node.clear();
  tmp_num.clear();
  pts_dom= bddfalse;
  if(gep2pts){
    bdd_freepair(gep2pts);
    gep2pts= 0;
  }
  geps.clear();
  _pb_free();
  if(stats){
    free(stats);
    stats= 0;
  }
  clear_bdd2vec();
  //We should not use bdd_done() here because the clients may still be
  //  using the BDD system.
}

//------------------------------------------------------------------------------
// Interface for the flow-sensitive analysis
//------------------------------------------------------------------------------

//Return the points-to set of node n, with offset off,
//  as a pointer to a vector in the cache.
const vector<u32>* Anders::pointsToSet(u32 n, u32 off){
  assert(n && n < nodes.size() && "node ID out of range");
  if(!off)
    return bdd2vec(nodes[get_node_rep(n)]->points_to);
  assert(off < geps.size() && geps[off] != bddfalse);
  bdd gep= bdd_replace(bdd_relprod(nodes[get_node_rep(n)]->points_to,
      geps[off], pts_dom), gep2pts);
  return bdd2vec(gep);
}

//Return the points-to set of V's node.
const vector<u32>* Anders::pointsToSet(Value* V, u32 off){
  return pointsToSet(get_val_node(V), off);
}

//Get the rep node of V, or MAX_U32 if it has no node.
u32 Anders::PE(Value* V){
  u32 n= get_val_node(V, 1);
  if(!n)
    return MAX_U32;
  return get_node_rep(n);
}

//Get the rep node of node n
u32 Anders::PE(u32 n){
  assert(n && n < nodes.size() && "node ID out of range");
  return get_node_rep(n);
}

bool Anders::is_null(u32 n, u32 off)
{
  assert(n && n < nodes.size() && "node ID out of range");
  bdd pts = nodes[get_node_rep(n)]->points_to;

  if (!off) { return (pts == bddfalse); }
  else {
    assert(off < geps.size() && geps[off] != bddfalse);
    bdd gep= bdd_replace(bdd_relprod(pts, geps[off], pts_dom), gep2pts);
    return (gep == bddfalse);
  }
}

bool Anders::is_single(u32 n, u32 off)
{
  assert(n && n < nodes.size() && "node ID out of range");
  bdd pts = nodes[get_node_rep(n)]->points_to;

  // !! is it faster to use bdd_satcountset or translate the bdd to a
  //    vector and count the size of the vector?

  if (!off) { return (bdd_satcountset(pts,pts_dom) == 1); }
  else {
    assert(off < geps.size() && geps[off] != bddfalse);
    bdd gep= bdd_replace(bdd_relprod(pts, geps[off], pts_dom), gep2pts);
    return (bdd_satcountset(gep,pts_dom) == 1);
  }
}

vector<bdd>& Anders::get_geps()
{
  return geps;
}
