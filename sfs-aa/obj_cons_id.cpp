// NOTES
//
// -- we assume that PRE's call-graph is precise, rather than worrying
//    about predicated control-flow edges due to indirect calls
//
// -- be aware that "Constraint& C = constraints[i]; ...;
//    add_cons(...);" can invalidate C if constraints[] gets re-sized
//
// TODO
//
// -- need to account for the fact that argv, envp, and some
//    uninitialized globals are actually initialized prior to program
//    execution
//
// -- should we run cons_opt after adding indirect ext stubs and
//    executing process_idr_cons? on the plus side, it might help us
//    find more equivalencies; on the minus side it makes cons_opt
//    inconsistent with PRE (the assert in cons_opt about PRE.PE fails)
//
// PERFORMANCE OPTS:
//
// -- construct a call-graph, collapsing SCCs; for each np/rq node,
//    record which SCC it belongs to. compute the transitive closure
//    and reverse transitive closure of the CG; for a set of functions
//    X let X_f be the forward reachable functions and X_b be the
//    backward reachable functions. when analyzing a partition, let NP
//    be the functions containing NP nodes and RQ be the functions
//    containing RQ nodes; intersect NP_f and RQ_b to find the
//    relevant functions for this partition. mark all non-relevant
//    function's start nodes as DEL, and use the start nodes of
//    relevant functions to begin SEG; once the SEG is computed only
//    restore nodes that are in relevant functions
//
//    the transitive closure operation doesn't seem too expensive, so
//    this may actually work

#include "sfs-aa.h"

namespace { // anon namespace for stuff local to this file

////////////////////////////////////////////////////////////////////////////////
//// TYPES

// a set class for SEG edges that makes changing the set
// implementation easier; the current version uses vectors
//
class EdgeSet
{
public:

  EdgeSet() {}

  void insert(u32 x) { S.push_back(x); }

  void erase(u32 x)
  {
    uv_it i = find(S.begin(),S.end(),x);
    if (i != S.end()) { *i = S.back(); S.pop_back(); }
  }

  void clear() { S.clear(); }

  bool has(u32 x) { return (find(S.begin(),S.end(),x) != S.end()); }

  bool empty() { return S.empty(); }

  u32 size() { return S.size(); }

  void destructive_copy(EdgeSet& rhs) { S.swap(rhs.S); rhs.S.clear(); }

  void unique()
  {
    std::sort(S.begin(),S.end());
    uv_it e = std::unique(S.begin(),S.end());
    S.erase(e,S.end());
  }

  bool operator==(const EdgeSet& rhs)
  {
    return (S == rhs.S);
  }

  void operator|=(const EdgeSet& rhs)
  {
    S.insert(S.end(),rhs.S.begin(),rhs.S.end());
  }

  void operator=(const EdgeSet& rhs) { S = rhs.S; }

  typedef uv_it set_it;
  typedef uv_cit set_cit;

  set_it begin() { return S.begin(); }
  set_it end()   { return S.end();   }

private:

  vector<u32> S;
};

typedef EdgeSet::set_it set_it;

// a node in the SEG
//
class SEGnode
{
public:

  bool np; // node is non-preserving
  bool r;  // node uses a relevant def
  bool c;  // node has a constant transfer function

  u32 rep; // set representative (> G.size() if node is the rep)

  u32 dfs;  // for tarjan's
  bool del; // "

  EdgeSet pred; // predecessors
  EdgeSet succ; // successors

  SEGnode(): np(false),r(false),c(false),rep(MAX_U32),dfs(0),del(false) {}
  SEGnode(bool _np): np(_np),r(false),c(false),rep(MAX_U32),dfs(0),del(false) {}
};

typedef map<BasicBlock*,u32>::iterator         bb2u_it;
typedef map<u32,vector<Function*> >::iterator  u2funv_it;
typedef vector<pair<CallInst*,u32> >::iterator cuv_it;

////////////////////////////////////////////////////////////////////////////////
//// GLOBALS

u32 dfs_num;        // for tarjans
stack<u32> node_st; // "

vector<SEGnode> G;   // the ICFG itself
u32 prog_start_node; // the program's initial SEG node

map<Function*,u32> fun_start;           // function -> start node
map<u32,vector<Function*> > fun_cs;     // callsite -> function targets
map<Function*,u32> fun_ret;             // function -> return node
map<u32,u32> call_succ;                 // callsite -> local successor
map<BasicBlock*,u32> bb_start;          // start nodes for BasicBlocks
vector<pair<CallInst*,u32> > idr_calls; // <idr call, callsite> pairs
vector<u32> idr_cons;                   // indices of constraints from idr calls
map<u32,vector<Function*> > tgts;       // fun ptr PRE rep -> internal targets

u32 num_tmp; // number of temporary vars created by process_idr_cons()

vector<u32> defs; //   store constraint -> node containing store
vector<u32> uses; //    load constraint -> node containing load

vector<u32> topo;     // topological number -> node, found by T4
vector<u32> rq;       // RQ nodes found by T4 for T6
vector<u32> not_nprq; // !NP && !RQ nodes found by T6 for T5
vector<u32> t5_reps;  // nodes made into reps by T5

map<u32,u32> pass_defs;          // node -> store for add_ssa_info
map<u32,u32> pass_node;          // node -> DFG index
map<u32,vector<u32> > pass_uses; // node -> loads for add_ssa_info

map<u32,vector<u32> > gv2n; // global var -> DFG init nodes

vector<u32> glob_init;  // global objects being initialized in a partition
vector<u32> cons_store; // store constraints for process_1{load,store}
vector<u32> cons_load;  // load constraints for process_1{load,store}

set<u32> cons_strong; // store constraints that are strong updates

map<u32,vector<u32> > cons_part; // constraint partitions
map<u32,bitmap> rel;             // obj -> constraint partitions

vector<bitmap> var_part; // access equivalence partition -> objects

map<u32,vector<u32> > n2p; // DFG node -> partitions
map<u32,bitmap> n2g;       // for sharing points-to graphs

////////////////////////////////////////////////////////////////////////////////
//// MACROS

#define NP(x)  (G[x].np)                     // is x non-preserving?
#define CN(x)  (G[x].c)                      // constant transfer fun?
#define RQ(x)  (G[x].r || (!CN(x) && NP(x))) // does x use a relevant def?

#define MAX_G  1000000000             // largest possible size of G
#define RPP(x) (G[x].rep > MAX_G)     // is x a set rep?
#define RNK(x) (MAX_U32 - G[x].rep)   // the rank of rep x
#define DEL(x) (!x || G[x].rep == 0)  // node has been deleted?
#define CHK(x) (x && x < G.size() &&\
                RPP(x) && !DEL(x))    // check index x is valid

////////////////////////////////////////////////////////////////////////////////
//// HELPER FUNCTIONS

u32 create_node(bool np = false)
{
  G.push_back(SEGnode(np)); assert(G.size() < MAX_G);
  return G.size()-1;
}

//// note that the following two edge functions are only for use when
//// constructing the initial ICFG; once nodes are merged together
//// they won't work correctly

void add_edge(u32 src, u32 dst)
{
  assert(CHK(src) && CHK(dst));
  if (src != dst) { G[dst].pred.insert(src); }
}

void erase_edge(u32 src, u32 dst)
{
  assert(CHK(src) && CHK(dst));
  G[dst].pred.erase(src);
}

void find_reach(u32 n, bitmap& vst)
{
  vst.set(n);
  FOREACH(set_it,i,G[n].succ) { if (!vst.test(*i)) { find_reach(*i,vst); }}
}

  inline
u32 find(u32 n)
{
  assert(n < G.size());

  u32 r = n;
  if (!RPP(n)) { G[n].rep = find(G[n].rep); r = G[n].rep; }

  return r;
}

// if !t2 && !t5 then we use union-by-rank, otherwise argument a is
// always the new rep
//
// !t2 && !t5: we must be in T4, in which case only the pred edges are
//             non-empty, so we only need to copy the pred edges
//
// t2: b will be the current node, a will be the predecessor; we know
//     that b's only pred edge is to a, so we don't have to copy any
//     edges (succ is empty)
//
// t5: b will be the current node, a will be the successor; we know
//     that b's only succ edge is to a, so the only edges we have to
//     copy are the pred edges
//
  inline
u32 unite(u32 a, u32 b, bool t2 = false, bool t5 = false)
{
  assert(CHK(a) && CHK(b));
  assert(!(NP(a) && NP(b)) && !(t2 && t5));

  if (a == b) { return a; }

  u32 ra = RNK(a), rb = RNK(b);

  if (!t2 && !t5) {
    if (ra < rb) { u32 t = a; a = b; b = t; }
    else if (ra == rb) { G[a].rep--; }
  }
  else if (ra < rb) { G[a].rep = (MAX_U32 - rb); } // a gets b's rank

  G[a].c  |= G[b].c;
  G[a].r  |= G[b].r;
  G[a].np |= G[b].np;

  if (!t2) { G[a].pred |= G[b].pred; }

  G[b].rep = a;  
  return a;
}

// get rid of redundant nodes and edges, updating defs[] and uses[]
//
// since this updates global data structures (ie, defs[] and uses[]),
// don't use it for the individual partition SEGs unless you save and
// then restore those data structures
//
void clean_G()
{
  u2u_it ii;
  u32 nn = 1; // 0 is reserved to detect errors
  map<u32,u32> redir;
  vector<SEGnode> newG;

  FOR1N(i,G.size()) { if (RPP(i) && !DEL(i)) { redir[i] = nn++; }}
  newG.assign(nn,SEGnode());

  FOREACH(u2u_it,i,redir) {
    SEGnode& N = G[i->first];
    SEGnode& X = newG[i->second];

    FOREACH(set_it,j,N.pred) {
      u32 p = find(*j);
      if (p == i->first) { continue; }
      if ((ii = redir.find(p)) != redir.end()) { X.pred.insert(ii->second); }
    }
    X.pred.unique();
  }

  ii = redir.find(find(prog_start_node)); assert(ii != redir.end());
  prog_start_node = ii->second;

  FOREACH(uv_it,i,defs) {
    // note that we can get defs whose nodes were deleted by T6
    // because of CN; these are set to 0 by the else branch
    //
    if (*i && (ii = redir.find(find(*i))) != redir.end()) { *i = ii->second; }
    else { *i = 0; }
  }

  FOREACH(uv_it,i,uses) {
    // note that we can get uses whose nodes were deleted by
    // rm_undef(); these are set to 0 by the else branch
    //
    if (*i && (ii = redir.find(find(*i))) != redir.end()) { *i = ii->second; }
    else { *i = 0; }
  }

  // do this last because find() uses G
  //
  G.swap(newG);
}

void print_seg(const string& file, bool app = false)
{
  ofstream out;

  if (app) { out.open(file.c_str(),ios_base::app);   }
  else     { out.open(file.c_str(),ios_base::trunc); }

  out << "strict digraph SEG {" << "\n";

  FOR1N(i,G.size()) {
    if (!RPP(i) || DEL(i)) { continue; }

    out << "\t" << i << " [label=\"";

    out << i << ":";
    if (NP(i)) { out << "DEF"; }
    if (RQ(i)) { if (NP(i)) { out << "_"; } out << "USE"; }

    out << "\"";
    if (i == find(prog_start_node)) { out << ",color=red"; }
    out << "];" << "\n";

    FOREACH(set_it,j,G[i].pred) {
      u32 p = find(*j);
      if (p == i || DEL(p)) { continue; }

      out << "\t" << p << " -> " << i << ";" << "\n";
    }
  }

  out << "}" << "\n";
  out.close();
}

// squeeze the two arguments into a single u32, and unsqueeze them again
//
map<pair<u32,u32>,u32> sq_map;
map<u32,pair<u32,u32> > sq_unmap;
typedef map<pair<u32,u32>,u32>::iterator up2u_it;
typedef map<u32,pair<u32,u32> >::iterator u2up_it;
u32 squeeze(u32 p, u32 o, bool save = false)
{
  static u32 idx = 1;
  pair<u32,u32> x(p,o);

  up2u_it i = sq_map.find(x);
  if (i == sq_map.end()) {
    sq_map[x] = idx++; assert(idx < MAX_U32);
    if (save) { sq_unmap[idx-1] = x; }
    return idx-1;
  }
  else { return i->second; }
}
pair<u32,u32> unsqueeze(u32 n) 
{ 
  u2up_it i = sq_unmap.find(n);
  assert(i != sq_unmap.end());
  return i->second;
}

////////////////////////////////////////////////////////////////////////////////
//// SEG functions

// collapse p-nodes with singleton predecessors in topological order
// (w.r.t. p-nodes)
//
void T2()
{
  FOREACH(uv_it,i,topo) {
    if (DEL(*i)) { continue; } // may have been deleted by rm_undef()

    u32 n = find(*i);
    SEGnode& N = G[n];

    // pred may have non-reps (though no self-edges), therefore we
    // need to look through all the elements
    //
    u32 p = 0;
    bool mult = false;

    FOREACH(set_it,j,N.pred) {
      u32 x = find(*j); assert(x != n && CHK(x));

      if (!p) { p = x; }
      else if (p != x) { mult = true; break; }
    }

    // signal unite() this is for T2, ensure that p is the new rep
    //
    if (!mult && p) { unite(p,n,true); assert(RPP(p)); }
  }
}

inline
void t4_visit(u32 n)
{
  assert(CHK(n));

  SEGnode& N = G[n];
  u32 my_dfs = dfs_num++;

  N.dfs = my_dfs;

  FOREACH(set_it,i,N.pred) {
    u32 p = find(*i); assert(CHK(p));

    if (NP(p)) { continue; }
    SEGnode& P = G[p];

    if (!P.del) {
      if (!P.dfs) { t4_visit(p); }
      if (N.dfs > P.dfs) { N.dfs = P.dfs; }
    }
  }

  if (my_dfs == N.dfs) {
    while (!node_st.empty() && G[node_st.top()].dfs >= my_dfs) {
      n = unite(n,node_st.top());
      node_st.pop();
    }

    topo.push_back(n);
    G[n].del = true;
  }
  else { node_st.push(n); }  
}

// collapse p-node SCCs and topologically number them
//
void T4()
{
  dfs_num = 1;

  rq.clear();
  topo.clear();

  FOR1N(i, G.size()) {
    if (RPP(i)) {
      if (!NP(i) && !G[i].dfs) { t4_visit(i); }

      if (RPP(i)) { // this includes NP nodes, which t4_visit doesn't
        G[i].del = true; // T6 assumes all rep nodes have del == true
        if (RQ(i)) { rq.push_back(i); } // save RQ nodes for T6
      }
    }
  }

  assert(node_st.empty());
}

inline
void t5_visit(u32 n)
{
  assert(CHK(n) && !NP(n) && !RQ(n));

  SEGnode& N = G[n];
  N.dfs = 0;

  FOREACH(set_it,i,N.succ) {
    u32 s = find(*i); assert(CHK(s) && s != n);
    if (!NP(s) && !RQ(s) && G[s].dfs) { t5_visit(s); assert(RPP(n)); }
  }

  u32 s = 0;
  bool mult = false;

  FOREACH(set_it,i,N.succ) {
    u32 x = find(*i); assert(CHK(x) && x != n);

    if (!s) { s = x; }
    else if (s != x) { mult = true; break; }
  }

  // signal unite() this is for T5, ensure that s is the new rep
  //
  if (!mult && s) {
    t5_reps.push_back(s);
    unite(s,n,false,true); assert(RPP(s));
  }
}

// collapse up-nodes with singleton successors in reverse topological
// order (w.r.t. up-nodes); we'll use dfs to mark visited nodes: T4
// set all p-nodes' dfs > 0, so dfs == 0 will indicate a visited node
//
void T5()
{
  t5_reps.clear();

  // not_nprq used to only contain !NP && !RQ nodes, but because of
  // node merges we have to re-check here
  //
  FOREACH(uv_it,i,not_nprq) {
    u32 n = find(*i);
    if (!DEL(n) && !NP(n) && !RQ(n) && G[n].dfs) { t5_visit(n); }
  }
}

inline
void t6_visit(u32 n, bool t7 = false)
{
  assert(CHK(n));

  SEGnode& N = G[n];
  N.del = false;

  // save !NP && !RQ nodes for T5
  //
  if (!NP(n) && !RQ(n)) { not_nprq.push_back(n); }

  if (t7 && CN(n)) { return; }

  FOREACH(set_it,i,N.pred) {
    u32 p = find(*i);

    if (p != n && !DEL(p)) {
      assert(CHK(p));

      if (G[p].del) { t6_visit(p); }
      if (!NP(p) && !RQ(p)) { G[p].succ.insert(n); }
    }
  }
}

// mark nodes that are not backward-reachable from a requiring node as
// DEL; also fill in succ info for the !NP && !RQ nodes
//
void T6(bool t7 = false)
{
  not_nprq.clear();

  FOREACH(uv_it,i,rq) {
    if (DEL(*i)) { continue; }

    u32 n = find(*i);
    if (G[n].del) { t6_visit(n,t7); }
  }

  FOR1N(i,G.size()) { if (G[i].del) { G[i].rep = 0; }}
}

// remove p-nodes that are not reachable from an m-node (not an
// official SEG transformation, but still useful); assumes that this
// is after T4 and before T2
//
void rm_undef()
{
  EdgeSet pred;

  FOREACH(uv_it,i,topo) {
    assert(CHK(*i) && !NP(*i));
    SEGnode& N = G[*i];

    FOREACH(set_it,j,N.pred) {
      u32 p = find(*j);
      if (!DEL(p) && p != *i) { pred.insert(p); }
    }

    if (!pred.empty()) {
      N.pred.destructive_copy(pred);
      continue;
    }

    // not reachable; delete node
    //
    N.rep = 0;
  }
}

// compute the SEG using the above transformations (from ramalingam's
// paper 'on sparse evaluation representations')
//
void SEG(bool first = false)
{
  assert(!NP(0) && !RQ(0)); // index 0 reserved to detect errors

  // INVARIANTS:
  //
  // [NOTE: 'exact' means each dest node of an edge is RPP, !DEL, and
  //        different from the source node]
  //
  // - forall N : 
  //      RPP, !DEL
  //      dfs = 0; del = F
  //      pred filled in, exact
  //      succ empty
  //
  // - global ds : topo, cn, rq, not_nprq empty

  T4();

  // INVARIANTS:
  //
  // - forall RPP :
  //      !DEL
  //      !NP => dfs > 0; del = T
  //      pred filled in, not exact
  //      succ empty
  //
  // - global ds : topo, cn, rq filled in

  // before T2 we want to remove any p-nodes that are not reachable
  // from an m-node
  //
  rm_undef();

  // INVARIANTS:
  //
  // - forall RPP, !DEL :
  //      !NP => dfs > 0; del = T
  //      pred exact unless NP
  //      succ empty
  //
  // - global ds : topo, rq may have deleted nodes, otherwise the same

  T2();

  // INVARIANTS:
  //
  // - forall RPP, !DEL :
  //      !NP => dfs > 0; del = T
  //      pred not exact but !NP => no self-edges, no DEL
  //      succ empty
  //
  // - global ds : topo invalid, otherwise the same

  // INVARIANTS: cn dead, otherwise the same

  T6(!first);

  // INVARIANTS:
  //
  // - forall RPP, !DEL :
  //      !NP => dfs > 0; del = F
  //      pred not exact but !NP => no self-edges, no DEL
  //      !NP && !RQ => succ filled in, exact
  //
  // - global ds : rq dead, not_nprq filled in, otherwise the same

  T5();

  // INVARIANTS:
  //
  // - forall RPP, !DEL :
  //      dfs = 0; del = F
  //      pred not exact but !NP => no self-edges, no DEL
  //      !NP && !RQ => succ not exact but no self-edges, no DEL
  //
  // - global ds : topo, cn, rq, not_nprq all dead
}

} // end anon namespace

////////////////////////////////////////////////////////////////////////////////
//// METHODS

// create the data structures used by the solver: constraint list,
// nodes, etc
//
void SFS::sfs_id()
{
  assert(G.empty());
  
  create_node(); // index 0 is reserved to detect errors
  prog_start_node = create_node(true); // NP for initializing globals

  // create the list of constraints; also construct the ICFG (except
  // for indirect and interprocedural edges)
  //
  obj_cons_id();

  // renumber val_node and obj_node to be consistent with Anders so we
  // can use PRE's results to compute the SSA info
  //
  clump_addr_taken();

  // we don't need the following data structured filled in by
  // obj_cons_id
  //
  ret_node.clear();
  vararg_node.clear();

  // check that we have the same {val,obj}_node as PRE; this only
  // works if Anders changes its protected data to public so we can
  // access it here
  //
#if 0
  {
    typedef DenseMap<Value*,u32>::iterator v2u_it;
    FOREACH(v2u_it,i,val_node) {
      assert(PRE.val_node[i->first] == i->second);
    }
    FOREACH(v2u_it,i,obj_node) {
      assert(PRE.obj_node[i->first] == i->second);
    }
  }
#endif

  // clean up unneeded data
  //
  pre_opt_cleanup();
  if (USE_MEM_TIME) {
    print_time("ocs/clump_addr");
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }

  // compute PRE info
  //
  PRE.runOnModule(*curr_module);
  if (USE_MEM_TIME) {
    print_time("PRE");
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }

  // optimize the constraints
  //
  cons_opt_wrap();

  // add interprocedural edges to the ICFG
  //
  icfg_inter_edges();

  // we can go ahead and process the constraints from indirect calls
  // now; we needed tgts filled in (by icfg_inter_edges) but we don't
  // need the SEG
  //
  process_idr_cons();

  // at this point we've added all the constraints we're going to add
  // and deleted all the constraints we're going to delete; now we
  // move everything into the SFS data structures
  //
  sfs_prep();

  // create the initial SEG, where all stores are non-preserving for
  // all address-taken variables and all loads use all address-taken
  // variables; then clean G by getting rid of redundant nodes and edges
  //
  SEG(true); if (USE_MEM_TIME) { print_time("initial SEG"); }
  clean_G(); if (USE_MEM_TIME) { print_time("clean_G");     }

  if (false && USE_STATS) {
    FOR1N(i,G.size()) {
      FOREACH(set_it,j,G[i].pred) { G[*j].succ.insert(i); }
    }

    map<u32,bitmap> reaches, v2n;
    find_reach(prog_start_node,reaches[0]);

    FORN(i,defs.size()) {
      if (!defs[i]) { continue; }
      find_reach(defs[i],reaches[i]);
    }

    FOREACH(u2bm_it,i,reaches) {
      if (!i->first) { continue; }
      Constraint& C = dfg.node_cons(dfg.st_idx(i->first,true));
      const vector<u32>& pts = *(PRE.pointsToSet(C.dest,C.off));
      FOREACH(uv_cit,j,pts) { v2n[*j] |= i->second; }
    }

    FOREACH(u2uv_it,i,gv2n) { v2n[i->first] |= reaches[0]; }

    u32 tot = 0;
    FOREACH(u2bm_it,i,v2n) { tot += i->second.count(); }

    errs() << "avg edges/var == " << (double)tot/v2n.size() << "\n";

    FOR1N(i,G.size()) { G[i].succ.clear(); }
  }

  // partition the variable into access equivalence classes
  //
  partition_vars();

  // we're done with PRE now
  //
  PRE.releaseMemory();

  // compute the SEG for each variable partition
  //
  compute_seg();
}

// override Anders::visit_func (called by obj_cons_id) so we can
// create the ICFG and map the load and store constraints to the
// appropriate ICFG nodes, in order to later compute the SSA
// information
//
// VITALLY IMPORTANT: we *must* ensure the same mapping from Value*
// for value and object nodes as used by PRE (in this case, Anders),
// otherwise we can't use PRE's points-to results
//
void SFS::visit_func(Function *F)
{
  //First make nodes for all ptr-return insn
  //  (since trace_int may sometimes return values below the current insn).
  for(inst_iterator it= inst_begin(F), ie= inst_end(F); it != ie; ++it){
    Instruction *I= &*it;
    if(isa<PointerType>(I->getType())){
      nodes.push_back(new Node(I));
      val_node[I]= next_node++;
    }
  }

  // insert entries for the global constraints into defs and uses
  // (this only needs to happen once, after obj_cons_id creates the
  // global constraints, but we insert the check here rather than
  // override obj_cons_id for something this trivial)
  //
  if (defs.empty() && uses.empty()) {
    defs.assign(constraints.size(),0);
    uses.assign(constraints.size(),0);
  }

  processBlock(MAX_U32,&F->getEntryBlock());
  bb_start.clear();

  // we don't actually need all of the things created by the various
  // *_id() methods, we're just using them to create the constraints
  //
  ind_calls.clear();
  icall_cons.clear();
}

void SFS::processBlock(u32 parent, BasicBlock *BB)
{
  // if we've seen this BasicBlock before, just fill in the successors
  // and predecessors appropriately and return
  //
  bb2u_it bbs = bb_start.find(BB);

  if (bbs != bb_start.end()) {
    assert(parent != MAX_U32);
    add_edge(parent,bbs->second);
    return;
  }

  // create a start node for this BasicBlock and fill in bb_start; if
  // this is the start node for the function containing this
  // BasicBlock then fill in fun_start
  //
  u32 n = create_node();
  bb_start[BB] = n;

  if (parent != MAX_U32) { add_edge(parent,n); }
  else {
    Function *F = BB->getParent();
    assert(!fun_start.count(F));
    fun_start[F] = n;
  }

  u32 cons_sz = constraints.size();
  bool block_call = false; // does this BasicBlock contain a call?

  // iterate through the instructions in this basic block; translate
  // the instructions to constraints, create the appropriate nodes for
  // the ICFG, and mark non-preserving and requiring nodes
  //
  for(ibb_it it = BB->begin(), e = BB->end(); it != e; ++it) {
    Instruction *I= &*it;
    bool is_ptr= isa<PointerType>(I->getType());

    u32 curr_cons = cons_sz;
    bool call = false, load = false, store = false; // relevant instructions

    switch(I->getOpcode()){
    case Instruction::Ret:
      assert(!is_ptr);
      id_ret_insn(I);

      // if there was a call in this BasicBlock prior to the return
      // instruction, we create a new node just for the return
      // instruction so the callsite will have a successor for the
      // interprocedural edges added later
      //
      if (block_call) {
        u32 next = create_node();
        add_edge(n,next); n = next;
      }
      assert(!fun_ret.count(BB->getParent()));
      fun_ret[BB->getParent()] = n;
      break;
    case Instruction::Invoke:
    case Instruction::Call:
      call = true;
      id_call_insn(I);
      break;
      //    case Instruction::Malloc:
    case Instruction::Alloca:
      assert(is_ptr);
      id_alloc_insn(I);
      break;
    case Instruction::Load:
      if (is_ptr) { load = true; id_load_insn(I); }
      break;
    case Instruction::Store:
      assert(!is_ptr);
      store = true;
      id_store_insn(I);
      break;
    case Instruction::GetElementPtr:
      assert(is_ptr);
      id_gep_insn(I);
      break;
    case Instruction::IntToPtr:
      assert(is_ptr);
      id_i2p_insn(I);
      break;
    case Instruction::BitCast:
      if (is_ptr) id_bitcast_insn(I);
      break;
    case Instruction::PHI:
      if (is_ptr) id_phi_insn(I);
      break;
    case Instruction::Select:
      if (is_ptr) id_select_insn(I);
      break;
    case Instruction::VAArg:
      if (is_ptr) id_vaarg_insn(I);
      break;
    default:
      assert(!is_ptr && "unknown insn has a pointer return type");
    }

    cons_sz = constraints.size();
    if (cons_sz == curr_cons && !call) { continue; }

    defs.insert(defs.end(),cons_sz-curr_cons,0);
    uses.insert(uses.end(),cons_sz-curr_cons,0);

    assert(defs.size() == constraints.size());
    assert(uses.size() == constraints.size());

    if (call) { // fill in interprocedural info
      if (Function *F = calledFunction(cast<CallInst>(I))) { // direct call
        if (extinfo->is_ext(F)) { // external call
          // see how many stores were added
          //
          u32 num_stores = 0;
          for (u32 i = curr_cons; i < cons_sz; ++i) {
            if (constraints[i].type == store_cons) { num_stores++; }
          }

          // memcpy/move, etc can create multiple loads and stores; we
          // want to treat each load/store pair in parallel, so we
          // create separate nodes for each pair and create a
          // "diamond" in the CFG -- we are aided by the fact that the
          // constraint generator placed the related pairs of
          // constraints in sequence: <load,store>, <load,store>, ...
          //
          if (num_stores > 1) {
            u32 b = create_node(); // the bottom of the diamond

            for (u32 i = 0; i < num_stores*2; i += 2) {
              assert(constraints[curr_cons+i].type == load_cons);
              assert(constraints[curr_cons+i+1].type == store_cons);

              u32 next = create_node(true);
              G[next].r = true;
              add_edge(n,next); add_edge(next,b);
              uses[curr_cons+i] = next;
              defs[curr_cons+i+1] = next;
            }

            n = b;
          }
          else {
            if (num_stores == 1) {
              if (!NP(n)) { G[n].np = true; }
              else {
                u32 next = create_node(true);
                add_edge(n,next); n = next;
              }
            }
            
            // map any loads and stores to the ICFG node
            //
            for (u32 i = curr_cons; i < cons_sz; ++i) {
              Constraint& C = constraints[i];
              
              if (C.type == store_cons) { defs[i] = n; }
              else if (C.type == load_cons)  { G[n].r = true; uses[i] = n; }
            }
          }
        }
        else { // direct call
          block_call = true;
          fun_cs[n].push_back(F);

          // guarantee a single successor for the callsite
          //
          assert(!call_succ.count(n));
          u32 next = create_node();
          call_succ[n] = next;
          add_edge(n,next); n = next;
        }
      }
      else { // indirect call
        CallInst *ci = cast<CallInst>(I);
        if (isa<InlineAsm>(ci->getCalledValue())) { continue; }

        u32 fp = get_val_node(ci->getCalledValue(),true);
        if (fp) {
          block_call = true;

          // we can process loads and stores from indirect calls
          // directly without computing SSA form, since the objects in
          // question are, by construction, already in SSA form; we
          // save these constraints to process later
          //
          for (u32 i = curr_cons; i < cons_sz; ++i) { idr_cons.push_back(i); }

          // we also save the indirect call inst and current node so
          // we can add the interprocedural control-flow edges later,
          // as well as process indirect external calls
          //
          idr_calls.push_back(std::make_pair((CallInst*)ci,(u32)n));

          // make sure call inst has an associated object node
          //
          assert(!get_val_node(ci,true) || get_obj_node(ci));

          // guarantee a single successor for the callsite
          //
          assert(!call_succ.count(n));
          u32 next = create_node();
          call_succ[n] = next;
          add_edge(n,next); n = next;
        }
      }
    }
    else if (load) { // requiring node
      G[n].r = true;

      // there may have been multiple constraints added, but there
      // will be exactly one load constraint
      //
      for (u32 i = curr_cons; i < cons_sz; ++i) {
        if (constraints[i].type == load_cons) { uses[i] = n; break; }
      }
    }
    else if (store) { // non-preserving node
      if (!NP(n)) { G[n].np = true; }
      else {
        u32 next = create_node(true);
        add_edge(n,next); n = next;
      }

      // there may have been multiple constraints added, but there
      // will be exactly one store constraint
      //
      for (u32 i = curr_cons; i < cons_sz; ++i) {
        Constraint& C = constraints[i];
        if (C.type == store_cons) { defs[i] = n; break; }
      }
    }
  }

  // now process each of this BasicBlock's successors
  //
  for (succ_iterator i = succ_begin(BB), e = succ_end(BB); i != e; ++i) {
    processBlock(n,*i);
  }
}

// optimize the constraints before we start adding the new variables
// and constraints for the SFS analysis; this invalidates idr_cons[],
// defs[], and uses[] so we need to fix them up afterwards: redir maps
// the old constraint index to the new index, or MAX_U32 if the
// constraint has been deleted
//
void SFS::cons_opt_wrap()
{
  vector<u32> redir;
  cons_opt(redir);

  vector<u32> new_idr;

  FOREACH(uv_it,i,idr_cons) {
    if (redir[*i] != MAX_U32) { new_idr.push_back(redir[*i]); }
  }
  std::sort(new_idr.begin(),new_idr.end());
  uv_it e = std::unique(new_idr.begin(),new_idr.end());
  new_idr.erase(e,new_idr.end());

  idr_cons.swap(new_idr);
  new_idr.clear();

  if (USE_DEBUG) {
    FOREACH(uv_it,i,idr_cons) {
      Constraint& C = constraints[*i];
      assert(C.type == load_cons || C.type == store_cons);
    }
  }

  vector<u32> new_defs(defs.size()), new_uses(uses.size());

  FORN(i,defs.size()) {
    if (defs[i] && redir[i] != MAX_U32) { new_defs[redir[i]] = defs[i]; }
    if (uses[i] && redir[i] != MAX_U32) { new_uses[redir[i]] = uses[i]; }
  }

  defs.swap(new_defs);
  uses.swap(new_uses);

  if (USE_DEBUG) {
    FORN(i,defs.size()) {
      assert(!defs[i] || constraints[i].type == store_cons);
      assert(!uses[i] || constraints[i].type == load_cons);
    }
  }

  redir.clear();
  new_defs.clear();
  new_uses.clear();

  if (USE_MEM_TIME) {
    print_time("cons_opt"); 
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }
}

// add interprocedural edges from direct and indirect calls to the ICFG
//
void SFS::icfg_inter_edges()
{
  // insert the program start node before main's start node
  //
  Function *main = curr_module->getFunction("main");
  assert(main && fun_start.count(main) && fun_start[main] < G.size());
  add_edge(prog_start_node,fun_start[main]);

  // process indirect calls to add interprocedural ICFG edges (we
  // couldn't do it before now because we have to have completed
  // obj_cons_id and clump_addr_taken before we can use PRE's results)
  //
  set<u32> has_ext, is_alloc;
  map<u32,pair<u32,u32> > factor;

  FOREACH(cuv_it,i,idr_calls) {
    CallInst *ci = i->first;
    u32 n = i->second;

    assert(call_succ.count(n));
    u32 succ = call_succ[n];

    u32 fp = get_val_node(ci->getCalledValue());
    u32 rep = PRE.PE(fp);
    bool seen = tgts.count(rep);

    // cache set of internal targets for each function pointer PE rep,
    // as well as whether it points to any external targets
    //
    if (!seen) {
      vector<Function*>& ffp = tgts[rep];

      FOREACH(uv_cit,j,(*PRE.pointsToSet(rep))) {
        Function *cle = dyn_cast_or_null<Function>(nodes[*j]->get_val());
        if (!cle) { continue; }
        
        if (extinfo->is_ext(cle)) {
          has_ext.insert(rep);
          if (extinfo->is_alloc(cle)) { is_alloc.insert(rep); }
          // currently we only handle indirect allocs for external stubs
        }
        else { ffp.push_back(cle); }
      }

      std::sort(ffp.begin(),ffp.end());
      funv_it e = std::unique(ffp.begin(),ffp.end());
      ffp.erase(e,ffp.end());

      // factor the edges for indirect calls: all the indirect calls
      // using rep will point to cll, and all the target functions
      // will return to ret
      //
      u32 cll = create_node();
      u32 ret = create_node();

      FOREACH(funv_it,j,ffp) {
	add_edge(cll,fun_start[*j]);
	if (fun_ret.count(*j)) { add_edge(fun_ret[*j],ret); }	
      }

      factor[rep] = pair<u32,u32>(cll,ret);
    }

    if (is_alloc.count(rep) && get_val_node(ci,true)) {
      u32 src = get_obj_node(ci);
      u32 dest = get_val_node(ci);
      add_cons(addr_of_cons, dest, src, 0);
    }

    assert(factor.count(rep));
    pair<u32,u32>& fact = factor[rep];

    add_edge(n,fact.first);
    add_edge(fact.second,succ);

    // indirect external calls mean that control can pass straight
    // from the call to the local successors of the callsite,
    // otherwise control goes via the callee
    //
    if (!has_ext.count(rep)) { erase_edge(n,succ); }
  }

  // these are dead now
  //
  has_ext.clear();
  is_alloc.clear();
  idr_calls.clear();

  // add the interprocedural edges from direct calls to the ICFG by
  // replacing the intraprocedural edges between a call node and its
  // local successors with edges between the call node and the callee
  // entry node and between the callee return node and the call node's
  // local successors
  //
  FOREACH(u2funv_it,i,fun_cs) {
    u32 clr = i->first; // call node
    vector<Function*>& fun = i->second;

    // the callsite's local successor
    //
    assert(call_succ.count(clr));
    u32 succ = call_succ[clr];
    erase_edge(clr,succ);

    FOREACH(funv_it,j,fun) {
      assert(fun_start.count(*j));
      add_edge(clr,fun_start[*j]);
      if (fun_ret.count(*j)) { add_edge(fun_ret[*j],succ); }
    }
  }

  // these are dead now
  //
  fun_cs.clear();
  fun_ret.clear();
  fun_start.clear();
  call_succ.clear();

  if (USE_MEM_TIME) { 
    print_time("icfg_inter_edges"); 
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }
}

// we take advantage of our assumption that the call-graph computed by
// PRE is precise by making these real edges rather than predicated
//
void SFS::process_idr_cons()
{
  // map <fp,off> -> tmp var
  //
  map<pair<u32,u32>,u32> tmps;
  typedef map<pair<u32,u32>,u32>::iterator up2u_it;
  
  vector<Constraint> new_cons;
  
  FOREACH(uv_it,i,idr_cons) {
    Constraint& C = constraints[*i];
    u32 fp = 0, cle = 0, tv = 0, el = 0, *src_p = 0, *dst_p = 0;
    
    // assume we don't pass a non-pointer arg to a pointer formal
    //
    if (C.src == p_i2p) { continue; }
    
    if (C.type == store_cons) { 
      assert(C.off > 1);
      fp = PRE.PE(C.dest); src_p = &tv; dst_p = &el;
    }
    else { 
      assert(C.type == load_cons && C.off == 1);
      fp = PRE.PE(C.src); src_p = &el; dst_p = &tv;
    }
    
    // we're going to factor the edges from indirect calls using
    // top-level variables created specifically for this purpose
    // (note that we don't actually create a Node for the new var)
    
    pair<u32,u32> p(fp,C.off);
    up2u_it j = tmps.find(p);
    
    if (j == tmps.end()) {
      tv = next_node++; num_tmp++;
      tmps[p] = tv;

      assert(tgts.count(fp));
      vector<Function*>& callees = tgts[fp];

      FOREACH(funv_it,j,callees) {
        cle = get_obj_node(*j);
        assert(isa<Function>(nodes[cle]->get_val()));
        
        if (nodes[cle]->obj_sz > C.off) {
          el = cle + C.off;
          
          // eliminate edges from pointer arguments to non-pointer formals
          //
          if (C.off > 1 && !isa<PointerType>(nodes[el]->get_val()->getType()))
            continue;

          new_cons.push_back(Constraint(copy_cons,*dst_p,*src_p,0));
        }
      }
    }
    else { tv = j->second; }
    
    if (C.off == 1) { src_p = &tv; dst_p = &C.dest; }
    else            { src_p = &C.src; dst_p = &tv;  }
    
    new_cons.push_back(Constraint(copy_cons,*dst_p,*src_p,0));
  }

  // unique the new constraints and add them to constraints[]
  //
  std::sort(new_cons.begin(),new_cons.end());
  vector<Constraint>::iterator e = std::unique(new_cons.begin(),new_cons.end());
  constraints.insert(constraints.end(),new_cons.begin(),e);

  // mark the constraints for deletion (we don't need to update
  // defs[], uses[], or the SEG nodes because the constraints from
  // indirect calls were never used for them).
  //
  FOREACH(uv_it,i,idr_cons) { constraints[*i].off = MAX_U32; }

  // these are dead now
  //
  tgts.clear();
  idr_cons.clear();

  if (USE_MEM_TIME) { 
    print_time("process_idr_cons");
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }
}

// move everything from the Anders data structures to the SFS data
// structures
//
void SFS::sfs_prep()
{  
  top.assign(nodes.size()+num_tmp,PtsSet()); // top-level var -> ptsto set

  strong.assign(last_obj_node+1,false); // object -> strong?
  FORN(i,last_obj_node+1) { strong[i] = !nodes[i]->weak; }

  // BDD globals (grab geps from Anders)
  //
  pdom = fdd_ithset(0);
  g2p = bdd_newpair();
  fdd_setpair(g2p,1,0);
  bdd_off = PRE.get_geps();

  // we're done with nodes[]
  //
  FORN(i,nodes.size()) { if (nodes[i]) { delete nodes[i]; }}
  nodes.clear();

  // now translate constraints[], remembering that some have been
  // marked for deletion by setting their off to MAX_U32; we also
  // update defs[] and uses[]
  //
  vector<u32> new_defs, new_uses;

  FORN(i,constraints.size()) {
    Constraint& C = constraints[i];
    if (C.off == MAX_U32) { continue; }

    u32 idx = dfg.insert(C);

    if (defs[i]) { 
      assert(C.type == store_cons);
      new_defs.resize(idx+1,0);
      new_defs[idx] = defs[i];
    }
    else if (uses[i]) { 
      assert(C.type == load_cons);
      new_uses.resize(idx+1,0);
      new_uses[idx] = uses[i];
    }
    else if ((C.type == addr_of_cons || C.type == copy_cons) &&
	     C.dest <= last_obj_node) { // global init
      gv2n[C.dest].push_back(idx);
    }
  }

  defs.swap(new_defs);
  uses.swap(new_uses);

  // we're done with constraints[]
  //
  constraints.clear();

  // we've added all the {Top,Ld,St}Nodes to the DFG, the only new
  // nodes to be added are the NopNodes; we can now finalize the
  // node indexing
  //
  dfg.finalize_insert();

  if (USE_MEM_TIME) { 
    print_time("sfs_prep");
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }
}

// partition variables into access equivalence classes:
//
// 1. group loads and stores into disjoint sets based on pointer
//    equivalence of the pointers they dereference
//
// 2. for each constraint set, map from each variable pointed to by
//    the pointer-equivalence class to the constraint set
//
// 3. variables are in the same partition if they are accessed by the
//    same set of constraints
//
void SFS::partition_vars()
{
  FORN(i,defs.size()) {
    if (!defs[i]) { continue; }

    u32 idx = dfg.st_idx(i,true);
    Constraint& C = dfg.node_cons(idx);
    assert(C.type == store_cons);

    cons_part[squeeze(PRE.PE(C.dest),C.off,true)].push_back(idx);

    if (PRE.is_single(C.dest,C.off)) {
      const vector<u32>& pts = *(PRE.pointsToSet(C.dest,C.off));
      if (strong[pts.front()]) { cons_strong.insert(idx); }
    }
    else if (PRE.is_null(C.dest,C.off)) { cons_strong.insert(idx); }
  }

  FORN(i,uses.size()) {
    if (!uses[i]) { continue; }

    u32 idx = dfg.ld_idx(i,true);
    Constraint& C = dfg.node_cons(idx);
    assert(C.type == load_cons);

    cons_part[squeeze(PRE.PE(C.src),C.off,true)].push_back(idx);
  }

  FOREACH(u2uv_it,i,cons_part) {
    pair<u32,u32> access = unsqueeze(i->first);
    const vector<u32>& pts = *(PRE.pointsToSet(access.first,access.second));
    FOREACH(uv_cit,j,pts) { rel[*j].set(i->first); }
  }

  sq_map.clear();
  sq_unmap.clear();

  // global objects could have been initialized when they were
  // decelared, and there won't be any stores for these; the
  // initialized global object were put in gv2n by sfs_prep()
  //
  // we'll designate the program start node as NP for initialized
  // globals and use a cons_part index of 0 to indicate global
  // initializers
  //
  assert(!cons_part.count(0));

  FOREACH(u2uv_it,i,gv2n) {
    if (rel.count(i->first)) { rel[i->first].set(0); }
  }

  std::map<bitmap,u32> eq;  // map relevant partitions to equiv. class

  assert(var_part.empty());
  var_part.push_back(bitmap()); // 0 index reserved

  FOREACH(u2bm_it,i,rel) {
    u32 cl = eq[i->second];

    if (!cl) {
      var_part.push_back(bitmap());
      cl = var_part.size() - 1;
      eq[i->second] = cl;
    }

    // we could keep track of the lowest var in each partition and
    // delete the rel entries for all other vars; this would only
    // matter if rel takes up a lot of space

    var_part[cl].set(i->first);
  }

  eq.clear();

  // fill in mapping from object to partition
  //
  o2p.assign(last_obj_node+1,0);

  FOR1N(i,var_part.size()) {
    FOREACH(bm_it,j,var_part[i]) { o2p[*j] = i; }
  }

  if (USE_STATS) {
    u32 cnt = 0;
    FOREACH(uv_it,i,o2p) { if (*i) { cnt++; }}
    errs() << "num partitions == " << var_part.size() << " for "
	 << cnt << " vars" << "\n";
  }

  if (USE_MEM_TIME) { 
    print_time("partition_vars");
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }
}

void SFS::compute_seg()
{
  vector<u32> rst;
  vector<SEGnode> saveG(G);

  FOR1N(i,var_part.size()) {
    u32 rep = var_part[i].find_first();
    u32 np = 0, r = 0;

    // mark relevant nodes with np, c, r flags
    //
    FOREACH(bm_it,j,rel[rep]) {
      if (*j == 0) { // global initializer
	FOREACH(bm_it,k,var_part[i]) {
	  assert(gv2n.count(*k));
	  glob_init.insert(glob_init.end(),gv2n[*k].begin(),gv2n[*k].end());
	}

	G[prog_start_node].np = true; ++np;
	rst.push_back(prog_start_node);
	continue;
      }
      
      FOREACH(uv_it,k,cons_part[*j]) {
	Constraint& C = dfg.node_cons(*k);
	
	if (C.type == store_cons) {
	  cons_store.push_back(*k);
	  
	  u32 st_idx = dfg.st_idx(*k,false);
	  u32 n = defs[st_idx]; assert(CHK(n) && !G[n].np);
	  
	  G[n].np = true; ++np;
	  if (np <= 1 || r <= 1) { rst.push_back(n); }
	  if (cons_strong.count(*k)) { G[n].c = true; }        
	}
	else {
	  assert(C.type == load_cons);
	  cons_load.push_back(*k);
	  
	  u32 ld_idx = dfg.ld_idx(*k,false);
	  u32 n = uses[ld_idx]; assert(CHK(n));
	  
	  G[n].r = true; ++r;
	  if (np <= 1 || r <= 1) { rst.push_back(n); }
	}
      }
    }

    // partitions with no stores can be ignored; for partitions with a
    // single store, we assume all loads will use that store, and
    // thereby avoid computing SSA for those partitions (this is
    // slightly optimistic -- because PRE is flow-insensitive, there
    // can be a load that isn't reached by the store; we could catch
    // this by checking reachability if we want)
    //
    // similarly, partitions with no loads can be ignored; for
    // partitions with a single load, we assume that all stores are
    // used by that load (with the same caveat as above)
    //
    if (np <= 1 || r <= 1) {
      if      (np == 1 && r > 0) { process_1store(i); }
      else if (np > 0 && r == 1) { process_1load(i);  }

      // for prepping DFG nodes
      //
      FOREACH(uv_it,j,cons_load)  { n2p[*j].push_back(i); }
      FOREACH(uv_it,j,cons_store) { n2p[*j].push_back(i); }

      // for sharing points-to graphs
      //
      if (np <= 1) {
	FOREACH(uv_it,j,cons_load)  { n2g[*j].set(squeeze(1,i)); }
	FOREACH(uv_it,j,cons_store) { n2g[*j].set(squeeze(1,i)); }
      }
      else {
	u32 k = 0;
	FOREACH(uv_it,j,cons_load)  { n2g[*j].set(squeeze(k,i)); ++k; }
	FOREACH(uv_it,j,cons_store) { n2g[*j].set(squeeze(k,i)); ++k; }
      }

      // need to reset state
      //
      FOREACH(uv_it,j,rst) {G[*j].np = false; G[*j].c = false; G[*j].r = false;}

      rst.clear();
      glob_init.clear();
      cons_load.clear();
      cons_store.clear();

      continue;
    }

    rst.clear();
    cons_load.clear();
    cons_store.clear();

    SEG(); // compute phi placement

    // map nodes to load and store constraints
    //
    FOREACH(bm_it,j,rel[rep]) {
      if (*j == 0) { continue; }

      FOREACH(uv_it,k,cons_part[*j]) {
        Constraint& C = dfg.node_cons(*k);

        if (C.type == store_cons) {
          u32 n = find(defs[dfg.st_idx(*k,false)]);
          if (DEL(n)) { continue; } // because of T6 and CN

          assert(CHK(n) && NP(n) && !pass_defs.count(n));
          pass_defs[n] = *k;
	  n2p[*k].push_back(i);
        }
        else {
          u32 n = find(uses[dfg.ld_idx(*k,false)]);
          if (DEL(n)) { continue; } // because of rm_undef

          assert(C.type == load_cons && CHK(n) && RQ(n));
          pass_uses[n].push_back(*k);
	  n2p[*k].push_back(i);
        }
      }
    }
    
    // fill in the required data structures for sparse FS
    //
    FOREACH(u2uv_it,j,pass_uses) {
      if (!pass_node.count(j->first)) { process_seg(i,j->first); }
    }
    FOREACH(u2u_it,j,pass_defs) {
      if (!pass_node.count(j->first)) { process_seg(i,j->first); }
    }

    // restore info for next iteration
    //
    glob_init.clear();
    pass_defs.clear();
    pass_uses.clear();
    pass_node.clear();

    FOR1N(j,G.size()) {
      SEGnode& N = G[j];
      
      N.np = N.r = N.c = N.del = false;
      N.dfs = 0;
      N.rep = MAX_U32;
      N.succ.clear();
    }

    FOREACH(uv_it,j,topo)    { G[*j].pred = saveG[*j].pred; }
    FOREACH(uv_it,j,t5_reps) { G[*j].pred = saveG[*j].pred; }

    if (USE_DEBUG) {
      FOR1N(j,G.size()) { assert(G[j].pred == saveG[j].pred); }
    }
  }

  // these are dead node
  //
  G.clear();
  rq.clear();
  rel.clear();
  topo.clear();
  uses.clear();
  defs.clear();
  gv2n.clear();
  t5_reps.clear();
  not_nprq.clear();
  cons_part.clear();
  cons_strong.clear();

  if (false && USE_STATS) { dfg.stats(var_part); }

  if (USE_MEM_TIME) { 
    print_time("compute_seg/parts"); 
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }

  // determine which load/store nodes can share points-to graphs; for
  // each group of nodes that can share a points-to graph, we
  // designate a rep node (the store node if it exists, an arbitrary
  // load node otherwise)
  // 
  std::map<bitmap,u32> st;
  std::map<bitmap,vector<u32> > ld;
  typedef std::map<bitmap,vector<u32> >::iterator bm2uv_it;

  FOREACH(u2bm_it,i,n2g) {
    if (dfg.is_st(i->first)) {
      assert(!st.count(i->second));
      st[i->second] = i->first;
    }
    else { ld[i->second].push_back(i->first); }
  }

  sq_map.clear(); // dead now

  FOREACH(bm2uv_it,i,ld) {
    u32 s = st[i->first];
    vector<u32>& n = i->second; // note that n is sorted

    if (!s && n.size() == 1) { continue; } // single node in eq class

    if (s) {
      StNode& R = dfg.get_st(s);
      R.part_succ.erase_dsts(n);

      FOREACH(uv_it,j,n) { 
	dfg.set_rep(*j,s);
	R.part_succ.insert(*j,0); // ensure rep has an edge to the non-rep
      }
    }
    else {
      u32 l = n.front();
      LdNode& R = dfg.get_ld(l);
      R.part_succ.erase_dsts(n);

      FOR1N(j,n.size()) {
	dfg.set_rep(n[j],l);
	R.part_succ.insert(n[j],0); // ensure rep has an edge to the non-rep
      }
    }
  }

  if (USE_MEM_TIME) { 
    print_time("compute_seg/sharing"); 
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }

  if (USE_DEBUG) {
    for (ld_it i = dfg.ld_begin(), e = dfg.ld_end(); i != e; ++i) {
      // a non-rep's rep does not itself have a rep, and a non-rep and
      // its rep have exactly the same partitions
      //
      if (i->rep) {
	if (dfg.is_ld(i->rep)) { assert(!dfg.get_ld(i->rep).rep); }
	u32 idx = dfg.ld_idx(i-dfg.ld_begin(),true);
	vector<u32>& p = n2p[idx];
	vector<u32>& r = n2p[i->rep];
	assert(p == r);
      }
    }
    if (USE_MEM_TIME) { reset_time(); }
  }

  if (USE_STATS) {
    errs() << "loads shared == " << dfg.num_shared() << " out of " 
	 << dfg.num_ld() << "\n";
  }

  // these are dead now
  //
  st.clear();
  ld.clear();
  n2g.clear();

  // we modify the edges from all nodes to point only to reps (except
  // for reps pointing to their own non-reps)
  //
  for (tp_it i = dfg.tp_begin(), e = dfg.tp_end(); i != e; ++i) {
    FOREACH(uv_it,j,i->succ) {
      if (dfg.is_ld(*j)) {
	LdNode& N = dfg.get_ld(*j);
	if (N.rep) { *j = N.rep; }
      }
    }
    std::sort(i->succ.begin(),i->succ.end());
    uv_it ee = std::unique(i->succ.begin(),i->succ.end());
    i->succ.erase(ee,i->succ.end());
  }

  for (ld_it i = dfg.ld_begin(), e = dfg.ld_end(); i != e; ++i) {
    u32 idx = (i->rep ? i->rep : (i-dfg.ld_begin()));

    FOREACH(pmap_it,j,i->part_succ) {
      if (dfg.is_ld(j->first)) {
	LdNode& N = dfg.get_ld(j->first);
	if (N.rep && N.rep != idx) { j->first = N.rep; }
      }
    }
    if (i->rep) { i->part_succ.erase_dst(i->rep); }
    i->part_succ.uniq();
  }

  for (st_it i = dfg.st_begin(), e = dfg.st_end(); i != e; ++i) {
    u32 idx = (i-dfg.st_begin());

    FOREACH(pmap_it,j,i->part_succ) {
      if (dfg.is_ld(j->first)) {
	LdNode& N = dfg.get_ld(j->first);
	if (N.rep && N.rep != idx) { j->first = N.rep; }
      }
    }
    i->part_succ.uniq();
  }

  for (np_it i = dfg.np_begin(), e = dfg.np_end(); i != e; ++i) {
    FOREACH(uv_it,j,i->succ) {
      if (dfg.is_ld(*j)) {
	LdNode& N = dfg.get_ld(*j);
	if (N.rep) { *j = N.rep; }
      }
    }
    std::sort(i->succ.begin(),i->succ.end());
    uv_it ee = std::unique(i->succ.begin(),i->succ.end());
    i->succ.erase(ee,i->succ.end());
  }

  if (USE_MEM_TIME) { 
    print_time("compute_seg/fix edges"); 
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }

  if (false && USE_STATS) { dfg.stats(var_part); }

  // prep the points-to graphs for {Ld,St,Np}Nodes in the DFG
  //
  vector<u32> vars;
  map<u32,vector<u32> > p2v;

  FOR1N(i,var_part.size()) {
    vector<u32>& v = p2v[i];
    FOREACH(bm_it,j,var_part[i]) { v.push_back(*j); }
  }

  var_part.clear(); // dead now

  FOREACH(u2uv_it,i,n2p) {
    if (dfg.is_ld(i->first) && dfg.get_ld(i->first).rep) { continue; }

    FOREACH(uv_it,j,i->second) {
      vars.insert(vars.end(),p2v[*j].begin(),p2v[*j].end());
    }
    dfg.prep_node(i->first,vars);
    vars.clear();
  }

  n2p.clear(); // dead now

  if (USE_MEM_TIME) { 
    print_time("compute_seg/prep nodes"); 
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  } 
}

void SFS::process_1store(u32 part)
{
  if (!cons_store.empty()) { // def is a store, not a global init
    assert(glob_init.empty());
    u32 st_idx = cons_store.front();
    FOREACH(uv_it,i,cons_load) { dfg.add_edge(st_idx,*i,part); }
  }
  else { // a global init
    FOREACH(uv_it,i,glob_init) {
      FOREACH(uv_it,j,cons_load) { dfg.add_edge(*i,*j); }
    }
  }
}

void SFS::process_1load(u32 part)
{
  u32 ld_idx = cons_load.front();  
  FOREACH(uv_it,i,cons_store) { dfg.add_edge(*i,ld_idx,part); }
}

void SFS::process_seg(u32 part, u32 n)
{
  assert(CHK(n) && !pass_node.count(n));

  // global inits are handled specially, since they involve TpNodes
  // in the DFG
  //
  if (!glob_init.empty() && n == find(prog_start_node)) {
    assert(glob_init.size() == 1 && G[n].pred.empty());
    pass_node[n] = glob_init.front();
    return;
  }

  // if there is a store, it should be the first node; any loads are
  // arbitrarily ordered after the store; if there are no stores or
  // loads then we create a NopNode

  u32 first;
  u2u_it def = pass_defs.find(n);
  u2uv_it use = pass_uses.find(n);

  bool st = (def != pass_defs.end());
  bool ld = (use != pass_uses.end());

  if      (st) { first = def->second; }
  else if (ld) { first = use->second.front(); }
  else         { first = dfg.insert_nop(); n2p[first].push_back(part); }

  if (!dfg.is_np(first)) { n2g[first].set(squeeze(n,part)); }

  if (!ld || (!st && use->second.size() == 1)) { pass_node[n] = first; }
  else {
    const vector<u32>& lds = use->second;
    u32 p = lds.front();

    if (first != p) {
      n2g[p].set(squeeze(n,part));
      dfg.add_edge(first,p,part);
    }

    // note that by construction, if there is no store then the load
    // with the least idx is 'first' -- this is important for sharing
    // points-to graphs, because we make the least idx the rep node

    FOR1N(i,lds.size()) {
      n2g[lds[i]].set(squeeze(n,part));
      dfg.add_edge(first,lds[i],part);
    }
    pass_node[n] = first;
  }

  // visit all the predecessors
  //
  EdgeSet pred;
  FOREACH(set_it,i,G[n].pred) {
    u32 p = find(*i);
    if (p == n || DEL(p)) { continue; }

    pred.insert(p);
    if (!pass_node.count(p)) { process_seg(part,p); }
  }
  pred.unique();

  // add the DFG edges from the predecessors
  //
  FOREACH(set_it,i,pred) {
    u32 p = pass_node[*i];
    dfg.add_edge(p,first,part);
  }

  if (false && USE_STATS) { //!!FIXME: investigate this later
    if (dfg.is_np(first) && pred.empty()) { errs() << "nop w/ no preds" << "\n"; }
  }
}
