#include "sfs-aa.h"

namespace { // anon namespace for stuff local to this file

////////////////////////////////////////////////////////////////////////////////
//// TYPES, MACROS, AND GLOBALS

struct OffNode
{
  bool del;     // for tarjans
  u32 rep, dfs; // "

  bool idr;
  bitmap edges, lbls;

  OffNode() : del(false), rep(MAX_U32), dfs(0), idr(false) {}
};

vector<OffNode> G;  // the offline constraint graph
u32 pe_lbl;         // next label to use
u32 dfs_num;        // for tarjans
stack<u32> node_st; // for tarjans

hash_map<pair<u32,u32>, u32> gep2pe; // GEP var,off -> lbl
typedef hash_map<pair<u32,u32>, u32>::const_iterator pr2u_cit;

#define RPP(x) (G[x].rep > G.size()) // is x a set rep?
#define RNK(x) (MAX_U32 - G[x].rep)  // the rank of rep x

////////////////////////////////////////////////////////////////////////////////
//// HELPER FUNCTIONS

u32 find(u32 n)
{
  if (RPP(n)) { return n; }
  else { return (G[n].rep = find(G[n].rep)); }
}

u32 unite(u32 a, u32 b)
{
  assert(RPP(a) && RPP(b));

  if (a == b) { return a; }

  u32 ra = RNK(a), rb = RNK(b);

  if (ra < rb) { u32 t = a; a = b; b = t; }
  else if (ra == rb) { G[a].rep--; }

  G[a].idr   |= G[b].idr;
  G[a].lbls  |= G[b].lbls;
  G[a].edges |= G[b].edges;

  G[b].rep = a;
  G[b].lbls.clear();
  G[b].edges.clear();

  return a;
}

void hu(u32 n)
{
  OffNode& N = G[n];

  u32 my_dfs = dfs_num++;
  N.dfs = my_dfs;

  FOREACH(bm_it,i,N.edges) {
    u32 p = find(*i);
    OffNode& P = G[p];

    if (p == n || P.del) { continue; }

    if (!P.dfs) { hu(p); }
    if (P.dfs < N.dfs) { N.dfs = P.dfs; }
  }

  if (my_dfs == N.dfs) {
    while (!node_st.empty() && G[node_st.top()].dfs >= my_dfs) {
      n = unite(n,node_st.top()); // N now invalid
      node_st.pop();
    }

    G[n].del = true;
    if (G[n].idr) { G[n].lbls.set(pe_lbl++); }

    FOREACH(bm_it,i,G[n].edges) {
      u32 p = find(*i);

      if (p == n) { continue; }
      assert(!G[p].lbls.empty());

      if (!G[p].lbls.test(0)) { // not a non-pointer
	G[n].lbls |= G[p].lbls;
      }
    }

    if (G[n].lbls.empty()) { G[n].lbls.set(0); } // non-pointer
  }
  else { node_st.push(n); }
}

} // end anon namespace

////////////////////////////////////////////////////////////////////////////////
//// METHODS

void SFS::make_off_graph()
{
  G.assign(nodes.size(),OffNode());
  
  // address-taken variables are indirect
  //
  FOR1N(i,last_obj_node+1) { G[i].idr = true; }

  FORN(i,constraints.size()) {
    const Constraint& C = constraints[i];

    switch(C.type) {
    case addr_of_cons:  // D = &S
      G[C.dest].idr = true;
    case load_cons:     // D = *S+k
      //!! this test makes results inconsistent with PRE (why?)
      //
      //if (PRE.is_null(C.src,C.off)) { continue; }
      G[C.dest].idr = true;
      break;
    case copy_cons:     // D = S
      G[C.dest].edges.set(C.src);
      break;
    case gep_cons:      // D = GEP S k
      {
	pair<u32,u32> A(C.src,C.off);
	pr2u_cit j = gep2pe.find(A);
	u32 l = pe_lbl;
	
	if (j != gep2pe.end()) { l = j->second; }
	else { gep2pe[A] = l; pe_lbl++; }
	
	G[C.dest].lbls.set(l);
      }
      break;
    case store_cons:    // *D+k = S
      // ignore
      break;
    default: assert(0 && "unknown constraint type!");
    }
  }

  gep2pe.clear();
}

// we'll do HU, except not using any REF nodes (because they can have
// a different value at each program point); instead, STOREs are
// ignored and the lhs of LOADs are made indirect
//
// !!FIXME: this can be made more aggressive, eg: *x = y; z = *x; w =
//          *x implies that *x has the same value at each program point 
//          and that z and w are pointer equivalent (but not necessarily 
//          with y, because of weak updates)
//
void SFS::cons_opt(vector<u32>& redir)
{
  pe_lbl = 1;
  dfs_num = 1;

  make_off_graph();

  // use HU to detect equivalences
  //
  FOR1N(i,G.size()) { if (!G[i].dfs) { hu(i); }}
  assert(node_st.empty());

  // merge nodes based on the detected equivalences
  //
  hash_map<bitmap,u32> eq;

  FOR1N(i,G.size()) {
    assert(nodes[i]->is_rep());

    OffNode& N = G[find(i)];
    if (N.lbls.empty() || N.lbls.test(0)) { nodes[i]->nonptr = true; continue; }

    bm2u_it j = eq.find(N.lbls);

    if (j != eq.end()) {
      assert(PRE.PE(i) == PRE.PE(get_node_rep(j->second)));
      merge_nodes(i,get_node_rep(j->second));
    }
    else { eq[N.lbls] = i; }
  }

  G.clear();
  eq.clear();

  // rewrite constraints to use node reps
  //
  DenseSet<Constraint> seen;
  vector<Constraint> old_cons;
  old_cons.swap(constraints);

  redir.assign(old_cons.size(),0);

  FORN(i,old_cons.size()) {
    const Constraint& OC = old_cons[i];
    if (nodes[OC.dest]->nonptr || nodes[OC.src]->nonptr) {
      redir[i] = MAX_U32;
      continue;
    }

    // eliminate constraints involving pointers that PRE says are null
    //
    if (OC.type != store_cons && OC.type != addr_of_cons && 
	PRE.is_null(OC.src,0)) { redir[i] = MAX_U32; continue; }
    else if (OC.type == store_cons && PRE.is_null(OC.dest,0)) { 
      redir[i] = MAX_U32; continue;
    }

    Constraint C(OC);
    C.dest = get_node_rep(C.dest);
    if (C.type != addr_of_cons) { C.src = get_node_rep(C.src); }

    if (C.type != load_cons && C.type != store_cons) {
      if ((C.type == copy_cons && !C.off && C.src == C.dest) ||
	  seen.count(C)) { redir[i] = MAX_U32; continue; }
      seen.insert(C);
    }

    redir[i] = constraints.size();
    constraints.push_back(C);
  }
}
