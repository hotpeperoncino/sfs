/*  [cons_opt.cpp] Constraint optimizations
 *  v. 014, 2008-09-14
 *------------------------------------------------------------------------------
 *  Changes from 013:
 *  - added class OffNode
 *  - added HCD and HRU (with HVN, HR, HU modes)
 *    - make_off_nodes(), add_off_edges(), hvn(), hr(), hvn_dfs(),
 *      hvn_check_edge(), hvn_label(), hu_label(), merge_ptr_eq(),
 *      hcd(), hcd_dfs()
 *  - in merge_nodes():
 *    - merging i2p is no longer allowed
 *    - added HCD support
 *------------------------------------------------------------------------------
 *  TODO:
 *  - implement LE opt.
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
void Anders::cons_opt(){
  assert(curr_module && "cons_opt called when not running on a module");
  //Do 1 pass of regular HVN, to reduce HU's memory usage.
  hvn(0);
  //Run HRU until it can no longer remove 100 constraints.
  hr(1, 100);
  //Do HCD after HVN, so that it has fewer nodes to put in the map.
  //This also avoids updating that map after HVN.
  hcd();

  //Count reduced nodes & constraints.
  for(u32 i= last_obj_node+1, ie= nodes.size(); i < ie; ++i){
    if(nodes[i]->is_rep())
      INC_STAT(r_val_nodes);
  }
  SET_STAT(r_cons, constraints.size());
  FORN(i, constraints.size()){
    switch(constraints[i].type){
      case addr_of_cons:
        INC_STAT(r_addr_cons);
        break;
      case copy_cons:
        INC_STAT(r_copy_cons);
        break;
      case load_cons:
        INC_STAT(r_load_cons);
        break;
      case store_cons:
        INC_STAT(r_store_cons);
        break;
      case gep_cons:
        INC_STAT(r_gep_cons);
        break;
      default:
        assert(!"unknown cons. type");
    }
  }

  factor_ls();
}

//------------------------------------------------------------------------------
//Move all address-taken nodes to the front, to make the points-to sets denser.
void Anders::clump_addr_taken(){
  if(DEBUG_OCI){
    DPUTS("***** Moving addr-taken nodes to the front...\n");
  }
  vector<Node*> old_nodes;
  old_nodes.swap(nodes);
  u32 onsz= old_nodes.size();
  nodes.resize(onsz);
  //The node that was originally at (i) will be at move_to[i].
  u32 *move_to= (u32*)malloc(onsz*4);

  //The special nodes must stay at the front.
  FORN(i, first_var_node){
    nodes[i]= old_nodes[i];
    move_to[i]= i;
  }

  u32 nn= first_var_node;               //size of nodes
  //First copy all addr_taken, then all others.
  for(u32 i= first_var_node; i < onsz; ++i){
    if(old_nodes[i]->obj_sz){
      nodes[nn]= old_nodes[i];
      move_to[i]= nn++;
    }
  }
  last_obj_node= nn-1;
  for(u32 i= first_var_node; i < onsz; ++i){
    if(!old_nodes[i]->obj_sz){
      nodes[nn]= old_nodes[i];
      move_to[i]= nn++;
    }
  }

  //Renumber the nodes in all constraints and value-node maps.
  FORN(i, constraints.size()){
    Constraint &C= constraints[i];
    C.dest= move_to[C.dest];
    C.src= move_to[C.src];
    //Make sure all address-taken nodes are in the object-node segment
    //  (i.e. that no value node has its address taken).
    assert(C.type != addr_of_cons || C.src <= last_obj_node);
  }
  for(DenseMap<Value*, u32>::iterator it= val_node.begin(), ie= val_node.end();
      it != ie; ++it)
    it->second= move_to[it->second];
  for(DenseMap<Value*, u32>::iterator it= obj_node.begin(), ie= obj_node.end();
      it != ie; ++it)
    it->second= move_to[it->second];
  for(DenseMap<Function*, u32>::iterator it= ret_node.begin(),
      ie= ret_node.end(); it != ie; ++it)
    it->second= move_to[it->second];
  for(DenseMap<Function*, u32>::iterator it= vararg_node.begin(),
      ie= vararg_node.end(); it != ie; ++it)
    it->second= move_to[it->second];
  //Also update ind_calls and icall_cons.
  set<u32> old_ind_calls;
  old_ind_calls.swap(ind_calls);
  for(set<u32>::iterator it= old_ind_calls.begin(), ie= old_ind_calls.end();
      it != ie; ++it)
    ind_calls.insert(move_to[*it]);
  vector<pair<Constraint, set<Instruction*> > > old_icall_cons;
  for(DenseMap<Constraint, set<Instruction*> >::iterator
      it= icall_cons.begin(), ie= icall_cons.end(); it != ie; ++it)
    old_icall_cons.push_back(*it);
  icall_cons.clear();
  FORN(i, old_icall_cons.size()){
    Constraint &C= old_icall_cons[i].first;
    C.dest= move_to[C.dest];
    C.src= move_to[C.src];
    icall_cons[C]= old_icall_cons[i].second;
  }

  free(move_to);
  //Recheck what we just modified and print the nodes in the new sequence.
  verify_nodes();
  if(DEBUG_OCI){
    DEBUG(print_all_nodes(0));
  }
}

//------------------------------------------------------------------------------
//Unify nodes #n1 and #n2, returning the # of the parent (the one of higher
//  rank). The node of lower rank has the rep field set to the parent,
//  and most of its data is deleted.
u32 Anders::merge_nodes(u32 n1, u32 n2){
  assert(n1 && n1 < nodes.size() && "invalid node 1");
  assert(n2 && n2 < nodes.size() && "invalid node 2");
  assert(n1 != n2 && "trying to merge a node with itself");
  assert(n1 != i2p && n2 != i2p && "trying to merge i2p");
  Node *N1= nodes[n1], *N2= nodes[n2];
  u32 rank1= N1->rep, rank2= N2->rep;
  assert(rank1 >= node_rank_min && rank2 >= node_rank_min &&
      "only rep nodes may be merged");
  //Make n1 the parent.
  if(rank1 < rank2){
    swap(n1, n2);
    swap(N1, N2);
  }else if(rank1 == rank2)
    ++N1->rep;
  N2->rep= n1;
  if(DEBUG_SOLVE){
    DPUTS("merge_nodes  ");
    DEBUG(print_node_now(n1));
    DPUTS("  <=  ");
    DEBUG(print_node_now(n2));
    DEOL;
  }

  //If n2 was not visited in a long time,
  //  the combined node should be visited sooner.
  if(N1->vtime > N2->vtime)
    N1->vtime= N2->vtime;
  //Move n2's edges and constraints into n1.
  //This may cause n1 to have some edges to itself; copy edges are removed
  //  here (and also by the solver), while other types should remain.
  N1->points_to |= N2->points_to;
  N1->copy_to |= N2->copy_to;
  if(N1->copy_to.test(n1)){
    INC_STAT(copy_del);
    N1->copy_to.reset(n1);
  }
  if(N1->copy_to.test(n2)){
    INC_STAT(copy_del);
    N1->copy_to.reset(n2);
  }
  N1->load_to |= N2->load_to;
  N1->store_from |= N2->store_from;
  N1->gep_to |= N2->gep_to;
  //The entire points_to must be propagated across the new copy edges.
  N1->prev_points_to= bddfalse;
  //Delete n2's edges and constraints (the lists were cleared by splice()).
  N2->points_to= bddfalse;
  N2->prev_points_to= bddfalse;
  N2->copy_to.clear();
  N2->load_to.clear();
  N2->store_from.clear();
  N2->gep_to.clear();
  //If n2 was used as an indirect call target, n1 will now be used as such.
  if(ind_calls.count(n2)){
    ind_calls.erase(n2);
    ind_calls.insert(n1);
  }
  //If n2 is not a non-pointer, neither is n1.
  N1->nonptr &= N2->nonptr;
  //The constraint list is not updated here; instead use get_node_rep
  //  when processing a constraint.
  //icall_cons is not updated either (see solve.cpp and merge_ptr_eq()).
  //obj_sz and addr_taken should not be merged,
  //  since n2 will be pointed to as before;
  //  the GEP-related BDDs should also be ignored here.

  //We don't want zero entries in the map, so use find() rather than [].
  DenseMap<u32, u32>::iterator i_hv= hcd_var.find(n1);
  u32 hv1= i_hv == hcd_var.end() ? 0 : i_hv->second;
  i_hv= hcd_var.find(n2);
  u32 hv2= i_hv == hcd_var.end() ? 0 : i_hv->second;
  //Was *N2 in an offline cycle?
  if(hv2){
    if(!hv1){
      //*N1 is the same as *N2 (because N1/N2 have to be pointer-equivalent
      //  to get merged), so *N1 would be in a cycle with HV2.
      hcd_var[n1]= hv2;
    }else{
      u32 rhv1= get_node_rep(hv1), rhv2= get_node_rep(hv2);
      if(rhv1 != rhv2){
        //If we had offline cycles (*N1, RHV1) and (*N2, RHV2), and we know
        //  that *N1 and *N2 are the same, it means RHV1 and RHV2
        //  will be in the same SCC.
        merge_nodes(rhv1, rhv2);
        INC_STAT(hcd_on_var_merge);
        if(n1 == rhv2){
          //This is the only way for N1 to get merged again.
          n1= get_node_rep(n1);
        }else{
          assert(nodes[n1]->is_rep());
        }
      }
    }
    //Delete N2 from HCD, as it no longer points to anything.
    hcd_var.erase(n2);
  }
  return n1;
}

//We don't want DEBUG_OPT to disable some of the output above.
#if DEBUG_OPT == 0
  #undef DEBUG
  #define DEBUG(x)
#endif

//------------------------------------------------------------------------------
//A node for the offline constraint graph.
//This graph has VAL nodes for the top-level pointer variables (aka value
//  nodes) and AFP nodes for the parameters and return values of address-taken
//  functions (which are object nodes in the main graph but are used as normal
//  variables within the function). There is also a corresponding
//  REF node for the dereference (*p) of any VAL/AFP node (p).
class OffNode{
public:
  //Outgoing constraint edges: X -> Y for any cons. X = Y (where X/Y may
  //  be VAR or REF nodes).
  bitmap edges;
  //Outgoing implicit edges:
  //  any cons. edge X -> Y has a corresponding impl. edge *X -> *Y.
  bitmap impl_edges;
  //The union-find rank of this node if >= node_rank_min, else the number of
  //  another node in the same SCC.
  u32 rep;
  //The set of pointer-equivalence labels (singleton for HVN, any size for HU).
  //  This is empty for unlabeled nodes, and contains 0 for non-pointers.
  bitmap ptr_eq;
  //The node of the main graph corresponding to us (for HCD).
  u32 main_node;
  //The number of the DFS call that first visited us (0 if unvisited).
  u32 dfs_id;
  //True if this is the root of an already processed SCC.
  bool scc_root;
  //A VAL node is indirect if it's the LHS of a load+offset constraint;
  //  the LHS of addr_of and GEP are pre-labeled when building the graph
  //  and so don't need another unique label.
  //All AFP and REF nodes are indirect.
  bool indirect;

  OffNode(bool ind= 0) : rep(node_rank_min), dfs_id(0), scc_root(0),
      indirect(ind) {}

  bool is_rep() const{
    return rep >= node_rank_min;
  }
};

//------------------------------------------------------------------------------
//The nodes of the offline graph: | null | AFP | VAL | REF |.
static vector<OffNode> off_nodes;
//The offline node corresponding to each node of the main graph (0 = none).
static vector<u32> main2off;
//The number of each type of node and the index of the first of each type.
static u32 nVAL, nAFP, nREF, firstVAL, firstAFP, firstREF;
//Use REF(p) to get the REF node for any VAL/AFP node (p).
#define REF(p) ((p)-firstAFP+firstREF)
//The ptr_eq label to use next.
static u32 next_ptr_eq;
//The number of the current DFS.
static u32 curr_dfs;
//The non-root nodes in the current SCC.
static stack<u32> dfs_stk;
//The ptr_eq for each set of incoming labels (HVN only).
static std::map<bitmap, u32> lbl2pe;
//The RHS of any GEP constraint is mapped to a label.
static std::map<pair<u32, u32>, u32> gep2pe;

//------------------------------------------------------------------------------
//Return the rep node of the SCC containing (n), with path compression.
u32 get_off_rep(u32 n){
  u32 &r0= off_nodes[n].rep;
  //If (n) has a rank, it is the rep.
  if(r0 >= node_rank_min){
    return n;
  }
  //Recurse on the parent to get the real rep.
  u32 r= get_off_rep(r0);
  r0= r;                                //set n's parent to the rep
  return r;
}

//------------------------------------------------------------------------------
//Unify offline nodes #n1 and #n2, returning the # of the parent (the one of
//  higher rank). The node of lower rank has the rep field set to the parent.
u32 merge_off_nodes(u32 n1, u32 n2){
  assert(n1 && n1 < off_nodes.size() && "invalid node 1");
  assert(n2 && n2 < off_nodes.size() && "invalid node 2");
  assert(n1 != n2 && "trying to merge a node with itself");
  OffNode *N1= &off_nodes[n1], *N2= &off_nodes[n2];
  assert(N1->dfs_id && N2->dfs_id && "trying to merge unvisited nodes");
  u32 rank1= N1->rep, rank2= N2->rep;
  assert(rank1 >= node_rank_min && rank2 >= node_rank_min &&
      "only rep nodes may be merged");
  //Make n1 the parent.
  if(rank1 < rank2){
    swap(n1, n2);
    swap(N1, N2);
  }else if(rank1 == rank2){
    ++N1->rep;
  }
  N2->rep= n1;
  DEBUG(fprintf(stderr, "    merge %u <= %u\n", n1, n2));

  //Move n2's edges and labels into n1. In HVN mode, if both nodes were
  //  pre-labeled, n1 may have >1 label, but hvn_label() will be called
  //  on n1 as soon as the SCC is collapsed, so it will have only 1 label
  //  after hvn_dfs() returns.
  N1->edges |= N2->edges;
  N1->impl_edges |= N2->impl_edges;
  N1->ptr_eq |= N2->ptr_eq;
  N2->edges.clear();
  N2->impl_edges.clear();
  N2->ptr_eq.clear();
  //The entire SCC should be indirect if any node in it is.
  N1->indirect |= N2->indirect;
  //If either node was pre-labeled, the merged node should get the same label.
  N1->ptr_eq |= N2->ptr_eq;
  return n1;
}

//------------------------------------------------------------------------------
//Hash-based Value Numbering: offline analysis to delete redundant constraints
//  by finding some of the pointer-equivalent variables.
//If (do_union) is 1, use the HU algorithm: give a node a set of labels
//  and union all incoming labels.
void Anders::hvn(bool do_union){
  DPUTS("***** Starting HVN\n");
  make_off_nodes();
  //The LHS of GEP's will be pre-labeled, so start the counter here.
  //  The labels must be disjoint from node IDs because addr_of_cons
  //  use the source ID as a label.
  next_ptr_eq= nodes.size();
  gep2pe.clear();
  add_off_edges();

  //Run the DFS starting from every node, unless it's already been processed.
  curr_dfs= 1;
  lbl2pe.clear();
  for(u32 i= firstAFP; i < firstREF + nREF; ++i){
    if(!off_nodes[i].dfs_id){
      hvn_dfs(i, do_union);
    }
  }
  assert(dfs_stk.empty());

  merge_ptr_eq();
  off_nodes.clear();
  main2off.clear();
  lbl2pe.clear();
  gep2pe.clear();
}

//------------------------------------------------------------------------------
//HVN with Reference processing: by iterating HVN, we can use the fact
//  that (X ptr_eq Y) => (*X ptr_eq *Y).
//The easiest way to do HR is to run the complete HVN as long as it removes
//  at least (min_del) constraints (default 100).
//If (do_union) is 1 (default 0), run HU rather than HVN.
void Anders::hr(bool do_union, u32 min_del){
  //Note: we can optimize this by modifying the constraint graph at the end
  //  of each iteration (merging *X and *Y whenever X ptr_eq Y), then
  //  running the DFS on the same graph.
  u32 curr_n_cons= constraints.size(), prev_n_cons= 0;
  if(USE_STATS){
    fprintf(stderr, "  running HR%s, constraint count:  %u",
        do_union ? "U" : "", curr_n_cons);
  }
  do{
    hvn(do_union);
    prev_n_cons= curr_n_cons;
    curr_n_cons= constraints.size();
    if(USE_STATS)
      fprintf(stderr, "  %u", curr_n_cons);
  }while(prev_n_cons - curr_n_cons >= min_del);
  if(USE_STATS)
    putc('\n', stderr);
}

//------------------------------------------------------------------------------
//Make the offline nodes corresponding to the rep nodes of the main graph.
void Anders::make_off_nodes(){
  DPUTS("***** Creating offline graph nodes\n");
  u32 nn= nodes.size();
  assert(last_obj_node && "clump_addr_taken is required");
  main2off.assign(nn, 0);
  //Start the graph with only the null node (onn - size of off_nodes).
  u32 onn= 1;
  //Add the AFP nodes first (assuming clump_addr_taken has already moved
  //  them in front of all the value nodes).
  firstAFP= 1;
  //Look for function object nodes.
  for(u32 i= first_var_node; i <= last_obj_node; ){
    const Node *N= nodes[i];
    u32 sz= N->obj_sz;
    assert(sz && "object nodes are not clumped");
    assert(N->get_val() && "obj node has no value");
    Function *F= dyn_cast<Function>(N->get_val());
    //Skip this object if it's not a function.
    if(!F){
      i += sz;
      continue;
    }
    //Go through the retval and all the parameters of F.
    for(u32 j= func_node_off_ret; j < sz; ++j){
      //A rep parameter node gets a new offline node,
      //  but non-rep parm. are not included in any constraints.
      if(nodes[i+j]->is_rep()){
        main2off[i+j]= onn++;
      }
    }
    //Set (i) to the node after the current object.
    i += sz;
  }
  firstVAL= onn;
  nAFP= firstVAL - firstAFP;

  //Now add the value nodes, including p_i2p and temporary (no-value) nodes.
  main2off[p_i2p]= onn++;
  for(u32 i= last_obj_node+1; i < nn; ++i){
    const Node *N= nodes[i];
    assert(!N->obj_sz && "unexpected obj node");
    if(N->is_rep()){
      main2off[i]= onn++;
    }
  }
  firstREF= onn;
  nVAL= firstREF-firstVAL;
  nREF= nVAL+nAFP;
  //Create all the offline nodes, including REF.
  //AFP & VAR start out direct; then indirect REFs are added.
  off_nodes.assign(onn, OffNode());
  off_nodes.insert(off_nodes.end(), nREF, OffNode(1));
  //Mark AFPs indirect.
  for(u32 i= firstAFP; i < firstVAL; ++i){
    off_nodes[i].indirect= 1;
  }
  DEBUG(fprintf(stderr, "  %u AFP, %u VAL, %u REF\n", nAFP, nVAL, nREF));
}

//------------------------------------------------------------------------------
//Add the offline constraint edges based on the current constraint list.
//If hcd is off (default), also add the implicit edges and mark some nodes
//  as indirect.
void Anders::add_off_edges(bool hcd){
  DPUTS("***** Adding offline constraint edges\n");
  u32 n_copy= 0, n_load= 0, n_store= 0, n_impl_addr= 0, n_impl_copy= 0;
  FORN(i, constraints.size()){
    const Constraint &C= constraints[i];
    //This may fail if the source of an addr_of is a non-rep (which is
    //  allowed but hasn't happened yet).
    assert(nodes[C.dest]->is_rep() && nodes[C.src]->is_rep());
    u32 od= main2off[C.dest], os= main2off[C.src];
    if(!od){
      //A few constraints will have an obj_node for the dest.
      if(nodes[C.dest]->obj_sz){
        continue;
      }
      assert(!"no offline node for dest");
    }
    assert(os || nodes[C.src]->obj_sz && "no offline node for non-obj src");
    switch(C.type){
      case addr_of_cons:
        if(!hcd){
          //D = &S: impl. *D -> S.
          //Also add the actual points-to edge to the label set.
          //  Because of SSA form, there is only one addr_of_cons per dest.
          //  node, so all initial label sets will be singletons or empty,
          //  and HVN mode (do_union = 0) will work correctly.
          off_nodes[od].ptr_eq.set(C.src);
          //Note that S is often a non-AFP obj_node, which we ignore.
          if(os){
            off_nodes[REF(od)].impl_edges.set(os);
            ++n_impl_addr;
          }
        }
        break;
      case copy_cons:
        //D = S: edge D -> S, impl. *D -> *S.
        if(os){
          off_nodes[od].edges.set(os);
          ++n_copy;
          if(!hcd){
            off_nodes[REF(od)].impl_edges.set(REF(os));
            ++n_impl_copy;
          }
        }else{
          //Copying from an obj_node not in the graph makes dest. indirect.
          if(!hcd){
            off_nodes[od].indirect= 1;
          }
        }
        break;
      case load_cons:
        //Note: we don't handle load/store with offset as part of the HVN.
        //  These are only used for indirect calls, so handling them
        //  would not help much.
        if(C.off){
          //D = *S + k: D indirect
          if(!hcd){
            off_nodes[od].indirect= 1;
          }
        }else{
          //D = *S: edge D -> *S
          assert(os && "no offline node for src");
          off_nodes[od].edges.set(REF(os));
          ++n_load;
        }
        break;
      case store_cons:
        //*D + k = *S: ignored
        if(!C.off){
          //*D = S: edge *D -> S
          assert(os && "no offline node for src");
          off_nodes[REF(od)].edges.set(os);
          ++n_store;
        }
        break;
      case gep_cons:
        //D = gep S k: D is pre-labeled with the ID of its
        //  (S, k) pair. This works because in SSA form, the LHS of a GEP
        //  cannot be assigned any other value.
        if(!hcd){
          u32 pe;
          pair<u32, u32> R(C.src, C.off);
          std::map<pair<u32, u32>, u32>::const_iterator i_g2p= gep2pe.find(R);
          if(i_g2p == gep2pe.end()){
            gep2pe[R]= pe= next_ptr_eq++;
          }else{
            pe= i_g2p->second;
          }
          off_nodes[od].ptr_eq.set(pe);
        }
        break;
      default:
        assert(!"unknown constraint type");
    }
  }
  DEBUG(fprintf(stderr,
      "  %u copy, %u load, %u store, %u impl. addr_of, %u impl. copy\n",
      n_copy, n_load, n_store, n_impl_addr, n_impl_copy));
}

//------------------------------------------------------------------------------
//Part of HVN: using Tarjan's algorithm, collapse cycles in the offline graph
//  and assign pointer-equivalence labels to the offline nodes.
//The DFS starts from (n); (do_union) is passed on to hvn_label().
void Anders::hvn_dfs(u32 n, bool do_union){
  assert(n);
  OffNode *N= &off_nodes[n];
  assert(!N->scc_root && N->is_rep());
  u32 our_dfs= curr_dfs++;
  N->dfs_id= our_dfs;

  //Look for SCCs using all edges.
  for(bitmap::iterator it= N->edges.begin(), ie= N->edges.end();
      it != ie; ++it){
    hvn_check_edge(n, *it, do_union);
  }
  for(bitmap::iterator it= N->impl_edges.begin(), ie= N->impl_edges.end();
      it != ie; ++it){
    hvn_check_edge(n, *it, do_union);
  }
  assert(N->is_rep());

  //Is N the root of an SCC?
  if(N->dfs_id == our_dfs){
    while(!dfs_stk.empty()){
      u32 n2= dfs_stk.top();
      //Anything visited before us should remain on the stack.
      if(off_nodes[n2].dfs_id < our_dfs){
        break;
      }
      dfs_stk.pop();
      n= merge_off_nodes(n, n2);
    }
    //Note: the SCC root may be different from the node we started from
    //  if one of the stack nodes had a higher rank.
    assert(n);
    N= &off_nodes[n];
    N->scc_root= 1;
    assert(N->is_rep());
    //Now label the root; a pre-labeled node still needs to get the data
    //  from its neighbors.
    if(do_union){
      hu_label(n);
    }else{
      hvn_label(n);
    }
  }else{
    dfs_stk.push(n);
  }
}

//------------------------------------------------------------------------------
//Look at the offline constraint edge from (n) to (dest) and possibly
//  continue the DFS along it; (do_union) is passed on to hvn_label().
void Anders::hvn_check_edge(u32 n, u32 dest, bool do_union){
  OffNode *N= &off_nodes[n];
  assert(N->is_rep());
  //dest comes from a bitmap entry, so it may be out of date.
  u32 n2= get_off_rep(dest);
  const OffNode *N2= &off_nodes[n2];
  //Skip this neighbor if it was merged into N or is a collapsed SCC.
  if(n2 == n || N2->scc_root){
    return;
  }
  //If it's unvisited, continue the DFS.
  if(!N2->dfs_id){
    hvn_dfs(n2, do_union);
  }
  //Set our dfs_id to the minimum reachable ID.
  if(N2->dfs_id < N->dfs_id){
    N->dfs_id= N2->dfs_id;
  }
  assert(N->is_rep());
}

//------------------------------------------------------------------------------
//Label a node based on its neighbors' labels (for HVN).
void Anders::hvn_label(u32 n){
  OffNode *N= &off_nodes[n];
  bitmap &pe= N->ptr_eq;
  assert(N->is_rep() && N->scc_root);
  //All indirect nodes get new labels.
  if(N->indirect){
    //Remove pre-labeling, in case a direct pre-labeled node was
    //  merged with an indirect one.
    pe.clear();
    pe.set(next_ptr_eq++);
    return;
  }
  //Collect all incoming labels into the current node.
  for(bitmap::iterator it= N->edges.begin(), ie= N->edges.end();
      it != ie; ++it){
    u32 n2= get_off_rep(*it);
    if(n2 == n){
      continue;
    }
    bitmap &pe2= off_nodes[n2].ptr_eq;
    assert(!pe2.empty() && "unlabeled neighbor");
    //Ignore non-ptr neighbors.
    if(!pe2.test(0)){
      pe |= pe2;
    }
  }
  //If a direct node has no incoming labels, it's a non-pointer.
  if(pe.empty()){
    pe.set(0);
  //If there was >1 incoming label, replace the set by its ID.
  }else if(!bitmap_single_bit_p(pe)){
    std::map<bitmap, u32>::const_iterator i_l2p= lbl2pe.find(pe);
    if(i_l2p == lbl2pe.end()){
      lbl2pe[pe] = next_ptr_eq;
      pe.clear();
      pe.set(next_ptr_eq++);
    }else{
      pe.clear();
      pe.set(i_l2p->second);
    }
  }
  //If there was only 1, keep it.
  assert(bitmap_single_bit_p(N->ptr_eq));
}

//------------------------------------------------------------------------------
//Label a node with the union of incoming labels (for HU).
void Anders::hu_label(u32 n){
  OffNode *N= &off_nodes[n];
  bitmap &pe= N->ptr_eq;
  assert(N->is_rep() && N->scc_root);
  //An indirect node starts with a unique label.
  if(N->indirect){
    pe.set(next_ptr_eq++);
  }
  //Collect all incoming labels into the current node.
  for(bitmap::iterator it= N->edges.begin(), ie= N->edges.end();
      it != ie; ++it){
    u32 n2= get_off_rep(*it);
    if(n2 == n){
      continue;
    }
    bitmap &pe2= off_nodes[n2].ptr_eq;
    assert(!pe2.empty() && "unlabeled neighbor");
    //Ignore non-ptr neighbors.
    if(!pe2.test(0)){
      pe |= pe2;
    }
  }
  //If a direct node has no incoming labels, it's a non-pointer.
  if(pe.empty()){
    pe.set(0);
  }
}

//------------------------------------------------------------------------------
//Merge all pointer-equivalent nodes and update the constraint list.
void Anders::merge_ptr_eq(){
  DPUTS("***** Merging pointer-equivalent nodes\n");
  u32 nn= nodes.size();
  //The first node (of the main graph) with the given ptr_eq.
  std::map<bitmap, u32> pe2node;
  FORN(i, nn){
    u32 on= main2off[i];
    //If this node has no offline version, it's not pointer-equivalent.
    if(!on){
      continue;
    }
    bitmap &pe= off_nodes[get_off_rep(on)].ptr_eq;
    assert(!pe.empty());
    //Non-ptr nodes should be deleted from the constraints.
    if(pe.test(0)){
      assert(bitmap_single_bit_p(pe));
      nodes[i]->nonptr= 1;
      continue;
    }
    //Anything previously marked as non-ptr cannot have another label.
    assert(!nodes[i]->nonptr);
    std::map<bitmap, u32>::iterator i_p2n= pe2node.find(pe);
    if(i_p2n == pe2node.end()){
      //This PE was not seen yet, so (i) is its first node.
      assert(nodes[i]->is_rep());
      pe2node[pe]= i;
    }else{
      u32 en= i_p2n->second;
      //Merge (i) into the node representing (pe).
      INC_STAT(hvn_merge);
      i_p2n->second= merge_nodes(en, i);
    }
  }

  vector<Constraint> old_cons;
  old_cons.swap(constraints);
  DenseSet<Constraint> cons_seen;
  FORN(i, old_cons.size()){
    Constraint &C= old_cons[i];
    //Ignore this constraint if either side is a non-ptr.
    if(nodes[C.dest]->nonptr || nodes[C.src]->nonptr)
      continue;
    C.dest= get_node_rep(C.dest);
    //Don't replace the source of addr_of by the rep: the merging
    //  done in HVN/HCD is based only on pointer equivalence,
    //  so non-reps may still be pointed to.
    if(C.type != addr_of_cons)
      C.src= get_node_rep(C.src);
    //Ignore (copy X X) and duplicates.
    if((C.type != copy_cons || C.dest != C.src) && !cons_seen.count(C)){
      cons_seen.insert(C);
      constraints.push_back(C);
    }
  }

  //Also rewrite icall_cons to refer to the rep nodes.
  vector<pair<Constraint, set<Instruction*> > > old_icall_cons;
  for(DenseMap<Constraint, set<Instruction*> >::iterator
      it= icall_cons.begin(), ie= icall_cons.end(); it != ie; ++it){
    old_icall_cons.push_back(*it);
  }
  icall_cons.clear();
  FORN(i, old_icall_cons.size()){
    Constraint &C= old_icall_cons[i].first;
    if(nodes[C.dest]->nonptr || nodes[C.src]->nonptr)
      continue;
    C.dest= get_node_rep(C.dest);
    C.src= get_node_rep(C.src);
    const set<Instruction*> &I= old_icall_cons[i].second;
    icall_cons[C].insert(I.begin(), I.end());
  }
}

//------------------------------------------------------------------------------
//Hybrid Cycle Detection, offline part: map any var X to var A if there is
//  an SCC containing both *X and A. Note: after HVN, no SCC will have >1
//  non-REF node.
void Anders::hcd(){
  DPUTS("***** Starting HCD\n");
  make_off_nodes();
  //(1) means don't make implicit edges or set the indirect flag.
  add_off_edges(1);
  //Map the offline nodes to the main graph.
  FORN(i, main2off.size()){
    u32 n= main2off[i];
    if(n){
      off_nodes[n].main_node= i;
      off_nodes[REF(n)].main_node= i;
    }
  }

  //Run the DFS starting from every node, unless it's already been processed.
  curr_dfs= 1;
  for(u32 i= firstAFP; i < firstREF + nREF; ++i){
    if(!off_nodes[i].dfs_id){
      hcd_dfs(i);
    }
  }
  assert(dfs_stk.empty());

  SET_STAT(hcd_size, hcd_var.size());
  off_nodes.clear();
  main2off.clear();

  //Update constraints and icall_cons to refer to the reps,
  //  because we merged some of the VARs.
  vector<Constraint> old_cons;
  old_cons.swap(constraints);
  DenseSet<Constraint> cons_seen;
  FORN(i, old_cons.size()){
    const Constraint &C0= old_cons[i];
    u32 dest= get_node_rep(C0.dest), src= C0.src;
    if(C0.type != addr_of_cons)
      src= get_node_rep(src);
    Constraint C(C0.type, dest, src, C0.off);
    //Ignore (copy X X) and duplicates.
    if((C.type != copy_cons || C.dest != C.src) && !cons_seen.count(C)){
      cons_seen.insert(C);
      constraints.push_back(C);
    }
  }
  vector<pair<Constraint, set<Instruction*> > > old_icall_cons;
  for(DenseMap<Constraint, set<Instruction*> >::iterator
      it= icall_cons.begin(), ie= icall_cons.end(); it != ie; ++it){
    old_icall_cons.push_back(*it);
  }
  icall_cons.clear();
  FORN(i, old_icall_cons.size()){
    Constraint &C= old_icall_cons[i].first;
    C.dest= get_node_rep(C.dest);
    C.src= get_node_rep(C.src);
    const set<Instruction*> &I= old_icall_cons[i].second;
    icall_cons[C].insert(I.begin(), I.end());
  }
}

//------------------------------------------------------------------------------
//Part of HCD: using Tarjan's algorithm, find SCCs containing both VAR and REF
//  nodes, then map all REFs to the VAR. We don't collapse SCCs here.
void Anders::hcd_dfs(u32 n){
  assert(n);
  DEBUG(fprintf(stderr, "  hcd_dfs %u\n", n));
  OffNode *N= &off_nodes[n];
  assert(!N->scc_root && N->is_rep());
  u32 our_dfs= curr_dfs++;
  N->dfs_id= our_dfs;

  //Look for SCCs using normal edges only.
  for(bitmap::iterator it= N->edges.begin(), ie= N->edges.end();
      it != ie; ++it){
    const OffNode *N2= &off_nodes[*it];
    assert(N2->is_rep());
    //Skip this neighbor if it's in an already processed SCC.
    if(N2->scc_root){
      continue;
    }
    //If it's unvisited, continue the DFS.
    if(!N2->dfs_id){
      hcd_dfs(*it);
    }
    //Set our dfs_id to the minimum reachable ID.
    if(N2->dfs_id < N->dfs_id){
      N->dfs_id= N2->dfs_id;
    }
  }
  assert(N->is_rep());

  //Is N the root of an SCC?
  if(N->dfs_id == our_dfs){
    //Record all nodes in our SCC (the root is not on the stack).
    vector<u32> scc(1, n);
    DEBUG(fprintf(stderr, "    HCD SCC: %u", n));
    //The VAR (non-REF) nodes in this SCC (may be several since we don't run
    //  HR to convergence).
    vector<u32> var;
    if(n < firstREF)
      var.push_back(n);
    while(!dfs_stk.empty()){
      u32 n2= dfs_stk.top();
      assert(n2 != n);
      //Anything visited before us should remain on the stack.
      if(off_nodes[n2].dfs_id < our_dfs){
        break;
      }
      dfs_stk.pop();
      scc.push_back(n2);
      DEBUG(fprintf(stderr, " %u", n2));
      if(n2 < firstREF){
        DEBUG(putc('*', stderr));
        var.push_back(n2);
      }
    }
    DEOL;
    //Singleton SCCs are ignored.
    if(scc.size() == 1){
      N->scc_root= 1;
      return;
    }
    assert(var.size() && "no VAR node in SCC");
    //Replace the offline VARs by the corresponding main nodes,
    //  then merge all of those.
    //Note that this will collapse any remaining VAR-only SCCs.
    u32 var_rep= off_nodes[var[0]].main_node;
    for(u32 i= 1, ie= var.size(); i != ie; ++i){
      var_rep= merge_nodes(var_rep, off_nodes[var[i]].main_node);
      INC_STAT(hcd_var_merge);
    }
    //Now process the entire SCC.
    FORN(i, scc.size()){
      u32 n= scc[i];
      assert(n);
      OffNode *N= &off_nodes[n];
      //Label N as a "root" (since it should be considered deleted but
      //  is not collapsed into the root).
      N->scc_root= 1;
      if(n >= firstREF){
        //Map the main node of N to the vars' rep.
        hcd_var[N->main_node]= var_rep;
      }
    }
  }else{
    dfs_stk.push(n);
  }
}

//Don't factor any constraint sets smaller than this (must be >1).
static const u32 factor_min_sz= 2;
//Map each factored constraint to the temp node of the result.
static DenseMap<Constraint, u32> factored_cons;

//------------------------------------------------------------------------------
//Factor load/store constraints.
//If there are (n) constraints of the form (A = *V + k), where (V) and (k)
//  are the same but (A) is any variable, the solver will create (n*p) copy
//  edges, where (p) is V's points-to size.
//We can replace them by a single load_cons (T = *V + k) and (n) copy_cons
//  (A = T), for a total of (n+p) copy edges and 1 extra node.
//Similarly, (*V + k = B) becomes (*V + k = T), plus (T = B) for all B.
void Anders::factor_ls(){
  //Map the (src,off) pair of each load_cons to the set of dest nodes,
  //  and the (dest,off) of each store_cons to the set of src.
  //Also delete all load/store cons. from the main list.
  std::map<pair<u32, u32>, set<u32> > loads, stores;
  vector<Constraint> old_cons;
  old_cons.swap(constraints);
  FORN(i, old_cons.size()){
    const Constraint &C= old_cons[i];
    if(C.type == load_cons){
      loads[make_pair(C.src, C.off)].insert(C.dest);
    }else if(C.type == store_cons){
      stores[make_pair(C.dest, C.off)].insert(C.src);
    }else{
      constraints.push_back(C);
    }
  }
  old_cons.clear();

  std::map<pair<u32, u32>, set<u32> >::const_iterator it, ie;
  for(it= loads.begin(), ie= loads.end(); it != ie; ++it){
    factor_ls(it->second, it->first.first, it->first.second, 1);
  }
  for(it= stores.begin(), ie= stores.end(); it != ie; ++it){
    factor_ls(it->second, it->first.first, it->first.second, 0);
  }

  //Update icall_cons to the new constraints.
  vector<pair<Constraint, set<Instruction*> > > old_icall_cons;
  for(DenseMap<Constraint, set<Instruction*> >::iterator
      it= icall_cons.begin(), ie= icall_cons.end(); it != ie; ++it){
    old_icall_cons.push_back(*it);
  }
  icall_cons.clear();
  FORN(i, old_icall_cons.size()){
    Constraint &C= old_icall_cons[i].first;
    DenseMap<Constraint, u32>::iterator i_fc= factored_cons.find(C);
    if(i_fc != factored_cons.end()){
      if(C.type == load_cons)
        C.dest= i_fc->second;
      else
        C.src= i_fc->second;
    }
    const set<Instruction*> &I= old_icall_cons[i].second;
    icall_cons[C].insert(I.begin(), I.end());
  }
  factored_cons.clear();
}

//------------------------------------------------------------------------------
//Factor a cons. of the form (other = *ref + off) or (*ref + off = other).
void Anders::factor_ls(const set<u32> &other, u32 ref, u32 off, bool load){
  u32 szo= other.size();
  assert(szo);
  //dest (for load) or src (for store) will be filled in below.
  Constraint C(load ? load_cons : store_cons, ref, ref, off);
  if(szo < factor_min_sz){
    //Return unfactored cons. to the list.
    for(set<u32>::const_iterator j= other.begin(), je= other.end();
        j != je; ++j){
      if(load)
        C.dest= *j;
      else
        C.src= *j;
      constraints.push_back(C);
    }
  }else{
    //Add (T = *V + k) or (*V + k = T).
    u32 t= nodes.size();
    nodes.push_back(new Node);
    if(load)
      C.dest= t;
    else
      C.src= t;
    constraints.push_back(C);
    //All the original cons. will be mapped to T.
    Constraint C0= C;
    //Add (A = T) or (T = B).
    C.type= copy_cons;
    C.off= 0;
    if(load)
      C.src= t;
    else
      C.dest= t;
    for(set<u32>::const_iterator j= other.begin(), je= other.end();
        j != je; ++j){
      if(load)
        C0.dest= C.dest= *j;
      else
        C0.src= C.src= *j;
      constraints.push_back(C);
      factored_cons[C0]= t;
    }
    ADD_STAT(ls_factored, szo-1);
  }
}

