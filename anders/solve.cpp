/*  [solve.cpp] Constraint solver
 *  v. 014, 2008-09-14
 *------------------------------------------------------------------------------
 *  Changes from 013:
 *  - LCD runs when the candidate set reaches lcd_size; lcd_period disabled
 *  - added a time limit for the solver; time/RAM limits are set in anders.h
 *  - added HCD opt. (at the start of solve_node() and for each load/store)
 *  - factored out add_copy_edge()
 *    - edges to/from i2p are no longer added
 *  - LCD candidates must now have nonempty points_to
 *------------------------------------------------------------------------------
 *  TODO:
 *  - handle indirect calls to varargs and to ext.func. other than allocs
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

#if DEBUG_SOLVE == 0
  #undef DEBUG
  #define DEBUG(x)
#endif

//------------------------------------------------------------------------------
//Initialize the BDDs for points-to sets and GEPs.
void Anders::pts_init(){
  assert(curr_module && "pts_init called when not running on a module");
  u32 npts= last_obj_node+1;
  //The offsets that occur in GEP/load/store constraints.
  set<u32> valid_off;
  FORN(i, constraints.size()){
    const Constraint &C= constraints[i];
    if(C.off){
      valid_off.insert(C.off);
      DEBUG(print_constraint_now(C));
      DEOL;
    }
  }
  //fprintf(stderr, "valid offsets: %u of %u\n", valid_off.count(), max_sz);
  //For each offset (i), off_nodes[i] holds the nodes with obj_sz == (i+1),
  //  i.e. those for which (i) is the max allowed offset.
  vector<set<u32> > off_nodes;
  u32 max_sz= 0;
  FORN(i, npts){
    u32 sz= nodes[i]->obj_sz;
    if(sz < 2)
      continue;
    if(max_sz < sz){
      max_sz= sz;
      off_nodes.resize(sz);
    }
    //Record the node in the largest valid offset.
    u32 off= sz-1;
    for(; off && !valid_off.count(off); --off);
    if(!off)
      continue;
    DEBUG(fprintf(stderr, "off_nodes[%u] <- ", off));
    DEBUG(print_node_now(i));
    DEOL;
    off_nodes[off].insert(i);
  }

  //Use at least 8M nodes, with 1 cache entry per 8 nodes.
  //The second parameter doesn't matter because cacheratio overrides it.
  bdd_init(8000000, 1000);
  bdd_setcacheratio(8);
  //Grow the node table by 1M at a time, when <40% is free.
  bdd_setmaxincrease(1000000);
  bdd_setminfreenodes(40);
  //Allow unlimited growth of the node table
  //  (since we already keep track of memory usage).
  bdd_setmaxnodenum(0);
  //Disable default pre/post-garbage-collection hook.
  bdd_gbc_hook(NULL);
  //We require a particular variable ordering.
  bdd_disable_reorder();

  //Make a BDD domain for the points_to members and another for the result
  //  of GEPs. This should be done with a single call to fdd_extdomain,
  //  so that the variables are interleaved, else making the GEP functions
  //  will be very slow. Also, the points-to domain must be the first
  //  set of BDD variables allocated.
  int domains[]= {npts, npts};
  fdd_extdomain(domains, 2);
  node_vars.assign(npts, bddfalse);
  pts_dom= fdd_ithset(0);
  if(npts >= 2){
    //This will fail if sat2vec assumes the wrong variable order.
    bdd b= get_node_var(npts-1) | get_node_var(npts/3);
    assert(bdd_satcountset(b, pts_dom) == 2 && "test set has wrong size");
    vector<u32> v= *bdd2vec(b);
    assert(v.size() == 2 && "bdd2vec doesn't work");
    assert(v[0] == npts/3 && v[1] == npts-1 && "bdd2vec doesn't work");
  }
  //Set up the domain map.
  gep2pts= bdd_newpair();
  fdd_setpair(gep2pts, 1, 0);
  //Make a bit vector for each domain.
  bvec vpts= bvec_varfdd(0), vgep= bvec_varfdd(1);
  u32 pts_bits= (u32)vpts.bitnum();
  //For each offset, make the GEP function.
  geps.assign(max_sz, bddfalse);
  //The set of nodes with more fields than the current offset.
  bdd om= bddfalse;
  off_mask.assign(max_sz, bddfalse);
  for(set<u32>::reverse_iterator it= valid_off.rbegin(),
      ie= valid_off.rend(); it != ie; ++it){
    u32 off= *it;
    for(set<u32>::iterator it= off_nodes[off].begin(),
        ie= off_nodes[off].end(); it != ie; ++it){
      om |= get_node_var(*it);
    }
    //Vector for (pts+off).
    bvec add= bvec_add(vpts, bvec_con(pts_bits, off));
    //The function starts as the adder mapped into the GEP domain,
    //  so that the GEP vars will hold the set of (x+off) for all x in PTS.
    bdd f= bvec_equ(vgep, add);
    //Restrict the final function's argument to the set of acceptable nodes.
    geps[off]= f & om;
    //Save the current offset mask.
    off_mask[off]= om;
  }
  FORN(i, npts){
    const Node *N= nodes[i];
    if(Function *F= dyn_cast_or_null<Function>(N->get_val())){
      if(extinfo->is_ext(F)){
        assert(N->obj_sz == 1);
        ext_func_nodes |= get_node_var(i);
        ext_func_node_set.insert(i);
        func_node_set.insert(i);
      }else if(N->obj_sz > 1){
        func_node_set.insert(i);
      }
    }
  }
}

//------------------------------------------------------------------------------
void Anders::solve_init(){
  assert(pts_dom != bddfalse && "solve_init called before pts_init");
  u32 nn= nodes.size(), npts= last_obj_node+1;
  //Build the constraint graph and cplx_cons.
  //Note that prev_points_to remains empty for all nodes.
  u32 ncplx= 0;
  cplx_cons.clear();
  FORN(i, constraints.size()){
    const Constraint &C= constraints[i];
    u32 dest= get_node_rep(C.dest), src= get_node_rep(C.src);
    switch(C.type){
      case addr_of_cons:
        assert(src < npts);
        nodes[dest]->points_to |= get_node_var(src);
        break;
      case copy_cons:
        assert(src != dest);
        nodes[src]->copy_to.set(dest);
        INC_STAT(copy_add);
        break;
      case load_cons:
        nodes[src]->load_to.set(ncplx++);
        cplx_cons.push_back(C);
        break;
      case store_cons:
        nodes[dest]->store_from.set(ncplx++);
        cplx_cons.push_back(C);
        break;
      case gep_cons:
        nodes[src]->gep_to.set(ncplx++);
        cplx_cons.push_back(C);
        break;
      default:
        assert(!"unknown constraint type");
    }
  }
  constraints.clear();
  DEBUG(print_cons_graph(0));           //print the complete constraint graph

  //Start the worklist with all nodes that point to something
  //  and have outgoing constraint edges.
  assert(!WL);
  WL= new Worklist(nn);
  DPUTS("***** Initial worklist:");
  FORN(i, nn){
    Node *N= nodes[i];
    if(!N->is_rep())
      continue;
    N->vtime= 0;
    if(N->points_to == bddfalse)
      continue;
    if(N->copy_to.empty() && N->load_to.empty() && N->store_from.empty() &&
        N->gep_to.empty()){
      //If N has no outgoing constraints, we can't do anything with it now.
      continue;
    }
    INC_STAT(node_push);
    WL->push(i, 0);
    DPUTS("  ");
    DEBUG(print_node_now(i));
  }
  DEOL;
  WL->swap_if_empty();
  ext_seen.clear();
  ext_failed.clear();
}

//------------------------------------------------------------------------------
//Returns 0 on completion, 1 on abort.
bool Anders::solve(){
  assert(WL && "solve called without a worklist");
  DPUTS("***** Starting pass 0\n");

  n_node_runs= 0;
  last_lcd= 0;
  vtime= 1;
  bool fail= 0;
  if(USE_MEM_TIME)
    PUTS("solving [");
  while(1){
    if(WL->swap_if_empty()){            //current pass done
      INC_STAT(passes);
      //If nothing is queued for this pass, the graph has converged.
      if(WL->empty())
        break;
      DEBUG(fprintf(stderr, "***** Starting pass %d\n", STAT(passes)));
    }
    u32 p;
    u32 n= WL->pop(&p);
    INC_STAT(node_pop);
    //If a node was merged after the push, it will stay on the list
    //  but should not be processed.
    if(!nodes[n]->is_rep())
      continue;

    if(WL_PRIO != WLP_ID){              //the ID worklist sets vtime to 0
      //This entry may have an earlier vtime if it was pushed onto next and then
      //  popped from curr.
      if(p < nodes[n]->vtime)
        continue;
      //If something was merged into n after it was pushed, its vtime may have
      //  been reduced below p.
    }
    solve_node(n);
    //Check time every 1024 node runs.
    if(USE_MEM_TIME && (n_node_runs&1023) == 0){
      if(get_cpu_time() - start_time > SOLVE_TIME_LIMIT*1000000LL){
        fprintf(stderr, "!! Running longer than %u sec, aborting.\n",
            SOLVE_TIME_LIMIT);
        fail= 1;
        break;
      }
    }
    //Check memory and output a dot every 10000 node runs.
    if(USE_MEM_TIME && (n_node_runs%10000) == 0){
      if(get_mem_usage() > SOLVE_RAM_LIMIT*1024){
        fprintf(stderr, "!! Used over %u MB of RAM, aborting.\n",
            SOLVE_RAM_LIMIT);
        fail= 1;
        break;
      }
      putc('.', stderr);
    }
    //Is it time to do cycle detection?
    if(lcd_starts.size() >= lcd_size || n_node_runs - last_lcd >= lcd_period)
      run_lcd();
  }
  if(USE_MEM_TIME)
    PUTS("]\n");
  if(USE_STATS && !ext_failed.empty()){
    PUTS("!! Unsupported indirect calls of ext. functions:\n");
    for(std::set<string>::iterator it= ext_failed.begin(),
        ie= ext_failed.end(); it != ie; ++it){
      PUTS(it->c_str());
      putc('\n', stderr);
    }
  }

  delete WL;
  WL= 0;
  SET_STAT(node_run, n_node_runs);
  return fail;
}

//------------------------------------------------------------------------------
//Lazy Cycle Detection: detect cycles starting from every node that had a
//  neighbor (across an outgoing copy edge) with an equal points-to set.
void Anders::run_lcd(){
  last_lcd= n_node_runs;
  curr_lcd_dfs= 1;
  lcd_dfs_id.clear();
  lcd_roots.clear();
  //Run DFS starting from every rep node on the list, unless it was already seen
  //  in the current LCD pass.
  INC_STAT(lcd_run);
  DPUTS("LCD starting\n");
  for(set<u32>::const_iterator it= lcd_starts.begin(), ie= lcd_starts.end();
      it != ie; ++it){
    u32 n= *it;
    if(nodes[n]->is_rep() && !lcd_dfs_id.count(n))
      lcd_dfs(n);
  }
  DPUTS("LCD done\n");
  assert(lcd_stk.empty());
  lcd_starts.clear();
}

//------------------------------------------------------------------------------
//Handle the complex constraints of node (n),
//  then propagate its points_to along its copy_to edges.
void Anders::solve_node(u32 n){
  ++n_node_runs;
  Node *N= nodes[n];
  DPUTS("solve_node  ");
  DEBUG(print_node_now(n));
  DEBUG(fprintf(stderr, "  vtime: %u -> %u\n", N->vtime, vtime));
  N->vtime= vtime++;

  //Points-to bits added to N since the last visit.
  bdd d_points_to= N->points_to - N->prev_points_to;
  //If this node was on the prev. worklist, it may have been processed
  //  (updating the points_to) after getting added to the curr. list.
  if(d_points_to == bddfalse)
    return;
  const vector<u32> *d_points_to_v= bdd2vec(d_points_to);
  const u32 *pdpts= &(d_points_to_v->at(0));
  const u32 *edpts= pdpts + d_points_to_v->size();

  //This takes constant time with BDDs.
  N->prev_points_to= N->points_to;

  //If we collapse our points_to via HCD, this will be its rep.
  u32 hcd_rep= 0;
  //Is there an offline cycle (*N, HV)?
  DenseMap<u32, u32>::iterator i_hv= hcd_var.find(n);
  if(i_hv != hcd_var.end()){
    DPUTS("HCD starting\n");
    //Then merge everything in our points_to with HV.
    hcd_rep= get_node_rep(i_hv->second);
    bool chg= 0;
    for(const u32 *ip= pdpts; ip != edpts; ++ip){
      u32 x= get_node_rep(*ip);
      if(x != hcd_rep && x != i2p){
        INC_STAT(hcd_on_sccn);
        hcd_rep= merge_nodes(hcd_rep, x);
        chg= 1;
      }
    }
    DPUTS("HCD done\n");
    if(chg){                  //don't count the SCC if nothing was merged
      INC_STAT(hcd_on_sccn);
      INC_STAT(hcd_on_scc);
    }
  }
  //The final rep of the SCC goes on the worklist.
  INC_STAT(node_push);
  WL->push(hcd_rep, nodes[hcd_rep]->vtime);
  //N can be non-rep if it either pointed to itself or was == HV.
  assert(nodes[n]->is_rep() || get_node_rep(n) == hcd_rep);

  //Because points_to changed, we need to go over the complex constraints again
  //  and propagate d_points_to along the copy edges.
  //All of these steps were factored out for profiling.
  //Each complex constraint is updated to refer to the rep node. This may
  //  introduce duplicates into the list, which will be deleted.
  set<Constraint> cons_seen;

  for(bitmap::iterator it= N->load_to.begin(), ie= N->load_to.end();
      it != ie; ){
    u32 cid= *it;
    //Move past the current element because we may erase it.
    ++it;
    if(solve_ls_cons(n, hcd_rep, d_points_to, cons_seen, cplx_cons[cid])){
      N->load_to.reset(cid);
      INC_STAT(ccons_del);
    }
  }

  cons_seen.clear();
  for(bitmap::iterator it= N->store_from.begin(), ie= N->store_from.end();
      it != ie; ){
    u32 cid= *it;
    ++it;
    if(solve_ls_cons(n, hcd_rep, d_points_to, cons_seen, cplx_cons[cid])){
      N->store_from.reset(cid);
      INC_STAT(ccons_del);
    }
  }

  cons_seen.clear();
  for(bitmap::iterator it= N->gep_to.begin(), ie= N->gep_to.end();
      it != ie; ){
    u32 cid= *it;
    ++it;
    if(solve_gep_cons(n, d_points_to, cons_seen, cplx_cons[cid])){
      N->gep_to.reset(cid);
      INC_STAT(ccons_del);
    }
  }

  solve_prop(n, d_points_to);
}

//------------------------------------------------------------------------------
//Add the copy edges for the load or store constraint (C);
//  all the other args are local vars in solve_node().
//Note that (C) will be updated in place with the node reps.
//Returns true if (C) became redundant.
bool Anders::solve_ls_cons(u32 n, u32 hcd_rep, bdd d_points_to,
    set<Constraint> &cons_seen, Constraint &C){
  bool load= C.type == load_cons;
  assert(load || C.type == store_cons);
  //This has to be done on every call because solve_ls_off() may invalidate
  //  the cache entry for d_points_to.
  const vector<u32> *d_points_to_v= bdd2vec(d_points_to);
  const u32 *pdpts= &(d_points_to_v->at(0));
  const u32 *edpts= pdpts + d_points_to_v->size();
  Constraint C0= C;
  u32 dest0= C.dest, src0= C.src;
  u32 dest= get_node_rep(dest0), src= get_node_rep(src0), off= C.off;
  //Is N a func.ptr used for indirect calls?
  bool ind_call= ind_calls.count(n);
  //If C is used for an actual ind. call, this will point to its insn.
  set<Instruction*> *I= 0;

  if(load){
    //If n2 was merged into n, C.src may still be n2.
    assert(src == n);
    //Update C with the rep of src/dest.
    C.src= n;
    C.dest= dest;
  }else{
    assert(dest == n);
    C.dest= n;
    C.src= src;
  }
  if(ind_call){
    //Use the original (pre-merge) cons. since icall_cons
    //  is not updated when merging.
    DenseMap<Constraint, set<Instruction*> >::iterator i_icc=
        icall_cons.find(C0);
    if(i_icc != icall_cons.end()){
      I= &(i_icc->second);
      if(dest != dest0 || src != src0){
        //If dest/src was merged, update icall_cons, so that we handle this
        //  call site again whenever a new ext.func enters our points_to.
        //Copy the current insn. set, delete the old entry (including the
        //  original copy of the set), point I to the new cons. entry
        //  and merge the current set into it.
        set<Instruction*> II(*I);
        icall_cons.erase(i_icc);
        I= &(icall_cons[C]);
        I->insert(II.begin(), II.end());
      }
    }
  }

  //If (C) was seen before, it's obviously redundant,
  //  but we should still handle ind. calls for (C0).
  if(cons_seen.count(C)){
    if(I){
      assert((load && off == 1) || (!load && off >= 2) &&
          "wrong offset for icall retval or arg");
      for(const u32 *ip= pdpts; ip != edpts; ++ip){
        u32 rn= *ip;
        const Node *R= nodes[rn];
        Function *F= dyn_cast_or_null<Function>(R->get_val());
        if(F && extinfo->is_ext(F)){
          for(set<Instruction*>::iterator it= I->begin(), ie= I->end();
              it != ie; ++it){
            handle_ext(F, *it);
          }
        }
      }
    }
    return 1;
  }
  cons_seen.insert(C);
  DPUTS(load ? "  load_cons  " : "  store_cons  ");
  DEBUG(print_node_now(load ? dest : src));
  DEBUG(fprintf(stderr, "  +%u  ", off));
  if(I)
    DPUTS(load ? "(ind_call retval)  " : "(ind_call arg)  ");

  //If our points_to was collapsed via HCD, we only need to add the edge
  //  from its rep. Note that loads with offset are still handled using
  //  the full poins_to, since HCD says nothing about the nodes
  //  at some offset from these members.
  if(hcd_rep && !off){
    assert(!I && "ind. call cons. has no offset");
    assert(nodes[hcd_rep]->is_rep());
    if(load){
      if(add_copy_edge(hcd_rep, dest)){
        INC_STAT(node_push);
        WL->push(dest, nodes[dest]->vtime);
      }
    }else{
      if(add_copy_edge(src, hcd_rep)){
        INC_STAT(node_push);
        WL->push(hcd_rep, nodes[hcd_rep]->vtime);
      }
    }
    DPUTS("<HCD>\n");
    //This cons. is now redundant because all future members of our points_to
    //  will be pointer-equivalent to hcd_rep, which already has the edge.
    return 1;
  }

  if(off){
    solve_ls_off(d_points_to, load, dest, src, off, I);
  }else{
    assert(!I);
    solve_ls_n(pdpts, edpts, load, dest, src);
  }

  DEOL;
  return 0;
}

//------------------------------------------------------------------------------
//The main loop of solve_ls_cons(), separated for profiling.
//The first version is for load/store with offset, and the second
//  is for normal load/store (offset 0).
void Anders::solve_ls_off(bdd d_points_to, bool load,
    u32 dest, u32 src, u32 off, const set<Instruction*> *I){
  //Remove points-to members too small for the offset.
  //However, if this is an ind. call, we must keep all ext. function nodes
  //  because they all have obj_sz 1.
  bdd mask= I ? off_mask[off] | ext_func_nodes : off_mask[off];
  bdd m_points_to= d_points_to & mask;
  if(m_points_to == bddfalse)
    return;
  const vector<u32> *d_points_to_v= bdd2vec(m_points_to);
  const u32 *pdpts= &(d_points_to_v->at(0));
  const u32 *edpts= pdpts + d_points_to_v->size();
  //Did D.points_to change? (for load only).
  bool chg= 0;                        
  for(const u32 *ip= pdpts; ip != edpts; ++ip){
    //Use the original points-to member (rather than the rep)
    //  to check for ext.func. and to compare offset/obj_sz.
    u32 rn= *ip;
    DEBUG(putc('{', stderr));
    DEBUG(print_node_now(rn));
    DEBUG(putc('}', stderr));
    //In case of ind. call, check if rsrc is an ext. function.
    if(I){
      assert((load && off == 1) || (!load && off >= 2) &&
          "wrong offset for icall retval or arg");
      //When handling an ind.call cons, skip non-func. members.
      if(!func_node_set.count(rn))
        continue;
      const Node *R= nodes[rn];
      if(ext_func_node_set.count(rn)){
        Function *F= dyn_cast_or_null<Function>(R->get_val());
        for(set<Instruction*>::iterator it= I->begin(), ie= I->end();
            it != ie; ++it){
          handle_ext(F, *it);
        }
        continue;
      }
      //For non-ext func, check if the offset is in range.
      //  The return and vararg nodes of non-ext func. have Function*
      //  values but obj_sz == 1, so only the node of the function itself
      //  will be processed.
//      assert(R->obj_sz > off);
      DPUTS("(non-ext)");
    }else if(func_node_set.count(rn)){
      //Skip load/store with a function if this cons.
      //  is not an actual ind. call.
      continue;
      //This is now an assert because we use off_mask (but it's disabled
      //  because checking the obj_sz is slow).
//    }else{
//      assert(nodes[rn]->obj_sz > off);
    }
    rn= get_node_rep(rn+off);
    if(load){
      if(add_copy_edge(rn, dest)){
        chg= 1;
      }
    }else{
      //Don't store into non-ptr args.
      if(I){
        Value *V= nodes[rn]->get_val();
        //Note: V may be null due to constraint factoring.
        if(V && !isa<PointerType>(V->getType()))
          continue;
      }
      if(add_copy_edge(src, rn)){
        INC_STAT(node_push);
        WL->push(rn, nodes[rn]->vtime);
      }
    }
  }
  if(chg){
    INC_STAT(node_push);
    WL->push(dest, nodes[dest]->vtime);
  }
}

//------------------------------------------------------------------------------
void Anders::solve_ls_n(const u32 *pdpts, const u32 *edpts, bool load,
    u32 dest, u32 src){
  bool chg= 0;                        
  for(const u32 *ip= pdpts; ip != edpts; ++ip){
    u32 rn= get_node_rep(*ip);
    DEBUG(putc('{', stderr));
    DEBUG(print_node_now(rn));
    DEBUG(putc('}', stderr));
    if(load){
      if(add_copy_edge(rn, dest)){
        chg= 1;
      }
    }else{
      if(add_copy_edge(src, rn)){
        INC_STAT(node_push);
        WL->push(rn, nodes[rn]->vtime);
      }
    }
  }
  if(chg){
    INC_STAT(node_push);
    WL->push(dest, nodes[dest]->vtime);
  }
}

//------------------------------------------------------------------------------
//Handle the GEP constraint (C).
bool Anders::solve_gep_cons(u32 n, bdd d_points_to,
  set<Constraint> &cons_seen, Constraint &C){
  assert(C.type == gep_cons);
  //If n2 was merged into n, C.src may still be n2.
  assert(get_node_rep(C.src) == n);
  C.src= n;
  u32 dest= get_node_rep(C.dest), off= C.off;
  C.dest= dest;
  if(cons_seen.count(C)){
    return 1;
  }
  cons_seen.insert(C);
  DPUTS("  gep_cons  ");
  DEBUG(print_node_now(dest));
  DPUTS("  ");
  Node *D= nodes[dest];
  bdd prev_pts= D->points_to;
  assert(off < geps.size() && geps[off] != bddfalse);
  //Apply the GEP function with the given offset (removing variables
  //  in the domain from the result) and map it back to the domain.
  D->points_to |= bdd_replace(bdd_relprod(d_points_to,
      geps[off], pts_dom), gep2pts);
  if(D->points_to != prev_pts){
    DEBUG(putc('*', stderr));
    INC_STAT(node_push);
    WL->push(dest, D->vtime);
  }
  DEOL;
  return 0;
}

//------------------------------------------------------------------------------
//Add the copy edge from (src) to (dest) and copy the entire points_to.
//Returns whether the points_to of (dest) changed.
//This doesn't push (dest) on the worklist, so that we can add several
//  edges toward (dest) and do 1 push at the end.
bool Anders::add_copy_edge(u32 src, u32 dest){
  //We don't want i2p to point to anything, so don't add edges to it.
  //Neither do we add edges from i2p, as there's nothing to propagate.
  //Also avoid edges from a node to itself.
  if(src == i2p || dest == i2p || src == dest)
    return 0;
  Node *S= nodes[src];
  if(S->copy_to.test_and_set(dest)){
    DEBUG(putc('c', stderr));
    INC_STAT(copy_add);
    Node *D= nodes[dest];
    bdd prev_pts= D->points_to;
    D->points_to |= S->points_to;
    if(D->points_to != prev_pts){
      DEBUG(putc('*', stderr));
      return 1;
    }
  }
  return 0;
}

//------------------------------------------------------------------------------
//Propagate (d_points_to) along all copy edges from node (n).
void Anders::solve_prop(u32 n, bdd d_points_to){
  Node *N= nodes[n];
  set<u32> copy_seen;
  for(bitmap::iterator it= N->copy_to.begin(), ie= N->copy_to.end(); it != ie;
      ++it){
    u32 dest0= *it;
    assert(dest0 != n && "copy self-loop not removed");
    u32 dest= get_node_rep(dest0);
    DPUTS("  copy edge  ");
    DEBUG(print_node_now(dest));
    //If the rep of this copy dest. is n itself, or if we already propagated
    //  to it, it can be skipped.
    if(dest == n || copy_seen.count(dest))
      continue;
    copy_seen.insert(dest);
    Node *D= nodes[dest];
    pair<u32, u32> E(n, dest);
    //If this is the first time N and D had equal (nonempty) points_to,
    //  do a cycle check starting from N.
    if(!lcd_edges.count(E) && N->points_to != bddfalse){
      if(N->points_to == D->points_to){
        lcd_edges.insert(E);
        lcd_starts.insert(n);
      }
    }
    bdd prev_pts= D->points_to;
    D->points_to |= d_points_to;
    if(D->points_to != prev_pts){
      DPUTS("  *");
      INC_STAT(node_push);
      WL->push(dest, D->vtime);
    }
    DEOL;
  }
}

//------------------------------------------------------------------------------
//Add the edges for the indirect call (I) of ext.func (F).
NOINLINE void Anders::handle_ext(Function *F, Instruction *I){
  assert(extinfo->is_ext(F));
  pair<Function*, Instruction*> arg(F, I);
  if(ext_seen.count(arg))
    return;
  ext_seen.insert(arg);
  CallSite CS(I);
  extf_t tF= extinfo->get_type(F);
  switch(tF){
    case EFT_ALLOC:
    case EFT_NOSTRUCT_ALLOC:{
      //For is_alloc, point the caller's copy of the retval to its object
      //  (making sure the retval is actually used).
      if(!isa<PointerType>(I->getType()))
        break;
      u32 vnD= get_node_rep(get_val_node(I));
      u32 onD= get_obj_node(I);
      Node *D= nodes[vnD];
      DEBUG(fprintf(stderr, "(alloc: %s: ", F->getName().c_str()));
      DEBUG(print_node_now(vnD));
      DPUTS(" -> ");
      DEBUG(print_node_now(onD));
      DEBUG(putc(')', stderr));
      bdd prev_pts= D->points_to;
      D->points_to |= get_node_var(onD);
      if(D->points_to != prev_pts){
        DEBUG(putc('*', stderr));
        INC_STAT(ind_alloc);
        INC_STAT(node_push);
        WL->push(vnD, D->vtime);
      }
      break;
    }
    case EFT_REALLOC:
      //The function pointer may point to realloc at one time
      //  and to a function with fewer args at another time;
      //  we should skip the realloc if the current call has fewer args.
      if(CS.arg_size() < 1)
        break;
      if(isa<ConstantPointerNull>(CS.getArgument(0))){
        if(!isa<PointerType>(I->getType()))
          break;
        DPUTS("realloc:(alloc)");
        u32 vnD= get_node_rep(get_val_node(I));
        u32 onD= get_obj_node(I);
        Node *D= nodes[vnD];
        bdd prev_pts= D->points_to;
        D->points_to |= get_node_var(onD);
        if(D->points_to != prev_pts){
          DEBUG(putc('*', stderr));
          INC_STAT(ind_alloc);
          INC_STAT(node_push);
          WL->push(vnD, D->vtime);
        }
        break;
      }
      DPUTS("realloc:");
    case EFT_L_A0:
    case EFT_L_A1:
    case EFT_L_A2:
    case EFT_L_A8:{
      if(!isa<PointerType>(I->getType()))
        break;
      u32 vnD= get_node_rep(get_val_node(I));
      u32 i_arg;
      switch(tF){
        case EFT_L_A1: i_arg= 1; break;
        case EFT_L_A2: i_arg= 2; break;
        case EFT_L_A8: i_arg= 8; break;
        default: i_arg= 0;
      }
      if(CS.arg_size() <= i_arg)
        break;
      DEBUG(fprintf(stderr, "(L_A%u)", i_arg));
      Value *src= CS.getArgument(i_arg);
      if(isa<PointerType>(src->getType())){
        u32 vnS= get_node_rep(get_val_node(src, 1));
        if(vnS){
          if(add_copy_edge(vnS, vnD)){
            INC_STAT(node_push);
            WL->push(vnD, nodes[vnD]->vtime);
          }
        }
      }else{
        Node *D= nodes[vnD];
        bdd prev_pts= D->points_to;
        D->points_to |= get_node_var(i2p);
        if(D->points_to != prev_pts){
          DEBUG(putc('*', stderr));
          INC_STAT(ind_alloc);
          INC_STAT(node_push);
          WL->push(vnD, D->vtime);
        }
      }
      break;
    }
    case EFT_NOOP:
    case EFT_OTHER:
      //No-op and unknown func. have no effect.
      DPUTS("(no-op)");
      break;
    default:
      //FIXME: support other types
      ext_failed.insert(F->getName());
  }
}

//------------------------------------------------------------------------------
//Detect cycles starting from node #n,
//  using Nuutila's version of Tarjan's algorithm.
//When a strongly-connected component is found, all nodes in it are unified.
void Anders::lcd_dfs(u32 n){
  assert(n != i2p && !lcd_roots.count(n));
  Node *N= nodes[n];
  assert(N->is_rep());
  u32 our_dfs= curr_lcd_dfs++;
  lcd_dfs_id[n]= our_dfs;
  //If any of n's edges point to non-rep nodes, they will be updated.
  bitmap del_copy, add_copy;

  for(bitmap::iterator it= N->copy_to.begin(), ie= N->copy_to.end();
      it != ie; ++it){
    u32 dest0= *it;
    assert(dest0 != n && "copy self-loop not removed");
    u32 dest= get_node_rep(dest0);
    //Delete and skip any edge whose replacement is already there
    //  or would copy (n) to itself.
    if(add_copy.test(dest) || dest == n){
      INC_STAT(copy_del);
      del_copy.set(dest0);
      continue;
    }

    //Note that dest may be an already collapsed SCC.
    if(!lcd_roots.count(dest)){
      //Recurse on dest if it hasn't been visited by this LCD pass;
      //  this may merge dest.
      if(!lcd_dfs_id.count(dest)){
        lcd_dfs(dest);
        dest= get_node_rep(dest);
      }
      //If dest (or any successor) was visited in this pass before us, it must
      //  be the root, so set our dfs_id to the root's id.
      if(lcd_dfs_id[dest] < lcd_dfs_id[n])
        lcd_dfs_id[n]= lcd_dfs_id[dest];
    }

    //If the dest. was merged (such as by the recursion above),
    //  make the edge point to the rep.
    if(dest != dest0){
      del_copy.set(dest0);
      //Don't add the replacement if it's already there.
      if(add_copy.test(dest)){
        INC_STAT(copy_del);
        continue;
      }
      assert(dest != n && "copy self-loop not removed");
      add_copy.set(dest);
    }
  }
  assert(N->is_rep());
  N->copy_to.intersectWithComplement(del_copy);
  N->copy_to |= add_copy;

  //If our dfs_id is unchanged, N is the root of an SCC.
  if(lcd_dfs_id[n] == our_dfs){
    bool chg= 0;                        //was (n) merged?
    while(!lcd_stk.empty()){
      u32 n2= lcd_stk.top();
      //Anything visited before us should remain on the stack.
      if(lcd_dfs_id[n2] < our_dfs)
        break;
      lcd_stk.pop();
      //Note: n2 may have been merged using HCD.
      u32 rn2= get_node_rep(n2);
      if(rn2 != n){
        INC_STAT(lcd_sccn);
        n= merge_nodes(n, rn2);
      }
      chg= 1;
    }
    //Once this SCC is collapsed, the root should not be processed again.
    lcd_roots.insert(n);
    if(chg){
      //N also counts as part of its SCC.
      INC_STAT(lcd_sccn);
      INC_STAT(lcd_scc);                  //1 more SCC detected
      WL->push(n, nodes[n]->vtime);
    }
  }else
    //Save N until we get back to the root.
    lcd_stk.push(n);
}
