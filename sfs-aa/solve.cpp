#include "sfs-aa.h"
#include "sfs-work.h"

sfs::Worklist *sfsWL;

bool SFS::solve()
{
  // initialize the node worklist and the priority map
  //
  sfsWL = new sfs::Worklist(dfg.num_nodes());
  priority.assign(dfg.num_nodes(),0);
  
  // insert address-of nodes into worklist
  //
  u32 idx = 0;
  for (tp_it i = dfg.tp_begin(), e = dfg.tp_end(); i != e; ++i, ++idx) {
    if (i->inst.type == addr_of_cons) { sfsWL->push(idx,0); }
  }

  // initialize the timestamp and n_node_runs
  //
  vtime = 1;
  n_node_runs = 0;

  // the main solver loop
  //
  while (1) {
    if (sfsWL->swap_if_empty()) {
      if (sfsWL->empty()) { break; } // solver is complete
    }

    n_node_runs++;

    u32 p; // node's priority
    u32 n = sfsWL->pop(&p);

    // may have been pushed onto the worklist multiple times; if we've
    // visited it already since this instance was pushed, leave it alone
    // (this only matters if we're using a dual worklist)
    //
    if (p < priority[n]) { continue; }
    priority[n] = vtime++;

    switch (dfg.type(n)) {
    case IS_TP: processTp(dfg.get_tp(n));   break;
    case IS_LD: processLd(dfg.get_ld(n),n); break;
    case IS_ST: processSt(dfg.get_st(n),n); break;
    case IS_NP: processNp(dfg.get_np(n));   break;
    default: assert(0 && "unknown type");
    }
  }

  if (USE_MEM_TIME) {
    print_time("solve");
    errs() << "memory == " << (get_mem_usage()+512)/1024 << " MB" << "\n";
  }

  return false;
}

void SFS::processTp(TpNode& N)
{
  bool change = false;

  switch (N.inst.type) {
  case addr_of_cons:
    change = top[N.inst.dest].insert(N.inst.src);
    break;
  case copy_cons:
    change = (top[N.inst.dest] |= top[N.inst.src]);
    break;
  case gep_cons:
    change = (top[N.inst.dest] |= (top[N.inst.src] + N.inst.off));
    break;
  default: assert(0 && "unknown constraint type");
  }

  if (change) {
    FOREACH(uv_cit,i,N.succ) { sfsWL->push(*i,priority[*i]); }
  }
}

// OPT: we could be more precise about only processing the new/changed
//      vars by separating rhs into "new vars" and "old vars"
//
void SFS::processLd(LdNode& N, u32 idx)
{
  // this node may not belong to any partition if it was pruned by the
  // initial SEG in obj_cons_id.cpp
  //
  if (N.pts.empty()) { return; }

  // first we process the load instruction itself

  PtsSet rhs = top[N.inst.src] + N.inst.off;
  const vector<u32>& ptsto = *(bdd2vec(rhs.get_bdd()));

  if (ptsto.empty()) { return; }
  
  bool change = false;
  PtsSet& lhs = top[N.inst.dest];

  if (rhs == N.old) {
    PtsSet old = lhs;
    N.pts.or_changed(lhs,ptsto);
    change = (lhs != old);
  }
  else {
    N.old = rhs;
    FOREACH(uv_cit,i,ptsto) { change |= (lhs |= N.pts[*i]); }
  }

  if (change) { FOREACH(uv_cit,i,N.tl_succ) { sfsWL->push(*i,priority[*i]); }}

  // now we propagate the address-taken ptsto info

  if (N.pts.check()) {
    FOREACH(pmap_it,i,N.part_succ) {
      bool c = false;

      switch (dfg.type(i->first)) {
      case IS_LD:
	{
	  LdNode& S = dfg.get_ld(i->first);
	  if (!S.rep) { c = S.pts.or_part(N.pts,i->second); }
	  else {
	    assert(S.rep == idx);
	    processSharedLd(S,N.pts);
	  }
	}
	break;
      case IS_ST:
	c = dfg.get_st(i->first).in.or_part(N.pts,i->second);
	break;
      case IS_NP:
	c = dfg.get_np(i->first).pts.or_part(N.pts,i->second);
	break;
      default: assert(0 && "unexpected type");
      }

      if (c) { sfsWL->push(i->first,priority[i->first]); }
    }
    N.pts.rst();
  }
}

// OPT: we could be more precise about only processing the new/changed
//      vars for weak updates
//
void SFS::processSt(StNode& N, u32 idx)
{
  // this node may not belong to any partition if it was pruned by the
  // initial SEG in obj_cons_id.cpp
  //
  if (N.out.empty()) { return; }

  PtsSet lhs = top[N.inst.dest] + N.inst.off;
  const vector<u32>& ptsto = *(bdd2vec(lhs.get_bdd()));

  if (ptsto.empty()) { return; }

  PtsSet& rhs = top[N.inst.src];

  if (ptsto.size() == 1 && strong[ptsto.front()]) {
    u32 v = ptsto.front();
    if (N.in.check()) { N.out.or_except(N.in,v); N.in.rst(); }
    N.out.assign_el(v,rhs);
  }
  else {
    if (N.in.check()) { N.out |= N.in; N.in.rst(); }

    if (rhs != N.old1 || lhs != N.old2) {
      FOREACH(uv_cit,i,ptsto) { N.out.or_el(*i,rhs); }
      N.old1 = rhs; N.old2 = lhs;
    }
  }

  if (N.out.check()) {
    FOREACH(pmap_it,i,N.part_succ) {
      bool c = false;

      switch (dfg.type(i->first)) {
      case IS_LD:
	{
	  LdNode& S = dfg.get_ld(i->first);
	  if (!S.rep) { c = S.pts.or_part(N.out,i->second); }
	  else {
	    assert(S.rep == idx);
	    processSharedLd(S,N.out);
	  }
	}
	break;
      case IS_ST:
	c = dfg.get_st(i->first).in.or_part(N.out,i->second);
	break;
      case IS_NP:
	c = dfg.get_np(i->first).pts.or_part(N.out,i->second);
	break;
      default: assert(0 && "unexpected type");
      }

      if (c) { sfsWL->push(i->first,priority[i->first]); }
    }
    N.out.rst();
  }
}

void SFS::processNp(NpNode& N)
{
  if (!N.pts.check()) { return; }

  FOREACH(uv_it,i,N.succ) {
    bool change = false;

    switch (dfg.type(*i)) {
    case IS_LD:
      {
	LdNode& S = dfg.get_ld(*i); assert(!S.rep);
	change = (S.pts |= N.pts);
      }
      break;
    case IS_ST:
      change = (dfg.get_st(*i).in |= N.pts);
      break;
    case IS_NP:
      change = (dfg.get_np(*i).pts |= N.pts);
      break;
    default: assert(0 && "unexpected type");
    }

    if (change) { sfsWL->push(*i,priority[*i]); }
  }

  N.pts.rst();
}

void SFS::processSharedLd(LdNode& N, PtsGraph& pts)
{
  n_node_runs++; // this counts as a processed node

  PtsSet rhs = top[N.inst.src] + N.inst.off;
  const vector<u32>& ptsto = *(bdd2vec(rhs.get_bdd()));
  
  bool change = false;
  PtsSet& lhs = top[N.inst.dest];
  
  if (rhs == N.old) {
    PtsSet old = lhs;
    pts.or_changed(lhs,ptsto);
    change = (lhs != old);
  }
  else {
    N.old = rhs;
    FOREACH(uv_cit,i,ptsto) { change |= (lhs |= pts[*i]); }
  }
  
  if (change) { FOREACH(uv_cit,i,N.tl_succ) { sfsWL->push(*i,priority[*i]); }}

  FOREACH(pmap_it,i,N.part_succ) {
    bool c = false;
    
    switch (dfg.type(i->first)) {
    case IS_LD:
      {
	LdNode& S = dfg.get_ld(i->first); assert(!S.rep);
	c = S.pts.or_part(pts,i->second);
      }
      break;
    case IS_ST:
      c = dfg.get_st(i->first).in.or_part(pts,i->second);
      break;
    case IS_NP:
      c = dfg.get_np(i->first).pts.or_part(pts,i->second);
      break;
    default: assert(0 && "unexpected type");
    }
    
    if (c) { sfsWL->push(i->first,priority[i->first]); }
  }
}
