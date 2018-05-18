#ifndef _STATS_H
#define _STATS_H

#include "common.h"
#include "cg.h"
#include "../sso-fs/dfg.h"
#include "data.h"
#include "../sso-fs/varinfo.h"
#include "../sso-fs/ptrinfo.bdd.h"
using llvm::errs;
using llvm::dbgs;

// class to display various statistics about the analysis
//
class Stats : protected Data
{
public:

  // statistics up to but not including the main analysis loop
  //
  static void print_pre(Module&,CG&,VarInfo&,DFG&);

  // statistics for the main analysis loop
  //
  static void print_post(DFG&,PtrInfo&);

};

//// PUBLIC METHODS

void Stats::print_pre(Module& M, CG& cg, VarInfo& vi, DFG& dfg)
{
  dbgs() << "CG STATS:" << "\n";
  cg.stats(M);

  dbgs() << "VARINFO STATS:" << "\n"
       << "  top-level vars == " << num_top << "\n"
       << "     bottom vars == " << num_btm << "\n"
       << "      total vars == " << num_vars << "\n" 
       << "null GEP offsets == " << nulloff << "\n";

  vi.stats();
  dbgs() << "\n";

  dbgs() << "DFG STATS:" << "\n";
  dfg.stats(M);
}

void Stats::print_post(DFG &dfg, PtrInfo &ti)
{
  dbgs() << "total functions == " << fun_proc << "\n" << "\n";

  dbgs() << "unique DFnodes == " << uniq_dfg.size() << "\n"
       << " total DFnodes == " << dfg_proc << "\n"
       << "    efficiency == " << (float)dfg_change/dfg_proc << "\n" << "\n";

  vector<DFnode*> nodes;
  u32 gep_null = 0, cpy_null = 0;

  for (DFG::dfg_it i = dfg.begin(), e = dfg.end(); i != e; ++i) {
    dfg.getDFnodes(i->second,nodes);
    for (dfnv_it j = nodes.begin(), e = nodes.end(); j != e; ++j) {
      if (!uniq_dfg.count(*j)) { continue; }

      if ((*j)->pi.op == GEP) {
	if (ti.null((*j)->pi.lhs)) { ++gep_null; }
      }
      else if ((*j)->pi.op == COPY) {
	if (ti.null((*j)->pi.lhs)) { ++cpy_null; }
      }
    }
    nodes.clear();
  }

  dbgs() << "breakdown:" << "\n"
       << " -- alloc  == " << num_alloc << "\n"
       << " -- copy   == " << num_copy << " (" << cpy_null
       << " null visited nodes)" << "\n"
       << " -- gep    == " << num_gep << " (" << gep_null
       << " null visited nodes)" << "\n"
       << " -- load   == " << num_load << "\n"
       << " -- store  == " << num_store << "\n"
       << " -- store2 == " << num_store2 << "\n"
       << " -- call   == " << num_call << "\n"
       << " -- icall  == " << num_icall << "\n"
       << " -- ret    == " << num_ret << "\n" << "\n";

  dbgs() << "unresolved indirect calls == " << icall_nores.size() << "\n";

  dfns_it k;

  for (dfns_it i = icall_nores.begin(), e = icall_nores.end(); i != e; ) {
    if (icall_res.count(*i)) { k = i; ++i; icall_nores.erase(k); }
    else                     { ++i; }
  }

  dbgs() << "   final unresolved calls == " << icall_nores.size()
       << " / " << icall_nores.size() + icall_res.size() << "\n";

  dbgs() << "indirect isAlloc/hasStatic calls: " << idr_alloc.size() << "\n";

  for (funs_it i = idr_alloc.begin(), e = idr_alloc.end(); i != e; ++i) {
    dbgs() << "\t" << (*i)->getName() << "\n";
  }
  dbgs() << "\n";

  dbgs() << "potential preserving icalls == " << psv_icalls.size() << "\n"
       << "   actual preserving icalls == " << psv_icalls.size()-not_psv.size()
       << "\n" << "\n";

#ifdef PTRINFO_BIT
  set<PtrInfo*> seen;
  u64 num_bits = 0, num_els = 0;

  for (DFG::dfg_it i = dfg.begin(), e = dfg.end(); i != e; ++i) {
    dfg.getDFnodes(i->second,nodes);

    for (dfnv_it j = nodes.begin(), e = nodes.end(); j != e; ++j) {
      DFnode *n = *j;

      if (n->in && !seen.count(n->in)) { 
	seen.insert(n->in);
	num_bits += n->in->size(); num_els += n->in->num_els();
      }

      if (n->out && !seen.count(n->out)) { 
	seen.insert(n->out);
	num_bits += n->out->size(); num_els += n->out->num_els();
      }
    }

    nodes.clear();
  }

  num_bits += ti.size();
  num_els += ti.num_els();

  dbgs() << " points-to bits == " << num_bits << "\n"
       << "  points-to els == " << num_els << "\n"
       << "average density == " << (double)num_bits/num_els << "\n"
       << "   wasted space == " << (u32)(((num_els*(double)(BM_ELSZ+64)/8)-num_bits)/(1024*1024)) << " MB" << "\n"
       << " alloc stack sz == " << bitmap::stack_size() << " ("
       << ((double)(BM_ELSZ+64)/8*bitmap::stack_size())/(1024*1024)
       << " MB)" << "\n" << "\n";

#endif
}

#endif // _STATS_H
