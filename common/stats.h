#ifndef _STATS_H
#define _STATS_H

#include "common.h"
#include "cg.h"
#include "dfg.h"
#include "data.h"
#include "varinfo.h"
#include PTRINFO_H

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
  cout << "CG STATS:" << endl;
  cg.stats(M);

  cout << "VARINFO STATS:" << endl
       << "  top-level vars == " << num_top << endl
       << "     bottom vars == " << num_btm << endl
       << "      total vars == " << num_vars << endl 
       << "null GEP offsets == " << nulloff << endl;

  vi.stats();
  cout << endl;

  cout << "DFG STATS:" << endl;
  dfg.stats(M);
}

void Stats::print_post(DFG &dfg, PtrInfo &ti)
{
  cout << "total functions == " << fun_proc << endl << endl;

  cout << "unique DFnodes == " << uniq_dfg.size() << endl
       << " total DFnodes == " << dfg_proc << endl
       << "    efficiency == " << (float)dfg_change/dfg_proc << endl << endl;

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

  cout << "breakdown:" << endl
       << " -- alloc  == " << num_alloc << endl
       << " -- copy   == " << num_copy << " (" << cpy_null
       << " null visited nodes)" << endl
       << " -- gep    == " << num_gep << " (" << gep_null
       << " null visited nodes)" << endl
       << " -- load   == " << num_load << endl
       << " -- store  == " << num_store << endl
       << " -- store2 == " << num_store2 << endl
       << " -- call   == " << num_call << endl
       << " -- icall  == " << num_icall << endl
       << " -- ret    == " << num_ret << endl << endl;

  cout << "unresolved indirect calls == " << icall_nores.size() << endl;

  dfns_it k;

  for (dfns_it i = icall_nores.begin(), e = icall_nores.end(); i != e; ) {
    if (icall_res.count(*i)) { k = i; ++i; icall_nores.erase(k); }
    else                     { ++i; }
  }

  cout << "   final unresolved calls == " << icall_nores.size()
       << " / " << icall_nores.size() + icall_res.size() << endl;

  cout << "indirect isAlloc/hasStatic calls: " << idr_alloc.size() << endl;

  for (funs_it i = idr_alloc.begin(), e = idr_alloc.end(); i != e; ++i) {
    cout << "\t" << (*i)->getNameStr() << endl;
  }
  cout << endl;

  cout << "potential preserving icalls == " << psv_icalls.size() << endl
       << "   actual preserving icalls == " << psv_icalls.size()-not_psv.size()
       << endl << endl;

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

  cout << " points-to bits == " << num_bits << endl
       << "  points-to els == " << num_els << endl
       << "average density == " << (double)num_bits/num_els << endl
       << "   wasted space == " << (u32)(((num_els*(double)(BM_ELSZ+64)/8)-num_bits)/(1024*1024)) << " MB" << endl
       << " alloc stack sz == " << bitmap::stack_size() << " ("
       << ((double)(BM_ELSZ+64)/8*bitmap::stack_size())/(1024*1024)
       << " MB)" << endl << endl;

#endif
}

#endif // _STATS_H
