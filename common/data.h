#ifndef _DATA_H
#define _DATA_H

#include "common.h"

struct DFnode; // forward declaration

// class to collect data about the analysis
//
class Data
{
public:

  //// COUNTERS

  // used by VarInfo for Stats
  //
  static u32 num_vars; // program variables
  static u32 num_top;  // top-level variables
  static u32 num_btm;  // bottom variables
  static u32 nulloff;  // gep offsets too large for any variable

  // used by SSaa for Stats
  //
  static u32 glob_roots; // number of global roots
  static u32 dfg_proc;   // number of processed dfg nodes
  static u32 dfg_change; // number of times a dfg node changed pointer info
  static u32 fun_proc;   // number of functions processed
  static u32 num_alloc;  // number of alloc instructions processed
  static u32 num_copy;   // ditto for copy
  static u32 num_gep;    // ditto for gep
  static u32 num_load;   // ditto for load
  static u32 num_store;  // ditto for store
  static u32 num_store2; // ditto for store2
  static u32 num_call;   // ditto for call
  static u32 num_icall;  // ditto for icall
  static u32 num_ret;    // ditto for ret

  //// SETS

  // used by SSaa for Stats
  //
  static set<DFnode*> icall_res;   // resolved indirect calls
  static set<DFnode*> icall_nores; // unresolved indirect calls
  static set<DFnode*> uniq_dfg;    // number of unique processed dfg nodes
  static set<DFnode*> psv_icalls;  // potentially preserving icalls
  static set<DFnode*> not_psv;     // psv_icalls that aren't really preserving
  static set<Function*> idr_alloc; // indirectly called isAlloc/hasStatic funs

};

u32 Data::num_vars   = 0;
u32 Data::num_top    = 0;
u32 Data::num_btm    = 0;
u32 Data::nulloff    = 0;
u32 Data::glob_roots = 0;
u32 Data::dfg_proc   = 0;
u32 Data::dfg_change = 0;
u32 Data::fun_proc   = 0;
u32 Data::num_alloc  = 0;
u32 Data::num_copy   = 0;
u32 Data::num_gep    = 0;
u32 Data::num_load   = 0;
u32 Data::num_store  = 0;
u32 Data::num_store2 = 0;
u32 Data::num_call   = 0;
u32 Data::num_icall  = 0;
u32 Data::num_ret    = 0;
set<DFnode*> Data::icall_res;
set<DFnode*> Data::icall_nores;
set<DFnode*> Data::uniq_dfg;
set<DFnode*> Data::psv_icalls;
set<DFnode*> Data::not_psv;
set<Function*> Data::idr_alloc;

#endif // _DATA_H
