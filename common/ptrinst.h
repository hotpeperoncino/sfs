#ifndef _PTRINST_H
#define _PTRINST_H

#include "common.h"

// pointer-related operations
//
enum PtrOp { NOOP,      // no-op
             CALL,      // direct internal function call
             ICALL,     // indirect function call
             RET,       // return
             COPY,      //  p =  q
             ALLOC,     //  p = &q
             LOAD,      //  p = *q
             STORE,     // *p =  q
             STORE2,    // *p = *q
	     GEP,       // GetElementPtr
             NUM_OPS };

// pointer instruction
//
class PtrInst
{
public:

  PtrOp op;    // the pointer operation
  Value *inst; // the corresponding LLVM instruction

  u32 lhs, off;    // left-hand side; offset (for GEP, STORE2)
  vector<u32> rhs; // right-hand side (used for args for [I]CALL)

  PtrInst() : op(NOOP), inst(0), lhs(0), off(0) {}
  PtrInst(PtrOp _op, Value *_inst) : op(_op), inst(_inst), lhs(0), off(0) {}
  PtrInst(PtrOp _op, u32 _lhs, Value *_inst): op(_op), inst(_inst), 
					      lhs(_lhs), off(0) {}

  static string StrOp(PtrOp o)
  {
    if (strop.empty()) {
      strop[NOOP]   = "noop";
      strop[CALL]   = "call";
      strop[ICALL]  = "icall";
      strop[RET]    = "ret";
      strop[COPY]   = "copy";
      strop[ALLOC]  = "alloc";
      strop[LOAD]   = "load";
      strop[STORE]  = "store";
      strop[STORE2] = "store2";
      strop[GEP]    = "gep";
    }

    return strop[o];
  }

private:

  static map<PtrOp,string> strop;
};

map<PtrOp,string> PtrInst::strop;


#endif // _PTRINST_H
