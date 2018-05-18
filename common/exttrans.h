#ifndef _EXTTRANS_H
#define _EXTTRANS_H

#include "common.h"
#include "extinfo.h"
#include "ptrinst.h"
#include "../sso-fs/varinfo.h"
using llvm::errs;
using llvm::dbgs;

extern ExtInfo *ext;

// translates an external call into the approprate pointer
// instruction
//
// separated from ExtInfo to break a circular dependence: VarInfo
// needs ExtInfo, while ExtTrans needs VarInfo
//
class ExtTrans
{
public:
  
  // translate an external function call into a pointer instruction
  //
  static PtrInst translate(CallInst*,Function*,VarInfo*);

private:

  static u32 get_max_offset(Value*,VarInfo*);
};

//// PUBLIC METHODS

PtrInst ExtTrans::translate(CallInst *ci, Function *F, VarInfo *vi)
{
  PtrInst pi;
  pi.inst = ci;
  CallSite cs(ci);
  Value *arg = 0, *dst = 0, *src = 0;

  // IMPORTANT NOTE: for the DFG to be sound external calls translated
  // to ALLOC, COPY, or LOAD need to modify the lhs of the call

  switch (ext->get_type(F)) {
  case EFT_L_A0:
    if (cs.arg_size() < 1) { errs() << "!!" << "\n"; break; }
    arg = cs.getArgument(0);
    // lack of break deliberate
  case EFT_L_A1:
    if (!arg) { 
      if (cs.arg_size() < 2) { errs() << "!!" << "\n"; break; }
      arg = cs.getArgument(1);
    }
    // lack of break deliberate
  case EFT_L_A2:
    if (!arg) { 
      if (cs.arg_size() < 3) { errs() << "!!" << "\n"; break; }
      arg = cs.getArgument(2);
    }
    // lack of break deliberate
  case EFT_L_A8:
    if (!arg) { 
      if (cs.arg_size() < 9) { errs() << "!!" << "\n"; break; }
      arg = cs.getArgument(8);
    }
    if (!isa<ConstantPointerNull>(arg) && !isa<UndefValue>(arg) &&
	isa<PointerType>(arg->getType())) {
      pi.lhs = vi->getTrans(ci);
      if (!pi.lhs) { errs() << "!!" << "\n"; return pi; }
      pi.op = COPY;
      pi.rhs.push_back((*vi)[arg]);
    }
    break;
  case EFT_L_A0__A0R_A1R:
    if (cs.arg_size() < 2) { errs() << "!!" << "\n"; break; }
    dst = cs.getArgument(0);
    src = cs.getArgument(1);
    
    if (!isa<ConstantPointerNull>(dst) && !isa<UndefValue>(dst) &&
	!isa<ConstantPointerNull>(src) && !isa<UndefValue>(src)) {
      pi.op = STORE2;
      pi.lhs = (*vi)[dst];
      pi.rhs.push_back((*vi)[src]);
      
      // figure out if this is a struct copy and set the offset
      // appropriately (we conservatively assume we're copying the
      // entire struct)
      //
      u32 off_1 = get_max_offset(dst,vi), off_2 = get_max_offset(src,vi);
      pi.off = (off_1 < off_2) ? off_1 : off_2;

      if (isa<PointerType>(ci->getType())) {
	errs() << "EFT_L_A0__A0R_A1R: ret value ignored" << "\n";
      }
    }
    break;
  case EFT_A3R_A1R_NS:
    if (cs.arg_size() < 4) { errs() << "!!" << "\n"; break; }
    dst = cs.getArgument(3);
    src = cs.getArgument(1);
    
    if (!isa<ConstantPointerNull>(dst) && !isa<UndefValue>(dst) &&
	!isa<ConstantPointerNull>(src) && !isa<UndefValue>(src)) {
      pi.op = STORE2;
      pi.off = 1;
      pi.lhs = (*vi)[dst];
      pi.rhs.push_back((*vi)[src]);
    }
    break;
  case EFT_A1R_A0R:
    if (cs.arg_size() < 2) { errs() << "!!" << "\n"; break; }
    dst = cs.getArgument(1);
    src = cs.getArgument(0);
    
    if (!isa<ConstantPointerNull>(dst) && !isa<UndefValue>(dst) &&
	!isa<ConstantPointerNull>(src) && !isa<UndefValue>(src)) {
      pi.op = STORE2;
      pi.lhs = (*vi)[dst];
      pi.rhs.push_back((*vi)[src]);
      
      // figure out if this is a struct copy and set the offset
      // appropriately (we conservatively assume we're copying the
      // entire struct)
      //
      u32 off_1 = get_max_offset(dst,vi), off_2 = get_max_offset(src,vi);
      pi.off = (off_1 < off_2) ? off_1 : off_2;
    }
    break;
  case EFT_A1R_A0:
    if (cs.arg_size() < 2) { errs() << "!!" << "\n"; break; }
    dst = cs.getArgument(1);
    src = cs.getArgument(0);
    // lack of break deliberate
  case EFT_A2R_A1:
    if (!dst && !src) {
      if (cs.arg_size() < 3) { errs() << "!!" << "\n"; break; }
      dst = cs.getArgument(2);
      src = cs.getArgument(1);
    }
    // lack of break deliberate
  case EFT_A4R_A1:
    if (!dst && !src) {
      if (cs.arg_size() < 5) { errs() << "!!" << "\n"; break; }
      dst = cs.getArgument(4);
      src = cs.getArgument(1);
    }

    if (!isa<ConstantPointerNull>(dst) && !isa<UndefValue>(dst) &&
	!isa<ConstantPointerNull>(src) && !isa<UndefValue>(src)) {
      pi.op = STORE;
      pi.lhs = (*vi)[dst];
      pi.rhs.push_back((*vi)[src]);
    }
    break;
  case EFT_L_A0__A2R_A0:
    if (cs.arg_size() < 3) { errs() << "!!" << "\n"; break; }
    dst = cs.getArgument(2);
    src = cs.getArgument(0);

    if (!isa<ConstantPointerNull>(dst) && !isa<UndefValue>(dst) &&
	!isa<ConstantPointerNull>(src) && !isa<UndefValue>(src)) {
      pi.op = STORE;
      pi.lhs = (*vi)[dst];
      pi.rhs.push_back((*vi)[src]);

      if (isa<PointerType>(ci->getType())) {
	errs() << "EFT_L_A0__A2R_A0: ret value ignored" << "\n";
      }
    }
    break;
  case EFT_A0R_NEW:
  case EFT_A1R_NEW:
  case EFT_A2R_NEW:
  case EFT_A4R_NEW:
  case EFT_A11R_NEW:
    errs() << "EFT_*_NEW: not implemented" << "\n";
    break;
  case EFT_REALLOC:
    if (cs.arg_size() < 1) { errs() << "!!" << "\n"; break; }
    if (!isa<ConstantPointerNull>(cs.getArgument(0)) &&
	isa<PointerType>(cs.getArgument(0)->getType())) {
      arg = cs.getArgument(0);
      if (isa<UndefValue>(arg)) { break; }
      pi.lhs = vi->getTrans(ci);
      if (!pi.lhs) { errs() << "!!" << "\n"; return pi; }
      pi.op = COPY;
      pi.rhs.push_back((*vi)[arg]);
      break;
    }
    // lack of break deliberate
  case EFT_ALLOC:
  case EFT_NOSTRUCT_ALLOC:
  case EFT_STAT:
  case EFT_STAT2:
    if (!isa<PointerType>(ci->getType())) { errs() << "!!" << "\n"; break; }
    pi.lhs = vi->getTrans(ci);
    if (!pi.lhs) { errs()   << "!!" << "\n"; return pi; }
    pi.op = ALLOC;
    pi.rhs.push_back((*vi)(ci));
    break;
  case EFT_NOOP:
  case EFT_OTHER:
    break;
  default: assert(0 && "unknown ext type");
  }
  
  return pi;
}

//// PRIVATE METHODS:

u32 ExtTrans::get_max_offset(Value *v, VarInfo *vi)
{
  u32 r = 1;
  const Type *typ = 0;

  if (ConstantExpr *C = dyn_cast<ConstantExpr>(v)) {
    typ = C->getOperand(0)->getType();
  }
  else if (BitCastInst *ii = dyn_cast<BitCastInst>(v)) {
    typ = ii->getOperand(0)->getType();
  }

  if (typ && isa<PointerType>(typ)) {
    typ = typ->getContainedType(0);

    if (isa<ArrayType>(*typ)) { 
      typ = cast<ArrayType>(typ)->getElementType();
    }

    if (isa<StructType>(typ)) {
      vector<u32>& off = vi->structOffsets(cast<StructType>(typ));
      assert(off.size());
      r = off.back();
    }
  }
  
  return r;
}

#endif // _EXTTRANS_H
