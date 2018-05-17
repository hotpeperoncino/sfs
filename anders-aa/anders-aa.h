/*  [anders-aa.h] LLVM ModulePass interface for Andersen analysis
 *  v. 013, 2008-08-29
 *------------------------------------------------------------------------------
 */
#ifndef _ANDERS_AA_H
#define _ANDERS_AA_H

#include "../include/anders.h"

class AndersAA : public ModulePass
{
public:

  static char ID;
  AndersAA(): ModulePass((intptr_t)&ID), anders(0) {}
  ~AndersAA(){
    if(anders)
      delete anders;
  }

  virtual bool runOnModule(Module &M);
  virtual void releaseMemory();

  virtual void print(std::ostream &O, const Module *M) const{
    assert(anders);
    //anders->print_cons_graph(1, 1, &O);
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }

private:

  Anders *anders;
};

#endif // _ANDERS_AA_H
