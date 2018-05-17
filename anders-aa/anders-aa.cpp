/*  [anders-aa.cpp] LLVM ModulePass interface impl.
 *  v. 013, 2008-08-29
 *------------------------------------------------------------------------------
 */
#include "anders-aa.h"

bool AndersAA::runOnModule(Module &M)
{
  if(!anders)
    anders= new Anders;
  return anders->runOnModule(M);
}

void AndersAA::releaseMemory()
{
  if(anders){
    delete anders;
    anders= 0;
  }
}

//Pass registration
char AndersAA::ID= 0;
RegisterPass<AndersAA> X("anders",
  "Andersen's interprocedural pointer analysis (field-sensitive)");
