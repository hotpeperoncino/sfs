#include "sfs-aa.h"

// horrible kludge to get the bdd information from Anders to be usable
// by PtsSet
//
bdd pdom;
bddPair *g2p;
vector<bdd> bdd_off, bdd_xlt;

bdd get_bdd(u32 x)
{
  if (x >= bdd_xlt.size()) { bdd_xlt.resize(x+1,bddfalse); }
  if (bdd_xlt[x] == bddfalse) { bdd_xlt[x] = fdd_ithvar(0,x); }
  return bdd_xlt[x];
}

// and same kludge so PtsGraph can access o2p[]
//
vector<u32> o2p; // object -> access equivalence partition

bool SFS::runOnModule(Module &M)
{
  reset_time();
  base_mem = get_mem_usage(true);

  run_init(&M);

  sfs_id();
  solve();

  return false;
}

void SFS::releaseMemory()
{
  //!!
}

//Pass registration
char SFS::ID= 0;
RegisterPass<SFS> X("sfs-aa",
		    "sparse flow-sensitive pointer analysis");
