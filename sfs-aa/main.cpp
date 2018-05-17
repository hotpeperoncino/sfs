#include "sfs-aa.h"

void SFS::reset_time()
{
  start_time = get_cpu_time();
}

void SFS::accum_time_and_rst(const char *lbl)
{
  u64 t = get_cpu_time();
  accum_tbl[lbl] += (t - start_time);
  start_time = t;
}

void SFS::print_accum_time(const char *lbl)
{
  u64 t = accum_tbl[lbl];
  fprintf(stderr,"Accumulative time for %s: %llu.%03llu s\n",
	  lbl, t/1000000, t%1000000);
}
