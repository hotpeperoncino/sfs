#ifndef _COMMON_H
#define _COMMON_H

//===============CUSTOMIZE COMPILATION================//

#define PTR_DS   2  // 1:bitmap, 2:bdd
#define RUN_TYPE 1  // 0:asserts,stats, 1:asserts, 2:optimized
#define METRICS  0  // 0:none, 1:all, 2:all with histograms
#define PRECIS   0  // 0:none, 1:precision analysis
#define PROF     0  // 0:none, 1:CPU
#define BM_ELSZ  64 // bitmap element size
#define SSO_OPT  1  // 0:no SSO call opt, 1:use SSO call opt

//=============END CUSTOMIZE COMPILATION==============//

#if PTR_DS == 1
#define PTRINFO_H "ptrinfo.bit.h"
#else // PTR_DS == 2
#define PTRINFO_H "ptrinfo.bdd.h"
#endif

#if RUN_TYPE == 0
#define STT(s) s
#define DBX(x) x
#elif RUN_TYPE == 1
#define STT(s)
#define DBX(x) x
#else // RUN_TYPE == 2
#define NDEBUG
#define STT(s)
#define DBX(x)
#endif

#define REPORT_METRICS()

#if PRECIS == 1
#define PRECISION_REPORT() Stats::precision_report(M,dfg,vi,ti)
#else
#define PRECISION_REPORT()
#endif

// reasons for weak variables (for PRECIS == 1)
//
#define NO_REASON  0x000
#define HEAP       0x001
#define ARRAY      0x002
#define REC        0x004
#define STRUCT     0x008
#define MULT       0x010

#if PROF == 1
#define CPU_PROFILE_START(x)  ProfilerStart(x)
#define CPU_PROFILE_STOP()    ProfilerStop()
#else // PROF == 0
#define CPU_PROFILE_START(x)
#define CPU_PROFILE_STOP()
#endif

#define MAX_U32 (u32)-1

#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Constants.h"
#include "llvm/BasicBlock.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/TypeSymbolTable.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringMap.h"

//#include "llvm/ADT/SparseBitVector.h"
#include "bitmap.h"

#include <set>
#include <map>
#include <list>
#include <queue>
#include <stack>
#include <deque>
#include <math.h>
#include <string>
#include <vector>
#include <sstream>
#include <iomanip>
#include <fstream>
#include <ext/hash_set>
#include <ext/hash_map>

#include "fdd.h"
#include "bvec.h"
#include "profiler.h"

using namespace std;
using namespace llvm;
using namespace __gnu_cxx;

typedef unsigned int                u32;
typedef unsigned long long          u64;
typedef MySparseBitVector<BM_ELSZ>  bitmap;

typedef Module::iterator                fmod_it;
typedef Module::const_iterator          fmod_cit;
typedef Module::global_iterator         glob_it;
typedef Function::iterator              bb_it;
typedef Function::arg_iterator          prm_it;
typedef BasicBlock::iterator            ibb_it;
typedef Value::use_iterator             use_it;
typedef CallSite::arg_iterator          arg_it;
typedef TypeSymbolTable::iterator       type_it;
typedef StructType::element_iterator    struct_it;
typedef gep_type_iterator               gept_it;
typedef User::op_iterator               op_it;
typedef bitmap::iterator                bm_it;
typedef set<Instruction*>::iterator     inss_it;
typedef set<Function*>::iterator        funs_it;
typedef set<Value*>::iterator           vals_it;
typedef set<GlobalValue*>::iterator     gvs_it;
typedef set<u32>::iterator              us_it;
typedef vector<Function*>::iterator     funv_it;
typedef vector<Instruction*>::iterator  insv_it;
typedef vector<Value*>::iterator        valv_it;
typedef vector<bool>::iterator          boolv_it;
typedef vector<u32>::iterator           uv_it;
typedef map<Value*,u32>::iterator       v2u_it;
typedef map<u32,u32>::iterator          u2u_it;
typedef map<u32,bitmap>::iterator       u2bm_it;
typedef map<Value*,Function*>::iterator v2f_it;
typedef map<Function*,u32>::iterator    f2u_it;
typedef map<u32,u32>::reverse_iterator  u2u_rit;
typedef map<Instruction*,u32>::iterator ins2u_it;

// for hashing pointers and bitmaps
//
namespace __gnu_cxx
{
  template<class T> struct hash<T*> {
    size_t operator()(const T* p) const { return hash<u32>()((u32)p); }};
  template<> struct hash<bitmap> {
    size_t operator()(const bitmap& s) const { return s.getHashValue(); }};
}

// get memory usage from the /proc filesystem
//
#define MEM_USAGE() {                                    \
    string line; ifstream in("/proc/self/status");       \
    for (u32 i = 0; i < 16; i++) { getline(in,line); }   \
    istringstream inl(line); string x; u32 mem;          \
    inl >> x >> mem; cerr << "memory usage  = " <<       \
    (double)mem/1024 << "M" << endl << endl; in.close(); \
}

// convenience wrapper around std::find
//
template<class T>
bool my_find(vector<T>& v, T x);

// convenience wrapper around std::binary_search
//
template<class T>
bool my_search(vector<T>& v, T x);

// true iff t is a pointer or is a type that contains a pointer
//
bool hasPtr(const Type *t);

// get the callee of a CallInst (0 if indirect call)
//
Function* calledFunction(CallInst *ci);

#endif // _COMMON_H
