/*  [common.h] Includes & definitions used by all the ptr-analysis projects
 *  v. 014, 2008-09-14
 *------------------------------------------------------------------------------
 *  Copyright 2008 Andrey Petrov, Ben Hardekopf
 *  - apetrov87@gmail.com, apetrov@cs.utexas.edu
 *  - benh@cs.utexas.edu
 *
 *  Permission is hereby granted, free of charge, to any person
 *  obtaining a copy of this software and associated documentation
 *  files (the "Software"), to deal in the Software without
 *  restriction, including without limitation the rights to use, copy,
 *  modify, merge, publish, distribute, sublicense, and/or sell copies
 *  of the Software, and to permit persons to whom the Software is
 *  furnished to do so, subject to the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 *  HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 *  WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 *  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 *  DEALINGS IN THE SOFTWARE.
 *------------------------------------------------------------------------------
 */

#ifndef __COMMON_H
#define __COMMON_H

//Set this to 0 to disable assertions.
#define USE_ASSERT 1

#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/Constants.h"
#include "llvm/BasicBlock.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/TypeSymbolTable.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/ADT/hash_set.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringMap.h"

#include "bitmap.h"
#include "fdd.h"

#include <set>
#include <map>
#include <list>
#include <queue>
#include <stack>
#include <deque>
#include <cstdio>
#include <math.h>
#include <time.h>
#include <string>
#include <vector>
#include <cassert>
#include <cstdarg>
#include <cstdlib>
#include <cstring>
#include <sstream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <functional>
#include <sys/time.h>
#include <sys/resource.h>
#include <ext/hash_set>
#include <ext/hash_map>
#include "profiler.h"

//Disable assert() if requested (must go above assert.h)
#if USE_ASSERT == 1
  #undef NDEBUG
#else
  #define NDEBUG 1
#endif
#include <assert.h>

#include "fdd.h"
#include "bvec.h"

using namespace std;
using namespace llvm;
using namespace __gnu_cxx;

#define BM_ELSZ   128
#define MAX_U32   (u32)-1
#define NOINLINE __attribute__((noinline))

#define FORN(i,n)  for(u32 i= 0, i##e= n; i < i##e; ++i)
#define FOR1N(i,n) for(u32 i= 1, i##e= n; i < i##e; ++i)

#define FOREACH(type,idx,ds) \
  for (type idx = ds.begin(), e = ds.end(); idx != e; ++idx)

#define ROFEACH(type,idx,ds) \
  for (type idx = ds.rbegin(), e = ds.rend(); idx != e; ++idx)

#define MEM_USAGE() {                                    \
    string line; ifstream in("/proc/self/status");       \
    for (u32 i = 0; i < 16; i++) { getline(in,line); }   \
    istringstream inl(line); string x; u32 mem;          \
    inl >> x >> mem; cerr << "memory usage  = " <<       \
    (double)mem/1024 << "M" << endl << endl; in.close(); \
}

typedef unsigned char               u8;
typedef unsigned short              u16;
typedef unsigned int                u32;
typedef unsigned long long          u64;
typedef MySparseBitVector<BM_ELSZ>  bitmap;

//The max. number of entries in bv_cache, and how many to remove at once
//  when it gets full (which may be faster than one at a time).
const u32 bvc_sz= 5000000, bvc_remove= 10000;

//------------------------------------------------------------------------------
//DenseMapInfo for different types
//------------------------------------------------------------------------------

namespace llvm{
  template<> struct DenseMapInfo<char>{
    static char getEmptyKey(){ return (char)0xf0; }
    static char getTombstoneKey(){ return (char)0xf1; }
    static unsigned getHashValue(u32 x){ return x; }
    static unsigned isEqual(u32 x, u32 y){ return x == y; }
    //for DenseSet
    static bool isPod(){ return true; }
  };
  template<> struct DenseMapInfo<bool>{
    static bool getEmptyKey(){ return 0; }
    static bool getTombstoneKey(){ return 1; }
    static unsigned getHashValue(bool x){ return x; }
    static unsigned isEqual(bool x, bool y){ return x == y; }
    static bool isPod(){ return true; }
  };
  template<> struct DenseMapInfo<pair<u32, u32> >{
    static pair<u32, u32> getEmptyKey(){
      return make_pair(0xffefffff, 0xffefffff);
    }
    static pair<u32, u32> getTombstoneKey(){
      return make_pair(0xffeffffe, 0xffeffffe);
    }
    static unsigned getHashValue(const pair<u32, u32> &X){
      return (X.first<<16) ^ (X.first>>16) ^ X.second;
    }
    static unsigned isEqual(const pair<u32, u32> &X, const pair<u32, u32> &Y){
      return X == Y;
    }
  };
  //Note: don't use DenseMap<bitmap>, hash_map is much faster.
  //DenseMapInfo<Constraint> is in anders.h.
}

//------------------------------------------------------------------------------
//GNU STL hashes/comparators for different types
namespace __gnu_cxx{
  template<> struct hash<pair<u32, u32> >{
    size_t operator () (const pair<u32, u32> &X) const{
      return (X.first<<16) ^ (X.first>>16) ^ X.second;
    }
  };
  template<> struct hash<bitmap>{
    size_t operator () (const bitmap& s) const{
      return (u32)s.getHashValue();
    }
  };
}

typedef Module::iterator                  fmod_it;
typedef Module::const_iterator            fmod_cit;
typedef Module::global_iterator           glob_it;
typedef Function::iterator                bb_it;
typedef Function::arg_iterator            prm_it;
typedef BasicBlock::iterator              ibb_it;
typedef Value::use_iterator               use_it;
typedef CallSite::arg_iterator            arg_it;
typedef TypeSymbolTable::iterator         type_it;
typedef StructType::element_iterator      struct_it;
typedef gep_type_iterator                 gept_it;
typedef User::op_iterator                 op_it;
typedef bitmap::iterator                  bm_it;
typedef set<Instruction*>::iterator       inss_it;
typedef set<Function*>::iterator          funs_it;
typedef set<Value*>::iterator             vals_it;
typedef set<GlobalValue*>::iterator       gvs_it;
typedef set<u32>::iterator                us_it;
typedef set<u32>::const_iterator          us_cit;
typedef vector<Function*>::iterator       funv_it;
typedef vector<Instruction*>::iterator    insv_it;
typedef vector<Value*>::iterator          valv_it;
typedef vector<bool>::iterator            boolv_it;
typedef vector<u32>::iterator             uv_it;
typedef vector<u32>::const_iterator       uv_cit;
typedef vector<u32>::reverse_iterator     uv_rit;
typedef map<Value*,u32>::iterator         v2u_it;
typedef map<u32,u32>::iterator            u2u_it;
typedef map<u32,u32>::reverse_iterator    u2u_rit;
typedef map<u32,bitmap>::iterator         u2bm_it;
typedef map<Value*,Function*>::iterator   v2f_it;
typedef map<Function*,u32>::iterator      f2u_it;
typedef map<Instruction*,u32>::iterator   ins2u_it;
typedef map<u32,vector<u32> >::iterator   u2uv_it;
typedef map<u32,set<u32> >::iterator      u2us_it;
typedef hash_map<bitmap,u32>::iterator    bm2u_it;
typedef DenseMap<Value*,u32>::iterator    dv2u_it;
typedef DenseMap<Function*,u32>::iterator df2u_it;
typedef DenseSet<u32>::iterator           dus_it;

// see anders/util.cpp
//
template<class T> bool my_find(vector<T>& v, T x);
template<class T> bool my_search(vector<T>& v, T x);
bool hasPtr(const Type *t);
bool is_dbl_ptr(const Type *T);
bool is_dbl_ptr(const Value *V);
bool is_tri_ptr(const Value *V);
Function* calledFunction(CallInst *ci);
void clear_bdd2vec();
const vector<u32>* bdd2vec(bdd x);
void sat2vec(char *v, int szv);

#endif
