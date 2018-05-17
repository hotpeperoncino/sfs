#include "../include/common.h"

// convenience wrapper around std::find
//
template<class T>
bool my_find(vector<T>& v, T x)
{
  return (find<typename vector<T>::iterator,T>(v.begin(),v.end(),x)!=v.end());
}

// convenience wrapper around std::binary_search
//
template<class T>
bool my_search(vector<T>& v, T x)
{
  return binary_search<typename vector<T>::iterator,T>(v.begin(),v.end(),x);
}

// true iff t is a pointer or is a type that contains a pointer
//
bool hasPtr(const Type *t)
{
  bool r = false;

  //Function pointers are marked as double because indirect calls may
  //  load/store pointers through them.
  if (isa<PointerType>(t) || isa<FunctionType>(t)) { r = true; }
  else if (const SequentialType *ta = dyn_cast<const SequentialType>(t)) {
    r = hasPtr(ta->getElementType());
  }
  else if (const StructType *tt = dyn_cast<const StructType>(t)) {
    for (u32 j = 0; j < tt->getNumElements(); ++j) {
      if (hasPtr(tt->getElementType(j))) { r = true; break; }
    }
  }

  return r;
}

//------------------------------------------------------------------------------
//Check if (T) is a double-pointer type.
bool is_dbl_ptr(const Type *T){
  if(const PointerType *PT= dyn_cast<PointerType>(T)){
    return hasPtr(PT->getContainedType(0));
  }
  return 0;
}
//Check if (V) is a double pointer.
bool is_dbl_ptr(const Value *V){
  return is_dbl_ptr(V->getType());
}
//Check if (V) points to a double pointer.
bool is_tri_ptr(const Value *V){
  if(const PointerType *PT= dyn_cast<PointerType>(V->getType()))
    return is_dbl_ptr(PT->getContainedType(0));
  return 0;
}

// get the callee of a CallInst (0 if indirect call)
//
Function* calledFunction(CallInst *ci)
{
  if (Function *F = ci->getCalledFunction()) { return F; }

  Value *v = ci->getCalledValue();

  if (ConstantExpr *C = dyn_cast<ConstantExpr>(v)) {
    if (C->getOpcode() == Instruction::BitCast) {
      if (Function *F = dyn_cast<Function>(C->getOperand(0))) { return F; }
    }
  }

  return 0;
}

//This vector holds the result of sat2vec().
static vector<u32> bddexp;
//A map of BDD IDs to their last-used time and vector expansion.
static map<u32, pair<u32, vector<u32>*> > bv_cache;

//The cache size limit and LRU tracking may be disabled because it already
//  uses relatively little memory.
//The sequence number of the current bdd2vec call (for LRU).
static u32 bv_time= 0;
//priority_queue puts the greatest element at the top, but we need the
//  lowest time at the top, so use the reverse comparator.
static priority_queue<pair<u32, u32>, vector<pair<u32, u32> >,
    greater<pair<u32, u32> > > bv_lru;

//------------------------------------------------------------------------------
//Delete all of the above data.
void clear_bdd2vec(){
  bddexp.clear();
  for(map<u32, pair<u32, vector<u32>*> >::iterator it= bv_cache.begin(),
      ie= bv_cache.end(); it != ie; ++it)
    delete it->second.second;
  bv_cache.clear();
  while(!bv_lru.empty())
    bv_lru.pop();
  bv_time= 0;
}

//------------------------------------------------------------------------------
//Return a pointer to a vector containing the data of BDD (x).
//Make sure you're finished with this pointer before calling bdd2vec again:
//  it can be deleted when the cache gets full.
const vector<u32>* bdd2vec(bdd x){
  assert(x != bddtrue);
  if(x == bddfalse){
    static vector<u32> v_false;
    return &v_false;
  }
  u32 id= x.id();
  map<u32, pair<u32, vector<u32>*> >::iterator i_bvc= bv_cache.find(id);
  if(i_bvc != bv_cache.end()){
    //If this BDD is cached, update its time and return its bitmap.
    i_bvc->second.first= bv_time;
    bv_lru.push(make_pair(bv_time++, id));
    return i_bvc->second.second;
  }

  //If the cache has reached its capacity, remove the oldest items.
  if(bv_cache.size() >= bvc_sz){
    FORN(i, bvc_remove){
      //Some LRU entries may have an older time than the cache entry.
      while(1){
        pair<u32, u32> x= bv_lru.top();
        bv_lru.pop();
        u32 t= x.first, id= x.second;
        i_bvc= bv_cache.find(id);
        assert(i_bvc != bv_cache.end());
        if(t == i_bvc->second.first){
          delete i_bvc->second.second;
          bv_cache.erase(i_bvc);
          break;
        }
      }
    }
  }

  //Fill in bddexp and copy it to the cache.
  //This is faster than passing a new blank vector to sat2vec()
  //  because bddexp doesn't need to grow every time.
  bddexp.clear();
  bdd_allsat(x, sat2vec);
  //The points-to results should be printed in the same order as with bitmaps,
  //  and the solver is a little faster when it processes in increasing order.
  sort(bddexp.begin(), bddexp.end());
  vector<u32> *v= new vector<u32>(bddexp);
  bv_cache[id]= make_pair(bv_time, v);
  bv_lru.push(make_pair(bv_time++, id));
  return v;
}

//------------------------------------------------------------------------------
//This bdd_allsat callback puts all assignments of bit vector (v)
//  (in which -1 means don't care) into the vector (bddexp);
//  the contents of (v) after the end of FDD domain 0 are ignored,
//  and odd positions in (v) are skipped because domains 0 and 1 have
//  their variables interleaved.
//It assumes that domain 0 is the first set of variables to be allocated.
void sat2vec(char *v, int szv){
  //The number of bits in (v) used for domain 0
  //  and any other variables interleaved into it.
  static u32 fdd0_bits= 0;
  if(!fdd0_bits)
    fdd0_bits= (u32)fdd_varnum(0) * 2 - 1;
  //The result with all dont-cares at 0.
  u32 base= 0;
  //The list of dont-care masks and its size.
  static u32 dc[32];
  u32 ndc= 0;
  //v[0] represents bit 0 of the result, so the 1 bit in (m) moves left.
  //Odd values of (i) are skipped because they refer to domain 1.
  for(u32 i= 0, m= 1; i < fdd0_bits; i += 2, m <<= 1){
    switch(v[i]){
      case -1:
        dc[ndc++]= m;
        break;
      case 1:
        base |= m;
        break;
      default:
        ;
    }
  }
  //Speed up the handling of small cases (up to 2 dont-cares).
  switch(ndc){
    case 2:{
      u32 x= base|dc[1];
      bddexp.push_back(x);
      bddexp.push_back(x|dc[0]);
    }
    case 1:
      bddexp.push_back(base|dc[0]);
    case 0:
      bddexp.push_back(base);
      break;
    default:
      assert(ndc <= 25 && "too many assignments for BDD");
      //Use all subsets of dont-cares.
      for(u32 i= 0, ie= 1<<ndc; i < ie; ++i){
        u32 x= base;
        for(u32 j= 0, m= 1; j < ndc; ++j, m <<= 1){
          if(i&m){
            x |= dc[j];
          }
        }
        bddexp.push_back(x);
      }
  }
}
