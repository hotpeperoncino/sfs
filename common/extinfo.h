/*  [extinfo.h] Info about external functions
 *  v. 005, 2008-08-15
 *------------------------------------------------------------------------------
 *  Copyright 2008 Andrey Petrov
 *  - apetrov87@gmail.com, apetrov@cs.utexas.edu
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

#ifndef __EXTINFO_H
#define __EXTINFO_H

#include "common.h"

//External function types
//Assume a call in the form LHS= F(arg0, arg1, arg2, arg3).
enum extf_t{
  EFT_NOOP= 0,      //no effect on pointers
  EFT_ALLOC,        //returns a ptr to a newly allocated object
  EFT_REALLOC,      //like L_A0 if arg0 is a non-null ptr, else ALLOC
  EFT_NOSTRUCT_ALLOC, //like ALLOC but only allocates non-struct data
  EFT_STAT,         //retval points to an unknown static var X
  EFT_STAT2,        //ret -> X -> Y (X, Y - external static vars)
  EFT_L_A0,         //copies arg0, arg1, or arg2 into LHS
  EFT_L_A1,
  EFT_L_A2,
  EFT_L_A8,
  EFT_L_A0__A0R_A1R,  //copies the data that arg1 points to into the location
                      //  arg0 points to; note that several fields may be
                      //  copied at once if both point to structs.
                      //  Returns arg0.
  EFT_A1R_A0R,      //copies *arg0 into *arg1, with non-ptr return
  EFT_A3R_A1R_NS,   //copies *arg1 into *arg3 (non-struct copy only)
  EFT_A1R_A0,       //stores arg0 into *arg1
  EFT_A2R_A1,       //stores arg1 into *arg2
  EFT_A4R_A1,       //stores arg1 into *arg4
  EFT_L_A0__A2R_A0, //stores arg0 into *arg2 and returns it
  EFT_A0R_NEW,      //stores a pointer to an allocated object in *arg0
  EFT_A1R_NEW,      //as above, into *arg1, etc.
  EFT_A2R_NEW,
  EFT_A4R_NEW,
  EFT_A11R_NEW,
  EFT_OTHER         //not found in the list
};

//------------------------------------------------------------------------------
class ExtInfo{
private:

  //Each function name is mapped to its extf_t
  //  (hash_map and map are much slower).
  StringMap<extf_t> info;
  //A cache of is_ext results for all Function*'s (hash_map is fastest).
  std::map<const Function*, bool> isext_cache;

  void init();                          //fill in the map (see extinfo.cpp)

public:
//------------------------------------------------------------------------------
  ExtInfo(){
    init();
    isext_cache.clear();
  }

  //Return the extf_t of (F).
  extf_t get_type(const Function *F) const{
    assert(F);
    StringMap<extf_t>::const_iterator it= info.find(F->getName());
    if(it == info.end())
      return EFT_OTHER;
    else
      return it->second;
  }

  //Does (F) have a static var X (unavailable to us) that its return points to?
  bool has_static(const Function *F) const{
    extf_t t= get_type(F);
    return t==EFT_STAT || t==EFT_STAT2;
  }
  //Assuming hasStatic(F), does (F) have a second static Y where X -> Y?
  bool has_static2(const Function *F) const{
    return get_type(F) == EFT_STAT2;
  }
  //Does (F) allocate a new object?
  bool is_alloc(const Function *F) const{
    extf_t t= get_type(F);
    return t==EFT_ALLOC || t==EFT_NOSTRUCT_ALLOC || t==EFT_A0R_NEW ||
      t==EFT_A1R_NEW || t==EFT_A2R_NEW || t==EFT_A4R_NEW || t==EFT_A11R_NEW;
  }
  //Does (F) allocate only non-struct objects?
  bool no_struct_alloc(const Function *F) const{
    return get_type(F) == EFT_NOSTRUCT_ALLOC;
  }
  //Does (F) not do anything with the known pointers?
  bool is_noop(const Function *F) const{
    return get_type(F) == EFT_NOOP;
  }

  //Should (F) be considered "external" (either not defined in the program
  //  or a user-defined version of a known alloc or no-op)?
  bool is_ext(const Function *F){
    assert(F);
    //Check the cache first; everything below is slower.
    std::map<const Function*, bool>::iterator i_iec= isext_cache.find(F);
    if(i_iec != isext_cache.end())
      return i_iec->second;

    bool res;
    if(F->isDeclaration() || F->isIntrinsic()){
      res= 1;
    }else{
      extf_t t= get_type(F);
      res= t==EFT_ALLOC || t==EFT_REALLOC || t==EFT_NOSTRUCT_ALLOC
          || t==EFT_NOOP;
      if (res && t != EFT_NOOP && 
	  !isa<PointerType>(F->getReturnType())) { 
	errs() << "!!!" << "\n";
	res = false; 
      }
    }
    isext_cache[F]= res;
    return res;
  }
};

#endif
