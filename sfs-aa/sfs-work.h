/*  [worklist.h] Worklist implementations for the solver
 *  v. 014, 2008-09-14
 *------------------------------------------------------------------------------
 *  Changes from 011:
 *  - added FIFO & LIFO priorities
 *  - single & dual WL (for a given priority) now share the class def.
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

#ifndef __SFS_WORKLIST_H
#define __SFS_WORKLIST_H

#include "../include/heap.h"
#include "../include/common.h"

namespace sfs {

#undef WLP_NONE
#undef WLP_ID
#undef WLP_LRF
#undef WLP_FIFO
#undef WLP_LIFO
#undef WL_PRIO
#undef DUAL_WL

//Priority of nodes in the worklist
#define WLP_NONE 0
#define WLP_ID 1        //pop in order of increasing node ID
#define WLP_LRF 2       //pop the Least Recently Fired (lowest vtime) first
#define WLP_FIFO 3      //pop the least recently pushed
#define WLP_LIFO 4      //pop the most recently pushed
#define WL_PRIO WLP_LRF
//Use 2 worklists, pushing onto next, popping from current, and swapping when
//  current is empty. The solver will make several passes over the graph,
//  using the above priority within each pass.
#define DUAL_WL 0

//------------------------------------------------------------------------------
#if WL_PRIO == WLP_ID
//Wrapper for the STL tree set (pops lowest ID first).
class Worklist{
private:
#if DUAL_WL == 0
  set<u32> curr;
#else
  set<u32> curr, next;
#endif

public:
  //(nn) is for compatibility with the heap worklist
  Worklist(u32 nn= 0) {}
  bool empty() const{
    return curr.empty();
  }
  //Switch to the next list (and return true)
  //  if nothing remains in the current one.
  bool swap_if_empty(){
#if DUAL_WL == 1
    if(curr.empty()){
      curr.swap(next);
      return 1;
    }
    return 0;
#else
    return curr.empty();
#endif
  }
  //Insert node (n) into the list; priority is ignored.
  void push(u32 n, u32 p= 0){
#if DUAL_WL == 1
    next.insert(n);
#else
    curr.insert(n);
#endif
  }
  //Return the lowest-numbered node from the list,
  //  storing priority (0) into (pp) if provided.
  u32 pop(u32 *pp= 0){
    assert(!curr.empty() && "trying to pop empty worklist");
    set<u32>::iterator it= curr.begin();
    u32 n= *it;
    curr.erase(it);
    if(pp)
      *pp= 0;
    return n;
  }
};
//------------------------------------------------------------------------------
#elif WL_PRIO == WLP_LRF
//Wrapper for the heap (pops earliest vtime first).
class Worklist{
private:
#if DUAL_WL == 0
  Heap curr;
#else
  Heap curr, next;
#endif

public:
  //The constructor requires the node count (nn) to make the heap.
#if DUAL_WL == 0
  Worklist(u32 nn) : curr(nn) {}
#else
  Worklist(u32 nn) : curr(nn), next(nn) {}
#endif
  bool empty() const{
    return curr.empty();
  }
  bool swap_if_empty(){
#if DUAL_WL == 1
    if(curr.empty()){
      curr.swap(next);
      return 1;
    }
    return 0;
#else
    return curr.empty();
#endif
  }
  //Insert node (n) with priority (p) into the list.
  void push(u32 n, u32 p){
#if DUAL_WL == 1
    next.push(n, p);
#else
    curr.push(n, p);
#endif
  }
  //Return the top-priority node from the list,
  //  storing the priority into (pp) if provided.
  u32 pop(u32 *pp= 0){
    assert(!curr.empty() && "trying to pop empty worklist");
    return curr.pop(pp);
  }
};
//------------------------------------------------------------------------------
#elif WL_PRIO == WLP_FIFO || WL_PRIO == WLP_LIFO
//Wrapper for the STL deque (used as a queue or stack).
class Worklist{
private:
#if DUAL_WL == 0
  deque<pair<u32, u32> > curr;
#else
  deque<pair<u32, u32> > curr, next;
#endif

public:
  Worklist(u32 nn= 0) {}
  bool empty() const{
    return curr.empty();
  }
  bool swap_if_empty(){
#if DUAL_WL == 1
    if(curr.empty()){
      curr.swap(next);
      return 1;
    }
    return 0;
#else
    return curr.empty();
#endif
  }
  void push(u32 n, u32 p){
#if DUAL_WL == 1
    next.push_back(make_pair(n, p));
#else
    curr.push_back(make_pair(n, p));
#endif
  }
  //Return the first (FIFO) or last (LIFO) node from the deque.
  u32 pop(u32 *pp= 0){
    assert(!curr.empty() && "trying to pop empty worklist");
#if WL_PRIO == WLP_FIFO
    pair<u32, u32> x= curr.front();
    curr.pop_front();
#else                                   //LIFO
    pair<u32, u32> x= curr.back();
    curr.pop_back();
#endif
    if(pp)
      *pp= x.second;
    return x.first;
  }
};
#else
#error "unknown WL_PRIO"
#endif                                  //WL_PRIO

}

#endif                                  //__WORKLIST_H
