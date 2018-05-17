#ifndef _PQUEUE_H
#define _PQUEUE_H

#include "common.h"

// priority worklist, single queue
//
// - the highest priorities are removed first
// 
// - elements with duplicate priorities can be inserted, but when an
//   element is popped all elements with duplicate priorities are
//   discarded
//
template<class T> 
class PQ_1
{
public:

   PQ_1() {}
  ~PQ_1() {}

  // insert n into the queue with priority p
  //
  void insert(T* n, u32 p) { Q.push(pair_t(n,p)); }

  // return (and pop) the element with the highest priority,
  // discarding duplicates
  //
  T* select()
  {
    assert(!empty());
    
    pair_t x = Q.top(); Q.pop();
    while (!Q.empty() && x.second == Q.top().second) { Q.pop(); }

    return x.first;
  }

  bool empty() { return Q.empty(); }

private:

  typedef pair<T*,u32> pair_t;

  struct pcomp { bool operator()(const pair_t& a, const pair_t& b) {
    return (a.second < b.second); }};
  
  priority_queue<pair_t,vector<pair_t>,pcomp> Q;
};


// priority worklist, double queue (current and next)
//
// - the highest priorities are removed first
//
// - elements with duplicate priorities can be inserted, but when an
//   element is popped all elements with duplicate priorities are
//   discarded
//
template<class T> 
class PQ_2
{
public:
  
   PQ_2() : curr(&Q1), next(&Q2) {}
  ~PQ_2() {}

  // insert n into the queue with priority p
  //
  void insert(T* n, u32 p) { next->push(pair_t(n,p)); }

  // return (and pop) the element with the highest priority in the
  // current queue, discarding duplicates
  //
  T* select()
  {
    assert(!empty());

    if (curr->empty()) {
      priority_queue<pair_t,vector<pair_t>,pcomp> *t;
      t = curr; curr = next; next = t;
    }

    pair_t x = curr->top(); curr->pop();
    while (!curr->empty() && x.second == curr->top().second) { curr->pop(); }

    return x.first;
  }

  bool empty() { return (Q1.empty() && Q2.empty()); }
  
private:

  typedef pair<T*,u32> pair_t;

  struct pcomp { bool operator()(const pair_t& a, const pair_t& b) {
    return (a.second < b.second); }};
  
  priority_queue<pair_t,vector<pair_t>,pcomp> Q1, Q2, *curr, *next;
};


// fifo worklist, single queue
//
template<class T>
class FIFO
{
public:

   FIFO() {}
  ~FIFO() {}

  void insert(T* n) { Q.push_back(n); }

  T* select()
  {
    assert(!empty());
    
    T* r = Q.front(); Q.pop_front();
    return r;
  }

  bool empty() { return Q.empty(); }

private:

  deque<T*> Q;
};

#endif // _PQUEUE_H
