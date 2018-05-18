#ifndef _PTRINFO_H
#define _PTRINFO_H

#define PTRINFO_BDD

#include "../common/common.h"
#include "varinfo.h"
using llvm::errs;
using llvm::dbgs;

struct DFnode; // forward declaration

// pointer information class
//
// - implements points-to sets using BDDs
//
// - the implementation is aware that the points-to information has
//   been split into a single object for all top-level vars and many
//   local objects for address-taken vars; some operations can only be
//   done to the top-level object, others only to the local objects
//
class PtrInfo
{
public:

   PtrInfo() : ti(0), vi(0) {}
   PtrInfo(PtrInfo *t, VarInfo *v) : ti(t), vi(v) {}
  ~PtrInfo() {}

  // initialize the BDD library, passing in the maximum variable index
  // that can be in a points-to set and the set of GEP offsets that
  // will be encountered during the analysis; call this before
  // anything else
  //
  static void init(u32,bitmap&,VarInfo*);

  void set_vi(VarInfo *v) { vi = v; }

  // we assume that all arguments to these functions are top-level
  // variables except the second argument to alloc
  //
  bool copy(u32,u32);  //  x =  y
  bool load(u32,u32);  //  x = *y
  bool store(u32,u32); // *x =  y
  bool alloc(u32,u32); //  x = &y

  // for initialization of address-taken pointers; for loc_alloc both
  // arguments are address-taken, for loc_copy the second argument
  // is top-level
  //
  bool loc_alloc(u32,u32);
  bool loc_copy(u32,u32);

  // for GEP instructions: lhs = rhs + offset
  //
  bool gep(u32,u32,u32);

  // let the PtrInfo* arg be x, then this performs x |= this->store()
  // without actually changing this. sets x->same if any info in x
  // changed, but returns true iff the store itself changed x's info
  //
  bool storeInto(PtrInfo*,u32,u32);

  // like storeInto, but computes *lhs = *rhs; the fourth argument is
  // a range s.t. for  0 <= k < range, *(lhs+k) = *(rhs+k)
  //
  bool storeInto2(PtrInfo*,u32,u32,u32);

  // union the given pointer info into the current points-to map
  //
  bool unite(PtrInfo*);

  // return a new PtrInfo object that is a copy of the current one
  // (must be deleted by the caller)
  //
  PtrInfo* dup() { return (new PtrInfo(*this)); }

  // filt is filled in with the pointer information reachable from
  // roots, while diff (if non-null) is filled in with the rest of the
  // pointer information
  //
  void filter(bitmap &roots, PtrInfo *filt, PtrInfo *diff = 0);

  // same records whether the pointer information is unchanged since
  // the last time it was reset. the parameter i specifies a
  // particular node using this ptrinfo -- if i is in same then the
  // info has not changed since the last time the info was reset for i
  //
  bool changed(DFnode *i) { return !same.count(i); }
  void setc(DFnode *i)    { same.erase(i);         }
  void rstc(DFnode *i)    { same.insert(i);        }

  // return true iff v is a null pointer
  //
  bool null(u32 v)
  {
    if (!ti) { return !tp.count(v); }
    else {
      assert(v < pd.size());
      return ((p & pd[v]) == bddfalse);
    }
  }

  // remove a pointer from the points-to set
  //
  void rm(u32 v)
  {
    if (!ti) { tp.erase(v); }
    else { assert(v < pd.size()); p -= pd[v]; }
  }

  // iterator over a points-to set; note that this does _NOT_ have the
  // regular iterator semantics -- (1) you can write to the iterator
  // but it doesn't actually change the points-to set; (2) we assume
  // the iterator will only be used to iterate over the entire
  // points-to set using a for loop, and in particular that the == and
  // != operators are only used to compare against the 'end' iterator
  //
  // OPT: bdd_allsat is very expensive, so for performance we cache
  //      the points-to sets that are iterated over. this may greatly
  //      increase memory in some cases, so watch out for this.
  //
  class BDD_iterator
  {
  public:

    BDD_iterator() { assert(0); }

    BDD_iterator(bdd pts, bool end = false)
    {
      if (!end) {
	if (!elm.count(pts.id())) {
	  el.clear();
	  bdd_allsat(pts,expand_pd);
	
	  vector<u32>& els = elm[pts.id()];

	  els.swap(el);
	  sort<uv_it>(els.begin(),els.end());
	}

	it = elm[pts.id()].begin();
	fin = elm[pts.id()].end();
      }
    }

    inline BDD_iterator& operator++() // prefix
    {
      assert(it != fin);
      
      ++it;
      return *this;
    }

    inline BDD_iterator operator++(int) // postfix
    {
      BDD_iterator tmp = *this;
      ++(*this);
      return tmp;
    }

    u32 operator*() const { return *it; }

    // here's the major place our assumptions come into play -- we
    // don't even check against rhs, we just check to see if we've
    // iterated all the way through els
    //
    bool operator==(const BDD_iterator& rhs) const
    {
      return (it == fin);
    }

    bool operator!=(const BDD_iterator& rhs) const
    {
      return !(*this == rhs);
    }

  private:

    uv_it it, fin;
    static map<u32,vector<u32> > elm;
  };

  typedef BDD_iterator ptr_it;

  // return iterators to the given points-to set
  //
  ptr_it begin(u32) const;
  ptr_it   end(u32) const;

  // true iff the two given pointers' points-to sets intersect
  //
  bool intersects(u32,u32);

  // print the pointer information (either all of it, or specifically
  // that belonging to a particular var, or all of it except with
  // equivalent pointers grouped together)
  //
  void print();
  void print(u32);
  void print_eq();

  void print_hist(); // print histogram of points-to set sizes

  // return the pointer info contained in this that is not contained
  // in rhs (returns a new PtrInfo that must be deleted by the caller)
  //
  PtrInfo* diff(PtrInfo *rhs);

  // compute the number of pointer-equivalent variables
  //
  void compute_pe();

  // collapse pointer-equivalent variables (note that after calling
  // this anything accessing ti should be sure to translate pointers
  // to their reps using vi)
  //
  void collapse_pe();

  // return the sum of the sizes of the points-to sets for each
  // variable, or the points-to set size of the given variable
  //
  u32 size();
  u32 size(u32);

  // return the sum of the number of elements used by the points-to
  // sets for each variable (noop for BDDs)
  //
  u32 num_els() { return 0; }

  // return the number of pointers in this points-to graph
  //
  u32 num_ptrs();

  // return whether the points-to map is empty
  //
  bool empty() { return (p == bddfalse && tp.empty()); }

  // compute a hash of the PtrInfo
  //
  size_t getHash() const;

  bool operator==(const PtrInfo& x) const { return (p == x.p && tp == x.tp); }
  bool operator!=(const PtrInfo& x) const { return !(*this == x); }

private:

#define EL(x)    { el.clear(); bdd_allsat(x,expand_pd); }
#define PTS(x,y) bdd_relprod(x,y,pd_dmn)
#define TOPD(x)  bdd_replace(x,pr2pd)
#define TOPR(x)  bdd_replace(x,pd2pr)
#define TOINT(x) (u32)x.id()

  typedef map<u32,bdd> pts_map;
  typedef pts_map::iterator pts_it;
  typedef pts_map::const_iterator pts_cit;

  bdd p;      // the points-to graph for local info
  pts_map tp; // the points-to graph for top info

  PtrInfo *ti; // pointer to the top-level pointer info (NULL if this
	       // _is_ the top-level pointer info)
  VarInfo *vi; // pointer to the variable info

  set<DFnode*> same; // is the pointer info unchanged since the last reset?

  static vector<u32> el; // holds the results of expand_pd
  static void expand_pd(char*,int); // to get elements of bdd

  static vector<bdd> pd;       // map from u32 -> bdd
  static bddPair *pr2pd;       // move points-to range to points-to domain
  static bddPair *pd2pr;       // move points-to domain to points-to range
  static bdd pd_dmn, pr_dmn;   // for existential quantification
  static map<u32,bdd> gep_off; // for computing GEP offsets
  static bdd plusone, o;       // for storeInto2; for filter
};

bdd PtrInfo::o;
bdd PtrInfo::pd_dmn;
bdd PtrInfo::pr_dmn;
bdd PtrInfo::plusone;
bddPair* PtrInfo::pr2pd;
bddPair* PtrInfo::pd2pr;
vector<u32> PtrInfo::el;
vector<bdd> PtrInfo::pd;
map<u32,bdd> PtrInfo::gep_off;
map<u32,vector<u32> > PtrInfo::BDD_iterator::elm;

//// PUBLIC METHODS

void PtrInfo::init(u32 n, bitmap& off, VarInfo *vi)
{
  // OPT: check these parameters
  //
  bdd_init(4000000,400000);
  bdd_gbc_hook(NULL);
  bdd_setcacheratio(8);
  bdd_disable_reorder();
  bdd_setmaxincrease(1000000);
  
  int vdom[] = { (int)n };
  fdd_extdomain(vdom,1); // points-to domain
  fdd_extdomain(vdom,1); // points-to range

  pr2pd = bdd_newpair();
  fdd_setpair(pr2pd,1,0);

  pd2pr = bdd_newpair();
  fdd_setpair(pd2pr,0,1);

  pd_dmn = fdd_ithset(0);
  pr_dmn = fdd_ithset(1);

  for (u32 i = 0; i < n; i++) { pd.push_back(fdd_ithvar(0,i)); }

  //
  // create offset BDDs for storeInto2 and GEP instructions
  //

  u32 sz = (u32)ceil(log2(n));
  bvec dmn = bvec_varfdd(0);
  bvec rng = bvec_varfdd(1);

  // for storeInto2 we need a 1-offset BDD for every variable
  //
  bvec add = bvec_add(dmn,bvec_con(sz,1));
  plusone = bddtrue;
  for (int j = 0, e = rng.bitnum(); j < e; ++j) {
    plusone &= bdd_apply(rng[j], add[j], bddop_biimp);
  }

  // for each offset o, create a BDD representing 'rng = dmn + o' that
  // contains every struct variable with at least that number of
  // fields
  //
  // OPT: would it be better to only compute the offset for the set of
  //      affected variables rather than compute it for the entire
  //      domain and then intersecting with the affected variables?
  //
  for (bm_it i = off.begin(), e = off.end(); i != e; ++i) {
    bvec add = bvec_add(dmn,bvec_con(sz,*i));
    bdd& res = gep_off[*i];

    res = bddtrue;

    for (int j = 0, e = rng.bitnum(); j < e; ++j) {
      res &= bdd_apply(rng[j], add[j], bddop_biimp);
    }

    bdd rel = bddfalse;
    bitmap& vars = vi->varf(*i);

    for (bm_it j = vars.begin(), e = vars.end(); j != e; ++j) {
      assert(*j < pd.size()); rel |= pd[*j];
    }

    res &= rel;
    o |= res; // all the offset bdds combined into one (for filter)
  }
}

bool PtrInfo::copy(u32 lhs, u32 rhs)
{
  assert(!ti && lhs && rhs);
  pts_it ri = tp.find(rhs);

  if (ri != tp.end()) {
    pts_it li = tp.find(lhs);

    if (li != tp.end()) {
      bdd oldp = li->second;
      li->second |= ri->second;

      if (li->second != oldp) { same.clear(); return true; }
      return false;
    }
    else { tp[lhs] = ri->second; same.clear(); return true; }
  }

  return false;
}

bool PtrInfo::load(u32 lhs, u32 rhs)
{
  assert(ti && lhs && rhs);
  pts_it ri = ti->tp.find(rhs);

  if (ri != ti->tp.end()) {
    bdd rp = TOPD(PTS(ri->second,p));
    if (rp == bddfalse) { return false; }

    pts_it li = ti->tp.find(lhs);

    if (li != ti->tp.end()) {
      bdd oldp = li->second;
      li->second |= rp;

      if (li->second != oldp) { ti->same.clear(); return true; }
      return false;
    }
    else { ti->tp[lhs] = rp; ti->same.clear(); return true; }
  }

  return false;
}

bool PtrInfo::store(u32 lhs, u32 rhs)
{
  assert(ti && lhs && rhs);
  bdd oldp = p;

  pts_it li = ti->tp.find(lhs);
  if (li == ti->tp.end()) { return false; }

  bdd lp = li->second;
  u32 ind = fdd_scanvar(lp,0);
  bool strong = (pd[ind] == lp) ? !vi->weakp(ind) : false;

  if (strong) { p -= lp; }

  pts_it ri = ti->tp.find(rhs);
  if (ri != ti->tp.end()) { p |= lp & TOPR(ri->second); }

  if (p != oldp) { same.clear(); return true; }
  return false;
}

bool PtrInfo::gep(u32 lhs, u32 rhs, u32 off)
{
  assert(!ti && lhs && rhs && off && gep_off.count(off));
  pts_it ri = tp.find(rhs);

  if (ri != tp.end()) {
    pts_it li = tp.find(lhs);

    if (li != tp.end()) {
      bdd oldp = li->second;

      // in this case TOPD(PTS()) is computing the offset rather than
      // the points-to set
      //
      li->second |= TOPD(PTS(ri->second,gep_off[off]));
      if (li->second != oldp) { same.clear(); return true; }
    }
    else {
      bdd x = TOPD(PTS(ri->second,gep_off[off])); // ditto
      if (x != bddfalse) { tp[lhs] = x; same.clear(); return true; }
    }
  }

  return false;
}

bool PtrInfo::storeInto(PtrInfo *x, u32 lhs, u32 rhs)
{
  assert(ti && x && x->ti && lhs && rhs);
  bdd oldp = x->p;

  pts_it li = ti->tp.find(lhs);
  pts_it ri = ti->tp.find(rhs);

  bdd lp = (li == ti->tp.end()) ? bddfalse : li->second;
  bdd rp = (ri == ti->tp.end()) ? bddfalse : TOPR(ri->second);

  // if x == this, we're essentially just unioning the result of the
  // store with the current info (which also means it can't be a
  // strong update)
  //
  if (x == this) {
    p |= lp & rp;
    if (p != oldp) { same.clear(); return true; }
    return false;
  }

  // if the lhs points-to set is empty then we don't propagate any
  // info -- either we'll return to this node with the proper info
  // later or the program will never advance past this node anyway
  //
  if (lp == bddfalse) { return false; }

  u32 ind = fdd_scanvar(lp,0);
  bool strong = (pd[ind] == lp) ? !vi->weakp(ind) : false;

  if (strong) { x->p |= p - lp; }
  else        { x->p |= p;      }

  x->p |= lp & rp;

  if (x->p != oldp) { x->same.clear(); return true; }
  return false;
}

bool PtrInfo::storeInto2(PtrInfo *x, u32 lhs, u32 rhs, u32 range)
{
  assert(ti && x && lhs && rhs && range);
  bdd oldp = x->p;

  pts_it li = ti->tp.find(lhs);
  pts_it ri = ti->tp.find(rhs);

  bdd lp = (li == ti->tp.end()) ? bddfalse : li->second;
  bdd rp = (ri == ti->tp.end()) ? bddfalse : ri->second;

  // enforce that only variables with sufficient fields are processed
  // by this instruction
  //
  if (range-1) {
    bitmap& vars = vi->varf(range-1);
    bdd rel = bddfalse;
    
    for (bm_it j = vars.begin(), e = vars.end(); j != e; ++j) {
      assert(*j < pd.size()); rel |= pd[*j];
    }
    
    lp &= rel;
    rp &= rel;
  }

  // if x == this we're just unioning the result of the store with the
  // current info (which also means it can't be a strong update)
  //
  if (x == this) {
    for (u32 off = 0; off < range; ++off) {
      p |= lp & PTS(rp,p);

      lp = TOPD(PTS(lp,plusone)); // add 1 to each element
      rp = TOPD(PTS(rp,plusone)); // ditto
    }
    
    if (p != oldp) { same.clear(); return true; }
    return false;
  }


  // if the lhs points-to set is empty then we don't propagate any
  // info -- either we'll return to this node with the proper info
  // later or the program will never advance past this node anyway
  //
  if (lp == bddfalse) { return false; }

  bdd xp = p;

  u32 ind = fdd_scanvar(lp,0);
  bool single = (pd[ind] == lp);

  for (u32 off = 0; off < range; ++off) {
    if (single && !vi->weakp(ind)) { xp -= lp; }

    x->p |= lp & PTS(rp,p);

    lp = TOPD(PTS(lp,plusone)); // add 1 to each element
    rp = TOPD(PTS(rp,plusone)); // ditto

    if (single) { ind = fdd_scanvar(lp,0); }
  }

  x->p |= xp;

  if (x->p != oldp) { x->same.clear(); return true; }
  return false;
}

bool PtrInfo::alloc(u32 lhs, u32 rhs)
{
  assert(!ti && lhs && rhs && rhs < pd.size());
  pts_it li = tp.find(lhs);
  
  if (li != tp.end()) {
    bdd oldp = li->second;
    li->second |= pd[rhs];

    if (li->second != oldp) { same.clear(); return true; }
    return false;
  }
  else { tp[lhs] = pd[rhs]; same.clear(); return true; }
}

bool PtrInfo::loc_alloc(u32 lhs, u32 rhs)
{
  assert(ti && lhs && rhs && lhs < pd.size() && rhs < pd.size());

  bdd oldp = p;
  p |= pd[lhs] & TOPR(pd[rhs]);

  if (p != oldp) { same.clear(); return true; }
  return false;
}

bool PtrInfo::loc_copy(u32 lhs, u32 rhs)
{
  assert(ti && lhs && rhs && lhs < pd.size());
  bdd oldp = p;

  pts_it i = ti->tp.find(rhs);
  if (i != ti->tp.end()) { p |= pd[lhs] & TOPR(i->second); }

  if (p != oldp) { same.clear(); return true; }
  return false;
}

bool PtrInfo::unite(PtrInfo *x)
{
  assert(ti && x->ti && x != this);

  bdd oldp = p;
  p |= x->p;

  if (p != oldp) { same.clear(); return true; }
  return false;
}

void PtrInfo::filter(bitmap &roots, PtrInfo *filt, PtrInfo *diff)
{
  assert(filt && filt->empty() && vi == filt->vi && filt != this && 
	 diff != this);

  bdd r;
  pts_it ri;

  for (bm_it i = roots.begin(), e = roots.end(); i != e; ++i) {
    ri = tp.find(*i);
    if (ri != tp.end()) { r |= ri->second; }
  }

  bdd oldp = filt->p, cum = r;

  do {
    r |= TOPD(PTS(r,o));
    r |= TOPD(PTS(r,p));

    r -= cum;
    cum |= r;
  }
  while (r != bddfalse);

  filt->p = cum & p;
  if (filt->p != oldp) { filt->same.clear(); }

  if (diff) {
    oldp = diff->p;
    diff->p |= (p - filt->p);
    if (diff->p != oldp) { diff->same.clear(); }
  }
}

PtrInfo::ptr_it PtrInfo::begin(u32 i) const
{
  bdd pts;

  if (!ti) {
    pts_cit ri = tp.find(i);
    pts = (ri == tp.end()) ? bddfalse : ri->second;
  }
  else { assert(i < pd.size()); pts = TOPD(PTS(pd[i],p)); }

  return ptr_it(pts);
}

PtrInfo::ptr_it PtrInfo::end(u32 i) const
{
  return ptr_it(bddfalse,true); // see BDD_iterator comments
}

bool PtrInfo::intersects(u32 p1, u32 p2)
{
  if (!ti) {
    pts_it i = tp.find(p1), j = tp.find(p2);
    if (i == tp.end() || j == tp.end()) { return false; }
    else { return ((i->second & j->second) != bddfalse); }
  }
  else {
    assert(p1 < pd.size() && p2 < pd.size());
    return ((PTS(pd[p1],p) & PTS(pd[p2],p)) != bddfalse);
  }
}

void PtrInfo::print()
{
  if (ti) {
    bdd dmn = bdd_exist(p,pr_dmn);
    EL(dmn);

    vector<u32> dv(el);
    sort<uv_it>(dv.begin(),dv.end());
    
    for (u32 i = 0, e = dv.size(); i < e; ++i) {
      outs() << dv[i] << " : [";
      
      bdd pts = TOPD(PTS(pd[dv[i]],p));
      EL(pts);
      
      sort<uv_it>(el.begin(),el.end());
      
      for (u32 j = 0; j < el.size(); ++j) {
	outs() << " " << el[j];
      }
      
      outs() << "  ]" << "\n";
    }
  }
  else {
    for (pts_it i = tp.begin(), e = tp.end(); i != e; ++i) {
      assert(i->second != bddfalse);
      outs() << i->first << " : [";

      EL(i->second);
      sort<uv_it>(el.begin(),el.end());
      
      for (u32 j = 0; j < el.size(); ++j) {
	outs() << " " << el[j];
      }
      
      outs() << "  ]" << "\n";
    }
  }

 
}

void PtrInfo::print(u32 i)
{
  bdd pts = bddfalse;

  outs() << i << " : [";

  if (ti) { assert(i < pd.size()); pts = TOPD(PTS(pd[i],p)); }
  else {
    pts_it ri = tp.find(i);
    if (ri != tp.end()) { pts = ri->second; }
  }
  
  if (pts != bddfalse) {
    EL(pts);
    sort<uv_it>(el.begin(),el.end());
    
    for (u32 i = 0, e = el.size(); i < e; ++i) {
      outs() << " " << el[i];
    }
  }

  outs() << "  ]" << "\n";
}

void PtrInfo::print_eq()
{
  set<u32> done;
  map<u32,bitmap> eq;

  if (ti) {
    bdd dmn = bdd_exist(p,pr_dmn);
    EL(dmn);

    vector<u32> dv(el);
    sort<uv_it>(dv.begin(),dv.end());

    for (uv_it i = dv.begin(), e = dv.end(); i != e; ++i) {
      bdd pts = TOPD(PTS(pd[*i],p));
      eq[TOINT(pts)].set(*i);
    }

    for (uv_it i = dv.begin(), e = dv.end(); i != e; ++i) {
      if (done.count(*i)) { continue; }
      
      bdd pts = TOPD(PTS(pd[*i],p));
      bitmap& ptrs = eq[TOINT(pts)];

      for (bm_it j = ptrs.begin(), e = ptrs.end(); j != e; ++j) {
	outs() << *j << " ";
	done.insert(*j);
      }

      outs() << ": [";

      EL(pts);
      sort<uv_it>(el.begin(),el.end());
      
      for (u32 j = 0, e = el.size(); j < e; ++j) { outs() << " " << el[j]; }
      outs() << "  ]" << "\n";      
    }
  }
  else {
    for (pts_it i = tp.begin(), e = tp.end(); i != e; ++i) {
      assert(i->second != bddfalse);
      eq[TOINT(i->second)].set(i->first);
    }

    for (pts_it i = tp.begin(), e = tp.end(); i != e; ++i) {
      if (done.count(i->first)) { continue; }

      bitmap& ptrs = eq[TOINT(i->second)];

      for (bm_it j = ptrs.begin(), e = ptrs.end(); j != e; ++j) {
	outs() << *j << " ";
	done.insert(*j);
      }

      outs() << ": [";

      bdd_allsat(i->second,expand_pd);
      sort<uv_it>(el.begin(),el.end());
      
      for (u32 j = 0, e = el.size(); j < e; ++j) { outs() << " " << el[j]; }
      el.clear();

      outs() << "  ]" << "\n";
    }
  }
}

void PtrInfo::print_hist()
{
  map<u32,u32> hist;

  if (!ti) {
    for (pts_it i = tp.begin(), e = tp.end(); i != e; ++i) {
      assert(i->second != bddfalse);
      hist[bdd_satcountset(i->second,pd_dmn)]++;
    }
  }
  else {
    bdd dmn = bdd_exist(p,pr_dmn);
    EL(dmn);

    for (u32 i = 0, e = el.size(); i < e; ++i) {
      bdd pts = TOPD(PTS(pd[el[i]],p));
      hist[bdd_satcountset(pts,pd_dmn)]++;
    }
  }

  outs() << "[SIZE]\t[NUMBER OF POINTS-TO SETS]" << "\n";

  for (u2u_it i = hist.begin(), e = hist.end(); i != e; ++i) {
    outs() << i->first << "\t" << i->second << "\n";
  }

  outs() << "\n";
}

PtrInfo* PtrInfo::diff(PtrInfo *rhs)
{
  assert(rhs && rhs != this && ti == rhs->ti);
  PtrInfo *r = new PtrInfo(ti,vi);

  if (ti) { r->p = (p - rhs->p); }
  else {
    for (pts_it i = tp.begin(), e = tp.end(); i != e; ++i) {
      u32 idx = i->first;
      assert(i->second != bddfalse);

      pts_it j = rhs->tp.find(idx);

      if (j == rhs->tp.end()) { r->tp[idx] = i->second; }
      else if (i->second != j->second) {
	r->tp[idx] = i->second - j->second;
      }
    }
  }

  return r;
}

void PtrInfo::compute_pe()
{
  u32 nv = 0;
  set<u32> pe;

  if (ti) {
    bdd dmn = bdd_exist(p,pr_dmn);
    EL(dmn);

    nv = el.size();
    
    for (u32 i = 0, e = el.size(); i < e; ++i) {
      bdd pts = PTS(pd[el[i]],p);
      pe.insert(TOINT(pts));
    }
  }
  else {
    nv = tp.size();

    for (pts_it i = tp.begin(), e = tp.end(); i != e; ++i) {
      pe.insert(TOINT(i->second));
    }
  }

  outs()   << "pointer equivalence:" << "\n"
       << "   -- number of variables  == " << nv << "\n"
       << "   -- number of eq classes == " << pe.size() << "\n"  ;
}

void PtrInfo::collapse_pe()
{
  assert(!ti);
  set<u32> del;
  map<u32,u32> eq;

  for (pts_it i = tp.begin(), e = tp.end(); i != e; ++i) {
    u2u_it j = eq.find(TOINT(i->second));

    if (j != eq.end()) {
      u32 p1 = (*vi)[j->second], p2 = (*vi)[i->first];
      if (vi->unite(p1,p2) == p1) { del.insert(p2); } else { del.insert(p1); }
    }
    else { eq[TOINT(i->second)] = i->first; }
  }

  for (us_it i = del.begin(), e = del.end(); i != e; ++i) { tp.erase(*i); }
}

u32 PtrInfo::num_ptrs()
{
  u32 tot = 0;

  if (ti) {
    bdd dmn = bdd_exist(p,pr_dmn);
    tot = bdd_satcountset(dmn,pd_dmn);
  }
  else { tot = tp.size(); }

  return tot;
}

u32 PtrInfo::size()
{
  u32 tot = 0;

  if (ti) {
    bdd dmn = bdd_exist(p,pr_dmn);
    EL(dmn);
    
    for (u32 i = 0, e = el.size(); i < e; ++i) {
      bdd pts = TOPD(PTS(pd[el[i]],p));
      tot += bdd_satcountset(pts,pd_dmn);
    }
  }
  else {
    for (pts_it i = tp.begin(), e = tp.end(); i != e; ++i) {
      assert(i->second != bddfalse);
      tot += bdd_satcountset(i->second,pd_dmn);
    }
  }

  return tot;
}

u32 PtrInfo::size(u32 v)
{
  if (ti) {
    assert(v < pd.size());
    bdd vp = TOPD(PTS(pd[v],p));
    return bdd_satcountset(vp,pd_dmn);
  }
  else {
    pts_it i = tp.find(v);
    return (i == tp.end()) ? 0 : bdd_satcountset(i->second,pd_dmn);
  }
}

size_t PtrInfo::getHash() const
{
  size_t h = 0;

  if (ti) { h = TOINT(p); }
  else {
    for (pts_cit i = tp.begin(), e = tp.end(); i != e; ++i) {
      h ^= TOINT(i->second);
    }
  }

  return h;
}

//// PRIVATE METHODS

// convert a BDD into a vector of its elements (use as a handler for
// the bdd_allsat function). assumes that all the elements are in the
// 0th domain.
//
void PtrInfo::expand_pd(char *vset, int sz)
{
  vector<u32> dc;
  u32 i, e, j, x, k = 0;

#define  TEST(a,b) (a & (1 << b))
#define   SET(a,b) (a |= (1 << b))
#define CLEAR(a,b) (a &= ~(1 << b))

  for (i = 0, e = (u32)fdd_varnum(0); i < e; i++) {
    if      (vset[i] < 0) { dc.push_back(i); }
    else if (vset[i] > 0) { SET(k,i);        }
  }

  if ((x = dc.size()) == 0) { el.push_back(k); return; }

  for (i = 0; i < (u32)(1<<x); i++) {
    for (j = 0; j < x; j++) {
      if (TEST(i,j)) { SET(k,dc[j]);   }
      else           { CLEAR(k,dc[j]); }
    }
    el.push_back(k);
  }
}


#endif // _PTRINFO_H
