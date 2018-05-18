#ifndef _SFS_AA_H
#define _SFS_AA_H

#include "../include/anders.h"

using llvm::errs;
using llvm::dbgs;

// Set each to 1 to enable, 0 to disable; first undefine the setting
// inherited from anders.h, then define our own settings
//
#undef USE_DEBUG
#undef USE_STATS
#undef USE_METRICS
#undef USE_MEM_TIME
#undef USE_PROFILER
#undef DEBUG_OCI
#undef DEBUG_OPT
#undef DEBUG_SOLVE
#undef SOLVE_RAM_LIMIT
#undef SOLVE_TIME_LIMIT

#define USE_DEBUG 0
#define USE_STATS 0
#define USE_METRICS 0
#define USE_MEM_TIME 1
#define USE_PROFILER 0
#define DEBUG_OCI 0
#define DEBUG_OPT 0
#define DEBUG_SOLVE 0

//// THE SFS CLASS ITSELF

// horrible kludge to get the bdd information from Anders to be usable
// by PtsSet
//
extern bdd pdom;
extern bddPair *g2p;
extern vector<bdd> bdd_off, bdd_xlt;
extern bdd get_bdd(u32);

using llvm::errs;
using llvm::dbgs;

// and same kludge so PtsGraph can access o2p[]
//
extern vector<u32> o2p; // object -> access equivalence partition

class SFS : public ModulePass, public Anders
{
public:

  static char ID;
 SFS() : ModulePass(ID) {}
  
  virtual bool runOnModule(Module &M);
  virtual void releaseMemory();
  
  virtual void print(std::ostream &O, const Module *M) const {}
  
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }

private:

  //// TYPES

  // points-to set for top-level variables
  //
  class PtsSet
  {
  public:
    
    PtsSet() {}
    PtsSet(bdd p) : pts(p) {}
    
    bool insert(u32 x) {
      bdd old = pts;
      pts |= ::get_bdd(x);
      return (pts != old);
    }

    PtsSet& operator=(const PtsSet& rhs)
    {
      pts = rhs.pts;
      return (*this);
    }
    
    bool operator|=(const PtsSet& rhs)
    {
      bdd old = pts;
      pts |= rhs.pts;
      return (pts != old);
    }
    
    PtsSet operator+(u32 off) const
    {
      if (off == 0) { return *this; }
      assert(off < bdd_off.size() && bdd_off[off] != bddfalse);
      return PtsSet(bdd_replace(bdd_relprod(pts,bdd_off[off],pdom),g2p));
    }

    bool operator==(const PtsSet& rhs)
    {
      return pts == rhs.pts;
    }

    bool operator!=(const PtsSet& rhs)
    {
      return !(*this == rhs);
    }

    bdd get_bdd() const { return pts; }

    void print()
    {
      // this is the really slow way to do it, but we don't want to
      // pollute the bdd->vector cache
      //
      bdd p = pts;
      while (p != bddfalse) {
	int x = fdd_scanvar(p,0);
	p -= fdd_ithvar(0,x);
	errs() << " " << x;
      }
      errs() << "\n";
    }
    
  private:
    
    bdd pts;
  };
  
  // points-to graph for address-taken variables
  //
  class PtsGraph
  {
  public:
    
    PtsGraph() {}
    
    void init(vector<u32>& vars)
    {
      sort(vars.begin(),vars.end());
      pts.resize(vars.size(),pts_el());
      FORN(i,vars.size()) { pts[i].first = vars[i]; }
    }

    PtsSet operator[](u32 el)
    {
      pts_cit i = pts_find(el);
      if (i == pts.end()) { return bddfalse; }
      return i->second;
    }
    
    bool operator|=(PtsGraph& rhs)
    {
      bool c = false;

      FOREACH(ch_it,i,rhs.change) {
	pts_cit k = rhs.pts_find(*i); assert(k != rhs.pts.end());
	pts_it j = pts_find(k->first); assert(j != pts.end());
	if (j->second |= k->second) { c = true; change.insert(j->first); }
      }

      return c;
    }

    bool or_part(PtsGraph& rhs, u32 part)
    {
      bool c = false;

      FOREACH(ch_it,i,rhs.change) {
	if (o2p[*i] != part) { continue; }
	pts_cit k = rhs.pts_find(*i); assert(k != rhs.pts.end());
	pts_it j = pts_find(k->first); assert(j != pts.end());
	if (j->second |= k->second) { c = true; change.insert(j->first); }
      }

      return c;
    }

    bool or_except(PtsGraph& rhs, u32 el)
    {
      bool c = false;
      
      FOREACH(ch_it,i,rhs.change) {
	if (*i == el) { continue; }
	pts_cit k = rhs.pts_find(*i); assert(k != rhs.pts.end());
	pts_it j = pts_find(k->first); assert(j != pts.end());
	if (j->second |= k->second) { c = true; change.insert(j->first); }
      }
      
      return c;
    }

    void assign_el(u32 el, const PtsSet& rhs)
    {
      pts_it i = pts_find(el); assert(i != pts.end());
      if (i->second != rhs) { change.insert(el); }
      i->second = rhs;
    }

    void or_el(u32 el, const PtsSet& rhs)
    {
      pts_it i = pts_find(el); assert(i != pts.end());
      if (i->second |= rhs) { change.insert(el); }
    }

    void or_changed(PtsSet& lhs, const vector<u32>& v)
    {
      change.uniq();
      FOREACH(uv_cit,i,v) { if (change.has(*i)) { lhs |= (*this)[*i]; }}
    }
    
    bool check() { change.uniq(); return !change.empty();  }
    void rst()   { change.clear(); }

    bool empty() { return pts.empty(); }

    void print()
    {
      FOREACH(pts_it,i,pts) {
	errs() << i->first << " :";
	i->second.print();
      }
    }
    
  private:
    
    class change_set
    {
    public:

      change_set() {}

      void insert(u32 x) { S.push_back(x); }

      void uniq() 
      {
	std::sort(S.begin(),S.end());
	uv_it e = std::unique(S.begin(),S.end());
	S.erase(e,S.end());
      }

      void clear() { S.clear(); }

      bool empty() { return S.empty(); }

      bool has(u32 x) {	return binary_search(S.begin(),S.end(),x); }

      typedef vector<u32>::iterator ch_it;

      ch_it begin() { return S.begin(); }
      ch_it end()   { return S.end();   }

    private:
      vector<u32> S;
    };

    change_set change;
    typedef change_set::ch_it ch_it;
    
    typedef pair<u32,PtsSet> pts_el;
    typedef vector<pts_el>::iterator pts_it;
    typedef vector<pts_el>::const_iterator pts_cit;

    vector<pts_el> pts;

    struct pts_comp
    {
      bool operator()(const pts_el& lhs, const pts_el& rhs) const
      {
	return (lhs.first < rhs.first);
      }
    };

    pts_it pts_find(u32 el)
    {
      return std::lower_bound
	(pts.begin(),pts.end(),pts_el(el,bddfalse),pts_comp());
    }
  };
  
  // map from a partition to a node's successors in that partition
  //
  class PartMap
  {
  public:
    
    PartMap() {}
    
    void insert(u32 dst, u32 part)
    {
      pmap.push_back(pair<u32,u32>(dst,part));
    }

    void erase_dst(u32 dst)
    {
      FORN(i,pmap.size()) {
	if (pmap[i].first == dst) { pmap[i] = pmap.back(); pmap.pop_back(); }
      }
    }

    void erase_dsts(vector<u32>& n)
    {
      uniq();
      // we assume n is sorted

      vector<pair<u32,u32> > p;
      u32 i = 0, j = 0, ie = pmap.size(), je = n.size();
      u32 pi = pmap[i].first, nj = n[j];
      
      while (i < ie && j < je) {
	if      (pi < nj) { p.push_back(pmap[i]); ++i; pi = pmap[i].first; }
	else if (pi == nj) { ++i; pi = pmap[i].first; }
	else /* pi > nj */ { ++j; nj = n[j]; }
      }

      if (i > 0) {
	for ( ; i < ie; ++i) { p.push_back(pmap[i]); }
	pmap.swap(p);
      }
    }

    void uniq()
    {
      std::sort(pmap.begin(),pmap.end());
      pmap_it e = std::unique(pmap.begin(),pmap.end());
      pmap.erase(e,pmap.end());
    }

    bool empty() { return pmap.empty(); }

    u32 size() { return pmap.size(); }

    typedef vector<pair<u32,u32> >::iterator pmap_it;

    pmap_it begin() { return pmap.begin(); }
    pmap_it end()   { return pmap.end();   }
    
  private:
    
    vector<pair<u32,u32> > pmap;
  };

  typedef PartMap::pmap_it pmap_it;
  
  // {addr_of, copy, gep} instruction
  //
  struct TpNode
  {
    Constraint inst;
    vector<u32> succ;
    
    TpNode(const Constraint& c) : inst(c) {}
  };
  
  // noop (a phi node for objects)
  //
  struct NpNode
  {
    PtsGraph pts;
    vector<u32> succ;
  };
  
  // load instruction
  //
  struct LdNode
  {
    u32 rep;             // rep node if this node is shared, 0 else
    PtsSet old;          // value of rhs last time this node was processed
    Constraint inst;
    PtsGraph pts;
    vector<u32> tl_succ; // TpNode successors
    PartMap part_succ;   // {Ld,St,Np}Node successors
    
    LdNode(const Constraint& c) : rep(0), inst(c) {}
  };
  
  // store instruction
  //
  struct StNode
  {
    PtsSet old1, old2; // value of lhs/rhs last time this node was processed
    Constraint inst;
    PtsGraph in, out;
    PartMap part_succ;
    
    StNode(const Constraint& c) : inst(c) {}
  };
  
  enum node_type { IS_TP, IS_LD, IS_ST, IS_NP };
  
  // the dataflow graph, containing all {Tp,Np,Ld,St}Nodes
  //
  class DFG
  {
  public:
    
    DFG() : tp_base(0), ld_base(0), st_base(0), np_base(0) {}
    
    // insert a constraint into the DFG, creating a node for it;
    // return the index of the node in the particular class it belongs
    // to (ie, Tp/Ld/St/Np), rather than in the overall index space
    //
    u32 insert(const Constraint& C)
    {
      switch (C.type) {
      case addr_of_cons:
      case copy_cons:
      case gep_cons:
	tp_nodes.push_back(TpNode(C));
	return tp_nodes.size()-1;
      case load_cons:
	ld_nodes.push_back(LdNode(C));
	return ld_nodes.size()-1;
      case store_cons:
	st_nodes.push_back(StNode(C));
	return st_nodes.size()-1;
      default: assert(0 && "unknown constraint type");
      }
    }
    
    // call this once all {Tp,Ld,St}Nodes have been inserted; it will
    // set the overall index namespace and create the top-level
    // def-use chains (ie, those involving top-level variables)
    //
    void finalize_insert()
    {
      tp_base = 0;
      ld_base = tp_nodes.size();
      st_base = ld_base + ld_nodes.size();
      np_base = st_base + st_nodes.size();

      map<u32,vector<u32> > v2d;
      FORN(i,tp_nodes.size()) {v2d[tp_nodes[i].inst.dest].push_back(tp_base+i);}
      FORN(i,ld_nodes.size()) {v2d[ld_nodes[i].inst.dest].push_back(ld_base+i);}
      
      FORN(i,tp_nodes.size()) {
	Constraint& C = tp_nodes[i].inst;
	if (C.type != addr_of_cons && v2d.count(C.src)) {
	  vector<u32>& def = v2d[C.src];
	  FOREACH(uv_it,j,def) { add_edge(*j,i); }
	}
      }

      FORN(i,ld_nodes.size()) {
	Constraint& C = ld_nodes[i].inst;
	vector<u32>& def = v2d[C.src];
	FOREACH(uv_it,j,def) { add_edge(*j,ld_base+i); }
      }

      FORN(i,st_nodes.size()) {
	Constraint& C = st_nodes[i].inst;
	vector<u32> &d1 = v2d[C.dest], &d2 = v2d[C.src];
	FOREACH(uv_it,j,d1) { add_edge(*j,st_base+i); }
	FOREACH(uv_it,j,d2) { add_edge(*j,st_base+i); }
      }
    }
    
    // insert a NpNode into the DFG; we assume this is done after
    // finalize_insert() has been called
    //
    u32 insert_nop()
    {
      np_nodes.push_back(NpNode());
      return (np_base + np_nodes.size()-1);
    }
    
    // return the type of node the index is for
    //
    bool is_tp(u32 i) { return (i < ld_base); }
    bool is_ld(u32 i) { return (i >= ld_base && i < st_base); }
    bool is_st(u32 i) { return (i >= st_base && i < np_base); }
    bool is_np(u32 i) { return (i >= np_base && i-np_base < np_nodes.size()); }
    
    node_type type(u32 i) const
    {
      if (i < ld_base) { return IS_TP; }
      if (i < st_base) { return IS_LD; }
      if (i < np_base) { return IS_ST; }
      assert(i < np_base + np_nodes.size());
      return IS_NP;
    }

    // return a node of the appropriate type
    //
    TpNode& get_tp(u32 i) { assert(is_tp(i)); return tp_nodes[i]; }
    LdNode& get_ld(u32 i) { assert(is_ld(i)); return ld_nodes[i-ld_base]; }
    StNode& get_st(u32 i) { assert(is_st(i)); return st_nodes[i-st_base]; }
    NpNode& get_np(u32 i) { assert(is_np(i)); return np_nodes[i-np_base]; }
    
    // translate an index for {st,ld}_nodes into the overall index
    // namespace (if d == true) or vice-versa (if d == false)
    //
    u32 st_idx(u32 i, bool d) const 
    {
      assert((d && i < st_nodes.size()) || (!d && i >= st_base && i < np_base));
      return d ? i+st_base : i-st_base;
    }
    
    u32 ld_idx(u32 i, bool d) const
    { 
      assert((d && i < ld_nodes.size()) || (!d && i >= ld_base && i < st_base));
      return d ? i+ld_base : i-ld_base; 
    }
    
    // return the constraint associated with the given node
    //
    Constraint& node_cons(u32 i)
    {
      if (i < ld_base) { return tp_nodes[i].inst; }
      if (i < st_base) { return ld_nodes[i-ld_base].inst; }
      if (i < np_base) { return st_nodes[i-st_base].inst; }
      assert(0 && "noop nodes have no constraints");
    }

    // given a node with a points-to graph, fill it with the set of
    // all vars it may contain
    //
    void prep_node(u32 n, vector<u32>& vars)
    {
      switch (type(n)) {
      case IS_LD:
	get_ld(n).pts.init(vars);
	break;
      case IS_ST:
	{
	  StNode& N = get_st(n);
	  N.in.init(vars);
	  N.out.init(vars);
	}
	break;
      case IS_NP:
	get_np(n).pts.init(vars);
	break;
      default: assert(0 && "unexpected type");
      }
    }

    // set an LdNode's rep
    //
    void set_rep(u32 ld, u32 rep)
    {
      assert(is_ld(ld));
      ld_nodes[ld-ld_base].rep = rep;
    }

    // return the number of shared nodes (ie, the number of LdNodes
    // with a non-zero rep)
    //
    u32 num_shared()
    {
      u32 cnt = 0;
      FORN(i,ld_nodes.size()) {	if (ld_nodes[i].rep) { cnt++; }}
      return cnt;
    }

    typedef vector<TpNode>::iterator tp_it;
    typedef vector<LdNode>::iterator ld_it;
    typedef vector<StNode>::iterator st_it;
    typedef vector<NpNode>::iterator np_it;
    
    // iterate over the TpNodes
    //
    tp_it tp_begin() { return tp_nodes.begin(); }
    tp_it tp_end()   { return tp_nodes.end();   }

    // iterator over the LdNodes
    //
    ld_it ld_begin() { return ld_nodes.begin(); }
    ld_it ld_end()   { return ld_nodes.end();   }

    // iterator over the StNodes
    //
    st_it st_begin() { return st_nodes.begin(); }
    st_it st_end()   { return st_nodes.end();   }

    // iterator over the NpNodes
    //
    np_it np_begin() { return np_nodes.begin(); }
    np_it np_end()   { return np_nodes.end();   }
    
    // insert an edge into the DFG
    //
    void add_edge(u32 src, u32 dst, u32 part = 0)
    {
      switch (type(src)) {
      case IS_TP: tp_nodes[src].succ.push_back(dst); break;
      case IS_LD:
	if (!part) { ld_nodes[src-ld_base].tl_succ.push_back(dst);     }
	else       { ld_nodes[src-ld_base].part_succ.insert(dst,part); }
	break;
      case IS_ST:
	assert(!is_tp(dst) && part);
	st_nodes[src-st_base].part_succ.insert(dst,part);
	break;
      case IS_NP:
	assert(!is_tp(dst) && src < np_base + np_nodes.size());
	np_nodes[src-np_base].succ.push_back(dst);
	break;
      default: assert(0 && "unknown type");
      }
    }
    
    u32 num_tp() const { return tp_nodes.size(); }
    u32 num_ld() const { return ld_nodes.size(); }
    u32 num_st() const { return st_nodes.size(); }
    u32 num_np() const { return np_nodes.size(); }
    u32 num_nodes() const { return np_base + np_nodes.size(); } 

    void stats(vector<bitmap>& vp)
    {
      assert(o2p.size());

      map<u32,u32> np2p, p2ne;
      u32 t1 = 0, t3 = 0, t4 = 0;

      FOREACH(tp_it,i,tp_nodes) { t1 += i->succ.size(); }
      FOREACH(ld_it,i,ld_nodes) { 
	t1 += i->tl_succ.size();

	FOREACH(pmap_it,j,i->part_succ) {
	  if (!j->second) { continue; }
	  assert(j->second < vp.size() && !vp[j->second].empty());
	  p2ne[j->second]++;
	  t3++; t4 += vp[j->second].count();
	  if (is_np(j->first)) { np2p[j->first] = j->second; }
	}
      }
      FOREACH(st_it,i,st_nodes) {
	FOREACH(pmap_it,j,i->part_succ) {
	  if (!j->second) { continue; }
	  assert(j->second < vp.size() && !vp[j->second].empty());
	  p2ne[j->second]++;
	  t3++; t4 += vp[j->second].count();
	  if (is_np(j->first)) { np2p[j->first] = j->second; }
	}
      }

      u32 cnt = 0, old;

      do{
	old = cnt;

	FOREACH(np_it,i,np_nodes) {
	  u32 idx = np_base+(i-np_nodes.begin());
	  if (!np2p.count(idx)) { continue; }
	  FOREACH(uv_it,j,i->succ) {
	    if (is_np(*j) && !np2p.count(*j)) { np2p[*j] = np2p[idx]; cnt++; }
	  }
	}
      }
      while (cnt > old);

      FOREACH(np_it,i,np_nodes) {
	u32 idx = np_base+(i-np_nodes.begin());
	if (!np2p.count(idx)) { continue; }

	p2ne[np2p[idx]] += i->succ.size();
	t3 += i->succ.size();
	t4 += i->succ.size() * vp[np2p[idx]].count();
      }

      errs() << "num edges w/out ae, w/ top == " << t4+t1 << "\n"
	   << "num edges with  ae, w/ top == " << t3+t1 << "\n"
	   << "num edges w/out ae, no top == " << t4 << "\n"
	   << "num edges with  ae, no top == " << t3 << "\n";

      u32 tot = 0, num = 0;

      FOREACH(u2u_it,i,p2ne) {
	u32 nv = vp[i->first].count();
	num += nv;
	tot += (nv * i->second);
      }

      errs() << "avg edges/var == " << (double)tot/num << "\n";
    }

    void print(const string& file)
    {
      //!!
    }
    
  private:
    
    vector<TpNode> tp_nodes; // {alloc,copy,gep} instructions
    vector<NpNode> np_nodes; // noop instructions
    vector<LdNode> ld_nodes; // load instructions
    vector<StNode> st_nodes; // store instructions
    
    // indices >= tp_base and < ld_base refer to tp_nodes; >= ld_base
    // and < st_base refer to ld_nodes; etc for st and np
    //
    u32 tp_base, ld_base, st_base, np_base;
  };
  
  typedef DFG::tp_it tp_it;
  typedef DFG::ld_it ld_it;
  typedef DFG::st_it st_it;
  typedef DFG::np_it np_it;

  //// DATA

  u32 base_mem; // base memory usage

  Anders PRE;               // for obj_cons_id, cons_opt
  StringMap<u64> accum_tbl; // for accumulative time keeping

  vector<PtsSet> top;  // top-level var -> points-to set
  vector<bool> strong; // object -> strong?

  vector<u32> priority; // the priority of each DFG node

  DFG dfg; // the dataflow graph

  //// NEW METHODS

  // obj_cons_id.cpp

  void sfs_id();
  void cons_opt_wrap();
  void processBlock(u32,BasicBlock*);

  void icfg_inter_edges();
  void process_idr_cons();

  void sfs_prep();

  void partition_vars();
  void compute_seg();

  void process_seg(u32,u32);
  void process_1store(u32);
  void process_1load(u32);

  // cons_opt.cpp

  void cons_opt(vector<u32>&);
  void make_off_graph();

  // main.cpp

  void reset_time();
  void accum_time_and_rst(const char*);
  void print_accum_time(const char*);

  // solve.cpp

  void processTp(TpNode&);
  void processLd(LdNode&,u32);
  void processSt(StNode&,u32);
  void processNp(NpNode&);
  void processSharedLd(LdNode&,PtsGraph&);

  //// METHODS OVERRIDDEN FROM ANDERS

  // obj_cons_id

  void visit_func(Function*);

  // solve.cpp

  bool solve();
};

#endif // _SFS_AA_H
