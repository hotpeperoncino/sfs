/*  [anders.h] Anders class definition and helper classes
 *  v. 014, 2008-09-14
 *  This is an LLVM implementation of Andersen's inclusion-based pointer
 *    analysis (interprocedural, flow-insensitive, context-insensitive, and
 *    field-sensitive).
 *  Run this pass with:
 *    opt -load $LLVM_INSTALL/lib/anders-aa.so -anders -analyze file.bc
 *
 *  The algorithm used here is described in:
 *    "The Ant and the Grasshopper: Fast and Accurate Pointer Analysis for
 *    Millions of Lines of Code", by Ben Hardekopf & Calvin Lin, in PLDI 2007.
 *  It operates in 3 phases:
 *  - Object/constraint identification: creates graph nodes for all relevant
 *    values in the program and translates instructions into
 *    inclusion constraints.
 *  - Constraint optimization
 *  - Constraint solving: computes the transitive closure of the cons. graph.
 *
 *  This project uses some ideas from the original LLVM implementation of
 *    Andersen's (-anders-aa), as well as from Ben Hardekopf's
 *    flow-sensitive analysis code.
 *------------------------------------------------------------------------------
 *  Changes from 013:
 *  - debug, stats, and metrics disabled here (rather than common.h)
 *    - debug output for obj_cons_id, cons_opt, or solve may be disabled
 *  - renamed first_val_node -> first_var_node
 *  - Node class has is_rep() and nonptr flag
 *  - removed DenseMapInfo<u32>; hash<pair> moved to common.h
 *  - added stats for HVN & HCD
 *  - added hcd_var
 *  - print_cons_graph() is now public
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

#ifndef __ANDERS_H
#define __ANDERS_H

//Set each to 1 to enable, 0 to disable: debug output, statistics processing,
//  metrics, memory/time tracking, and Google profiler.
//Note that disabling debug may cause "empty body in an if statement" warnings.
//Assertions can be disabled in common.h.
#define USE_DEBUG 0//1
#define USE_STATS 0//1
#define USE_METRICS 0//1
#define USE_MEM_TIME 0//1
#define USE_PROFILER 0//1
//Disable some types of debug output by setting these to 0.
#define DEBUG_OCI 0
#define DEBUG_OPT 0
#define DEBUG_SOLVE 0
//Stop as soon as the constraints have been generated?
#define OCI_ONLY 0
//Skip the solver (for testing the optimization stage)?
#define NO_SOLVE 0
//Check for constraints with "undefined" sources?
#define CHECK_CONS_UNDEF 0//1
//List unknown external calls to stderr?
#define LIST_EXT_UNKNOWN 0
//How much RAM (in MB) and time (sec) the solver is allowed to use.
#define SOLVE_RAM_LIMIT 1200//3072
#define SOLVE_TIME_LIMIT 1200

#include "common.h"
#include "extinfo.h"
#include "worklist.h"

typedef DenseMap<const StructType*, pair<vector<u32>, vector<u32> > >
    structinfo_t;

//LCD runs when there are at least (lcd_size) candidates for cycle detection,
//  or if it has not run for (lcd_period) solve_node runs.
const u32 lcd_size= 600, lcd_period= 999999999;

//------------------------------------------------------------------------------
#if USE_DEBUG == 1
  #undef DEBUG_TYPE
  #define DEBUG_TYPE "anders"
#else
  #undef DEBUG
  #define DEBUG(x)
#endif

//Print the C-str (s) to stderr.
#define PUTS(s) fputs(s, stderr)
#define DPUTS(s) DEBUG(PUTS(s))
#define DEOL DEBUG(putc('\n', stderr))

//------------------------------------------------------------------------------
//Special node IDs: 0 - no node, i2p - unknown target of pointers cast from int,
//  p_i2p - constant ptr to i2p,
//  first_var_node - the 1st node representing a real variable.
const u32 i2p= 1, p_i2p= 2, first_var_node= 3;
//When there are no structs, max_struct is assigned the smallest type.
const Type *const min_struct= Type::Int8Ty;
//The offsets from a function's obj node to the return value and first arg.
const u32 func_node_off_ret= 1, func_node_off_arg0= 2;
//The starting union-find rank of any node.
const u32 node_rank_min= 0xf0000000;

//------------------------------------------------------------------------------
// Constraint class
//------------------------------------------------------------------------------

//There are 5 types of constraints in Andersen's analysis:
//  Address-of (Base): D = &S
//  Copy (Simple): D = S
//  Load (Complex 1): D = *S + off
//  Store (Complex 2): *D + off = S
//  GEP (copy+offset): D = S + off
enum ConsType {addr_of_cons, copy_cons, load_cons, store_cons, gep_cons};

//------------------------------------------------------------------------------
class Constraint{
public:
  ConsType type;
  u32 dest, src, off;

  Constraint(ConsType t, u32 d, u32 s, u32 o= 0):
    type(t), dest(d), src(s), off(o) {}

//------------------------------------------------------------------------------
  bool operator == (const Constraint &b) const{
    return type == b.type && dest == b.dest && src == b.src && off == b.off;
  }
  bool operator < (const Constraint &b) const{
    if(type != b.type)
      return type < b.type;
    if(dest != b.dest)
      return dest < b.dest;
    if(src != b.src)
      return src < b.src;
    return off < b.off;
  }
  bool operator > (const Constraint &b) const{
    if(type != b.type)
      return type > b.type;
    if(dest != b.dest)
      return dest > b.dest;
    if(src != b.src)
      return src > b.src;
    return off > b.off;
  }
  bool operator != (const Constraint &b) const{
    return !(operator==(b));
  }
  bool operator >= (const Constraint &b) const{
    return !(operator<(b));
  }
  bool operator <= (const Constraint &b) const{
    return !(operator>(b));
  }
};

namespace llvm{
  template<> struct DenseMapInfo<Constraint>{
    static Constraint getEmptyKey(){
      return Constraint(addr_of_cons, 0, 0, 0);
    }
    static Constraint getTombstoneKey(){
      return Constraint(copy_cons, 0, 0, 0);
    }
    static unsigned getHashValue(const Constraint &X){
      return ((u32)X.type<<29) ^ (X.dest<<12) ^ X.src ^ X.off;
    }
    static unsigned isEqual(const Constraint &X, const Constraint &Y){
      return X == Y;
    }
  };
}
namespace __gnu_cxx{
  template<> struct hash<Constraint>{
    size_t operator () (const Constraint &X) const{
      return ((size_t)X.type<<29) ^ (X.dest<<12) ^ X.src ^ X.off;
    }
  };
}

//------------------------------------------------------------------------------
// Node class
//------------------------------------------------------------------------------

class Node{
private:
  //The LLVM value represented by this node, or 0 for artificial nodes
  Value *val;

public:
  //How many nodes in the object that starts here (0 if it's not an obj node).
  //  For structs this equals the corresponding struct_sz element.
  u32 obj_sz;
  //The time this node was last visited
  u32 vtime;
  //If rep < node_rank_min, this node is part of a set of equivalent nodes
  //  and (rep) is another node in that set.
  //Else this is the representative node of the set,
  //  and (rep) is its rank in the union-find structure.
  u32 rep;
  //If this node was determined to not point to anything
  bool nonptr;
  //For SFS: true if this is an array or is heap-allocated
  bool weak;

  //The nodes in our points-to set
  bdd points_to;
  //The points_to set at the start of the last visit to this node
  bdd prev_points_to;
  //The simple constraint edges, i.e. the neighbors that
  //  include our points-to set
  bitmap copy_to;
  //Indices into cplx_cons for load, store, and gep cons.
  bitmap load_to, store_from, gep_to;

//------------------------------------------------------------------------------
  Node(Value *v= 0, u32 s= 0, bool w= 0): val(v), obj_sz(s), vtime(0),
      rep(node_rank_min), nonptr(0), weak(w) {}

  bool is_rep() const{
    return rep >= node_rank_min;
  }

  Value* get_val() const{
    return val;
  }
  void set_val(Value *v){
    val= v;
  }
};

//------------------------------------------------------------------------------
// Main class
//------------------------------------------------------------------------------

class Anders {
protected:
//------------------------------------------------------------------------------
// Statistics
//------------------------------------------------------------------------------

  //Declare all global integer stats here; prefix all names with stat_.
  //They will be printed in the order they appear here.
  //Keep the num_stats at the end.
  enum{
    stat_i_val_nodes= 0, stat_i_obj_nodes, stat_insn, stat_i_cons,
    stat_i_addr_cons, stat_i_copy_cons, stat_i_load_cons, stat_i_store_cons,
    stat_i_gep_cons, stat_r_val_nodes, stat_r_cons, stat_r_addr_cons,
    stat_r_copy_cons, stat_r_load_cons, stat_r_store_cons, stat_r_gep_cons,
    stat_hvn_merge, stat_hcd_size, stat_hcd_var_merge,
    stat_hcd_on_var_merge, stat_hcd_on_scc, stat_hcd_on_sccn,
    stat_ls_factored,
    stat_passes, stat_node_push, stat_node_pop, stat_node_run,
    stat_copy_add, stat_copy_del, stat_ccons_del, stat_ind_alloc,
    stat_lcd_run, stat_lcd_scc, stat_lcd_sccn,
  num_stats};

  //Describe all stats at the bottom of print.cpp.
  static const char *const (stat_desc[]);

  //The values of the stats go here.
  u32 *stats;

#if USE_STATS == 1
  //To get the value of stat_foo, use STAT(foo).
  #define STAT(i) stats[stat_##i]
  //Use these to change the values of stats; never modify STAT(i) directly.
  #define SET_STAT(i, x) (STAT(i) = (x))
  #define COPY_STAT(i, j) (STAT(i) = STAT(j))
  #define INC_STAT(i) (++STAT(i))
  #define ADD_STAT(i, x) (STAT(i) += (x))
  #define SUB_STAT(i, x) (STAT(i) -= (x))
#else
  #define STAT(i) 0
  #define SET_STAT(i, x)
  #define COPY_STAT(i, j)
  #define INC_STAT(i)
  #define ADD_STAT(i, x)
  #define SUB_STAT(i, x)
#endif

//------------------------------------------------------------------------------
// Analysis results (should remain in memory after the run completes)
//------------------------------------------------------------------------------

  //The CPU time at the last print_time() (or at the start of the pass)
  u64 start_time;

  //The nodes of the constraint and points-to graph
  vector<Node*> nodes;

  //The ID of the last object node (set by clump_addr_taken).
  u32 last_obj_node;

  //The node ID of each value, the first node of its object (if it has one),
  //  and the nodes for the return value and varargs of a function.
  DenseMap<Value*, u32> val_node, obj_node;
  DenseMap<Function*, u32> ret_node, vararg_node;

  //The number (within a function) of each unnamed temporary value.
  //These numbers should match those in the bitcode disassembly.
  DenseMap<Instruction*, u32> tmp_num;

  //The set of BDD variables in FDD domain 0 (which is used to represent
  //  the IDs of points-to members).
  bdd pts_dom;
  //Map the GEP-result FDD domain (1) to the points-to domain (0).
  bddPair *gep2pts;
  //For offset (i), geps[i] is the BDD function from the points-to domain
  //  to the GEP domain that adds (i) to each points-to member and removes
  //  the members too small for this offset.
  //The offsets that don't occur in actual constraints are mapped to bddfalse.
  vector<bdd> geps;

//------------------------------------------------------------------------------
// Data required during the entire run (may be deleted when the solver exits)
//------------------------------------------------------------------------------

  //The module we are currently analyzing
  Module *curr_module;

  //The constraint list
  vector<Constraint> constraints;

  //The function pointer nodes used for indirect calls
  set<u32> ind_calls;

  ExtInfo *extinfo;                     //see extinfo.h

  //The load/store constraints representing an indirect call's
  //  return and args are mapped to the instruction of that call.
  //  Because constraints referring to different calls may be merged,
  //  1 cons. may map to several calls.
  DenseMap<Constraint, set<Instruction*> > icall_cons;

  //The map of a dereferenced node to the VAR node in its SCC; see hcd().
  DenseMap<u32, u32> hcd_var;

  //For every valid offset (i), off_mask[i] is the set of nodes
  //  with obj_sz > i (for faster handling of load/store with offset).
  vector<bdd> off_mask;

  //The set of obj. nodes representing ext. functions.
  //The second version is for quickly testing if a given node is an ext.func.
  bdd ext_func_nodes;
  set<u32> ext_func_node_set;
  //The set of all nodes that start a function object
  //  (superset of ext_func_node_set).
  set<u32> func_node_set;

  //The solver's worklist.
  Worklist *WL;
  //How many times solve_node() has run.
  u32 n_node_runs;
  //The n_node_runs at the time of the last LCD run.
  u32 last_lcd;
  //The sequence number of the current node visit
  u32 vtime;
  //The number of the current lcd_dfs run
  u32 curr_lcd_dfs;
  //The copy edges across which we already found identical points-to sets
  DenseSet<pair<u32, u32> > lcd_edges;
  //The next LCD run should start from these nodes.
  set<u32> lcd_starts;
  //The DFS timestamp of each visited node
  map<u32,u32> lcd_dfs_id;
  //The stack of nodes visited by lcd_dfs()
  stack<u32> lcd_stk;
  //The roots of SCCs collapsed on this pass
  set<u32> lcd_roots;
  //The indirect ext. calls that have already been handled
  set<pair<Function*, Instruction*> > ext_seen;
  //The result of fdd_ithvar for each object node ID.
  vector<bdd> node_vars;
  //The names of unsupported external functions that were indirectly called.
  hash_set<string> ext_failed;
  //The complex constraints (load, store, GEP) from the optimized list.
  vector<Constraint> cplx_cons;

//------------------------------------------------------------------------------
// Data required only for object/constraint ID
//   (may be deleted before optimize/solve)
//------------------------------------------------------------------------------

  //The ID of the node to create next (should equal nodes.size())
  u32 next_node;

  //The struct type with the most fields
  //  (or min_struct if no structs are found).
  //All allocations are assumed to be of this type,
  //  unless trace_alloc_type() succeeds.
  const Type* max_struct;
  //The # of fields in max_struct (0 for min_struct)
  u32 max_struct_sz;

  //Every struct type T is mapped to the vectors S (first) and O (second).
  //If field [i] in the expanded struct T begins an embedded struct,
  //  S[i] is the # of fields in the largest such struct, else S[i] = 1.
  //S[0] is always the size of the expanded struct T, since a pointer to
  //  the first field of T can mean all of T.
  //Also, if a field has index (j) in the original struct, it has index
  //  O[j] in the expanded struct.
  structinfo_t struct_info;

  //The list of value nodes for constant GEP expr.
  vector<u32> gep_ce;

  //The nodes that have already been visited by proc_global_init or proc_gep_ce.
  //The value is the return of proc_global_init, or 1 for proc_gep_ce.
  DenseMap<u32, u32> global_init_done;

  //The name of every has_static() ext. function is mapped to
  //  the node of the static object that its return points to.
  map<string, u32> stat_ret_node;

  //The args of addr-taken func. (exception for the node-info check)
  DenseSet<Value*> at_args;

//------------------------------------------------------------------------------
// Private methods
//------------------------------------------------------------------------------

  //Object/constraint identification phase (obj_cons_id.cpp)
  void obj_cons_id();
  bool add_cons(ConsType t, u32 dest, u32 src, u32 off= 0);
  void verify_nodes();
  void id_func(Function *F);
  virtual void visit_func(Function *F);
  void processBlock(BasicBlock*);

  void id_ret_insn(Instruction *I);
  void id_call_insn(Instruction *I);
  void id_alloc_insn(Instruction *I);
  void id_load_insn(Instruction *I);
  void id_store_insn(Instruction *I);
  void id_gep_insn(Instruction *I);
  void id_i2p_insn(Value *V);
  void id_bitcast_insn(Instruction *I);
  void id_phi_insn(Instruction *I);
  void id_select_insn(Instruction *I);
  void id_vaarg_insn(Instruction *I);
  void id_extract_insn(Instruction *I);

  void id_call_obj(u32 vnI, Function *F);
  void id_dir_call(CallSite CS, Function *F);
  void id_ind_call(CallSite CS);
  void id_ext_call(CallSite CS, Function *F);
  void add_store2_cons(Value *D, Value *S, u32 sz= 0);

  void id_global(GlobalVariable *G);
  void id_gep_ce(Value *G);
  u32 proc_global_init(u32 onG, Constant *C, bool first= 1);
  void proc_gep_ce(u32 vnE);

  void _analyze_struct(const StructType *T);
  u32 compute_gep_off(User *V);
  const Type* trace_alloc_type(Instruction *I);
  u32 get_max_offset(Value *V);
  u32 get_val_node_cptr(Value *V);
  bool escapes(Value *V) const;
  bool trace_int(Value *V, DenseSet<Value*> &src,
      DenseMap<Value*, bool> &seen, u32 depth= 0);

//------------------------------------------------------------------------------
  //Constraint optimization phase (cons_opt.cpp)
  void cons_opt();
  void clump_addr_taken();
  u32 merge_nodes(u32 n1, u32 n2);
  void make_off_nodes();
  void add_off_edges(bool hcd= 0);
  void hvn(bool do_union);
  void hr(bool do_union= 0, u32 min_del= 100);
  void hvn_dfs(u32 n, bool do_union);
  void hvn_check_edge(u32 n, u32 dest, bool do_union);
  void hvn_label(u32 n);
  void hu_label(u32 n);
  void merge_ptr_eq();
  void hcd();
  void hcd_dfs(u32 n);
  void factor_ls();
  void factor_ls(const set<u32> &other, u32 ref, u32 off, bool load);

//------------------------------------------------------------------------------
  //Constraint solving phase (solve.cpp)
  void pts_init();
  void solve_init();
  bool solve();
  void run_lcd();
  void solve_node(u32 n);
  bool solve_ls_cons(u32 n, u32 hcd_rep, bdd d_points_to,
      set<Constraint> &cons_seen, Constraint &C);
  void solve_ls_off(bdd d_points_to, bool load, u32 dest, u32 src, u32 off,
      const set<Instruction*> *I);
  void solve_ls_n(const u32 *pdpts, const u32 *edpts, bool load,
      u32 dest, u32 src);
  bool solve_gep_cons(u32 n, bdd d_points_to,
      set<Constraint> &cons_seen, Constraint &C);
  bool add_copy_edge(u32 src, u32 dest);
  void solve_prop(u32 n, bdd d_points_to);
  void lcd_dfs(u32 n);
  void handle_ext(Function *F, Instruction *I);

//------------------------------------------------------------------------------
  //Init/cleanup (main.cpp)
  void run_init(Module *M);
  void pre_opt_cleanup();
  void run_cleanup();
  void pts_cleanup();
  u32 get_mem_usage(bool init= 0) const;
  u64 get_cpu_time() const;
  void print_time(const char *label);

//------------------------------------------------------------------------------
  //Printing (print.cpp)
  void _pb_free();
  void print_val(Value *V, u32 n= 0, bool const_with_val= 1, bool first= 1)
      const;
  void print_val_now(Value *V, u32 n= 0) const;
  void _print_const(Constant *C, u32 n, bool const_with_val, bool first) const;
  void _print_const_expr(ConstantExpr *E) const;
  void print_node(u32 n, u32 width= 0) const;
  void print_node_now(u32 n) const;
  void print_all_nodes(bool sorted= 0) const;
  void print_struct_info(const Type *T) const;
  void print_all_structs() const;
  void print_constraint(const Constraint &C) const;
  void print_constraint_now(const Constraint &C) const;
  void print_all_constraints(bool sorted= 0) const;
  void _print_node_cons(const bitmap &L) const;
  void print_stats() const;
  void print_metrics() const;
  void list_ext_calls(Module &M) const;
  void list_ext_unknown(Module &M) const;

//------------------------------------------------------------------------------
// Inline methods
//------------------------------------------------------------------------------

  //Find the node representing the value (V).
  //If V is not mapped to any node, returns 0 when allow_null is 1, else aborts.
  u32 get_val_node(Value *V, bool allow_null= 0) const{
    assert(V);
    DenseMap<Value*, u32>::const_iterator it= val_node.find(V);
    if(it == val_node.end()){
      if(allow_null)
        return 0;
      else{
        PUTS("\nValue has no node:  ");
        print_val_now(V);
        putc('\n', stderr);
        assert(0);
      }
    }
    u32 vn= it->second;
    assert(vn && "val_node map has a 0 entry");
    return vn;
  }

  //Find the starting node of the object of (V).
  u32 get_obj_node(Value *V, bool allow_null= 0) const{
    assert(V);
    DenseMap<Value*, u32>::const_iterator it= obj_node.find(V);
    if(it == obj_node.end()){
      if(allow_null)
        return 0;
      else{
        PUTS("\nValue has no obj node:  ");
        print_val_now(V);
        putc('\n', stderr);
        assert(0);
      }
    }
    u32 on= it->second;
    assert(on && "obj_node map has a 0 entry");
    return on;
  }

//------------------------------------------------------------------------------
  //Find the node for the return value of (F).
  //Returns 0 if F doesn't return a ptr.
  u32 get_ret_node(Function *F) const{
    assert(F);
    if(!isa<PointerType>(F->getFunctionType()->getReturnType()))
      return 0;
    DenseMap<Function*, u32>::const_iterator it= ret_node.find(F);
    if(it == ret_node.end()){
      //Addr-taken func. have obj nodes in place of the ret/vararg nodes.
      u32 on= get_obj_node(F, 1);
      assert(on && "missing ret_node entry");
      return on + func_node_off_ret;
    }
    u32 rn= it->second;
    assert(rn && "ret_node map has a 0 entry");
    return rn;
  }

  //Find the node for the vararg part of (F).
  //Returns 0 if F is not vararg.
  u32 get_vararg_node(Function *F) const{
    assert(F);
    if(!F->getFunctionType()->isVarArg())
      return 0;
    DenseMap<Function*, u32>::const_iterator it= vararg_node.find(F);
    if(it == vararg_node.end()){
      u32 on= get_obj_node(F, 1);
      assert(on && "missing vararg_node entry");
      return on + nodes[on]->obj_sz - 1;
    }
    u32 va= it->second;
    assert(va && "vararg_node map has a 0 entry");
    return va;
  }

//------------------------------------------------------------------------------
  //Return the name of type (T).
  const char* get_type_name(const Type *T) const{
    assert(T);
    if(curr_module){
      const char *s= curr_module->getTypeName(T).c_str();
      if(*s)
        return s;
    }
    //getDescription() seems buggy, sometimes runs out of memory
//    return T->getDescription();
    if(isa<StructType>(T))
      return "<anon.struct>";
    return "<??\?>";
  }

//------------------------------------------------------------------------------
  //Get an iterator for struct_info[T], initializing as needed.
  //Do not call this directly; use the methods below.
  structinfo_t::iterator _get_struct_info_iter(const StructType *T){
    assert(T);
    structinfo_t::iterator it= struct_info.find(T);
    if(it != struct_info.end())
      return it;
    _analyze_struct(T);
    return struct_info.find(T);
  }

  //Get a reference to struct_info[T].
  const pair<vector<u32>, vector<u32> >& get_struct_info(const StructType *T){
    return _get_struct_info_iter(T)->second;
  }
  //Get a reference to either component of struct_info.
  const vector<u32>& get_struct_sz(const StructType *T){
    return _get_struct_info_iter(T)->second.first;
  }
  const vector<u32>& get_struct_off(const StructType *T){
    return _get_struct_info_iter(T)->second.second;
  }

//------------------------------------------------------------------------------
  //Return the representative node # of the set containing node #n.
  //This also does path compression by setting the rep field
  //  of all nodes visited to the result.
  u32 get_node_rep(u32 n){
    u32 &r0= nodes[n]->rep;
    //If (n) has a rank, it is the rep.
    if(r0 >= node_rank_min)
      return n;
    //Recurse on the parent to get the real rep.
    u32 r= get_node_rep(r0);
    r0= r;                              //set n's parent to the rep
    return r;
  }
  //const version of the above, w/o path compression.
  u32 cget_node_rep(u32 n) const{
    u32 r;
    while((r= nodes[n]->rep) < node_rank_min)
      n= r;
    return n;
  }

//------------------------------------------------------------------------------
  //A caching wrapper for fdd_ithvar. This is faster than filling in
  //  all the entries at the start because we don't use all the nodes.
  bdd get_node_var(u32 n){
    bdd &b= node_vars[n];
    if(b == bddfalse)
      b= fdd_ithvar(0, n);
    return b;
  }

public:
//------------------------------------------------------------------------------
// LLVM interface
//------------------------------------------------------------------------------

  Anders(): stats(0), last_obj_node(0), gep2pts(0), curr_module(0),
      extinfo(0), WL(0) {}
  ~Anders(){
    releaseMemory();
  }

  //see main.cpp
  virtual bool runOnModule(Module &M);
  virtual void releaseMemory();
  //for AndersAA::print()
  void print_cons_graph(bool points_to_only= 1, bool sorted= 0,
      std::ostream *O= 0) const;

  //see main.cpp
  const vector<u32>* pointsToSet(Value*, u32= 0);
  const vector<u32>* pointsToSet(u32, u32= 0);
  u32 PE(Value*);
  u32 PE(u32);
  bool is_null(u32,u32);
  bool is_single(u32,u32);
  vector<bdd>& get_geps();
};

#endif
