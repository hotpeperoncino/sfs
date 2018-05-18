/*  [obj_cons_id.cpp] Object/constraint identification
 *  v. 014, 2008-09-14
 *------------------------------------------------------------------------------
 *  Changes from 013:
 *  - visit_func() processes basic blocks in CFG order
 *    - processBlock()
 *  - proc_global_init() uses isSingleValueType()
 *  - removed id_getresult_insn() and GetResult support
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

#include "../include/anders.h"
#if DEBUG_OCI == 0
  #undef DEBUG
  #define DEBUG(x)
#endif

//------------------------------------------------------------------------------
void Anders::obj_cons_id(){
  assert(curr_module && "obj_cons_id called when not running on a module");
  DPUTS("***** obj_cons_id starting\n");

  //Insert special nodes w/o values.
  next_node= first_var_node;
  FORN(i, first_var_node)
    nodes.push_back(new Node);
  //i2p is actually an object, since its addr. is taken;
  //  p_i2p is its initial pointer
  nodes[i2p]->obj_sz= 1;
  add_cons(addr_of_cons, p_i2p, i2p);

  //Find and analyze all struct types in the program.
  max_struct= min_struct;
  max_struct_sz= 0;

  //  TypeSymbolTable &tst= curr_module->getTypeSymbolTable();
  //  for(TypeSymbolTable::iterator it= tst.begin(), ie= tst.end(); it != ie; ++it)
  //    if(const StructType* ST= dyn_cast<StructType>(it->second))
  //      _analyze_struct(ST);

  //ID all functions & globals.
  for(Module::iterator it= curr_module->begin(), ie= curr_module->end();
      it != ie; ++it)
    id_func(&*it);
  for(Module::global_iterator it= curr_module->global_begin(),
      ie= curr_module->global_end(); it != ie; ++it)
    id_global(&*it);

  //Init globals separately
  //  (since an initializer may refer to a global below it).
  for(Module::global_iterator it= curr_module->global_begin(),
      ie= curr_module->global_end(); it != ie; ++it){
    GlobalVariable *G= &*it;
    if(G->hasInitializer()){
      proc_global_init(get_obj_node(G), G->getInitializer());
//    }else{
//      PUTS("!! uninitialized global:  ");
//      print_val_now(G);
//      putc('\n', stderr);
    }
  }
  //Now handle all remaining GEP CEs, since some of them are local.
  FORN(i, gep_ce.size())
    proc_gep_ce(gep_ce[i]);

  //Visit all instructions (which may refer to any of the above).
  for(Module::iterator it= curr_module->begin(), ie= curr_module->end();
      it != ie; ++it){
    if(!extinfo->is_ext(&*it))
      visit_func(&*it);
  }

  //Count the node types (except the special nodes).
  assert(next_node == nodes.size() && "wrong node count");
  for(u32 i= first_var_node, ie= nodes.size(); i < ie; ++i){
    //Anything with an obj_sz is an object node, else it's a value node.
    //Note that "artificial" nodes (with no value) now count as value nodes
    //  because the optimizations and solver treat them the same.
    if(nodes[i]->obj_sz)
      INC_STAT(i_obj_nodes);
    else
      INC_STAT(i_val_nodes);
  }
  SET_STAT(i_cons, constraints.size());

  DEBUG(print_all_structs());
  //The nodes are now verified and printed at the end of clump_addr_taken().
  //The original constraints should appear in the order they were identified.
  DEBUG(print_all_constraints(0));

#if CHECK_CONS_UNDEF
  //Look for nodes that are read by constraints but never written.
  hash_set<u32> def;
  FORN(i, constraints.size()){
    if(constraints[i].type != store_cons)
      def.insert(constraints[i].dest);
  }
  //Assume addr-taken function args are always defined (as they will be
  //  written by the store_cons of indirect calls).
  for(DenseSet<Value*>::iterator it= at_args.begin(), ie= at_args.end();
      it != ie; ++it){
    def.insert(get_val_node(*it));
  }
  //The header should not appear if there is no problem.
  bool hdr_done= 0;
  FORN(i, constraints.size()){
    const Constraint &C= constraints[i];
    assert(C.src);
    if(C.type == addr_of_cons || def.count(C.src))
      continue;
    Value /**D= nodes[C.dest]->get_val(),*/ *S= nodes[C.src]->get_val();
    if(S){
      if(isa<Argument>(S)){
        //A non-addr-taken function may be never used, or one of its args
        //  may be always set to null.
        continue;//PUTS("[arg] ");
      }else if(!strcmp(S->getNameStart(), "UnifiedRetVal")){
        //A function may always return null; with opt -mergereturn,
        //  the UnifiedRetVal is undef, else the <retval> itself is.
        continue;//PUTS("[uret] ");
      }else if(Function *F= dyn_cast<Function>(S)){
        if(C.src == get_ret_node(F)){
          continue;//PUTS("[ret] ");
        //The vararg part may also be unused.
        }else if(C.src == get_vararg_node(F)){
          continue;//PUTS("[vararg] ");
        }
      }
    }
    if(!hdr_done){
      hdr_done= 1;
      PUTS("!! Constraints with undefined src:\n");
    }
    print_constraint_now(C);
    putc('\n', stderr);
  }
#endif
}

//------------------------------------------------------------------------------
//add_cons - Add the constraint (t dest src off) to the list, unless:
//  - the constraint is meaningless, like (copy A A 0)
//  - one of the nodes is null
//  - offset is given for addr_of or copy
//Returns true iff it was added.
bool Anders::add_cons(ConsType t, u32 dest, u32 src, u32 off){
  assert(src && dest && "null node in constraint");
  if(t == copy_cons && src == dest)
    return 0;
  if(t == gep_cons && !off)             //replace 0-offset GEP by copy
    t= copy_cons;
  Constraint C(t, dest, src, off);
  switch(t){
    case addr_of_cons:
      assert(dest != i2p);
      assert(!off && "offset not allowed on addr_of_cons");
      INC_STAT(i_addr_cons);
      break;
    case copy_cons:
      assert(src != i2p && dest != i2p);
      assert(!off && "offset not allowed on copy_cons");
      INC_STAT(i_copy_cons);
      break;
    case load_cons:
      assert(src != i2p && dest != i2p && src != p_i2p);
      INC_STAT(i_load_cons);
      break;
    case store_cons:
      assert(src != i2p && dest != i2p && dest != p_i2p);
      INC_STAT(i_store_cons);
      break;
    case gep_cons:
      assert(src != i2p && dest != i2p);
      INC_STAT(i_gep_cons);
      break;
    default:
      assert(!"unknown constraint type");
  }
  constraints.push_back(C);
  return 1;
}

//------------------------------------------------------------------------------
//Make sure that every node has reasonable info and all values are mapped
//  to the right nodes.
void Anders::verify_nodes(){
  DPUTS("***** Checking node info consistency...\n");
  FORN(i, nodes.size()){
    const Node *N= nodes[i];
    Value *V= N->get_val();
    u32 sz= N->obj_sz;
    if(!V){
      assert(!sz || i == i2p && "artificial node has an obj_sz");
      continue;
    }
    u32 vn= get_val_node(V, 1), on= get_obj_node(V, 1), rn= 0, va= 0;
    if(Function *F= dyn_cast<Function>(V)){
      //Don't use get_ret_node, etc. here -
      //  they will return the obj node for AT func.
      DenseMap<Function*, u32>::iterator it= ret_node.find(F);
      if(it != ret_node.end())
        rn= it->second;
      it= vararg_node.find(F);
      if(it != vararg_node.end())
        va= it->second;
    }
    u32 osz= nodes[on]->obj_sz;
    //This is a value node (including ret/vararg).
    if(i == vn || i == rn || i == va)
      assert((!sz || at_args.count(V)) && "value node has an obj_sz");
    //This node is within the object of its value.
    else if(i < on+osz)
      assert(sz && i+sz <= on+osz && "invalid obj_sz");
    else
      assert(!"node is none of val. obj. or art.");
  }

  for(DenseMap<Value*, u32>::iterator it= val_node.begin(),
      ie= val_node.end(); it != ie; ++it){
    Value *V= it->first;
    //The args of addr-taken func. are mapped to the func. obj_nodes instead.
    if(!at_args.count(V))
      assert(V == nodes[it->second]->get_val() && "bad val_node entry");
  }
  for(DenseMap<Value*, u32>::iterator it= obj_node.begin(),
      ie= obj_node.end(); it != ie; ++it)
    assert(it->first == nodes[it->second]->get_val() && "bad obj_node entry");
  for(DenseMap<Function*, u32>::iterator it= ret_node.begin(),
      ie= ret_node.end(); it != ie; ++it)
    assert(it->first == nodes[it->second]->get_val() && "bad ret_node entry");
  for(DenseMap<Function*, u32>::iterator it= vararg_node.begin(),
      ie= vararg_node.end(); it != ie; ++it)
    assert(it->first == nodes[it->second]->get_val() &&
        "bad vararg_node entry");
}

//------------------------------------------------------------------------------
// Function processing
//------------------------------------------------------------------------------
//Add the nodes & constraints for the declaration of (F).
void Anders::id_func(Function *F){
  assert(F);
  bool AT= escapes(F);        //whether this function's addr. is ever taken
  DPUTS("id_func  ");
  DEBUG(print_val_now(F));
  DPUTS(":  addr ");
  DPUTS(AT ? "taken" : "not taken");
  u32 vnF= 0, onF= 0;
  //Only make val/obj nodes for addr-taken functions.
  if(AT){
    vnF= next_node++;
    onF= next_node++;
    nodes.push_back(new Node(F));
    //Only 1 obj node for ext.func
    nodes.push_back(new Node(F, 1));
    val_node[F]= vnF;
    obj_node[F]= onF;
    add_cons(addr_of_cons, vnF, onF);
  }
  //Ext. func. should not be analyzed (since they are handled at the call site).
  if(extinfo->is_ext(F)){
    DPUTS(", ext\n");
    return;
  }
  DEOL;
  bool is_va= F->isVarArg();
  bool ptr_ret= isa<PointerType>(F->getReturnType());
  //The double-ptr args to main(), argv & envp, are treated as external vars.
  if(F->getName() == "main"){
    //Assume that main() is never called indirectly.
    u32 i= 0;
    for(Function::arg_iterator it= F->arg_begin(), ie= F->arg_end(); it != ie;
      ++it, ++i){
      if(i < 1)
        continue;
      if(i > 2)
        break;
      //Args 1 (argv) & 2 (envp) need 2 obj nodes, with v -> o0 -> o1.
      u32 vn= next_node++;
      nodes.push_back(new Node(it));
      val_node[it]= vn;
      u32 on= next_node;
      nodes.push_back(new Node(it, 2));
      nodes.push_back(new Node(it, 1));
      next_node += 2;
      obj_node[it]= on;
      add_cons(addr_of_cons, vn, on);
      add_cons(addr_of_cons, on, on+1);
    }
  }else if(!AT){
    //Make a value node for each ptr arg.
    for(Function::arg_iterator it= F->arg_begin(), ie= F->arg_end(); it != ie;
        ++it){
      if(isa<PointerType>(it->getType())){
        u32 vn= next_node++;
        nodes.push_back(new Node(it));
        val_node[it]= vn;
      }
    }
    //Make return and vararg nodes, if needed.
    if(ptr_ret){
      u32 rn= next_node++;
      nodes.push_back(new Node(F));
      ret_node[F]= rn;
    }
    if(is_va){
      u32 va= next_node++;
      nodes.push_back(new Node(F));
      vararg_node[F]= va;
    }
  }else{
    //Map all args to the correct obj nodes
    //  and find where the last ptr arg is.
    //  If there are no ptr args at all, last_ptr will be ~0 rather than 0.
    vector<Value*> args;
    u64 last_ptr= (~(0UL)), i= 0;
    for(Function::arg_iterator it= F->arg_begin(), ie= F->arg_end(); it != ie;
        ++it, ++i){
      Value *V= it;
      args.push_back(V);
      val_node[V]= onF + func_node_off_arg0 + i;
      at_args.insert(V);
      if(isa<PointerType>(V->getType()))
        last_ptr= i;
    }
    //The return node must go right after the first obj node.
    assert(next_node == onF + func_node_off_ret);
    nodes.push_back(new Node(F, 1));
    ++next_node;
    //If the return is non-ptr, point it to i2p, since indirect calls
    //  can load the retval
    //  from a node pointing to both a ptr-ret func. and a non-ptr-ret one.
    //NOTE: this shouldn't really happen in correct programs
    //if(!ptr_ret)
      //add_cons(addr_of_cons, onF + func_node_off_ret, i2p);
    //Make object nodes for all args up to the last ptr;
    //  their values must be the args themselves (not the function).
    assert(next_node == onF + func_node_off_arg0);
    if(last_ptr != ~0UL){
      for(u32 i= 0; i <= last_ptr; ++i){
        nodes.push_back(new Node(args[i], 1));
      }
      next_node += last_ptr+1;
    }
    //Make the vararg node if needed.
    if(is_va){
      nodes.push_back(new Node(F, 1));
      ++next_node;
    }
    //Now we have the complete object of F.
    nodes[onF]->obj_sz= next_node-onF;
    //Note that the args of AT functions are not mapped to value nodes.
  }
}

//------------------------------------------------------------------------------

set<BasicBlock*> bb_seen; // for processBlock()

//Process all instructions in (F).
void Anders::visit_func(Function *F){
  assert(F);
  DPUTS("visit_func  ");
  DEBUG(print_val_now(F));
  DEOL;
  //First make nodes for all ptr-return insn
  //  (since trace_int may sometimes return values below the current insn).
  //Also number all unnamed instructions that have a result.
  u32 next_num= 0;
  for(inst_iterator it= inst_begin(F), ie= inst_end(F); it != ie; ++it){
    Instruction *I= &*it;
    if(isa<PointerType>(I->getType())){
      nodes.push_back(new Node(I));
      val_node[I]= next_node++;
    }
    if(!I->hasName() && I->getType()->getTypeID() != Type::VoidTyID){
      tmp_num[I]= next_num++;
    }
  }

  // process basic blocks in CFG depth-first order (this is not a
  // requirement for this analysis, but it is required by the sparse
  // flow-sensitive pointer analysis using this analysis because (1)
  // it must enforce the same mapping from Value* to value and object
  // nodes as this analysis, and (2) it must process the basic blocks
  // in CFG depth-first order)
  //
  processBlock(&F->getEntryBlock());
  bb_seen.clear();
}

void Anders::processBlock(BasicBlock *BB)
{
  if (bb_seen.count(BB)) { return; }
  bb_seen.insert(BB);

  //Handle each insn based on opcode.
  for(ibb_it it= BB->begin(), ie= BB->end(); it != ie; ++it){
    Instruction *I= &*it;
    INC_STAT(insn);
    bool is_ptr= isa<PointerType>(I->getType());
    switch(I->getOpcode()){
      case Instruction::Ret:
        assert(!is_ptr);
        id_ret_insn(I);
        break;
      case Instruction::Invoke:
      case Instruction::Call:
        id_call_insn(I);
        break;
	//      case Instruction::Malloc:
      case Instruction::Alloca:
        assert(is_ptr);
        id_alloc_insn(I);
        break;
      case Instruction::Load:
        if(is_ptr)
          id_load_insn(I);
        break;
      case Instruction::Store:
        assert(!is_ptr);
        id_store_insn(I);
        break;
      case Instruction::GetElementPtr:
        assert(is_ptr);
        id_gep_insn(I);
        break;
      case Instruction::IntToPtr:
        assert(is_ptr);
        id_i2p_insn(I);
        break;
      case Instruction::BitCast:
        if(is_ptr)
          id_bitcast_insn(I);
        break;
      case Instruction::PHI:
        if(is_ptr)
          id_phi_insn(I);
        break;
      case Instruction::Select:
        if(is_ptr)
          id_select_insn(I);
        break;
      case Instruction::VAArg:
        if(is_ptr)
          id_vaarg_insn(I);
        break;
      case Instruction::ExtractValue:
        if(is_ptr)
          id_extract_insn(I);
        break;
      //No other ops should affect pointer values.
      default:
        assert(!is_ptr && "unknown insn has a pointer return type");
    }
  }

  // now process each of this BasicBlock's successors
  //
  for (succ_iterator i = succ_begin(BB), e = succ_end(BB); i != e; ++i) {
    processBlock(*i);
  }
}

//------------------------------------------------------------------------------
// Instruction handlers
//------------------------------------------------------------------------------

void Anders::id_ret_insn(Instruction *I){
  assert(I);
  ReturnInst *RI= cast<ReturnInst>(I);
  //no val_node for RI

  //ignore void and non-ptr return statements
  if(!RI->getNumOperands())
    return;
  Value *src= RI->getOperand(0);
  if(!isa<PointerType>(src->getType()))
    return;

  Function *F= RI->getParent()->getParent();
  DPUTS("  id_ret_insn  ");
  DEBUG(print_val_now(F));
  DPUTS(" <= ");
  DEBUG(print_val_now(src));
  DEOL;

  u32 rnF= get_ret_node(F), vnS= get_val_node_cptr(src);
  assert(rnF);
  //vnS may be null if src is a null ptr
  if(vnS)
    add_cons(copy_cons, rnF, vnS);
}

//------------------------------------------------------------------------------
//Note: this handles both call and invoke
void Anders::id_call_insn(Instruction *I){
  assert(I);
  CallSite CS(I);                       //this will assert the correct opcode
  u32 vnI= get_val_node(I, 1);
  //val_node may be 0 if the call returns non-ptr.

  DPUTS("  id_call_insn  ");
  DEBUG(print_val_now(I));
  DEOL;

  Value *callee= I->getOperand(0);
  Function *F= dyn_cast<Function>(callee);
  if(!F){
    //Try to recover the original function pointer from a bitcast.
    ConstantExpr *E= dyn_cast<ConstantExpr>(callee);
    if(E && E->getOpcode() == Instruction::BitCast)
      F= dyn_cast<Function>(E->getOperand(0));
  }

  if(vnI)
    id_call_obj(vnI, F);

  if(F){
    if(extinfo->is_ext(F))
      id_ext_call(CS, F);
    else
      id_dir_call(CS, F);
  }else
    //If the callee was not identified as a function (null F), this is indirect.
    id_ind_call(CS);
}

//------------------------------------------------------------------------------
void Anders::id_alloc_insn(Instruction *I){
  assert(I);
  AllocaInst *AI= cast<AllocaInst>(I);
  u32 vnI= get_val_node(AI);

  DPUTS("  id_alloc_insn  ");
  DEBUG(print_val_now(AI));
  DEOL;

  const Type *T= 0;
  //heap-allocated or array => weak
  bool weak= 0;
  //Find out which type of data was allocated.
  //  if(MallocInst *MI= dyn_cast<MallocInst>(AI)){
  //    weak= 1;
  //    T= trace_alloc_type(MI);
  //  }else
     {
    T= AI->getAllocatedType();
    //An array is considered the same as 1 element.
    while(const ArrayType *AT= dyn_cast<ArrayType>(T)){
      weak= 1;
      T= AT->getElementType();
    }
     }

  u32 on= next_node;
  obj_node[AI]= on;
  if(const StructType *ST= dyn_cast<StructType>(T)){
    const vector<u32> &sz= get_struct_sz(ST);
    u32 nf= sz.size();
    //Make nodes for all the fields, with the same obj_sz.
    FORN(i, nf){
      nodes.push_back(new Node(AI, sz[i], weak));
    }
    next_node += nf;
  }else{
    //Non-struct is 1 field.
    nodes.push_back(new Node(AI, 1, weak));
    ++next_node;
  }
  add_cons(addr_of_cons, vnI, on);
}

//------------------------------------------------------------------------------
void Anders::id_load_insn(Instruction *I){
  assert(I);
  LoadInst *LI= cast<LoadInst>(I);
  u32 vnI= get_val_node(LI);

  DPUTS("  id_load_insn  ");
  DEBUG(print_val_now(LI));
  DEOL;

  u32 vnS= get_val_node_cptr(LI->getOperand(0));
  if(!vnS){
    PUTS("!! load from null:  ");
    print_val_now(LI);
    PUTS("  <=  ");
    print_val_now(LI->getOperand(0));
    putc('\n', stderr);
    return;
  }
  add_cons(load_cons, vnI, vnS);
}

//------------------------------------------------------------------------------
void Anders::id_store_insn(Instruction *I){
  assert(I);
  StoreInst *SI= cast<StoreInst>(I);
  //no val_node for SI

  Value *dest= SI->getOperand(1), *src= SI->getOperand(0);
  //ignore stores of non-ptr values
  if(!isa<PointerType>(src->getType()))
    return;

  DPUTS("  id_store_insn  ");
  DEBUG(print_val_now(dest));
  DPUTS("  <=  ");
  DEBUG(print_val_now(src));
  DEOL;

  u32 vnD= get_val_node_cptr(dest), vnS= get_val_node_cptr(src);
  if(vnS && vnD)                        //either may be a null ptr
    add_cons(store_cons, vnD, vnS);
}

//------------------------------------------------------------------------------
void Anders::id_gep_insn(Instruction *I){
  assert(I);
  GetElementPtrInst *GI= cast<GetElementPtrInst>(I);
  u32 vnI= get_val_node(GI);

  DPUTS("  id_gep_insn  ");
  DEBUG(print_val_now(GI));
  DEOL;

  Value *S= GI->getOperand(0);
  if(isa<ConstantPointerNull>(S)){
    if(GI->getNumOperands() == 2)
      id_i2p_insn(GI);
    //A multi-index GEP of null is not a replacement for i2p, and so
    //  the result may be considered null.
    return;
  }
  u32 vnS= get_val_node_cptr(S);
  assert(vnS && "non-null GEP operand has no node");
  u32 off= compute_gep_off(GI);
  add_cons(gep_cons, vnI, vnS, off);
}

//------------------------------------------------------------------------------
//Handle IntToPtr insn. and const.expr, as well as insn/expr
//  in the from (GEP null X), which are equivalent.
void Anders::id_i2p_insn(Value *V){
  assert(V);
  DPUTS("  id_i2p_insn  ");
  DEBUG(print_val_now(V));
  DEOL;
  u32 vnD= 0;
  Value *op= 0;
  if(IntToPtrInst *II= dyn_cast<IntToPtrInst>(V)){
    vnD= get_val_node(II);
    op= II->getOperand(0);
  }else if(GetElementPtrInst *GI= dyn_cast<GetElementPtrInst>(V)){
    assert(isa<ConstantPointerNull>(GI->getOperand(0)) &&
        GI->getNumOperands() == 2 &&
        "only single-index GEP of null is used for i2p");
    vnD= get_val_node(GI);
    op= GI->getOperand(1);
  }else if(ConstantExpr *E= dyn_cast<ConstantExpr>(V)){
    //A const.expr should not have a node yet.
    assert(!val_node.count(E));
    vnD= next_node++;
    nodes.push_back(new Node(E));
    val_node[E]= vnD;
    if(E->getOpcode() == Instruction::IntToPtr){
      op= E->getOperand(0);
    }else if(E->getOpcode() == Instruction::GetElementPtr){
      assert(isa<ConstantPointerNull>(E->getOperand(0)) &&
          E->getNumOperands() == 2 &&
          "only single-index GEP of null is used for i2p");
      op= E->getOperand(1);
    }else
      assert(!"const.expr is not i2p or gep");
  }else
    assert(!"value is not i2p, gep, or const.expr");

  DenseSet<Value*> src;
  DenseMap<Value*, bool> seen;
  bool has_i2p= trace_int(op, src, seen);
  DPUTS("    src:");
  for(DenseSet<Value*>::iterator it= src.begin(), ie= src.end(); it != ie;
      ++it){
    Value *S= *it;
    DPUTS("  ");
    DEBUG(print_val_now(S));
    u32 vnS= get_val_node_cptr(S);
    if(vnS)
      add_cons(copy_cons, vnD, vnS);
  }
  if(has_i2p){
    DPUTS("  <i2p>");
    add_cons(addr_of_cons, vnD, i2p);
  }
  DEOL;
}

//------------------------------------------------------------------------------
void Anders::id_bitcast_insn(Instruction *I){
  assert(I);
  BitCastInst *BI= cast<BitCastInst>(I);
  u32 vnI= get_val_node(BI);

  DPUTS("  id_bitcast_insn  ");
  DEBUG(print_val_now(BI));
  DEOL;

  Value *op= BI->getOperand(0);
  //Bitcast can only convert ptr->ptr or num->num.
  assert(isa<PointerType>(op->getType()));
  u32 vnS= get_val_node_cptr(op);
  if(vnS)                               //src may be a null ptr
    add_cons(copy_cons, vnI, vnS);
}

//------------------------------------------------------------------------------
void Anders::id_phi_insn(Instruction *I){
  assert(I);
  PHINode *PN= cast<PHINode>(I);
  u32 vnI= get_val_node(PN);

  DPUTS("  id_phi_insn  ");
  DEBUG(print_val_now(PN));
  DEOL;

  FORN(i, PN->getNumIncomingValues()){
    u32 vnS= get_val_node_cptr(PN->getIncomingValue(i));
    if(vnS)                             //src may be a null ptr
      add_cons(copy_cons, vnI, vnS);
  }
}

//------------------------------------------------------------------------------
void Anders::id_select_insn(Instruction *I){
  assert(I);
  SelectInst *SI= cast<SelectInst>(I);
  u32 vnI= get_val_node(SI);

  DPUTS("  id_select_insn  ");
  DEBUG(print_val_now(SI));
  DEOL;

  //(select a0 a1 a2) = (a0 ? a1 : a2).
  u32 vnS1= get_val_node_cptr(SI->getOperand(1)), vnS2=
      get_val_node_cptr(SI->getOperand(2));
  //S1/S2 may be null ptr.
  if(vnS1)
    add_cons(copy_cons, vnI, vnS1);
  if(vnS2)
    add_cons(copy_cons, vnI, vnS2);
}

//------------------------------------------------------------------------------
void Anders::id_vaarg_insn(Instruction *I){
  assert(I);
  VAArgInst *VI= cast<VAArgInst>(I);
  u32 vnI= get_val_node(VI);

  DPUTS("  id_vaarg_insn  ");
  DEBUG(print_val_now(VI));
  DEOL;

  Function *F= I->getParent()->getParent();
  u32 vaF= get_vararg_node(F);
  //Anything accessed by va_arg is either one of the varargs
  //  or a normal arg of type va_list.
  assert(vaF && "va_list args not handled yet");
  add_cons(copy_cons, vnI, vaF);
}

//------------------------------------------------------------------------------
void Anders::id_extract_insn(Instruction *I){
  assert(I);
  ExtractValueInst *EI= cast<ExtractValueInst>(I);
  //u32 vnI= get_val_node(EI);

  DPUTS("  id_extract_insn  ");
  DEBUG(print_val_now(EI));
  DEOL;

  assert(!"ExtractValue not handled yet");
}

//------------------------------------------------------------------------------
// Call handlers
//------------------------------------------------------------------------------

//Make the object nodes for the ptr-return call at node vnI;
//  (F) is the called function (may be null).
void Anders::id_call_obj(u32 vnI, Function *F){
  Instruction *I= dyn_cast_or_null<Instruction>(nodes[vnI]->get_val());
  assert(I);
  CallSite CS(I);
  DPUTS("    id_call_obj:  ");

  if(F && extinfo->no_struct_alloc(F)){
    DPUTS("ext/no_struct_alloc\n");
    //1 obj for non-struct-alloc externals (heap alloc => weak).
    u32 on= next_node++;
    obj_node[I]= on;
    nodes.push_back(new Node(I, 1, 1));
    add_cons(addr_of_cons, vnI, on);
  //An indirect call may refer to an is_alloc external.
  //Also, realloc does a normal alloc if arg0 is null.
  }else if(!F || extinfo->is_alloc(F) || (extinfo->get_type(F) == EFT_REALLOC
      && isa<ConstantPointerNull>(CS.getArgument(0)))){
    DPUTS(F ? "ext/alloc\n" : "indirect\n");
    //An ext. alloc call is equivalent to a malloc.
    const Type *T= trace_alloc_type(I);
    u32 on= next_node;
    obj_node[I]= on;

    if(const StructType *ST= dyn_cast<StructType>(T)){
      const vector<u32> &sz= get_struct_sz(ST);
      u32 nf= sz.size();
      FORN(i, nf){
        nodes.push_back(new Node(I, sz[i], 1));
      }
      next_node += nf;
    }else{
      nodes.push_back(new Node(I, 1, 1));
      ++next_node;
    }
    if(F)
      add_cons(addr_of_cons, vnI, on);
    //For indirect calls, the solver will determine
    //  if the above should be added.
  }else if(extinfo->has_static(F)){
    bool stat2= extinfo->has_static2(F);
    DPUTS("ext/static");
    if(stat2)
      DEBUG(putc('2', stderr));
    DEOL;
    string fn= F->getName();
    u32 on= 0;
    map<string, u32>::const_iterator i_srn= stat_ret_node.find(fn);
    if(i_srn != stat_ret_node.end())
      on= i_srn->second;
    else{
      obj_node[I]= on= next_node;
      stat_ret_node[fn]= on;
      //Unknown ext. static vars X,Y where ret -> X -> Y
      if(stat2){
        //stat2 funcs have only non-struct static data.
        nodes.push_back(new Node(I, 2, true));
        nodes.push_back(new Node(I, 1, true));
        next_node += 2;
        add_cons(addr_of_cons, on, on+1);
      }else{                            //ret -> X; X may be a struct
        const Type *T= I->getType()->getContainedType(0);
        if(const StructType *ST= dyn_cast<StructType>(T)){
          const vector<u32> &sz= get_struct_sz(ST);
          u32 nf= sz.size();
          FORN(i, nf){
            nodes.push_back(new Node(I, sz[i], true));
          }
          next_node += nf;
        }else{
          nodes.push_back(new Node(I, 1, true));
          ++next_node;
        }
      }
    }
    add_cons(addr_of_cons, vnI, on);
  //Only alloc/static externals need a call-site object.
  }else
    DEOL;
}

//------------------------------------------------------------------------------
//Add the constraints for a direct, non-external call.
void Anders::id_dir_call(CallSite CS, Function *F){
  assert(F);
  DPUTS("    id_dir_call:  ");
  DEBUG(print_val_now(F));
  DPUTS("  (ret.val ");

  //Only handle the ret.val. if it's used as a ptr.
  if(isa<PointerType>(CS.getType())){
    u32 vnI= get_val_node(CS.getInstruction());
    //Does it actually return a ptr?
    if(isa<PointerType>(F->getReturnType())){
      u32 rnF= get_ret_node(F);
      assert(rnF);
      add_cons(copy_cons, vnI, rnF);
      DPUTS("normal)\n");
    }else{
      //If not, this is an int->ptr cast that we can't trace.
      add_cons(addr_of_cons, vnI, i2p);
      DPUTS("i2p)\n");
    }
  }else
    DPUTS("ignored)\n");

  //Iterators for the actual and formal parameters
  CallSite::arg_iterator itA= CS.arg_begin(), ieA= CS.arg_end();
  Function::arg_iterator itF= F->arg_begin(), ieF= F->arg_end();
  //Go through the fixed parameters.
  DPUTS("      args:");
  for(; itF != ieF; ++itA, ++itF){
    //Some programs (e.g. Linux kernel) leave unneeded parameters empty.
    if(itA == ieA){
      DPUTS(" !! not enough args\n");
      break;
    }
    Value *AA= *itA, *FA= itF;          //current actual/formal arg
    //Non-ptr formal args don't need constraints.
    if(!isa<PointerType>(FA->getType()))
      continue;
    DPUTS("    ");
    DEBUG(print_val_now(FA));
    DPUTS(" <= ");
    DEBUG(print_val_now(AA));
    u32 vnFA= get_val_node(FA);
    if(isa<PointerType>(AA->getType())){
      u32 vnAA= get_val_node_cptr(AA);
      if(vnAA)
        add_cons(copy_cons, vnFA, vnAA);
    }else
      add_cons(addr_of_cons, vnFA, i2p);
  }
  //Any remaining actual args must be varargs.
  if(F->isVarArg()){
    u32 vaF= get_vararg_node(F);
    assert(vaF);
    DPUTS("\n      varargs:");
    for(; itA != ieA; ++itA){
      Value *AA= *itA;
      DPUTS("  ");
      DEBUG(print_val_now(AA));
      if(isa<PointerType>(AA->getType())){
        u32 vnAA= get_val_node_cptr(AA);
        if(vnAA)
          add_cons(copy_cons, vaF, vnAA);
      }else
        add_cons(addr_of_cons, vaF, i2p);
    }
  }else
    assert(itA == ieA && "too many args to non-vararg func.");
  DEOL;
}

//------------------------------------------------------------------------------
//Add the constraints for an indirect call.
void Anders::id_ind_call(CallSite CS){
  DPUTS("    id_ind_call:  ");
  Value *C= CS.getCalledValue();
  assert(C);
  if(isa<InlineAsm>(C)){
    DPUTS("ignoring inline ASM\n");
    return;
  }

  Instruction *I= CS.getInstruction();
  //The callee may be an i2p const.expr.
  u32 vnC= get_val_node_cptr(C);
  assert(vnC && "null callee");
  ind_calls.insert(vnC);

  DPUTS("retval ");
  if(isa<PointerType>(CS.getType())){
    u32 vnI= get_val_node(CS.getInstruction());
    add_cons(load_cons, vnI, vnC, func_node_off_ret);
    //Map the constraint to the insn. that created it.
    icall_cons[Constraint(load_cons, vnI, vnC, func_node_off_ret)].insert(I);
    DPUTS("normal");
  }else
    DPUTS("ignored");

  //Go through the fixed parameters.
  DPUTS("\n      args:");
  //The node offset of the next ptr arg
  u32 arg_off= func_node_off_arg0;
  CallSite::arg_iterator itA= CS.arg_begin(), ieA= CS.arg_end();
  for(; itA != ieA; ++itA, ++arg_off){
    Value *AA= *itA;
    DPUTS("  ");
    DEBUG(print_val_now(AA));
    //FIXME: don't add these cons. if the current formal arg in the
    //  function ptr type is of non-ptr type
    if(isa<PointerType>(AA->getType())){
      u32 vnAA= get_val_node_cptr(AA);
      if(vnAA){
        add_cons(store_cons, vnC, vnAA, arg_off);
        icall_cons[Constraint(store_cons, vnC, vnAA, arg_off)].insert(I);
      }
    }else{
      add_cons(store_cons, vnC, p_i2p, arg_off);
      icall_cons[Constraint(store_cons, vnC, p_i2p, arg_off)].insert(I);
    }
  }
  //TODO: handle varargs (whenever the offset on a store cons. is exceeded,
  //  the solver will need to reset it to the vararg node offset if the current
  //  member of the dest. points_to is a vararg func).
  DEOL;
}

//------------------------------------------------------------------------------
//Add the constraints for the direct call of ext. function F, based on its name.
//If F is unknown, assume it does nothing to pointers.
void Anders::id_ext_call(CallSite CS, Function *F){
  assert(F && extinfo->is_ext(F));
  Instruction *I= CS.getInstruction();
  DPUTS("    id_ext_call:  ");
  DEBUG(print_val_now(F));
  DEOL;

  //The constraints for static/alloc were added by id_call_obj.
  if(extinfo->is_alloc(F) || extinfo->has_static(F))
    return;

  extf_t tF= extinfo->get_type(F);
  switch(tF){
    case EFT_REALLOC:
      //When realloc is passed a non-null pointer, it copies the data
      //  to a new block, so the return will point to a copy of the object
      //  that arg0 pointed to. We can consider it to be the same object,
      //  so the return can just copy arg0's points-to.
      if(isa<ConstantPointerNull>(CS.getArgument(0)))
        break;
    case EFT_L_A0:
    case EFT_L_A1:
    case EFT_L_A2:
    case EFT_L_A8:{
      if(!isa<PointerType>(I->getType()))
        break;
      u32 vnD= get_val_node(I);
      u32 i_arg;
      switch(tF){
        case EFT_L_A1: i_arg= 1; break;
        case EFT_L_A2: i_arg= 2; break;
        case EFT_L_A8: i_arg= 8; break;
        default: i_arg= 0;
      }
      DEBUG(fprintf(stderr, "      L_A%u\n", i_arg));
      Value *src= CS.getArgument(i_arg);
      if(isa<PointerType>(src->getType())){
        u32 vnS= get_val_node_cptr(src);
        if(vnS)
          add_cons(copy_cons, vnD, vnS);
      }else
        add_cons(addr_of_cons, vnD, i2p);
      break;
    }
    case EFT_L_A0__A0R_A1R:{
      DPUTS("      L_A0__A0R_A1R\n");
      add_store2_cons(CS.getArgument(0), CS.getArgument(1));
      //memcpy returns the dest.
      if(isa<PointerType>(I->getType())){
        add_cons(copy_cons, get_val_node(I), get_val_node(CS.getArgument(0)));
      }
      break;
    }
    case EFT_A1R_A0R:
      DPUTS("      A1R_A0R\n");
      add_store2_cons(CS.getArgument(1), CS.getArgument(0));
      break;
    case EFT_A3R_A1R_NS:
      DPUTS("      A3R_A1R_NS\n");
      //These func. are never used to copy structs, so the size is 1.
      add_store2_cons(CS.getArgument(3), CS.getArgument(1), 1);
      break;
    case EFT_A1R_A0:{
      DPUTS("      A1R_A0\n");
      u32 vnD= get_val_node_cptr(CS.getArgument(1));
      u32 vnS= get_val_node_cptr(CS.getArgument(0));
      if(vnD && vnS)
        add_cons(store_cons, vnD, vnS);
      break;
    }
    case EFT_A2R_A1:{
      DPUTS("      A2R_A1\n");
      u32 vnD= get_val_node_cptr(CS.getArgument(2));
      u32 vnS= get_val_node_cptr(CS.getArgument(1));
      if(vnD && vnS)
        add_cons(store_cons, vnD, vnS);
      break;
    }
    case EFT_A4R_A1:{
      DPUTS("      A4R_A1\n");
      u32 vnD= get_val_node_cptr(CS.getArgument(4));
      u32 vnS= get_val_node_cptr(CS.getArgument(1));
      if(vnD && vnS)
        add_cons(store_cons, vnD, vnS);
      break;
    }
    case EFT_L_A0__A2R_A0:{
      DPUTS("      L_A0__A2R_A0\n");
      if(isa<PointerType>(I->getType())){
        //Do the L_A0 part if the retval is used.
        u32 vnD= get_val_node(I);
        Value *src= CS.getArgument(0);
        if(isa<PointerType>(src->getType())){
          u32 vnS= get_val_node_cptr(src);
          if(vnS)
            add_cons(copy_cons, vnD, vnS);
        }else
          add_cons(addr_of_cons, vnD, i2p);
      }
      //Do the A2R_A0 part.
      u32 vnD= get_val_node_cptr(CS.getArgument(2));
      u32 vnS= get_val_node_cptr(CS.getArgument(0));
      if(vnD && vnS)
        add_cons(store_cons, vnD, vnS);
      break;
    }
    case EFT_A0R_NEW:
    case EFT_A1R_NEW:
    case EFT_A2R_NEW:
    case EFT_A4R_NEW:
    case EFT_A11R_NEW:{
      u32 i_arg;
      switch(tF){
        case EFT_A1R_NEW: i_arg= 1; break;
        case EFT_A2R_NEW: i_arg= 2; break;
        case EFT_A4R_NEW: i_arg= 4; break;
        case EFT_A11R_NEW: i_arg= 11; break;
        default: i_arg= 0;
      }
      DEBUG(fprintf(stderr, "      A%uR_NEW\n", i_arg));
      //X -> X/0; *argI = X
      Value *dest= CS.getArgument(i_arg);
      u32 vnD= get_val_node_cptr(dest);
      if(!vnD)
        break;
      const Type *T= dest->getType()->getContainedType(0);
      assert(isa<PointerType>(T) && "arg is not a double pointer");
      T= T->getContainedType(0);
      while(const ArrayType *AT= dyn_cast<ArrayType>(T))
        T= AT->getElementType();

      //make X/0 etc.
      u32 on= next_node;
      obj_node[dest]= on;
      if(const StructType *ST= dyn_cast<StructType>(T)){
        const vector<u32> &sz= get_struct_sz(ST);
        u32 nf= sz.size();
        FORN(i, nf){
          //FIXME: X/0 shouldn't really have a value because it's not
          //  pointed to by any program variable, but for now we require
          //  all obj_nodes to have one.
          nodes.push_back(new Node(dest, sz[i], 1));
        }
        next_node += nf;
      }else{
        nodes.push_back(new Node(dest, 1, 1));
        ++next_node;
      }
      u32 vn= next_node++;
      nodes.push_back(new Node);        //X
      add_cons(addr_of_cons, vn, on);   //X -> X/0
      add_cons(store_cons, vnD, vn);    //*argI = X
      break;
    }
    case EFT_ALLOC:
    case EFT_NOSTRUCT_ALLOC:
    case EFT_STAT:
    case EFT_STAT2:
      assert(!"alloc type func. are not handled here");
    case EFT_NOOP:
    case EFT_OTHER:
      break;
    default:
      assert(!"unknown ext.func type");
  }
}

//Add the load/store constraints and temp. nodes for the complex constraint
//  *D = *S (where D/S may point to structs).
void Anders::add_store2_cons(Value *D, Value *S, u32 sz){
  assert(D && S);
  u32 vnD= get_val_node_cptr(D), vnS= get_val_node_cptr(S);
  if(!vnD || !vnS)
    return;
  //Get the max possible size of the copy, unless it was provided.
  if(!sz)
    sz= min(get_max_offset(D), get_max_offset(S));
  //For each field (i), add (Ti = *S + i) and (*D + i = Ti).
  FORN(i, sz){
    u32 tn= next_node++;
    nodes.push_back(new Node(0));
    add_cons(load_cons, tn, vnS, i);
    add_cons(store_cons, vnD, tn, i);
  }
}

//------------------------------------------------------------------------------
// Global object processing
//------------------------------------------------------------------------------

//Add the nodes & constraints for the declaration of (G).
void Anders::id_global(GlobalVariable *G){
  assert(G);
  //Make a node for the global ptr.
  nodes.push_back(new Node(G));
  DEBUG(fprintf(stderr, "global #%u:  ", next_node));
  DEBUG(print_val_now(G));
  DEOL;
  u32 vnG= next_node++;
  val_node[G]= vnG;

  //The type this global points to
  const Type *T= G->getType()->getContainedType(0);
  bool is_array= 0;
  //An array is considered a single variable of its type.
  while(const ArrayType *AT= dyn_cast<ArrayType>(T)){
    T= AT->getElementType();
    is_array= 1;
  }
  //The first node of the global object (a struct may have more)
  u32 onG= next_node;
  obj_node[G]= onG;

  if(const StructType *ST= dyn_cast<StructType>(T)){
    const vector<u32> &sz= get_struct_sz(ST);
    u32 nf= sz.size();
    //Make nodes for all the fields, with the same obj_sz (array => weak).
    FORN(i, nf)
      nodes.push_back(new Node(G, sz[i], is_array));
    next_node += nf;
    //A struct may be used in constant GEP expr.
    id_gep_ce(G);
  }else{
    //Make 1 obj node, with obj size 1.
    nodes.push_back(new Node(G, 1, is_array));
    ++next_node;
    //An array may be used in constant GEP expr.
    if(is_array)
      id_gep_ce(G);
  }

  add_cons(addr_of_cons, vnG, onG);
}

//------------------------------------------------------------------------------
//Add nodes for any const GEP expressions using the global (G).
void Anders::id_gep_ce(Value *G){
  assert(G);
  //Check all GEP and bitcast ConstantExpr's using G.
  for(Value::use_iterator it= G->use_begin(), ie= G->use_end(); it != ie; ++it){
    ConstantExpr *E= dyn_cast<ConstantExpr>(*it);
    if(!E)
      continue;
    //Recursively check the uses of a bitcast.
    if(E->getOpcode() == Instruction::BitCast)
      id_gep_ce(E);
    else if(E->getOpcode() == Instruction::GetElementPtr){
      DEBUG(fprintf(stderr, "CGEP #%u:  ", next_node));
      DEBUG(print_val_now(E));
      DEOL;
      //A GEP can only use a pointer as its first op.
      assert(E->getOperand(0) == G && "ptr used as index operand");
      //Make a node for this CGEP and record it to init
      //  after other globals are done.
      assert(!val_node.count(E));
      u32 vn= next_node++;
      nodes.push_back(new Node(E));
      val_node[E]= vn;
      gep_ce.push_back(vn);
    }
  }
}

//------------------------------------------------------------------------------
//Add constraints for the global with obj. node (onG) and initializer (C).
//Returns the # of fields processed.
//(first) is used for recursion.
u32 Anders::proc_global_init(u32 onG, Constant *C, bool first){
  assert(onG && C);
  DenseMap<u32, u32>::iterator i_gid= global_init_done.find(onG);
  if(i_gid != global_init_done.end())
    return i_gid->second;

  if(first){
    DPUTS("global_init  ");
    DEBUG(print_node_now(onG));
    DPUTS(" <= ");
    DEBUG(print_val_now(C));
    DEOL;
  }

  //Strip bitcast expr from C, until we get to non-expr value or GEP;
  //  set C=0 in case of int->ptr (which we don't trace for globals)
  //  and exit on a ptr->int (a non-ptr single value).
  bool done= 0;
  for(ConstantExpr *E= dyn_cast<ConstantExpr>(C); E && !done;
      E= dyn_cast_or_null<ConstantExpr>(C)){
    switch(E->getOpcode()){
      case Instruction::BitCast:
        C= E->getOperand(0);
        break;
      case Instruction::GetElementPtr:
        done= 1;
        break;
      case Instruction::IntToPtr:
        C= 0;
        break;
      case Instruction::PtrToInt:
        if(first)
          global_init_done[onG]= 1;
        return 1;
      default:
        assert(!"unexpected constant expr type");
    }
  }

  if(!C){
    add_cons(addr_of_cons, onG, i2p);
    //Don't mark it as done until the top-level call exits.
    if(first){
      DPUTS("  <i2p>\n");
      global_init_done[onG]= 1;
    }
    return 1;
  }
  //No constraint for null/undef init
  if(C->isNullValue() || isa<UndefValue>(C)){
    if(first)
      global_init_done[onG]= 1;
    return 1;
  }

  //single-value init
  if(C->getType()->isSingleValueType()){
    if(isa<PointerType>(C->getType())){
      if(ConstantExpr *E= dyn_cast<ConstantExpr>(C)){
        //The expr. itself may need initialization;
        //  then it can be copied to the global.
        //This may be the first time we reach E.
        u32 vnE= get_val_node(E, 1);
        if(!vnE){
          DEBUG(fprintf(stderr, "CE #%u:  ", next_node));
          DEBUG(print_val_now(E));
          DEOL;
          vnE= next_node++;
          nodes.push_back(new Node(E));
          val_node[E]= vnE;
        }
        proc_gep_ce(vnE);
        add_cons(copy_cons, onG, vnE);
      }else{
        //This must be a global ptr initialized above the current one.
        u32 onC= get_obj_node(C);
        add_cons(addr_of_cons, onG, onC);
      }
    }
    if(first)
      global_init_done[onG]= 1;
    return 1;
  }

  u32 off= 0;
  if(ConstantStruct *CS= dyn_cast<ConstantStruct>(C)){
    //Recursively copy each field of the original struct into the next available
    //  field of the expanded struct. Note that the fields of a constant struct
    //  are accessed by getOperand().
    FORN(i, CS->getNumOperands())
      off += proc_global_init(onG+off, CS->getOperand(i), 0);
  }else if(ConstantArray *CA= dyn_cast<ConstantArray>(C)){
    //Copy each array element into the same node.
    //The offset returned (the field count of 1 el.)
    //  will be the same every time.
    FORN(i, CA->getNumOperands())
      off= proc_global_init(onG, CA->getOperand(i), 0);
  }else
    assert(!"unexpected non-1st-class constant");

  if(first)
    global_init_done[onG]= off;
  return off;
}

//------------------------------------------------------------------------------
//Add constraints for the GEP CE at node vnE.
void Anders::proc_gep_ce(u32 vnE){
  ConstantExpr *E= dyn_cast_or_null<ConstantExpr>(nodes[vnE]->get_val());
  assert(E);
  assert(E->getOpcode() == Instruction::GetElementPtr);
  if(global_init_done.count(vnE))
    return;
  global_init_done[vnE]= 1;

  Value *R= E->getOperand(0);
  //Strip bitcasts from the RHS, until we get to GEP, i2p, or non-CE value.
  bool nested= 0;
  for(ConstantExpr *ER= dyn_cast<ConstantExpr>(R); ER && !nested;
      ER= dyn_cast_or_null<ConstantExpr>(R)){
    switch(ER->getOpcode()){
      case Instruction::BitCast:
        R= ER->getOperand(0);
        break;
      case Instruction::IntToPtr:
        add_cons(addr_of_cons, vnE, i2p);
        return;
      case Instruction::GetElementPtr:
        //We can have (gep (bitcast (gep X 1)) 1); the inner gep
        //  must be handled recursively.
        nested= 1;
        break;
      default:
        assert(!"unexpected constant expr type");
    }
  }
  assert(!isa<ConstantPointerNull>(R) &&
      "GEP of null not supported for global init");
  DPUTS("  CGEP  ");
  DEBUG(print_val_now(E));
  DEOL;

  //This may be the first time we reach R.
  u32 vnR= get_val_node(R, 1);
  if(!vnR){
    DEBUG(fprintf(stderr, "CE #%u:  ", next_node));
    DEBUG(print_val_now(R));
    DEOL;
    vnR= next_node++;
    nodes.push_back(new Node(R));
    val_node[R]= vnR;
  }
  u32 off= compute_gep_off(E);

  //For E = (gep R off), the constraint is (gep E R off).
  add_cons(gep_cons, vnE, vnR, off);
  if(nested){
    proc_gep_ce(vnR);
  }else if(GlobalVariable *RG= dyn_cast<GlobalVariable>(R)){
    //R itself may need global_init if it's a global var.
    if(RG->hasInitializer()){
      proc_global_init(get_obj_node(R), RG->getInitializer());
    }else{
      DPUTS("!! uninitialized global in CGEP\n");
    }
  }
}

//------------------------------------------------------------------------------
// Other analysis
//------------------------------------------------------------------------------

//Fill in struct_info for T.
//This should only be called by get_struct_info().
void Anders::_analyze_struct(const StructType *T){
  assert(T);
  if(struct_info.count(T))
    return;
  DPUTS("  analyze_struct  ");
  DPUTS(get_type_name(T));
  DEOL;
  vector<u32> sz, off;
  //How many fields have been placed in the expanded struct
  u32 nf= 0;

  for(StructType::element_iterator it= T->element_begin(), ie= T->element_end();
      it != ie; ++it){
    const Type *ET= *it;
    //Treat an array field as a single element of its type.
    while(const ArrayType *AT= dyn_cast<ArrayType>(ET))
      ET= AT->getElementType();
    //The offset is where this element will be placed in the exp. struct.
    off.push_back(nf);
    //Process a nested struct.
    if(const StructType *ST= dyn_cast<StructType>(ET)){
      const vector<u32> &szE= get_struct_sz(ST);
      u32 nfE= szE.size();
      //Copy ST's info, whose element 0 is the size of ST itself.
      FORN(j, nfE){
        sz.push_back(szE[j]);
      }
      nf += nfE;
    }else{                              //simple type
      sz.push_back(1);
      ++nf;
    }
  }
  //Record the size of the complete struct and update max_struct.
  sz[0]= nf;
  if(nf > max_struct_sz){
    max_struct= T;
    max_struct_sz= nf;
  }
  struct_info[T]= make_pair(sz, off);
}

//------------------------------------------------------------------------------
//Return the object-node offset corresponding to GEP insn (V).
u32 Anders::compute_gep_off(User *V){
  assert(V);
  DPUTS("    (gep  ");
  DEBUG(print_val_now(V->getOperand(0)));
  u32 off= 0;
  for(gep_type_iterator gi= gep_type_begin(*V), ge= gep_type_end(*V);
      gi != ge; ++gi){
    //The int-value object of the current index operand
    //  (may not be constant for arrays).
    ConstantInt *op= dyn_cast<ConstantInt>(gi.getOperand());
    //The actual index
    u32 idx= op ? op->getZExtValue() : 0;
    const StructType *ST= gi.getStructTypeOrNull();
    //Skip non-struct (i.e. array) offsets
    if(!ST)
      continue;
    assert(op && "non-const struct index in GEP");
    DEBUG(fprintf(stderr, "  %s[%u]", get_type_name(ST), idx));
    const vector<u32> &so= get_struct_off(ST);
    if(idx >= so.size()){
      putc('\n', stderr);
      print_struct_info(ST);
      fprintf(stderr, "!! Struct index out of bounds: %d\n", idx);
      assert(0);
    }
    //add the translated offset
    off += so[idx];
  }
  DPUTS(")\n");
  return off;
}

//------------------------------------------------------------------------------
//Find the largest type that this allocation may be cast to.
//This handles both AllocaInst's and allocating calls.
const Type* Anders::trace_alloc_type(Instruction *I){
  assert(I);
  //The largest type seen so far
  const Type *MT= I->getType()->getContainedType(0);
  u32 msz= 0;                           //the size of MT (0 for non-struct)
  bool found= 0;                        //if any casts were found

  while(const ArrayType *AT= dyn_cast<ArrayType>(MT))
    MT= AT->getElementType();
  if(const StructType *ST= dyn_cast<StructType>(MT))
    msz= get_struct_sz(ST).size();

  for(Value::use_iterator it= I->use_begin(), ie= I->use_end(); it != ie; ++it){
    CastInst *CI= dyn_cast<CastInst>(*it);
    //Only check casts to other ptr types.
    if(!CI || !isa<PointerType>(CI->getType()))
      continue;
    found= 1;
    //The type we're currently casting to and its size
    const Type *T= CI->getType()->getContainedType(0);
    u32 sz= 0;
    while(const ArrayType *AT= dyn_cast<ArrayType>(T))
      T= AT->getElementType();
    if(const StructType *ST= dyn_cast<StructType>(T))
      sz= get_struct_sz(ST).size();
    if(sz > msz)
      msz= sz, MT= T;
  }

  //If the allocation is of non-struct type and we can't find any casts,
  //  assume that it may be cast to the largest struct later on.
  if(!found && !msz)
    return max_struct;
  return MT;
}

//------------------------------------------------------------------------------
//Find the max possible offset for an object pointed to by (V).
u32 Anders::get_max_offset(Value *V){
  assert(V);
  DPUTS("        get_max_offset  ");
  DEBUG(print_val_now(V));
  DEOL;
  const Type *T= V->getType();
  //  assert(isa<PointerType>(T) && T->getContainedType(0) == Type::getInt8Ty(llvm::getGlobalContext()));
  //If V is a CE or bitcast, the actual pointer type is its operand.
  if(ConstantExpr *E= dyn_cast<ConstantExpr>(V))
    T= E->getOperand(0)->getType();
  else if(BitCastInst *BI= dyn_cast<BitCastInst>(V))
    T= BI->getOperand(0)->getType();
  //For other values, use the biggest struct type out of all operands.
  else if(User *U= dyn_cast<User>(V)){
    DPUTS("          ops:");
    u32 msz= 1;                         //the max size seen so far
    for(User::op_iterator it= U->op_begin(), ie= U->op_end(); it != ie; ++it){
      Value *V= it->get();
      DPUTS("  ");
      DEBUG(print_val_now(V));
      T= V->getType();
      if(!isa<PointerType>(T))
        continue;
      T= T->getContainedType(0);
      while(const ArrayType *AT= dyn_cast<ArrayType>(T))
        T= AT->getElementType();
      if(const StructType *ST= dyn_cast<StructType>(T)){
        u32 sz= get_struct_sz(ST).size();
        if(msz < sz)
          msz= sz;
      }
    }
    DEOL;
    return msz;
  }else                                 //V has no operands
    return 1;

  if(!isa<PointerType>(T))
    return 1;
  T= T->getContainedType(0);
  while(const ArrayType *AT= dyn_cast<ArrayType>(T))
    T= AT->getElementType();
  if(const StructType *ST= dyn_cast<StructType>(T))
    return get_struct_sz(ST).size();
  return 1;
}

//------------------------------------------------------------------------------
//Returns the value node of V, with special handling of const pointers.
u32 Anders::get_val_node_cptr(Value *V){
  assert(V);
  u32 vn= get_val_node(V, 1);
  //The value-node map takes priority over the general const.ptr. handling.
  if(vn)
    return vn;

  Constant *C= dyn_cast<Constant>(V);
  assert(C && isa<PointerType>(C->getType()) &&
    "value w/o node is not a const ptr");
  assert(!isa<GlobalValue>(C) && "global const.ptr has no node");

  //We don't need constraints for null/undef.
  if(isa<ConstantPointerNull>(C) || isa<UndefValue>(C))
    return 0;

  ConstantExpr *E= dyn_cast<ConstantExpr>(C);
  assert(E && "unknown const.ptr type");

  switch(E->getOpcode()){
    case Instruction::BitCast:
      return get_val_node_cptr(E->getOperand(0));
    case Instruction::IntToPtr:
      id_i2p_insn(E);
      return get_val_node(E);
    case Instruction::GetElementPtr:
      if(isa<ConstantPointerNull>(E->getOperand(0))){
        if(E->getNumOperands() > 2)
          return 0;
        id_i2p_insn(E);
        return get_val_node(E);
      }
      assert(!"unexpected GEP CE");
    default:
      assert(!"unknown opcode in const.ptr expr");
  }
  return 0;
}

//------------------------------------------------------------------------------
//Check if the address of (V) is ever taken. This can happen if:
//- V is an arg of some function call
//- V is used by an insn. other than compare
//- V is part of a const.expr whose addr. is taken.
bool Anders::escapes(Value *V) const{
  assert(V);
  for(Value::use_iterator it= V->use_begin(), ie= V->use_end(); it != ie; ++it){
    if(CallInst *I= dyn_cast<CallInst>(*it)){
      for(u32 k= 1, ke= I->getNumOperands(); k < ke; ++k)
        if(I->getOperand(k) == V)
          return 1;
    }else if(InvokeInst *I= dyn_cast<InvokeInst>(*it)){
      for(u32 k= 3, ke= I->getNumOperands(); k < ke; ++k)
        if(I->getOperand(k) == V)
          return 1;
    }else if(ConstantExpr *E= dyn_cast<ConstantExpr>(*it)){
      if(escapes(E))
        return 1;
    }else if(!isa<CmpInst>(*it))
      return 1;
  }
  return 0;
}

//------------------------------------------------------------------------------
//Find the possible pointer sources of the int value (V), storing them in (src).
//Returns true if some path can't be traced to a ptr (and so the i2p cons.
//  should be added).
//(seen) maps the values visited by the current trace to the return value.
//Pass empty sets for both (src) and (seen) when calling from the outside.
//(depth) is the current recursion level; do not set from the outside.
bool Anders::trace_int(Value *V, DenseSet<Value*> &src,
    DenseMap<Value*, bool> &seen, u32 depth){
  DenseMap<Value*, bool>::iterator i_seen= seen.find(V);
  if(i_seen != seen.end())
    return i_seen->second;
  DEBUG(fprintf(stderr, "    trace_int[%u]  ", depth));
  DEBUG(print_val_now(V));
  DPUTS("\n      ");
  const Type *TL= V->getType();
  assert(V && isa<IntegerType>(TL) &&
      "trying to trace non-int value");
  seen[V]= 0;

  //Opcode/operands of V (which is either insn or const.expr)
  u32 opcode= 0;
  vector<Value*> ops;

  //Arguments and numbers provide unknown addresses.
  if(isa<Argument>(V) || isa<ConstantInt>(V)){
    DPUTS("<i2p>\n");
    seen[V]= 1;
    return 1;
  }else if(ConstantExpr *CE= dyn_cast<ConstantExpr>(V)){
    DPUTS("CE");
    opcode= CE->getOpcode();
    FORN(i, CE->getNumOperands())
      ops.push_back(CE->getOperand(i));
  }else if(Instruction *I= dyn_cast<Instruction>(V)){
    DPUTS("insn");
    opcode= I->getOpcode();
    FORN(i, I->getNumOperands())
      ops.push_back(I->getOperand(i));
  }else
    assert(!"unknown type of int value");

  assert(opcode);
  DPUTS("  (");
  DPUTS(Instruction::getOpcodeName(opcode));
  FORN(i, ops.size()){
    DPUTS("  ");
    DEBUG(print_val_now(ops[i]));
  }
  DPUTS(")\n");

  bool r= 0;
  switch(opcode){
    //These return untraceable int values.
    case Instruction::Invoke:
    case Instruction::FPToUI:
    case Instruction::FPToSI:
    case Instruction::ICmp:
    case Instruction::FCmp:
    case Instruction::Call:
    case Instruction::VAArg:
    case Instruction::ExtractElement:
      DPUTS("      <i2p>\n");
      seen[V]= 1;
      return 1;
    //This is the only direct way to get a ptr source.
    case Instruction::PtrToInt:
      src.insert(ops[0]);
      return 0;
    case Instruction::Load:{
      //Loading from a global constant gives its initializer.
      if(GlobalVariable *G= dyn_cast<GlobalVariable>(ops[0])){
        if(G->hasInitializer() && G->isConstant()){
          Value *GI= G->getInitializer();
          DPUTS("      global const  ");
          DEBUG(print_val_now(GI));
          DEOL;
          r= trace_int(GI, src, seen, depth+1);
          if(r)
            seen[V]= 1;
          return r;
        }
      }
      //Try to find what was last stored here, within the same basic block.
      DPUTS("      last store  ");
      LoadInst *LI0= cast<LoadInst>(V);
      Value *addr= ops[0];
      Value *S= 0;
      //Whether the BB iterator reached the current insn.
      bool found= 0;
      BasicBlock *bb= LI0->getParent();
      for(BasicBlock::iterator it= bb->begin(), ie= bb->end();
          !found && it != ie; ++it){
        if(StoreInst *SI= dyn_cast<StoreInst>(it)){
          if(SI->getPointerOperand() == addr)
            S= SI->getOperand(0);
        }else if(LoadInst *LI= dyn_cast<LoadInst>(it))
          found= LI == LI0;
      }
      assert(found);
      if(S){
        DEBUG(print_val_now(S));
        DEOL;
        r= trace_int(S, src, seen, depth+1);
        if(r)
          seen[V]= 1;
        return r;
      }
      DPUTS("<??\?>\n");
      seen[V]= 1;
      return 1;
    }
    //For 1-addr arithmetic or casts, trace the addr operand.
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
    case Instruction::Trunc:
    case Instruction::ZExt:
    case Instruction::SExt:
    case Instruction::BitCast:{
      const Type *TR= ops[0]->getType();
      DEBUG(fprintf(stderr, "  (cast %s -> %s)\n",
          TR->getDescription().c_str(), TL->getDescription().c_str()));
      if(isa<IntegerType>(TR)){
        r= trace_int(ops[0], src, seen, depth+1);
        if(r)
          seen[V]= 1;
        return r;
      }else{
        assert(opcode == Instruction::BitCast &&
            "invalid operand for int insn");
        Type::TypeID t= TR->getTypeID();
        assert(t == Type::FloatTyID || t == Type::DoubleTyID &&
            "invalid cast to int");
        seen[V]= 1;
        return 1;
      }
    }
    //Arithmetic with possibly 2 addr: trace both; add i2p only if both
    //  return i2p (if only 1 has i2p, assume it's an offset for the addr).
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::Mul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
      r= trace_int(ops[0], src, seen, depth+1) &
          trace_int(ops[1], src, seen, depth+1);
      if(r)
        seen[V]= 1;
      return r;
    //Trace all ops into the same set (if any op has i2p,
    //  the result can point to i2p too).
    case Instruction::PHI:
      r= 0;
      FORN(i, ops.size()){
        //Sometimes a pointer or other value can come into an int-type phi node.
        const Type *T= ops[i]->getType();
        if(isa<IntegerType>(T))
          r |= trace_int(ops[i], src, seen, depth+1);
        else if(isa<PointerType>(T))
          src.insert(ops[i]);
        else
          r= 1;
      }
      if(r)
        seen[V]= 1;
      return r;
    case Instruction::Select:
      r= trace_int(ops[0], src, seen, depth+1) |
          trace_int(ops[1], src, seen, depth+1);
      if(r)
        seen[V]= 1;
      return r;
    default:
      assert(!"this insn should not produce an int value");
  }
  assert(!"should not get here");
  return 0;
}
