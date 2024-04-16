//===-- HelloWorld.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/HelloWorld.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/IRBuilder.h"
#include <string>
#include <map>
#include <vector>
#include <typeinfo>

using namespace llvm;

//--ValueName Table---------------------------------------//
int VN = 1;
std::map<Value*, int> valueName;

int LOAD_OPCODE = 32;
int STORE_OPCODE = 33;

int addValueName(Value* val){
  if (valueName.find(val) != valueName.end()){
    return valueName[val];
  }
  valueName[val] = VN;
  VN++;
  return valueName[val];
}

int getValueName(Value* val){
  return valueName[val];
}
//-------------------------------------------------------//

//--Name Table-------------------------------------------//
struct aValue {
    Value* val;
    bool isConstant;
    APInt constantVal;
};

std::map<int ,aValue*> nameTable;

void addName (Value* val, APInt constant)
{   
    int value_number =  getValueName(val);
    if (nameTable.find(value_number) != nameTable.end())
    {
      delete (nameTable[value_number]);
    }
    nameTable[value_number] = new aValue {val, true, constant};
}

void addName (Value* val)
{   
  int value_number =  getValueName(val);
  if (nameTable.find(value_number) != nameTable.end())
  {
    delete (nameTable[value_number]);
  }
  nameTable[value_number] = new aValue {val, false, APInt(32, 0)};
}
//-------------------------------------------------//

//--Hash-Table-------------------------------------//

std::map<std::tuple<int, Value * , Value *>, Value *> expMap;

void addExpMap (Value * dest, int opcode , Value* op1, Value* op2 = NULL)
{
  if (op2 != NULL)
  {
    if (op1 < op2)
      expMap[{opcode,op1,op2}] = dest;
    else 
      expMap[{opcode,op2,op1}] = dest;
  }
  else
  {
    expMap[{opcode,op1,op2}] = dest;
  }
}

bool isExpPresent (int opcode, Value* op1, Value* op2 = NULL)
{
  if ( op2 != NULL)
  {
    if (op1 < op2)
      return expMap.find({opcode,op1,op2}) != expMap.end();
    else 
      return expMap.find({opcode,op2,op1}) != expMap.end();
  }
  else
  {
    return expMap.find({opcode,op1,op2}) != expMap.end();
  }
}

Value * getExpMap (int opcode, Value* op1, Value* op2 = NULL)
{
  if (op2 != NULL)
  {
    if (op1 < op2)
      return expMap[{opcode,op1,op2}];
    else 
      return expMap[{opcode,op2,op1}];
  }
  else
  {
    return expMap[{opcode,op1,op2}];
  }
}

void printExpTable ()
{
  errs() << "------------------------------------------------\n";
  errs() << "Exp Table\n";
  errs() << "Dest     <= Exp \n";
  for (auto it = expMap.begin(); it != expMap.end(); ++it){
    errs() << it->second << " <= " << get<0>(it->first) << ","<< get<1>(it->first) << "," << get<2>(it->first) << "\n";
  } 
}

//-------------------------------------------------//

//------function-to-extract-constant-from-use------//

bool isUseConst (Value * ptr){
  if (isa<ConstantInt>(*ptr)){
    return true;
  }
  if (valueName.find(ptr) != valueName.end())
  {
    int value_number = valueName[ptr];
    if (nameTable.find(value_number) != nameTable.end())
      return nameTable[value_number]->isConstant;
  }
  return false;
}

// should only be used after checking isUseConst
APInt getConstFromUse(Value* ptr){

  if (isa<ConstantInt>(*ptr)){
    return dyn_cast<ConstantInt>(ptr)->getValue();
  }

  return nameTable[valueName[ptr]]->constantVal;
}

//-------------------------------------------------//

// checks if a value is ever used in the block
bool isValueUnused(Value *V) {
    // Check if the value has any users
    return V->user_empty();
}

// checks if the value is used in a load statement
bool isValueUsedtoLoad(Value *Op) {
  
  // Iterate over the users of the operand
  for (User *U : Op->users()) {
    if (LoadInst *LI = dyn_cast<LoadInst>(U)) {
      if(LI->getOperand(0) == Op){  
        return true;
      }
    }
  }
  return false;
}

bool isValueUsedtoLoadLater (BasicBlock::iterator I, BasicBlock::iterator end)
{
  auto* ptr = dyn_cast<User>(I);
  auto* src = ptr->getOperand(1);
  for (auto it = ++I; it != end; ++it){
    if (isa<LoadInst>(it)){
      LoadInst *LI = dyn_cast<LoadInst>(it);
      auto* op1 = LI->getOperand(0);
      if (op1 == src){
        return true;
      }
    }
  }
  return false;
}


bool IsInstructionDead (BasicBlock::iterator I, BasicBlock::iterator end)
{
  if (I->getOpcode() == Instruction::Ret || I->getOpcode() == Instruction::Call)
  {
    return false;
  }
  else if (isa<StoreInst>(I))
  { 
    return !isValueUsedtoLoadLater(I,end);
  }
  else
  {
    auto * val = dyn_cast<Value>(I);
    return isValueUnused(val);
  }
  return false;
}     

void replaceAllUses (Value * operand, APInt newAPIntValue)
{
  Value *newOperand = ConstantInt::get(operand->getType(), newAPIntValue);

  for (User *U : operand->users()) {
    Instruction *userInst = cast<Instruction>(U);
    userInst->replaceUsesOfWith(operand, newOperand);
  }
}
void replaceAllUses (Value * operand, Value * newOperand)
{
  for (User *U : operand->users()) {
    Instruction *userInst = cast<Instruction>(U);
    userInst->replaceUsesOfWith(operand, newOperand);
  }
}

void performArithmeticOpt (BasicBlock::iterator I)
{
  auto* ptr = dyn_cast<User>(I);
  auto* val = dyn_cast<Value>(I);
  addValueName(val);
  
  auto* op1 = ptr->getOperand(0);
  auto* op2 = ptr->getOperand(1);
  
  if (isUseConst(op1) && isUseConst(op2)){
    switch (I->getOpcode())
    {
      case Instruction::Add:
        addName(val, getConstFromUse(op1) + getConstFromUse(op2));
        replaceAllUses(val,getConstFromUse(op1) + getConstFromUse(op2));
        break;
      case Instruction::Sub:
        addName(val, getConstFromUse(op1) - getConstFromUse(op2));
        replaceAllUses(val,getConstFromUse(op1) - getConstFromUse(op2));
        break;
      case Instruction::Mul:
        addName(val, getConstFromUse(op1) * getConstFromUse(op2));
        replaceAllUses(val,getConstFromUse(op1) * getConstFromUse(op2));
        break;
      case Instruction::UDiv:
        addName(val, getConstFromUse(op1).udiv(getConstFromUse(op2)));
        replaceAllUses(val,getConstFromUse(op1).udiv(getConstFromUse(op2)));
        break;
      case Instruction::SDiv:
        addName(val, getConstFromUse(op1).sdiv(getConstFromUse(op2)));
        replaceAllUses(val,getConstFromUse(op1).udiv(getConstFromUse(op2)));
        break;
      default:  
        break;
    }
  }
  else if (isUseConst(op1))
  {
    if (getConstFromUse(op1) == 0){
      if (I->getOpcode() == Instruction::Add)
      {
        replaceAllUses(val, op2);
      }
      else if (I->getOpcode() == Instruction::SDiv || I->getOpcode() == Instruction::UDiv || I->getOpcode() == Instruction::Mul)
      {
        addName(val, APInt(32, 0));
        replaceAllUses(val, APInt(32, 0));
      }
    }
    else if (getConstFromUse(op1) == 1)
    {
      if (I->getOpcode() == Instruction::Mul)
      {
        replaceAllUses(val, op2);
      }
    }
    else if (getConstFromUse(op1).isPowerOf2())
    {
      uint64_t ShiftAmount = getConstFromUse(op1).exactLogBase2();
      IRBuilder<> Builder(&*I);

      if (I->getOpcode() == Instruction::Mul)
      {
        Value *NewShlInst = Builder.CreateShl(op2, ConstantInt::get(op2->getType(), ShiftAmount));
        
        I->replaceAllUsesWith(NewShlInst);
      }
      else if (I->getOpcode() == Instruction::UDiv || I->getOpcode() == Instruction::SDiv)
      {
        Value *NewAShrInst = Builder.CreateAShr(op2, ConstantInt::get(op2->getType(), ShiftAmount));
        
        I->replaceAllUsesWith(NewAShrInst);
      }
    }
  }
  else if (isUseConst(op2))
  {
    if (getConstFromUse(op2) == 0){
      if (I->getOpcode() == Instruction::Add)
      {
        replaceAllUses(val, op1);
      }
      else if (I->getOpcode() == Instruction::SDiv || I->getOpcode() == Instruction::UDiv || I->getOpcode() == Instruction::Mul)
      {
        addName(val, APInt(32, 0));
        replaceAllUses(val, APInt(32, 0));
      }
    }
    else if (getConstFromUse(op2) == 1)
    {
      if (I->getOpcode() == Instruction::SDiv || I->getOpcode() == Instruction::UDiv || I->getOpcode() == Instruction::Mul)
      {
        replaceAllUses(val, op1);
      }
    }
    else if (getConstFromUse(op2).isPowerOf2())
    {
      uint64_t ShiftAmount = getConstFromUse(op2).exactLogBase2();
      IRBuilder<> Builder(&*I);
      
      if (I->getOpcode() == Instruction::Mul)
      {
        Value *NewShlInst = Builder.CreateShl(op1, ConstantInt::get(op1->getType(), ShiftAmount));
        
        I->replaceAllUsesWith(NewShlInst);
      }
      else if (I->getOpcode() == Instruction::UDiv || I->getOpcode() == Instruction::SDiv)
      {
        Value *NewAShrInst = Builder.CreateAShr(op1, ConstantInt::get(op1->getType(), ShiftAmount));
        
        I->replaceAllUsesWith(NewAShrInst);
      }
    }
  }
  else 
  {
    if(I->getOpcode() == Instruction::Sub){
      if (op1 == op2){
        addName(val, APInt(32, 0));
        replaceAllUses(val, APInt(32, 0));
      }
    }
    else if (I->getOpcode() == Instruction::SDiv || I->getOpcode() == Instruction::UDiv){
      if (op2 == op1){
        addName(val, APInt(32, 1));
        replaceAllUses(val, APInt(32, 1));
      }
    }
  }
}

void printNameTable(){
  errs() << "------------------------------------------------\n";
  errs() << "Name Table\n";
  errs() << "Val     => Const\n";
  for (auto it = nameTable.begin(); it != nameTable.end(); ++it){
    errs() << it->first << " => " << it->second << "\n";
  }
}

void printValueName(){
  errs() << "------------------------------------------------\n";
  errs() << "ValueName Table\n";
  errs() << "Val     => Name \n";
  for (auto it = valueName.begin(); it != valueName.end(); ++it){
    errs() << it->first << " => " << it->second << "\n";
  }
}

void printOperand (Value * ptr)
{
  if (isa<ConstantInt>(ptr))
  {
    errs() << dyn_cast<ConstantInt>(ptr)->getValue() <<": " <<ptr;
  }
  else 
  {
    errs() <<ptr;
  }
}

void printInstruction (BasicBlock::iterator I, bool clean = false)
{
  errs() << *I << "\n  ";
  if(!clean)
  {
    errs() <<"[op_c = "<< I->getNumOperands()<<"] ";
    if(isa<StoreInst>(I))
    {
      auto* ptr = dyn_cast<User>(I);
      
      errs() << "[op1 = ";
      printOperand( ptr->getOperand(0));
      errs() << "] ";
      errs() << "[dest = " << ptr->getOperand(1) << "] ";
    }
    else if (isa<LoadInst>(I))
    {
      auto* val = dyn_cast<Value>(I);
      auto* ptr = dyn_cast<User>(I);
      
      errs() << "[dest = " << val << "] ";
      errs() << "[op1 = ";
      printOperand( ptr->getOperand(0));
      errs() << "] ";
    }
    else if (I->isBinaryOp())
    {

      if (I->getOpcode() == Instruction::Add){
        errs() << "[+] ";
      }
      if (I->getOpcode() == Instruction::Sub){
        errs() << "[-] ";
      }
      if (I->getOpcode() == Instruction::Mul){
        errs() << "[*] ";
      }
      if (I->getOpcode() == Instruction::UDiv || I->getOpcode() == Instruction::SDiv){
        errs() << "[/] ";
      }
      auto* val = dyn_cast<Value>(I);
      auto* ptr = dyn_cast<User>(I);

      errs() << "[dest = " << val << "] ";
      errs() << "[op1 = ";
      printOperand( ptr->getOperand(0));
      errs() << "] ";

      errs() << "[op2 = ";
      printOperand( ptr->getOperand(1));
      errs() << "] ";
    }
  }
  errs () << "\n";
}

void eliminateDeadCode(Function &F)
{
  bool changed = false;
  do {
    changed = false;
    for(Function::iterator bb=F.begin();bb!=F.end(); bb++)
    {
      std::vector <BasicBlock::iterator> toRemove;
      for(BasicBlock::iterator I=bb->begin(); I!=bb->end();I++){
        
        if(IsInstructionDead(I,bb->end()))
        {
          toRemove.push_back(I);
        }
        else
        {
          // errs () << *I << " is not dead\n";
        }
      }
      for (auto it = toRemove.begin(); it != toRemove.end(); ++it){
        (*it)->eraseFromParent();
        changed = true;
      }
    }
  } while (changed);
}

PreservedAnalyses HelloWorldPass::run(Function &F, FunctionAnalysisManager &AM) {

  for(Function::iterator bb=F.begin();bb!=F.end(); bb++)
  {
    // errs()<< "BasicBlock name = " << bb->getName()<<"\n";
    // errs() << "BasicBlok size = " << bb->size()<<"\n";
      
    for(BasicBlock::iterator I=bb->begin(); I!=bb->end();I++){
      // printInstruction(I,true);
      // errs() <<"\n";
      if (isa<AllocaInst>(I)) {
        auto* val = dyn_cast<Value>(I);  
        addValueName(val);
        addName (val);
        continue;
      }
      // Store Instruction
      else if (isa<StoreInst>(I))
      {
        auto* ptr = dyn_cast<User>(I);
         
        auto * op1 = ptr->getOperand(0);   // source
        auto * op2 = ptr->getOperand(1);   // destination
        addValueName(op2);  
        addExpMap(op1,LOAD_OPCODE,op2);
        
        if (isUseConst(op1)){
          addName(ptr->getOperand(1), getConstFromUse(op1));
          replaceAllUses(op1,getConstFromUse(op1));
        }
      }
      // Load Instruction
      else if (isa<LoadInst>(I))
      {
        auto* val = dyn_cast<Value>(I);               //destination
        addValueName(val);
        auto* op1 = dyn_cast<User>(I)->getOperand(0); //source
        if ( isExpPresent(LOAD_OPCODE,op1) )
        {
          replaceAllUses(val, getExpMap(LOAD_OPCODE,op1));
        }
        else 
        {
          addExpMap(val,LOAD_OPCODE,op1);
        }
        // if(isUseConst(op1)){

        //   addName(val, getConstFromUse(op1));
        //   replaceAllUses(val,getConstFromUse(op1));

        // }
      }
      // Arith Instruction
      else if (I->isBinaryOp() )
      {
        auto* ptr = dyn_cast<User>(I);
        auto* val = dyn_cast<Value>(I);    // destination
        auto * op1 = ptr->getOperand(0);   // op1
        auto * op2 = ptr->getOperand(1);   // op2

        if (isExpPresent(I->getOpcode(),op1,op2))
        {
          replaceAllUses(val, getExpMap(I->getOpcode(),op1,op2));
        }
        else{
          addExpMap(val,I->getOpcode(),op1,op2);
          performArithmeticOpt(I);
        }
      }
      else if (isa<ReturnInst>(I))
      {
        auto* ptr = dyn_cast<User>(I);
        auto* val = ptr->getOperand(0);
        if (isUseConst(val)){
          replaceAllUses(val,getConstFromUse(val));
        }
      }
    }
    errs()<<"\n";
  }
  errs() << F.getName() << "\n";
  // printNameTable();
  // printValueName();
  // printExpTable();

  eliminateDeadCode(F);
  for(Function::iterator bb=F.begin();bb!=F.end(); bb++)
  {
    for(BasicBlock::iterator I=bb->begin(); I!=bb->end();I++){
      printInstruction (I, true);
      // errs() << "\n";
    }
  }
  return PreservedAnalyses::all();
}
