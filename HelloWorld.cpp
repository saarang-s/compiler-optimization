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
#include <string>
#include <map>
#include <vector>
#include <typeinfo>

using namespace llvm;

// ValueName Table
int VN = 1;
std::map<Value*, int> valueName;

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

// Name Table
std::map<Value*, APInt> nameTable;

void addName(Value* val, APInt constant){
  nameTable[val] = constant;
  // return nameTable[val];
}

bool isUseConst (Value * ptr){
  if (isa<ConstantInt>(*ptr)){
    return true;
  }
  else if (nameTable.find(ptr) != nameTable.end())
  {
    return true;
  }
  return false;
}

bool isValueUnused(Value *V) {
    // Check if the value has any users
    return V->user_empty();
}

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

// should only be used after checking isUseConst
APInt getConstFromUse(Value* ptr){
  if (isa<ConstantInt>(*ptr)){
    return dyn_cast<ConstantInt>(ptr)->getValue();
  }

  return nameTable[ptr];
}

void getValueName(Use *it, std::string *op){
  if ((*it)->hasName()){
      *op = (*it)->getName();
      errs() << *it << " has name\n";
  }
  else {
      if (isa<ConstantInt>(it)){
          auto* constantVal = dyn_cast<ConstantInt>(it);
          errs() <<"[const = "<< (constantVal->getValue()) << "] ";
      }
      else{
          errs () << "[reg? = " << *it << "] ";
          // errs() << "neither has name nor it is constant " << *it << "\n"; 
          *op = "";
      }
  }
}

bool IsInstructionDead (BasicBlock::iterator I)
{
  if (I->getOpcode() == Instruction::Ret)
  {
    return false;
  }
  else if (isa<StoreInst>(I))
  {
    auto* ptr = dyn_cast<User>(I);
    auto* op1 = ptr->getOperand(1);
    if (!isValueUsedtoLoad(op1))
    {
      return true;
    }
    else
    {
      return false;
    }
  }
  else
  {
    auto * val = dyn_cast<Value>(I);
    if(isValueUnused(val))
    {
      return true;
    }
  }
  return false;
}     

void replaceAllUses (Value * operand, APInt newAPIntValue)
{
  Value *newOperand = ConstantInt::get(operand->getType(), newAPIntValue);

  for (Use &U : operand->uses()) {
    Instruction *userInst = cast<Instruction>(U.getUser());

    userInst->replaceUsesOfWith(operand, newOperand);
  }
}
void replaceAllUses (Value * operand, Value * newOperand)
{
  for (Use &U : operand->uses()) {
    Instruction *userInst = cast<Instruction>(U.getUser());

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
    if (I->getOpcode() == Instruction::Add){
      if (getConstFromUse(op1) == 0){
        replaceAllUses(val, op2);
      }
    }
    else if (I->getOpcode() == Instruction::SDiv || I->getOpcode() == Instruction::UDiv || I->getOpcode() == Instruction::Mul){
      if (getConstFromUse(op1) == 0){
        addName(val, APInt(32, 0));
        replaceAllUses(val, APInt(32, 0));
      }
    }
  }
  else if (isUseConst(op2))
  {
    if (I->getOpcode() == Instruction::Add || I->getOpcode() == Instruction::Sub){
      if (getConstFromUse(op2) == 0){
        replaceAllUses(val, op1);
      }
    }
    else if (I->getOpcode() == Instruction::SDiv || I->getOpcode() == Instruction::UDiv || I->getOpcode() == Instruction::Mul){
      if (getConstFromUse(op2) == 0){
        addName(val, APInt(32, 0));
        replaceAllUses(val, APInt(32, 0));
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
    errs() << dyn_cast<ConstantInt>(ptr)->getValue() <<", " <<ptr;
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
        if(IsInstructionDead(I))
        {
          toRemove.push_back(I);
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
    errs() << "BasicBlok size = " << bb->size()<<"\n";
      
    for(BasicBlock::iterator I=bb->begin(); I!=bb->end();I++){
      // printInstruction(I);
      // errs() <<"\n";
      if (isa<AllocaInst>(I)) {
        continue;
      }
      // Store Instruction
      else if (isa<StoreInst>(I))
      {
        auto* ptr = dyn_cast<User>(I);
         
        addValueName(ptr->getOperand(1)); // destination
        auto * op1 = ptr->getOperand(0);   // source
        
        if (isUseConst(op1)){
          addName(ptr->getOperand(1), getConstFromUse(op1));
          replaceAllUses(op1,getConstFromUse(op1));
        }
      }
      // Load Instruction
      else if (isa<LoadInst>(I))
      {
        auto* val = dyn_cast<Value>(I);                
        addValueName(val);
        auto* op1 = dyn_cast<User>(I)->getOperand(0);
        
        if(isUseConst(op1)){
          addName(val, getConstFromUse(op1));
          replaceAllUses(val,getConstFromUse(op1));
        }
      }
      // Arith Instruction
      else if (I->getOpcode() == Instruction::Add 
            || I->getOpcode() == Instruction::Sub 
            || I->getOpcode() == Instruction::Mul 
            || I->getOpcode() == Instruction::UDiv 
            || I->getOpcode() == Instruction::SDiv )
      {
        performArithmeticOpt(I);
      }
    
    }
    errs()<<"\n";
  }
  errs() << F.getName() << "\n";
  // printNameTable();
  // printValueName();

  eliminateDeadCode(F);
  for(Function::iterator bb=F.begin();bb!=F.end(); bb++)
  {
    for(BasicBlock::iterator I=bb->begin(); I!=bb->end();I++){
      printInstruction (I, true);
      errs() << "\n";
    }
  }
  return PreservedAnalyses::all();
}
