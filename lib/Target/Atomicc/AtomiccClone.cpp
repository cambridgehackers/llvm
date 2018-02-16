//===-- AtomiccClone.cpp - Generating Verilog from LLVM -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements zzz
//
//===----------------------------------------------------------------------===//
#include <stdio.h>
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

#include "AtomiccDecl.h"

static std::map<const Value *, Value *> cloneVmap;
static int trace_clone;

/*
 * clone a DAG from one basic block to another
 */
Instruction *cloneTree(const Instruction *I, Instruction *insertPoint)
{
    Instruction *NewInst = I->clone();

    if (I->hasName())
        NewInst->setName(I->getName());
    for (unsigned OI = 0, E = I->getNumOperands(); OI != E; ++OI) {
        const Value *oval = I->getOperand(OI);
        if (cloneVmap.find(oval) == cloneVmap.end()) {
            if (const Instruction *IC = dyn_cast<Instruction>(oval))
                cloneVmap[oval] = cloneTree(IC, insertPoint);
            else
                continue;
        }
        NewInst->setOperand(OI, cloneVmap[oval]);
    }
    NewInst->insertBefore(insertPoint);
    if (trace_clone)
        printf("[%s:%d] %s %d\n", __FUNCTION__, __LINE__, NewInst->getOpcodeName(), NewInst->getNumOperands());
    return NewInst;
}

void prepareClone(Instruction *TI, const Function *SourceF)
{
    cloneVmap.clear();
    auto TargetA = TI->getParent()->getParent()->arg_begin();
    auto AI = SourceF->arg_begin(), AE = SourceF->arg_end();
    for (; AI != AE; ++AI, ++TargetA)
        cloneVmap[AI] = TargetA;
}

void prepareReplace(const Value *olda, Value *newa)
{
    cloneVmap.clear();
    cloneVmap[olda] = newa;
}

/*
 * Recursively delete an Instruction and operands (if they become unused)
 */
void recursiveDelete(Value *V) //nee: RecursivelyDeleteTriviallyDeadInstructions
{
    Instruction *I = dyn_cast<Instruction>(V);
    if (!I)
        return;
    for (unsigned i = 0, e = I->getNumOperands(); i != e; ++i) {
        Value *OpV = I->getOperand(i);
        I->setOperand(i, nullptr);
        if (OpV && OpV->use_empty())
            recursiveDelete(OpV);
    }
    I->eraseFromParent();
}
