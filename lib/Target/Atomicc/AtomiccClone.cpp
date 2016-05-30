/* Copyright (c) 2015 The Connectal Project
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */
// Portions of this program were derived from source with the license:
//     This file is distributed under the University of Illinois Open Source
//     License. See LICENSE.TXT for details.
#include <stdio.h>
#include <cxxabi.h> // abi::__cxa_demangle
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
    std::string NameSuffix = "foosuff";
    Instruction *NewInst = I->clone();

    if (I->hasName())
        NewInst->setName(I->getName()+NameSuffix);
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

void prepareClone(Instruction *TI, const Instruction *I)
{
    cloneVmap.clear();
    auto TargetA = TI->getParent()->getParent()->arg_begin();
    const Function *SourceF = I->getParent()->getParent();
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
