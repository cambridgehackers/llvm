//===-- AtomiccTargetInfo.cpp - Atomicc Target Implementation -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "AtomiccTargetMachine.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/TargetRegistry.h"
using namespace llvm;

Target llvm::TheAtomiccTarget;

extern "C" void LLVMInitializeAtomiccTargetInfo() {
  RegisterTarget<Triple::atomicc, /*HasJIT=*/false>  X(TheAtomiccTarget, "atomicc", "Atomicc");

}

extern "C" void LLVMInitializeAtomiccTargetMC() {}
