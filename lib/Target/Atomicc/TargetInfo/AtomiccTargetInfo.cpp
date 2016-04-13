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

static bool Atomicc_TripleMatchQuality(Triple::ArchType Arch) {
  // This backend doesn't correspond to any architecture. It must be explicitly
  // selected with -march.
  return false;
}

extern "C" void LLVMInitializeAtomiccTargetInfo() {
  TargetRegistry::RegisterTarget(TheAtomiccTarget, "atomicc",
                                  "Atomicc",
                                  &Atomicc_TripleMatchQuality);
}

extern "C" void LLVMInitializeAtomiccTargetMC() {}
