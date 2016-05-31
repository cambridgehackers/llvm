//===-- Atomicc.cpp - Library for converting LLVM code to C++ code -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the writing of the LLVM IR as a set of C++ calls to the
// LLVM IR interface. The input module is assumed to be verified.
//
//===----------------------------------------------------------------------===//

#include "AtomiccTargetMachine.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/IR/LegacyPassManager.h"
using namespace llvm;

void AtomiccMain(Module *M);
extern "C" void LLVMInitializeAtomiccTarget() {
  RegisterTargetMachine<AtomiccTargetMachine> X(TheAtomiccTarget);
}
//===----------------------------------------------------------------------===//
//                       External Interface declaration
//===----------------------------------------------------------------------===//
namespace {
  class AtomiccWriter : public ModulePass {
    std::unique_ptr<formatted_raw_ostream> OutOwner;
    formatted_raw_ostream &Out;
    //const Module *TheModule;
  public:
    static char ID;
    explicit AtomiccWriter(std::unique_ptr<formatted_raw_ostream> o)
        : ModulePass(ID), OutOwner(std::move(o)), Out(*OutOwner) {}

    const char *getPassName() const override { return "Atomicc backend"; }

    bool runOnModule(Module &M) override {
printf("[%s:%d] ATOMICCCCCCCCCC\n", __FUNCTION__, __LINE__);
AtomiccMain(&M);
return false;
    }
  };
} // end anonymous namespace.
char AtomiccWriter::ID = 0;

bool AtomiccTargetMachine::addPassesToEmitFile(
    PassManagerBase &PM, raw_pwrite_stream &o, CodeGenFileType FileType,
    bool DisableVerify, AnalysisID StartBefore, AnalysisID StartAfter,
    AnalysisID StopAfter, MachineFunctionInitializer *MFInitializer) {
printf("[%s:%d]  AtomiccTargetMachine::addPassesToEmitFile ZZZZZZZ %d\n", __FUNCTION__, __LINE__, (FileType != TargetMachine::CGFT_AssemblyFile));
  if (FileType != TargetMachine::CGFT_AssemblyFile)
    return true;
  auto FOut = llvm::make_unique<formatted_raw_ostream>(o);
  PM.add(new AtomiccWriter(std::move(FOut)));
  return false;
}
