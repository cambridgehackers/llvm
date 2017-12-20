//===-- AtomiccTargetMachine.h - TargetMachine for the C++ backend --*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file declares the TargetMachine that is used by the C++ backend.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_ATOMICCBACKEND_ATOMICCTARGETMACHINE_H
#define LLVM_LIB_TARGET_ATOMICCBACKEND_ATOMICCTARGETMACHINE_H

#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetSubtargetInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/TargetLoweringObjectFileImpl.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/IR/LegacyPassManager.h"
//#include "llvm/MC/MCAsmInfo.h"
#include "llvm/Support/TargetRegistry.h"

namespace llvm {

class formatted_raw_ostream;

struct AtomiccTargetMachine : public LLVMTargetMachine {
  std::unique_ptr<TargetLoweringObjectFile> TLOF;
  AtomiccTargetMachine(const Target &T, const Triple &TT, StringRef CPU,
                     StringRef FS, const TargetOptions &Options,
                     Optional<Reloc::Model> RM, CodeModel::Model CM,
                     CodeGenOpt::Level OL)
      : LLVMTargetMachine(T, "e-m:e-i64:64-f80:128-n8:16:32:64-S128", TT, CPU, FS, Options, Reloc::Static, CM, OL),
      TLOF(make_unique<TargetLoweringObjectFileELF>())
      { }

public:
  bool addPassesToEmitFile(
      PassManagerBase &PM, raw_pwrite_stream &Out, CodeGenFileType FileType,
      bool DisableVerify = true, AnalysisID StartBefore = nullptr,
      AnalysisID StartAfter = nullptr, AnalysisID StopBefore = nullptr,
      AnalysisID StopAfter = nullptr) override;
  ~AtomiccTargetMachine() override {}

  TargetPassConfig *createPassConfig(PassManagerBase &PM) override;

  TargetLoweringObjectFile *getObjFileLowering() const override {
    return TLOF.get();
  }
};

extern Target TheAtomiccTarget;

} // End llvm namespace


#endif
