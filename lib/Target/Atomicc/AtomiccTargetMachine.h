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

namespace llvm {

class formatted_raw_ostream;

struct AtomiccTargetMachine : public TargetMachine {
  AtomiccTargetMachine(const Target &T, const Triple &TT, StringRef CPU,
                   StringRef FS, const TargetOptions &Options, Reloc::Model RM,
                   CodeModel::Model CM, CodeGenOpt::Level OL)
      : TargetMachine(T, "e-m:e-i64:64-f80:128-n8:16:32:64-S128", TT, CPU, FS, Options) {}

public:
  bool addPassesToEmitFile(PassManagerBase &PM, raw_pwrite_stream &Out,
                           CodeGenFileType FileType, bool DisableVerify,
                           AnalysisID StartBefore, AnalysisID StartAfter,
                           AnalysisID StopAfter,
                           MachineFunctionInitializer *MFInitializer) override;
};

extern Target TheAtomiccTarget;

} // End llvm namespace


#endif
