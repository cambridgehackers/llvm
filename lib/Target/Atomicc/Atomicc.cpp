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
#include "llvm/Support/DynamicLibrary.h"

using namespace llvm;
#include "AtomiccDecl.h"

extern "C" void LLVMInitializeAtomiccTarget() {
  RegisterTargetMachine<AtomiccTargetMachine> X(TheAtomiccTarget);
}
//===----------------------------------------------------------------------===//
//                       External Interface declaration
//===----------------------------------------------------------------------===//
ExecutionEngine *EE;
namespace {
  class AtomiccWriter : public ModulePass {
    std::string Filename;
  public:
    static char ID;
    explicit AtomiccWriter(std::string _Filename): ModulePass(ID), Filename(_Filename) {}
    const char *getPassName() const override { return "Atomicc backend"; }
    bool runOnModule(Module &M) override;
  };
} // end anonymous namespace.
char AtomiccWriter::ID = 0;
static std::list<const StructType *> structSeq;
static std::map<std::string, const StructType *> structAlpha;

static void getDepend(const Type *Ty)
{
std::map<std::string, const StructType *> structTemp;
    if (const PointerType *PTy = dyn_cast_or_null<PointerType>(Ty))
        if (auto STy = dyn_cast<StructType>(PTy->getElementType()))
            structTemp[getStructName(STy)] = STy;
    const StructType *STy = dyn_cast_or_null<StructType>(Ty);
    if (!STy || !STy->hasName() || STy->getName().substr(0, 7) == "emodule")
        return;
    std::string name = getStructName(STy);

    if (!isInterface(STy))
    if (strncmp(STy->getName().str().c_str(), "class.std::", 11) // don't generate anything for std classes
     && strncmp(STy->getName().str().c_str(), "struct.std::", 12)) {
        ClassMethodTable *table = classCreate[STy];
        int Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            Type *element = *I;
            if (table)
            if (Type *newType = table->replaceType[Idx])
                element = newType;
            if (auto iSTy = dyn_cast<StructType>(element))
                structTemp[getStructName(iSTy)] = iSTy;
        }
        for (auto FI : table->method) {
            Function *func = FI.second;
            if (!func) {
                printf("[%s:%d] missing function in table method %s\n", __FUNCTION__, __LINE__, FI.first.c_str());
                continue;
                //exit(-1);
            }
            auto AI = func->arg_begin(), AE = func->arg_end();
            if (const StructType *iSTy = dyn_cast<StructType>(func->getReturnType()))
                structTemp[getStructName(iSTy)] = iSTy;
            AI++;
            for (; AI != AE; ++AI) {
                Type *element = AI->getType();
                if (auto PTy = dyn_cast<PointerType>(element))
                    element = PTy->getElementType();
                if (const StructType *iSTy = dyn_cast<StructType>(element))
                    structTemp[getStructName(iSTy)] = iSTy;
            }
        }
    }
    for (auto element: structTemp) {
         if (structAlpha[element.first])
             getDepend(element.second);
         if (structAlpha[element.first]) {
             structSeq.push_back(element.second);
             structAlpha[element.first] = NULL;
         }
    }
    if (structAlpha[name]) {
        structSeq.push_back(STy);
        structAlpha[name] = NULL;
    }
}

bool AtomiccWriter::runOnModule(Module &M)
{
    std::string OutputDir = "tmp/foo";
    if (Filename != "") {
        OutputDir = Filename;
        int ind = OutputDir.rfind('.');
        if (ind > 0)
            OutputDir = OutputDir.substr(0, ind);
    }
    std::string ErrorMsg;
    // Create the execution environment and allocate memory for static items
    EngineBuilder builder((std::unique_ptr<Module>(&M)));
    builder.setMCPU("");
    builder.setErrorStr(&ErrorMsg);
    builder.setEngineKind(EngineKind::Interpreter);
    builder.setOptLevel(CodeGenOpt::None);
    EE = builder.create();
    assert(EE);
#ifdef __APPLE__
    std::string extraLibFilename = "libstdc++.dylib";
    if (sys::DynamicLibrary::LoadLibraryPermanently(extraLibFilename.c_str(), &ErrorMsg)) {
        printf("[%s:%d] error opening %s\n", __FUNCTION__, __LINE__, extraLibFilename.c_str());
        exit(-1);
    }
#endif
    /*
     * Top level processing done after all module object files are loaded
     */
    globalMod = &M;
    // Before running constructors, clean up and rewrite IR
    preprocessModule(&M);

    // run Constructors from user program
    EE->runStaticConstructorsDestructors(false);

    // Construct the address -> symbolic name map using actual data allocated/initialized.
    // Pointer datatypes allocated by a class are hoisted and instantiated statically
    // in the generated class.  (in cpp, only pointers can be overridden with derived
    // class instances)
    constructAddressMap(&M);

    // Walk the list of all classes referenced in the IR image,
    // recursively generating cpp class and verilog module definitions
    std::string myName = OutputDir;
    int ind = myName.rfind('/');
    if (ind > 0)
        myName = myName.substr(0, ind);
    myName += "_GENERATED_";
    FILE *OStrV = fopen((OutputDir + ".generated.v").c_str(), "w");
    FILE *OStrVH = fopen((OutputDir + ".generated.vh").c_str(), "w");
    FILE *OStrC = fopen((OutputDir + ".generated.cpp").c_str(), "w");
    FILE *OStrCH = fopen((OutputDir + ".generated.h").c_str(), "w");
    fprintf(OStrV, "`include \"%s.generated.vh\"\n\n", OutputDir.c_str());
    fprintf(OStrVH, "`ifndef __%s_VH__\n`define __%s_VH__\n\n", myName.c_str(), myName.c_str());
    fprintf(OStrC, "#include \"%s.generated.h\"\n", OutputDir.c_str());
    fprintf(OStrCH, "#ifndef __%s_H__\n#define __%s_H__\n", myName.c_str(), myName.c_str());
    for (auto current : classCreate)
        if (!isInterface(current.first))
            structAlpha[getStructName(current.first)] = current.first;
    for (auto item : structAlpha)
        getDepend(item.second);
    for (auto current : structSeq)
        generateContainedStructs(current, OStrV, OStrVH, OStrC, OStrCH);
    fprintf(OStrCH, "#endif  // __%s_H__\n", myName.c_str());
    fprintf(OStrVH, "`endif\n");
    return false;
}

bool AtomiccTargetMachine::addPassesToEmitFile(
    PassManagerBase &PM, raw_pwrite_stream &o, CodeGenFileType FileType,
    bool DisableVerify, AnalysisID StartBefore, AnalysisID StartAfter,
    AnalysisID StopAfter, MachineFunctionInitializer *MFInitializer) {
    if (FileType != TargetMachine::CGFT_AssemblyFile)
      return true;
    PM.add(new AtomiccWriter(o.getFilename()));
    return false;
}
