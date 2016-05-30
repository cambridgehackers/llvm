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
#include "llvm/Linker/Linker.h"
#include "llvm/AsmParser/Parser.h"
#include "llvm/AsmParser/SlotMapping.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/DynamicLibrary.h"

using namespace llvm;

#include "AtomiccDecl.h"

cl::list<std::string> InputFile(cl::Positional, cl::OneOrMore, cl::desc("<input bitcode>"));
cl::opt<std::string> MArch("march", cl::desc("Architecture to generate assembly for (see --version)"));
cl::list<std::string> MAttrs("mattr", cl::CommaSeparated, cl::desc("Target specific attributes (-mattr=help for details)"), cl::value_desc("a1,+a2,-a3,..."));
cl::opt<std::string> OutputDir("odir", cl::init(""), cl::desc("<output directory>"));

ExecutionEngine *EE;

/*
 * Read/load llvm input files
 */
static Module *llvm_ParseIRFile(const std::string &Filename, LLVMContext &Context, SlotMapping *Slots)
{
    SMDiagnostic Err;
//printf("[%s:%d] file %s\n", __FUNCTION__, __LINE__, Filename.c_str());
    Module *M = new Module(Filename, Context);
    M->addModuleFlag(llvm::Module::Warning, "Debug Info Version", llvm::DEBUG_METADATA_VERSION);
    ErrorOr<std::unique_ptr<MemoryBuffer>> FileOrErr = MemoryBuffer::getFileOrSTDIN(Filename);
    if (parseAssemblyInto(FileOrErr.get()->getMemBufferRef(), *M, Err, Slots)) {
        printf("llvm-translate: load error in %s, error: %s, line: %s\n", Filename.c_str(),
            Err.getMessage().str().c_str(),
            Err.getLineContents().str().c_str());
        exit(-1);
    }
    return M;
}

int Atomiccmain(int argc, char **argv, char * const *envp)
{
    std::string ErrorMsg;

    cl::ParseCommandLineOptions(argc, argv, "llvm interpreter & dynamic compiler\n");
    if (OutputDir == "") {
        printf("llvm-translate: output directory must be specified with '--odir=directoryName'\n");
        exit(-1);
    }

    // Load the first input bitcode file
    LLVMContext &Context = getGlobalContext();
    SlotMapping slots;
    Module *Mod = llvm_ParseIRFile(InputFile[0], Context, &slots);
    if (!Mod) {
        printf("llvm-translate: load/link error in %s\n", InputFile[0].c_str());
        return 1;
    }
    Linker L(Mod);
    for (unsigned i = 1; i < InputFile.size(); ++i) {
        // Load/link subsequent input bitcode files
        Module *M = llvm_ParseIRFile(InputFile[i], Context, &slots);
        if (!M || L.linkInModule(M)) {
            printf("llvm-translate: load/link error in %s\n", InputFile[i].c_str());
        }
    }

    // Create the execution environment and allocate memory for static items
    EngineBuilder builder((std::unique_ptr<Module>(Mod)));
    builder.setMArch(MArch);
    builder.setMCPU("");
    builder.setMAttrs(MAttrs);
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
    globalMod = Mod;
    // Before running constructors, clean up and rewrite IR
    preprocessModule(Mod);

    // run Constructors from user program
    EE->runStaticConstructorsDestructors(false);

    // Construct the address -> symbolic name map using actual data allocated/initialized.
    // Pointer datatypes allocated by a class are hoisted and instantiated statically
    // in the generated class.  (in cpp, only pointers can be overridden with derived
    // class instances)
    constructAddressMap(Mod);

    // Walk the list of all classes referenced in the IR image,
    // recursively generating cpp class and verilog module definitions
    for (auto current : classCreate)
        generateContainedStructs(current.first, OutputDir);
printf("[%s:%d] end processing\n", __FUNCTION__, __LINE__);
    fflush(stderr);
    fflush(stdout);
    return 0;
}
