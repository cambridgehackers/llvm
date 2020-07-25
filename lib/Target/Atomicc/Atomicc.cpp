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
#include <stdlib.h> // system()

using namespace llvm;
#include "AtomiccDecl.h"

std::string globalPath; // from clang/tools/driver/driver.cpp
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
    StringRef getPassName() const override { return "Atomicc backend"; }
    bool runOnModule(Module &M) override;
  };
} // end anonymous namespace.
char AtomiccWriter::ID = 0;

#include <unistd.h>
#include <fcntl.h>
#ifdef __APPLE__ // hack for debugging
#include <libproc.h>
#endif
#define MAX_FILENAME 1000
static char filenameBuffer[MAX_FILENAME];
char *getExecutionFilename(char *buf, int buflen)
{
    int rc, fd;
#ifdef __APPLE__ // hack for debugging
    static char pathbuf[PROC_PIDPATHINFO_MAXSIZE];
    rc = proc_pidpath (getpid(), pathbuf, sizeof(pathbuf));
    return pathbuf;
#endif
    char *filename = 0;
    buf[0] = 0;
    fd = open("/proc/self/maps", O_RDONLY);
    while ((rc = read(fd, buf, buflen-1)) > 0) {
	buf[rc] = 0;
	rc = 0;
	while(buf[rc]) {
	    char *endptr;
	    unsigned long addr = strtoul(&buf[rc], &endptr, 16);
	    if (endptr && *endptr == '-') {
		char *endptr2;
		unsigned long addr2 = strtoul(endptr+1, &endptr2, 16);
		if (addr <= (unsigned long)&getExecutionFilename && (unsigned long)&getExecutionFilename <= addr2) {
		    filename = strstr(endptr2, "  ");
		    while (*filename == ' ')
			filename++;
		    endptr2 = strstr(filename, "\n");
		    if (endptr2)
			*endptr2 = 0;
		    goto endloop;
		}
	    }
	    while(buf[rc] && buf[rc] != '\n')
		rc++;
	    if (buf[rc])
		rc++;
	}
    }
endloop:
    if (!filename) {
	fprintf(stderr, "[%s:%d] could not find execution filename\n", __FUNCTION__, __LINE__);
	return 0;
    }
    return filename;
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
    for (auto item = globalMod->getFunctionList().begin(),
              iend = globalMod->getFunctionList().end(); item != iend; item++)
        functionMap[item->getName()] = &*item;
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
    // recursively generating IR
    generateIR(OutputDir);

    // Read/process IR to generate verilog module definitions
    globalPath = "../../../atomicc/";
    char *fn = getExecutionFilename(filenameBuffer, sizeof(filenameBuffer));
    globalPath = fn;
    int ind = globalPath.rfind("/");
    globalPath = globalPath.substr(0, ind) + "/../../../atomicc/";
    std::string commandLine = globalPath + "veriloggen " + OutputDir;
    int ret = system(commandLine.c_str());
printf("[%s:%d] RETURN from '%s' %d\n", __FUNCTION__, __LINE__, commandLine.c_str(), ret);
    if (ret)
        exit(-1); // force error return to be propigated
    return false;
}

bool AtomiccTargetMachine::addPassesToEmitFile(
    PassManagerBase &PM, raw_pwrite_stream &o, CodeGenFileType FileType,
    bool DisableVerify, AnalysisID StartBefore, AnalysisID StartAfter,
    AnalysisID StopBefore, AnalysisID StopAfter) {
    if (FileType != TargetMachine::CGFT_AssemblyFile)
      return true;
    PM.add(new AtomiccWriter(o.getFilename()));
    return false;
}
TargetPassConfig *AtomiccTargetMachine::createPassConfig(PassManagerBase &PM) {
  return new TargetPassConfig(*this, PM);
}
