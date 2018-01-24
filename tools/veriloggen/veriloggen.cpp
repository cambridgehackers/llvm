//===--- veriloggen.cpp - The verilog generator -----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This utility may be invoked in the following manner:
//
//===----------------------------------------------------------------------===//
#include <stdio.h>
#include "../../lib/Target/Atomicc/AtomiccReadIR.h"
#include "../../lib/Target/Atomicc/AtomiccVerilog.h"
#include "../../lib/Target/Atomicc/AtomiccMetaGen.h"

int main(int argc, char **argv) {
printf("[%s:%d] VERILOGGGEN\n", __FUNCTION__, __LINE__);
    if (argc != 2) {
        printf("[%s:%d] veriloggen <outputFileStem>\n", __FUNCTION__, __LINE__);
        exit(-1);
    }
    std::string OutputDir = argv[1];
printf("[%s:%d] stem %s\n", __FUNCTION__, __LINE__, OutputDir.c_str());
    FILE *OStrIRread = fopen((OutputDir + ".generated.IR").c_str(), "r");
    FILE *OStrV = fopen((OutputDir + ".generated.v").c_str(), "w");
    FILE *OStrVH = fopen((OutputDir + ".generated.vh").c_str(), "w");
    fprintf(OStrV, "`include \"%s.generated.vh\"\n\n", OutputDir.c_str());
    std::string myName = OutputDir;
    int ind = myName.rfind('/');
    if (ind > 0)
        myName = myName.substr(0, ind);
    myName += "_GENERATED_";
    fprintf(OStrVH, "`ifndef __%s_VH__\n`define __%s_VH__\n\n", myName.c_str(), myName.c_str());
    std::list<ModuleIR *> irSeq;
    readModuleIR(irSeq, OStrIRread);
    for (auto irItem : irSeq) {
        // now generate the verilog header file '.vh'
        metaGenerate(irItem, OStrVH);
        // Only generate verilog for modules derived from Module
        generateModuleDef(irItem, OStrV);
    }
    fprintf(OStrVH, "`endif\n");
    return 0;
}
