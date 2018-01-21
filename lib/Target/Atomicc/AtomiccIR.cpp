//===-- AtomiccIR.cpp - Generating IR from LLVM -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements zzz
//
//===----------------------------------------------------------------------===//
#include <stdio.h>
#include "llvm/ADT/StringExtras.h"

using namespace llvm;

#include "AtomiccDecl.h"

/*
 * Generate Module info into IR
 */
void generateModuleIR(ModuleIR *IR, FILE *OStr)
{
    static std::string metaName[] = {"METANONE", "METAREAD ", "METAINVOKE "};
    fprintf(OStr, "MODULE %s = %d (\n", IR->name.c_str(), IR->sequence);
    for (auto item: IR->softwareName)
        if (item.second)
            fprintf(OStr, "    SOFTWARE %s\n", item.first.c_str());
    for (auto item: IR->outcall)
        fprintf(OStr, "    OUTCALL %s = %d\n", item.fldName.c_str(), item.IR->sequence);
    for (auto item: IR->ruleFunctions)
        if (item.second)
            fprintf(OStr, "    RULE %s\n", item.first.c_str());
    for (auto item: IR->priority)
        fprintf(OStr, "    PRIORITY %s %s\n", item.first.c_str(), item.second.c_str());
    for (auto item: IR->interfaceConnect)
        fprintf(OStr, "    INTERFACECONNECT %s=%s, IR=%d\n", item.target.c_str(), item.source.c_str(), item.IR->sequence);
    for (auto item: IR->fields) {
        std::string irstr;
        if (item.IR)
            irstr = utostr(item.IR->sequence) + ":";
        std::string temp = item.fldName;
        if (item.vecCount != -1)
            temp += " VEC " + utostr(item.vecCount);
        if (item.arrRange != "")
            temp += " RANGE " + item.arrRange;
        if (item.typeStr != "")
            temp += " FORMAT " + item.typeStr;
        fprintf(OStr, "    FIELD%s %s%s\n", item.isPtr ? "/PTR ": "", irstr.c_str(), temp.c_str());
    }
    for (auto item: IR->method) {
        std::list<std::string> mlines;
        MethodInfo *MI = item.second;
        std::string temp = item.first;
        if (MI->retArrRange != "")
            temp += " RANGE " + MI->retArrRange;
        if (MI->guard != "")
            temp += " = (" + MI->guard + ")";
        fprintf(OStr, "    METHOD%s%s", MI->action ? "/Action ":" ", temp.c_str());
        for (auto litem: MI->params)
            mlines.push_back("PARAM " + litem.name + " " + litem.arrRange);
        for (auto litem: MI->storeList) {
            std::string alloc = " ";
            if (litem.isAlloca)
                alloc = "/Alloca ";
            mlines.push_back("STORE" + alloc + litem.cond + ":" + litem.dest + " = " + litem.value);
        }
        for (auto litem: MI->callList)
            mlines.push_back("CALL" + std::string(litem.isAction ? "/Action ":" ")
                + litem.cond + ":" + litem.value);

        for (int index = MetaRead; index != MetaMax; index++)
            for (auto litem: MI->meta[index])
                for (auto sitem: litem.second)
                    mlines.push_back(metaName[index] + litem.first + " " + sitem);
        if (mlines.size())
            fprintf(OStr, " (");
        fprintf(OStr, "\n");
        for (auto line: mlines)
             fprintf(OStr, "        %s\n", line.c_str());
        if (mlines.size())
            fprintf(OStr, "    )\n");
    }
    fprintf(OStr, ")\n");
}
