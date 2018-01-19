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
    static const char *metaName[] = {"METANONE", "METAREAD", "METAWRITE", "METAINVOKE"};
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
    for (auto item: IR->fields)
        fprintf(OStr, "    FIELD %s VEC %lld RANGE %s IR %d PTR %d TYPE %s\n", item.fldName.c_str(),
            item.vecCount, item.arrRange.c_str(), item.iIR ? item.iIR->sequence : -1,
            item.isPtr, item.typeStr.c_str());
    for (auto item: IR->method) {
        MethodInfo *MI = item.second;
        fprintf(OStr, "    METHOD %s %d %s = %s(\n", item.first.c_str(), MI->action,
             MI->retArrRange.c_str(), MI->guard.c_str());
        for (auto litem: MI->params)
            fprintf(OStr, "        PARAM %s %s\n",
                litem.name.c_str(), litem.arrRange.c_str());
        for (auto litem: MI->storeList)
            fprintf(OStr, "        STORE %s, %s, %s\n",
                litem.dest.c_str(), litem.value.c_str(), litem.cond.c_str());
        for (auto litem: MI->callList)
            fprintf(OStr, "        CALL %s, %s, %d\n",
                litem.value.c_str(), litem.cond.c_str(), litem.isAction);
        for (int index = MetaRead; index != MetaMax; index++)
            for (auto litem: MI->meta.list[index])
                for (auto sitem: litem.second)
                    fprintf(OStr, "        %s %s %s\n", metaName[index], litem.first.c_str(), sitem.c_str());
        fprintf(OStr, "    )\n");
    }
    fprintf(OStr, ")\n");
}
