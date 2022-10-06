// slang-ir-eliminate-multi-level-break.h
#pragma once

namespace Slang
{
    struct IRModule;
    struct CodeGenContext;
    struct IRGlobalValueWithCode;

    void eliminateMultiLevelBreak(CodeGenContext* codeGenContext, IRModule* module);
    void eliminateMultiLevelBreakForFunc(CodeGenContext* codeGenContext, IRModule* module, IRGlobalValueWithCode* func);

}
