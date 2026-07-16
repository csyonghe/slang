#include "slang-ir-defunctionalization.h"

#include "slang-ir-insts.h"
#include "slang-ir-specialize-function-call.h"
#include "slang-ir-ssa-simplification.h"
#include "slang-ir.h"

namespace Slang
{

struct FunctionParameterSpecializationCondition : FunctionCallSpecializeCondition
{
    TargetRequest* targetRequest = nullptr;

    bool doesParamWantSpecialization(IRParam* param, IRInst* /*arg*/, IRCall* /*callInst*/)
    {
        IRType* type = param->getDataType();
        return as<IRFuncType>(type);
    }
};

bool specializeHigherOrderParameters(IRInst* rootInst, CodeGenContext* codeGenContext)
{
    auto module = rootInst->getModule();
    FunctionParameterSpecializationCondition condition;
    condition.targetRequest = codeGenContext->getTargetReq();
    // The consolidated specialization driver owns the fixed point. One invocation processes the
    // current call graph; if simplification exposes another round of higher-order calls, the driver
    // invokes this function again after draining its other opcode-specific work.
    return specializeFunctionCalls(codeGenContext, module, &condition, rootInst);
}

} // namespace Slang
