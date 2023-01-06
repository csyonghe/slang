#include "slang-ir-autodiff-rev.h"

#include "slang-ir-clone.h"
#include "slang-ir-dce.h"
#include "slang-ir-eliminate-phis.h"
#include "slang-ir-util.h"
#include "slang-ir-inst-pass-base.h"

#include "slang-ir-autodiff-fwd.h"


namespace Slang
{
    IRFuncType* BackwardDiffTranscriberBase::differentiateFunctionTypeImpl(IRBuilder* builder, IRFuncType* funcType, IRInst* intermeidateType)
    {
        List<IRType*> newParameterTypes;
        IRType* diffReturnType;

        for (UIndex i = 0; i < funcType->getParamCount(); i++)
        {
            bool noDiff = false;
            auto origType = funcType->getParamType(i);
            if (auto attrType = as<IRAttributedType>(origType))
            {
                if (attrType->findAttr<IRNoDiffAttr>())
                {
                    noDiff = true;
                    origType = attrType->getBaseType();
                }
            }
            if (noDiff)
            {
                newParameterTypes.add(origType);
            }
            else
            {
                if (auto diffPairType = tryGetDiffPairType(builder, origType))
                {
                    auto inoutDiffPairType = builder->getPtrType(kIROp_InOutType, diffPairType);
                    newParameterTypes.add(inoutDiffPairType);
                }
                else
                    newParameterTypes.add(origType);
            }
        }

        newParameterTypes.add(differentiateType(builder, funcType->getResultType()));

        if (intermeidateType)
        {
            newParameterTypes.add((IRType*)intermeidateType);
        }

        diffReturnType = builder->getVoidType();

        return builder->getFuncType(newParameterTypes, diffReturnType);
    }
    
    IRFuncType* BackwardDiffPrimalTranscriber::differentiateFunctionType(IRBuilder* builder, IRInst* func, IRFuncType* funcType)
    {
        auto intermediateType = builder->getBackwardDiffIntermediateContextType(func);
        auto outType = builder->getOutType(intermediateType);
        return differentiateFunctionTypeImpl(builder, funcType, outType);
    }

    InstPair BackwardDiffPrimalTranscriber::transcribeFunc(IRBuilder* builder, IRFunc* primalFunc, IRFunc* diffFunc)
    {
        SLANG_UNUSED(builder);
        SLANG_UNUSED(diffFunc);
        auto intermediateTypeDecor = primalFunc->findDecoration<IRBackwardDerivativeIntermediateTypeDecoration>();
        SLANG_RELEASE_ASSERT(intermediateTypeDecor);
        auto primalDecor = primalFunc->findDecoration<IRBackwardDerivativePrimalDecoration>();
        return InstPair(primalFunc, primalDecor->getBackwardDerivativePrimalFunc());
    }

    IRFuncType* BackwardDiffPropagateTranscriber::differentiateFunctionType(IRBuilder* builder, IRInst* func, IRFuncType* funcType)
    {
        auto intermediateType = builder->getBackwardDiffIntermediateContextType(func);
        return differentiateFunctionTypeImpl(builder, funcType, intermediateType);
    }

    IRFuncType* BackwardDiffTranscriber::differentiateFunctionType(IRBuilder* builder, IRInst* func, IRFuncType* funcType)
    {
        SLANG_UNUSED(func);
        return differentiateFunctionTypeImpl(builder, funcType, nullptr);
    }

    InstPair BackwardDiffPropagateTranscriber::transcribeFunc(IRBuilder* builder, IRFunc* primalFunc, IRFunc* diffFunc)
    {
        IRGlobalValueWithCode* diffPrimalFunc = nullptr;
        transcribeFuncImpl(builder, primalFunc, diffFunc, diffPrimalFunc);
        return InstPair(primalFunc, diffFunc);
    }

    InstPair BackwardDiffTranscriberBase::transcribeInstImpl(IRBuilder* builder, IRInst* origInst)
    {
        switch (origInst->getOp())
        {
        case kIROp_Param:
            return transcribeParam(builder, as<IRParam>(origInst));

        case kIROp_Return:
            return transcribeReturn(builder, as<IRReturn>(origInst));

        case kIROp_LookupWitness:
            return transcribeLookupInterfaceMethod(builder, as<IRLookupWitnessMethod>(origInst));

        case kIROp_Specialize:
            return transcribeSpecialize(builder, as<IRSpecialize>(origInst));

        case kIROp_MakeVectorFromScalar:
        case kIROp_MakeTuple:
        case kIROp_FloatLit:
        case kIROp_IntLit:
        case kIROp_VoidLit:
        case kIROp_ExtractExistentialWitnessTable:
        case kIROp_ExtractExistentialType:
        case kIROp_ExtractExistentialValue:
        case kIROp_WrapExistential:
        case kIROp_MakeExistential:
        case kIROp_MakeExistentialWithRTTI:
            return trascribeNonDiffInst(builder, origInst);

        case kIROp_StructKey:
            return InstPair(origInst, nullptr);
        }

        return InstPair(nullptr, nullptr);
    }

    // Returns "dp<var-name>" to use as a name hint for parameters.
    // If no primal name is available, returns a blank string.
    // 
    String BackwardDiffTranscriberBase::makeDiffPairName(IRInst* origVar)
    {
        if (auto namehintDecoration = origVar->findDecoration<IRNameHintDecoration>())
        {
            return ("dp" + String(namehintDecoration->getName()));
        }

        return String("");
    }

    InstPair BackwardDiffTranscriberBase::transposeBlock(IRBuilder* builder, IRBlock* origBlock)
    {
        IRBuilder subBuilder(builder->getSharedBuilder());
        subBuilder.setInsertLoc(builder->getInsertLoc());

        IRBlock* diffBlock = subBuilder.emitBlock();

        subBuilder.setInsertInto(diffBlock);

        // First transcribe every parameter in the block.
        for (auto param = origBlock->getFirstParam(); param; param = param->getNextParam())
            this->copyParam(&subBuilder, param);

        // The extra param for input gradient
        auto gradParam = subBuilder.emitParam(as<IRFuncType>(origBlock->getParent()->getFullType())->getResultType());

        // Then, run through every instruction and use the transcriber to generate the appropriate
        // derivative code.
        //
        for (auto child = origBlock->getFirstOrdinaryInst(); child; child = child->getNextInst())
            this->copyInst(&subBuilder, child);

        auto lastInst = diffBlock->getLastOrdinaryInst();
        List<IRInst*> grads = { gradParam };
        upperGradients.Add(lastInst, grads);
        for (auto child = diffBlock->getLastOrdinaryInst(); child; child = child->getPrevInst())
        {
            auto upperGrads = upperGradients.TryGetValue(child);
            if (!upperGrads)
                continue;
            if (upperGrads->getCount() > 1)
            {
                auto sumGrad = upperGrads->getFirst();
                for (auto i = 1; i < upperGrads->getCount(); i++)
                {
                    sumGrad = subBuilder.emitAdd(sumGrad->getDataType(), sumGrad, (*upperGrads)[i]);
                }
                this->transposeInstBackward(&subBuilder, child, sumGrad);
            }
            else
                this->transposeInstBackward(&subBuilder, child, upperGrads->getFirst());
        }

        subBuilder.emitReturn();

        return InstPair(diffBlock, diffBlock);
    }

    static bool isMarkedForBackwardDifferentiation(IRInst* callable)
    {
        return callable->findDecoration<IRBackwardDifferentiableDecoration>() != nullptr;
    }

    // Create an empty func to represent the transcribed func of `origFunc`.
    InstPair BackwardDiffTranscriberBase::transcribeFuncHeaderImpl(IRBuilder* inBuilder, IRFunc* origFunc)
    {
        if (auto bwdDiffFunc = findExistingDiffFunc(origFunc))
            return InstPair(origFunc, bwdDiffFunc);

        if (!isMarkedForBackwardDifferentiation(origFunc))
            return InstPair(nullptr, nullptr);

        IRBuilder builder(inBuilder->getSharedBuilder());
        builder.setInsertBefore(origFunc);

        IRFunc* primalFunc = origFunc;

        differentiableTypeConformanceContext.setFunc(origFunc);

        primalFunc = origFunc;

        auto diffFunc = builder.createFunc();

        SLANG_ASSERT(as<IRFuncType>(origFunc->getFullType()));
        IRType* diffFuncType = this->differentiateFunctionType(
            &builder,
            origFunc,
            as<IRFuncType>(origFunc->getFullType()));
        diffFunc->setFullType(diffFuncType);

        if (auto nameHint = origFunc->findDecoration<IRNameHintDecoration>())
        {
            auto originalName = nameHint->getName();
            StringBuilder newNameSb;
            newNameSb << "s_bwd_" << originalName;
            builder.addNameHintDecoration(diffFunc, newNameSb.getUnownedSlice());
        }

        if (auto outerGen = findOuterGeneric(diffFunc))
        {
            builder.setInsertBefore(origFunc);
            auto specialized =
                specializeWithGeneric(builder, outerGen, as<IRGeneric>(findOuterGeneric(origFunc)));
            addExistingDiffFuncDecor(&builder, origFunc, specialized);
        }
        else
        {
            addExistingDiffFuncDecor(&builder, origFunc, diffFunc);
        }

        // Mark the generated derivative function itself as differentiable.
        builder.addBackwardDifferentiableDecoration(diffFunc);

        // Find and clone `DifferentiableTypeDictionaryDecoration` to the new diffFunc.
        if (auto dictDecor = origFunc->findDecoration<IRDifferentiableTypeDictionaryDecoration>())
        {
            cloneDecoration(dictDecor, diffFunc);
        }

        return InstPair(primalFunc, diffFunc);
    }

    InstPair BackwardDiffTranscriberBase::transcribeFuncHeader(IRBuilder* inBuilder, IRFunc* origFunc)
    {
        auto result = transcribeFuncHeaderImpl(inBuilder, origFunc);

        FuncBodyTranscriptionTask task;
        task.originalFunc = as<IRFunc>(result.primal);
        task.resultFunc = as<IRFunc>(result.differential);
        task.type = diffTaskType;
        if (task.resultFunc)
        {
            autoDiffSharedContext->followUpFunctionsToTranscribe.add(task);
        }
        return result;
    }

    InstPair BackwardDiffTranscriber::transcribeFuncHeader(IRBuilder* inBuilder, IRFunc* origFunc)
    {
        auto header = transcribeFuncHeaderImpl(inBuilder, origFunc);
        if (!header.differential)
            return header;

        IRBuilder builder(inBuilder->getSharedBuilder());
        builder.setInsertInto(header.differential);
        builder.emitBlock();
        auto funcType = as<IRFuncType>(header.differential->getDataType());
        List<IRInst*> args;
        for (UInt i = 0; i < funcType->getParamCount(); i++)
        {
            auto paramType = funcType->getParamType(i);
            args.add(builder.emitParam(paramType));
        }
        auto outerGeneric = findOuterGeneric(origFunc);
        IRInst* specializedOriginalFunc = origFunc;
        if (outerGeneric)
        {
            specializedOriginalFunc = maybeSpecializeWithGeneric(builder, outerGeneric, findOuterGeneric(header.differential));
        }
        auto intermediateType = builder.getBackwardDiffIntermediateContextType(specializedOriginalFunc);
        auto intermediateVar = builder.emitVar(intermediateType);
        auto primalFunc = builder.emitBackwardDifferentiatePrimalInst(builder.getTypeKind(), specializedOriginalFunc);
        auto propagateFunc = builder.emitBackwardDifferentiatePropagateInst(builder.getTypeKind(), specializedOriginalFunc);
        args.add(intermediateVar);
        builder.emitCallInst(builder.getVoidType(), primalFunc, args);
        args.removeLast();
        args.add(builder.emitLoad(intermediateVar));
        builder.emitCallInst(builder.getVoidType(), propagateFunc, args);
        builder.emitReturn();
        return header;
    }

    // Puts parameters into their own block.
    void BackwardDiffTranscriberBase::makeParameterBlock(IRBuilder* inBuilder, IRFunc* func)
    {
        IRBuilder builder(inBuilder->getSharedBuilder());

        auto firstBlock = func->getFirstBlock();
        IRParam* param = func->getFirstParam();

        builder.setInsertBefore(firstBlock);
        
        // Note: It looks like emitBlock() doesn't use the current 
        // builder position, so we're going to manually move the new block
        // to before the existing block.
        auto paramBlock = builder.emitBlock();
        paramBlock->insertBefore(firstBlock);
        builder.setInsertInto(paramBlock);

        while(param)
        {
            IRParam* nextParam = param->getNextParam();

            // Copy inst into the new parameter block.
            auto clonedParam = cloneInst(&cloneEnv, &builder, param);
            param->replaceUsesWith(clonedParam);
            param->removeAndDeallocate();

            param = nextParam;
        }
        
        // Replace this block as the first block.
        firstBlock->replaceUsesWith(paramBlock);

        // Add terminator inst.
        builder.emitBranch(firstBlock);
    }

    void BackwardDiffTranscriberBase::cleanUpUnusedPrimalIntermediate(IRInst* func, IRInst* primalFunc, IRInst* intermediateType)
    {
        IRStructType* structType = as<IRStructType>(intermediateType);
        if (!structType)
        {
            auto genType = as<IRGeneric>(intermediateType);
            structType = as<IRStructType>(findGenericReturnVal(genType));
            SLANG_RELEASE_ASSERT(structType);
        }

        // Collect fields that are never fetched by reverse func.
        OrderedHashSet<IRStructKey*> fieldsToCleanup;
        for (auto children : structType->getChildren())
        {
            if (auto field = as<IRStructField>(children))
            {
                auto structKey = field->getKey();
                bool usedByRevFunc = false;
                for (auto use = structKey->firstUse; use; use = use->nextUse)
                {
                    if (isChildInstOf(use->getUser(), func))
                    {
                        usedByRevFunc = true;
                        break;
                    }
                }
                if (!usedByRevFunc)
                {
                    List<IRInst*> users;
                    for (auto use = structKey->firstUse; use; use = use->nextUse)
                    {
                        users.add(use->getUser());
                    }
                    for (auto user : users)
                    {
                        if (!isChildInstOf(user, primalFunc))
                            continue;
                        if (auto addr = as<IRFieldAddress>(user))
                        {
                            if (addr->hasMoreThanOneUse())
                                continue;
                            if (addr->firstUse)
                            {
                                if (addr->firstUse->getUser()->getOp() == kIROp_Store)
                                {
                                    addr->firstUse->getUser()->removeAndDeallocate();
                                }
                                addr->removeAndDeallocate();
                            }
                        }
                    }

                    bool hasNonTrivialUse = false;
                    for (auto use = structKey->firstUse; use; use = use->nextUse)
                    {
                        switch (use->getUser()->getOp())
                        {
                        case kIROp_PrimalValueStructKeyDecoration:
                        case kIROp_StructField:
                            continue;
                        default:
                            hasNonTrivialUse = true;
                            break;
                        }
                    }
                    if (!hasNonTrivialUse)
                    {
                        fieldsToCleanup.Add(structKey);
                    }
                }
            }
        }

        // Actually remove fields from struct.
        for (auto children : structType->getChildren())
        {
            if (auto field = as<IRStructField>(children))
            {
                if (fieldsToCleanup.Contains(field->getKey()))
                {
                    auto key = field->getKey();
                    List<IRInst*> keyUsers;
                    for (auto use = key->firstUse; use; use = use->nextUse)
                        keyUsers.add(use->getUser());
                    for (auto keyUser : keyUsers)
                        keyUser->removeAndDeallocate();
                    key->removeAndDeallocate();
                }
            }
        }
    }

    // Transcribe a function definition.
    void BackwardDiffTranscriberBase::transcribeFuncImpl(IRBuilder* builder, IRFunc* primalFunc, IRFunc* diffPropagateFunc, IRGlobalValueWithCode*& diffPrimalFunc)
    {
        SLANG_ASSERT(primalFunc);
        SLANG_ASSERT(diffPropagateFunc);
        // Reverse-mode transcription uses 4 separate steps:
        // TODO(sai): Fill in documentation.

        // Generate a temporary forward derivative function as an intermediate step.
        IRBuilder tempBuilder = *builder;
        tempBuilder.setInsertBefore(diffPropagateFunc);
        IRFunc* fwdDiffFunc = as<IRFunc>(
            fwdDiffTranscriber->transcribeFuncHeader(&tempBuilder, primalFunc).differential);
        SLANG_ASSERT(fwdDiffFunc);

        fwdDiffTranscriber->transcribeFunc(&tempBuilder, primalFunc, fwdDiffFunc);
        
        // Split first block into a paramter block.
        this->makeParameterBlock(&tempBuilder, as<IRFunc>(fwdDiffFunc));
        
        // This steps adds a decoration to instructions that are computing the differential.
        // TODO: This is disabled for now because fwd-mode already adds differential decorations
        // wherever need. We need to run this pass only for user-writted forward derivativecode.
        // 
        // diffPropagationPass->propagateDiffInstDecoration(builder, fwdDiffFunc);

        // Copy primal insts to the first block of the unzipped function, copy diff insts to the
        // second block of the unzipped function.
        // 
        IRFunc* unzippedFwdDiffFunc = diffUnzipPass->unzipDiffInsts(fwdDiffFunc);

        // Clone the primal blocks from unzippedFwdDiffFunc
        // to the reverse-mode function.
        // 
        // Special care needs to be taken for the first block since it holds the parameters
        
        // Clone all blocks into a temporary diff func.
        // We're using a temporary sice we don't want to clone decorations, 
        // only blocks, and right now there's no provision in slang-ir-clone.h
        // for that.
        // 
        builder->setInsertInto(diffPropagateFunc->getParent());
        auto tempDiffFunc = as<IRFunc>(cloneInst(&cloneEnv, builder, unzippedFwdDiffFunc));

        // Move blocks to the diffFunc shell.
        {
            List<IRBlock*> workList;
            for (auto block = tempDiffFunc->getFirstBlock(); block; block = block->getNextBlock())
                workList.add(block);
            
            for (auto block : workList)
                block->insertAtEnd(diffPropagateFunc);
        }

        // Transpose the first block (parameter block)
        transposeParameterBlock(builder, diffPropagateFunc);

        builder->setInsertInto(diffPropagateFunc);

        auto dOutParameter = diffPropagateFunc->getLastParam()->getPrevParam();

        // Transpose differential blocks from unzippedFwdDiffFunc into diffFunc (with dOutParameter) representing the 
        DiffTransposePass::FuncTranspositionInfo info = {dOutParameter, nullptr};
        diffTransposePass->transposeDiffBlocksInFunc(diffPropagateFunc, info);

        // Extracts the primal computations into its own func, and replace the primal insts
        // with the intermediate results computed from the extracted func.
        IRInst* intermediateType = nullptr;
        auto extractedPrimalFunc = diffUnzipPass->extractPrimalFunc(diffPropagateFunc, unzippedFwdDiffFunc, intermediateType);

        // Clean up by deallocating intermediate versions.
        tempDiffFunc->removeAndDeallocate();
        unzippedFwdDiffFunc->removeAndDeallocate();
        fwdDiffFunc->removeAndDeallocate();

        eliminateDeadCode(diffPropagateFunc);
        cleanUpUnusedPrimalIntermediate(diffPropagateFunc, extractedPrimalFunc, intermediateType);
        
        // If primal function is nested in a generic, we want to create separate generics for all the associated things
        // we have just created.
        auto primalOuterGeneric = findOuterGeneric(primalFunc);
        IRInst* specializedFunc = nullptr;
        auto intermediateTypeGeneric = hoistValueFromGeneric(*builder, intermediateType, specializedFunc);
        auto specializedIntermeidateType = maybeSpecializeWithGeneric(*builder, intermediateTypeGeneric, primalOuterGeneric);
        builder->addBackwardDerivativeIntermediateTypeDecoration(primalFunc, specializedIntermeidateType);

        auto primalFuncGeneric = hoistValueFromGeneric(*builder, extractedPrimalFunc, specializedFunc);
        builder->setInsertBefore(primalFunc);

        if (auto existingDecor = primalFunc->findDecoration<IRBackwardDerivativePrimalDecoration>())
        {
            // If we already created a header for primal func, move the body into the existing primal func header.
            auto existingPrimalHeader = existingDecor->getBackwardDerivativePrimalFunc();
            if (auto spec = as<IRSpecialize>(existingPrimalHeader))
                existingPrimalHeader = spec->getBase();
            moveInstChildren(existingPrimalHeader, primalFuncGeneric);
            primalFuncGeneric->replaceUsesWith(existingPrimalHeader);
            primalFuncGeneric->removeAndDeallocate();
        }
        else
        {
            auto specializedBackwardPrimalFunc = maybeSpecializeWithGeneric(*builder, primalFuncGeneric, primalOuterGeneric);
            builder->addBackwardDerivativePrimalDecoration(primalFunc, specializedBackwardPrimalFunc);
        }
        diffPrimalFunc = as<IRGlobalValueWithCode>(primalOuterGeneric);
    }

    void BackwardDiffTranscriberBase::transposeParameterBlock(IRBuilder* builder, IRFunc* diffFunc)
    {
        IRBlock* fwdDiffParameterBlock = diffFunc->getFirstBlock();

        // Find the 'next' block using the terminator inst of the parameter block.
        auto fwdParamBlockBranch = as<IRUnconditionalBranch>(fwdDiffParameterBlock->getTerminator());
        auto nextBlock = fwdParamBlockBranch->getTargetBlock();

        builder->setInsertInto(fwdDiffParameterBlock);

        // 1. Turn fwd-diff versions of the parameters into reverse-diff versions by wrapping them as InOutType<>
        for (auto child = fwdDiffParameterBlock->getFirstParam(); child;)
        {
            IRParam* nextChild = child->getNextParam();

            auto fwdParam = as<IRParam>(child);
            SLANG_ASSERT(fwdParam);
            
            // TODO: Handle ptr<pair> types.
            if (auto diffPairType = as<IRDifferentialPairType>(fwdParam->getDataType()))
            {
                // Create inout version. 
                auto inoutDiffPairType = builder->getInOutType(diffPairType);
                auto newParam = builder->emitParam(inoutDiffPairType); 

                // Map the _load_ of the new parameter as the clone of the old one.
                auto newParamLoad = builder->emitLoad(newParam);
                newParamLoad->insertAtStart(nextBlock); // Move to first block _after_ the parameter block.
                fwdParam->replaceUsesWith(newParamLoad);
                fwdParam->removeAndDeallocate();
            }
            else
            {
                // Default case (parameter has nothing to do with differentiation)
                // Do nothing.
            }

            child = nextChild;
        }

        auto paramCount = as<IRFuncType>(diffFunc->getDataType())->getParamCount();

        // 2. Add a parameter for 'derivative of the output' (d_out). 
        // The type is the second last parameter type of the function.
        // 
        auto dOutParamType = as<IRFuncType>(diffFunc->getDataType())->getParamType(paramCount - 2);

        SLANG_ASSERT(dOutParamType);

        builder->emitParam(dOutParamType);

        // Add a parameter for intermediate val.
        builder->emitParam(as<IRFuncType>(diffFunc->getDataType())->getParamType(paramCount - 1));
    }

    IRInst* BackwardDiffTranscriberBase::copyParam(IRBuilder* builder, IRParam* origParam)
    {
        auto primalDataType = origParam->getDataType();

        if (auto diffPairType = tryGetDiffPairType(builder, (IRType*)primalDataType))
        {
            auto inoutDiffPairType = builder->getPtrType(kIROp_InOutType, diffPairType);
            IRInst* diffParam = builder->emitParam(inoutDiffPairType);

            auto diffPairVarName = makeDiffPairName(origParam);
            if (diffPairVarName.getLength() > 0)
                builder->addNameHintDecoration(diffParam, diffPairVarName.getUnownedSlice());

            SLANG_ASSERT(diffParam);
            auto paramValue = builder->emitLoad(diffParam);
            auto primal = builder->emitDifferentialPairGetPrimal(paramValue);
            orginalToTranscribed.Add(origParam, primal);
            primalToDiffPair.Add(primal, diffParam);

            return diffParam;
        }

        return cloneInst(&cloneEnv, builder, origParam);
    }

    InstPair BackwardDiffTranscriberBase::copyBinaryArith(IRBuilder* builder, IRInst* origArith)
    {
        SLANG_ASSERT(origArith->getOperandCount() == 2);

        auto origLeft = origArith->getOperand(0);
        auto origRight = origArith->getOperand(1);

        IRInst* primalLeft;
        if (!orginalToTranscribed.TryGetValue(origLeft, primalLeft))
        {
            primalLeft = origLeft;
        }
        IRInst* primalRight;
        if (!orginalToTranscribed.TryGetValue(origRight, primalRight))
        {
            primalRight = origRight;
        }

        auto resultType = origArith->getDataType();
        IRInst* newInst;
        switch (origArith->getOp())
        {
        case kIROp_Add:
            newInst = builder->emitAdd(resultType, primalLeft, primalRight);
            break;
        case kIROp_Mul:
            newInst = builder->emitMul(resultType, primalLeft, primalRight);
            break;
        case kIROp_Sub:
            newInst = builder->emitSub(resultType, primalLeft, primalRight);
            break;
        case kIROp_Div:
            newInst = builder->emitDiv(resultType, primalLeft, primalRight);
            break;
        default:
            newInst = nullptr;
            getSink()->diagnose(origArith->sourceLoc,
                Diagnostics::unimplemented,
                "this arithmetic instruction cannot be differentiated");
        }
        orginalToTranscribed.Add(origArith, newInst);
        return InstPair(newInst, nullptr);
    }

    IRInst* BackwardDiffTranscriberBase::transposeBinaryArithBackward(IRBuilder* builder, IRInst* origArith, IRInst* grad)
    {
        SLANG_ASSERT(origArith->getOperandCount() == 2);

        auto lhs = origArith->getOperand(0);
        auto rhs = origArith->getOperand(1);

        if (as<IRInOutType>(lhs->getDataType()))
        {
            lhs = builder->emitLoad(lhs);
            lhs = builder->emitDifferentialPairGetPrimal(lhs);
        }
        if (as<IRInOutType>(rhs->getDataType()))
        {
            rhs = builder->emitLoad(rhs);
            rhs = builder->emitDifferentialPairGetPrimal(rhs);
        }

        IRInst* leftGrad;
        IRInst* rightGrad;


        switch (origArith->getOp())
        {
        case kIROp_Add:
            leftGrad = grad;
            rightGrad = grad;
            break;
        case kIROp_Mul:
            leftGrad = builder->emitMul(grad->getDataType(), rhs, grad);
            rightGrad = builder->emitMul(grad->getDataType(), lhs, grad);
            break;
        case kIROp_Sub:
            leftGrad = grad;
            rightGrad = builder->emitNeg(grad->getDataType(), grad);
            break;
        case kIROp_Div:
            leftGrad = builder->emitMul(grad->getDataType(), rhs, grad);
            rightGrad = builder->emitMul(grad->getDataType(), lhs, grad); // TODO 1.0 / Grad
            break;
        default:
            getSink()->diagnose(origArith->sourceLoc,
                Diagnostics::unimplemented,
                "this arithmetic instruction cannot be differentiated");
        }

        lhs = origArith->getOperand(0);
        rhs = origArith->getOperand(1);
        if (auto leftGrads = upperGradients.TryGetValue(lhs))
        {
            leftGrads->add(leftGrad);
        }
        else
        {
            upperGradients.Add(lhs, leftGrad);
        }
        if (auto rightGrads = upperGradients.TryGetValue(rhs))
        {
            rightGrads->add(rightGrad);
        }
        else
        {
            upperGradients.Add(rhs, rightGrad);
        }

        return nullptr;
    }

    InstPair BackwardDiffTranscriberBase::copyInst(IRBuilder* builder, IRInst* origInst)
    {
        // Handle common SSA-style operations
        switch (origInst->getOp())
        {
        case kIROp_Param:
            return transcribeParam(builder, as<IRParam>(origInst));

        case kIROp_Return:
            return InstPair(nullptr, nullptr);

        case kIROp_Add:
        case kIROp_Mul:
        case kIROp_Sub:
        case kIROp_Div:
            return copyBinaryArith(builder, origInst);

        default:
            // Not yet implemented
            SLANG_ASSERT(0);
        }

        return InstPair(nullptr, nullptr);
    }

    IRInst* BackwardDiffTranscriberBase::transposeParamBackward(IRBuilder* builder, IRInst* param, IRInst* grad)
    {
        IRInOutType* inoutParam = as<IRInOutType>(param->getDataType());
        auto pairType = as<IRDifferentialPairType>(inoutParam->getValueType());
        auto paramValue = builder->emitLoad(param);
        auto primal = builder->emitDifferentialPairGetPrimal(paramValue);
        auto diff = builder->emitDifferentialPairGetDifferential(
            (IRType*)pairBuilder->getDiffTypeFromPairType(builder, pairType),
            paramValue
        );
        auto newDiff = builder->emitAdd(grad->getDataType(), diff, grad);
        auto updatedParam = builder->emitMakeDifferentialPair(pairType, primal, newDiff);
        auto store = builder->emitStore(param, updatedParam);

        return store;
    }

    IRInst* BackwardDiffTranscriberBase::transposeInstBackward(IRBuilder* builder, IRInst* origInst, IRInst* grad)
    {
        // Handle common SSA-style operations
        switch (origInst->getOp())
        {
        case kIROp_Param:
            return transposeParamBackward(builder, as<IRParam>(origInst), grad);

        case kIROp_Add:
        case kIROp_Mul:
        case kIROp_Sub:
        case kIROp_Div:
            return transposeBinaryArithBackward(builder, origInst, grad);

        case kIROp_DifferentialPairGetPrimal:
        {
            if (auto param = primalToDiffPair.TryGetValue(origInst))
            {
                if (auto leftGrads = upperGradients.TryGetValue(*param))
                {
                    leftGrads->add(grad);
                }
                else
                {
                    upperGradients.Add(*param, grad);
                }
            }
            else
                SLANG_ASSERT(0);
            return nullptr;
        }

        default:
            // Not yet implemented
            SLANG_ASSERT(0);
        }

        return nullptr;
    }

    InstPair BackwardDiffTranscriberBase::transcribeSpecialize(IRBuilder* builder, IRSpecialize* origSpecialize)
    {
        auto primalBase = findOrTranscribePrimalInst(builder, origSpecialize->getBase());
        List<IRInst*> primalArgs;
        for (UInt i = 0; i < origSpecialize->getArgCount(); i++)
        {
            primalArgs.add(findOrTranscribePrimalInst(builder, origSpecialize->getArg(i)));
        }
        auto primalType = findOrTranscribePrimalInst(builder, origSpecialize->getFullType());
        auto primalSpecialize = (IRSpecialize*)builder->emitSpecializeInst(
            (IRType*)primalType, primalBase, primalArgs.getCount(), primalArgs.getBuffer());

        if (auto diffBase = instMapD.TryGetValue(origSpecialize->getBase()))
        {
            List<IRInst*> args;
            for (UInt i = 0; i < primalSpecialize->getArgCount(); i++)
            {
                args.add(primalSpecialize->getArg(i));
            }
            auto diffSpecialize = builder->emitSpecializeInst(
                builder->getTypeKind(), *diffBase, args.getCount(), args.getBuffer());
            return InstPair(primalSpecialize, diffSpecialize);
        }

        auto genericInnerVal = findInnerMostGenericReturnVal(as<IRGeneric>(origSpecialize->getBase()));
        // Look for an IRBackwardDerivativeDecoration on the specialize inst.
        // (Normally, this would be on the inner IRFunc, but in this case only the JVP func
        // can be specialized, so we put a decoration on the IRSpecialize)
        //
        if (auto derivativeFunc = findExistingDiffFunc(origSpecialize))
        {
            // Make sure this isn't itself a specialize .
            SLANG_RELEASE_ASSERT(!as<IRSpecialize>(derivativeFunc));

            return InstPair(primalSpecialize, derivativeFunc);
        }
        else if (auto diffBase = findExistingDiffFunc(genericInnerVal))
        {
            List<IRInst*> args;
            for (UInt i = 0; i < primalSpecialize->getArgCount(); i++)
            {
                args.add(primalSpecialize->getArg(i));
            }

            // A `BackwardDerivative` decoration on an inner func of a generic should always be a `specialize`.
            auto diffBaseSpecialize = as<IRSpecialize>(diffBase);
            SLANG_RELEASE_ASSERT(diffBaseSpecialize);

            // Note: this assumes that the generic arguments to specialize the derivative is the same as the
            // generic args to specialize the primal function. This is true for all of our stdlib functions,
            // but we may need to rely on more general substitution logic here.
            auto diffSpecialize = builder->emitSpecializeInst(
                builder->getTypeKind(), diffBaseSpecialize->getBase(), args.getCount(), args.getBuffer());

            return InstPair(primalSpecialize, diffSpecialize);
        }
        else if (auto diffDecor = genericInnerVal->findDecoration<IRBackwardDifferentiableDecoration>())
        {
            List<IRInst*> args;
            for (UInt i = 0; i < primalSpecialize->getArgCount(); i++)
            {
                args.add(primalSpecialize->getArg(i));
            }
            auto diffCallee = findOrTranscribeDiffInst(builder, origSpecialize->getBase());
            auto diffSpecialize = builder->emitSpecializeInst(
                builder->getTypeKind(), diffCallee, args.getCount(), args.getBuffer());
            return InstPair(primalSpecialize, diffSpecialize);
        }
        else
        {
            return InstPair(primalSpecialize, nullptr);
        }
    }
}
