// slang-ir-specialize.h
#pragma once

namespace Slang
{
struct IRModule;
struct IRInst;
struct IRFunc;
struct IRSpecialize;
struct SpecializationContext;
struct CodeGenContext;
class DiagnosticSink;
class TargetProgram;

struct SpecializationOptions
{
    // Option that allows specializeModule to generate dynamic-dispatch code
    // wherever possible to open up more specialization opportunities.
    //
    bool lowerWitnessLookups = false;

    // Option to report dynamic dispatch sites.
    bool reportDynamicDispatchSites = false;

    // When non-null, higher-order function parameters are specialized by the same fixed-point
    // driver as concrete opcode specialization and type-flow. A null context leaves that
    // target-dependent transformation disabled.
    CodeGenContext* higherOrderCodeGenContext = nullptr;
};

/// Specialize generic and interface-based code to use concrete types.
bool specializeModule(
    IRModule* module,
    TargetProgram* target,
    DiagnosticSink* sink,
    SpecializationOptions options);

void finalizeSpecialization(IRModule* module);

IRInst* specializeGeneric(
    SpecializationContext* context,
    IRSpecialize* specInst,
    bool queueFollowUpWork = true);
IRInst* specializeGeneric(IRSpecialize* specInst);

/// Run local specialization opportunities exposed under an already-materialized IR value.
bool specializeChildInsts(SpecializationContext* context, IRInst* rootInst);

} // namespace Slang
