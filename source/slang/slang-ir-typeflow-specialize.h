// slang-ir-typeflow-specialize.h
#pragma once
#include "slang-ir.h"
#include "slang-target-program.h"

namespace Slang
{
struct SpecializationContext;

struct InvalidExistentialSpecializationDiagnostic
{
    String genericName;
    SourceLoc location;
};

// True for functions that seed the live call graph used by both concrete specialization and
// type-flow analysis.
bool isTypeFlowEntryPoint(IRFunc* func);

// True when a concrete specialization still derives an argument from an existential value.
bool isInvalidExistentialSpecialization(IRInst* specializedValue);

// Emit the diagnostic candidates produced by the final, unchanged type-flow epoch.
void diagnoseInvalidExistentialSpecializations(
    List<InvalidExistentialSpecializationDiagnostic> const& diagnostics,
    DiagnosticSink* sink);

// Convert dynamic insts such as `LookupWitnessMethod`, `ExtractExistentialValue`,
// `ExtractExistentialType`, `ExtractExistentialWitnessTable` and more into specialized versions
// based on the possible values at at the use sites, based on a data-flow-style interprocedural
// analysis.
//
// This pass is intended to be run after all specialization insts with concrete arguments have
// already been processed.
//
// This pass may generate more `Specialize` insts. `outLiveRoots` receives the concrete functions
// and global values rewritten during the type-flow epoch so the consolidated specialization
// driver can process exactly those roots after this analysis context has been discarded.
//
bool specializeDynamicInsts(
    IRModule* module,
    TargetProgram* target,
    DiagnosticSink* sink,
    SpecializationContext* context,
    bool shouldReportDynamicDispatchSites,
    List<IRInst*>* outLiveRoots = nullptr,
    List<InvalidExistentialSpecializationDiagnostic>* outDiagnostics = nullptr,
    HashSet<IRInst*>* expandedDynamicCalls = nullptr,
    HashSet<IRInst*>* terminalDispatcherCalls = nullptr);

bool isSetSpecializedGeneric(IRInst* callee);

IROp getSetOpFromType(IRType* type);
} // namespace Slang
