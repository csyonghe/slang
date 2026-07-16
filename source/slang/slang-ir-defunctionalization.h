// Aspirational filename
#pragma once

namespace Slang
{
struct CodeGenContext;
struct IRInst;
struct IRModule;
struct IRType;

/// Specialize calls to higher order functions
///
/// This pass will rewrite any calls to higher order functions passing
/// global functions with calls to specialized versions simply
/// referencing the global.
///
bool specializeHigherOrderParameters(IRInst* rootInst, CodeGenContext* codeGenContext);
} // namespace Slang
