#!/usr/bin/env python3
"""Reject replaced semantic vocabulary in the frontend specification.

The terminology chapter is the sole alias registry and is intentionally excluded. All other
Markdown files are checked with ASCII identifier boundaries so canonical compounds such as
``ParamPassingMode`` and ``StorageAccessMode`` do not accidentally match their replaced suffixes.
The validator is deterministic and uses only the Python standard library.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys
from typing import Pattern


TYPE_SYSTEM_DIR = Path(__file__).resolve().parent
REPOSITORY_ROOT = TYPE_SYSTEM_DIR.parent.parent
TERMINOLOGY_CHAPTER = "00-terminology.md"

IDENTIFIER_LEFT = r"(?<![A-Za-z0-9_])"
IDENTIFIER_RIGHT = r"(?![A-Za-z0-9_])"


@dataclass(frozen=True)
class ForbiddenTerm:
    """One forbidden spelling and the canonical vocabulary named by its diagnostic."""

    description: str
    canonical: str
    pattern: Pattern[str]


def _schema_root(root: str) -> Pattern[str]:
    """Match an alias used as a schema root, including derived ``Id``/``Result`` names."""

    return re.compile(rf"{IDENTIFIER_LEFT}{re.escape(root)}[A-Za-z0-9_]*{IDENTIFIER_RIGHT}")


def _exact_identifier(identifier: str) -> Pattern[str]:
    """Match one complete identifier without matching it inside a canonical compound."""

    return re.compile(
        rf"{IDENTIFIER_LEFT}{re.escape(identifier)}{IDENTIFIER_RIGHT}"
    )


def _identifier_with_component(component: str) -> Pattern[str]:
    """Match an identifier containing a CamelCase component at an identifier boundary."""

    return re.compile(
        rf"{IDENTIFIER_LEFT}(?=[A-Za-z_])[A-Za-z0-9_]*"
        rf"{re.escape(component)}[A-Za-z0-9_]*{IDENTIFIER_RIGHT}"
    )


def _compound_identifier_with_component(component: str) -> Pattern[str]:
    """Match a CamelCase component only when it occurs in a compound identifier."""

    escaped = re.escape(component)
    return re.compile(
        rf"{IDENTIFIER_LEFT}(?=[A-Za-z_])(?:"
        rf"[A-Za-z0-9_]+{escaped}[A-Za-z0-9_]*|"
        rf"{escaped}[A-Za-z0-9_]+"
        rf"){IDENTIFIER_RIGHT}"
    )


ALLOWED_FORBIDDEN_MATCHES = {
    # This is a grammar-production name, not a replacement schema name for ``Decl``.
    "AmbiguousDeclarationOrExpressionStatement",
    # A prose/section plural, not a schema identifier.
    "Declarations",
}


FORBIDDEN_TERMS = (
    # Storage replaced the compiler-literature term "place" throughout the semantic model.
    ForbiddenTerm(
        "Place-derived identifier",
        "Storage / PhysicalStorage / AbstractStorage",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?=[A-Za-z_])"
            rf"[A-Za-z0-9_]*Places?(?=[A-Z0-9_]|{IDENTIFIER_RIGHT})"
            rf"[A-Za-z0-9_]*{IDENTIFIER_RIGHT}"
        ),
    ),
    ForbiddenTerm(
        "lowercase place vocabulary",
        "storage",
        re.compile(r"(?<![A-Za-z])places?(?![A-Za-z])"),
    ),
    ForbiddenTerm(
        "PhysicalTokenTape",
        "PhysicalTokenList",
        _schema_root("PhysicalTokenTape"),
    ),
    ForbiddenTerm(
        "token tape phrase",
        "physical token list",
        re.compile(r"(?<![A-Za-z])token[ -]+tape(?![A-Za-z])", re.IGNORECASE),
    ),
    ForbiddenTerm("TokenKind", "TokenType", _schema_root("TokenKind")),
    ForbiddenTerm("FileId", "SourceFileId", _schema_root("FileId")),
    ForbiddenTerm(
        "bare SnapshotId",
        "ASTSnapshotId / SemanticSnapshotId / SourceFileSnapshotId",
        _exact_identifier("SnapshotId"),
    ),
    ForbiddenTerm("AstKind", "SyntaxNode kind", _schema_root("AstKind")),
    ForbiddenTerm("AstNode", "SyntaxNode", _schema_root("AstNode")),
    ForbiddenTerm("AstSnapshot", "ASTSnapshot", _schema_root("AstSnapshot")),
    ForbiddenTerm("AstEdit", "ASTEdit", _schema_root("AstEdit")),
    ForbiddenTerm(
        "Cst identifier component", "CST", _identifier_with_component("Cst")
    ),
    ForbiddenTerm(
        "Ast identifier component", "AST", _identifier_with_component("Ast")
    ),
    ForbiddenTerm(
        "Declaration identifier component",
        "Decl",
        _compound_identifier_with_component("Declaration"),
    ),
    ForbiddenTerm("FunctionType", "FuncType", _schema_root("FunctionType")),
    ForbiddenTerm(
        "FunctionSignature query",
        "BuildCallableSignature / CallableSignature",
        _exact_identifier("FunctionSignature"),
    ),
    ForbiddenTerm(
        "SemanticValue-derived identifier",
        "SchemaValue (with Val as the type-system subset)",
        _identifier_with_component("SemanticValue"),
    ),
    ForbiddenTerm("PassingMode", "ParamPassingMode", _schema_root("PassingMode")),
    ForbiddenTerm("SelfType", "ThisType", _schema_root("SelfType")),
    ForbiddenTerm("UnitType", "VoidType", _schema_root("UnitType")),
    ForbiddenTerm("NeverType", "BottomType", _schema_root("NeverType")),
    ForbiddenTerm("NominalType", "DeclRefType", _schema_root("NominalType")),
    ForbiddenTerm("PointerType", "PtrType", _schema_root("PointerType")),
    ForbiddenTerm("ReferenceType", "ExplicitRefType", _schema_root("ReferenceType")),
    ForbiddenTerm("ArrayType", "ArrayExpressionType", _schema_root("ArrayType")),
    ForbiddenTerm("PackType", "ConcreteTypePack", _schema_root("PackType")),
    ForbiddenTerm(
        "OpenedExistentialType",
        "ExtractExistentialType",
        _schema_root("OpenedExistentialType"),
    ),
    ForbiddenTerm("IntersectionType", "AndType", _schema_root("IntersectionType")),
    ForbiddenTerm("CanonicalDeclRef", "DeclRef", _schema_root("CanonicalDeclRef")),
    ForbiddenTerm("DeclUseExpr", "DeclRefExpr", _schema_root("DeclUseExpr")),
    # These are deliberately exact roots: StorageAccessMode and StorageAccessPlan are canonical.
    ForbiddenTerm("bare AccessMode", "StorageAccessMode", _schema_root("AccessMode")),
    ForbiddenTerm("bare AccessPlan", "StorageAccessPlan", _schema_root("AccessPlan")),
    ForbiddenTerm(
        "visibility AccessContext", "VisibilityContext", _schema_root("AccessContext")
    ),
    ForbiddenTerm(
        "visibility AccessDecision", "VisibilityDecision", _schema_root("AccessDecision")
    ),
    ForbiddenTerm(
        "visibility AccessEvidence", "VisibilityEvidence", _schema_root("AccessEvidence")
    ),
    ForbiddenTerm(
        "schema Visibility",
        "DeclVisibility",
        re.compile(
            rf"(?:(?<=`)Visibility(?=`)|(?<=: )Visibility{IDENTIFIER_RIGHT}|"
            rf"(?<=\| )Visibility{IDENTIFIER_RIGHT}|^\s*Visibility(?=\s*=))"
        ),
    ),
    ForbiddenTerm("CapabilityFormula", "CapabilitySet", _schema_root("CapabilityFormula")),
    ForbiddenTerm("ConversionRank", "ConversionCost", _schema_root("ConversionRank")),
    ForbiddenTerm(
        "AccessOperand", "StorageAccessOperand", _schema_root("AccessOperand")
    ),
    ForbiddenTerm("AccessStep", "StorageAccessStep", _schema_root("AccessStep")),
    ForbiddenTerm(
        "rankingConversion", "rankingCoercion", _exact_identifier("rankingConversion")
    ),
    ForbiddenTerm(
        "ConvertedAccess", "AppliedStorageCoercion", _schema_root("ConvertedAccess")
    ),
    ForbiddenTerm(
        "ConsumedWithoutAccessConversion",
        "ConsumedWithoutStorageCoercion",
        _schema_root("ConsumedWithoutAccessConversion"),
    ),
    ForbiddenTerm(
        "InterfaceSubtypeWitness", "SubtypeWitness", _schema_root("InterfaceSubtypeWitness")
    ),
    ForbiddenTerm(
        "InterfaceSubtypeEvidence",
        "SubtypeWitnessRef",
        _schema_root("InterfaceSubtypeEvidence"),
    ),
    ForbiddenTerm(
        "InterfaceSubtypeTarget / ConformanceTarget",
        "SubtypeWitnessTarget",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:InterfaceSubtypeTarget|ConformanceTarget)"
            rf"{IDENTIFIER_RIGHT}"
        ),
    ),
    ForbiddenTerm(
        "RefinementClauseId",
        "InterfaceInheritanceClauseId",
        _schema_root("RefinementClauseId"),
    ),
    ForbiddenTerm(
        "ConformanceDefinition", "WitnessTable definition", _schema_root("ConformanceDefinition")
    ),
    ForbiddenTerm(
        "RequirementEvidenceMap", "RequirementDictionary", _schema_root("RequirementEvidenceMap")
    ),
    ForbiddenTerm(
        "RequirementSatisfaction", "RequirementWitness", _schema_root("RequirementSatisfaction")
    ),
    ForbiddenTerm("WitnessUseStage", "WitnessTableState", _schema_root("WitnessUseStage")),
    ForbiddenTerm("WitnessTableValue", "WitnessTable", _schema_root("WitnessTableValue")),
    ForbiddenTerm(
        "WitnessTableConstructionScope",
        "ConformanceConstructionScope",
        _schema_root("WitnessTableConstructionScope"),
    ),
    ForbiddenTerm(
        "ConformanceDependency",
        "WitnessTableDependency",
        _schema_root("ConformanceDependency"),
    ),
    ForbiddenTerm(
        "WitnessTableClassifier", "WitnessTableForm", _schema_root("WitnessTableClassifier")
    ),
    ForbiddenTerm(
        "ConformanceClassifier", "WitnessTableForm", _schema_root("ConformanceClassifier")
    ),
    ForbiddenTerm(
        "InterfaceWitnessClassifier",
        "SubtypeWitnessForm",
        _schema_root("InterfaceWitnessClassifier"),
    ),
    ForbiddenTerm(
        "InterfaceWitness identifier component",
        "SubtypeWitness",
        _identifier_with_component("InterfaceWitness"),
    ),
    ForbiddenTerm(
        "PackNonEmptyWitness", "NonEmptyPackWitness", _schema_root("PackNonEmptyWitness")
    ),
    ForbiddenTerm(
        "PackNonEmptyDerivation",
        "NonEmptyPackWitnessDerivation",
        _schema_root("PackNonEmptyDerivation"),
    ),
    ForbiddenTerm(
        "WitnessEntryKey", "InterfaceRequirementKeyOf", _schema_root("WitnessEntryKey")
    ),
    ForbiddenTerm(
        "SomeWitnessEntryKey",
        "SomeInterfaceRequirementKey",
        _schema_root("SomeWitnessEntryKey"),
    ),
    ForbiddenTerm(
        "WitnessRuntimeEntryKey",
        "RuntimeInterfaceRequirementKey",
        _schema_root("WitnessRuntimeEntryKey"),
    ),
    ForbiddenTerm(
        "ReferenceHandle-derived identifier",
        "PointerLike / ExplicitRef",
        _identifier_with_component("ReferenceHandle"),
    ),
    ForbiddenTerm("CoreAST", "IRReadyAST", _schema_root("CoreAST")),
    ForbiddenTerm(
        "Core AST phrase",
        "IRReadyAST",
        re.compile(r"(?<![A-Za-z])Core[ -]+AST(?![A-Za-z])"),
    ),
    ForbiddenTerm("LowerToCore", "LowerToIRReadyAST", _schema_root("LowerToCore")),
    ForbiddenTerm(
        "Core-stage schema identifier",
        "IRReady-stage identifier",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:"
            rf"Core(?:Stage|Snapshot|Expr|Stmt|Decl|Type|Value|Call|Storage|Initialization|"
            rf"Differential|Witness|Operation|Shape|Input|Output|Block|Param|Callable|Argument|"
            rf"Capture|Function|Member|Aggregate|Access|Result|Evidence|Plan|Node)[A-Za-z0-9_]*"
            rf"|[A-Za-z_][A-Za-z0-9_]*Core(?:AST|Stage|Snapshot|Expr|Stmt|Decl|Type|Value|Call|"
            rf"Storage|Initialization|Differential|Witness|Operation|Shape|Input|Output|Block|"
            rf"Param|Callable|Argument|Capture|Function|Member|Aggregate|Access|Result|Evidence|"
            rf"Plan|Node)"
            rf"[A-Za-z0-9_]*"
            rf"){IDENTIFIER_RIGHT}"
        ),
    ),
    ForbiddenTerm("IRInstruction", "IRInst", _schema_root("IRInstruction")),
    ForbiddenTerm("IROperation", "IROp / IRInst", _schema_root("IROperation")),
    ForbiddenTerm("IRBlockParameter", "IRParam", _schema_root("IRBlockParameter")),
    ForbiddenTerm(
        "call-specific invented IR opcode",
        "IRCall plus CallInstSemanticMetadata",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:DirectCallOperation|WitnessCallOperation|"
            rf"DynamicCallOperation|LambdaCallOperation){IDENTIFIER_RIGHT}"
        ),
    ),
    ForbiddenTerm(
        "invented control-flow opcode",
        "IRUnconditionalBranch / IRConditionalBranch / IRSwitch / IRReturn / "
        "IRThrow / IRUnreachable",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:BranchOperation|ConditionalBranchOperation|SwitchOperation|"
            rf"ReturnOperation|ThrowOperation|UnreachableOperation){IDENTIFIER_RIGHT}"
        ),
    ),
    ForbiddenTerm(
        "SelectDerivativeOperation",
        "IRForwardDifferentiate / IRBackwardDifferentiate plus DerivativeSelectionInstSemanticPlan",
        _schema_root("SelectDerivativeOperation"),
    ),
    ForbiddenTerm("IRErrorOperation", "IRPoison", _schema_root("IRErrorOperation")),
    ForbiddenTerm("IRError", "IRPoison", _schema_root("IRError")),
    ForbiddenTerm(
        "invented IR reference/storage operation sum",
        "ReferenceInstSemanticPlan / PhysicalStorageInstSemanticPlan / "
        "StorageAccessInstSemanticPlan",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:IRReferenceOperation|IRPhysicalStorageOperation|"
            rf"IRStorageAccessOperation){IDENTIFIER_RIGHT}"
        ),
    ),
    ForbiddenTerm(
        "invented IR initialization operation",
        "InitializationInstSemanticPlan",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:IRInitializationDescriptor|IRInitializationOperation|"
            rf"IRReadyInitializationOperation){IDENTIFIER_RIGHT}"
        ),
    ),
    ForbiddenTerm(
        "invented reference/storage opcode alternative",
        "the corresponding ...InstPlan sidecar selecting an actual IROp",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:AddressOfOperation|AccessorReferenceResultOperation|"
            rf"RegisteredReferenceProducerOperation|ReferenceDereferenceOperation|"
            rf"PointerDereferenceOperation|RegisteredReferenceDereferenceOperation|"
            rf"BuiltinPhysicalProjectionStorageOperation|RegisteredPhysicalProjectionOperation|"
            rf"MaterializeTemporaryOperation|InitializeTemporaryOperation|"
            rf"DestroyTemporaryOperation){IDENTIFIER_RIGHT}"
        ),
    ),
    ForbiddenTerm(
        "old derivative IR payload schema",
        "IRReadyDerivativeSelectionPlan / IRReadyDifferentiationPlan / "
        "derivative semantic metadata",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:IRReadyDerivativeSelection|IRReadyDifferentiationOperation|"
            rf"IRDerivativeProviderDescriptor|IRDerivativeSelectionOperandLayout)"
            rf"{IDENTIFIER_RIGHT}"
        ),
    ),
    # FacetClosure names the mathematical closure operation, not a synthesized lambda construct.
    ForbiddenTerm(
        "Closure schema identifier",
        "LambdaDecl / synthesized lambda environment",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?!FacetClosure(?:[A-Za-z0-9_]|{IDENTIFIER_RIGHT}))"
            rf"(?=[A-Za-z_])[A-Za-z0-9_]*Closure[A-Za-z0-9_]*{IDENTIFIER_RIGHT}"
        ),
    ),
    ForbiddenTerm(
        "PartialGeneric schema root",
        "PartiallyAppliedGenericValue",
        _schema_root("PartialGeneric"),
    ),
    ForbiddenTerm("BindHeader", "BindDeclHeader", _schema_root("BindHeader")),
    ForbiddenTerm("BoundHeader", "DeclHeader", _schema_root("BoundHeader")),
    ForbiddenTerm("ReceiverExpr", "ThisExpr", _schema_root("ReceiverExpr")),
    ForbiddenTerm(
        "InitializerExpression", "InitializerExpr", _schema_root("InitializerExpression")
    ),
    ForbiddenTerm(
        "EmptyInitializerExpression",
        "InvokeExpr(argumentCount: 0)",
        _schema_root("EmptyInitializerExpression"),
    ),
    ForbiddenTerm(
        "NewInitializerExpression", "NewExpr", _schema_root("NewInitializerExpression")
    ),
    ForbiddenTerm(
        "CStyleExplicitCast", "ExplicitCastExpr", _schema_root("CStyleExplicitCast")
    ),
    ForbiddenTerm(
        "DeclEqualsBraces",
        "DeclEqualsInitializerList",
        _schema_root("DeclEqualsBraces"),
    ),
    ForbiddenTerm(
        "InterfaceInstance shorthand",
        "InterfaceInstanceKey",
        _exact_identifier("InterfaceInstance"),
    ),
    ForbiddenTerm(
        "ConditionalSatisfaction",
        "ConditionalRequirementWitnessAt",
        _schema_root("ConditionalSatisfaction"),
    ),
    ForbiddenTerm("SourceDocument", "TestSourceFixture", _schema_root("SourceDocument")),
    ForbiddenTerm(
        "WitnessCallRef", "SubtypeWitnessRef", _schema_root("WitnessCallRef")
    ),
    ForbiddenTerm("SurfaceFile", "ASTSnapshot<Surface>", _schema_root("SurfaceFile")),
    ForbiddenTerm("ScopedFile", "ASTSnapshot<Scoped>", _schema_root("ScopedFile")),
    ForbiddenTerm(
        "NominalDefinition", "NodeRef<Typed, Decl>", _schema_root("NominalDefinition")
    ),
    ForbiddenTerm("TypedStmt", "NodeRef<Typed, Stmt>", _schema_root("TypedStmt")),
    ForbiddenTerm(
        "IRWitnessLookupKey",
        "first-class interface-requirement key operand",
        _schema_root("IRWitnessLookupKey"),
    ),
    ForbiddenTerm(
        "ReverseDifferentiate", "BackwardDifferentiate", _schema_root("ReverseDifferentiate")
    ),
    ForbiddenTerm(
        "bare differentiate-expression constructor",
        "ForwardDifferentiateExpr / BackwardDifferentiateExpr",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:ForwardDifferentiate|BackwardDifferentiate)(?=\()"
        ),
    ),
    ForbiddenTerm(
        "SelectReverseDerivative",
        "Backward derivative selection",
        _schema_root("SelectReverseDerivative"),
    ),
    ForbiddenTerm(
        "BackwardUnitResult", "BackwardVoidResult", _schema_root("BackwardUnitResult")
    ),
    ForbiddenTerm(
        "StopGradient-derived identifier",
        "DetachExpr / IRDetachDerivative",
        _identifier_with_component("StopGradient"),
    ),
    ForbiddenTerm(
        "DifferentialHarness-derived identifier",
        "FrontendComparisonHarness",
        _identifier_with_component("DifferentialHarness"),
    ),
    ForbiddenTerm("TypeApplication", "DeclRefType application", _schema_root("TypeApplication")),
    ForbiddenTerm("TypeExpr", "typed Expr plus TypeId", _schema_root("TypeExpr")),
    ForbiddenTerm(
        "bare AST judgment constructor",
        "LiteralExpr / AssignExpr / SelectExpr / BreakStmt / ReturnStmt",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:Literal|Assign|Conditional|Break|Return)(?=\()"
        ),
    ),
    ForbiddenTerm("BareBraces", "InitializerListExpr", _schema_root("BareBraces")),
    ForbiddenTerm("BracedInput", "InitializerListExpr input", _schema_root("BracedInput")),
    ForbiddenTerm(
        "BracedElements", "InitializerListExpr elements", _schema_root("BracedElements")
    ),
    ForbiddenTerm(
        "DeclaredInitializer schema root",
        "DeclaredConstructor",
        _schema_root("DeclaredInitializer"),
    ),
    ForbiddenTerm(
        "InitializerCallable", "ConstructorCallable", _schema_root("InitializerCallable")
    ),
    ForbiddenTerm(
        "RefinementWitnessEntry",
        "BaseInterfaceEntry",
        _schema_root("RefinementWitnessEntry"),
    ),
    ForbiddenTerm(
        "self-looking staged initialization alias",
        "InitializationCandidateResultAt / InitializationResultAt / InitializationPlanIdAt",
        re.compile(
            rf"{IDENTIFIER_LEFT}(?:InitializationCandidateResult|InitializationResult|"
            rf"InitializationPlanId)\s*<"
        ),
    ),
    ForbiddenTerm(
        "SynthesizedInitializer schema root",
        "SynthesizedConstructor",
        _schema_root("SynthesizedInitializer"),
    ),
    ForbiddenTerm(
        "LookupWitnessOperation",
        "IRLookupWitnessMethod / lookupWitness",
        _schema_root("LookupWitnessOperation"),
    ),
    ForbiddenTerm(
        "SpecializeWitnessOperation",
        "IRSpecialize / specialize",
        _schema_root("SpecializeWitnessOperation"),
    ),
    ForbiddenTerm(
        "ExtractExistentialWitnessOperation",
        "IRExtractExistentialWitnessTable / extractExistentialWitnessTable",
        _schema_root("ExtractExistentialWitnessOperation"),
    ),
    ForbiddenTerm("PpOptions", "PreprocessorDesc", _schema_root("PpOptions")),
    ForbiddenTerm("ParseOptions", "ParserOptions", _schema_root("ParseOptions")),
    ForbiddenTerm(
        "AccessorRole.Get/Set/Ref",
        "AccessorRole.Getter/Setter/RefAccessor",
        re.compile(rf"{IDENTIFIER_LEFT}AccessorRole\.(?:Get|Set|Ref){IDENTIFIER_RIGHT}"),
    ),
    ForbiddenTerm("EnumUnderlyingType", "EnumTagType", _schema_root("EnumUnderlyingType")),
    ForbiddenTerm(
        "NestedConformance", "ConformanceRequirement", _schema_root("NestedConformance")
    ),
    ForbiddenTerm(
        "InterfaceContract", "InterfaceDecl<Typed>", _schema_root("InterfaceContract")
    ),
    ForbiddenTerm(
        "CheckedInterfaceDecl",
        "InterfaceDecl<Typed>",
        _schema_root("CheckedInterfaceDecl"),
    ),
)


def _display_path(path: Path) -> str:
    """Return a stable repository-relative path for diagnostics."""

    return path.relative_to(REPOSITORY_ROOT).as_posix()


def main() -> int:
    findings: list[tuple[str, int, int, str, str, str]] = []

    markdown_files = sorted(
        path
        for path in TYPE_SYSTEM_DIR.glob("*.md")
        if path.name != TERMINOLOGY_CHAPTER
    )
    for path in markdown_files:
        with path.open("r", encoding="utf-8") as stream:
            for line_number, line in enumerate(stream, start=1):
                for term in FORBIDDEN_TERMS:
                    for match in term.pattern.finditer(line):
                        if match.group(0) in ALLOWED_FORBIDDEN_MATCHES:
                            continue
                        findings.append(
                            (
                                _display_path(path),
                                line_number,
                                match.start() + 1,
                                match.group(0),
                                term.description,
                                term.canonical,
                            )
                        )

    if findings:
        for path, line, column, spelling, description, canonical in findings:
            print(
                f"{path}:{line}:{column}: forbidden terminology {spelling!r} "
                f"({description}); use {canonical}"
            )
        print(f"terminology validation failed with {len(findings)} finding(s)")
        return 1

    print(f"terminology validation passed for {len(markdown_files)} Markdown file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
