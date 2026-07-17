# Slang frontend and type-system specification

This directory is the design contract for a replacement Slang frontend. It specifies the
language as a sequence of immutable representations and the relations that transform one
representation into the next. The intended end state is that syntax, name binding, type checking,
elaboration, synthesis, and initial IR generation are independently testable implementations of
rules in this directory.

The source baseline for the first edition is official `master` at
`4f4ec505761e2e56a45da873d5c169ff6e512f52` (2026-07-16). Existing behavior is evidence, not an
excuse to preserve accidental implementation details.

`SPEC-AUTH-001`: The current implementation is never a semantic authority merely because it is the
only implementation. A proposed rule must state an observable language invariant or an operational
transformation that downstream representations preserve. When current AST or checker structure
cannot express that invariant—for example, an l-value bit that cannot distinguish physical from
abstract storage, or a transitive witness that hides a witness-table lookup—the specification
replaces the structure and records compatibility separately. Implementation-shaped behavior is not
promoted into the language by copying its class hierarchy.

## Status and interpretation

This is a **proposed normative specification** for the replacement frontend. It has three kinds of
text:

- **Normative** text uses **must**, **must not**, **shall**, or a named inference rule. A conforming
  replacement frontend implements it.
- **Compatibility** text records behavior verified in the current compiler. Compatibility behavior
  remains provisional until accepted as a language rule.
- **Open** text identifies a decision for review. An open item is not permission for an
  implementation to choose silently; it must be resolved in the
  [compatibility ledger](12-compatibility-ledger.md).

This first edition is a formalization foundation for review, not a claim that every existing Slang
feature is already fully defined. The grammar, its exhaustive generated parsed-CST production
schema, and the core transformation/evidence algebras are concrete; rows marked open in chapter 12
and the remaining preprocessor/AST/semantic portions of `NodeSchemaRegistry` explicitly block
implementation freeze. The purpose of review is to accept or revise these representations before
expanding every feature row into rule-linked tests.

The existing language reference under [`docs/language-reference`](../language-reference/README.md)
describes user-facing Slang. The reverse-engineered material under
[`docs/generated/design`](../generated/design/README.md) is a useful implementation index, but is
auto-generated and explicitly allowed to drift. This directory is the hand-maintained semantic
contract that connects user syntax to checked representations and IR.

## Scope boundary

The language is defined by four inputs:

1. this core syntax and semantic specification;
2. a versioned **standard environment** containing builtin declarations, conversion declarations,
   operator declarations, capability atoms, and target facts;
3. a language-version and compatibility-mode configuration; and
4. the source module graph.

Treating builtins as declarations in a standard environment keeps the core rules finite and makes
them testable. A builtin is not a hidden type-checker branch unless a rule in this specification
explicitly classifies it as a primitive.

The specification covers preprocessing only where it affects the lossless token model, source
provenance, conditional activity, or parsing. Macro replacement rules remain aligned with the
preprocessor reference until they are formalized here. Target layout, optimization, and final code
emission are downstream of the frontend and out of scope, except for the contract imposed on
frontend IR.

## Representation pipeline

```text
SourceView { SourceFileRecord, decoded SourceFileSnapshot, interpretation }
  -> TokenList = NodeList<Token | Trivia>
  -> CSTSnapshot<Lexed> { TokenizedSource(elements: TerminalNode...) }
  -> initial CSTSnapshot<PreprocessorStructured>
     { directives, MacroDefinition, TokenPaste, text/inactive regions, ... }
  -> ordered preprocessing rewrites
     { PreprocessorState transitions plus structured MacroInvocation/argument fragments }
  -> PreprocessorExpansionResult { final state, trace, CSTSnapshot<MacroExpanded> }
     { MacroExpansion, TokenPasteExpansion, IncludeExpansion, ... }
  -> CSTSnapshot<Parsed>
     { production-specific NonTerminalNode fields and TerminalNode references }
     where every generated Token names a CSTRewrite output
  -> SurfaceAST
  -> ScopedAST
  -> BoundAST
  -> TypedAST
  -> ElaboratedAST
  -> IRReadyAST
  -> FrontendIR
```

Every arrow is a total transformation: valid input produces a value, and invalid input produces a
value containing explicit error/recovery nodes plus diagnostics. No stage mutates its input. Every
CST output records a `CSTNodeOrigin` whose rewrite inputs identify predecessor nodes/source, and
every AST node records an `Origin` that identifies the previous representation from which it was
derived. Synthesized AST nodes use `Origin::Synthesized`, naming the group, output role, and
semantic inputs that caused synthesis.

The stages are intentionally different types. A function accepting `TypedExpr` cannot receive a
`SurfaceExpr`, and an IR lowering function cannot receive a tree that still contains unresolved
overload sets or implicit conversions.

## Design invariants

The following invariants apply throughout this specification.

1. **Losslessness.** For the authoritative `TokenList` returned by `Lex`, concatenating the physical
   spellings of ordered `Token | Trivia` elements reproduces the decoded UTF-8 snapshot;
   `SourceFileRecord` separately preserves original encoded/BOM bytes for unmodified identity output. The
   `Lexed` and `PreprocessorStructured` CST snapshots cover directives and inactive regions; the
   `Parsed` snapshot covers active syntax, missing terminals, and skipped terminals. Token values
   remain owned by their lists, and identity formatting follows predecessor CST fields.
2. **Immutability.** Published tokens, CST nodes, AST nodes, types, substitutions, witnesses,
   diagnostics, and task results never change. Caches and scheduler state are not AST fields.
3. **Explicit semantics.** Resolved declarations, substitutions, receiver conventions, parameter
   directions, conversions, generic arguments, witnesses, effects, and capabilities are data, not
   implicit checker state.
4. **Typed stages.** Each checking boundary constructs a node in the next representation and links
   it to its origin. A phase cannot mark an old node as checked.
5. **Keyed evidence.** Conceptually unordered mappings, especially interface requirement
   witnesses, are keyed by stable requirement identity and are never interpreted by position.
6. **Determinism.** The same source snapshots, standard environment, options, and dependency
   versions produce byte-identical serialized results and diagnostics, independent of scheduling.
7. **Total error recovery.** An error is a first-class result with typed recovery data. Null, a
   partially initialized node, or an unchecked field is never the representation of failure.
8. **One semantic owner.** Each derived fact is produced by exactly one named query. Other rules
   request that query instead of recomputing or repairing the fact.
9. **Schema visibility.** Every node kind and field is described by the node schema. Generic tools
   can enumerate, compare, serialize, clone, and functionally replace operands without a
   kind-specific visitor. Every CST non-terminal exposes its terminal and non-terminal
   constituents as named typed fields; a generic operand list is only a projection of them.
10. **Rule-to-test traceability.** Every normative rule has a stable identifier and at least one
    positive, negative, boundary, serialization, and recovery test where those categories apply.

## Document map

| Document                                                                        | Contract                                                                                                                      |
| ------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------- |
| [00 — Terminology and implementation correspondence](00-terminology.md)         | Canonical Slang vocabulary, principled new terms, implementation anchors, and forbidden aliases                               |
| [01 — Notation and conformance](01-notation.md)                                 | Grammar, algebraic-data-type, judgment, result, and rule-ID notation                                                          |
| [02 — Lexical and syntactic grammar](02-syntax.md)                              | Source snapshots, tokens, trivia, staged preprocessing/grammar translations, ambiguity, and recovery                          |
| [03 — Immutable representations](03-representations.md)                         | Terminal/non-terminal CST and AST schemas, rewrite provenance, reflection, editing, serialization, and stage invariants       |
| [04 — Semantic domains](04-semantic-domains.md)                                 | Names, declarations, types, values, substitutions, decl-refs, facets, and evidence                                            |
| [05 — Names and declarations](05-names-and-declarations.md)                     | Scope construction, lookup, imports, extensions, redeclaration, and visibility                                                |
| [06 — Expressions and statements](06-expressions-and-statements.md)             | Expression classifiers, property/subscript reference formation, statements, control context, and constants                    |
| [07 — Calls, conversions, and generics](07-calls-and-generics.md)               | Coercion plans, overload resolution, argument mapping, generic deduction, and ranking                                         |
| [08 — Interfaces and synthesis](08-interfaces-and-synthesis.md)                 | Conformance, requirement-keyed witness maps, associated types, defaults, and synthesis                                        |
| [09 — Capabilities and visibility](09-capabilities-and-visibility.md)           | Capability DNF algebra, inference, availability, and visibility lattice                                                       |
| [10 — Work scheduler](10-work-scheduler.md)                                     | Query model, dependencies, cycle policies, fixpoints, diagnostics, and incrementality                                         |
| [11 — Elaboration and IR](11-elaboration-and-ir.md)                             | Explicit desugaring, checked function types, lambda/conformance synthesis, and IR contract                                    |
| [12 — Compatibility ledger](12-compatibility-ledger.md)                         | Verified source map, open decisions, known gaps, and acceptance criteria                                                      |
| [13 — Validation plan](13-validation.md)                                        | Unit-test seams, generated conformance tests, coverage, cross-frontend comparison, and fuzzing                                |
| [14 — Subtyping, facets, and extensions](14-subtyping-facets-and-extensions.md) | Operational subtype witnesses, generic witness tables, facet routes, extension application, and partial lookup priority       |
| [15 — Initialization and construction](15-initialization.md)                    | Initialization forms, strategies, aggregate shapes, constructors, definite initialization, and direct-to-destination lowering |
| [16 — Differentiability](16-differentiability.md)                               | Differential evidence, activity, derivative signatures/providers, interface dispatch, synthesis, and frontend-IR obligations  |
| [Grammar source](grammar.ebnf)                                                  | Structural first-edition EBNF baseline paired with the parsed-CST production profile                                          |
| [CST production profile](cst-production-profile.json)                           | Machine-readable field naming, stable wire-tag policy, category membership, and semantic production overrides                 |
| [CST production generator](generate-cst-production-schema.py)                   | Validates complete EBNF coverage and emits wire-stable typed product/variant `NodeSchemaRegistry` descriptors                 |
| [Rule manifest](rule-manifest.json)                                             | Generated machine-readable index of normative rule identities and locations                                                   |

## What “fully defined” means

A feature is fully defined only when all of the following exist:

- concrete grammar productions and recovery behavior;
- a CST shape and a surface-AST shape;
- scope and binding behavior;
- typing, conversion, and elaboration judgments;
- explicit success and failure result types;
- interaction rules for generics, interfaces, visibility, and capabilities where relevant;
- an IR-ready AST and frontend-IR mapping, or an explicit statement that the feature is erased earlier;
- stable rule IDs with validation cases; and
- a compatibility disposition: preserve, intentionally change, or unresolved.

A table of contents is not completeness. The compatibility ledger is the auditable checklist: a
feature remains incomplete while any required column is blank.

## Implementation strategy implied by the specification

The specification does not require a particular C++ class layout, but it does require observable
properties. The recommended implementation is generated from a declarative schema:

- closed node-kind enums and field descriptors;
- immutable arena-allocated nodes with structural sharing;
- typed wrappers over a uniform operand API;
- stable IDs rather than process pointers in semantic edges;
- versioned deterministic serialization;
- pure query implementations with explicit service dependencies; and
- a centralized dependency scheduler implementing the cycle policies in chapter 10.

This design lets unit tests instantiate a five-node AST, a synthetic scope, or a mock standard
environment without constructing a compiler session, loading the core module, or running unrelated
checking phases.

## Review order

Review the representation pipeline and semantic domains before individual language rules. In
particular, settle these decisions first:

1. physical/preprocessed token provenance and inactive-code representation;
2. the exact AST stage boundaries;
3. explicit receiver and parameter-mode representation in `FuncType`;
4. requirement-keyed, first-class generic witness values and lookup-spine algebra;
5. physical versus abstract storage and passing-mode access plans;
6. initialization target/result conventions and strategy policies;
7. differentiability participation, derivative signature maps, and provider policy; and
8. scheduler cycle classes and fixpoint domains.

Those choices constrain every later rule and are expensive to retrofit.
