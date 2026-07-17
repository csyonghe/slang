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
  [compatibility ledger](13-compatibility-ledger.md).

This first edition is a formalization foundation for review, not a claim that every existing Slang
feature is already fully defined. The grammar, its exhaustive generated parsed-CST production
schema, and the core transformation/evidence algebras are concrete; rows marked open in chapter 13
and the remaining preprocessor/outline/AST/semantic portions of `NodeSchemaRegistry` explicitly block
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

The specification covers preprocessing as a complete immutable translation, including persistent
state and macro invocation expansion, because those rules determine concrete syntax and source
provenance. Target layout, optimization, and final code
emission are downstream of the frontend and out of scope, except for the contract imposed on
frontend IR.

## Representation pipeline

```text
SourceView { SourceFileRecord, decoded SourceFileSnapshot, interpretation }
  -> TokenList = NodeList<Token | Trivia>
  -> CSTSnapshot<Lexed> { TokenizedSource(elements: TerminalNode...) }
  -> initial CSTSnapshot<PreprocessorStructured>
     { directives, MacroDefinition, TokenPaste, text/inactive regions, ... }
  -> ordered preprocessing translation
     { persistent PreprocessorPersistentState plus transient PreprocessorState }
  -> PreprocessorExpansionResult
     { entryState, exitState, finalPersistentState, CSTSnapshot<MacroExpanded> }
     { MacroExpansion, TokenPasteExpansion, IncludeExpansion, ... }
  -> ParseDecls
     -> CSTSnapshot<DeclParsed>
        { declaration outlines, names, DirectGenericMarker, exact UnparsedContent }
  -> ResolveImportOutlines
     -> ImportResolutionIndex { outline-only imported module facts }
  -> WireLookupScopes
     -> ScopeWiring { scopes, declaration fragments, content entry positions }
  -> centralized demand-driven query graph
     { ParseAndCheckContent, LookupName/Member, CheckDeclHeader, ResolveOverload, ... }
     -> CSTSnapshot<Parsed> fragments plus node-local Surface / Typed forms
     -> node-local Elaborated forms
     -> node-local IRReady forms
  -> FrontendIR
```

Every pure arrow returns a total success/recovery result. A scheduler query additionally returns
`Blocked(dependencies)` when its semantic inputs are not yet available. No translation mutates its
input. Every CST output stores direct `CSTNodeOrigin` predecessor inputs, and every AST node stores
an `ASTNodeOrigin` identifying the exact prior nodes from which it was derived. The act of
translation is not materialized as an operation object.

Node forms are intentionally different types. A function accepting `TypedExpr` cannot receive a
`SurfaceExpr`, and IR lowering cannot receive a node that still contains unresolved overload sets
or implicit conversions. These types make no whole-file phase assertion: independently requested
nodes in one semantic snapshot may have different forms.

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
4. **Typed node forms.** Each checking query constructs a node in the next form and links it to its
   exact inputs. A query cannot mark an old node, declaration, or whole tree as checked.
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

| Document                                                                        | Contract                                                                                                                                      |
| ------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- |
| [00 — Terminology and implementation correspondence](00-terminology.md)         | Canonical Slang vocabulary, principled new terms, implementation anchors, and forbidden aliases                                               |
| [01 — Notation and conformance](01-notation.md)                                 | Grammar, algebraic-data-type, judgment, result, and rule-ID notation                                                                          |
| [02 — Lexical and syntactic grammar](02-syntax.md)                              | Source snapshots, tokens, trivia, declaration outlining, scope-directed fine parsing, ambiguity, and recovery                                 |
| [03 — Immutable representations](03-representations.md)                         | Terminal/non-terminal CST, direct provenance, node-local AST forms, reflection, editing, and serialization                                    |
| [04 — Preprocessing](04-preprocessing.md)                                       | Persistent state, directive semantics, macro invocation/expansion, includes, recovery, and provenance                                         |
| [05 — Semantic domains](05-semantic-domains.md)                                 | Names, declarations, types, values, substitutions, decl-refs, facets, and evidence                                                            |
| [06 — Names and declarations](06-names-and-declarations.md)                     | Scope wiring, lookup, imports, extensions, redeclaration, and visibility                                                                      |
| [07 — Expressions and statements](07-expressions-and-statements.md)             | Expression classifiers, property/subscript reference formation, statements, control context, and constants                                    |
| [08 — Calls, conversions, and generics](08-calls-and-generics.md)               | Coercion plans, overload resolution, argument mapping, generic deduction, and ranking                                                         |
| [09 — Interfaces and synthesis](09-interfaces-and-synthesis.md)                 | Conformance, requirement-keyed witness maps, associated types, defaults, and synthesis                                                        |
| [10 — Capabilities and visibility](10-capabilities-and-visibility.md)           | Capability DNF algebra, inference, availability, and visibility lattice                                                                       |
| [11 — Work scheduler](11-work-scheduler.md)                                     | Query model, dependencies, cycle policies, fixpoints, diagnostics, and incrementality                                                         |
| [12 — Elaboration and IR](12-elaboration-and-ir.md)                             | Explicit desugaring, checked function types, lambda/conformance synthesis, and IR contract                                                    |
| [13 — Compatibility ledger](13-compatibility-ledger.md)                         | Verified source map, open decisions, known gaps, and acceptance criteria                                                                      |
| [14 — Validation plan](14-validation.md)                                        | Unit-test seams, generated conformance tests, coverage, cross-frontend comparison, and fuzzing                                                |
| [15 — Subtyping, facets, and extensions](15-subtyping-facets-and-extensions.md) | Operational subtype witnesses, generic witness tables, facet routes, extension application, and partial lookup priority                       |
| [16 — Initialization and construction](16-initialization.md)                    | Initialization forms, strategies, aggregate shapes, constructors, definite initialization, and direct-to-destination lowering                 |
| [17 — Differentiability](17-differentiability.md)                               | Differential evidence, activity, derivative signatures/providers, interface dispatch, synthesis, and frontend-IR obligations                  |
| [Grammar source](grammar.ebnf)                                                  | Structural full/fine grammar baseline paired with the parsed-CST production profile                                                           |
| [CST production profile](cst-production-profile.json)                           | Machine-readable field naming, stable wire tags, category membership, and semantic production overrides                                       |
| [Declaration-outline grammar](decl-outline-grammar.ebnf)                        | Coarse `DeclParsed` grammar for declaration hierarchy, `DeclGroup` bindings, imports, active/inactive content, opaque regions, and containers |
| [Declaration CST profile](decl-cst-production-profile.json)                     | Machine-readable `DeclParsed` fields, categories, stable wire tags, and import-terminal roles                                                 |
| [CST production generator](generate-cst-production-schema.py)                   | Validates either explicit stage/profile pair and emits wire-stable typed product/variant registry descriptors                                 |
| [Rule manifest](rule-manifest.json)                                             | Generated machine-readable index of normative rule identities and locations                                                                   |

## What “fully defined” means

A feature is fully defined only when all of the following exist:

- concrete grammar productions and recovery behavior;
- a CST shape and a surface-AST shape;
- scope and binding behavior;
- typing, conversion, and elaboration judgments;
- explicit success and failure result types;
- interaction rules for generics, interfaces, visibility, and capabilities where relevant;
- an IR-ready node form and frontend-IR mapping, or an explicit statement that the feature is erased earlier;
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
- a centralized dependency scheduler implementing the cycle policies in chapter 11.

This design lets unit tests instantiate a five-node AST, a synthetic scope, or a mock standard
environment without constructing a compiler session, loading the core module, or running unrelated
checking phases.

## Review order

Review the representation pipeline and semantic domains before individual language rules. In
particular, settle these decisions first:

1. physical/preprocessed token provenance and inactive-code representation;
2. declaration-outline coverage, explicit lookup-scope wiring, and node-local AST form boundaries;
3. explicit receiver and parameter-mode representation in `FuncType`;
4. requirement-keyed, first-class generic witness values and lookup-spine algebra;
5. physical versus abstract storage and passing-mode access plans;
6. initialization target/result conventions and strategy policies;
7. differentiability participation, derivative signature maps, and provider policy; and
8. scheduler cycle classes and fixpoint domains.

Those choices constrain every later rule and are expensive to retrofit.
