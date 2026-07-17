# Validation and unit-test architecture

The replacement frontend is accepted rule by rule. End-to-end `.slang` tests remain valuable, but
they cannot substitute for direct tests of lookup, overload resolution, generic solving, coercion,
visibility, capability algebra, scheduler cycles, or lowering primitives.

## Rule manifest

Every normative rule ID is registered in a machine-readable manifest generated or checked alongside
these documents:

```text
RelativePathSegment = {
    text: Utf8String
    | text is NFC-normalized, non-empty, not "." or "..", and contains no slash,
      backslash, NUL, drive prefix, or URI scheme
}

RelativePath = {
    segments: NodeList<RelativePathSegment>
}

ImplementationLanguage =
    CppImplementation | SlangImplementation | PythonImplementation |
    GeneratedSchemaImplementation | RegisteredImplementation(QualifiedName)

SymbolRef = {
    language: ImplementationLanguage,
    artifact: RelativePath,
    name: QualifiedName,
    overloadDiscriminator: Option<ByteString>
}

TestHarnessKind =
    UnitHarness | SlangTestHarness | PropertyHarness | FuzzHarness |
    FrontendComparisonHarness | RegisteredTestHarness(QualifiedName)

TestSelector =
    WholeArtifact
  | NamedTest(name: QualifiedName)
  | DirectiveTest(ordinal: UInt32)

TestCaseRef = {
    harness: TestHarnessKind,
    artifact: RelativePath,
    selector: TestSelector,
    configuration: CanonicalArguments
}

RuleManifestEntry = {
    id: RuleId,
    title: Text,
    primary: (file: RelativePath, line: UInt32),
    definitionCount: UInt32,
    references: NodeList<(file: RelativePath, line: UInt32)>,
    implementation: NodeList<SymbolRef>,
    tests: NodeList<TestCaseRef>,
    status: Proposed | Accepted | Implemented | Verified,
    compatibility: Unclassified | Preserve | Mode | Change | New
}
```

`RelativePath` is repository-root-relative; the empty segment list denotes the repository root.
Its canonical display joins segments with `/`, but serialization is the count-prefixed segment
sequence and comparison is case-sensitive on every host. `SymbolRef` identifies an overload by its
full versioned canonical discriminator when a qualified name is not unique; a digest alone is not a
discriminator. `TestCaseRef` identifies the harness-visible test independently of a rendered command
line, and `configuration` records only semantic matrix parameters. The `artifact` in either record
has at least one segment. Absolute paths, environment variables, discovery order, and platform
separators therefore cannot enter the checked-in manifest.

[`rule-manifest.json`](rule-manifest.json) is the checked-in generated index, and
`generate-rule-manifest.py` deterministically refreshes it from the Markdown sources plus the
hand-maintained [`rule-annotations.json`](rule-annotations.json) overlay. During this design review
the overlay is empty, so every entry is `Proposed`/`Unclassified` with empty implementation/test
lists. Acceptance edits the overlay; regeneration preserves and validates that metadata instead of
overwriting it or inventing a separate rule identity.

`TST-RULE-001`: CI fails when a normative rule ID is absent from the manifest, duplicated, or has
no test after its status reaches `Implemented`.

`TST-RULE-002`: A feature cannot reach `Verified` while any applicable test category below is
missing. “Not applicable” is an explicit reviewed value, not an empty list.

## Test categories per rule

Where meaningful, each rule has:

- **positive** — the smallest successful input;
- **negative** — each distinct premise failure and diagnostic code;
- **boundary** — empty, one, maximum, nesting, and numeric limits;
- **interaction** — generic/interface/visibility/capability/error combinations;
- **recovery** — output node/fact after an error and cascade suppression;
- **serialization** — round trip and deterministic bytes;
- **incremental** — an edit that should and should not invalidate the fact;
- **property** — algebraic law, determinism, or generator invariant; and
- **differential** — old frontend comparison when compatibility is `Preserve`.

Tests cite rule IDs in metadata. Rule coverage is computed from that metadata rather than guessed
from filenames or line coverage.

## Test kernel

The unit-test library exposes builders for each immutable domain:

```text
TestSourceFixture = {
    record: SourceFileRecord,
    snapshot: SourceFileSnapshot,
    view: SourceView
}

TestSource::fromBytes(bytes, encoding) -> TestSourceFixture
TestTokens::fromElements(Token | Trivia...) -> TokenList
TestTokens::view(TokenList, TokenListSelection) -> TokenListView
TestCST::terminal<S>(value, origin) -> TerminalNode<S>
TestCST::nonTerminal<S, K>(kind, namedFields, origin) -> NonTerminalNode<S, K>
TestCST::rewrite(rule, typedOperation) -> CSTRewrite
TestCST::snapshot<S>(root, terminals, nonTerminals, predecessors...) -> CSTSnapshot<S>
TestAST<S>::node(kind, fields...) -> ASTSnapshot<S>
TestSemantics::type(...), decl(...), scope(...), witness(...)
FakeQueryContext::given(key, result)
FakeStandardEnvironment::withDecls(...)
```

Builders validate the same schema as production code and assign deterministic synthetic IDs. A
`TestSourceFixture` satisfies `record.decoded = ContentId(snapshot)` and
`view.key.snapshot = record.decoded`. A
test that needs two overload candidates should not load the core module, construct a linkage, parse
a file, or run declaration checking unless that dependency is the subject of the test.

Diagnostics are collected values. Tests compare structured code, arguments, rule ID, and origins;
rendered English text has a separate snapshot suite.

## Dependency isolation and mocks

Each query or semantic service lists its dependencies in its public constructor/signature. Tests
supply small fakes:

| Subject                      | Mocked dependencies                                                                                          |
| ---------------------------- | ------------------------------------------------------------------------------------------------------------ |
| lexical classification       | source snapshot and language options                                                                         |
| preprocessor structuring     | `CSTSnapshot<Lexed>`, `PreprocessorOptions`, rewrite publisher                                               |
| macro/include expansion      | structured CST, `PreprocessorState`, fake versioned `IncludeSystem`, paste lexer, rewrite publisher          |
| parser production            | terminal reader over `ActiveTokenView`, `GrammarVocabulary`, `SyntaxParseInfoSet`, recovery/rewrite sink     |
| lookup                       | immutable scope graph, facet provider, access predicate                                                      |
| facet closure/priority       | typed aggregate relations, witness-route provider, extension applicability, priority proofs                  |
| visibility                   | declaration facts, module/container relation, extension target equality                                      |
| coercion                     | canonical types, standard conversion declarations, relation-specific evidence providers                      |
| overload resolution          | candidate list, signatures, argument mapper, generic solver, coercion planner                                |
| generic solver               | constraint set, type equality, conformance provider, constant evaluator                                      |
| conformance                  | requirement list, member lookup, signature comparer, synthesis planner                                       |
| initialization               | initialization model, candidate provider, conversion/call planner, storage and definite-initialization facts |
| differentiability            | differential-info provider, signature transformer, derivative candidates, activity facts                     |
| effect inference             | direct-effect uses, declared contracts, local/imported callee facts                                          |
| capability inference         | atom graph, direct-use facts, callee requirements                                                            |
| expression checking          | bound children and the narrow primitive queries the node rule requests                                       |
| property reference formation | typed abstract/physical storage, accessor target, call/access planner, registered-operation validator        |
| IRReady lowering             | canonical semantic values, imported symbol resolver, IR fragment builder                                     |

Mocks return real domain values, not booleans that bypass invariants. For example, a mock coercion
provider returns a `ConversionResult` with plan, rank, and witness; a mock conformance provider
returns a `WitnessTableSearchResult` referring to immutable identity/definition facts.

`TST-MOCK-001`: A unit test asserts both its result and the exact dependency requests made. An
unexpected dependency fails the test, exposing hidden coupling early.

## Lexer and lossless syntax tests

Required direct lexer/CST suites include:

- every token kind and invalid-token path;
- every literal base, suffix, separator, escape, raw string delimiter, and overflow boundary;
- whitespace, newline convention, line continuation, ordinary/doc comments, and malformed comments;
- logical tokens whose contiguous physical spelling records exact removed line-continuation ranges;
- rejection of absent physical spelling with nonempty continuation ranges and of copied spelling
  whose continuation metadata is dropped, reordered, overlapping, or out of bounds;
- exact flat `Token | Trivia` source partition and identity-format round trip;
- token-only, trivia-only, semantic, markup, and active-token view projection, composition,
  stable `(list, index)` identity, immutability, and serialization;
- `TokenSpan` empty/end/bounds behavior and selected-index-to-base-index resolution under every
  filter, plus rejection of incomplete or wrong-list `TokenActivityMap` values;
- `TokenReader` `peekToken`/`advanceToken`/`isAtEnd` behavior, `ParsingCursor` restore on the same
  view, rejection across different views, and rejection of any trivia-containing view;
- contextual `tokenFlags` at list start, after whitespace/comments/newlines/line continuations, at
  EOF, and after sharing the same token into a differently contextualized list;
- adjacency-derived leading/trailing/documentation trivia with no stored gap authority;
- BOM, decoded encodings, source maps, `#line` logical locations, and rejection of self/descendant
  `SourceView` predecessor anchors;
- active versus inactive `#line`, macro-expanded line operands, final interpreted-view construction,
  and `BuiltinLine`/`BuiltinFile` observation of the exact logical-location state without a lex-time
  directive prescan;
- `BuildLexedCST` bijection with its exact `TokenList`, plus
  `StructurePreprocessor`/`ExpandPreprocessor` rejection of snapshots paired with the wrong
  view/options/state or include-system revision, including inherited child options;
- total stage-specific `terminalKind`/`terminalClass` round trips for every admitted terminal value,
  including rejection of an ID or record whose cached kind disagrees with its value class;
- zero-width `MacroInvocationArg` and grammar-production rewrites with exact `Empty` anchors,
  distinguishing `Before`, `After`, `EndOfInput`, and `SourceAnchor` and rejecting a fabricated
  consumed terminal;
- literal decoding as a pure `(TokenRef, LanguageRuleSetId)` query, including every radix/format,
  suffix, escape failure, macro-pasted spelling, and cache-key distinction;
- direct-source, replacement-body, repeated-parameter-occurrence, prescanned-argument,
  unexpanded-argument, and nested macro CST rewrite chains plus `BusyMacro` suppression linked to
  the exact blocking invocation;
- nested macro-output recognition where `PreserveTerminal(..., PreprocessorStructured)` bridges
  each terminal to the new stage while its `TokenOrigin` remains the earlier macro output, rejecting
  a direct wrong-stage origin binding and any non-terminal or bare source-range preserve input;
- direct active/inactive `TextRegion` token and trivia terminals bridged into the `MacroExpanded`
  primary list in exact interleaved order, with unchanged token origins/trivia values, correct
  activity, and no accidental directive-terminal leakage into active views;
- `Suppressed` and recovered `Failed` macro outcomes whose verbatim tokens are produced by the exact
  `ReplayMacroInvocationResult` projection, preserving each token value/origin while giving each new
  terminal its replay origin; interleaved nested/recovery outputs must reproduce the rescan trace,
  and a missing, duplicate, reordered, anonymous, or mismatched-decision replay is rejected;
- `FunctionLike` including zero parameters, `ObjectLike`, and source-less `BuiltinObjectLike`
  definitions; named, named-variadic, and `...`/`__VA_ARGS__` parameters; every legal and illegal
  `MacroDefinition::Opcode`/`MacroDefinition::Op` pair; name/field/argument-map invariants;
  the definition distinction between `#define F(x)` and object-like `#define F (x)`; accepted trivia
  between a resolved function-like invocation name and `(`; cross-definition rewrite rejection; and
  source-token/output spelling equality;
- stringization from exact argument `Token | Trivia`; token paste with two/one/zero/invalid operands,
  chained `X ## Y ## Z`, an empty middle operand, and trivia-like `/ ## *`; variadics,
  `BuiltinLine`/`BuiltinFile`, includes, and synthesized tokens;
- traversed (including a macro-produced child token), `#pragma once`-suppressed, pre-resolution
  failed, and `Failed(Cycle, error)` include edges with no fabricated view/list, including rejection
  of a traversed include back to an ancestor expanded snapshot and rejection of wrong directive,
  predecessor, initiating-range, included-root, or resolved-identity links;
- traversed-include `includedInputs` equality with `IncludedContentView`'s active non-EOF terminal
  projection; interleaved `tokenResult`/`triviaResult` output reconstruction; token
  type/logical-spelling/physical-spelling/continuation copying; exact trivia copying; and retention
  of the child EOF without inserting it into the parent list, rejecting wrong count, order, input,
  class, or output metadata;
- ordered state replay where an include defines or undefines `M` before a parent-file use, an
  inactive definition does not mutate the environment, conditional/busy/input stacks push and pop
  without leakage, pragma-once identities and loaded source versions propagate, and identical text
  is recognized differently under two immutable `PreprocessorState` values;
- deterministic physical-source, invocation, definition, primary-anchor, and full-trace provenance
  projections, including left/right branch preorder and first-visit deduplication; exact
  `CSTProvenanceTrace` closure/role equations; DAG acyclicity; and copy/serialization round trips;
- active and inactive conditional regions;
- exact initial `Lexed -> PreprocessorStructured`, dynamically recognized structured-fragment,
  and final `MacroExpanded -> Parsed` predecessor links; per-token rewrite roots; lexed and
  macro-expanded primary terminal-projection coverage bijections; structured-stage predecessor-list
  retention without duplicate trivia terminals; and parsed active-token coverage;
- a `TokenizedSource` whose terminal fields are in one-to-one list order with every `Token | Trivia`
  element, and rejection of an anonymous/parallel child authority;
- `DefineDirective`, `MacroDefinition`, parameter/argument clause and comma-tail nodes,
  `MacroInvocation`, `MacroInvocationArg`, and `TokenPaste` non-terminals with all
  keyword/operator/delimiter/separator terminals in named fields and exact interleaved operand order;
- `MacroExpansion`, chained `TokenPasteExpansion`, and `IncludeExpansion` nodes whose
  `expandedFrom` fields reach the exact predecessor non-terminal and whose ordered `result` fields
  agree with the rewrite outputs;
- whole and sliced `>>` token coverage, including exact `SplitToken` predecessor, partition, and
  output-ordinal validation;
- every grammar production in isolation;
- every EBNF choice as one closed, wire-tagged variant with exactly one selected alternative, never
  as a product that requires every alternative's fields;
- every repeated sequence as one ordered list of element products, including delimiter/value pairs,
  never as parallel component lists;
- `IfStatement` with exact `ifKeyword`, `leftParenthesis`, `conditionExpr`, `rightParenthesis`,
  `trueBranch`, optional `elseKeyword`, and optional `falseBranch` fields; wrong keyword,
  delimiter, category, or unmatched else-pair rejection; and equality between generic operand
  enumeration and typed field order;
- property/subscript accessor blocks containing `constref`, `ref`, and both spellings; normalization
  to distinct `AccessorRole.RefAccessor(ReadAccess)`/`Ref(ReadWriteAccess)` keys; exact-role duplicate
  diagnostics; and round trips preserving declaration order without using that order as identity;
- disambiguation of unbracketed accessor `constref`, parameter `__constref`, and receiver
  `[constref]`, including recovery at each production boundary and CST-to-Surface normalization;
- each ambiguous CST form and its later binding resolution;
- every production recovery set, missing terminal, skipped-token non-terminal, unexpected
  construct, field/kind mismatch rejection, and progress guarantee;
- `CSTCursor` parent/path/range behavior for repeated or shared-equal node records; and
- incremental reparse sharing without conflating distinct occurrences.

The parser/preprocessor schema has three generated completeness tests:

1. every `NonTerminalKind<S>` at every `CSTStage` must be constructible by at least one lexical,
   preprocessing, expansion, grammar, or recovery rule;
2. every terminal/non-terminal occurrence in every production must have a unique field name,
   declared cardinality/category, and generated source-order position; and
3. every grammar production must have at least one positive token sequence and one generated
   single-terminal deletion/insertion recovery case.

The second test is executable now:

```text
python docs/type-system/generate-cst-production-schema.py
```

The command parses the EBNF, validates its pinned canonical UTF-8/LF digest and terminal vocabulary,
resolves every explicit selector, generates every typed production shape, and checks the exact
seven-field `IfStatement` contract. It also has executable sentinels proving that `declaration` is a
closed variant and that the repeated suffix of `dotted-name` is a list of ordered
`{ dot, identifier }` products. Generation validates the `{ major, minor }` schema version, derives
non-zero wire tags for every kind/field/group/alternative, and rejects tag collisions. `--emit`
writes the complete `NodeSchemaRegistry` fragment to standard output; `--production if-statement`
emits one descriptor for focused review and unit-test fixtures.

## Schema and immutable representation tests

Generated tests iterate every node descriptor and verify:

- typed fields and generic fields enumerate identical values;
- every parsed production's `NonTerminalFields` matches `compileShape(descriptor.shape)`, with
  products in descriptor order, exactly one selected variant tag/payload, explicit optional
  presence, and complete repeated-product elements;
- recursive CST serialization and generic traversal agree at every product/variant/optional/list
  boundary, including `comma[0], argument[0], comma[1], argument[1]` rather than parallel lists;
- every `CSTCategoryDescriptor` accepts exactly its registered production members and cannot be
  constructed as a concrete occurrence, including a production in multiple categories and
  rejection of non-injective `grammarProductions` kinds;
- `nodes[production.kind]` equals the descriptor generated from `compileShape`, direct group fields
  are the sole serialized authority, and every nested leaf uses the exact generated
  `CSTShapeProjectedField` and `projectedCSTFieldKind`;
- `NodeKindValue` checks exact, acyclic `baseKind`, and category-membership cases; abstract category
  and terminal-family kinds never enter `stageKinds` or acquire constructors;
- `terminalKinds` is total and injective for each stage's admitted `TerminalClass` values, and its
  generated inverse rejects the wrong family or stage;
- each CST non-terminal's generic operands are derived exactly from its named structural fields,
  with no anonymous child list or omitted punctuation terminal;
- structural/alternative/semantic/provenance edge filters are correct;
- `withCSTField` requires a rule, creates a `FunctionalCSTEdit` predecessor edge, and leaves the old
  snapshot byte-identical; `replacementOf` round trips scalars, CST/schema references, products,
  variants, optionals, lists, non-empty lists, and maps without hiding node inputs; its canonical
  replacement distinguishes different edits; origin and rewrite-projected fields are read-only,
  and preserving the old origin while changing a field is rejected;
- non-root `withCSTField` edits remain reachable from the returned root after canonical reindexing;
  identity edits update every intentional alias, while `withCSTCursorField` clones/rewires only the
  selected alternative occurrence;
- `withField` creates a new node and leaves the old snapshot byte-identical;
- invalid field kinds, presence, or collection shapes fail before publication;
- generic rewrite identity preserves structural hashes;
- serialization round trips every optional/variant field;
- `DerivedField`, `CSTShapeProjectedField`, and `CSTRewriteProjectedField` each expose their complete
  declared dependency class; rewrite output projections reconstruct from serialized
  `outputBindings` and reject the wrong operation/path/class;
- unknown optional fields survive schema-version round trips; and
- unknown required fields fail atomically, forward/SCC graph references round trip, and golden files
  migrate through every supported wire version;
- every staged CST rewrite round trips with its predecessor snapshot IDs and rejects forward,
  dangling, wrong-role, wrong-stage, or cyclic provenance inputs; output resolution also rejects an
  unknown port, wrong output class, or ordinal at/above the declared dynamic count;
- snapshot output bindings reject a missing/duplicate inverse, wrong local node, wrong
  terminal-class/non-terminal-kind, mismatched token/terminal origins, or ambiguous predecessor
  realization; `resolveOutput` returns the exact bound occurrence;
- canonical CST snapshot encoding omits its own ID, uses unique local indices with matching
  terminal-kind/non-terminal-kind tags, gives equivalent trees built in different allocation or
  scheduler orders the same ID, and rejects unreachable records, a wrong root class, or
  noncanonical array order;
- atomic preprocessor transitions replay their typed effect exactly; scoped macro/include steps
  require matching enter/leave effects, a valid nested state chain, and only the declared outward
  state changes;
- copy/share counts and snapshot lifetime do not affect equality or serialization.

Every node kind receives a minimal valid fixture. This is type coverage independent of which
end-to-end language tests happen to create the node.

## Semantic primitive suites

### Substitution and types

- identity, associativity, shadowing rejection, and capture avoidance;
- substitution through every type, function receiver, parameter, constraint, and witness field;
- working-key to alpha-normalized `SpecializationFrame` freezing and proof-relevant evidence
  preservation;
- nominal versus structural equality;
- canonicalization idempotence and deterministic interning;
- recursive nominal identity versus rejected structural alias cycles; and
- kind mismatch and error recovery.

### Lookup and visibility

- lexical shadowing and overload accumulation at every scope kind;
- imports, exported imports, reopened namespaces, transparent members, bases, and extensions;
- route-keyed facet closure, path-distinct diamonds, all partial-priority outcomes, and one
  `LookupSubtypeWitness` per refinement route step;
- lookup ambiguities retain an endpoint-correct comparison for every pair of maximal candidates,
  while legal overload pairs remain `Found`;
- `Private < Internal < Public` meet laws;
- access from same/different type, namespace, extension, file, and module;
- generic specialization and composite-type effective visibility; and
- language-version defaults and synthesized-member caps.

### Conversion and overload resolution

- one unit case for every conversion constructor and `ConversionFailure`;
- primitive, local-user, imported-user, and nested conversion plans preserve and deduplicate their
  exact effect/capability use edges through access-plan and typed-expression collection;
- `extendRank` identity/associativity/monotonicity, overflow failure, and search dominance;
- rank ordering, irreflexivity/transitivity of `strictlyBetter`, antisymmetry after quotienting by
  `SemanticallyEquivalent`, and stable equal-rank ambiguity;
- argument arity, labels, defaults, variadics, direction/storage requirements, and receiver matching;
- generic and non-generic candidates, explicit/partial generic application, and defaults;
- each tie-break rule isolated from all later rules;
- “best failed candidate” diagnostic ranking isolated from semantic applicability; and
- error arguments suppress cascades without making an error candidate outrank a valid candidate.

Passing-mode tests use a direct cross-product of builtin fields/arrays/pointers, getter-only and
setter-only properties, access-indexed reference-accessor properties, declared subscripts,
swizzles, resources, temporaries, and rvalues against `InMode`, `OutMode`, `InOutMode`,
`ConstRefMode(r)`, and `RefMode(r)` for every location-contract variant. They assert physical
versus abstract classification, single evaluation, access/effect requirements, lifetime failures,
address-space and source-provenance admission, allowed write-back, and that neither physical
reference mode manufactures storage through a value conversion or getter/setter plan.

Argument-planning unit tests construct `ArgumentPlanningContext` directly and independently mutate
its callable signature, `CallInput`, `ArgumentMap`, conversion environment, access environment,
expression context, authenticated operation site, slot, and typed binding alternative. Each
projection mismatch selects its exact `ArgumentPlanningContextFailure`; no ambient test harness
state repairs it. `PlanArgumentAdaptationAt<S>` is mocked with all three `ConversionResult`
alternatives and both outer `CheckResult` alternatives: only an applicable conversion may inhabit
`AbstractConversion`, and only nested successful adaptation plus access results create a candidate
slot. Dependency tests leave each child query pending in turn and require scheduler blocking rather
than a fabricated semantic failure.

Ranking mutation tests replace `StorageAccessPlan.rankingCoercion` independently with `None`,
`AppliedStorageCoercion`, and each `ConsumedWithoutStorageCoercion(rule)`. Candidate validation derives
exactly one `SourceAdaptationRank` from that stored value, rejects `None`, and admits
`PhysicalParameterIdentityPassingRule` as the sole conversion-free physical-mode rule. No parallel
rank field or conversion plan is accepted. Alias-rejection fixtures round-trip the complete
`ConflictingCallAliasClaims` through `AliasClaimConflict`, mutate each claim, slot, overlap reason,
and versioned rejection rule independently, and prove that a disjointness result cannot inhabit a
conflict payload.

The `__constref` matrix contains, at minimum:

- header normalization maps `__constref` to `ConstRefMode(r)` with
  `mode.domain = PhysicalOperand(r)` and `mode.access = ReadAccess`, while `__ref` maps to
  `RefMode(r)` with `ReadWriteAccess`; changing either structural axis fails
  function-type validation;
- an exactly typed physical storage satisfying the complete instantiated `r` succeeds without a
  temporary and remains `isPhysicalStorage = True` through Typed, IRReady, IR, and the callable ABI;
- mutable physical storage may satisfy `ConstRefMode(r)` through a read-only provision proof, but
  the selected argument cannot gain write access from the underlying location's stronger access;
- mutable and immutable stored variables are crossed with both physical modes: each readable
  location may satisfy `ConstRefMode`, while `RefMode` succeeds only when effective access provides
  `ReadWriteAccess`; mutability and access failures retain distinct reasons;
- an rvalue, literal, computed value, temporary materialization proposal, nonidentity conversion,
  getter-only, setter-only, getter-plus-setter property/subscript, and ordinary abstract storage
  without the exact reference-accessor key each fail with their distinct structured premise
  failure;
- a property or subscript with a declared `constref` accessor evaluates its receiver and indices
  once, selects exactly `AccessorRole.RefAccessor(ReadAccess)`, validates the returned reference/location
  certificate, and passes the resulting physical location without loading its value;
- accessor-produced physical-parameter fixtures pair the retained plan with the exact typed
  `AbstractStorage` source and authenticated slot site. Replacing that source with an equal-classified
  sibling, validating against the enclosing call node, changing the slot ordinal, or reusing a
  sibling slot's site is rejected before lowering;
- a property or subscript having only `get`, only `ref` (`AccessorRole.RefAccessor(ReadWriteAccess)`), or an
  optional/absent `constref` accessor does not satisfy `ConstRefMode`; no access-strength
  substitution, ordinary-read fallback, or getter-to-temporary recovery is attempted;
- properties/subscripts declaring both `constref` and `ref` retain both keys through requirement
  signatures, `RequirementDictionary` values, adapters, serialization, and runtime witness-entry projection; lookup
  selects the exact requested role independently of declaration order;
- exact, one-of, generic, and standard-referenceable address-space requirements are crossed with
  allowed and forbidden storage address spaces, while `AnyPhysicalStorage` and every registered
  source-provenance requirement are crossed with matching and mismatching roots;
- `__constref groupshared` fixtures require the exact groupshared address-space proof, and a
  varying-input-only intrinsic accepts only a root carrying its registered source fact; an unrelated
  readable location with the same value type is rejected, while projections preserve or transform
  that fact only through their registered component rule;
- a physical formal with `AnyReferenceableAddressSpace` or unresolved `OneOfAddressSpaces` may be
  forwarded to a compatible physical parameter but cannot form a first-class pointer/reference;
  exact and generically specialized-to-exact formals succeed only with the corresponding
  `ConcreteAddressSpaceProjectionProof`, and no case chooses a representative address space;
- builtin physical subscripts with read-only and read-write storage results are crossed with both
  modes: the former can satisfy only `ConstRefMode`, while the latter may satisfy either mode under
  its complete requirement. An explicit dereference is likewise admitted only from its already
  checked physical result and never from the undereferenced handle value;
- direct and accessor-produced locations preserve their proven location identity, lifetime,
  address space, source provenance, and alias root; overlapping const-reference reads are compatible
  by rule, while read/write and write/write overlap replay the exact registered alias/access-
  discipline policy, with both allowed and rejected fixtures for every outcome the policy exposes;
- within the callee, read and read-only physical projections succeed and continue to report
  `isPhysicalStorage = True`; writes and forwarding as `RefMode`, `OutMode`, or `InOutMode` fail,
  and forwarding as another `ConstRefMode(r2)` succeeds only when the original proof entails the
  complete instantiated `r2`; and
- storing, returning, capturing, or otherwise escaping the physical location beyond its admitted
  lifetime fails. No successful or recovery path contains temporary allocation, initialization,
  destruction, write-back, value load, or a nonphysical storage ABI alternative.

Mutation tests independently exchange the accessor role, physical-location identity, access proof,
location requirement, address space, source provenance, lifetime, alias root,
`AccessEnvironmentId`, IRReady category, IR operation, ABI input alternative, and call-local admission
proof. They also inject a getter, value conversion, load, temporary, nonphysical category, or
write-capable use. Each mutation must fail validation rather than being repaired by lowering.
Const-reference projection fixtures cover stored fields, builtin indexing, vector elements, and
registered read-only physical projections with zero, one, and multiple runtime indices. Every
success preserves the physical base's location proof and derives the projected physical location,
read access, lifetime, address space, provenance, and alias by the registered projection rule; no
projection may erase `isPhysicalStorage`, mint write permission, or reconstruct an operand from a
later IRReady/IR result.
Alias-algebra unit tests exhaust the exact/exact, exact/joined, joined/joined, and unknown cases of
`CompareAliasOverlap`, including symmetry and canonical common-region selection. Call-level tests
then cross disjoint, shared-read, exclusive, read-only-reference, write-capable-reference, and
atomic-discipline claims. They assert the exact `AliasPairCompatibilityProof` or structured pair
conflict and mutate each root set, access kind, rule identity, and slot order independently.
Physical-reference fixtures independently instantiate `InvocationExtent` and
`DeclaredMinimumLifetime`, separate
access-plan cache keys by invocation lifetime, and cover exact, listed, standard-referenceable, and
generic address-space requirements. Every success/failure retains the exact instantiated
requirement and admission proof; no test reconstructs it from access mode alone. A successful
`PhysicalParameterBindingProofAt<S>` additionally retains the exact storage/parameter value-type
equality, source-provenance proof, and `AccessEnvironmentId`; its access plan records the
conversion-free `PhysicalParameterIdentityPassingRule` and no `ConversionPlan`. The matrix runs
once with `ConstRefMode`/`ReadAccess` and once with `RefMode`/`ReadWriteAccess`. Mutating any
equality endpoint, substituting a recovery proof or any conversion, or passing the proof under
another call environment is rejected.

Reference-formation fixtures separately cover `EXP-REF-001`, `EXP-REF-002`, `EXP-REF-003`,
`EXP-REF-004`, `EXP-REF-005`, `EXP-REF-006`, `EXP-REF-007`, `EXP-REF-008`, `EXP-REF-009`, and
`EXP-REF-010` through `EXP-REF-016`. Cases include a selected registered builtin address operator and `__getAddress` on
physical storage; explicit property/subscript reference through a valid accessor; missing,
inaccessible, wrong-referent, insufficient-access, short-lifetime, forbidden-address-space,
source-amplification, argument-mapping/passing, effect, concrete-region, and missing-rule failures.
Policy fixtures independently vary handle kind, direct/accessor strategy, evaluation versus expected
lifetime, symbolic address-space predicate, inferred capability use, and concrete availability.
They prove that user-defined `operator&` remains an ordinary call and that an expected physical
reference mode cannot
create or weaken a policy. Every checked result stores the resolved policy; deserialization tests
mutate its syntax, strategy, requirement, lifetime proof, or availability proof without rerunning
resolution. Registered physical resource projections are positive `__ref` cases;
declared properties/subscripts remain negative direct-`__ref` cases. Dereference fixtures likewise
require the selected registered standard prefix candidate; a user-defined `operator*` remains an
ordinary typed call and cannot enter `CheckDereferenceAt<S>` from token spelling alone. They set the
handle and expression-context lifetimes independently, require every successful result storage to use
the context's exact `evaluationLifetime`, and require the source-lifetime proof to have those exact
endpoints; a shorter handle selects `DereferenceLifetimeExpired(actual, required)`. Every
successful case also derives a stage-free `DereferenceApplicationIdentity`, retains the exact
executable handle separately, and carries `DereferencedReference(identity)` through Typed, IRReady,
and IR forms. Tests
replace the identity with the handle `NodeId<Typed>`, a sibling dereference identity, and the later
IRReady/IR producer ID; drop or replace the handle operand; and independently mutate every
`DereferencedStorageProof` endpoint. The matrix is repeated for an internal ref-accessor read/write
fallback, whose identity is derived from the accessor invocation rather than an otherwise
nonexistent dereference-expression node.
Registered-operation negative cases independently vary static-input arity/sort/value, runtime
input/result count, endpoint type/category, handle/storage shape, and throwing/control shape; a
schema version embedded in the rule ID is never used as the application failure.

Registered physical-projection fixtures independently vary standard-environment ID, rule/static
inputs, source-only site assignment, optional base, zero/one/multiple indices, endpoint access
plans, and written evaluation order. A success retains executable base/index expressions and
evaluates each exactly once through
Typed, Elaborated, IRReady, and IR forms. Negative tests drop, duplicate, reorder, or replace one
runtime operand; mutate registered result type, path identity, or each access/mutability/lifetime/
address-space/alias derivation; and substitute an ordinary data operation with the same target
opcode. Construction stores only the intrinsic `RegisteredPhysicalProjectionResultProof`.
Read/write/physical-reference-mode/initialization/address tests then create distinct use-specific
`PhysicalStorageProof` values without changing the projection's classifier, content identity, or
serialized IRReady/IR descriptor. Round trips require the IR operand order and role-to-shape map to
replay the exact registered application without an AST or reconstructed base path.

Builtin physical-element fixtures independently vary the physical base, converted runtime index,
named builtin rule, result type, path, alias derivation, and written base-then-index order. A
success retains exactly one `BuiltinPhysicalProjectionApplicationAt<S>` and lowers one-to-one
through Elaborated, `IRReadyBuiltinPhysicalProjection`, and
an instruction carrying `BuiltinPhysicalProjectionInstPlan`. Round trips assert that
`BuiltinElement(inputStorage.path, identity)` contains no `NodeId<Typed>`, while the application and
IRReady/IR operation still carry both executable operands and the complete result proof. Negative
tests drop, duplicate, reorder, or exchange equal-typed operands; substitute the index node ID,
IRReady value ID, or IR instruction ID for the stable identity; mutate the base path or any storage
component; and retag the application as a registered projection or generic data operation. Every
mutation fails instead of triggering path-based operand reconstruction.

Semantic-operation-site tests cover parsed multi-range/macro origins, same-range occurrences,
source-rooted synthesized paths, imported, source-only recovery, and nested implicit roles. They
mutate the frozen assignment context, source
range, occurrence, parent, role, ordinal, and request origin independently; reuse an assignment on
a sibling; and verify that builtin, registered, dereference, const-reference-accessor, and
accessor-invocation constructors produce distinct nominal identities. Synthesized-anchor mutation
tests attempt to embed a `SynthesizedSemanticId`, `SynthesisKey`, or syntax-node cause; recovery
tests attempt to embed `ErrorId` or its semantic diagnostic anchor. All are rejected transitively,
as are direct `StableSemanticId`, `NodeId<Typed>`, IRReady value, and IR instruction substitutions.
Index tests publish the exact content-addressed internal storage plans and
their scheduler-query dependencies, then reject duplicate identities, missing/extra plans,
non-bijective dependencies, unresolved owners, wrong application kinds, and identity mismatches.
Round trips require `StoredRoot(DeclRef)` and reject a `BoundDeclUse`, lookup path, access
decision, witness sidecar, origin, or AST ID in every transitive IRReady/IR storage proof.

The matrix covers declared and registered accessor availability; exact direct/witness/dynamic/
builtin dispatch; recursive accessor calls that retain pre-inference `TypedCallAt.Selection`; and
later contract completion through the ordinary call path. It includes instance, static, zero-index,
multi-index, and pack-expanded accessors. It verifies capture-once receiver/index order, multiple
expansion projections from one captured pack, dense capture-result IDs, each source-binding's exact
slot/operand/evaluate-once step, each keyed access recipe and cleanup, exact referent/
access/lifetime/address-space/alias proof endpoints, and serialization without fresh lookup,
mapping, conversion, or contract inference. It also asserts that the original property remains an
abstract storage: a physical mode succeeds only when planning selects and retains the exact declared
reference-accessor route. `ConstRefMode` requires `AccessorRole.RefAccessor(ReadAccess)`, while `RefMode`
requires `AccessorRole.RefAccessor(ReadWriteAccess)`; neither key substitutes for the other. Each route
invokes the accessor and its stored dereference exactly once to produce the proved physical
endpoint, without reclassifying the original property. Each stored semantic-use edge enters inference
exactly once. Separate
store/load, copy, argument, return, and control-flow-merge cases mutate each handle-provenance field
and verify preservation, canonical alias join, or a structured failure; equal `TypeId` alone never
authorizes dereference.

Accessor-result contract tests mutate selector, signature, result type, referent, each provenance
derivation, captured-source role, call subject/ID, authenticated invocation site,
`AccessorInvocationIdentity`, and final handle
field independently. Fixed, captured, fresh, conservative-unknown, and registered provenance
constructors each have positive and negative cases. A bare `FreshAccessorAlias` is unconstructible:
the only fresh case supplies a complete `RegisteredGenerativeAccessorAliasRule`, whose registered
allocation rule proves a new region and whose registered lifetime rule produces exactly the
accessor result lifetime. Omitting either rule, changing its environment/static inputs, or pairing
the allocation with a different lifetime derivation is rejected. An ordinary non-generative
accessor must use `PreserveCapturedAlias` for one validated captured source or
`ConservativeUnknownAlias`; it cannot mint an invocation root from its declaration, call, AST, or
result value. Registered generative fresh-alias tests preserve the same stage-free
`AccessorInvocationIdentity` and derived alias root through typed instantiation, ABI instantiation,
and `LoweredAccessorReferenceResultCertificate`; substituting the call/IR producer ID or a sibling
invocation's identity is rejected. `constref` and `ref` accessor declarations return their
structural handle type with respectively `ReadAccess` and `ReadWriteAccess`, and reject a bare
referent value that lowering would otherwise have to retrofit. Storage-access-intent tests keep
ordinary getter/setter and named reference-accessor read/write fallbacks distinct from explicit reference
formation and chapter 7's physical-reference argument plans. `StorageAccessIntentAt<S>` admits only
reads and payload-complete writes; `OutMode`, `InOutMode`, `ConstRefMode`, and `RefMode` are tested
as exclusive `PlanArgumentAccess` inputs. Write fixtures independently mutate the exact checked source,
conversion endpoints/plan, and completion condition and require the selected physical store,
setter, or ref-accessor fallback to retain them byte-for-byte and evaluate the source once. Read
fixtures require `YieldStorageRead`; write fixtures require
`CompleteStorageWrite(operation, sourceValue)` with that exact evaluated source; and every call-slot
fixture requires `PassArgument`. Cross-purpose alternatives, a dummy runtime argument on a
standalone write, or a storage terminal in a call slot are independently rejected under
`ELB-ACC-010`.
Read/write fallback fixtures require the
closed `ResolveAbstractStorageThroughReference` sequence, physical load/store, and a non-escaping
intermediate handle; they reject naming that handle from the plan terminal, turning it into a
`RuntimeArgument`, returning/capturing it, or
reclassifying the source `AbstractStorage` as physical.
The fallback accessor site must be the fixed-role child of the authenticated storage-access site,
and the fallback dereference site must in turn be the fixed-role child of that accessor site.
Sibling-parent substitutions and identities derived from either typed call ID are rejected.

`TST-ID-001`: For every retained operational identity above, round-trip validation accepts only the
matching nominal `ContentId<SemanticOperationSiteKey>` constructor. It recursively rejects every
site anchor containing an AST identity and every identity reconstructed from a Typed/IRReady/IR node,
while proving that removing the source-only assignment at the IRReady boundary leaves the nominal ID
and complete executable application unchanged.

Typed-call construction tests independently vary the complete `capabilitySelection` against the
selected callable, every retained extension use, and every call-slot conversion/access plan. They
cover zero, one, and multiple concrete sources; missing/extra/reordered sources; a stale combined
requirement; wrong region or proof endpoints; a missing/extra/inconsistently keyed ordinary use;
and a region mismatch while merging constituents. `BuildTypedCall` must reproduce the exact
`CAP-SEL-004` merge of the applicable winner and all call-slot selections, while
`BuildSelectedSurfaceTypedCallAt` must validate an independently supplied complete
callable/extension product and produce its exact merge with the call-slot selections. Explicit
accessor tests construct a prospective call identity and instantiate its result certificate
atomically;
they reject a certificate for a prior/equal-typed call and prove that no builder requires a
`TypedCallAt` which already contains its own certificate. Ordinary, fixed, accessor, and registered
call-result authorities are tested as disjoint alternatives. Every successful accessor invocation
must have the exact `PointerLikeCallResult`/raw-certificate equation from `EXP-REF-003`;
deserialization rejects `OrdinaryCallResult`, fixed/registered provenance, changed raw shape, or a
sibling certificate even when signature and result type agree. Header tests give two declarations
the same signature but different result authorities and require `BindDeclHeader`, specialization,
candidate construction, typed/elaborated/IRReady calls, `FunctionAbiMap`, and IR function/call shapes
to preserve the declaration-anchored ID. Builders receive no authority override, and mutation of
the ABI map or declaration shape to the other same-signature authority is rejected.
Access-environment tests require the
winner's exact `AccessEnvironmentId`, derive the invocation lifetime only by resolving it, and
reject a selected-surface plan checked under a different environment even when a separately chosen
lifetime would have compared equal.

### Generic solving

- each constraint kind and evidence kind;
- occurs checks, conflicting bounds, underconstrained variables, defaults, and ambiguity;
- bidirectional inference from parameters and expected results where specified;
- type/value packs, empty/non-empty packs, count equations, and nested expansion, including direct
  fixtures for `ConcreteNonEmptyPackWitness`, `DeclaredNonEmptyPackWitness`, positive-count
  derivation, and invalid proof endpoints;
- conformance and coercion constraints with fake providers;
- optional constraints distinguish replayable refutation from blocking, cancellation, resource
  exhaustion, ill-formed predicates, and recovery;
- solver permutation invariance for conceptually unordered constraints; and
- minimal unsatisfied-constraint explanations.

### Interfaces and witnesses

- exact, adapted, defaulted, builtin, missing, and ambiguous requirement matches;
- associated type, value, callable, property/accessor, subscript, constructor, and nested
  conformance requirements;
- `RequirementDictionary` values under reordered interface declarations;
- inherited/overridden requirements and diamond interfaces;
- receiver/mode/effect/capability mismatch;
- witness-table identity/definition graph cycles, conditional witness partitions, optional absence,
  and path-distinct diamond keys;
- concrete, generic, specialized, bound, lookup, existential, and pack `SubtypeWitness`
  values, with stable identity across construction-to-publication definition-resolution rewrites;
- exact one-to-one `LookupSubtypeWitness` spines, including requirement-key mismatch, diamond path
  distinction, serialization, and one frontend-IR lookup operation per semantic lookup;
- synthesis-key idempotence and deterministic synthesized requirement witness method bodies; and
- witness substitution, composition, validation, serialization, and IR key preservation.

### Initialization

- every source form × initialization strategy × value/storage goal and declaration site;
- `T(e)` and `(T)e` use the same `ExplicitSingle` candidate/ranking relation while retaining
  occurrence-specific CST origins, bound input IDs, request IDs, and (when those IDs differ) plans;
- target-directed braces, zero/one/many elements, nested aggregates, defaults, designators, packs,
  excess/missing/duplicate slots, and each versioned missing/flattening policy;
- declared, synthesized, builtin, extension, generic, and witness-provided initializers;
- composite initialization models whose descriptor maps offer nominal and aggregate strategies
  together, with deterministic scheduler results, structured rejected/ambiguous candidates, and the
  one admissible rank-detail family for every strategy;
- absence of a flag-like default operation: every accepted default/value/omitted request resolves a
  mandatory zero-input call, aggregate binding, or registered execution;
- complete call/registered/transfer endpoint maps for copy, move, aggregate written/member/type
  defaults, standard initialization, allocators, deallocators, and destructors, including
  operation-qualified exactly-once evaluation/storage orders;
- supplied, plan-owned, and allocated target-entry evidence; exact derived required-subobject sets;
  exhaustive legal/illegal state-transition tables; and nested-plan state/exit/cleanup composition;
- every initialization physical-endpoint shape retains physical address space and typed source
  provenance; plan-owned compiler storage has the explicit empty fact set, ordinary subobject
  projections preserve facts, and registered projections replay their exact source-component rule;
- cleanup maps with exactly the complete exit domain, including normal-exit storage destruction,
  moved-from destruction contracts, allocation ownership transfer/release, and lifetime ending;
- distinct allocation-object, physical-storage, owning-handle, and payload endpoints with executable
  provider/projection/cleanup plans and no recursive content-ID equation;
- explicit returned-value and plan-storage output transfers, physical destination rejection,
  direct-to-destination lowering, and exactly-once input evaluation;
- materialized temporary initialization uses one authenticated `TemporaryStorageIdentity` and
  `TemporaryStorageAliasRegion` through the outer access descriptor, nested destination binding,
  IRReady storage, and IR storage; substituting a plan ordinal, node ID, destination content ID, or
  sibling operation site is rejected;
- `INI-CTR-001` endpoint mutation in which access, value type, lifetime, entry state, and capability
  facts remain valid while the exact `AddressSpaceAdmissionProof` is missing, belongs to another
  storage shape, or proves another symbolic address-space requirement; none can substitute for it;
- exact selected-plan-step mapping to its declared actual-`IROp` emission recipe and
  `InitializationInstSemanticPlan` sidecars, including explicit creation, result extraction,
  all-exit cleanup, dependency-map merging for multi-instruction recipes, and lossless physical
  storage shapes;
- tooling-only recovered initialization lowers to `IRPoison` with no initialization-plan
  dependency and is rejected from publishable frontend IR;
- per-subobject definite initialization on normal/exceptional/delegating paths, replay of every
  exit-state proof, dependency-correct partial destruction, and exactly-once required allocation
  cleanup; and
- explicit rejection of concrete struct base slots, base-constructor steps, and legacy `(Struct)0`
  outside its named compatibility rule.

Registered-plan fixtures exercise `INI-PLN-012` and `INI-PLN-013` with absent, explicitly true, and
restrictive concrete availability. The rule's ordinary inferred capability always contributes its
own keyed use, even when its formula equals the concrete requirement; concrete sources, combined
requirement, and region proof remain only in the `CapabilitySelectionAt<S>` concrete alternative.
Plan composition must preserve both roles through `CAP-SEL-004`, and tests reject any replay that
drops one role, converts one into the other, or loses a source while retaining the same formula.

### Differentiability

- value and pointer differential evidence, associated-type idempotence, `dzero`/`dadd`, aggregate
  field maps, exclusions, and ambiguous providers;
- forward and backward signature maps for receiver, every passing mode, result/error policy, packs,
  active/inactive slots, and derivative order boundaries;
- `ConstRefMode(r)` is tested separately from `InMode` in forward and backward mode, for both active
  and inactive slots. Missing registration yields `MissingPhysicalOperandDerivativeRule`; no case
  falls back to an unchanged value input or an implicit pair/accumulator mapping;
- registered const-reference derivative rules are crossed with exact and mismatched access,
  lifetime, address-space, source-provenance, location-identity, and alias contracts. Successful
  maps use `RegisteredDerivativeRole(rule)`, preserve `isPhysicalStorage = True`, and contain no
  primal load, temporary materialization, or value-mode substitution;
- direct, custom, synthesized, witness, dynamic, builtin, and assumed providers,
  partial-priority ambiguity, generic specialization, exact stage-bound primal callable values,
  visibility, effects, and capabilities;
- `DIF-PRV-001`, `DIF-PRV-007`, and `DIF-PRV-016` capability phases independently: applicability
  records the provider's pre-inference ordinary use without requesting a local effective contract;
  optional concrete sources alone filter under the exact request region before ranking; and a
  selected pending local/witness/dynamic/synthesized provider is immutably revalidated against its
  exact post-fixpoint effective source without changing winner, ranking, ordinary use, or concrete
  selection;
- provider-candidate applicability, every registered priority dimension, comparison-proof replay,
  retained rejected candidates, equivalent maxima, and deterministic pairwise ambiguity independent
  of discovery/source/module order;
- keyed differential-evidence operand plans for concrete, generic-specialized, bound, lookup,
  associated-type, and opened-existential witnesses, including transitive substitution/constraint
  dependencies, stage-correct resolution sets, topological order, and exact IRReady/IR operand shapes;
- derivative slot maps whose domains include receiver, every expanded `ParameterKey`, result, and
  preserved error channel, with receiver/result/error never encoded as ordinary parameters;
- `fwd_diff`, `bwd_diff`, `no_diff`, custom association coherence, interface dispatch, and exact
  preservation of ordinary effects/access across detach-derivative boundaries;
- body activity joins, mutation/control-flow restrictions, recursive provider/synthesis queries,
  and deterministic serialization;
- total differentiation query products covering every structured rejection and ambiguity,
  scheduler blocking/resumption, valid recovery values, and proof that no declared failure is
  reachable only through diagnostic text;
- IRReady-to-IR provider lowering in which callable endpoints are `IRSymbolRef`s, other provider facts
  are canonical `IRStaticData`, all references resolve, and no descriptor serializes an AST callable
  or witness-resolution sidecar; and
- exact IRReady/IR preservation of provider identity, `DerivativeSignatureMap`, prerequisite
  witness/dynamic/lambda materialization, and final generated operands: one `base` for
  `IRForwardDifferentiate`; `applyFunction`, `contextType`, and `backwardPropagateFunction` for
  `IRBackwardDifferentiate`; and one `value` for `IRDetachDerivative`. Tests reject extra provider
  or evidence operands, swapped backward operands, an opcode payload, and a detach boundary stored
  anywhere except `IRInstSemanticMetadata`.

### Capabilities

- atom implication graph closure and cycle validation;
- conjunction/disjunction normalization, absorption, incompatibility, and canonical ordering;
- implication truth tables and counterexample clauses;
- `CAP-REG-005` region-availability proofs for positive and negative world assumptions, universe
  mismatches, and pointwise generic requirements;
- every `SelectCapabilitiesAt<S>` producer with zero, one, and multiple ordinary uses and concrete
  sources, including declaration, registered-operation, and language-rule subjects. One-field
  mutations cover wrong use-map keys, missing/extra/duplicate source, stale combined requirement,
  wrong region/proof endpoint, cross-universe input, and `NoConcreteAvailability` paired with a
  nonempty source list;
- `CAP-SEL-004` merge identity, associativity, and canonical source/use union under one region,
  including explicit-true sources; different regions and inconsistent equal use IDs are structured
  failures, and neither ordinary uses nor concrete sources may be converted into the other role;
- ordinary local/imported/witness `inferredCapabilities` remain applicable under a symbolic region
  that does not imply them, produce exactly one keyed use, and create the appropriate local
  inference dependency without requesting an effective contract;
- callable selection with no source yields `NoConcreteAvailability`; one or many callable and
  extension sources yield one `ProvenConcreteAvailability` containing their exact canonical source
  set, recomputed combined requirement, and proof under the query's exact world assumption.
  Unavailable concrete filters produce their dedicated candidate stage/failure and never affect
  ranking after applicability;
- one intrinsic extension-applicability fact is reusable in multiple caller regions without
  caller-use identity entering the facet route. Each committed `ExtensionFacetUseAt<S>` instead
  carries caller-specific keyed ordinary uses and the region-specific concrete proof; tests reject
  reusing either sidecar across callers or regions even when the extension/facet identity matches;
- conversion, access-plan, and typed-call composition preserves the complete
  `CapabilitySelectionAt<S>`. A selected call merges its callable/extension selection with every
  call-slot plan selection; removing a conversion source/use, retaining only a flat requirement,
  or copying a proof from another region is invalid in both IRReady replay and frontend-IR replay;
- interface and adapter fixtures independently mutate ordinary inferred compatibility and
  region-indexed concrete-availability compatibility, including an equal formula used in both roles
  without merging their proof/use identities;
- join/meet laws using the domain's actual semantic order;
- recursive call-graph least fixpoints and declared-requirement validation;
- target/stage switch branch formulas; and
- standard capability-definition file validation.

### Effects

- effect-set subset/union laws and canonical ordering;
- direct effect-use collection, local/imported/witness call edges, and error-type conversions;
- mutually recursive least-fixpoint inference using current SCC approximations;
- constrained/unconstrained declared-contract validation and the pure effective-set accessor;
- interface/adapter effect compatibility before and after inference; and
- deterministic term-growth/resource recovery without inserting errors into the effect lattice.

## Scheduler suites

Scheduler tests use artificial query kinds and integer/bitset lattices before testing language
queries. They cover every case listed in chapter 10, including SCC policy mixing, atomic publication,
SCC enlargement/restart, current-approximation reads, acyclic key growth, context-sensitive query
keys, parallel determinism, cancellation, and hash-based incremental reuse.

For every real query kind, one metadata test asserts that a cycle policy, durability class, result
validator, and implementation version are registered.

## Elaboration and IR tests

Elaboration tests directly instantiate typed nodes and assert explicit plans:

- `IROp` is mutated independently from every `IRInstSemanticMetadata` facet. Tests require the
  exact generated opcode/operand schemas for `IRCall`, `IRSpecialize`,
  `IRLookupWitnessMethod`, `IRExtractExistentialWitnessTable`, the three derivative instructions,
  `IRUnconditionalBranch`, `IRConditionalBranch`, `IRSwitch`, `IRReturn`, `IRThrow`, and
  `IRUnreachable`; reject semantic payload hidden in an opcode; and derive CFG successors only from
  terminator operands;
- receiver insertion and every parameter passing mode;
- default/named argument mapping, stage-neutral access recipes, operand binding, aliasing,
  temporary/write-back, closed terminal purpose, and terminal-relative normal/exceptional cleanup
  behavior;
- call capability metadata from typed call through elaborated call, `IRReadyCallContract`, and the
  stage-free `IRCapabilitySelection` projection. Fixtures cover zero, one, and multiple concrete
  sources; exact subject/source IDs, combined requirement, region proof, and keyed ordinary uses;
  local/witness use stamps, per-concrete-source dependency stamps, inverse reconstruction; and
  exact declaration, standard-rule, language-rule-set, and nested-conformance IR dependencies.
  Projection is rejected after mutating any source/use/proof/stamp/dependency. The metadata is
  absent from ABI inputs/results and
  `AbiCallInstantiation`, and equal flattened formulas never substitute for it;
- lambda capture identity, ordering, mode, nested forwarding, environment layout, and callable
  witness;
- property/subscript getter and setter rewrites plus explicit reference-formation accessor calls;
  capture-once result environments retain the exact `CapturedStorageSource` and executable
  `ElaboratedExprAt<S>` even for a storage; source-set identity, source projections, ordinary
  typed-call contract completion,
  closed IRReady reference producer/dereference payloads, and one-to-one
  `ReferenceInstSemanticPlan` alternatives whose selected actual opcodes match their sidecars;
  multi-expansion tests project one captured pack result, while negative tests mutate
  the result ID, source role, expansion path, slot, operand, or evaluate-once step independently;
  physical-mode call planning retains exactly one keyed reference-accessor invocation and its
  stored dereference when the argument is abstract. `ConstRefMode` accepts only
  `AccessorRole.RefAccessor(ReadAccess)` and rejects a mutable `ref`-only property; `RefMode` accepts only
  `AccessorRole.RefAccessor(ReadWriteAccess)`. Both preserve the resulting physical location without a
  load. The separately authorized
  ordinary read/write fallback expands through `ResolveAbstractStorageThroughReference`, physical
  load/store, and a non-escaping handle. Payload-complete writes retain their source evaluation,
  conversion, completion condition, write terminal, and returned source value under `ELB-ACC-009`;
  physical reads lower directly to IRReady `Load`, writes to `Store`/setter regions, and only
  `PassArgument` contributes to an enclosing call region. These cover `ELB-REF-001` through
  `ELB-REF-004`, `ELB-ACC-007` through `ELB-ACC-010`, and `IR-REF-001` through `IR-REF-005`
  independently. Registered direct-reference and handle-transform cases require their stage-free
  IRReady applications to retain registration, endpoint proofs, and control while keeping the exact
  physical/handle value as a separate IRReady operand; `input.operand`, selection state, semantic uses,
  and every typed-node identity are absent;
- builtin physical-element applications preserve their base/index operand roles, evaluation order,
  stable projection identity, result proof, and output storage through `ELB-STO-003`,
  `ELB-STO-004`, and `IR-STO-002`. Dereference applications preserve the independently executable
  handle plus the stable identity/path equation through `IR-REF-004`; no IRReady or IR descriptor
  contains a `NodeId<Typed>`;
- accessor-result certificate lowering retains producer instruction/normal ordinal, call
  instantiation ID, contract, stage-free subject evidence, signature, referent, exact
  source-role-to-producer-operand/projection bindings, every component derivation, and result shape,
  but no typed node. It accepts only the exact producer call's normal handle result. Tests substitute
  a block parameter, copy, sibling call, wrong result ordinal, wrong instantiation, wrong direct or
  witness subject/evidence, wrong contract/signature, wrong captured producer/ABI operand/pack
  projection, and equal-`TypeId` ordinary value, then mutate every certificate field;
- function ABI input/result alternatives: `ConstRefMode(location)` and `RefMode(location)`
  both enter the body only as contract-derived physical-location value shapes with respectively
  read-only and read-write admission; `isPhysicalStorage` remains true for each. A reusable
  declaration map always uses
  `CallableActivationLifetime(signature)` and target/ABI-selected formal address spaces, never a
  caller lexical lifetime. Call-local instantiations independently bind the exact caller invocation
  extent and address substitution. Reference/pointer input contracts exercise structural type
  derivation plus default/declared mutability, lifetime, alias, and physical-source-provenance
  policies without storing a concrete call proof. The conservative source policy yields the empty
  proven-fact set, and declared policies retain every rule/static-input/environment tuple.
  Fixed/accessor/registered result contracts are tested independently:
  function returns prove the reusable contract, while calls instantiate exact concrete SSA results.
  Cross-category, activation, access, mutability, lifetime, address-space, alias, source-provenance,
  requirement, provenance-policy, and same-`TypeId` mutations exercise `IR-ABI-001` through
  `IR-ABI-004`;
  return/throw and call-result tests reject handle provenance erasure or fabrication;
- physical/abstract plan-ID separation and elimination of every abstract storage before IRReady;
- interface adapter/default/builtin synthesis;
- existential open/pack and witness dispatch;
- static/generic/specialized/bound/lookup/existential witness values and witness calls whose first
  IR operand is the witness value rather than a table symbol;
- direct-to-destination initialization and derivative-provider/detach-derivative IRReady operations;
- defer/throw cleanup edges; and
- pack/compile-time/target elaboration.

IRReady-to-IR tests use a fake symbol resolver and compare a normalized IR fragment. They do not run
target legalization or emission. Mutual-recursion tests publish all `IRSymbolDecl`s before
definitions and verify stable `ParameterKey`/requirement-key maps.

## Differential and migration testing

For compatibility-preserving rules, a differential harness runs the old and new frontends on the
same source and compares normalized observations:

- accepted/rejected status and structured diagnostics;
- exported declarations and canonical signatures;
- selected overloads and inferred generic arguments;
- `RequirementDictionary` keys and satisfying declaration identities;
- required effects, capabilities, and visibility; and
- normalized initial IR.

Expected differences are keyed by an accepted `Intentional change` ledger entry and rule ID. A
global “known differences” text file is not acceptable.

The existing `tests/` corpus seeds differential coverage, but small generated programs exercise
cross-products that integration tests miss. Corpus minimization retains the smallest source for
each distinct semantic observation.

## Fuzzing and metamorphic properties

Continuous fuzzers cover tokens, preprocessing, CST parsing/recovery, serialization, generic
constraints, and scheduler dependency graphs. Important metamorphic properties are:

- inserting/removing trivia does not change semantic results outside trivia-sensitive legacy rules;
- reformatting and identity serialization preserve source/CST semantics;
- reordering independent declarations does not change modern-language binding;
- reordering keyed interface requirements does not change witness satisfaction;
- reordering generic constraints does not change a unique solution;
- adding an unused private declaration does not change exported semantic hashes;
- one-worker and many-worker schedules are identical; and
- serialize/deserialize between stages does not change the next-stage result.

## Coverage gates

The frontend uses several complementary gates:

1. **rule coverage:** 100% of implemented normative rule IDs have required manifest tests;
2. **schema coverage:** 100% of node/field/variant descriptors have generated fixtures and round
   trips;
3. **primitive function coverage:** every exported frontend primitive has direct tests for success,
   each failure alternative, and mocks for external queries;
4. **branch coverage:** enforced per frontend library as a regression signal, not a semantic proof;
5. **mutation testing:** required for comparison/ranking/algebra code where ordinary line coverage
   is weak; and
6. **differential feature coverage:** every `Preserve` ledger row has old/new observations.

A coverage waiver names the rule, unreachable condition proof, owner, and expiry. It cannot waive a
whole file or subsystem.

## Test layout

The proposed implementation keeps direct tests near the frontend libraries:

```text
tools/slang-unit-test/frontend/
    source/
    lexer/
    preprocessor/
    cst/
    schema/
    scheduler/
    names/
    facets/
    types/
    storage/
    conversions/
    overloads/
    generics/
    interfaces/
    capabilities/
    initialization/
    differentiability/
    elaboration/
    ir/

tests/frontend-differential/
tests/frontend-generated/
```

The exact directory can change during implementation; the separation between direct unit tests,
differential tests, and target/end-to-end tests is normative in intent.
