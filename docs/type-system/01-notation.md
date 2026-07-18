# Notation and conformance

This chapter defines the metalanguage used by the remaining specification. The notation is chosen
to be readable in Markdown, mechanically extractable, and direct enough to translate into unit
tests.

## Stable rule identifiers

Every normative rule has an identifier of the form `AREA-CATEGORY-NNN`:

- `LEX`, `PP`, `PAR` — lexing, preprocessing, and parsing;
- `REP` — representation invariants;
- `NAM`, `DEC`, `VIS` — names, declarations, and visibility;
- `TYP`, `EXP`, `STM`, `CON` — types, expressions, statements, and constant evaluation;
- `CVR`, `OVL`, `GEN` — conversion, overload resolution, and generics;
- `IFC`, `WIT`, `SYN` — interfaces, evidence, and synthesis;
- `SUB` — representation/interface subtyping, facet routes, extensions, and lookup priority;
- `INI` — initialization and construction;
- `DIF` — differentiability and derivative surfaces;
- `CAP` — capabilities;
- `SCH` — scheduler and cycle handling; and
- `ELB`, `IR` — elaboration and frontend IR;
- `SPEC` — specification-wide authority and interpretation; and
- `TST` — validation and test architecture.

Identifiers are never renumbered. Removing a rule leaves a tombstone in the compatibility ledger.
A rule may be split by adding lowercase suffixes, for example `AREA-CATEGORY-NNNa` and
`AREA-CATEGORY-NNNb`.

## Grammar notation

Grammar is written in ISO-style EBNF with these extensions:

```text
production = element, { element | alternative } ;
optional   = [ element ] ;
repeated   = { element } ;
one-or-more = element, { element } ;
token      = "literal-token" | IDENTIFIER ;
exclusion  = TOKEN - ";" ;
predicate  = <semantic-or-lookahead-predicate> ;
```

Uppercase names denote token kinds. `snake-case` names denote nonterminals. A production annotated
with `@recover(...)` declares its parser recovery set. A production annotated with
`@language-version(V)` is present only under that Slang language version. HLSL/GLSL dialect gates
are not part of this edition's grammar notation. Contextual keywords are spelled as identifier text
in the grammar and are never silently added to the lexer keyword set.

The grammar defines accepted token sequences, not typing. For example, a syntactically valid type
expression may later classify as a value and produce a semantic diagnostic.

## Scalar domains and stable names

The metalanguage uses the following mathematical scalar domains. These definitions are independent
of the host implementation's integer widths, character type, locale, and path syntax:

```text
Bool       = False | True
UInt8      = { n : BigNat | 0 <= n < 2^8 }
UInt16     = { n : BigNat | 0 <= n < 2^16 }
UInt32     = { n : BigNat | 0 <= n < 2^32 }
UInt64     = { n : BigNat | 0 <= n < 2^64 }
BigNat     = arbitrary-precision non-negative integer
BigInt     = arbitrary-precision signed integer
UnicodeScalar = { n : UInt32 | n < 0xD800 or 0xDFFF < n <= 0x10FFFF }
ByteString = finite sequence of octets
BitString  = finite sequence of bits
Utf8String = finite, well-formed UTF-8 encoding of Unicode scalar values
Text       = Utf8String
InternedString = Utf8String
Hash256    = { bytes : ByteString | bytes.count = 32 }

RuleId = {
    text: Utf8String
    | text matches `[A-Z]{2,4}(-[A-Z0-9]+)+-[0-9]{3}[a-z]?`
}

Utf8Identifier = {
    text: Utf8String
    | text is non-empty, NFC-normalized, and satisfies the schema-identifier grammar
}

QualifiedName = {
    segments: NodeList<Utf8Identifier> | segments.count >= 1
}
```

The schema-identifier grammar accepts an underscore or Unicode `XID_Start` followed by underscores
or Unicode `XID_Continue` characters. It is a registry grammar, not Slang's source identifier
grammar. A `QualifiedName` compares and serializes as the count-prefixed sequence of normalized
segments; punctuation-joined display text is not its identity. Diagnostic codes, registered rule
names, schema kinds, and capability atoms therefore cannot collide because of a chosen display
separator or platform case-folding. `Hash256` is an index/checksum value wherever an exact
discriminator is also required; chapter-specific rules state when it may itself be an identity.
`InternedString` equality is UTF-8 value equality; interning is an unobservable implementation
optimization. `RuleId` is its exact ASCII text and is never identified by a manifest position or a
rendered heading.

## Algebraic data types

Representation schemas use sums, products, immutable sequences, and immutable maps:

```text
Option<T>       = None | Some(T)
Result<T, E>    = Ok(T) | Err(E)
NodeList<T>     = immutable sequence of T
NonEmpty<T>     = immutable sequence of T whose count is at least one
NodeMap<K, V>   = immutable map from K to V
CanonicalFiniteSet<T> = immutable duplicate-free finite set sorted by canonical T encoding
CanonicallyOrderedMap<K, V> = immutable map sorted by canonical K encoding
CanonicallyOrderedSet<T> = CanonicalFiniteSet<T>

CanonicalSetInclusionProof<T> = {
    subset: CanonicalFiniteSet<T>,
    superset: CanonicalFiniteSet<T>
}

ExampleExpr<F> = VarExpr<F>(name: Name)
               | InvokeExpr<F>(callee: Expr<F>, arguments: NodeList<Argument<F>>)
```

`ExampleExpr` is notation for this example sum, not an AST kind. Its alternatives deliberately use
the established `VarExpr` and `InvokeExpr` node names; the complete `Expr` registry is defined by
the syntax schema rather than this illustrative fragment.

`F` is a node-local representation form. A field ending in `Id` is a stable identity, not an owning
pointer. `ASTNodeId<F, K>` is a reference to a node of form `F` and kind family `K` in one
heterogeneous immutable semantic snapshot. It does not assert the form of any other node.
`ExternalRef` identifies a node in a dependency snapshot by content hash and exported ID.

Product fields are named. Positional interpretation of a heterogeneous product is forbidden even
when the physical storage uses an operand array.

A `CanonicalSetInclusionProof<T>` is valid exactly when every member of `subset` occurs in
`superset` under `T`'s declared canonical equality. Validators replay membership; the record is not
an unchecked assertion.

## Environments and judgments

The main metavariables are:

| Symbol             | Meaning                                                              |
| ------------------ | -------------------------------------------------------------------- |
| `P`                | immutable program snapshot and module graph                          |
| `Σ`                | standard environment and target facts                                |
| `Γ`                | lexical and semantic environment                                     |
| `Δ`                | generic binders and constraints                                      |
| `C`                | control-flow context (function, loops, switch, defer, target branch) |
| `κ`                | available capability requirement                                     |
| `ν`                | visibility/access context                                            |
| `e`, `s`, `d`, `t` | expression, statement, declaration, and type                         |
| `τ`, `ρ`           | canonical semantic types                                             |
| `c`                | expression classifier                                                |
| `q`                | value category and access capability                                 |
| `w`                | witness/evidence value                                               |
| `π`                | explicit elaboration or conversion plan                              |
| `D`                | ordered diagnostic set                                               |

Judgments have inputs on the left and derived outputs on the right:

```text
P; Σ; Γ; Δ ⊢ e ⇝ e' :: c ▷ D
```

This reads: in program `P`, standard environment `Σ`, lexical environment `Γ`, and generic context
`Δ`, surface expression `e` elaborates to `e'`, has classifier `c`, and emits diagnostics `D`.
The notation `e' : τ @ q` is shorthand for `e' :: ValueClassifier(τ, q)` and is valid only for
value-classified expressions. Type, overload-set, partial-generic, namespace, and recovery terms use
their explicit classifier alternatives instead of a fictitious type and value category.

Common judgments are:

```text
Γ ⊢ name ⇝ LookupResult                         name lookup
Δ ⊢ τ ≡ ρ                                      type equality
Δ ⊢ τ ≤repr ρ ⇝ RepresentationAdjustmentPath   representation adjustment
Σ; Γ; Δ ⊢ τ <: I ⇝ SubtypeWitness     interface subtyping/conformance
Δ ⊢ I refines J ⇝ InterfaceRefinementProof      interface refinement
Σ; Γ; Δ ⊢ Coerce(e, ρ) ⇝ ConversionResult       implicit coercion planning
Σ; Γ; Δ ⊢ call(args) ⇝ OverloadResult           overload resolution
Σ; Δ ⊢ constraints ⇝ GenericSolution            generic solving
Σ; Δ ⊢ τ : I ⇝ ConformanceSearchResult          interface conformance
κ₁ ⊨ κ₂                                        capability implication
ν ⊢ decl visible                               access permission
```

An omitted environment is unchanged from the enclosing section. An inference rule is written:

```text
premise-1    premise-2
---------------------- RULE-ID
conclusion
```

The rule identifier is part of the rule and is recorded in elaboration provenance and diagnostics.

## Total results and recovery

Every primitive query returns a value of this shape:

```text
Severity = Disable | Note | Warning | Error | Fatal | Internal
EmittedSeverity = Severity where value in {Note, Warning, Error, Fatal}

DiagnosticAnchor = SourceAnchor(SourceRange) | SemanticAnchor(StableSemanticId)

ErrorIdentity = {
    code: QualifiedName,
    primary: DiagnosticAnchor,
    rule: RuleId,
    arguments: CanonicalArguments
}

ErrorId = ContentId<ErrorIdentity>

RelatedDiagnostic = {
    role: QualifiedName,
    origin: Origin,
    arguments: CanonicalArguments
}

DiagnosticKey = {
    rootError: Option<ErrorId>,
    code: QualifiedName,
    severity: EmittedSeverity,
    primary: Origin,
    rule: RuleId,
    arguments: CanonicalArguments
}

Diagnostic = {
    key: DiagnosticKey,
    related: NodeList<RelatedDiagnostic>
}

DiagnosticSet = {
    byKey: CanonicallyOrderedMap<DiagnosticKey, Diagnostic>,
    presentationOrder: NodeList<DiagnosticKey>
}

DiagnosticSelection = CanonicallyOrderedSet<DiagnosticKey>

CheckResult<T> =
    Success(value: T, diagnostics: DiagnosticSet)
  | Recovered(value: T, errors: NonEmpty<ErrorId>, diagnostics: DiagnosticSet)
```

`Disable` is the result of diagnostic policy and never appears in a `DiagnosticKey`. `Internal`
records a compiler invariant/infrastructure failure rather than a source-language error; chapter 11
captures it as an execution failure, not a serialized language diagnostic.

Dependency blocking and cancellation are execution states of the scheduler in chapter 11, not
semantic `CheckResult` alternatives and never values in a published `SemanticSnapshot`.
`Recovered` contains a structurally valid value of the requested type. Recovery values carry an
`ErrorId`, so later rules suppress diagnostics caused by the same root error without treating the
value as semantically valid.

Diagnostics are values, not side effects. A `Diagnostic` has a stable code, severity, primary
origin, ordered related origins, rule ID, and structured arguments. Sorting diagnostics by source
origin, rule priority, and stable tie-break key makes output independent of task order.

`REP-DIA-001`: Every diagnostic map key equals its value's `key`, and `presentationOrder` is a
duplicate-free bijection onto the map keys in the stated deterministic order. Error recovery uses
an `ErrorId` whose code, rule, arguments, and projected stable anchor equal the root error
diagnostic. `DiagnosticAnchor` deliberately excludes recovery provenance, which keeps error
identity finite. Merging diagnostic sets is canonical map union plus deterministic related-origin
union; worker or discovery order is unobservable.

`REP-DIA-002`: A recovered result's `errors` are duplicate-free root IDs, and each has exactly one
root error diagnostic in the result's sole `DiagnosticSet`. A semantic payload or rejection trace
may retain only a `DiagnosticSelection`; every selected key must occur in the enclosing query
result (or its `DiagnosticIndex` entry). Structural AST, semantic-definition, synthesis-group, and
IR records never embed a second diagnostic set that could diverge.

## Equality, identity, and canonicalization

The specification distinguishes:

- **node identity** — stable identity within a snapshot, used for provenance and declarations;
- **structural equality** — equal kind and recursively equal fields;
- **semantic equality** — equality after canonical type/value normalization; and
- **source equivalence** — equal ordered `Token | Trivia` physical spellings and token-origin
  mapping.

Canonicalization is a pure query. Pointer equality may optimize canonical equality inside one
process but must never define language semantics.

For a canonicalizer `canon`:

```text
canon(canon(x)) = canon(x)                       idempotence
x ≡ y  iff  canon(x) structurally-equals canon(y)
```

### Canonical key values

Scheduler, synthesis, and builtin-rule inputs use one closed, versioned key algebra:

```text
AnyASTNodeId<F> = exists K . ASTNodeId<F, K>
AnyASTNodeId = exists F . AnyASTNodeId<F>
AnyNodeId = CST(AnyCSTNodeId) | AST(AnyASTNodeId)
SchemaValue = exists K: registered semantic NodeKind . Value<K>

ContentId<T> = {
    schemaKind: QualifiedName,
    digest: Hash256,
    exactDiscriminator: ByteString
}

StableSemanticId =
    SourceFileSnapshotIdentity(file: SourceFileId,
                               revision: RevisionId,
                               content: Hash256)
  | SyntaxNodeIdentity(AnyNodeId)
  | DeclIdentity(DeclId)
  | ScopeIdentity(ScopeId)
  | TypeIdentity(TypeId)
  | WitnessTableIdentity(WitnessTableId)
  | RequirementIdentity(kind: RequirementKind,
                        encoding: ByteString)
  | SynthesizedIdentity(SynthesizedSemanticId)
  | ContentIdentity(ContentId<SchemaValue>)

CanonicalArgumentKey = {
    wireTag: UInt32,
    stableName: QualifiedName
}

CanonicalArgument =
    UnitArgument
  | BoolArgument(Bool)
  | UnsignedArgument(BigNat)
  | SignedArgument(BigInt)
  | BytesArgument(ByteString)
  | TextArgument(Utf8String)
  | EnumArgument(type: QualifiedName, variantTag: UInt32)
  | IdentityArgument(StableSemanticId)
  | SchemaValueArgument(ContentId<SchemaValue>)
  | ListArgument(NodeList<CanonicalArgument>)
  | MapArgument(CanonicallyOrderedMap<CanonicalArgumentKey, CanonicalArgument>)

CanonicalArguments =
    CanonicallyOrderedMap<CanonicalArgumentKey, CanonicalArgument>
```

Canonical encoding uses the schema version, explicit variant/field tags, unsigned LEB128 lengths
and unsigned integers, and a sign byte followed by a minimal big-endian magnitude for signed
integers (zero is the sole empty-magnitude encoding). It uses raw byte strings and
NFC-normalized UTF-8 only for fields whose schema declares semantic text normalization. Lists retain
order; maps sort by the canonical encoding of their keys and reject duplicates. A
`ContentId.exactDiscriminator` is the complete canonical value encoding; `digest` is only an index
accelerator, so collisions never define equality. Recursive `SynthesizedIdentity` cause chains must
be finite and satisfy the scheduler/synthesis key-growth limits.

`REP-KEY-001`: A query or synthesis rule may accept only fields representable in
`CanonicalArgument`. Process addresses, provisional handles, unordered container iteration,
diagnostic rendering, and snapshot-local definition revisions excluded by an identity-projection
rule cannot enter canonical key bytes. Round-trip and cross-process fixtures test every alternative.

## Orders and algebraic laws

`≤` denotes an information or permission order defined by the surrounding domain. `⊔` and `⊓`
denote join and meet when they exist; they do not automatically mean set union and intersection.
Every fixpoint query names its domain, bottom element `⊥`, order, and transfer function.

The following laws must have property tests for every declared algebra:

```text
x ⊔ y = y ⊔ x                                  commutativity
(x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)                      associativity
x ⊔ x = x                                      idempotence
x ⊔ ⊥ = x                                      identity
```

If a domain intentionally violates one of these laws, the rule defining the operator must say so;
the implementation must not use it as a scheduler lattice.

## Provenance

Every AST or semantic transformation output carries one of the following. Concrete-syntax
translations carry the direct `CSTNodeOrigin` records defined in chapter 3; a transformation is a
function or query and is not stored as a separate operation object.

```text
ModuleInterfaceContentId = ContentId<SchemaValue>
ModuleDeclOutlineInterfaceId = ContentId<ModuleDeclOutlineInterface>

Origin =
    ConcreteSyntax(cst: AnyCSTNodeId)
  | PriorAST(previous: AnyASTNodeId, rule: RuleId)
  | Synthesized(group: SynthesisKey, outputRole: SynthesisOutputRole,
                causes: NonEmpty<StableSemanticId>)
  | ImportedDeclOutline(module: ModuleDeclOutlineInterfaceId,
                        outline: ExportedDeclOutlineId)
  | Imported(module: ModuleInterfaceContentId, exported: ExportedId)
  | Recovery(source: SourceRange, error: ErrorId)

OriginSet = CanonicallyOrderedSet<Origin>
```

Provenance is a semantic edge, not a structural child. Generic traversal can choose whether to
follow structural, packed-alternative, semantic, or provenance edges and therefore cannot
accidentally recurse through the entire history of a node.

## Rule template

Each language feature is specified using this template:

1. **Syntax** — productions and contextual-keyword rules.
2. **Representation** — CST and every node-local AST-form shape.
3. **Static semantics** — premises, output value, and diagnostics.
4. **Elaboration** — all implicit behavior made explicit.
5. **Interactions** — generics, interfaces, capabilities, visibility, and errors.
6. **IR contract** — emitted operation or proof of earlier erasure.
7. **Compatibility evidence** — current source symbols and tests.
8. **Validation** — rule-linked unit and integration cases.

No implementation-only boolean such as `checked`, `resolved`, or `beingChecked` is an allowed
semantic output. The corresponding state is represented by the output type or by scheduler state.
