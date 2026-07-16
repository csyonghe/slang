# Immutable frontend representations

This chapter defines the data model on which syntax and semantic rules operate. It is normative for
observable structure, provenance, losslessness, generic access, and serialization. Exact C++ object
layouts are not normative.

## Source snapshots

```text
SourceFileSnapshot = {
    file: SourceFileId,
    revision: RevisionId,
    bytes: ByteString,
    encoding: Utf8,
    lineMap: LineMap,
    contentHash: Hash256
}

SourceFileRecord = {
    id: SourceFileId,
    physicalBytes: ByteString,
    decoded: SourceFileSnapshotId,
    decodingMap: OffsetMap,
    encoding: DetectedEncoding
}

SourceViewUse =
    PrimarySourceView
  | IncludedSourceView(initiatingRange: SourceRange)
  | GeneratedSourceView(rule: RuleId, anchor: Option<SourceRange>)

SourceLineDirective = {
    byteOffset: UInt64,
    presumedPath: Option<Utf8String>,
    presumedLine: UInt32,
    resetToFileDefault: Bool
}

SourceViewKey = {
    snapshot: SourceFileSnapshotId,
    use: SourceViewUse,
    viewPath: Option<Utf8String>,
    lineDirectives: NodeList<SourceLineDirective>
}

SourceViewId = ContentId<SourceViewKey>

SourceView = {
    id: SourceViewId,
    key: SourceViewKey
}

SourceRange = {
    view: SourceViewId,
    startByte: UInt64,
    endByte: UInt64
}

SourceRangeSet = {
    ranges: NonEmpty<SourceRange>
}

ByteRange = {
    startByte: UInt64,
    endByte: UInt64
}

SourceTextSlice = {
    snapshot: SourceFileSnapshotId,
    range: ByteRange
}
```

`SourceFileSnapshot` is the immutable decoded-content counterpart of the codebase's `SourceFile`;
`SourceFileRecord` additionally retains the original encoded bytes and their decoding map. An
immutable `SourceView` is one interpretation/use of that content for a particular lex/parse, just
as in the current source manager. Re-including equal file contents may therefore reuse a snapshot
while producing a distinct view with a different initiating range or line-directive interpretation.

Source offsets are byte offsets into the snapshot selected by the range's `SourceView`. A source
range is half-open `[start, end)` and belongs to exactly one view. Line and column are derived from
that view's snapshot and line directives and are not serialized as competing authority.

`REP-SRC-001`: A snapshot is immutable. Editing creates a new snapshot and an explicit change map
from old byte ranges to new byte ranges.

`REP-SRC-002`: Source locations in tokens and syntax nodes identify a source view and byte range; they
must not be raw pointers into a mutable source manager.

`REP-SRC-003`: Every range satisfies
`startByte <= endByte <= resolve(resolve(range.view).key.snapshot).bytes.count`.
`SourceRangeSet.ranges` is duplicate-free and in token-origin traversal order; adjacent ranges are
coalesced only when they belong to the same view and no origin boundary would be lost. A macro-
derived red node may therefore name ranges in several snapshots without inventing one contiguous
span.

`REP-SRC-004`: `ByteRange` is half-open and satisfies `startByte <= endByte` in the coordinate
space of its containing field. A `SourceTextSlice` range is bounded by its named snapshot. For a
`PhysicalSlice`, `rawText.snapshot = resolve(span.view).key.snapshot` and its byte range equals
`[span.startByte, span.endByte)`; the two fields provide a lazy byte view and an explicit source
location, not competing extents.

`REP-SRC-005`: `SourceFileSnapshot.bytes` is well-formed UTF-8,
`contentHash = SHA256(bytes)`, and `lineMap = buildUtf8LineMap(bytes)`. The canonical line map starts
with byte offset zero and adds the offset immediately after every LF byte; CR in a CRLF pair remains
part of the preceding line. It stores no redundant line/column cache. These equations are checked
when a snapshot is interned and again when it is deserialized.

`REP-SRC-006`: Resolving `SourceFileRecord.decoded` yields a snapshot whose `file` equals the
record's `id` and whose bytes equal `decode(physicalBytes, encoding)`. `DetectedEncoding` includes
the BOM decision. `OffsetMap` is the canonical, total, monotone segment map produced by that same
decode operation: it maps every physical and decoded segment boundary, including a consumed BOM and
replacement spans for invalid input, and no independently supplied map is accepted. Consequently
the decoded snapshot is the semantic source of truth while `(physicalBytes, encoding, decodingMap)`
is sufficient to reproduce and diagnose the original file exactly.

`REP-SRC-007`: `SourceView.id = ContentId(SourceView.key)`. Line directives are in strictly
increasing `byteOffset` order and are bounded by the selected snapshot. An included view's
initiating range resolves to its parent view; a generated view records its rule and optional source
anchor. Equal decoded bytes do not merge views whose include use, view path, or line-directive
interpretation differs.

## Physical tokens, trivia, and preprocessing

The frontend maintains a byte-partitioning physical token list, logical lexer tokens, and expanded
preprocessor tokens so that formatting and semantic compilation do not fight over one lossy stream.

```text
PhysicalSlice = {
    id: PhysicalSliceId,
    span: SourceRange,
    rawText: SourceTextSlice,
    role: TokenPiece(token: TokenId, pieceIndex: UInt32)
        | TriviaPiece(trivia: TriviaId)
        | PreprocessorMarker(marker: PpMarkerId)
}

Trivia = {
    id: TriviaId,
    kind: Whitespace | Newline | LineComment | BlockComment | LineContinuation,
    isDocumentation: Bool,
    span: SourceRange,
    rawText: SourceTextSlice
}

TriviaRange = {
    id: TriviaRangeId,
    items: NodeList<TriviaId>,
    span: SourceRange
}

Token = {
    id: TokenId,
    type: TokenType,
    pieces: NonEmpty<PhysicalSliceId>,
    logicalSpelling: Text,
    leadingGap: TriviaRangeId,
    trailingGap: TriviaRangeId,
    interstitialTrivia: NodeList<TriviaId>,
    flags: TokenFlags
}

PhysicalToken =
    SourceToken(Token)
  | BoundaryToken {
        id: BoundaryTokenId,
        boundary: StartOfFile | EndOfFile,
        adjacentGap: TriviaRangeId
    }

PhysicalTokenList = {
    slices: NodeList<PhysicalSlice>,
    tokens: NodeList<PhysicalToken>,
    trivia: NodeList<Trivia>,
    gaps: NodeList<TriviaRange>,
    view: SourceViewId
}

PhysicalTokenListId = ContentId<PhysicalTokenList>

TokenFlag = StartOfLogicalLine | EscapedIdentifier | ContextualKeywordCandidate |
            InvalidSpelling | StandardTokenFlag(StandardTokenFlagId)
TokenFlags = CanonicalFiniteSet<TokenFlag>
```

`PhysicalTokenList` is the lossless replacement form of the codebase's `TokenList`. Each
`SourceToken` contains the established `Token`/`TokenType` concept with added immutable trivia and
slice links; `BoundaryToken` is a list sentinel, not a renamed lexical token.

Ordered `PhysicalSlice`s, not logical token extents, partition the source. Most tokens have one
piece. A token containing a spliced backslash-newline has multiple token pieces separated by a
`LineContinuation` trivia slice; `logicalSpelling` is the spelling after the language-defined
splice. Thus neither a fake contiguous source range nor discarded bytes are required.

Ordinary trivia is stored once in immutable inter-token gaps. The gap between token `i` and token `i+1` is
visible as `i.trailingGap` and `i+1.leadingGap`; both fields refer to the same `TriviaRangeId`.
Start/end `BoundaryToken`s own no source slice and anchor the outer gaps. Every `Token` has at
least one piece and exposes both surrounding gaps. `isDocumentation` is valid only on line/block
comments, so documentation classification preserves the base comment form. Documentation
extraction is a view over trivia and never removes comments from the CST.

`TriviaRange.items` is in physical-slice order and contains exactly the ordinary gap trivia whose
slices concatenate to `span`. An empty gap has no items and a zero-width span at the shared token
boundary. Every `TriviaId` occurs exactly once either in one gap or in one lexical token's
`interstitialTrivia`, never both. The start/end boundary tokens make even an empty file have one
well-defined outer gap. These rules make shared leading/trailing trivia serializable without
duplicating ownership.

`REP-TOK-001`: Ordered physical slices partition the decoded source snapshot. Their raw text
concatenates to its exact UTF-8 bytes. The list retains `SourceViewId`; resolving the view and its
snapshot yields the `SourceFileRecord`, so identity output of an unmodified non-UTF-8/BOM input can
reproduce the original encoded `physicalBytes`.

`REP-TOK-002`: Token spelling is preserved independently of its decoded value. `0x10`, `020`, and
`16` may have the same integer value but different raw text.

`REP-TOK-003`: Invalid bytes and malformed literals produce tokens with lexical diagnostics; the
physical token list remains lossless.

Preprocessing produces an immutable tree and a view, not a second unrelated token list:

```text
PreprocessorTree = {
    root: SourceGreenNodeId,
    macroDefinitions: NodeMap<PpMacroDefinitionId, PpMacroDefinition>,
    macroInvocations: NodeMap<PpInvocationId, PpMacroInvocation>,
    physicalTokens: PhysicalTokenListId
}

ExpandedToken = {
    id: ExpandedTokenId,
    kind: TokenType,
    spelling: Text,
    origin: TokenOriginId
}

TokenOrigin =
    Physical(token: TokenId)
  | MacroExpansion(invocation: PpInvocationId, definition: PpMacroDefinitionId,
                   arguments: NodeList<TokenOriginId>, step: ExpansionStep)
  | Synthesized(rule: RuleId, anchor: SourceRange)

ExpandedTokenView = {
    tokens: NodeList<ExpandedToken>,
    origins: NodeMap<TokenOriginId, TokenOrigin>,
    conditions: PresenceConditionMap,
    preprocessorTree: PreprocessorTreeId
}
```

Inactive regions remain in `PreprocessorTree` as physical tokens with a false presence condition.
The grammar parser normally consumes the active `ExpandedTokenView`; tooling may parse inactive
regions speculatively without changing the authoritative presence condition.

Preprocessor identities are allocated entirely in the lexical/preprocessing domain. They never
refer to grammar `CSTNodeId` or semantic `DeclId`, because neither exists when expansion provenance
is constructed. Later CST and AST nodes point back to these IDs.

## Lossless CST

Parsing returns two linked immutable trees. The source/preprocessor tree owns physical slices and is
the authority for formatting; the grammar tree owns the active expanded-token sequence and is the
authority for syntactic structure. A macro invocation's physical spelling and its expanded grammar
tokens are therefore represented once in their respective domains instead of being forced into one
contradictory leaf sequence.

```text
SourceGreenElement = PhysicalSliceElement(PhysicalSliceId) |
                     SourceNode(SourceGreenNodeId)

ExpandedTokenSliceId = {
    parent: ExpandedTokenId,
    spellingRange: ByteRange,
    virtualKind: TokenType
}

GrammarTokenRef = Whole(ExpandedTokenId) | Slice(ExpandedTokenSliceId)
GrammarGreenElement = GrammarToken(GrammarTokenRef) | GrammarNode(GrammarGreenNodeId)

ExpandedTokenRange = {
    view: ExpandedTokenViewId,
    startIndex: UInt64,
    endIndex: UInt64
}

CSTNodeId = SourceCSTNode(SourceGreenNodeId)
          | GrammarCSTNode(GrammarGreenNodeId)

SourceGreenNode = {
    kind: SourceCSTKind,
    children: NodeList<SourceGreenElement>,
    byteWidth: UInt32,
    flags: SourceCSTFlags
}

SourceCSTFlag = ContainsDirective | ContainsInactiveText | ContainsMacroSpelling |
                ContainsSourceRecovery | ContainsDiagnostics
SourceCSTFlags = CanonicalFiniteSet<SourceCSTFlag>

GrammarGreenNode = {
    kind: CSTKind,
    children: NodeList<GrammarGreenElement>,
    expandedTokenCount: UInt32,
    flags: CSTFlags
}

CSTFlag = ContainsMissingToken | ContainsSkippedToken | ContainsAmbiguity |
          MacroDerived | ContainsDiagnostics
CSTFlags = CanonicalFiniteSet<CSTFlag>

RedNode = {
    green: SourceGreenNodeId | GrammarGreenNodeId,
    parent: Option<RedNodeId>,
    childIndex: UInt32,
    absoluteRange: SourceRangeSet
}

LosslessCST = {
    sourceTree: SourceGreenNodeId,
    grammarTree: GrammarGreenNodeId,
    preprocessing: PreprocessorTreeId,
    expandedTokens: ExpandedTokenViewId
}

AmbiguityDescriptor = {
    ownedRange: ExpandedTokenRange,
    alternatives: NonEmpty<NonOwningParseAlternative>
}
```

Green nodes contain only structural information and can be hash-consed. Red nodes are immutable
views that supply parent and absolute-position context. A macro-derived CST node may map to a set of
physical source ranges; its primary diagnostic range follows the token-origin policy in chapter 2.

`REP-CST-005`: `ExpandedTokenRange` is half-open in its named `ExpandedTokenView` and satisfies
`startIndex <= endIndex <= view.tokens.count`. An `ExpandedTokenSliceId.spellingRange` is a valid
UTF-8 byte range within its parent token spelling and its `virtualKind` is authorized by a named
token-splitting rule. Ambiguity ownership and field bindings use these exact coordinates, never
lexer-buffer pointers.

`LosslessCST.sourceTree` is exactly `PreprocessorTree.root`, not a separately constructed copy.
Preprocessing builds the source-green view; parsing adds only the grammar tree and the aggregate
links. Validation requires ID equality and the physical-slice bijection, so directive/macro/include
structure has one owner.

The source tree has explicit nodes for preprocessor directives, macro definitions/invocations,
include boundaries, and inactive regions. The grammar tree has explicit nodes for:

- every delimiter and separator;
- modifiers and attributes in written order;
- ambiguous syntactic forms;
- `MissingToken(expectedKind, anchor)` inserted during recovery; and
- `SkippedTokens(items, recoveryRule)` retained during synchronization.

`REP-CST-001`: Every physical slice occurs exactly once in the source-tree ownership projection.
Every active expanded token's spelling is covered exactly once in the grammar-tree ownership
projection: either one `Whole` leaf or a complete, ordered, non-overlapping set of `Slice` leaves,
possibly inside an explicit `SkippedTokens` node.

`REP-CST-002`: Formatting `LosslessCST.sourceTree` in identity mode reproduces the physical source.
The expanded grammar tree is not a formatter authority and is not required to reproduce macro
invocation spelling, directives, or inactive text. The expansion projection links its leaves back
to physical/preprocessor provenance through each canonical `ExpandedToken.origin`; there is no
second token-to-origin map that can disagree.

`REP-CST-003`: Parser recovery creates data. It must not rewrite a token kind, drop a token, or
pretend a missing token existed in the source.

`REP-CST-004`: An ambiguity node owns its expanded token range once. Alternatives are non-owning
shape descriptors over that range, not green subtrees that duplicate token leaves. Binding chooses
or diagnoses an alternative and records the selected descriptor in provenance.

## Stage-indexed AST

The semantic tree is a family of representations, not a mutable object gradually filled in:

```text
Stage = Surface | Scoped | Bound | Typed | Elaborated | IRReady
LocalNodeIndex = UInt64

SyntaxNode<S> = {
    id: NodeId<S>,
    kind: ASTNodeType<S>,
    fields: NodeFields<S>
}

ASTOriginField: FieldName = FieldName(text: "origin", wireTag: 1)

ASTSnapshot<S> = {
    id: ASTSnapshotId<S>,
    stage: S,
    schema: SchemaVersion,
    roots: NonEmpty<NodeId<S>>,
    nodes: CanonicallyOrderedMap<NodeId<S>, SyntaxNode<S>>,
    sourceDependencies: CanonicallyOrderedSet<SourceFileSnapshotId>,
    semanticSnapshot: SemanticSnapshotId,
    externalDependencies: CanonicallyOrderedSet<ExternalRef>
}

ASTSnapshotId<S> = ContentId<CanonicalASTSnapshotRecord<S>>

CanonicalLocalNodeFields<S> =
    canonical projection of NodeFields<S> with each same-snapshot AST reference encoded by
    LocalNodeIndex

CanonicalASTSnapshotRecord<S> = {
    stage: S,
    schema: SchemaVersion,
    roots: NonEmpty<LocalNodeIndex>,
    nodes: NodeList<CanonicalSyntaxNodeRecord<S>>,
    sourceDependencies: CanonicallyOrderedSet<SourceFileSnapshotId>,
    semanticSnapshot: SemanticSnapshotId,
    externalDependencies: CanonicallyOrderedSet<ExternalRef>
}

CanonicalSyntaxNodeRecord<S> = {
    kind: ASTNodeType<S>,
    fields: CanonicalLocalNodeFields<S>
}
```

`CanonicalASTSnapshotRecord` encodes same-snapshot AST references by `LocalNodeIndex`, not by the
enclosing `ASTSnapshotId`; publication derives that ID from the canonical record and then derives
each `NodeId<S>` from `(ASTSnapshotId<S>, LocalNodeIndex)`. This removes an identity-hash cycle.
`CanonicalSyntaxNodeRecord.fields` is derived bijectively from the published fields; decoding supplies
the enclosing snapshot ID to restore each local reference. The node map contains exactly the
derived IDs, every root belongs to that map, every
same-snapshot structural AST edge resolves in it, and `stage = S`. Cross-snapshot structural or
semantic edges occur only through `ExternalRef`; an `Origin` may separately retain its specified
provenance identity in an earlier snapshot. Thus `ASTSnapshot<S>` is the immutable owning unit
missing from a naked `SyntaxNode<S>`; copying a node reference never extends the lifetime of mutable
builder state.

Every AST descriptor contains exactly one required, serialized `ASTOriginField` whose value is an
`Origin` and whose edge category is `Provenance`. Thus `origin` is ordinary schema-visible storage,
not a header field hidden from generic traversal. Typed node notation may continue to write
`node.origin` as sugar for reading that field.

Diagnostics belong to `CheckResult` and the semantic-query result that produced the node, not to
the structural node. A serialized analysis snapshot may materialize a separate
`DiagnosticIndex = NodeMap<QueryKey, DiagnosticSet>`; its values are the exact deterministic query
diagnostic sets. Reusing the same structural node under another context therefore cannot attach a
contradictory mutable/node-local diagnostic field.

### Surface AST

`SurfaceAST` removes punctuation that has no semantic role while retaining a `Parsed(cst)` origin
for every node. It preserves written distinctions needed for diagnostics and compatibility, such as
C-style versus colon-style declarations, omitted types, written generic arguments, and modifier
order. Names are text plus hygiene/origin identity; no name has been resolved.

### Scoped AST

`ScopedAST` assigns stable `DeclFragmentId` and `ScopeId` values, classifies parsed modifiers
and attributes, and records written scope membership/order in a `FragmentScopeGraph`. It does not
resolve arbitrary name references or pretend that each written redeclaration is a distinct logical
entity.

The `FreezeDeclIndex` boundary groups compatible fragments, freezes logical `DeclId` values,
and rewrites the fragment graph into a `FrozenScopeGraph`. `BoundAST` and all later stages use only
the frozen graph and retain fragment origins separately.

### Bound AST

`BoundAST` replaces lexically decidable name uses with one of:

```text
BoundName = Resolved(BoundDeclUse)
          | OverloadSet(NodeList<LookupCandidate>)
          | DeferredMemberLookup(base: BoundExpr, name: Name, recipe: LookupRecipe)
          | Ambiguous(NodeList<LookupCandidate>, ErrorId)
          | Unresolved(Name, ErrorId)
```

Binding preserves lookup paths and visibility decisions. A member whose lookup requires the checked
type of its base remains `DeferredMemberLookup`; expression checking resolves it after checking the
base. Binding does not choose a callable overload when argument types are required to do so.

### Typed AST

Every `TypedExpr` has one canonical classifier. A value classifier contains its type and value
category; other classifiers do not manufacture placeholder values. Every callable declaration has a
checked `CallableSignature`; every generic declaration has a checked binder and constraint set. Calls
carry a chosen declaration and complete generic solution, but implicit operations may still be
represented as plans.

```text
TypedValueProvenance =
    NoAdditionalValueProvenance
  | PointerLikeProvenance(proof: PointerLikeProof)

TypedExpr = {
    ...,
    classifier: Classifier,
    valueProvenance: TypedValueProvenance,
    effects: EffectSet,
    directCapabilityUses: NodeList<CapabilityUse>,
    origin: Origin
}
```

`REP-TYP-001`: `PointerLikeProvenance(p)` is permitted exactly for
`ValueClassifier(p.resultType, RValue)`. Every typed reference/pointer value that may be
dereferenced has this provenance; a type alone cannot authorize dereference. Ordinary values,
storage, type-level expressions, overload sets, and errors use `NoAdditionalValueProvenance` unless
their closed recovery alternative explicitly carries a typed error handle.

`REP-TYP-002`: Identity-preserving binding, copy, reference-view formation, argument passing, and
return preserve the complete pointer-like shape. A registered pointer-like conversion supplies a new
checked proof. Control-flow merge requires equal referent, address-space, access, mutability,
lifetime, and physical-source-provenance facts and joins only alias provenance through `joinAlias`;
otherwise the merge has a structured incompatibility or uses a named registered representation
rule. No operation derives provenance from the destination node ID or from equal `TypeId` values.

### Elaborated AST

`ElaboratedAST` makes all semantics that affect evaluation explicit:

- implicit conversions and their witnesses;
- default arguments and argument reordering;
- inferred generic arguments and constraint witnesses;
- implicit receivers and dispatch mode;
- existential opening/packing;
- synthesized accessors, constructors, and conformance thunks; and
- implicit loads, reference-view formation, write-backs, and temporary lifetimes.

An elaborated call is therefore directly interpretable without re-running overload resolution.

### IR-ready AST

`IRReadyAST` uses a small, typed set of constructs that map structurally to frontend IR. Surface-only
forms such as operator syntax, lambdas, properties, `defer`, and target switches have been rewritten
to explicit IR-ready forms. Generated declarations are ordinary immutable IR-ready nodes with
`Synthesized` provenance.

Abstract storage is also eliminated at this boundary. A property or declared subscript has become
explicit getter, setter, or ref-accessor calls with captured receiver/index evaluation; every
IR-ready storage is proven physical storage. The IR-ready AST and IR therefore cannot reinterpret
an assignable abstract
projection as a valid `__ref`/`__constref` argument or silently allocate a reference temporary. A
physical-mode property argument reaches the IR-ready AST only after its exact access-indexed
accessor call and
stored dereference have produced a distinct proof-carrying physical endpoint.

`REP-STG-001`: A node in stage `S+1` refers to its stage-`S` origin but never mutates or embeds a
writable pointer to it.

`REP-STG-002`: A stage constructor is total. If checking fails it constructs the stage-appropriate
error node with the strongest classifier known.

`REP-STG-003`: Semantic caches are keyed by node/query identity and live in a semantic database;
they are not serialized as mutable fields of AST nodes.

## Uniform node schema and generic editing

All node types are generated from a versioned schema. Each field declares a name, closed value
kind (including presence and collection shape), edge category, stage availability, and serialization
policy:

```text
SchemaVersion = (major: UInt16, minor: UInt16)
StageSet = BitSet<Stage>

FieldName = {
    text: Utf8Identifier,
    wireTag: UInt32
}

NodeKind = {
    family: SourceCST | GrammarCST | AST | Semantic,
    wireTag: UInt32,
    stableName: QualifiedName
}

ASTNodeType<S> = { k: NodeKind | descriptor(k).family = AST and S in descriptor(k).stages }
NodeFields<S> = CanonicallyOrderedMap<FieldName, FieldValue>

FieldValueKind = ScalarKind(T)
               | NodeKindValue(K)
               | ListKind(element: FieldValueKind)
               | MapKind(key: FieldValueKind, value: FieldValueKind)
               | OptionalKind(value: FieldValueKind)

FieldWirePolicy = SerializedField
                | DerivedField(rule: RuleId, inputs: NonEmpty<FieldName>)

FieldDescriptor = {
    name: FieldName,
    valueKind: FieldValueKind,
    edge: Structural | Semantic | Provenance,
    stages: StageSet,
    wire: FieldWirePolicy
}

NodeDescriptor = {
    kind: NodeKind,
    baseKind: Option<NodeKind>,
    fields: NodeList<FieldDescriptor>,
    invariants: NodeList<RuleId>
}

AnySchemaNodeRef = SyntaxNodeRef(AnyNodeId)
                 | SourceGreenRef(SourceGreenNodeId)
                 | GrammarGreenRef(GrammarGreenNodeId)
                 | SchemaValueRef(ContentId<SchemaValue>)

FieldMapEntry = {
    key: FieldValue,
    value: FieldValue
}

RegisteredScalarValue = {
    type: QualifiedName,
    canonicalEncoding: ByteString
}

FieldValue = ScalarValue(RegisteredScalarValue)
           | SchemaNodeValue(AnySchemaNodeRef)
           | ListValue(NodeList<FieldValue>)
           | MapValue(NodeList<FieldMapEntry>)
           | OptionalValue(Absent | Present(FieldValue))

OriginUpdateRule = PreserveExplicitOrigin
                 | DeriveOrigin(rule: RuleId)
                 | ReplaceOrigin(origin: Origin)

ProductionId = {
    grammarVersion: SchemaVersion,
    qualifiedName: QualifiedName
}

SourceCSTKind = SourceRoot | Directive | MacroDefinition | MacroInvocation |
                IncludeBoundary | ConditionalRegion | InactiveRegion |
                SourceRecovery | RegisteredSourceKind(NodeKind)

CSTKind = GrammarRoot | Production(ProductionId) | Ambiguity |
          MissingToken | SkippedTokens | RegisteredGrammarKind(NodeKind)

NonOwningParseAlternative = {
    production: ProductionId,
    alternativeOrdinal: UInt32,
    range: ExpandedTokenRange,
    fieldBindings: NodeMap<FieldName, ExpandedTokenRange>,
    recoveryCost: UInt32
}

NodeSchemaRegistry = {
    version: SchemaVersion,
    nodes: CanonicallyOrderedMap<NodeKind, NodeDescriptor>,
    grammarProductions: CanonicallyOrderedMap<ProductionId, NodeKind>,
    stageKinds: NodeMap<Stage, CanonicallyOrderedSet<NodeKind>>,
    migrations: NodeList<SchemaMigrationDescriptor>
}

SchemaMigrationDescriptor = {
    from: SchemaVersion,
    to: SchemaVersion,
    kindRemaps: NodeMap<NodeKind, NodeKind>,
    fieldRemaps: NodeMap<(NodeKind, FieldName), FieldName>,
    insertedDefaults: NodeMap<(NodeKind, FieldName), FieldValue>,
    removedOptionalFields: CanonicallyOrderedSet<(NodeKind, FieldName)>,
    validationRules: NonEmpty<RuleId>
}
```

Every named production in `grammar.ebnf` has exactly one `ProductionId` and registry entry. A
production node's descriptor names each semantic child/range role; punctuation remains token leaves
and need not become a semantic field. Recovery and ambiguity use the dedicated closed kinds above.
Every `ASTNodeType<S>` and semantic value constructor likewise has exactly one descriptor. Stable names
are diagnostic labels; `(family, wireTag)` is the wire discriminator, and wire tags are never reused
after publication.

`FieldValue` is the one reflective carrier across all four node families. A `MapValue` key must be
a scalar or schema-node reference with canonical encoding; entries are sorted by that encoding and
duplicate keys are rejected. Its descriptor's `MapKind(key,value)` recursively validates the
key/value kinds. Lists preserve order. Thus a descriptor cannot advertise a CST/semantic node edge or a
node-valued map that the generic API cannot return.

Every `ScalarKind(T)` names a registry codec that bijectively encodes values of `T` as
`RegisteredScalarValue(type(T), canonicalEncoding)`. `Origin`, `CanonicalArgument`, ranges, enums,
and primitive values all use this route; pointer/object bytes are never a scalar encoding. Typed
access decodes with the same codec, so it cannot disagree with the generic value.

`REP-SCH-006`: `NodeFields` has exactly the descriptor's field-name domain at the node's stage.
`OptionalKind` is represented explicitly by `OptionalValue(Absent|Present)`; a missing map entry is
never used as optionality. `ListKind` and `MapKind` are the only collection constructors and may not
be combined with a second cardinality flag. Validation recursively matches each value to its one
declared kind, rejects illegal optional/collection nesting at the wrong field, and requires every
present value to match the wrapped kind. This same law controls migration defaults and wire
deserialization, so absent optional, empty list/map, and malformed missing required field are
distinct states.

`REP-SCH-007`: A `SerializedField` is present in the wire record. A `DerivedField` names a total,
versioned pure rule and its complete non-empty input field set; derived-field dependencies within a
descriptor are acyclic, and deserialization evaluates them in canonical topological order. The
result is then compared with the normal node validator. A field with no serialized bytes and no
derivation rule is forbidden, and provenance/structural semantic fields default to
`SerializedField`. Thus every exact `NodeFields` entry is reconstructed before a node is published.

The generated generic read API and immutable AST edit API provide:

```text
kind(node) -> NodeKind
origin(node) -> Origin
fieldCount(node, edgeFilter) -> UInt32
fieldDescriptor(node, i) -> FieldDescriptor
field(node, i) -> FieldValue
operandCount(node) -> UInt32
operand(node, i) -> AnySchemaNodeRef

ASTEditFailure =
    UnknownField(kind: NodeKind, field: FieldName)
  | FieldValueMismatch(field: FieldName, expected: FieldValueKind, actual: FieldValue)
  | CrossStageReference(field: FieldName, expected: Stage, actual: Stage)
  | DanglingReference(reference: AnySchemaNodeRef)
  | InvariantViolation(rule: RuleId)
  | InvalidRewriteReplacement(expectedKind: NodeKind, actualKind: NodeKind)

ASTEditResult<S, K> = {
    snapshot: ASTSnapshot<S>,
    node: NodeRef<S, K>
}

StagePreservingRewriter<S> =
    forall K . NodeRef<S, K> -> Result<NodeRef<S, K>, ASTEditFailure>

withField<S, K>(snapshot: ASTSnapshot<S>, node: NodeRef<S, K>,
                fieldName: FieldName, value: FieldValue,
                originRule: OriginUpdateRule)
    -> Result<ASTEditResult<S, K>, ASTEditFailure>

withOrigin<S, K>(snapshot: ASTSnapshot<S>, node: NodeRef<S, K>, origin: Origin)
    -> Result<ASTEditResult<S, K>, ASTEditFailure>

rewrite<S, K>(snapshot: ASTSnapshot<S>, node: NodeRef<S, K>,
              rewriter: StagePreservingRewriter<S>)
    -> Result<ASTEditResult<S, K>, ASTEditFailure>
```

Here `K` is the statically accepted node-kind family of the input position. `withField` and
`withOrigin` retain the exact dynamic kind; `rewrite` may choose another dynamic kind only when it
belongs to the same `K`. All three retain stage `S`, validate the complete result, and return a new
owning snapshot plus a reference into it. A transformation between stages is instead a named query
such as `Bind`, `Check`, `ElaborateNode`, or `LowerToIRReadyAST`; it cannot masquerade as a generic edit.

`withField` is functional: it validates the descriptor and returns a new snapshot, sharing
unchanged subtree storage where possible while leaving the input snapshot byte-identical. Typed
accessors are generated over the same storage and cannot disagree with the generic view.

`PreserveExplicitOrigin` retains the node's current origin (or, when the edited field is
`ASTOriginField`, accepts that explicit new value). `DeriveOrigin(rule)` writes
`Derived(previous: node.id, rule)` while changing the requested field. `ReplaceOrigin(origin)` writes
the supplied complete origin and is the only generic recovery/synthesis/import route. These policies
make a transform's provenance decision explicit without maintaining a second header value.

`REP-SCH-001`: Every semantically relevant field is visible through the schema. Hidden subclass
fields that generic serialization or rewriting cannot observe are forbidden.

`REP-SCH-002`: Structural operands have stable names. Operand index is an optimization and never
the specification of a role.

`REP-SCH-003`: A generic rewriter must preserve node invariants or return a validation error; it
cannot create a partially initialized node.

`REP-SCH-005`: For every AST node, descriptor lookup of `ASTOriginField` succeeds exactly once,
`origin(node)` returns that field, and `withOrigin(snapshot, node, origin)` has exactly the result of
`withField(snapshot, node, ASTOriginField, origin, PreserveExplicitOrigin)` with the same type
parameters. Provenance-filtered traversal observes the field; structural-only traversal does not.
Serialization, copying, and generic rewriting therefore cannot omit or disagree with typed
provenance access.

`REP-SCH-004`: The checked-in machine-readable registry is an implementation-blocking deliverable,
not inferred from C++ subclasses. Grammar coverage is a bijection between named EBNF productions
and `grammarProductions`; stage coverage is a bijection between generated node constructors and
`stageKinds`. The registry generator rejects duplicate tags/names, unknown field types, illegal
stage edges, missing production mappings, and descriptors without validators for their listed
invariants.

This design document specifies the registry format and completeness laws; the exhaustive per-node
registry is intentionally a review follow-up before implementation begins, because freezing field
roles now would prejudge the surface-to-IR-ready node taxonomy under review. Its absence is tracked as
a blocking specification item in chapter 12, not silently treated as an implementation detail.

## Types, values, and semantic graphs

Types, constant values, substitutions, constraints, and witnesses use the same immutable schema
machinery but are semantic graphs rather than source trees. Acyclic structural values are interned
by content inside a `SemanticSnapshot`. Recursive nominal and conformance values use an immutable
identity/definition split: an identity may be referenced before its separately published definition,
and the frozen snapshot validates the resulting strongly connected graph.

Subtype witnesses—including generic table values, specializations, bound parameters,
keyed lookups, and existential extractions—are registered `SchemaValue` alternatives, not opaque
side-table handles. Generic operand enumeration, `withField`, substitution, copying, and
serialization therefore work through the same node schema used for types and constants; chapter 14
defines their classifier and operational validation.

Nominal identity is represented explicitly by `DeclId`; interning does not make two distinct
nominal declarations equal. Recursive nominal types refer to a declaration identity, not a cyclic
physical type object. The identity/definition split keeps serialization finite and non-recursively
nested; semantic graph sections may still contain forward references and SCCs.

## Stable identity

Construction uses private provisional handles. Freezing validates the graph, canonically sorts
content/identity records, assigns frozen IDs, and rewrites every handle before publication. Only
frozen IDs may occur in serialized nodes or persistent query keys.

Snapshot-local frozen handles are namespaced by snapshot:

```text
NodeId<S>   = (ASTSnapshotId<S>, LocalNodeIndex, StageTag)
ScopeId     = (SemanticSnapshotId, LocalScopeIndex)
TypeHandle  = (SemanticSnapshotId, CanonicalValueIndex)

ExportedId = {
    module: ModuleStableId,
    path: CanonicalDeclPath,
    kind: DeclKind,
    signature: CanonicalSignatureEncoding
}
```

`DeclId`, `CanonicalDeclPath`, `DeclDisambiguator`, and
`CanonicalSignatureEncoding` are defined once in chapter 4. They are revision-independent nominal
identities and therefore deliberately do not share the snapshot-local tuple form above.

Local IDs may change after an edit. Public/importable declarations additionally receive an
`ExportedId` containing the exact canonical path and versioned alpha-normalized canonical-signature
encoding. The signature separates overloads while a two-phase nominal identity supports recursive
signatures. Hashes of path/signature bytes are lookup accelerators only and never define equality.
An implementation that writes compact hash references also writes a canonical collision bucket with
the full discriminator bytes; deserialization resolves the bucket by exact comparison or rejects an
ambiguous/corrupt reference. Content hashes detect stale external references. Source byte offsets
alone are not declaration identity.

`TypeHandle` is compact snapshot storage for the `CanonicalTypeRecord` whose collision-safe
`TypeId` is defined in chapter 4. It is never serialized or compared as semantic type identity;
freezing rewrites handles to `TypeId` in nodes, query keys, and exported data.

## Serialization and copying

Each snapshot serializes as a versioned collection of content-addressed chunks. The wire schema uses
stable numeric node/field/variant tags, length-delimited field payloads, canonical tag order, an
unknown-optional-field extension bag, and indexed graph records that permit forward/SCC references.
Required unknown tags fail loading; optional unknown payloads round-trip byte-for-byte.

The chunks are:

1. schema version and feature bits;
2. string/name table;
3. source snapshot references and line maps;
4. node records grouped by representation stage;
5. canonical semantic values plus identity/definition graph records;
6. structural, semantic, and provenance edge tables;
7. diagnostics; and
8. exported-ID index.

Serialization is deterministic: maps are emitted in canonical key order and diagnostics in their
specified order. Construction order and provisional handles are erased by freezing. Process
addresses, cache state, scheduler states, and hash-table iteration order are never serialized.

Copying a snapshot is constant-time reference sharing. Editing uses a builder that owns unpublished
nodes; `freeze()` validates all invariants and publishes a new immutable snapshot. Builders are
single-owner values and cannot expose mutable nodes through the public AST API.

`REP-SER-001`: Deserialize followed by serialize without schema migration is byte-identical.

`REP-SER-002`: Unknown optional fields survive a load/save round trip through their raw extension
bag; unknown required fields produce a version diagnostic and no partially loaded snapshot.

`REP-SER-003`: Deserialization validates node kind, field type, edge target, graph identity/
definition completeness, stage, and declared invariants before publishing the snapshot.

## Example: one expression across stages

For `f(1)`:

```text
CST:
  CallSyntax(NameToken("f"), OpenParen, IntToken("1"), CloseParen)

Surface:
  Call(Name("f"), [IntLiteral(raw="1")])

Bound:
  Call(OverloadSet([BoundDeclUse(f_int), BoundDeclUse(f_float)]),
       [IntLiteral(value=1)])

Typed:
  Call(result=Selected(winner.use=BoundDeclUse(DeclRef(f_int))),
       args=[IntLiteral(value=1, classifier=ValueClassifier(int, RValue))],
       classifier=ValueClassifier(R, RValue))

Elaborated:
  ElaboratedCall(
      callee=CallableValue(
          dispatch=Direct(DeclRef(f_int)),
          contract=Effective(contract_f_int)),
      receiver=None, signature=sig_f_int,
      args=[BoundStorageAccessPlan(
          identityRecipe(terminal=PassArgument(ImmediateValue(arg0))),
          operandBindings)], result=R)

IR-ready:
  CallRegion(preparation=[Let(arg0, ConstInt(1))],
             call=DirectCall(f_int, [arg0]),
             normalCompletion=[], exceptionalCompletion=[], result=R)
```

Each line is a new node graph with an origin edge to the preceding line. Overload candidates and
the chosen conversion remain inspectable even though the IR-ready AST no longer needs the overload set.

## Compatibility notes

The current compiler has useful pieces of this design: `Val` operands provide a uniform DAG-like
interface, `FIDDLE` drives node metadata and serialization, AST serialization exists, and many
types are hash-consed by `ASTBuilder`. The syntax tree, however, is mutated through declaration
check states and expression fields; parser output is not a lossless CST; comments are not attached
through a formatter-grade trivia model; and synthesis inserts mutable declarations into existing
containers. The replacement design preserves the useful uniformity while removing stage mutation
and implicit state.
