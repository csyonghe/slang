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

SourceFileSnapshotId = ContentId<SourceFileSnapshot>

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

FinalizeInterpretedView(base: SourceViewId,
                        directives: NodeList<SourceLineDirective>) -> SourceView
logicalLocation(range: SourceRange, result: PreprocessorExpansionResult)
    -> (presumedPath: Utf8String, line: UInt32, column: UInt32)

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

The `SourceView` passed to `Lex` contains only line directives supplied by an already-published
outer interpretation (normally none for a primary file). Lexing never pre-scans `#line`.
Preprocessing evaluates active line directives in source order inside
`PreprocessorLogicalLocationState`; after expansion, `FinalizeInterpretedView` appends exactly those
directives and `PreprocessorExpansionResult.interpretedViews[base]` names the resulting view. An
inactive `#line` contributes nothing. Diagnostics and `BuiltinLine`/`BuiltinFile` use this explicit
state/final view, so neither lexing nor a raw directive scan is a circular authority.

`REP-SRC-001`: A snapshot is immutable. Editing creates a new snapshot and an explicit change map
from old byte ranges to new byte ranges.

`REP-SRC-002`: Source locations in tokens and syntax nodes identify a source view and byte range; they
must not be raw pointers into a mutable source manager.

`REP-SRC-003`: Every range satisfies
`startByte <= endByte <= resolve(resolve(range.view).key.snapshot).bytes.count`.
`SourceRangeSet.ranges` is duplicate-free and in token-origin traversal order; adjacent ranges are
coalesced only when they belong to the same view and no origin boundary would be lost. A macro-
derived CST occurrence may therefore name ranges in several snapshots without inventing one
contiguous span.

`REP-SRC-004`: `ByteRange` is half-open and satisfies `startByte <= endByte` in the coordinate
space of its containing field. A `SourceTextSlice` range is bounded by its named snapshot. For a
`Token` with a physical spelling, `span` is `directSpellingRange(token)`; for `Trivia`, it is
the stored `span`. In either case, `physicalSpelling.snapshot =
resolve(span.view).key.snapshot` and its byte range equals `[span.startByte, span.endByte)`; the
fields provide a lazy byte view and an explicit source location, not competing extents.

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
anchor. Every such parent/anchor view is published before the derived view and cannot be the view
itself or one of its descendants; `PrimarySourceView` and an unanchored generated view have no
predecessor. The resulting predecessor relation is acyclic and is validated before computing the
child `ContentId`. Equal decoded bytes do not merge views whose include use, view path, or
line-directive interpretation differs.

## Tokens, trivia, views, and preprocessing

The lexer's authoritative product is one flat, lossless sequence. `TokenList` deliberately has no
parallel token table, trivia table, gap table, spelling-piece table, or boundary-token wrapper:

```text
TokenOriginId = ContentId<TokenOrigin>

Token = {
    type: TokenType where not isTrivia(type),
    physicalSpelling: Option<SourceTextSlice>,
    logicalSpelling: Text,
    removedLineContinuations: NodeList<ByteRange>,
    origin: TokenOriginId
}

Trivia = {
    type: TokenType where isTrivia(type),
    isDocumentation: Bool,
    span: SourceRange,
    physicalSpelling: SourceTextSlice
}

isTrivia(type) iff type in
    {WhiteSpace, NewLine, LineComment, BlockComment, LineContinuation}

TokenList = NodeList<Token | Trivia>
TokenListId = ContentId<TokenList>
TokenListIndex = UInt64

LexicalContext = {
    sourceView: SourceViewId,
    options: LexOptions
}

LexicalContextId = ContentId<LexicalContext>

TokenListElementRef = {
    list: TokenListId,
    index: TokenListIndex
}

TokenRef = ref: TokenListElementRef where resolve(ref) is Token
TriviaRef = ref: TokenListElementRef where resolve(ref) is Trivia

TokenListRange = {
    list: TokenListId,
    startIndex: TokenListIndex,
    endIndex: TokenListIndex
}

TokenListView = {
    list: TokenListId,
    selection: TokenListSelection
}

TokenListSelection =
    SelectNone
  | AllElements
  | IsToken
  | IsTrivia
  | IsMarkup
  | IsNotEndOfFile
  | IsActive(activity: TokenActivityMapId)
  | And(CanonicalFiniteSet<TokenListSelection>)

TokenActivity = Active | Inactive
TokenActivityMap = NodeMap<TokenListElementRef, TokenActivity>
TokenActivityMapId = ContentId<TokenActivityMap>

TokenListViewId = ContentId<TokenListView>

PhysicalTokenView(list returned by Lex) = TokenListView(list, IsToken)
SemanticTokenView(list) = TokenListView(list, IsToken)
MarkupTokenView(list) = TokenListView(list, IsMarkup)

TokenSpan = {
    view: TokenListViewId,
    startIndex: UInt64,
    endIndex: UInt64
}

TokenReader::ParsingCursor = {
    view: TokenListViewId,
    nextIndex: UInt64
}

TokenFlag = AtStartOfLine | AfterWhitespace
TokenFlags = CanonicalFiniteSet<TokenFlag>
tokenFlags(token: TokenRef) -> TokenFlags

selectedCount(view: TokenListViewId) -> UInt64
selectedElement(view: TokenListViewId, index: UInt64) -> Option<TokenListElementRef>
baseIndex(view: TokenListViewId, index: UInt64) -> Option<TokenListIndex>
lexedSourceRange(range: TokenListRange) -> SourceRange
```

The sum in `TokenList` is the entire owning representation. An `EndOfFile` `Token` is the final
element, including for an empty file; there is no start-of-file or end-of-file wrapper. A
`TokenListView` owns no elements and stores no copied index vector. Its selected indices are the
deterministic projection of `selection` over `list`, and composition is canonical conjunction.
`PhysicalTokenView(list)` means the `IsToken` view of a list returned by `Lex`; the same selection
over preprocessor output is a token view but is not called physical. `SemanticTokenView` and
`MarkupTokenView` preserve the established `lexAllSemanticTokens` and `lexAllMarkupTokens`
policies as named projections over the one list rather than separate lexer runs.

`IsMarkup` selects every `Token` plus `LineComment` and `BlockComment` trivia while excluding
`WhiteSpace`, `NewLine`, and `LineContinuation`; `SemanticTokenView` is the `IsToken` projection.
`IsNotEndOfFile` selects every trivia element and every token whose type is not `EndOfFile`; it is
used when embedding one file's contents into another while retaining the child snapshot's own EOF.
Every `TokenListRange` is half-open and satisfies `startIndex <= endIndex <= list.count`. A
`TokenRef` or `TriviaRef` is valid only when its referenced alternative has the stated kind.
`TokenSpan` indices are coordinates in the selected sequence, not base-list indices. For
`index < selectedCount(view)`, `selectedElement` returns the selected element and `baseIndex`
returns its stable base-list index; both return `None` at or beyond the end. Empty spans and a span
whose two endpoints equal `selectedCount(view)` are valid.

`lexedSourceRange` accepts a nonempty range in a list returned by `Lex`. All elements must belong to
one source view; the result runs from the first element's physical-spelling start to the last
element's physical-spelling end. It is undefined for preprocessing output and rejected rather than
made to guess when the preconditions do not hold.

Before hashing a view, selection normalization recursively flattens `And`, removes `AllElements`,
deduplicates and semantically sorts operands, maps an empty conjunction to `AllElements`, propagates
`SelectNone`, maps `And(IsToken, IsTrivia)` to `SelectNone`, and removes `IsMarkup` when `IsToken` is
also present. It removes `IsNotEndOfFile` when `IsTrivia` is present because EOF is a token. These
are the complete subsumption rules for this selection algebra. Every
`IsActive(map)` operand is valid only when `map` has exactly one activity entry for every element
of the view's base list. A `TokenActivityMap` is deliberately not called a condition map: it stores
the evaluated `Active`/`Inactive` result for one list, not the Boolean expression that led to it.

Leading and trailing trivia are adjacency views:

```text
LeadingTrivia(token: TokenRef) -> TokenListRange
TrailingTrivia(token: TokenRef) -> TokenListRange
```

Each result is the maximal contiguous run of `Trivia` elements immediately before or after the
token. Thus one inter-token run can be observed as the preceding token's trailing trivia and the
following token's leading trivia without being stored twice. Prefix trivia is before the first
non-EOF token; suffix trivia is before `EndOfFile`. `isDocumentation` is valid only on line/block
comments, as determined by `Trivia.type`, and documentation extraction is another view over these
ranges.

A token returned by `Lex` has a contiguous `physicalSpelling`. If backslash-newline splicing joins
characters into one logical token, that token owns the whole contiguous physical extent,
`logicalSpelling` contains the splice result, and `removedLineContinuations` identifies the exact
removed subranges. Those bytes are not duplicated as top-level trivia. A line continuation between
logical tokens is a `LineContinuation` `Trivia` element. This phase-order rule keeps the list flat
while exposing every removed byte. A macro-produced token may have no direct physical spelling;
its `origin` supplies all contributing sources.

For a list returned by `Lex`, every token has `SourceTokenOrigin` and a present
`physicalSpelling`, including the zero-width EOF token. A preprocessing output token may retain a
physical spelling when it directly reuses one contiguous source spelling; its macro/include origin
still records why that spelling appears at this output position. Paste, builtin, and synthesized
tokens have no direct physical spelling and reach their sources only through provenance.

`AtStartOfLine` and `AfterWhitespace` use the established `TokenFlag` names, but they are contextual
facts derived by `tokenFlags` from a token's preceding `Trivia` and logical-line boundary in its
current list. They are not copied into `Token`. The current storage-optimization flag `Name` is not
semantic, and `ScrubbingNeeded` is derived from `removedLineContinuations`, so neither is serialized
as independent authority. The start of a list is a virtual whitespace and logical-line boundary,
so its first `Token` has both flags. `AtStartOfLine` holds when no preceding `Token` follows the
latest unspliced newline boundary, including a newline within comment trivia; a
`LineContinuation` is not such a boundary. `AfterWhitespace` holds at list start or when the
immediately preceding trivia run has a whitespace effect (`WhiteSpace`, `NewLine`, or a comment),
and does not arise from `LineContinuation` alone. `EndOfFile` follows these same rules: it has both
flags in an empty list, and otherwise reflects only the suffix trivia. Moving the same immutable
`Token` into a differently contextualized list preserves `origin` but may change `tokenFlags`.

`TokenReader` is the established name for an ephemeral cursor over a `TokenListView`. Its only
mutable state is `(view, nextIndex)`. Construction requires a normalized selection that contains
`IsToken` (or `SelectNone`), proving that every selected element is a `Token`; a trivia-containing
`AllElements`, `IsTrivia`, or `IsMarkup` view is rejected. `peekToken()` and `advanceToken()` return
`Option<TokenRef>` and yield `None` at end without inventing a sentinel element. `getCursor()`
returns a `TokenReader::ParsingCursor`, and `setCursor()` may restore it only on the same view.
Reader state is neither serialized with the view nor part of token identity.

`REP-TOK-001`: For a `TokenList` returned by `Lex`, every non-EOF element has one contiguous
`physicalSpelling`, the EOF spelling is zero-width, and the ordered spellings partition the decoded
source view exactly. Their bytes concatenate to the snapshot's UTF-8 bytes. Resolving that view and
snapshot yields the `SourceFileRecord`, so identity output of an unmodified non-UTF-8/BOM input can
reproduce its original encoded `physicalBytes`.

`REP-TOK-002`: Physical spelling is preserved independently of logical spelling and decoded value.
`0x10`, `020`, and `16` may have the same integer value but different physical spellings. Applying
the ordered `removedLineContinuations` to a token's physical spelling yields exactly its logical
spelling. For every token, `physicalSpelling=None` requires an empty continuation list. When the
spelling is present, all continuation ranges are relative to it, strictly ordered, disjoint,
in-bounds, and each matches one accepted backslash-newline spelling. Macro/include copies either
retain this spelling and continuation metadata together or drop both; they cannot retain ranges in
a nonexistent coordinate space.

`REP-TOK-003`: Invalid bytes and malformed literals produce tokens or trivia with lexical
diagnostics; the lexed `TokenList` remains lossless.

`REP-TOK-004`: A `TokenListView` is immutable, non-owning, and order-preserving. Every selected
element resolves to the same `(list, index)` as in its base list. Serialization records only the
base list and normalized canonical selection; cached selected-index tables are disposable derived
data. A view with a mismatched or incomplete activity map is invalid, not an empty projection.

`REP-TOK-005`: Token derivation is topologically prior to the list that owns the derived token. For
each `TokenList`, every `SourceToken`/`SourceTrivia` in an element's transitive `TokenOrigin` graph
resolves to an already published predecessor list, and every `SourceNode`/`context` resolves to an
already published predecessor snapshot. No origin reachable from a list may refer to that list or
to a snapshot whose canonical content contains that list. Paste chains, argument substitution, and
rescan therefore freeze each intermediate result before using it as a later derivation input. A
builder may use provisional handles internally, but freezing rewrites them in this topological order
before computing any `TokenOriginId`, `TokenListId`, or `CSTSnapshotId`. This rule prevents a
`TokenListId -> TokenOriginId -> TokenListId` content-identity cycle.

## Staged concrete syntax

Lexing, preprocessing, declaration outlining, and fine parsing are immutable translations of
concrete representations. A translation is a function or scheduler query: it consumes immutable
inputs and returns an immutable result. The compiler does **not** materialize a separate object for
the act of rewriting. Provenance needed after the translation is stored directly on the produced
nodes and tokens.

```text
CSTStage = Lexed | PreprocessorStructured | MacroExpanded | DeclParsed | Parsed

CSTNodeId<S> = Terminal(TerminalNodeId<S>)
             | NonTerminal(NonTerminalNodeId<S>)

AnyCSTSnapshotId = exists S: CSTStage . CSTSnapshotId<S>
AnyCSTNodeId = exists S: CSTStage . CSTNodeId<S>

CSTNodeOrigin =
    LexedElement(element: TokenListElementRef)
  | Translated(origin: CSTTranslationOrigin)

CSTTranslationOrigin = {
    rule: RuleId,
    source: CSTTranslationSource
}

CSTTranslationSource =
    Consumed(inputs: NonEmpty<CSTOriginInput>)
  | Empty(anchor: CSTOriginAnchor)

CSTOriginInput =
    PreviousNode(node: AnyCSTNodeId)
  | PreviousToken(element: TokenListElementRef)
  | PhysicalSource(range: SourceRange)

CSTOriginAnchor = Before(node: AnyCSTNodeId)
                | After(node: AnyCSTNodeId)
                | AtSource(anchor: SourceRange where startByte = endByte)

TokenOrigin =
    SourceTokenOrigin(range: SourceRange)
  | DerivedTokenOrigin(derivation: TokenDerivation)

TokenDerivation = {
    rule: RuleId,
    inputs: NonEmpty<TokenOriginInput>,
    context: Option<AnyCSTNodeId>
}

TokenOriginInput = SourceToken(token: TokenRef)
                 | SourceTrivia(trivia: TriviaRef)
                 | SourceNode(node: AnyCSTNodeId)
                 | PhysicalSource(range: SourceRange)

TerminalNode<S> = {
    id: TerminalNodeId<S>,
    kind: TerminalNodeKind<S>,
    value: TerminalValue<S>,
    origin: CSTNodeOrigin
}

NonTerminalNode<S, K: NonTerminalKind<S>> = {
    id: NonTerminalNodeId<S>,
    kind: K,
    fields: NonTerminalFields<S, K>,
    origin: CSTNodeOrigin
}
```

`CSTTranslationOrigin` is retained data, not an instruction to replay and not an identity for a
translation event. It answers only why this result node exists. A source node may be referenced by
many later origins, and one later node may name several predecessor nodes. No output registry,
output ordinal, replacement program, or mutable back-link is required. Specification judgments such
as `input -> output` describe the translator's behavior; they do not require a runtime `Rewrite`
class.

The origin graph is acyclic because every input belongs to a predecessor snapshot or to an earlier
published node in the same construction transaction. A builder validates that order before
publishing. Content identity includes the direct origin, so two structurally equal nodes with
different macro, include, recovery, or synthesis provenance remain distinguishable when provenance
is observable.

`TokenDerivation` is the corresponding direct provenance for a produced token. The
[preprocessing chapter](04-preprocessing.md) refines
its rule and context for replacement-list substitution, argument prescan, stringizing, token paste,
includes, and builtin macros. Inputs point backward to prior tokens or CST nodes, so provenance
cannot form a cycle; `REP-TOK-005` makes “prior” a validated publication relation rather than
construction-order convention. Identifier equality does not inspect this provenance.

### Terminal and non-terminal nodes

A terminal node is a concrete token, trivia occurrence, token slice, or explicit missing terminal.
A non-terminal node is an occurrence of a grammar or representation production. These are the
standard compiler terms; there is no color-based node taxonomy.

```text
TokenSlice = {
    parent: TokenRef,
    spellingRange: ByteRange,
    virtualType: TokenType
}

TokenSliceId = ContentId<TokenSlice>

TerminalClass = TokenClass | TriviaClass | TokenSliceClass | MissingClass

TerminalNodeKind<S> = {
    kind: NodeKind where
        kind.family = TerminalNode and
        kind in currentNodeSchemaRegistry.domainKinds[Concrete(S)]
}

ExprCSTNodeId<S> =
    NonTerminalNodeId<S, kind where category(kind) includes ExprCSTCategory>
StmtCSTNodeId<S> =
    NonTerminalNodeId<S, kind where category(kind) includes StmtCSTCategory>
DeclCSTNodeId<S> =
    NonTerminalNodeId<S, kind where category(kind) includes DeclCSTCategory>

TerminalValue<Lexed> =
    TokenTerminal(token: TokenRef)
  | TriviaTerminal(trivia: TriviaRef)

TerminalValue<PreprocessorStructured> = TerminalValue<Lexed> | MissingTerminal
TerminalValue<MacroExpanded> = TerminalValue<Lexed>
TerminalValue<DeclParsed> = TerminalValue<MacroExpanded>

TerminalValue<Parsed> =
    TokenTerminal(token: TokenRef)
  | TokenSliceTerminal(slice: TokenSliceId)
  | MissingTerminal
```

`TokenList` remains the sole owner of `Token | Trivia` values. Terminals refer to those values and
never copy them. `TokenSlice` is admitted only by a named parsing rule, for example after generic
syntax has been selected and one `>>` spelling must supply two `>` terminals. A missing terminal has
an `Empty` translation origin naming its recovery rule and exact anchor.

A `PreprocessorStructured` missing terminal represents an expected directive delimiter such as a
recovered `#endif`; it is not a `TokenList` element and is excluded from token, trivia, physical,
semantic, and markup projections. `MacroExpanded` and `DeclParsed` do not inherit that alternative:
they may refer to the predecessor recovery node through provenance, but their own terminal
projections contain only the listed token/trivia values.

Every written constituent is an explicit named field of its containing non-terminal. For example:

```text
IfStatementFields = {
    ifKeyword: TerminalNodeId<Parsed>,
    leftParenthesis: TerminalNodeId<Parsed>,
    conditionExpr: ExprCSTNodeId<Parsed>,
    rightParenthesis: TerminalNodeId<Parsed>,
    trueBranch: StmtCSTNodeId<Parsed>,
    elseKeyword: Option<TerminalNodeId<Parsed>>,
    falseBranch: Option<StmtCSTNodeId<Parsed>>
}
```

The production descriptor attaches the `PAR-CST-COPRESENT` invariant to `elseKeyword` and
`falseBranch`, so the two optional fields cannot disagree about presence. This is the exact
seven-field generated `IfStatement` product; neither field is hidden behind an implementation-only
wrapper node.
Products, closed variants, optionals, and lists retain the same shape in typed and reflective APIs.
A repetition of `(comma, argument)` is a list of complete pairs, not parallel comma and argument
arrays. Trivia remains accessible through each referenced token and through predecessor CST nodes;
grammar productions do not silently discard it.

```text
fieldDescriptors<S>(kind: NonTerminalKind<S>) -> NodeList<FieldDescriptor>
field<S>(node: CSTNodeId<S>, key: FieldName) -> CSTFieldQueryResult
cstOperands<S>(node: CSTNodeId<S>) -> NodeList<CSTNodeId<S>>

withCSTField<S>(snapshot: CSTSnapshot<S>, node: CSTNodeId<S>,
                key: FieldName, value: CSTFieldValue, rule: RuleId)
    -> Result<CSTEditResult<S>, CSTEditFailure>

CSTEditResult<S> = {
    snapshot: CSTSnapshot<S>,
    node: CSTNodeId<S>
}

CSTFieldValue = FieldValue where every SchemaNodeValue is a CSTNodeRef or SchemaValueRef
CSTFieldQueryResult = UnknownField | InactiveField | FoundField(CSTFieldValue)

CSTEditFailure = UnknownCSTField(kind: NodeKind, field: FieldName)
               | ReadOnlyCSTField(kind: NodeKind, field: FieldName)
               | CSTFieldValueMismatch(field: FieldName,
                                       expected: FieldValueKind,
                                       actual: CSTFieldValue)
               | CSTInvariantViolation(rule: RuleId)
               | InvalidCSTOrigin(input: CSTOriginInput)
```

`field` and `cstOperands` are generated from the same schema as typed accessors. `cstOperands`
enumerates structural children in concrete source order. `withCSTField` validates the complete
product and returns a new snapshot; the produced node has
`Translated(rule, Consumed([PreviousNode(node)]))`. It cannot retain the old origin after changing
content. Occurrence-specific editing uses a `CSTCursor` to clone only the selected ancestor path.
Neither edit API creates or stores an operation object.

### CST snapshots and cursors

```text
LocalCSTNodeIndex = UInt64

TerminalNodeId<S> = {
    snapshot: CSTSnapshotId<S>,
    local: LocalCSTNodeIndex,
    kind: TerminalNodeKind<S>
}

NonTerminalNodeId<S, K = NonTerminalKind<S>> = {
    snapshot: CSTSnapshotId<S>,
    local: LocalCSTNodeIndex,
    kind: K
}

CSTSnapshot<S> = {
    id: CSTSnapshotId<S>,
    stage: S,
    schema: SchemaVersion,
    lexicalContext: LexicalContextId,
    root: NonTerminalNodeId<S>,
    terminals: CanonicallyOrderedMap<TerminalNodeId<S>, TerminalNode<S>>,
    nonTerminals: CanonicallyOrderedMap<NonTerminalNodeId<S>,
                                        NonTerminalNode<S, NonTerminalKind<S>>>,
    primaryList: TokenListId,
    tokenLists: CanonicallyOrderedSet<TokenListId>,
    activityMaps: NodeMap<TokenListId, TokenActivityMapId>,
    predecessors: CanonicallyOrderedSet<AnyCSTSnapshotId>,
    sourceDependencies: CanonicallyOrderedSet<SourceFileSnapshotId>
}

CanonicalCSTSnapshotForm<S> = ByteString produced by the canonical traversal below
CSTSnapshotId<S> = ContentId<CanonicalCSTSnapshotForm<S>>

CSTCursor<S> = {
    snapshot: CSTSnapshotId<S>,
    path: NodeList<CSTFieldStep>
}

CSTFieldStep = {
    field: FieldName,
    occurrence: Option<UInt32>
}
```

Snapshot-local indices are builder handles, not semantic identity. `CanonicalCSTSnapshotForm`
omits `CSTSnapshot.id`, replaces every same-snapshot node reference with its canonical local index,
and encodes every other field of the snapshot. Its traversal starts at `root`, visits structural
fields in descriptor/source order, then alternative and direct provenance edges, and assigns
canonical indices on first visit. It rejects unreachable nodes, dangling origins, origins that skip
an undeclared predecessor, and cycles. The published `id` must equal the `ContentId` of those bytes.
There is no parallel map binding translation outputs to nodes: the nodes themselves are the
outputs.

`CSTCursor` is ephemeral navigation context. Parentage is not stored on immutable nodes because a
node may be shared. Its path selects one occurrence from the root and can derive parent, occurrence,
and aggregate source ranges without changing node identity.

### Lexed concrete syntax

```text
TokenizedSourceFields = {
    elements: NodeList<TerminalNodeId<Lexed>>
}

BuildLexedCST(list: TokenListId,
              lexicalContext: LexicalContextId) -> CSTSnapshot<Lexed>
```

`BuildLexedCST` creates one terminal for each element of the flat `Token | Trivia` list, in order,
and wraps that list once in `TokenizedSource`. Each terminal has `LexedElement(element)`. The root covers
the entire list including EOF. Token-only, trivia-only, physical-token, semantic-token, and markup
projections are views over the same list, not alternative ownership structures.

The context's `sourceView` is the view passed to `Lex`, and `context.options` is the exact normalized
`LexOptions` used for that call. Every successor snapshot for the same primary unit retains this
`lexicalContext`; an included unit has its own context and is reached through predecessor edges.

Preprocessor structuring and expansion translate this snapshot into `PreprocessorStructured` and
`MacroExpanded` snapshots. Their complete state and macro rules are specified in the
[preprocessing chapter](04-preprocessing.md). This
chapter supplies their common immutable node, token, snapshot, and provenance framework only.

### Declaration-outline parsing

Parsing begins with a deliberately coarse grammar that finds declarations and the scope structure
needed to interpret the remaining syntax. It does not pretend to parse or type-check every
expression and statement.

```text
ParseDecls(input: CSTSnapshot<MacroExpanded>,
           grammar: DeclGrammar,
           vocabulary: GrammarVocabulary,
           options: DeclParserOptions)
    -> CheckResult<DeclParseResult>

DeclParseResult = {
    snapshot: CSTSnapshot<DeclParsed>
}

declOutlineIndex(result: DeclParseResult)
    -> NodeMap<DeclOutlineId, DeclOutline>
unparsedContentIndex(result: DeclParseResult)
    -> NodeMap<UnparsedContentId, UnparsedContent>
inactiveContentIndex(result: DeclParseResult)
    -> NodeMap<InactiveContentId, InactiveContent>

DeclOutlineId =
    NonTerminalNodeId<DeclParsed,
        kind where category(kind) includes DeclOutlineCSTCategory>
UnparsedContentId = NonTerminalNodeId<DeclParsed, UnparsedContentNode>
InactiveContentId =
    NonTerminalNodeId<DeclParsed,
        kind where category(kind) includes InactiveContentCSTCategory>
CStyleDeclaratorCSTNodeId =
    NonTerminalNodeId<DeclParsed,
        kind where category(kind) includes CStyleDeclaratorCSTCategory>
CStyleInlineTypeSpecifierCSTNodeId =
    NonTerminalNodeId<DeclParsed,
        kind where category(kind) includes CStyleInlineTypeSpecifierCSTCategory>

DeclOutlineBindingOrdinal = UInt32

DeclOutline = {
    id: DeclOutlineId,
    modifiers: NodeList<
        NonTerminalNodeId<DeclParsed,
            kind where category(kind) includes DeclModifierOutlineCSTCategory>>,
    introducer: Option<TerminalNodeId<DeclParsed>>,
    bindings: NonEmpty<DeclOutlineBinding>,
    members: NodeList<DeclOutlineId>,
    payload: DeclOutlinePayload,
    origin: CSTNodeOrigin
}

DeclOutlineBinding = {
    ordinal: DeclOutlineBindingOrdinal,
    kind: DeclKind,
    name: Option<TerminalNodeId<DeclParsed>>,
    directGeneric: DirectGenericMarker,
    header: DeclHeaderSyntax,
    body: DeclBodyOutline
}

DeclHeaderSyntax =
    NoDeclHeader
  | OrdinaryDeclHeader(content: UnparsedContentId)
  | CStyleDeclHeader {
        declarationSpecifiers: UnparsedContentId,
        declaratorPrefix: UnparsedContentId,
        name: TerminalNodeId<DeclParsed>,
        declaratorSuffix: UnparsedContentId
    }

DeclModifierOutlineFields =
    KeywordDeclModifier(token: TerminalNodeId<DeclParsed>)
  | AttributeDeclModifier {
        leftBracket: TerminalNodeId<DeclParsed>,
        content: UnparsedContentId,
        rightBracket: TerminalNodeId<DeclParsed>
    }

DeclOutlinePayload =
    OrdinaryDeclOutline
  | DeclGroupOutline {
        inlineTypeSpecifier: Option<CStyleInlineTypeSpecifierCSTNodeId>,
        declarators: NonEmpty<CStyleDeclaratorCSTNodeId>
    }
  | ImportDeclOutline {
        exportedKeyword: Option<TerminalNodeId<DeclParsed>>,
        importKeyword: TerminalNodeId<DeclParsed>,
        moduleName: ImportModuleNameFields,
        semicolon: TerminalNodeId<DeclParsed>
    }

ImportModuleNameFields =
    DottedImportModuleName {
        first: TerminalNodeId<DeclParsed>,
        remaining: NodeList<ImportModuleNameTailFields>
    }
  | StringImportModuleName(literal: TerminalNodeId<DeclParsed>)

ImportModuleNameTailFields = {
    dot: TerminalNodeId<DeclParsed>,
    name: TerminalNodeId<DeclParsed>
}

DirectGenericMarker =
    NonGeneric
  | DirectGeneric {
        leftAngle: TerminalNodeId<DeclParsed>
    }
  | RecoveredGeneric(error: ErrorId)

DelimiterKind = ParenthesisDelimiter | BracketDelimiter | BraceDelimiter

BalancedDelimiterEntry =
    MatchedDelimiter {
        kind: DelimiterKind,
        opener: UInt32,
        closer: UInt32
    }
  | UnmatchedOpeningDelimiter {
        kind: DelimiterKind,
        opener: UInt32,
        recoveryBoundary: UInt32,
        error: ErrorId
    }
  | UnmatchedClosingDelimiter {
        kind: DelimiterKind,
        closer: UInt32,
        error: ErrorId
    }

BalancedDelimiterSummary = {
    entries: NodeList<BalancedDelimiterEntry>,
    maximumDepth: UInt32
}

DeclBodyOutline =
    NoBody
  | DeclContainer {
        leftBrace: TerminalNodeId<DeclParsed>,
        rightBrace: TerminalNodeId<DeclParsed>
    }
  | DeferredContent(content: UnparsedContentId)

UnparsedContent = {
    id: UnparsedContentId,
    role: UnparsedContentRole,
    terminals: NodeList<TerminalNodeId<DeclParsed>>,
    range: TokenListRange,
    delimiters: BalancedDelimiterSummary,
    origin: CSTNodeOrigin
}

InactiveContent = {
    id: InactiveContentId,
    elements: NonEmpty<TerminalNodeId<DeclParsed>>,
    range: TokenListRange,
    origin: CSTNodeOrigin
}

UnparsedContentRole = DeclHeaderContent | GenericParameterContent |
                      TypeContent | ExprContent | StmtContent |
                      InitializerContent | CallableBodyContent |
                      AttributeArgumentContent | RecoveryContent
```

The outline grammar recognizes declaration introducers, every declaration binding, a direct
generic-parameter marker per binding, and balanced active delimiters. Namespace, aggregate,
interface, and extension bodies are recursively
outlined because they introduce declaration members. Callable bodies, initializers, expression and
statement regions, type spellings, defaults, and constraints remain `UnparsedContent`. Local
declarations and block scopes are discovered when their containing content is fine-parsed.

Most outline nodes have one `DeclOutlineBinding` with ordinal zero. A C-style declaration is the
existing language concept `DeclGroup`: its `DeclGroupOutline.declarators` are the direct structured
products generated by the paired grammar/profile. When the declaration specifiers contain an
inline `struct`, `class`, or `enum`, `inlineTypeSpecifier` names its structured product and the
binding list begins with that type declaration; it then contains one entry per declarator in source
order. Each binding has its own `DeclKind`. A declarator entry's `CStyleDeclHeader` references the
shared declaration-specifier content plus that declarator's exact prefix, direct name terminal, and
suffix. These are reference projections into the one structural group; shared type syntax is not
copied. Binding ordinals are gap-free in `[0, bindings.count)` and are the only early discriminator
among heterogeneous group members.

An import is the one declaration whose module-name operand is needed before ordinary fine parsing:
its `ImportDeclOutline` payload therefore retains the exact `import`/`__import`, optional
`__exported`, dotted-name-or-string, and semicolon terminals. This is still syntax-only. Resolving
that written name to a module interface is the separate query below; the outline never stores a
module pointer.

`UnparsedContent.terminals` is the exact ordered list of `DeclParsed` terminal children, so generic
traversal reaches every deferred token and trivia occurrence. It never owns a copied token buffer,
mutable parser cursor, or scope pointer. The descriptor marks `range` as a `DerivedField`; it is the
generated, read-only contiguous range of
those terminals in the macro-expanded list; for an empty region it is the zero-width range at the
node's `Empty` origin anchor. Its delimiter summary records pair indices and recovery boundaries
while every opening and closing delimiter remains one of the terminal descendants or a named field
of the surrounding outline node. Only elements marked `Active` contribute delimiter entries;
inactive delimiters remain in the terminal projection but cannot change a parse boundary.
Every input terminal occurs exactly once in the outline root's structural coverage, either as a
recognized field, under one `UnparsedContent`, or under one maximal `InactiveContent` node.
`InactiveContent.elements` are exactly one maximal contiguous run marked `Inactive` by the
macro-expanded snapshot's activity map. Such a node has no declaration binding and is never a
fine-parse subject.

`declOutlineIndex`, `unparsedContentIndex`, and `inactiveContentIndex` are generated traversal views
over `snapshot.root`.
Their values expose common fields from the concrete production nodes in the declaration-outline
registry; they are not serialized maps and cannot diverge from those nodes. Each binding's `kind`,
the outline's `bindings`, and its `members` are schema-declared projections whose rules name the
exact production
fields from which they are derived. The declaration profile's `fallbackDeclBindings` sentinel
requires both C-style declarator alternatives, the optional inline-type alternative, and their
direct `name` fields, so the fallback
cannot regress into an opaque header that scope wiring is unable to name.

Delimiter ordinals are zero-based indices into `UnparsedContent.terminals`; a recovery boundary is
an insertion boundary in `[0, terminals.count]`. Matched pairs are properly nested, use equal
delimiter kinds, and name distinct ordinals. `entries` is ordered by the first encountered ordinal,
with an opening entry before any nested entry at the same boundary, and `maximumDepth` is derived by
replaying that sequence. The summary is a generated `DerivedField` of `terminals`: it cannot become
a second authority for token ownership or recovery diagnostics.

Each binding's `DirectGenericMarker` is syntactic information only. It says whether the first
active non-trivia token immediately after that binding's declaration name is a direct
generic-clause `<` marker. The marker terminal remains structurally owned by the ordinary header or
C-style declarator suffix; `DirectGenericMarker.leftAngle` is a derived reference to that terminal,
not a second structural occurrence. The outline deliberately does not
find the matching `>`, split parameters, or promise a parameter count. This is enough for early
generic-head classification without having to interpret nested `<`, `>`, or `>>` inside parameter
types, constraints, or defaults. The checked `GenericBinder` is computed later by
`GetGenericBinder` after the header can be fine-parsed and parameter kinds, defaults, and
constraints can be checked.

### Explicit lookup-scope wiring

The declaration outlines are sufficient to create the initial immutable lookup wiring used by fine
parsing. Scope wiring is a query product, not another AST stage.

```text
ResolveImportOutlines(decls: DeclParseResult,
                      currentModule: ModuleId,
                      provider: ModuleResolutionProvider,
                      providerRevision: ModuleResolutionRevision,
                      languageRules: LanguageRuleSetId)
    -> QueryStep<ImportResolutionIndex>

WireLookupScopes(decls: DeclParseResult,
                 imports: ImportResolutionIndex,
                 environment: ScopeWiringEnvironment)
    -> QueryStep<ScopeWiring>

ScopeNamespaceKey = {
    module: ModuleId,
    declarations: CSTSnapshotId<DeclParsed>
}

ScopeNamespaceId = ContentId<ScopeNamespaceKey>

ScopePathStep =
    OutlineScope(owner: DeclOutlineId, role: ScopeKind)
  | DeferredScope(owner: UnparsedContentId,
                  role: ScopeKind,
                  ordinal: UInt32)

ScopeId = {
    namespace: ScopeNamespaceId,
    path: NonEmpty<ScopePathStep>
}

ParserDeclStub = {
    fragment: DeclFragmentId,
    outline: DeclOutlineId,
    binding: DeclOutlineBindingOrdinal,
    name: Option<Name>,
    kind: DeclKind,
    directGeneric: DirectGenericMarker,
    declaringScope: ScopeId,
    bindingPosition: ScopePosition,
    memberScope: Option<ScopeId>,
    origin: Origin
}

ScopeWiring = {
    roots: NodeList<ScopeId>,
    scopes: NodeMap<ScopeId, Scope>,
    declarations: NodeMap<DeclFragmentId, ParserDeclStub>,
    contentEntryPositions: NodeMap<UnparsedContentId, ScopePosition>
}

LocalScopeMemberContribution = {
    scope: ScopeId,
    name: NameKey,
    fragments: NonEmpty<DeclFragmentId>
}

LocalScopeWiringFragment = {
    base: ScopeWiringId,
    owner: UnparsedContentId,
    newScopes: NodeMap<ScopeId, Scope>,
    newDecls: NodeMap<DeclFragmentId, ParserDeclStub>,
    memberContributions: NodeList<LocalScopeMemberContribution>,
    bindingPoints: NodeMap<DeclFragmentId, ScopePosition>,
    advancedEnds: NodeMap<ScopeId, ScopePosition>,
    contentEntryPositions: NodeMap<UnparsedContentId, ScopePosition>
}

LocalScopeWiringFragmentId = ContentId<LocalScopeWiringFragment>

ScopeWiringPublication = {
    input: ScopeWiringId,
    fragment: Option<LocalScopeWiringFragmentId>,
    output: ScopeWiringId
}

ExtendScopeWiring(base: ScopeWiringId,
                  fragment: LocalScopeWiringFragmentId)
    -> Result<ScopeWiringId, ScopeWiringExtensionFailure>

ScopeWiringExtensionFailure =
    ScopeWiringBaseMismatch
  | ExistingScopeConflict(scope: ScopeId)
  | ExistingDeclConflict(fragment: DeclFragmentId)
  | InvalidBindingPoint(fragment: DeclFragmentId)
  | InvalidScopeEnd(scope: ScopeId)
  | InvalidContentEntry(content: UnparsedContentId)

GenericPresence =
    NotGeneric
  | IsGeneric
  | RecoveredGenericPresence(error: ErrorId)

ExportedDeclOutlinePathSegment = {
    name: Option<NameKey>,
    kind: DeclKind,
    siblingOrdinal: UInt32
}

ExportedDeclOutlineId = {
    module: ModuleId,
    path: NonEmpty<ExportedDeclOutlinePathSegment>
}

ImportedDeclOutlineId = ExportedDeclOutlineId

ImportedDeclOutlineScopeId = {
    module: ModuleId,
    owner: Option<ExportedDeclOutlineId>
}

ImportedDeclOutline = {
    id: ImportedDeclOutlineId,
    name: NameKey,
    kind: DeclKind,
    genericPresence: GenericPresence,
    memberScope: Option<ImportedDeclOutlineScopeId>,
    origin: Origin
}

ImportedDeclOutlineScope = {
    id: ImportedDeclOutlineScopeId,
    members: NodeMap<NameKey, NodeList<ImportedDeclOutlineId>>
}

ModuleDeclOutlineInterface = {
    module: ModuleId,
    rootScope: ImportedDeclOutlineScopeId,
    scopes: NodeMap<ImportedDeclOutlineScopeId, ImportedDeclOutlineScope>,
    declarations: NodeMap<ImportedDeclOutlineId, ImportedDeclOutline>
}

ModuleDeclOutlineExportMap =
    NodeMap<ExportedDeclOutlineId, ExportedId>

ModuleResolutionRevision = ContentId<SchemaValue>

ImportModuleSpecifier =
    DottedModuleName(NonEmpty<Utf8String>)
  | StringModuleName(Utf8String)

decodeImportModuleSpecifier(fields: ImportModuleNameFields,
                            lexicalContext: LexicalContextId,
                            languageRules: LanguageRuleSetId)
    -> CheckResult<ImportModuleSpecifier>

ModuleResolutionRequest = {
    from: ModuleId,
    name: ImportModuleSpecifier,
    languageRules: LanguageRuleSetId
}

ResolvedImportedModule = {
    module: ModuleId,
    outlineInterface: ModuleDeclOutlineInterfaceId,
    outlines: ModuleDeclOutlineInterface
}

ModuleResolutionResult =
    ResolvedModule(ResolvedImportedModule)
  | MissingModule(request: ModuleResolutionRequest)
  | AmbiguousModules(candidates: NonEmpty<ResolvedImportedModule>)

ModuleResolutionProvider = read-only interface {
    revision() -> ModuleResolutionRevision,
    resolve(request: ModuleResolutionRequest)
        -> QueryStep<ModuleResolutionResult>
}

resolveImport(provider: ModuleResolutionProvider,
              revision: ModuleResolutionRevision,
              request: ModuleResolutionRequest)
    -> QueryStep<ModuleResolutionResult>

ImportedDeclOutlineIndex =
    CanonicallyOrderedMap<ModuleId, ModuleDeclOutlineInterface>

ResolvedImportOutline = {
    outline: DeclOutlineId,
    edge: ImportEdge,
    outlineInterface: ModuleDeclOutlineInterfaceId
}

FailedImportOutline = {
    outline: DeclOutlineId,
    request: ModuleResolutionRequest,
    errors: NonEmpty<ErrorId>
}

ImportResolutionEntry =
    ResolvedImport(ResolvedImportOutline)
  | FailedImport(FailedImportOutline)

ImportResolutionIndex = {
    imports: NodeMap<DeclOutlineId, ImportResolutionEntry>,
    outlines: ImportedDeclOutlineIndex,
    providerRevision: ModuleResolutionRevision
}

ParserLookupTarget =
    LocalDeclOutline(fragment: DeclFragmentId)
  | ImportedDeclOutline(declaration: ImportedDeclOutlineId)

ParserLookupStep =
    LocalScopeLookup(scope: ScopeId)
  | ImportLookup(edge: ImportEdge, scope: ImportedDeclOutlineScopeId)
  | MemberScopeLookup(owner: ParserLookupTarget)

ParserLookupCandidate = {
    target: ParserLookupTarget,
    path: NonEmpty<ParserLookupStep>
}
```

Each `Scope` has an explicit parent, parent-entry position, source-order policy, and name-to-fragment
membership. Module, namespace, aggregate, and interface members are unordered where the language
allows forward lookup; generic and parameter binders are sequential; function and block scopes are
source ordered. Namespace reopening and imported outline summaries are explicit inputs. Fine parsing
publishes immutable scope-wiring fragments for newly discovered local declarations. There is no
ambient mutable `currentScope` in the representation.

`WireLookupScopes` emits exactly one `ParserDeclStub` for every `DeclOutlineBinding` and none for
`InactiveContent`. The stub's `binding` equals the gap-free source-order ordinal stored by the
outline, its `kind` equals that binding's `DeclKind`, and its fragment identity includes both facts.
Thus all members of a C-style `DeclGroup`
are available to early lookup even though their declaration-specifier terminals have one structural
owner. A binding with no source name may create an anonymous declaration stub only when its
registered `DeclKind` permits one; recovery never fabricates a named stub.

`ExtendScopeWiring` persistently merges a `LocalScopeWiringFragment` into its exact `base`:
unchanged maps are structurally shared, while the result is a complete `ScopeWiring` with its own
content ID. A fragment may add members/binding points to an existing source-ordered scope and add
nested scopes, declaration stubs, and content-entry positions. It cannot alter a pre-existing
parent, policy, binding point, or declaration. `ScopeWiringPublication.fragment=None` requires
`output=input`. Fine parsing threads `output` to the next source-order sibling, so no ambient scope
or prose-only overlay participates in lookup.

An `ImportedDeclOutlineIndex` is the syntax-classification projection of the immutable interfaces
selected by `ResolveImportOutlines`. It exposes only exported name, declaration kind, generic
presence, and member-scope hierarchy. `NotGeneric` means there is no direct generic binder;
`IsGeneric` means that the exported declaration has a direct generic binder. A successfully
published module outline interface cannot contain `RecoveredGenericPresence`. The projection does not copy a `GenericBinder`,
type, constraint, overload result, or conformance into the parser.

`ResolveImportOutlines` is keyed by the exact `ImportDeclOutline` spelling, current module,
language rules, and provider revision. It derives the provider request only through
`decodeImportModuleSpecifier`; equal decoded module names at different source sites therefore have
equal provider requests while their enclosing resolution entries retain different outline origins.
Each successful result pairs that source outline with one
`ImportEdge`, one immutable module-outline-interface identity, and that interface's declaration-outline
projection. The map contains exactly the import outlines in `decls`, including typed failures or
blocked dependencies in the enclosing `QueryStep`; `WireLookupScopes` never reparses an import
operand or performs module loading ambiently.

A failed lookup has a `FailedImport` entry and contributes no `ImportEdge` or imported scope; it is
not represented by a missing map key. An unavailable module/interface query blocks the whole
resolution query and publishes no partial index. `ImportResolutionIndex.outlines` contains exactly
the distinct modules named by its `ResolvedImport` entries and no module introduced only by a
failed entry.

`ModuleResolutionProvider` is a read-only service boundary around the current linkage/module-load
mechanism. Equal `ModuleResolutionRequest` values at an equal `ModuleResolutionRevision` return
equal `ModuleResolutionResult` values. `MissingModule` and `AmbiguousModules` are ordinary typed
lookup outcomes from which `ResolveImportOutlines` constructs its diagnostics and `FailedImport`
entry; neither outcome fabricates an empty module interface. The provider object's address and load
order are neither query inputs nor declaration identity; tests inject resolved, missing, ambiguous,
blocked, and stale-revision providers directly.

`ModuleDeclOutlineInterfaceId` is the `ContentId` of the corresponding
`ModuleDeclOutlineInterface`. This outline interface is independently publishable after
`ParseDecls`; it does not contain checked signatures, types, generic binders, conformances, or
definitions. `ExportedDeclOutlineId` uses only module identity plus a canonical declaration-outline
path; its sibling ordinal distinguishes same-name/kind overload outlines without guessing a
signature. A later full module interface names the exact outline-interface ID from which its
exported declarations were checked and publishes a `ModuleDeclOutlineExportMap` from each successful
outline to its checked `ExportedId`. Mutually importing modules may therefore exchange outline
interfaces without forcing either module's headers to be checked first.

Local and imported parser candidates retain different identities. In particular, wiring an import
does not fabricate a local `DeclFragmentId` for an exported declaration. A `ParserLookupStep`
records the exact lexical, import, and qualified-member route used for early syntax classification;
later semantic lookup constructs its own evidence-bearing `LookupPath` instead of treating this
syntax-only path as a subtype, conformance, or access proof.

`REP-SCP-001`: `WireLookupScopes` is a total function of declaration outlines, imported declaration
outlines, module/file assembly facts, and language scope rules. It may diagnose malformed scope
structure, but it never requests a declaration header, a checked type, or a function body.

`REP-SCP-002`: Generic-head classification obtains `GenericPresence` from the candidate target:
by projecting the local `ParserDeclStub.directGeneric` or reading the imported outline. It is
`Blocked`, rather than guessed, if the required import interface or member outline is unavailable.

`REP-SCP-003`: For every `ResolvedImportOutline`, `edge.from` equals the current module,
`edge.origin` names the exact import outline, `edge.to` equals the indexed imported module, and the
content ID of that module's `ModuleDeclOutlineInterface` equals the result's `outlineInterface`.
Missing, duplicate, mismatched, or stale
entries make scope wiring invalid rather than creating an empty imported scope. Every source import
has exactly one resolution entry; a `FailedImport` has no corresponding edge or outline module.

`REP-SCP-004`: Module resolution for scope wiring may depend only on
`ModuleDeclOutlineInterfaceId`, never on `ModuleInterfaceContentId` or another checked-export
product. Requesting a full module interface while resolving an outline import is an invalid query
edge because it reintroduces a parse/header cycle.

`REP-SCP-005`: Within each exported outline parent, `siblingOrdinal` is the zero-based physical
source-order ordinal among children with the same `NameKey` (or both anonymous) and `DeclKind`.
Those tuples are unique and gap-free. The later `ModuleDeclOutlineExportMap` is functional but need
not be total for recovered or non-exported outlines; it may not map two distinct successful outline
IDs to the same `ExportedId` unless the module's explicit redeclaration rule proves that they are
fragments of one declaration.

`REP-SCP-006`: `resolveImport(provider, revision, request)` first requires
`provider.revision() = revision` and then returns exactly `provider.resolve(request)`. Every
`ResolvedModule` and ambiguous candidate validates its `outlineInterface` against the content ID of
`outlines` and requires `outlines.module = module`. A missing or ambiguous result contains no
selected import edge; selection by provider iteration order is forbidden.

`REP-SCP-007`: `decodeImportModuleSpecifier` reads only the selected terminal logical spellings and
the stated lexical/language rules. A dotted name preserves its source segment order after identifier
decoding; a string form uses the registered module-string literal decoder. It performs no name
lookup, filesystem probing, or module load. A recovered decode produces the one typed failed-import
entry for that outline and never calls the provider with guessed text.

`ReadyForParserLookup` in the existing compiler corresponds to publishing a declaration outline in
this wiring. It is not evidence that the header or body has been type-checked. Logical declaration
identity and redeclaration grouping may require signature facts and therefore remain scheduler
queries; scope membership is keyed initially by `DeclFragmentId`.

### Fine parsing and checking

After scope wiring, parsing and checking form one fine-grained, demand-driven query graph. A query
may parse one content region, request lookup or a checked base type to disambiguate it, and publish
both the immutable parsed CST fragment and the next immutable AST node. There is no bulk full-file
parsed-tree, separately bound-tree, or whole-file typed-tree transition.

Each query derives its grammar cursor by restricting the predecessor snapshot's
`ActiveTokenView` to its subject. The `Parsed` fragment structurally owns only the active token,
token-slice, and missing-terminal fields admitted by `TerminalValue<Parsed>`; it does not copy active
trivia or `DeclParsed`-stage `InactiveContent` into a second node domain. Its exact
`ParsedContent.source` and predecessor snapshot retain those elements in base-list order for
formatting and provenance. Inactive elements cannot form expressions, statements, local
declarations, generic heads, delimiters, or recovery lookahead.

```text
ParsedContent<C: CSTCategoryId> = {
    snapshot: CSTSnapshot<Parsed>,
    root: NonTerminalNodeId<Parsed,
            kind where category(kind) includes C>,
    source: ParsedContentSource
}

ParsedContentSource =
    DeferredContentSource(content: UnparsedContentId)
  | DeclHeaderSource(outline: DeclOutlineId,
                     binding: DeclOutlineBindingOrdinal)

SurfaceExpr = ASTNodeId<Surface, Expr>
TypedExpr = ASTNodeId<Typed, Expr>
SurfaceStmt = ASTNodeId<Surface, Stmt>
TypedStmt = ASTNodeId<Typed, Stmt>

FineParseSubject = {
    content: UnparsedContentId,
    range: TokenListRange,
    entry: ScopePosition,
    scopes: ScopeWiringId
}

DeclHeaderFineParseSubject = {
    fragment: DeclFragmentId,
    outline: DeclOutlineId,
    binding: DeclOutlineBindingOrdinal,
    syntax: DeclHeaderSyntax,
    entry: ScopePosition,
    scopes: ScopeWiringId
}

PostfixHeadSyntaxKey = {
    subject: FineParseSubject,
    headRange: TokenListRange
}

ExpressionPrefixRequest = {
    subject: FineParseSubject,
    expressionRange: TokenListRange,
    context: ExpressionCheckContextId
}

CheckExpressionPrefix(request: ExpressionPrefixRequest,
                      disambiguation: SyntaxDisambiguationProvider)
    -> QueryStep<CheckedExpressionContent>

ParseAndCheckExpression(content: UnparsedContentId,
                        entry: ScopePosition,
                        context: ExpressionCheckContextId,
                        scopes: ScopeWiringId,
                        disambiguation: SyntaxDisambiguationProvider)
    -> QueryStep<CheckedExpressionContent>

CheckedExpressionContent = {
    syntax: ParsedContent<ExprCSTCategory>,
    surface: SurfaceExpr,
    typed: TypedExpr,
    scopes: ScopeWiringPublication
}

CheckedStatementContent = {
    syntax: ParsedContent<StmtCSTCategory>,
    surface: SurfaceStmt,
    typed: TypedStmt,
    scopes: ScopeWiringPublication
}

CheckedDeclHeaderContent = {
    syntax: ParsedContent<DeclCSTCategory>,
    surface: ASTNodeId<Surface, Decl>,
    header: DeclHeader,
    scopes: ScopeWiringPublication
}

ParseAndCheckStatement(...) -> QueryStep<CheckedStatementContent>
ParseAndCheckDeclHeader(subject: DeclHeaderFineParseSubject,
                        disambiguation: SyntaxDisambiguationProvider)
    -> QueryStep<CheckedDeclHeaderContent>
```

For every successful composite query, `surface` is the exact node returned by its CST-to-surface
translation. `CheckedExpressionContent.typed` is exactly the result of
`CheckExpression(surface, context)`; `CheckedStatementContent.typed` is exactly the result of
`CheckStatement(surface, context)`; and `ParseAndCheckDeclHeader.header` is exactly the result of
`BindDeclHeader` for `surface` and its parsed syntax. These are dependency results embedded for
convenience, not second producers or copied authorities. The composite queries exist so syntax may
use the same lookup-backed disambiguation interface while it is being constructed.

Each result's `scopes.input` equals the query's input `ScopeWiringId`. Its `output` is the complete
persistent wiring after any local declarations and nested deferred regions discovered by that
query. A caller processing source-order siblings supplies that output to the next query. Internal
scopes may be present in the output but cannot affect a sibling unless a binding-point contribution
was explicitly made to the sibling's entered scope.

A full parsed file can be assembled as a serialization or tooling view after the required regions
are available. Such an assembly does not impose execution order on the scheduler.

Generic application is the motivating parser/checker dependency:

```text
ClassifyGenericApplicationHead(head: PostfixHeadSyntaxKey,
                               position: ScopePosition,
                               scopes: ScopeWiringId,
                               context: ExpressionCheckContextId)
    -> QueryStep<GenericHeadClassification>

GenericHeadClassification =
    GenericHead(genericCandidates: NonEmpty<ParserLookupCandidate>,
                otherCandidates: NodeList<ParserLookupCandidate>)
  | NonGenericHead(candidates: NodeList<ParserLookupCandidate>)
  | UnresolvedHead(failure: ParserLookupFailure)

ParserLookupFailure = {
    head: PostfixHeadSyntaxKey,
    position: ScopePosition,
    errors: NonEmpty<ErrorId>
}

GenericHeadClassificationRequest = {
    head: PostfixHeadSyntaxKey,
    position: ScopePosition,
    scopes: ScopeWiringId,
    context: ExpressionCheckContextId
}

ScopedSyntaxLookupRequest = {
    subject: FineParseSubject,
    identifier: TokenRef,
    position: ScopePosition,
    syntaxInfos: SyntaxParseInfoSetId
}

ScopedSyntaxLookupResult =
    NoScopedSyntax
  | FoundScopedSyntax(NonEmpty<SerializedSyntaxParseInfo>)
  | RecoveredScopedSyntax(NonEmpty<SerializedSyntaxParseInfo>, NonEmpty<ErrorId>)

TerminalExpectation =
    TokenTypeExpectation(TokenType)
  | LiteralExpectation(Utf8String)
  | GrammarWordExpectation(QualifiedName)

ParserRecoveryRequest = {
    subject: FineParseSubject,
    production: ProductionId,
    expected: CanonicalFiniteSet<TerminalExpectation>,
    cursor: TokenListIndex,
    options: ParserOptions
}

ParserRecoveryDecision =
    InsertMissing(expected: TerminalExpectation, rule: RuleId)
  | SkipThrough(end: TokenListIndex, rule: RuleId)
  | RejectRecovery(rule: RuleId)

SyntaxDisambiguationRevision = ContentId<SchemaValue>

SyntaxDisambiguationProvider = read-only interface {
    revision() -> SyntaxDisambiguationRevision,
    classifyGenericHead(GenericHeadClassificationRequest)
        -> QueryStep<GenericHeadClassification>,
    checkExpressionPrefix(ExpressionPrefixRequest)
        -> QueryStep<CheckedExpressionContent>,
    lookupScopedSyntax(ScopedSyntaxLookupRequest)
        -> QueryStep<ScopedSyntaxLookupResult>,
    chooseRecovery(ParserRecoveryRequest)
        -> ParserRecoveryDecision
}
```

`REP-PAR-001`: If lookup of a postfix head has at least one visible generic declaration outline,
the following balanced `<...>` is parsed as `GenericApplication`. Non-generic candidates remain for
later overload filtering but do not force `<` to be relational syntax.

`REP-PAR-002`: If lookup is complete and has no generic candidate, `<` remains available to the
relational-expression grammar. If lookup or a required checked base is blocked, the parse/check
query is `Blocked`; it does not guess and memoize a speculative tree.

`REP-PAR-003`: A `>>` token is exposed as two `TokenSlice` closing terminals only after generic
syntax has been selected. Otherwise it remains one shift token. Namespace-qualified heads can be
classified from outline scope wiring; a value-member head may request base-expression checking and
member lookup through the scheduler. This interleaving is the intended architecture.

`SyntaxDisambiguationProvider` is a narrow injectable interface. Its revision and the complete
request value participate in the enclosing parse query key. Unit tests can supply lookup-only,
blocked, ambiguous, recovery, and semantic-member mocks without constructing a compiler session.
The production implementation forwards dependency-bearing requests to the centralized scheduler;
`chooseRecovery` is a pure policy lookup and cannot read checker state.

Its exact operations are `ClassifyGenericApplicationHead`, `CheckExpressionPrefix`, scoped
`SyntaxParseInfoSet` lookup, and recovery-policy lookup. A value-member head uses
`ExpressionPrefixRequest` for the base's exact token range; that range must be a strict subrange of
the enclosing expression query. The prefix query publishes its own parsed CST fragment, surface
node, typed node, and scope publication before the enclosing query consumes it. Namespace/name
heads require only outline lookup and do not create an expression prefix.

Fine-parser cursor and builder state are ephemeral. If a provider operation returns `Blocked`, the
enclosing query publishes no partial CST/AST snapshot; after the dependency completes it may restart
from its immutable `FineParseSubject`. Determinism makes restart equivalent to resuming a private
continuation, so parser stacks/cursors never become serialized semantic identity.

`REP-PAR-004`: Every mid-parse semantic dependency is keyed by a `FineParseSubject` or a strict
subrange key derived from it, the exact check context, and the exact input scope wiring. Provider
object identity and mutable cursor position are forbidden query-key inputs.

`REP-PAR-005`: `CheckExpressionPrefix` may recursively request only strict token subranges or
non-parser semantic facts. Equal-range parse/check recursion is a scheduler cycle error; it cannot
be hidden by speculative parsing.

`REP-PAR-006`: A successful `ScopeWiringPublication` is reproducible by applying its optional
fragment to `input`; the result must equal `output`. Later sibling visibility is therefore a
function of source order and the publication chain, never task completion order.

`REP-PAR-007`: A `FineParseSubject` is valid only when `range = resolve(content).range` and
`entry = resolve(scopes).contentEntryPositions[content]`. The repeated values authenticate the exact
subrange/position used by a dependency key; they are derived from, and may never override, the
content and wiring authorities.

`REP-PAR-008`: The registered `declOutlineIndex` derived view is total over
`DeclOutlineCSTCategory`. An exact-introducer, import, empty, or recovered production projects one
ordinal-zero binding from its named fields and selected recovery alternative. A C-style fallback
first projects an inline-type binding when `DeclGroupOutline.inlineTypeSpecifier` is present, then
visits the selected variable-declarator list or sole function declarator in source order. Each
binding carries the `DeclKind` selected by its own introducer/declarator role. A declarator
binding's `name` is the declarator's direct `name` field, and its
`CStyleDeclHeader` names the one shared specifier content plus that declarator's prefix/suffix
content. The optional inline-type binding uses its direct optional name, ordinary header, and
aggregate body. Each ordinal is the binding's visit index. `directGeneric` is derived only from the
first active
token of the selected header/suffix. Variable-group bindings use `NoBody`; the sole traditional
function binding uses the selected `outline-deferred-body`. Every group binding projects the same
enclosing modifier prefix without copying its terminals. Any missing field, non-gap-free ordinal,
extra declarator,
inactive declarator, or disagreement with `ScanFallbackDecl` invalidates the snapshot rather
than producing a shortened scope index.

`REP-PAR-009`: A `DeclHeaderFineParseSubject` resolves its `fragment` to the exact
`ParserDeclStub(outline, binding)` in `scopes`; `syntax` equals that binding's `DeclHeaderSyntax`,
and `entry` is the stub's declaration binding position. An ordinary header parses its one content
range. A C-style header parses the shared declaration specifiers and the selected declarator
prefix/name/suffix as one logical header while retaining their distinct structural owners. No
sibling declarator, separator, or sibling initializer can enter that logical subject through an
enclosing byte range. Inactive descendants remain in its structural projections but are absent from
the active grammar cursor.

## Node-local immutable AST forms

Different AST forms describe the readiness of one node, not the readiness of a whole module. One
semantic store may therefore contain surface syntax for an unrequested body, a typed signature for
one declaration, and an elaborated expression for another.

```text
NodeForm = Surface | Typed | Elaborated | IRReady

LocalNodeIndex = UInt64
FormTag = NodeForm
SemanticId = ContentId<SchemaValue>

ASTNodeId<F: NodeForm, N: ASTNodeType<F>> = {
    snapshot: SemanticSnapshotId,
    local: LocalNodeIndex,
    form: F,
    kind: N
}

AnyASTNodeId<F> = exists N . ASTNodeId<F, N>
AnyASTNodeId = exists F . AnyASTNodeId<F>
AnyNodeId = CST(any: AnyCSTNodeId) | AST(any: AnyASTNodeId)

ASTNodeOrigin =
    FromCST(node: AnyCSTNodeId)
  | FromAST(nodes: NonEmpty<AnyASTNodeId>, rule: RuleId)
  | Synthesized(rule: RuleId, inputs: NodeList<AnyASTNodeId>, anchor: Origin)

ASTNode<F, N> = {
    id: ASTNodeId<F, N>,
    kind: N,
    origin: ASTNodeOrigin,
    fields: NodeFields<F, N>
}

AnyASTNode = exists F, N . ASTNode<F, N>

CanonicalSemanticSnapshotForm =
    ByteString produced by the canonical traversal below
SemanticSnapshotId = ContentId<CanonicalSemanticSnapshotForm>

SemanticSnapshot = {
    id: SemanticSnapshotId,
    nodes: CanonicallyOrderedMap<AnyASTNodeId, AnyASTNode>,
    values: CanonicallyOrderedMap<SemanticId, SchemaValue>,
    schema: SchemaVersion,
    predecessors: CanonicallyOrderedSet<SemanticSnapshotId>
}
```

The store is heterogeneous. `ASTNodeId<Typed, Expr>` proves only that this node is typed; it says
nothing about siblings, parents, or other declarations. A query that advances a construct returns a
new node referring to its exact input nodes. It never mutates those inputs or relies on a global
phase counter.

`CanonicalSemanticSnapshotForm` omits `SemanticSnapshot.id`, replaces every node/value reference
to the snapshot being encoded with its canonical local index, and traverses node fields, semantic
values, and provenance in schema order. It retains external predecessor IDs exactly. The published
snapshot ID must equal the `ContentId` of those bytes. This closes the apparent self-reference from
`ASTNodeId.snapshot` without using allocation address or construction order.

Every typed expression has one canonical classifier and explicit pointer/reference provenance:

```text
TypedValueProvenance =
    NoAdditionalValueProvenance
  | PointerLikeProvenance(proof: PointerLikeProof)

TypedExprInfo = {
    classifier: Classifier,
    valueProvenance: TypedValueProvenance,
    effects: EffectSet,
    directCapabilityUses: NodeList<CapabilityUse>
}
```

`TypedExprInfo` is the generated semantic field product of a `TypedExpr` node, not a separately
stored value. `typedExprInfo(node: TypedExpr)` reads those fields from the node identified by
`node`; the node's `ASTNodeOrigin` remains the single origin authority.

`REP-TYP-001`: `PointerLikeProvenance(p)` is permitted exactly for
`ValueClassifier(p.resultType, RValue)`. Every typed reference/pointer value that may be
dereferenced has this provenance; a type alone cannot authorize dereference. Ordinary values,
storage, type-level expressions, overload sets, and errors use `NoAdditionalValueProvenance` unless
their closed recovery alternative explicitly carries a typed error handle.

`REP-TYP-002`: Identity-preserving binding, copy, reference-view formation, argument passing, and
return preserve the complete pointer-like shape. A registered pointer-like conversion supplies a
new checked proof. Control-flow merge requires equal referent, address-space, access, mutability,
lifetime, and physical-source-provenance facts and joins only alias provenance through `joinAlias`;
otherwise the merge has a structured incompatibility or uses a named registered representation
rule. No operation derives provenance from the destination node ID or from equal `TypeId` values.

Surface nodes retain source spelling choices that matter to diagnostics and tools but omit trivia
already retained by CST terminals. Typed nodes contain explicit classifiers, selected declaration
uses, generic solutions, conversion plans, storage categories, and typed error nodes. Name lookup
is performed inside the checking query: a typed name expression is constructed from the syntax,
scope position, lookup result, and expected context. There is no pre-bound name tree.

Elaborated nodes make implicit semantic work explicit: default arguments, selected witness calls,
conversion operations, synthesized accessors or conforming methods, lambda environment objects,
and storage-access plans. IR-ready nodes contain only constructs with direct lowering rules;
short-circuiting, properties, `defer`, differentiation requests, and target switches have already
become explicit control/data forms.

Abstract storage is eliminated at the IR-ready boundary. A property or declared subscript becomes
an explicit getter, setter, `ref` accessor, or `constref` accessor call with captured receiver/index
evaluation. Every IR-ready physical storage endpoint carries the proof required by `__ref` or
`__constref`; neither mode may allocate a temporary for abstract storage.

`REP-NOD-001`: Every successful query result is immutable and names all semantic inputs needed to
validate it. Error recovery returns a form-appropriate error node with the strongest known
classifier rather than a partially initialized successful node.

`REP-NOD-002`: Semantic caches are keyed by query identity and live beside, not inside, immutable
nodes. Cache and scheduler state are not serialized.

`REP-NOD-003`: Surface, typed, elaborated, and IR-ready nodes are serializable and copyable even
when only a subset of the source program has been requested. Optional assembled-tree indices are
derived views over the independently published nodes.

## Uniform node schema and generic editing

All node types are generated from a versioned schema. Each field declares a name, closed value
kind (including presence and collection shape), edge category, representation-domain availability,
and serialization policy:

```text
SchemaVersion = (major: UInt16, minor: UInt16)
RepresentationDomain = Concrete(CSTStage) | Abstract(NodeForm) | SemanticDomain
DomainSet = BitSet<RepresentationDomain>

FieldName = {
    text: Utf8Identifier,
    wireTag: UInt32
}

NodeKind = {
    family: TerminalNode | NonTerminalNode | AST | Semantic,
    wireTag: UInt32,
    stableName: QualifiedName
}

ASTNodeType<F> = {
    k: NodeKind |
        k.family = AST and
        k in currentNodeSchemaRegistry.domainKinds[Abstract(F)]
}
NonTerminalKind<S> = {
    k: NodeKind |
        k.family = NonTerminalNode and
        k in currentNodeSchemaRegistry.domainKinds[Concrete(S)]
}
NodeFields<F, N> = CanonicallyOrderedMap<FieldName, FieldValue>

FieldSlotKind = {
    name: FieldName,
    valueKind: FieldValueKind
}

FieldVariantAlternativeKind = {
    tag: CSTVariantTag,
    valueKind: FieldValueKind
}

FieldValueKind = ScalarKind(T)
               | NodeKindValue(K)
               | ProductKind(fields: NodeList<FieldSlotKind>)
               | VariantKind(group: CSTGroupTag,
                             alternatives: NonEmpty<FieldVariantAlternativeKind>)
               | ListKind(element: FieldValueKind)
               | NonEmptyListKind(element: FieldValueKind)
               | MapKind(key: FieldValueKind, value: FieldValueKind)
               | OptionalKind(value: FieldValueKind)

CSTShapeProjectionDescriptor = {
    production: ProductionId,
    field: FieldName,
    rule: RuleId
}

FieldWirePolicy = SerializedField
                | DerivedField(rule: RuleId, inputs: NonEmpty<FieldName>)
                | CSTShapeProjectedField(CSTShapeProjectionDescriptor)

FieldAccess = Editable | ReadOnly

FieldDescriptor = {
    name: FieldName,
    valueKind: FieldValueKind,
    edge: Structural | Alternative | Semantic | Provenance,
    domains: DomainSet,
    wire: FieldWirePolicy,
    access: FieldAccess
}

NodeDescriptor = {
    kind: NodeKind,
    baseKind: Option<NodeKind>,
    fields: NodeList<FieldDescriptor>,
    invariants: NodeList<RuleId>
}

AnySchemaNodeRef = SyntaxNodeRef(AnyNodeId)
                 | CSTNodeRef(AnyCSTNodeId)
                 | SchemaValueRef(ContentId<SchemaValue>)

FieldMapEntry = {
    key: FieldValue,
    value: FieldValue
}

FieldBinding = {
    name: FieldName,
    value: FieldValue
}

RegisteredScalarValue = {
    type: QualifiedName,
    canonicalEncoding: ByteString
}

FieldValue = ScalarValue(RegisteredScalarValue)
           | SchemaNodeValue(AnySchemaNodeRef)
           | ProductValue(NodeList<FieldBinding>)
           | VariantValue(tag: CSTVariantTag, payload: FieldValue)
           | ListValue(NodeList<FieldValue>)
           | NonEmptyListValue(NonEmpty<FieldValue>)
           | MapValue(NodeList<FieldMapEntry>)
           | OptionalValue(Absent | Present(FieldValue))

CSTShapeValue<p: CSTProductionDescriptor> =
    FieldValue where value matches compileShape(p.shape)

OriginUpdateRule = DeriveFromEditedNode(rule: RuleId)
                 | ReplaceASTOrigin(origin: ASTNodeOrigin)

ProductionId = {
    grammarVersion: SchemaVersion,
    qualifiedName: QualifiedName
}

DeclGrammarProductionId = ProductionId where
    qualifiedName begins with QualifiedName("slang", "declOutline")

CSTCategoryDescriptor = {
    category: CSTCategoryId,
    kind: NodeKind where kind.family = NonTerminalNode,
    members: CanonicallyOrderedSet<ProductionId>
}

CSTDerivedViewDescriptor = {
    stableName: QualifiedName,
    sourceCategory: CSTCategoryId,
    valueKind: QualifiedName,
    rule: RuleId
}

NodeSchemaRegistryFragment = {
    version: SchemaVersion,
    domain: RepresentationDomain,
    cstCategories: CanonicallyOrderedMap<CSTCategoryId, CSTCategoryDescriptor>,
    grammarProductions: CanonicallyOrderedMap<ProductionId, NodeKind>,
    cstProductionDescriptors:
        CanonicallyOrderedMap<ProductionId, CSTProductionDescriptor>,
    derivedViews:
        CanonicallyOrderedMap<QualifiedName, CSTDerivedViewDescriptor>
}

NodeSchemaRegistryFragmentId = ContentId<NodeSchemaRegistryFragment>

NonTerminalKind<Lexed> = TokenizedSource

NonTerminalKind<PreprocessorStructured> =
    PreprocessorUnit | PreprocessorFragment | PreprocessorDirective | TextRegion |
    DefineDirective | MacroDefinition |
    MacroDefinitionParameterClause | MacroDefinitionParameterTail | MacroDefinitionParam |
    MacroInvocation | MacroInvocationArgumentClause | MacroInvocationArgumentTail |
    MacroInvocationArg | MacroRawSpan | MacroParamReference |
    MacroStringize | TokenPaste | IncludeDirective | ConditionalGroup | ConditionalBranch |
    DiagnosticDirective | LineDirective | PragmaDirective | LanguageDirective |
    UndefDirective | UnknownDirective | PreprocessorRecovery |
    RegisteredPreprocessorKind(NodeKind)

NonTerminalKind<MacroExpanded> =
    PreprocessorUnit | TextExpansion | ConditionalExpansion |
    MacroExpansion | MacroRawSpanExpansion | MacroParamExpansion |
    MacroStringizeExpansion | TokenPasteExpansion | BuiltinMacroExpansion |
    IncludeExpansion | SuppressedExpansion | FailedExpansion |
    SuppressedIncludeExpansion | FailedIncludeExpansion | ExpandedRecovery |
    RegisteredExpansionKind(NodeKind)

NonTerminalKind<DeclParsed> =
    DeclOutlineRoot | Production(DeclGrammarProductionId) | UnparsedContentNode |
    DeclOutlineRecovery | RegisteredDeclOutlineKind(NodeKind)

NonTerminalKind<Parsed> =
    GrammarRoot | Production(ProductionId) | Ambiguity | SkippedTokens |
    UnexpectedConstruct | RegisteredGrammarKind(NodeKind)

NodeSchemaRegistry = {
    version: SchemaVersion,
    nodes: CanonicallyOrderedMap<NodeKind, NodeDescriptor>,
    terminalKinds:
        CanonicallyOrderedMap<(CSTStage, TerminalClass), NodeKind>,
    cstConstructors:
        CanonicallyOrderedMap<(CSTStage, NodeKind), NonEmpty<RuleId>>,
    cstCategories:
        CanonicallyOrderedMap<CSTCategoryId, CSTCategoryDescriptor>,
    grammarProductions: CanonicallyOrderedMap<ProductionId, NodeKind>,
    cstProductionDescriptors:
        CanonicallyOrderedMap<ProductionId, CSTProductionDescriptor>,
    domainKinds: NodeMap<RepresentationDomain, CanonicallyOrderedSet<NodeKind>>,
    migrations: NodeList<SchemaMigrationDescriptor>
}

NodeSchemaRegistryId = ContentId<NodeSchemaRegistry>

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

For a production descriptor `p`, let `directSlots(p)` be the ordered fields of
`compileShape(p.shape)`. `directProductionDescriptor(p, slot)` copies the matching direct leaf's
metadata or the matching `CSTShapeGroup.field` metadata and replaces its `valueKind` with the slot's
compiled kind. The complete registry is required to satisfy:

```text
productionNodeDescriptor(p) = NodeDescriptor {
    kind: p.kind,
    baseKind: None,
    fields: [descriptor(CSTOriginField)] ++
            map(directProductionDescriptor(p), directSlots(p)),
    invariants: p.invariants ++ map(rule, p.constraints)
}

nodes[p.kind] = productionNodeDescriptor(p)

fieldDescriptors(Production(p.production)) =
    nodes[p.kind].fields ++
    sourceOrderedUnique([
        projectedDescriptor(f) |
        f in p.fields and f.name not in directSlots(p).names
    ])

projectedDescriptor(f).valueKind = projectedCSTFieldKind(p.kind, f.name)
projectedDescriptor(f).wire =
    CSTShapeProjectedField(CSTShapeProjectionDescriptor {
        production: p.production,
        field: f.name,
        rule: ruleForProjection(f)
    })
```

The direct product is the sole serialized field authority. A nested leaf descriptor is a generated
read/edit projection into that product, never a second stored field. The `wire` member on a
`CSTProductionFieldDescriptor` describes how the leaf is encoded at its occurrence inside the
closed shape; `projectedDescriptor` describes how the node-level generic query reconstructs it.
Schema assembly rejects any disagreement between the node descriptor, compiled direct slots,
production leaf inventory, or constraints.

Node-kind checking uses one explicit relation:

```text
acceptsNodeKind(expected, actual) iff
    expected = actual
 or expected occurs in the acyclic baseKind chain of nodes[actual]
 or exists c: CSTCategoryDescriptor, p: ProductionId .
        c.kind = expected and
        grammarProductions[p] = actual and
        p in c.members
```

Every category kind is unique and abstract, every member resolves to exactly one concrete
production kind, `grammarProductions` is injective, and category membership cannot make the
category itself constructible. A production may belong to several category sets. Concrete
terminal descriptors use the stage's abstract terminal-family kind as `baseKind`; production
categories use the final clause because one production may implement several categories.
`NodeKindValue(expected)` accepts a `SchemaNodeValue` exactly when the referenced node's actual kind
satisfies `acceptsNodeKind(expected, actual)`.

Abstract category and terminal-family kinds have entries in `nodes` so their family, wire identity,
and base-kind role are validated, but they occur in no `domainKinds` set and have no constructor.
Only concrete production and terminal kinds occur in `domainKinds[Concrete(stage)]`. This keeps an
accepted-kind constraint distinct from a constructible `NonTerminalKind<S>` or
`TerminalNodeKind<S>`.

Every named production in `grammar.ebnf` has exactly one `ProductionId`, `grammarProductions`
entry, and `cstProductionDescriptors` entry. A production descriptor names every terminal and
non-terminal role, including punctuation, and its closed shape states how those roles compose. A
terminal is a leaf and the role is a named field on its containing non-terminal; neither fact
substitutes for the other. A `CSTCategoryDescriptor` is an abstract accepted-kind constraint whose
members are productions; it is not itself a constructible syntax occurrence. Recovery and
ambiguity use the dedicated closed kinds above. Every `ASTNodeType<F>` and schema-value
constructor likewise has exactly one descriptor. Stable names are diagnostic labels;
`(family, wireTag)` is the wire discriminator, and wire tags are never reused after publication.

Every `(CSTStage, NonTerminalKind)` pair has one `cstConstructors` entry naming all rules permitted
to produce it. A rule that creates a node absent from that entry, or a registered kind with no
constructor, fails schema generation.

`terminalKinds[(stage, class)]` is total exactly for the terminal classes admitted by
`TerminalValue<stage>`, and its values are unique within a stage. `terminalKind` is this lookup;
`terminalClass` is its generated inverse after validating that the referenced
`NodeDescriptor.kind.family` is `TerminalNode` and its kind occurs in
`domainKinds[Concrete(stage)]`. Thus terminal record validation depends only on serialized registry
data, not a hidden implementation switch.

`FieldValue` is the one reflective carrier across all registered representation families.
`ProductValue` bindings are stored once in descriptor order and have exactly the product kind's
field-name domain. `VariantValue` stores one valid tag and only that alternative's payload.
`ListValue` and `NonEmptyListValue` store complete element values in order; neither permits a
second per-leaf list authority. A `MapValue` key must be a scalar or schema-node reference with
canonical encoding; entries are sorted by that encoding and duplicate keys are rejected. Its
descriptor's `MapKind(key,value)` recursively validates the key/value kinds. Thus a descriptor
cannot advertise a CST/semantic node edge or a node-valued map that the generic API cannot return.

Every `ScalarKind(T)` names a registry codec that bijectively encodes values of `T` as
`RegisteredScalarValue(type(T), canonicalEncoding)`. `Origin`, `CanonicalArgument`, ranges, enums,
and primitive values all use this route; pointer/object bytes are never a scalar encoding. Typed
access decodes with the same codec, so it cannot disagree with the generic value.

`REP-SCH-006`: For an AST, semantic value, or manually registered fixed-field CST kind,
`NodeFields` has exactly the descriptor's field-name domain in the node's representation domain. For a parsed
`Production(p)` non-terminal, `NonTerminalFields<Parsed, Production(p)>` is isomorphic to
`CSTShapeValue<p>` and matches `compileShape(p.shape)`: a product has exactly its direct bindings; a
variant has exactly one valid tag and its selected payload; an optional explicitly stores
`Absent|Present`; and a list stores zero or more complete element values while a non-empty list
stores one or more. A missing product binding is never used as optionality, and an unselected
variant field is not represented as an absent optional. Validation recursively matches every value
to its one declared kind and rejects a parallel leaf projection as a second authority. This same
law controls migration defaults and wire deserialization, so an inactive variant field, absent
optional, empty list/map, and malformed missing required field are distinct states.

`REP-SCH-007`: A `SerializedField` is present in the wire record. A `DerivedField` names a total,
versioned pure rule and its complete non-empty input field set; derived-field dependencies within a
descriptor are acyclic, and deserialization evaluates them in canonical topological order. A
`CSTShapeProjectedField` is a generated projection from the one compiled production shape; its
production/field pair must resolve uniquely, and it cannot add bytes or an independently editable
authority. Direct `CSTNodeOrigin` and `ASTNodeOrigin` fields are ordinary serialized provenance
fields. A field with no serialized bytes and no declared derivation/projection policy is forbidden.
Thus every exact `NodeFields` entry is reconstructed before a node is published without consulting
an operation log or output-binding side table.

`REP-SCH-008`: CST shape serialization and generic traversal are the same structural recursion.
A product writes and visits bindings in descriptor order. A variant writes its tag followed by its
selected payload. An optional writes presence followed, when present, by its payload. A list writes
its count followed by each complete element value; a non-empty list uses the same encoding after
validating a positive count. Consequently a repeated product such as `(comma, argument)` is visited
and encoded as `comma[0], argument[0], comma[1], argument[1], ...`. Deserialization constructs this
single shape value before any field projection is exposed.

`REP-SCH-009`: Registry assembly satisfies the `productionNodeDescriptor`,
`fieldDescriptors`, `projectedCSTFieldKind`, and `acceptsNodeKind` equations above for every parsed
production, category, terminal kind, and base-kind edge. Neither deserialization nor generic access
may substitute a separately handwritten production switch for these registry relations.

The generated generic read API and immutable AST edit API provide:

```text
kind(node) -> NodeKind
schemaOrigin(node) -> CSTOrigin(CSTNodeOrigin) | ASTOrigin(ASTNodeOrigin) | NoSchemaOrigin
origin(node: SyntaxNodeRef) -> CSTNodeOrigin | ASTNodeOrigin
fieldCount(node, edgeFilter) -> UInt32
fieldDescriptor(node, i) -> FieldDescriptor
field(node, i) -> FieldValue
operandCount(node) -> UInt32
operand(node, i) -> AnySchemaNodeRef

ASTEditFailure =
    UnknownField(kind: NodeKind, field: FieldName)
  | FieldValueMismatch(field: FieldName, expected: FieldValueKind, actual: FieldValue)
  | CrossFormReference(field: FieldName, expected: NodeForm, actual: NodeForm)
  | DanglingReference(reference: AnySchemaNodeRef)
  | InvariantViolation(rule: RuleId)
  | InvalidEditReplacement(expectedKind: NodeKind, actualKind: NodeKind)

ASTEditResult<F, K> = {
    snapshot: SemanticSnapshot,
    node: ASTNodeId<F, K>
}

FormPreservingEditor<F> =
    forall K . ASTNodeId<F, K> -> Result<ASTNodeId<F, K>, ASTEditFailure>

withField<F, K>(snapshot: SemanticSnapshot, node: ASTNodeId<F, K>,
                fieldName: FieldName, value: FieldValue,
                originRule: OriginUpdateRule)
    -> Result<ASTEditResult<F, K>, ASTEditFailure>

withOrigin<F, K>(snapshot: SemanticSnapshot, node: ASTNodeId<F, K>,
                 origin: ASTNodeOrigin)
    -> Result<ASTEditResult<F, K>, ASTEditFailure>

mapNode<F, K>(snapshot: SemanticSnapshot, node: ASTNodeId<F, K>,
              editor: FormPreservingEditor<F>)
    -> Result<ASTEditResult<F, K>, ASTEditFailure>
```

Here `K` is the statically accepted node-kind family of the input position. `withField` and
`withOrigin` retain the exact dynamic kind; `mapNode` may choose another dynamic kind only when it
belongs to the same `K`. All three retain form `F`, validate the complete result, and return a new
semantic snapshot plus a reference into it. Advancing a node to another form is a named scheduler
query such as `CheckExpression`, `ElaborateNode`, or `LowerNodeToIRReady`, not a generic edit.

`withField` is functional: it validates the descriptor and returns a new snapshot, sharing
unchanged subtree storage where possible while leaving the input snapshot byte-identical. Typed
accessors are generated over the same storage and cannot disagree with the generic view.

`DeriveFromEditedNode(rule)` writes `FromAST([node.id], rule)` while changing the requested field.
`ReplaceASTOrigin(origin)` writes the supplied complete origin and is the only generic
recovery/synthesis/import route. Preserving the old origin while changing semantic content is not
permitted. These policies make a transform's provenance decision explicit without maintaining a
second header value.

`REP-SCH-001`: Every semantically relevant field is visible through the schema. Hidden subclass
fields that generic serialization or editing cannot observe are forbidden.

`REP-SCH-002`: Structural operands have stable names. Operand index is an optimization and never
the specification of a role.

`REP-SCH-003`: A generic rewriter must preserve node invariants or return a validation error; it
cannot create a partially initialized node.

`REP-SCH-005`: For every AST node, descriptor lookup of `ASTOriginField` succeeds exactly once and
`origin(node)` returns that field. `withOrigin(snapshot, node, origin)` is the origin-specialized
form of `withField` using `ReplaceASTOrigin(origin)`. Provenance-filtered traversal observes the
field; structural-only traversal does not. Serialization, copying, and generic editing therefore
cannot omit or disagree with typed provenance access.

`REP-SCH-004`: The checked-in machine-readable registry is an implementation-blocking deliverable,
not inferred from C++ subclasses. Grammar coverage is a bijection between named EBNF productions
and `grammarProductions`; domain coverage is a bijection between generated node constructors and
`domainKinds`. The registry generator rejects duplicate tags/names, unknown field types, illegal
domain edges, missing production mappings, and descriptors without validators for their listed
invariants.

The parsed-production portion is generated exhaustively from `grammar.ebnf` and
`cst-production-profile.json`; the paired-schema validator proves that every grammar leaf has a
named typed field and grouped cardinality. Preprocessor nodes, AST forms, and
semantic values still require exhaustive registry instances before implementation begins. That
remaining scope is tracked as a blocking specification item in chapter 13, not silently treated as
an implementation detail.

## Types, values, and semantic graphs

Types, constant values, substitutions, constraints, and witnesses use the same immutable schema
machinery but are semantic graphs rather than source trees. Acyclic structural values are interned
by content inside a `SemanticSnapshot`. Recursive nominal and conformance values use an immutable
identity/definition split: an identity may be referenced before its separately published definition,
and the frozen snapshot validates the resulting strongly connected graph.

Subtype witnesses—including generic witness-table values, specializations, bound parameters,
keyed lookups, and existential extractions—are registered `SchemaValue` alternatives, not opaque
side-table handles. Generic operand enumeration, `withField`, substitution, copying, and
serialization therefore work through the same node schema used for types and constants; chapter 15
defines their classifier and operational validation.

Nominal identity is represented explicitly by `DeclId`; interning does not make two distinct
nominal declarations equal. Recursive nominal types refer to a declaration identity, not a cyclic
physical type object. The identity/definition split keeps serialization finite and non-recursively
nested; semantic graph sections may still contain forward references and SCCs.

## Stable identity

Construction uses private provisional handles. Freezing validates the graph, canonically sorts
content/identity records, assigns frozen IDs, and rewrites every handle before publication. Only
frozen IDs may occur in serialized nodes or persistent query keys.

Snapshot-local frozen semantic-value handles are namespaced by snapshot; AST node IDs have the
equivalent product schema defined in the node-form section, while scope IDs use their independent
declaration-outline namespace because they exist before any semantic snapshot:

```text
CanonicalValueIndex = UInt64
TypeHandle  = (SemanticSnapshotId, CanonicalValueIndex)

ExportedId = {
    module: ModuleStableId,
    path: CanonicalDeclPath,
    kind: DeclKind,
    signature: CanonicalSignatureEncoding
}
```

`DeclId`, `CanonicalDeclPath`, `DeclDisambiguator`, and
`CanonicalSignatureEncoding` are defined once in chapter 5. They are revision-independent nominal
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
`TypeId` is defined in chapter 5. It is never serialized or compared as semantic type identity;
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
4. node records grouped by representation domain;
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
definition completeness, representation domain, and declared invariants before publishing the
snapshot.

## Example: one expression through on-demand queries

For `f(1)`:

```text
DeclParsed CST:
  UnparsedContent(role=ExprContent, terminals=`f ( 1 )`)

ParseAndCheckExpression query:
  ParsedContent(
      CallSyntax(name=NameToken("f"), leftParenthesis=OpenParen,
                 arguments=[IntToken("1")], rightParenthesis=CloseParen))
  SurfaceExpr:
      Call(Name("f"), [IntLiteral(raw="1")])
  TypedExpr:
      Call(
          considered=[BoundDeclUse(f_int), BoundDeclUse(f_float)],
          result=Selected(winner.use=BoundDeclUse(DeclRef(f_int))),
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

Each query publishes new immutable nodes with origins naming the exact syntax or prior-form inputs.
No whole file first becomes bound or typed. Overload candidates and the chosen conversion remain
inspectable even though the IR-ready node no longer needs the overload set.

## Compatibility notes

The current compiler has useful pieces of this design: `Val` operands provide a uniform DAG-like
interface, `FIDDLE` drives node metadata and serialization, AST serialization exists, and many
types are hash-consed by `ASTBuilder`. The syntax tree, however, is mutated through declaration
check states and expression fields; parser output is not a lossless CST; comments are not attached
through a formatter-grade trivia model; and synthesis inserts mutable declarations into existing
containers. The replacement design preserves the useful uniformity while removing stage mutation
and implicit state.
