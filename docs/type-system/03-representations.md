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

## Staged concrete syntax

Lexing, preprocessing, macro expansion, and grammar parsing are immutable translations of concrete
syntax. They use the same two node classes throughout:

```text
CSTStage = Lexed | PreprocessorStructured | MacroExpanded | Parsed

CSTNodeId<S> = Terminal(TerminalNodeId<S>)
             | NonTerminal(NonTerminalNodeId<S>)

AnyCSTSnapshotId = exists S: CSTStage . CSTSnapshotId<S>
AnyTerminalNodeId = exists S: CSTStage . TerminalNodeId<S>
AnyNonTerminalNodeId = exists S: CSTStage . NonTerminalNodeId<S>
AnyCSTNodeId = exists S: CSTStage . CSTNodeId<S>

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

CSTNode<S> = TerminalNode<S> | NonTerminalNode<S, NonTerminalKind<S>>

CSTOriginField: FieldName = FieldName(text: "origin", wireTag: 1)
CSTTerminalValueField: FieldName = FieldName(text: "value", wireTag: 2)
```

A terminal node is a concrete token, trivia element, token slice, or explicit missing terminal. A
non-terminal node is an occurrence of a grammar or transformation production. These terms have
their conventional grammar meanings; this specification does not introduce a second color-based
node taxonomy.

`CSTStage` is a representation sort, not a global time counter. Initial source processing follows
`Lexed -> PreprocessorStructured`, while recursive macro rescan may alternate an intermediate
`MacroExpanded` token stream with a newly recognized `PreprocessorStructured` fragment. The
well-founded order is the explicit rewrite/predecessor graph; stage tags constrain node schemas and
operations but cannot by themselves prove that one occurrence precedes another.

`NonTerminalFields<S, K>` is a generated closed value type specific to `K`. A fixed sequence is a
product; a grammar choice is a tagged closed variant of products; an optional group is an `Option`
of its complete group value; and repetition is a `NodeList`/`NonEmpty` of the complete group value,
not parallel lists for its leaves. Every terminal constituent written by a production (keyword,
operator, delimiter, separator, or other token) and every non-terminal constituent still has a
named field within the product in which it occurs. Lexical trivia are themselves terminal nodes in
the `Lexed` snapshot and are retained by the stage-specific list/region fields described below; a
grammar production does not invent anonymous whitespace children. There is no independently stored
`children` list or untyped payload that can disagree with the active product/variant value. Generic
operand enumeration traverses that value in source order, so a repeated `(comma, element)` group
enumerates `comma, element, comma, element`, not both field projections in batches.

### Terminal nodes

`TokenList` remains the sole owner of token and trivia values. Terminal nodes are zero-copy
references:

```text
TokenSlice = {
    parent: TokenRef,
    spellingRange: ByteRange,
    virtualType: TokenType
}

TokenSliceId = ContentId<TokenSlice>

TerminalValue<Lexed> =
    TokenTerminal(token: TokenRef)
  | TriviaTerminal(trivia: TriviaRef)

TerminalValue<PreprocessorStructured> =
    TokenTerminal(token: TokenRef)
  | TriviaTerminal(trivia: TriviaRef)

TerminalValue<MacroExpanded> =
    TokenTerminal(token: TokenRef)
  | TriviaTerminal(trivia: TriviaRef)

TerminalValue<Parsed> =
    TokenTerminal(token: TokenRef)
  | TokenSliceTerminal(slice: TokenSliceId)
  | MissingTerminal

TerminalClass = TokenClass | TriviaClass | TokenSliceClass | MissingClass

TerminalNodeKind<S> = {
    k: NodeKind |
        k.family = TerminalNode and
        k in currentNodeSchemaRegistry.stageKinds[Concrete(S)]
}

terminalKind<S>(class: TerminalClass where class is admitted by TerminalValue<S>)
    -> TerminalNodeKind<S>
terminalClass<S>(kind: TerminalNodeKind<S>) -> TerminalClass
terminalClass<S>(value: TerminalValue<S>) -> TerminalClass

terminalClass(terminalKind<S>(class)) = class
terminalKind<S>(terminalClass(kind)) = kind
terminalClass(TokenTerminal(_)) = TokenClass
terminalClass(TriviaTerminal(_)) = TriviaClass
terminalClass(TokenSliceTerminal(_)) = TokenSliceClass
terminalClass(MissingTerminal) = MissingClass

TerminalConstraint =
    TokenTypeConstraint(TokenType)
  | IdentifierSpelling(Text)
  | RegisteredTerminal(SyntaxParseInfoId)

```

`currentNodeSchemaRegistry` denotes the immutable registry selected by the owning snapshot's
`schema` version. It is an explicit serialization/query input, not process-global mutable state.

`terminalKind` and `terminalClass` are generated total inverse mappings for the terminal classes
admitted at each stage. A terminal record's `kind`, its ID's cached `kind`, and the class of its
`value` must agree through those mappings. This gives every terminal exactly one `NodeDescriptor`
without encoding a grammar field's contextual `TerminalConstraint` into the terminal itself.

`MissingTerminal` owns no `Token` and cannot appear in a token projection. Its descriptor exposes
`expected`, directional `anchor`, and `recoveryRule` as read-only projections of its
`RecoverMissing` rewrite; the nullary terminal alternative does not store those facts a second
time. A `TokenSlice` is valid
only under a named token-splitting rule; its byte range lies within its parent token's logical
spelling. For example, parsing generic closers can expose one physical `>>` token as two terminal
nodes whose slice ranges partition that spelling. The parent token and its trivia do not change.
`Parsed` terminals follow the active token projection and therefore do not duplicate trivia
terminals. A parsed token reaches its `LeadingTrivia`/`TrailingTrivia` ranges through its `TokenRef`
and reaches inactive/directive trivia through predecessor CST snapshots.

### Typed non-terminal fields

The generated CST schema has category-refined reference types:

```text
ExprCSTNodeId<S> =
    NonTerminalNodeId<S, kind where category(kind) includes ExprCSTCategory>
StmtCSTNodeId<S> =
    NonTerminalNodeId<S, kind where category(kind) includes StmtCSTCategory>
DeclCSTNodeId<S> =
    NonTerminalNodeId<S, kind where category(kind) includes DeclCSTCategory>

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

For an `IfStatement` node, `ifKeyword` is an `Identifier` token whose logical spelling is `if`,
`leftParenthesis` and `rightParenthesis` satisfy the established `LParent` and `RParent` token
constraints, and `elseKeyword`, when present, is an `Identifier` spelling `else`. The invariant
`isSome(elseKeyword) = isSome(falseBranch)` is generated from the production. Notice that
`ifKeyword` is a field role, not a new `TokenType`: Slang lexes language words as identifiers.
The contextual `IfLetBinding` alternative implements `ExprCSTCategory` at this field while
remaining unavailable to the general expression production.

The CST production is named `IfStatement`, following `if-statement` and `parseIfStatement`. Its
surface AST translation constructs the established `IfStmt` fields `predicate`,
`positiveStatement`, and `negativeStatement`. CST field names describe written grammar roles;
AST field names retain codebase terminology for the semantic syntax hierarchy.

The schema exposes both typed and generic access from the same stored fields:

```text
fieldDescriptors<S>(kind: NonTerminalKind<S>) -> NodeList<FieldDescriptor>
projectedCSTFieldKind<S>(kind: NonTerminalKind<S>, key: FieldName)
    -> Option<FieldValueKind>
activeFieldOccurrences<S>(node: CSTNodeId<S>) -> NodeList<ActiveCSTFieldOccurrence>
field<S>(node: CSTNodeId<S>, key: FieldName) -> CSTFieldQueryResult
cstShapeValue(p: CSTProductionDescriptor,
              node: NonTerminalNodeId<Parsed, Production(p.production)>)
    -> CSTShapeValue<p>
withCSTField<S>(snapshot: CSTSnapshot<S>, node: CSTNodeId<S>,
                key: FieldName, value: CSTFieldValue, rewriteRule: RuleId)
    -> Result<CSTEditResult<S>, CSTEditFailure>
withCSTCursorField<S>(snapshot: CSTSnapshot<S>, cursor: CSTCursor<S>,
                      key: FieldName, value: CSTFieldValue, rewriteRule: RuleId)
    -> Result<CSTEditResult<S>, CSTEditFailure>
constructCSTRewriteOutput<S, K>(snapshot: CSTSnapshot<S>, rewrite: CSTRewrite,
                                role: FieldName, fields: NonTerminalFields<S, K>)
    -> Result<CSTEditResult<S>, CSTEditFailure>
cstOperands<S>(node: CSTNodeId<S>) -> NodeList<CSTNodeId<S>>

CSTEditResult<S> = {
    snapshot: CSTSnapshot<S>,
    node: CSTNodeId<S>
}

CSTEditFailure = UnknownCSTField(kind: NodeKind, field: FieldName)
               | ReadOnlyCSTField(kind: NodeKind, field: FieldName)
               | CSTFieldValueMismatch(field: FieldName,
                                       expected: FieldValueKind,
                                       actual: CSTFieldValue)
               | CSTInvariantViolation(rule: RuleId)
               | InvalidCSTRewritePredecessor(rewrite: CSTRewriteId)

CSTFieldValue =
    FieldValue where every SchemaNodeValue is CSTNodeRef | SchemaValueRef

CSTFieldQueryResult = UnknownField | InactiveField | FoundField(CSTFieldValue)

CSTShapeStep =
    ProductField(field: FieldName)
  | VariantAlternative(group: CSTGroupTag, alternative: CSTVariantTag)
  | OptionalPayload(group: CSTGroupTag)
  | ListElement(group: CSTGroupTag, index: UInt32)

ActiveCSTFieldOccurrence = {
    descriptor: FieldDescriptor,
    path: NodeList<CSTShapeStep>,
    value: CSTFieldValue
}
```

`fieldDescriptors(kind)` returns the closed schema inventory, including fields confined to variant
alternatives. A `CSTProductionFieldDescriptor` structurally refines `FieldDescriptor` with its
typed reference and grammar occurrences. `projectedCSTFieldKind` applies the enclosing
product/variant/cardinality paths to the leaf descriptor; that is the expected kind used by
`field` and `withCSTField`, not the unwrapped leaf kind. `cstShapeValue` returns the one complete
reflective value whose kind is obtained by compiling the production shape. `activeFieldOccurrences(node)` walks that actual
product/variant/cardinality value and may report the same repeated field role at several occurrence
paths. `field(node,key)` returns `InactiveField` when the name exists only in an unselected variant;
through optional/repeated groups it returns the corresponding `OptionalValue`, `ListValue`, or
`NonEmptyListValue` projection. That projection is a view, not parallel storage.

`projectedCSTFieldKind` walks the final `CSTProductionDescriptor.shape`, starts with the leaf
descriptor's `valueKind`, and folds its enclosing final-shape cardinalities from inner to outer,
applying `OptionalKind`, `ListKind`, or `NonEmptyListKind`. A final-shape variant affects whether
the query returns `InactiveField`; it does not wrap an active leaf in a second variant value. The
occurrence-level `variantPath` and `cardinalityPath` retain the original EBNF trace for auditing but
do not override an exact reviewed shape promotion such as `IfStatement.conditionExpr`. A profile
may merge several occurrences under one field name only when they are mutually exclusive or
co-referential and all yield the same projected kind. Otherwise schema generation rejects the name
collision. This generated function is the single kind authority for both reads and edits.

`cstOperands` recursively walks the active shape and flattens only occurrences whose descriptor
edge is `Structural`, in concrete source order. Such a field may be serialized or a read-only
projection of declared rewrite outputs; rewrite-input/scalar projections have `Provenance` or
`Semantic` edges and are excluded. `field` exposes every category, and callers traverse
non-structural relations through `rewriteInputs` or an explicit edge-category query. `withCSTField`
accepts only descriptors marked `Editable`; for a repeated/optional path it replaces the whole
projected value and reconstructs a shape only if sibling co-presence/cardinality invariants still
hold. It validates the generated field type and all cross-field invariants and returns a node in a new owning snapshot.
It never mutates its argument. It creates a `FunctionalCSTEdit` rewrite from the old node using the
mandatory `rewriteRule` and assigns that rewrite output as the new node origin. `CSTOriginField` and
every `DerivedField`/rewrite-projected provenance field are `ReadOnly`; a caller that needs a new
provenance relation must use a generated translation constructor or `constructCSTRewriteOutput`,
which validates the operation, output role, and complete product together. Preserving an old origin
while changing a field is not an API option. Serialization uses stable field tags rather than C++
layout.

For a non-root identity edit, the new snapshot copies the finite indexed graph, replaces the target
record at its corresponding canonical occurrence, and rebinds unchanged ancestor local indices in
the new snapshot namespace; the returned root therefore reaches the edited node without mutating or
orphaning the old graph. Ancestor field products and origins remain valid because their local-index
values did not change. `withCSTField` edits the node identity, so an intentionally shared
`Alternative` terminal changes at every alias in the new snapshot. `withCSTCursorField` is the
occurrence-specific operation: it clones the selected alternative path, rewires that path through
functional edit outputs, and leaves other aliases bound to their old records. Both operations rerun
root reachability, structural-parent, output-binding, and canonical reindexing validation before
publication.

Every CST node descriptor exposes `CSTOriginField` exactly once as a provenance field. A terminal
descriptor also exposes `CSTTerminalValueField` exactly once. These schema fields are the generic
view of the correspondingly named typed record members; they are not duplicate storage.
`cstOperands` excludes both header fields.

### Snapshots and cursors

```text
LocalCSTNodeIndex = UInt64
CanonicalCSTNodeIndex = UInt64

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
    root: NonTerminalNodeId<S>,
    terminals: CanonicallyOrderedMap<TerminalNodeId<S>, TerminalNode<S>>,
    nonTerminals: CanonicallyOrderedMap<NonTerminalNodeId<S>,
                                        NonTerminalNode<S, NonTerminalKind<S>>>,
    outputBindings:
        CanonicallyOrderedMap<CSTRewriteOutput, CSTRewriteOutputBinding<S>>,
    primaryList: TokenListId,
    tokenLists: CanonicallyOrderedSet<TokenListId>,
    activityMaps: NodeMap<TokenListId, TokenActivityMapId>,
    predecessors: CanonicallyOrderedSet<AnyCSTSnapshotId>,
    sourceDependencies: CanonicallyOrderedSet<SourceFileSnapshotId>
}

CSTSnapshotId<S> = ContentId<CanonicalCSTSnapshotRecord<S>>

CanonicalNonTerminalFields<S, K> =
    canonical serialization of NonTerminalFields<S, K> with same-snapshot node IDs remapped to
    CanonicalCSTNodeIndex and every map/set normalized by its declared schema rule

CanonicalCSTRewriteOutputBinding<S> =
    canonical serialization of CSTRewriteOutputBinding<S> with its same-snapshot terminal or
    non-terminal ID remapped to CanonicalCSTNodeIndex

CanonicalTerminalRecord<S> = {
    local: CanonicalCSTNodeIndex,
    kind: TerminalNodeKind<S>,
    value: TerminalValue<S>,
    origin: CSTNodeOrigin
}

CanonicalNonTerminalRecord<S> = {
    local: CanonicalCSTNodeIndex,
    kind: NonTerminalKind<S>,
    fields: CanonicalNonTerminalFields<S, kind>,
    origin: CSTNodeOrigin
}

CanonicalCSTSnapshotRecord<S> = {
    stage: S,
    schema: SchemaVersion,
    root: CanonicalCSTNodeIndex,
    terminals: NodeList<CanonicalTerminalRecord<S>>,
    nonTerminals: NodeList<CanonicalNonTerminalRecord<S>>,
    outputBindings:
        CanonicallyOrderedMap<CSTRewriteOutput, CanonicalCSTRewriteOutputBinding<S>>,
    primaryList: TokenListId,
    tokenLists: CanonicallyOrderedSet<TokenListId>,
    activityMaps: NodeMap<TokenListId, TokenActivityMapId>,
    predecessors: CanonicallyOrderedSet<AnyCSTSnapshotId>,
    sourceDependencies: CanonicallyOrderedSet<SourceFileSnapshotId>
}

CSTCursor<S> = {
    snapshot: CSTSnapshotId<S>,
    path: NodeList<CSTFieldStep>
}

CSTFieldStep = {
    field: FieldName,
    occurrence: Option<UInt32>
}
```

Nodes have snapshot-local identity just as staged AST nodes do. `CanonicalCSTSnapshotRecord` omits
the self-referential `CSTSnapshot.id` and never hashes builder-assigned `LocalCSTNodeIndex` values.
Before encoding, a deterministic worklist starts at the root, assigns consecutive
`CanonicalCSTNodeIndex` values on first visit, and enqueues same-snapshot edges by edge class
(`Structural` before `Alternative`), then descriptor source order and list occurrence. After that
primary/alternative closure, it visits auxiliary same-snapshot outputs of provenance-reachable
rewrites in rewrite-input, operation-list, output-role, and output-ordinal order, recursively applying
the same structural/alternative ordering to each auxiliary node. Provenance does not create a
primary parent, but it may retain an intermediate `TokenPasteExpansion` or recovery result needed
for a complete trace. Every stored node must be reached by one of these phases; an unrelated orphan
record is invalid. Terminal and non-terminal arrays are emitted in canonical-index order, indices
are unique across both arrays, and all same-snapshot references are remapped to those indices. The
root is canonical index zero and resolves to a non-terminal. A terminal ID's cached
`kind` and a non-terminal ID's cached `kind` must agree with the referenced record. Each terminal
record's kind must also equal `terminalKind<S>(terminalClass(record.value))`. The record is
hashed only after all local and predecessor references validate. Equal subrecords may share
storage, but two occurrences remain distinguishable by their field paths.

`primaryList` belongs to `tokenLists`; every terminal's `TokenRef`/`TriviaRef` ultimately resolves
in one of those lists. `Lexed` and initial `PreprocessorStructured` snapshots have empty
`activityMaps`: recognizing a conditional does not evaluate it. `MacroExpanded` publishes one flat
primary expansion list and a `TokenActivityMap` total over that list. It may retain maps for source,
include, and intermediate lists when provenance or tooling addresses those lists. `Parsed` retains
the macro-expanded lists and maps unchanged. A map entry's key must equal the containing
`activityMaps` key, so activity for one list cannot accidentally filter another.

Parent, occurrence, and aggregate range are contextual queries on `CSTCursor`, not stored node
fields. `parent(cursor)` removes the last path step. `physicalRanges(cursor)` traverses terminal
origins under that occurrence and returns an ordered `SourceRangeSet` or `None`. A cursor is an
ephemeral navigation value: it is neither serialized nor part of node identity.

### The lexed CST

Lexing still returns exactly the flat `TokenList = NodeList<Token | Trivia>` defined above. A pure
mechanical query wraps that list in the initial CST:

```text
BuildLexedCST(tokens: TokenList) -> CSTSnapshot<Lexed>

TokenizedSourceFields = {
    elements: NodeList<TerminalNodeId<Lexed>>
}
```

There is one terminal node for every list element, in the same order, and
`TokenizedSource.elements[i]` refers to `(tokens, i)`. The root is the single
`TokenizedSource` non-terminal. This wrapper adds concrete structure but no second token owner and
no token-only shadow array.

`REP-CST-001`: The terminal projection of `CSTSnapshot<Lexed>.root` is a bijection with its input
`TokenList`, including trivia and EOF. Concatenating the physical spellings in that projection
reproduces the decoded source exactly; resolving the source record permits byte-exact identity
output for an unchanged file.

### Preprocessor structuring

`StructurePreprocessor` translates the flat lexed CST into named preprocessor productions before
expansion:

```text
StructurePreprocessor(CSTSnapshot<Lexed>, PreprocessorOptions)
    -> CheckResult<CSTSnapshot<PreprocessorStructured>>

PreprocessorName = {
    text: InternedString
}

BuiltinMacroDefinitionId = (standardEnvironment: StandardEnvironmentId,
                            name: PreprocessorName,
                            rule: RuleId)

MacroDefinitionRef =
    SourceMacroDefinition(NonTerminalNodeId<PreprocessorStructured, MacroDefinition>)
  | BuiltinMacroDefinition(BuiltinMacroDefinitionId)

MacroBinding =
    Defined(definition: MacroDefinitionRef)
  | Undefined(undef: NonTerminalNodeId<PreprocessorStructured, UndefDirective>)

preprocessor::Environment = {
    parent: Option<preprocessor::EnvironmentId>,
    macros: NodeMap<PreprocessorName, MacroBinding>
}

preprocessor::EnvironmentId = ContentId<preprocessor::Environment>

IncludeUniqueIdentity = Utf8String

PragmaWarningSpecifier = Default | Disable | Error | Once | Suppress

WarningOnceState = Available | Consumed(at: SourceRange)

WarningTimelineEntry = {
    specifier: PragmaWarningSpecifier,
    location: SourceRange,
    onceState: Option<WarningOnceState>,
    suppressedDiagnostic: Option<SourceRange>
}

WarningTimeline = NodeList<WarningTimelineEntry>

WarningStateTracker = {
    timelines: NodeMap<Int32, WarningTimeline>,
    stack: NodeList<NodeMap<Int32, PragmaWarningSpecifier>>
}

WarningStateTrackerId = ContentId<WarningStateTracker>

PreprocessorDirectiveState = {
    warningStateTracker: WarningStateTrackerId,
    languageRules: LanguageRuleSetId,
    logicalLocations: PreprocessorLogicalLocationStateId,
    registered: NodeMap<QualifiedName, SchemaValue>
}

PreprocessorLogicalLocationState = {
    lineDirectives: NodeMap<SourceViewId, NodeList<SourceLineDirective>>
}

PreprocessorLogicalLocationStateId = ContentId<PreprocessorLogicalLocationState>

PreprocessorInputFrame = {
    sourceView: SourceViewId,
    uniqueIdentity: IncludeUniqueIdentity,
    includeDirective: Option<
        NonTerminalNodeId<PreprocessorStructured, IncludeDirective>>
}

preprocessor::Conditional = {
    group: NonTerminalNodeId<PreprocessorStructured, ConditionalGroup>,
    branch: UInt32,
    activity: TokenActivity
}

PreprocessorState = {
    environment: preprocessor::EnvironmentId,
    inputStack: NodeList<PreprocessorInputFrame>,
    conditionalStack: NodeList<preprocessor::Conditional>,
    busyInvocations: NodeList<
        NonTerminalNodeId<PreprocessorStructured, MacroInvocation>>,
    pragmaOnceUniqueIdentities: CanonicallyOrderedSet<IncludeUniqueIdentity>,
    loadedSources: NodeMap<IncludeUniqueIdentity, SourceFileSnapshotId>,
    directiveState: PreprocessorDirectiveState
}

PreprocessorStateId = ContentId<PreprocessorState>

PreprocessorExpansionResult = {
    snapshot: CSTSnapshot<MacroExpanded>,
    initialState: PreprocessorStateId,
    finalState: PreprocessorStateId,
    steps: NodeList<PreprocessorStep>,
    interpretedViews: NodeMap<SourceViewId, SourceViewId>
}

PreprocessorElementCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured,
        kind where category(kind) includes PreprocessorElement>
SourcePreprocessorElementCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured,
        kind where category(kind) includes SourcePreprocessorElement>
MacroDefinitionCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroDefinition>
MacroDefinitionParamCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroDefinitionParam>
MacroDefinitionParameterClauseCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroDefinitionParameterClause>
MacroDefinitionParameterTailCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroDefinitionParameterTail>
MacroInvocationArgCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroInvocationArg>
MacroInvocationArgumentClauseCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroInvocationArgumentClause>
MacroInvocationArgumentTailCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroInvocationArgumentTail>
MacroReplacementElementCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured,
        kind where category(kind) includes MacroReplacementElement>
PreprocessorDirectiveCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured,
        DefineDirective | UndefDirective | IncludeDirective |
        ConditionalGroup | DiagnosticDirective | LineDirective |
        PragmaDirective | LanguageDirective | UnknownDirective>

PreprocessorUnitFields<PreprocessorStructured> = {
    elements: NodeList<SourcePreprocessorElementCSTNodeId>
}

PreprocessorFragmentFields = {
    elements: NodeList<PreprocessorElementCSTNodeId>
}

PreprocessorUnitFields<MacroExpanded> = {
    elements: NodeList<CSTNodeId<MacroExpanded>>
}

PreprocessorElement = TextRegion | DefineDirective | UndefDirective | IncludeDirective |
                      ConditionalGroup | DiagnosticDirective | LineDirective |
                      PragmaDirective | LanguageDirective | MacroInvocation |
                      UnknownDirective | PreprocessorRecovery

SourcePreprocessorElement = TextRegion | DefineDirective | UndefDirective | IncludeDirective |
                            ConditionalGroup | DiagnosticDirective | LineDirective |
                            PragmaDirective | LanguageDirective |
                            UnknownDirective | PreprocessorRecovery

DefineDirectiveFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    defineKeyword: TerminalNodeId<PreprocessorStructured>,
    definition: MacroDefinitionCSTNodeId,
    lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
}

MacroDefinitionFields = {
    name: TerminalNodeId<PreprocessorStructured>,
    parameterClause: Option<MacroDefinitionParameterClauseCSTNodeId>,
    replacement: NodeList<MacroReplacementElementCSTNodeId>
}

MacroDefinitionParameterClauseFields = {
    leftParenthesis: TerminalNodeId<PreprocessorStructured>,
    firstParameter: Option<MacroDefinitionParamCSTNodeId>,
    remainingParameters: NodeList<MacroDefinitionParameterTailCSTNodeId>,
    rightParenthesis: TerminalNodeId<PreprocessorStructured>
}

MacroDefinitionParameterTailFields = {
    comma: TerminalNodeId<PreprocessorStructured>,
    parameter: MacroDefinitionParamCSTNodeId
}

MacroDefinitionParamFields = {
    name: Option<TerminalNodeId<PreprocessorStructured>>,
    ellipsis: Option<TerminalNodeId<PreprocessorStructured>>
}

MacroInvocationArgFields = {
    elements: NodeList<CSTNodeId<PreprocessorStructured>>,
    writtenRange: TokenListRange
}

MacroRawSpanFields = {
    terminals: NonEmpty<TerminalNodeId<PreprocessorStructured>>
}

MacroParamReferenceFields = {
    name: TerminalNodeId<PreprocessorStructured>
}

MacroStringizeFields = {
    stringizeOperator: TerminalNodeId<PreprocessorStructured>,
    parameter: NonTerminalNodeId<PreprocessorStructured, MacroParamReference>
}

MacroInvocationFields = {
    name: TerminalNodeId<PreprocessorStructured>,
    definition: rewriteProjection<MacroDefinitionRef>,
    argumentClause: Option<MacroInvocationArgumentClauseCSTNodeId>
}

MacroInvocationArgumentClauseFields = {
    leftParenthesis: TerminalNodeId<PreprocessorStructured>,
    firstArgument: Option<MacroInvocationArgCSTNodeId>,
    remainingArguments: NodeList<MacroInvocationArgumentTailCSTNodeId>,
    rightParenthesis: TerminalNodeId<PreprocessorStructured>
}

MacroInvocationArgumentTailFields = {
    comma: TerminalNodeId<PreprocessorStructured>,
    argument: MacroInvocationArgCSTNodeId
}

TokenPasteFields = {
    leftOperand: MacroReplacementElementCSTNodeId,
    pasteOperator: TerminalNodeId<PreprocessorStructured>,
    rightOperand: MacroReplacementElementCSTNodeId
}
```

A serialized `preprocessor::Environment` in the input state may refer only to builtin definitions
or source definitions in already-published predecessor snapshots. Definitions and `#undef`
tombstones encountered during expansion produce a new environment before the following source
region is scanned. A newly recognized `MacroInvocation` projects its resolved definition from the
recognition rewrite. Environment publication therefore follows source order; no environment
content ID can depend on the snapshot ID that is still being computed.

`PreprocessorName` is the serializable immutable counterpart of the current preprocessor's `Name*`:
it interns decoded identifier text but has no AST `NameClass`, `Origin`, or hygiene. Preprocessor
lookup compares that text under the active lexical language rules, never pointer identity. A
`MacroBinding.Undefined` entry is a tombstone: lookup stops at that environment and does not fall
through to a parent's definition. This is what makes `#undef` of an inherited binding representable.

`PreprocessorState` is the complete immutable state that can affect a later preprocessing step.
`inputStack` is the single authority for active include traversal; the current implementation's
`includedFiles` cycle-detection set is derived from its unique identities. `conditionalStack` and
`busyInvocations` make branch activity and `MacroInvocation::isBusy` explicit rather than hidden
control state. `pragmaOnceUniqueIdentities` retains the established codebase name. `loadedSources`
freezes the exact source snapshot selected for an include identity, and `directiveState` contains
warning/language/logical-location plus schema-declared registered-directive state. Entering and leaving an included
file functionally push and pop `inputStack`; the included unit's final environment, pragma-once
additions, source selections, and directive state flow back to the including scan. No mutable field
of `IncludeSystem`, `SourceManager`, or a scheduler cache is an undeclared semantic input.

The state passed to `ExpandPreprocessor` has a nonempty `inputStack` whose last frame's `sourceView`
is the view underlying the initial structured snapshot. On normal or recovered return the same root
frame remains last; only nested include frames are scoped away. `MacroExpansionContext.currentInput`
is always that last frame, so top-level and included builtin macros have a defined file context.

For a function-like definition, `parameterClause` is present only when its left parenthesis
immediately follows the definition name with no intervening `Trivia`; thus `#define F(x)` is
function-like while `#define F (x)` is object-like and begins its replacement with `(`. For an
invocation, `argumentClause` is selected only after name lookup resolves a `FunctionLike`
definition; ordinary trivia may occur between the invocation name and its left parenthesis. An
object-like invocation has no argument clause. A clause owns both parentheses. Its optional first item is followed
by source-ordered tail non-terminals, each of which owns one comma immediately followed by the next
parameter or argument. Thus generic operand traversal yields `a , b , c`, never parallel
`[a,b,c]` and `[, ,]` projections. A zero-parameter definition has no first parameter and no tails.
Invocation recognition uses the selected definition to distinguish a zero-argument `M()` from one
zero-width argument; the latter has a `MacroInvocationArg` with an `Empty` rewrite source anchored
before the right parenthesis. A variadic definition retains the exact ellipsis terminal in its
last `MacroDefinitionParam`; the spelling-only form `...` derives the established name
`__VA_ARGS__` without fabricating a name terminal. An ordinary parameter has only `name`, a named
variadic parameter has both fields, and the spelling-only form has only `ellipsis`. These equations,
keyword/operator spelling, and
definition/argument arity are generated validators, not assumptions in expansion code.

The initial `StructurePreprocessor` root contains source-order directives, definitions,
conditionals, and `TextRegion` nodes; it does not guess whether an ordinary identifier is a macro.
While expanding an active text region, `RecognizeMacroInvocation` resolves the then-current
environment and publishes a later `PreprocessorStructured` fragment containing the invocation and
its arguments. The same operation applies to intermediate macro-output and include streams. Thus a
`MacroInvocation` is still concrete non-terminal structure, but its existence and `definition`
projection are justified by the exact state at its recognition rewrite.

The actual generated products also name every directive operand, conditional delimiter, parameter
token, argument delimiter, and recovery constituent. `TokenList` remains the sole owner of every
`Trivia` value. A structured production may reference a trivia terminal when it is syntactically
significant (for example `DefineDirective.lineEnd`) without copying that value. Other intervening
trivia is reached through token adjacency or an exact `TokenListRange`; in particular,
`MacroInvocationArg.writtenRange` includes the complete written argument spelling used by
stringization. No anonymous gap field or reconstructed whitespace flag is a second authority. The
abbreviated products above establish the important identity and typing constraints; they do not
license anonymous punctuation. `MacroDefinitionRef` names either a source `MacroDefinition`
non-terminal or a registered builtin definition. Compiled `MacroDefinition::Op` values are a pure
derived query over the definition's replacement fields. They are executable preprocessing data,
not a competing concrete-syntax representation.

Every nonempty structured node has a `CSTRewrite` whose `Consumed` inputs are the exact predecessor
terminals it groups. A zero-width node instead uses `Empty` with its exact directional predecessor
anchor.
Nothing is dropped: inactive branches and ignored/unknown directives remain ordinary typed
non-terminals. Identity formatting follows the structure rewrites to the `Lexed` predecessor root,
which reproduces the exact token/trivia sequence; the structured snapshot does not create a second
layout authority.

An invocation that appears only after argument prescan or replacement playback is structured with
the same `MacroInvocation`/`MacroInvocationArg` schema in a later, topologically ordered
`PreprocessorStructured` fragment. Each fragment terminal is produced by
`PreserveTerminal(earlierMacroOutput, PreprocessorStructured)`: its `Token` keeps the earlier macro
`TokenOrigin`, while the new terminal's own origin has the stage-correct bridge output. The final
`MacroExpanded` snapshot lists those fragments among its
predecessors. Thus nested expansion does not fall back to an untyped token-loop record merely
because its spelling was generated.

Likewise, `ExpandPreprocessor` carries every retained source `TextRegion` terminal not replaced by
a macro into the `MacroExpanded` primary list through
`PreserveTerminal(input, MacroExpanded)`, preserving the exact token/trivia interleaving. A copied
immutable `Token` retains its existing `TokenOrigin`; copied `Trivia` retains its exact value. The
new terminal records the stage bridge in either case, and the list's `TokenActivityMap` records
whether its enclosing conditional branch contributes to an active view. Directive terminals remain
reachable through the structured predecessor and do not enter the parser-facing view unless a named
directive rule explicitly produces a token or trivia element.

### Rewrite provenance

A translation records why each output node exists and which earlier nodes produced it. This same
mechanism covers preprocessor structuring, macro expansion, include traversal, grammar parsing,
recovery, and later syntax synthesis:

```text
CSTRewriteId = ContentId<CSTRewrite>

AtomicPreprocessorActionRewriteId =
    CSTRewriteId where operation is RecognizeMacroInvocation |
                                    ApplyPreprocessorDirective |
                                    ChangePreprocessorState

ScopedPreprocessorActionRewriteId =
    CSTRewriteId where operation is ExpandMacroInvocation | IncludeExpansion

CSTRewrite = {
    rule: RuleId,
    operation: CSTRewriteOperation
}

CSTRewriteOutputClass =
    TokenTerminalBundle(stage: CSTStage)
  | TerminalResult(stage: CSTStage,
                   class: TerminalClass where class is admitted by TerminalValue<stage>)
  | NonTerminalResult(stage: CSTStage, kind: NonTerminalKind<stage>)

CSTRewriteOutputDescriptor = {
    role: FieldName,
    outputClass: CSTRewriteOutputClass,
    count: UInt32
}

rewriteOutputDescriptors(operation: CSTRewriteOperation)
    -> NodeList<CSTRewriteOutputDescriptor>

CSTRewriteOutput = {
    rewrite: CSTRewriteId,
    role: FieldName,
    ordinal: UInt32
}

rewriteOutputDescriptor(output: CSTRewriteOutput where output is valid)
    -> CSTRewriteOutputDescriptor

CSTRewriteOutputBinding<S> =
    TokenTerminalBundleBinding {
        token: TokenRef,
        terminal: TerminalNodeId<S>
    }
  | TerminalResultBinding(terminal: TerminalNodeId<S>)
  | NonTerminalResultBinding(node: NonTerminalNodeId<S>)

resolveOutput<S>(snapshot: CSTSnapshot<S>, output: CSTRewriteOutput)
    -> Option<CSTRewriteOutputBinding<S>>

CSTNodeOrigin =
    LexedRoot(tokens: TokenListId)
  | LexedElement(element: TokenListElementRef)
  | RewriteOutput(output: CSTRewriteOutput)

CSTRewriteInput =
    PreviousNode(role: FieldName, node: AnyNonTerminalNodeId)
  | PreviousTerminal(role: FieldName, terminal: AnyTerminalNodeId)
  | EarlierOutput(role: FieldName, output: CSTRewriteOutput)
  | SourceInput(role: FieldName, range: SourceRange)

CSTTerminalRewriteInput =
    input: CSTRewriteInput where
        input is PreviousTerminal or
        (input is EarlierOutput(_, output) and
         rewriteOutputDescriptor(output).outputClass is
            TokenTerminalBundle | TerminalResult)

terminalClass(input: CSTTerminalRewriteInput) -> TerminalClass

CSTTokenRewriteInput =
    input: CSTTerminalRewriteInput where terminalClass(input) = TokenClass

CSTPositionalRewriteInput =
    input: CSTRewriteInput where input is PreviousNode | PreviousTerminal | EarlierOutput

CSTRewriteAnchor =
    Before(input: CSTPositionalRewriteInput)
  | After(input: CSTPositionalRewriteInput)
  | EndOfInput(view: TokenListViewId)
  | SourceAnchor(range: SourceRange where range.startByte = range.endByte)

CSTRewriteSource =
    Consumed(inputs: NonEmpty<CSTRewriteInput>)
  | Empty(anchor: CSTRewriteAnchor)

CSTRewriteOperand =
    PreviousTerminalOperand(terminal: AnyTerminalNodeId
                            where terminalClass(terminal.kind) = TokenClass)
  | EarlierOutputOperand(output: CSTRewriteOutput
                         where rewriteOutputDescriptor(output).outputClass is
                             TokenTerminalBundle | TerminalResult(_, TokenClass))

CSTRewriteReplacementBinding = {
    name: FieldName,
    value: CSTRewriteReplacement
}

CSTRewriteReplacementMapEntry = {
    key: CSTRewriteReplacement,
    value: CSTRewriteReplacement
}

CSTRewriteReplacement =
    ReplacementCSTNode(CSTPositionalRewriteInput)
  | ReplacementSchemaValue(ContentId<SchemaValue>)
  | ReplacementScalar(RegisteredScalarValue)
  | ReplacementProduct(NodeList<CSTRewriteReplacementBinding>)
  | ReplacementVariant(tag: CSTVariantTag, payload: CSTRewriteReplacement)
  | ReplacementOptional(Option<CSTRewriteReplacement>)
  | ReplacementList(NodeList<CSTRewriteReplacement>)
  | ReplacementNonEmptyList(NonEmpty<CSTRewriteReplacement>)
  | ReplacementMap(NodeList<CSTRewriteReplacementMapEntry>)

CSTRewriteOperation =
    StructureNonTerminal(stage: CSTStage,
                         kind: NonTerminalKind<stage>,
                         source: CSTRewriteSource)
  | PreserveTerminal(input: CSTTerminalRewriteInput, targetStage: CSTStage)
  | RecognizeMacroInvocation(MacroInvocationRecognitionRewrite)
  | ApplyPreprocessorDirective(PreprocessorDirectiveRewrite)
  | ChangePreprocessorState(PreprocessorStateChangeRewrite)
  | ExpandMacroDefinitionOp(MacroDefinitionOpRewrite)
  | ReplayMacroInvocationResult(MacroInvocationResultReplayRewrite)
  | ExpandMacroInvocation(MacroInvocationExpansionRewrite)
  | IncludeExpansion(IncludeExpansionRewrite)
  | SplitToken(TokenSplitRewrite)
  | ParseProduction(production: ProductionId,
                    source: CSTRewriteSource)
  | RecoverMissing(expected: TerminalConstraint,
                   anchor: CSTRewriteAnchor)
  | RecoverSkipped(source: NonEmpty<CSTRewriteInput>)
  | RecoverUnexpected(actual: CSTRewriteInput,
                      expectedCategory: QualifiedName)
  | FunctionalCSTEdit(previous: CSTRewriteInput,
                      changedField: FieldName,
                      replacement: CSTRewriteReplacement)
  | SynthesizeSyntax(role: QualifiedName,
                     inputs: NodeList<CSTRewriteInput>)
```

The typed record carried by each operation is authoritative; a generic `rewriteInputs` query
enumerates its named input fields and does not read a second stored input list. A `Consumed` source
enumerates every consumed predecessor. An `Empty` source consumes nothing and records only its
directional position: a `Before`/`After` input must be a strict predecessor, `EndOfInput` must be the
exact input view, and `SourceAnchor` must be a zero-width source position. This permits an empty
macro argument or grammar production without fabricating a consumed token. Every input names a
strict predecessor snapshot, a source range, or an output of a rewrite that does not transitively
depend on the current rewrite. A rewrite never names a node or token that it produces. Consequently
`CSTRewriteId` can be published before output tokens and nodes, and the provenance graph cannot
contain a content-identity cycle.

An empty syntax production uses `Before(next)` when a following predecessor occurrence exists,
otherwise `After(previous)` when a preceding occurrence exists, and otherwise `EndOfInput(view)`.
`SourceAnchor` is reserved for source-driven synthesis with no token-list position. This canonical
choice prevents two equivalent zero-width productions from receiving different rewrite identities.

`CSTTerminalRewriteInput` is a static refinement, not a runtime convention. Its `terminalClass` is
obtained from the previous terminal record or earlier output descriptor and is therefore total.
`PreserveTerminal` cannot accept a non-terminal or bare source range. `CSTTokenRewriteInput` further
proves `TokenClass` for operations that replay an unchanged token sequence.

`rewriteOutputDescriptors` is a generated pure function of the typed operation. Dynamic counts
come from authoritative operation fields such as a raw-span length, paste re-lex result count, or
included-terminal count. A `CSTRewriteOutput` is valid only when exactly one descriptor has its
`role` and `ordinal < count`; that named role is the output port, and resolving it must produce the
descriptor's `outputClass`.
`TokenTerminalBundle` deliberately denotes one generated `Token` together with the terminal node
that wraps that token-list element, so both can share one provenance output without colliding with
the containing expansion non-terminal's distinct output role. Unknown roles, wrong sorts, and
out-of-range ordinals are invalid serialized data rather than recovery cases.

`CSTSnapshot.outputBindings` is the authority that realizes an abstract rewrite output as exact
snapshot-local data. Its keys are unique. A `TokenTerminalBundleBinding` is valid only for a
matching bundle descriptor: `token` is in the snapshot's lists, the token's `TokenOrigin` names the
same output, and `terminal.value = TokenTerminal(token)` with the same `RewriteOutput` origin. A
terminal/non-terminal binding likewise matches the descriptor stage/class/kind and the bound node's
origin. Every current-snapshot node with a rewrite-output origin has exactly one inverse binding;
there are no unbound or multiply bound output occurrences. `resolveOutput(snapshot, output)` is the
map lookup, so read-only structural projections such as `MacroExpansion.result` select exact local
nodes rather than guessing from a port.

An `EarlierOutput` input is resolved relative to the snapshot that realizes the consuming rewrite:
the binding must be an earlier local output or occur in exactly one direct predecessor snapshot.
Multiple predecessor bindings without an explicit intervening `PreserveTerminal` are ambiguous and
invalid. The abstract output identity may be realized again in another snapshot only through that
new snapshot's own binding; resolution is always snapshot-qualified.

The built-in descriptor equations include:

```text
outputs(RecognizeMacroInvocation) =
    [(invocation, NonTerminalResult(PreprocessorStructured, MacroInvocation), 1)]

outputs(PreserveTerminal(input, targetStage)) =
    [(terminal, TerminalResult(targetStage, terminalClass(input)), 1)]

outputs(ReplayMacroInvocationResult(replay)) =
    [(result, TerminalResult(MacroExpanded, TokenClass), replay.inputs.count)]

outputs(ExpandMacroDefinitionOp(opcode != TokenPaste)) =
    [(result, TokenTerminalBundle(MacroExpanded), opcodeResultCount(operation))]

outputs(ExpandMacroDefinitionOp(opcode == TokenPaste)) =
    [(result, TokenTerminalBundle(MacroExpanded), operation.input.resultCount),
     (expansion, NonTerminalResult(MacroExpanded, TokenPasteExpansion), 1)]

outputs(ExpandMacroInvocation) =
    [(expansion, NonTerminalResult(MacroExpanded, decisionNodeKind(decision)), 1)]

outputs(IncludeExpansion) =
    [(tokenResult, TokenTerminalBundle(MacroExpanded), includedTokenCount(includedInputs)),
     (triviaResult, TerminalResult(MacroExpanded, TriviaClass),
                    includedTriviaCount(includedInputs)),
     (expansion, NonTerminalResult(MacroExpanded, includeDecisionNodeKind(decision)), 1)]
```

`opcodeResultCount` is derived from the exact raw-span, argument/prescan input, or fixed
stringize/builtin rule; it is never container capacity or a separately editable cache. Grammar,
recovery, split, synthesis, and functional-edit operations have analogous generated equations in
their registered operation descriptors. `includeResultOutputs(r)` walks `r.includedInputs` once in
source order and emits the next `tokenResult` or `triviaResult` output ordinal according to each
input terminal class. This derived list is the authoritative interleaving resolved by an include
expansion node's structural `result` field; separate output ports do not create separate ordering
authorities.

`replacementOf(snapshot, field, value)` is a total structural conversion from a valid
`CSTFieldValue` of `projectedCSTFieldKind(kind, field)` to `CSTRewriteReplacement`. It mirrors every
`FieldValue` constructor: product bindings remain ordered and named; a variant retains its tag and
selected payload; lists, non-empty lists, maps, and optionals recurse without flattening. A
`SchemaNodeValue(CSTNodeRef(n))` becomes `ReplacementCSTNode` naming `n` as a predecessor input; a
`SchemaNodeValue(SchemaValueRef(v))` becomes `ReplacementSchemaValue(v)`. A CST field containing an
AST `SyntaxNodeRef` is invalid. Each predecessor input's role is the nearest named product/group
field; repeated equal roles remain unambiguous because their complete list/product path is retained
by the replacement value. `FunctionalCSTEdit.replacement` is this canonical complete value.
Every node reference in it is a predecessor input or earlier rewrite output; it never points to the
node being produced. Consequently edits of the same predecessor field to different values have
different rewrite identities, and validators can replay an edit without inspecting an unrecorded
caller argument.

For a rewritten non-terminal, predecessor roles such as `expandedFrom`, `definition`, and
`argument` are schema-visible named fields projected from its `CSTRewrite.operation`; structural
roles such as `result` are ordinary current-snapshot node fields. Both are returned by `field`,
while `cstOperands` enumerates only the structural current-snapshot nodes. Thus provenance is not a
side table hidden from generic CST access, and it is not duplicated as an independently editable
field value.

### Macro expansion as a CST rewrite

Expansion replaces a `MacroInvocation` occurrence with an expansion non-terminal in a new
snapshot. The old snapshot remains unchanged. A successful occurrence produces `MacroExpansion`,
an intentionally suppressed occurrence produces `SuppressedExpansion`, and a resource failure
produces `FailedExpansion`; the `MacroInvocation` predecessor itself stores no future-stage
decision:

```text
ExpandPreprocessor(CSTSnapshot<PreprocessorStructured>, IncludeSystem,
                   PreprocessorState, PreprocessorOptions)
    -> CheckResult<PreprocessorExpansionResult>

MacroExpansionFields = {
    expandedFrom: rewriteInput<
        NonTerminalNodeId<PreprocessorStructured, MacroInvocation>>,
    definition: rewriteProjection<MacroDefinitionRef>,
    operations: rewriteProjection<NodeList<CSTRewriteId>>,
    result: structuralRewriteProjection<NodeList<CSTNodeId<MacroExpanded>>>
}

SuppressedExpansionFields = {
    expandedFrom: rewriteInput<
        NonTerminalNodeId<PreprocessorStructured, MacroInvocation>>,
    reason: rewriteProjection<MacroSuppressionReason>,
    operations: rewriteProjection<NodeList<CSTRewriteId>>,
    result: structuralRewriteProjection<NodeList<CSTNodeId<MacroExpanded>>>
}

FailedExpansionFields = {
    expandedFrom: rewriteInput<
        NonTerminalNodeId<PreprocessorStructured, MacroInvocation>>,
    error: rewriteProjection<ErrorId>,
    operations: rewriteProjection<NodeList<CSTRewriteId>>,
    result: structuralRewriteProjection<NodeList<CSTNodeId<MacroExpanded>>>
}

TokenPasteExpansionFields = {
    expandedFrom: rewriteInput<
        NonTerminalNodeId<PreprocessorStructured, TokenPaste>>,
    invocation: rewriteInput<
        NonTerminalNodeId<PreprocessorStructured, MacroInvocation>>,
    definitionOp: rewriteProjection<MacroDefinition::Op>,
    leftInput: Option<rewriteInput<CSTRewriteOperand>>,
    rightInput: Option<rewriteInput<CSTRewriteOperand>>,
    concatenatedSpelling: rewriteProjection<Text>,
    result: structuralRewriteProjection<NodeList<TerminalNodeId<MacroExpanded>>>
}

IncludeExpansionFields = {
    expandedFrom: rewriteInput<
        NonTerminalNodeId<PreprocessorStructured, IncludeDirective>>,
    requestInputs: rewriteProjection<NodeList<CSTRewriteOperand>>,
    request: rewriteProjection<IncludeRequest>,
    resolved: rewriteProjection<ResolvedInclude>,
    includedRoot: rewriteInput<
        NonTerminalNodeId<MacroExpanded, PreprocessorUnit>>,
    result: structuralRewriteProjection<NodeList<CSTNodeId<MacroExpanded>>>
}

SuppressedIncludeExpansionFields = {
    expandedFrom: rewriteInput<
        NonTerminalNodeId<PreprocessorStructured, IncludeDirective>>,
    requestInputs: rewriteProjection<NodeList<CSTRewriteOperand>>,
    request: rewriteProjection<IncludeRequest>,
    resolved: rewriteProjection<Option<ResolvedInclude>>,
    reason: rewriteProjection<IncludeSuppressionReason>,
    result: structuralRewriteProjection<NodeList<CSTNodeId<MacroExpanded>>>
}

FailedIncludeExpansionFields = {
    expandedFrom: rewriteInput<
        NonTerminalNodeId<PreprocessorStructured, IncludeDirective>>,
    requestInputs: rewriteProjection<NodeList<CSTRewriteOperand>>,
    request: rewriteProjection<IncludeRequest>,
    resolved: rewriteProjection<Option<ResolvedInclude>>,
    stage: rewriteProjection<IncludeFailureStage>,
    error: rewriteProjection<ErrorId>,
    result: structuralRewriteProjection<NodeList<CSTNodeId<MacroExpanded>>>
}
```

The notation `rewriteInput<T>` denotes a named, type-checked provenance edge from the node's rewrite
record. `rewriteProjection<T>` exposes a scalar or semantic value, while
`structuralRewriteProjection<T>` resolves declared rewrite outputs as read-only structural fields.
None is stored again in the node's serialized field product. The latter still participates in
`cstOperands` exactly like a stored structural field. `MacroExpansion.expandedFrom` therefore
refers exactly to the macro-call CST node that was replaced. `TokenPasteExpansion.expandedFrom`
refers exactly to the `TokenPaste` node in the definition structure. Its left input may be an
earlier paste output, so `X ## Y ## Z` records the second paste as consuming the first paste result
rather than pretending both operations consumed only source tokens.

Macro operation records retain the codebase's established names:

```text
MacroDefinition::Flavor = FunctionLike | ObjectLike | BuiltinObjectLike
MacroDefinition::Opcode = RawSpan | ExpandedParam | UnexpandedParam |
                          StringizedParam | TokenPaste | BuiltinLine | BuiltinFile

MacroDefinition::Param = {
    definition: MacroDefinitionRef,
    ordinal: UInt32,
    node: Option<MacroDefinitionParamCSTNodeId>,
    name: PreprocessorName,
    isVariadic: Bool
}

MacroDefinition::OpOperand =
    RawSpanNode(node: NonTerminalNodeId<PreprocessorStructured, MacroRawSpan>)
  | ParameterNode(node: NonTerminalNodeId<PreprocessorStructured, MacroParamReference>,
                  parameter: MacroDefinition::Param)
  | StringizeNode(node: NonTerminalNodeId<PreprocessorStructured, MacroStringize>,
                  parameter: MacroDefinition::Param)
  | PasteNode(node: NonTerminalNodeId<PreprocessorStructured, TokenPaste>)
  | BuiltinOperand(rule: RuleId)

MacroDefinition::Op = {
    definition: MacroDefinitionRef,
    ordinal: UInt32,
    opcode: MacroDefinition::Opcode,
    operand: MacroDefinition::OpOperand
}

MacroInvocationRecognitionRewrite = {
    transition: PreprocessorTransitionId,
    source: NonEmpty<CSTRewriteInput>,
    writtenRange: TokenListRange,
    name: PreprocessorName,
    definition: MacroDefinitionRef
}

PreprocessorEffect =
    RecognizeMacroInvocation
  | DefineBinding(definition: MacroDefinitionRef)
  | UndefineBinding(name: PreprocessorName)
  | EnterConditional(group:
        NonTerminalNodeId<PreprocessorStructured, ConditionalGroup>)
  | SelectConditionalBranch(branch: UInt32, activity: TokenActivity)
  | LeaveConditional(group:
        NonTerminalNodeId<PreprocessorStructured, ConditionalGroup>)
  | PushBusyInvocation(invocation:
        NonTerminalNodeId<PreprocessorStructured, MacroInvocation>)
  | PopBusyInvocation(invocation:
        NonTerminalNodeId<PreprocessorStructured, MacroInvocation>)
  | PushInputFile(frame: PreprocessorInputFrame)
  | PopInputFile(frame: PreprocessorInputFrame)
  | ApplyPragma(name: PreprocessorName)
  | ApplyDiagnosticDirective
  | ApplyLineDirective(view: SourceViewId, directive: SourceLineDirective)
  | ApplyLanguageDirective
  | NoStateChange

PreprocessorTransition = {
    before: PreprocessorStateId,
    effect: PreprocessorEffect,
    after: PreprocessorStateId
}

PreprocessorTransitionId = ContentId<PreprocessorTransition>

PreprocessorDirectiveRewrite = {
    transition: PreprocessorTransitionId,
    directive: PreprocessorDirectiveCSTNodeId,
    evaluation: Option<PreprocessorDirectiveEvaluation>
}

PreprocessorDirectiveEvaluation =
    ConditionalEvaluation(ConditionalDirectiveEvaluation)
  | LineEvaluation(LineDirectiveEvaluation)

ConditionalDirectiveEvaluation = {
    expandedInputs: NodeList<CSTRewriteOperand>,
    expression: CanonicalPreprocessorExpression,
    value: BigInt
}

LineDirectiveEvaluation = {
    expandedInputs: NodeList<CSTRewriteOperand>,
    directive: SourceLineDirective
}

CanonicalPreprocessorExpression =
    PPInteger(value: BigInt)
  | PPDefined(name: PreprocessorName, value: Bool)
  | PPFeature(name: PreprocessorName, value: Bool)
  | PPIdentifier(name: PreprocessorName)
  | PPUnary(operator: TokenType, operand: CanonicalPreprocessorExpression)
  | PPBinary(operator: TokenType,
             left: CanonicalPreprocessorExpression,
             right: CanonicalPreprocessorExpression)

PreprocessorStateChangeRewrite = {
    transition: PreprocessorTransitionId
}

MacroExpansionContext = {
    environment: preprocessor::EnvironmentId,
    busyInvocations: NodeList<
        NonTerminalNodeId<PreprocessorStructured, MacroInvocation>>,
    currentInput: PreprocessorInputFrame,
    languageRules: LanguageRuleSetId,
    lineDirectives: NodeList<SourceLineDirective>
}

MacroExpansionContextId = ContentId<MacroExpansionContext>

MacroExpansionKey = {
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    definition: MacroDefinitionRef,
    context: MacroExpansionContextId
}

MacroExpansionId = ContentId<MacroExpansionKey>

MacroDefinitionOpInput =
    RawSpan {
        expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroRawSpan>
    }
  | ExpandedParam {
        expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroParamReference>,
        argument: NonTerminalNodeId<PreprocessorStructured, MacroInvocationArg>,
        prescannedInputs: NodeList<CSTRewriteOperand>
    }
  | UnexpandedParam {
        expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroParamReference>,
        argument: NonTerminalNodeId<PreprocessorStructured, MacroInvocationArg>
    }
  | StringizedParam {
        expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroStringize>,
        argument: NonTerminalNodeId<PreprocessorStructured, MacroInvocationArg>
    }
  | TokenPaste {
        expandedFrom: NonTerminalNodeId<PreprocessorStructured, TokenPaste>,
        left: Option<CSTRewriteOperand>,
        right: Option<CSTRewriteOperand>,
        concatenatedSpelling: Text,
        resultCount: UInt32
    }
  | BuiltinLine {
        evaluationAnchor: TerminalNodeId<PreprocessorStructured>
    }
  | BuiltinFile {
        evaluationAnchor: TerminalNodeId<PreprocessorStructured>
    }

MacroDefinitionOpRewrite = {
    expansion: MacroExpansionId,
    definitionOp: MacroDefinition::Op,
    input: MacroDefinitionOpInput
}

MacroExpansionDecision =
    Expanded
  | Suppressed(reason: MacroSuppressionReason)
  | Failed(error: ErrorId)

MacroSuppressionReason =
    BusyMacro(blockingInvocation:
        NonTerminalNodeId<PreprocessorStructured, MacroInvocation>)

MacroInvocationResultReplayRewrite = {
    expansion: MacroExpansionId,
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    decision: MacroExpansionDecision where decision is Suppressed | Failed,
    inputs: NonEmpty<CSTTokenRewriteInput>
}

MacroInvocationExpansionRewrite = {
    expansion: MacroExpansionId,
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    definition: MacroDefinitionRef,
    decision: MacroExpansionDecision,
    operations: NodeList<CSTRewriteId>,
    resultOutputs: NodeList<CSTRewriteOutput>
}

IncludeSystem::Mode = Quote | System

IncludeRequest = {
    path: Utf8String,
    mode: IncludeSystem::Mode
}

FileSystemRevisionId = ContentId<SchemaValue>

IncludeSystemConfiguration = {
    searchDirectories: NodeList<Utf8String>,
    fileSystemRevision: FileSystemRevisionId,
    pathRules: LanguageRuleSetId
}

IncludeSystemRevision = ContentId<IncludeSystemConfiguration>

includeSystemRevision(IncludeSystem) -> IncludeSystemRevision

ResolvedInclude = {
    uniqueIdentity: IncludeUniqueIdentity,
    foundPath: Utf8String,
    sourceView: SourceViewId,
    source: SourceFileSnapshotId
}

ResolveInclude(IncludeSystem, IncludeSystemRevision,
               includingView: SourceViewId, request: IncludeRequest)
    -> CheckResult<ResolvedInclude>

IncludeExpansionDecision =
    Traversed(includedRoot: NonTerminalNodeId<MacroExpanded, PreprocessorUnit>)
  | Suppressed(reason: IncludeSuppressionReason)
  | Failed(stage: IncludeFailureStage, error: ErrorId)

IncludeFailureStage = Resolve | Load | Decode | Cycle | ResourceLimit

IncludeSuppressionReason = PragmaOnce(uniqueIdentity: IncludeUniqueIdentity)

IncludeExpansionRewrite = {
    directive: NonTerminalNodeId<PreprocessorStructured, IncludeDirective>,
    requestInputs: NodeList<CSTRewriteOperand>,
    request: IncludeRequest,
    resolved: Option<ResolvedInclude>,
    decision: IncludeExpansionDecision,
    includedInputs: NodeList<TerminalNodeId<MacroExpanded>>
}

PreprocessorStep =
    Atomic {
        transition: PreprocessorTransitionId,
        action: AtomicPreprocessorActionRewriteId
    }
  | Scoped {
        action: ScopedPreprocessorActionRewriteId,
        enter: PreprocessorTransitionId,
        nested: NodeList<PreprocessorStep>,
        leave: PreprocessorTransitionId
    }

TokenSplitRewrite = {
    input: TerminalNodeId<MacroExpanded>,
    parent: TokenRef,
    slices: NonEmpty<TokenSliceId>
}
```

`MacroDefinition::Op` is identified by its definition CST node and operation ordinal. The compiled
operation must agree with the replacement fields that supplied its operator and parameter
occurrences. `ExpandedParam` consumes the prescanned argument expansion; `UnexpandedParam` consumes
the written argument terminals. `StringizedParam` retains the complete argument non-terminal,
including trivia. `TokenPaste` retains its exact `##` terminal and both optional boundary inputs.

Legal opcode/operand pairs are exactly: `RawSpan/RawSpanNode`;
`ExpandedParam/ParameterNode`; `UnexpandedParam/ParameterNode`;
`StringizedParam/StringizeNode`; `TokenPaste/PasteNode`; and
`BuiltinLine/BuiltinOperand` or `BuiltinFile/BuiltinOperand`. Parameter and operation ordinals are
contiguous within their definition. A source definition's values are uniquely derived from its
named CST fields; a builtin definition has no fabricated source node and uses its registered rule.
`MacroDefinitionOpRewrite.input` has the same tag as `definitionOp.opcode`; it names the exact
replacement non-terminal, argument, and any prior output consumed by that opcode. One rewrite is
created per `MacroDefinition::Op`, so a `RawSpan` may have several output ordinals without being
misdescribed as several source operations.

`rewriteInputs(ExpandMacroDefinitionOp(r))` begins with
`resolve(r.expansion).invocation`, then enumerates any source-definition/operation node, argument,
replacement node, and prior output named by `r.definitionOp`/`r.input` in descriptor order. A
builtin definition contributes its registered rule as a semantic projection rather than a fake CST
edge. `resolve(r.expansion).context` is a `Semantic` state field, not recursive provenance. Thus the
origin of every opcode output mechanically reaches the exact invocation and replacement structure
without treating the later aggregate node as its producer.

`MacroInvocationExpansionRewrite.operations` lists every already-published opcode,
nested-expansion, recovery, and result-replay rewrite in execution order, including zero-output
operations.
`resultOutputs` lists only the final structural sequence after consumed intermediate paste/prescan
outputs have been removed. Every result output belongs to an operation in that list or the declared
transitive result of a listed nested expansion, and the list is topologically ordered by rewrite
dependencies. The aggregate rewrite produces the `MacroExpansion`,
`SuppressedExpansion`, or `FailedExpansion` non-terminal; it does not claim to have produced the
listed child tokens/nodes. The node's `result` is a read-only resolution of `resultOutputs`.
Every opcode rewrite and the aggregate record share `MacroExpansionId`, whose key contains the
invocation, definition, and minimal expansion context and can be published before any result. This lets a token
trace reach the aggregate expansion identity without a forward rewrite edge.

An `Expanded` decision has no `ReplayMacroInvocationResult` operation. A `Suppressed` or `Failed`
decision has exactly one such operation for the same expansion, invocation, and decision. Its
`inputs` are the nonempty source-order subsequence of that invocation's token-terminal projection
which the decision retains verbatim, always including the unexpanded macro name and excluding
trivia terminals. Each replay output wraps the exact input `Token` value and therefore retains its
`TokenOrigin`; only the new terminal has the replay rewrite output as its origin. Every verbatim
invocation token in `resultOutputs` must be one of those replay outputs. Nested argument/rescan or
recovery outputs may be interleaved only when their producing rewrites occur in `operations`, and
the combined `resultOutputs` order must equal the replayable rescan trace. Thus busy suppression and
recovered failure cannot silently drop or anonymously reintroduce spelling, while another macro
inside a suppressed invocation can still expand normally.

`PreprocessorExpansionResult.initialState` is the content ID of the query's state argument, and
`finalState` resolves to the returned state. `steps` is the replayable state trace. An `Atomic` action operation
names the same transition stored by the step; applying its typed `effect` to `before` must produce
exactly `after`. A `Scoped` macro/include step first applies `enter`, replays `nested` from
`enter.after` to `leave.before`, then applies `leave`. The enter/leave effects must be the matching
`PushBusyInvocation`/`PopBusyInvocation` or `PushInputFile`/`PopInputFile` pair for the scoped action.
At each list level, the first step starts at the enclosing input state, consecutive step endpoints
are equal, and the last ends at the enclosing output state; an empty list requires those states to
be equal. On scoped return, the caller's input, conditional, and busy stack shapes are restored;
only the environment, `pragmaOnceUniqueIdentities`, loaded source versions, and declared
directive-state effects may flow outward. Recognition is a state-neutral transition
(`before = after`) whose definition must be the lookup result in that state. Inactive definitions
have no `DefineBinding` transition.

A conditional-selection directive requires `ConditionalDirectiveEvaluation`; its
`expandedInputs` are the exact macro-rewrite outputs/source terminals consumed by the expression,
and reparsing/evaluating those inputs under `before` must reproduce `expression`, `value`, and the
selected branch effect. An active `#line` requires `LineDirectiveEvaluation`; applying its expanded
operands must reproduce the stored `SourceLineDirective` and `ApplyLineDirective` state effect.
Other directives have `evaluation=None`. Likewise an include's
`requestInputs` are the exact expanded operand sequence, and decoding that sequence under
`IncludeSystem::Mode` must reproduce `request`. Flattened path text or a final Boolean never replaces
the rewrite inputs that computed it.

For a scoped macro step, `MacroExpansionKey.context` equals the declared projection of
`enter.before` containing only the environment, busy chain, current input, language rules, and that
input view's line-directive list observed by `BuiltinLine`/`BuiltinFile`.
Unrelated pragma-once or loaded-source history cannot perturb macro/token identity. `enter` pushes
that invocation onto `busyInvocations` before nested prescan/rescan steps. `BusyMacro(blocker)` is valid
only when `blocker` is the nearest active invocation of the selected definition in the current
state. The matching `leave` pops the same invocation even on recovered failure, so recursion cannot
become scheduler-global mutable state.

Every output token has provenance rooted in the same rewrite graph:

```text
TokenOrigin =
    SourceTokenOrigin(source: SourceRange)
  | CSTRewriteTokenOrigin(output: CSTRewriteOutput)
```

For a macro-produced token, `CSTRewriteTokenOrigin.output.rewrite` is the operation that created
it, and `output.ordinal` is its zero-based position among that operation's token results. The
`TokenTerminalBundle` terminal created with that token has the same `RewriteOutput` origin; a later
stage bridge has its own `PreserveTerminal` origin while retaining the token's origin. No token points forward to
its containing expansion node; both token and node point backward to the already-published rewrite
record. This gives tokens, terminal nodes, and expansion non-terminals one provenance authority
without introducing a token-list/snapshot identity cycle.

Raw, parameter-copy, and include-copy rewrites may retain a direct physical spelling only when they
copy one contiguous input spelling together with its continuation metadata. Stringize, paste,
builtin, and synthesized results have `physicalSpelling=None`. Paste results are exactly the ordered output of
the chapter 2 `LexPasteSequence` operation; `resultCount`, output ordinals, token types, and
spellings must agree with re-lexing `concatenatedSpelling`.

A parsed `TokenSliceTerminal` is produced only by `SplitToken`. The rewrite's `input` must wrap
`parent`; its ordered slice ranges are nonempty, disjoint, and partition the authorized logical
spelling range. Each slice terminal's origin is the matching rewrite-output ordinal. A
`ParseProduction` consumes those terminals but is not misrepresented as the operation that split
their token.

Include expansion is the same operation at a larger granularity. Each successful include use has a
distinct `SourceView` and lexed/structured/expanded snapshot chain. The including expansion node
refers to both the written `IncludeDirective` and the included expanded root. Suppressed and failed
include occurrences remain explicit non-terminals and fabricate neither a child snapshot nor
tokens. Recursive traversal closes with `PragmaOnce` suppression or a `Failed(Cycle | ResourceLimit)`
result, so included-root rewrite edges are acyclic.

The `IncludeSystem` argument exposes a content-addressed `IncludeSystemRevision`; `ResolveInclude`
is deterministic for that revision and is the only file-resolution/loading capability used by the
query. A unit test may supply a mock with the same interface. A traversed
`IncludeExpansionRewrite.includedInputs` is exactly the included root's ordered active terminal
projection after applying `IsNotEndOfFile`; the included snapshot retains its own EOF, and no child
EOF is copied into the including list. For a token input, the corresponding `tokenResult` output is
a `TokenTerminalBundle` copying its token type, `logicalSpelling`, physical spelling, and
continuation metadata while replacing only its origin with the include rewrite output. For a trivia
input, the corresponding `triviaResult` terminal copies the immutable trivia value, and its terminal
origin records the include rewrite. `includeResultOutputs` preserves their original interleaving.
Literal decoding remains the separate `DecodeLiteral` query and is not copied as unstated token
storage. `Traversed` and `PragmaOnce` require
`resolved=Some`; only `Traversed` permits nonempty `includedInputs`. A `Resolve` failure requires
`resolved=None`; later failure stages retain `Some` and an empty input list. Suppressed and failed
decisions have no copied-token outputs. Cyclic inclusion is `Failed(Cycle, error)`; an
ordinary source include guard is represented by conditional activity, not an invented include
suppression reason. `PragmaOnce` alone uses the explicit unique-identity state.

`ActiveTokenView(snapshot)` is the derived
`TokenListView(snapshot.primaryList,
And([IsToken, IsActive(snapshot.activityMaps[snapshot.primaryList])]))` for a `MacroExpanded`
snapshot. It is a `TokenListView`, not an owning expansion object. Its order equals
the ordered terminal results reachable from the root. Inactive regions remain reachable through
predecessor CST fields but are absent from this active projection.

`IncludedContentView(snapshot)` is
`TokenListView(snapshot.primaryList,
And([IsActive(snapshot.activityMaps[snapshot.primaryList]), IsNotEndOfFile]))`. Unlike
`ActiveTokenView`, it retains active trivia and excludes the child EOF. A traversed include's
`includedInputs` is exactly the ordered terminal projection of this view.

### Provenance queries

```text
physicalSpellingSources(TokenOriginId) -> Option<SourceRangeSet>
directSpellingRange(TokenRef) -> Option<SourceRange>
includeTrace(TokenOriginId) -> NodeList<
    NonTerminalNodeId<PreprocessorStructured, IncludeDirective>>
macroInvocationTrace(TokenOriginId) -> NodeList<
    NonTerminalNodeId<PreprocessorStructured, MacroInvocation>>
macroDefinitionSources(TokenOriginId) -> Option<SourceRangeSet>
primaryDiagnosticAnchor(TokenOriginId) -> Option<SourceRange>
fullTokenTrace(TokenOriginId) -> CSTProvenanceTrace

CSTProvenanceTrace = {
    root: TokenOriginId,
    rewrites: NodeMap<CSTRewriteId, CSTRewrite>,
    sourceLeaves: CanonicallyOrderedSet<SourceRange>
}
```

`fullTokenTrace` is the transitive closure of the root origin through `rewriteInputs`, preserving
every named edge and shared predecessor. Traversal is deterministic depth-first preorder in schema
field order with first-visit deduplication. `physicalSpellingSources` collects source leaves in that
order. `macroInvocationTrace` selects invocation inputs from macro rewrite records;
`includeTrace` selects include-directive inputs. `macroDefinitionSources` selects definition token,
operator, and parameter-occurrence leaves.

`directSpellingRange(token)` is present exactly when `token.physicalSpelling` is present; the range
selected through provenance must spell the same decoded bytes. The primary diagnostic anchor for a
macro result is the name terminal of the outermost invocation reached by the trace. If there is no
macro invocation it is the first physical source leaf, or `None` when the rewrite is wholly
synthesized. Selecting a primary anchor never removes nested invocation, argument, definition,
stringize, paste, or include notes from `fullTokenTrace`.

`REP-CST-002`: Every rewrite input resolves, satisfies its declared role and stage, and is a strict
predecessor under the snapshot/rewrite topological order. The transitive rewrite relation is finite
and acyclic. Copying or serializing a token preserves its `TokenOriginId`; traversal never depends
on pointer identity, scheduler order, or diagnostic rendering.

`REP-CST-003`: For every macro, paste, and include outcome node, schema-visible predecessor and
projection fields equal the corresponding typed rewrite fields. A `MacroExpansion` result resolves
exactly `MacroInvocationExpansionRewrite.resultOutputs`, whose producers are the earlier opcode,
nested-expansion, recovery, or explicit result-replay rewrites; only the aggregate non-terminal is an output of the
aggregate rewrite. Paste/include result terminals are the matching declared output port of their
own rewrite. Validators re-run stringize, paste, parameter selection, state-transition, and include
copy equations from predecessor CST rather than trusting cached metadata.

### Grammar parsing

```text
Parse(CSTSnapshot<MacroExpanded>, GrammarVocabulary, SyntaxParseInfoSet, ParserOptions)
    -> CheckResult<CSTSnapshot<Parsed>>
```

Each grammar production produces one typed non-terminal with named fields. Each field points to a
terminal or non-terminal in the parsed snapshot; the node's `ParseProduction` rewrite points back
to the exact macro-expanded terminals/non-terminals consumed by the production, or records an
`Empty` directional anchor when it consumes nothing. Delimiters and
separators remain first-class terminal fields even when the later AST does not retain them.

Parser recovery also produces concrete structure:

```text
SkippedTokensFields = {
    tokens: structuralRewriteProjection<NonEmpty<TerminalNodeId<Parsed>>>,
    recoveryRule: rewriteProjection<RuleId>
}

UnexpectedConstructFields = {
    actual: structuralRewriteProjection<NonTerminalNodeId<Parsed>>,
    expectedCategory: rewriteProjection<QualifiedName>,
    recoveryRule: rewriteProjection<RuleId>
}
```

A missing terminal is the `MissingTerminal` alternative, not a non-terminal payload and not a
mutated real token. `RecoverMissing`, `RecoverSkipped`, and `RecoverUnexpected`, together with the
enclosing `CSTRewrite.rule`, are the sole authorities for the fields above; generated descriptors
resolve them as read-only projections. `RecoverMissing.anchor` retains `Before` versus `After` as
part of rewrite identity; `EndOfInput` and `SourceAnchor` are distinct zero-width positions rather
than aliases for the last real terminal. Skipped terminals remain under the smallest enclosing
recovery non-terminal. An unexpected construct retains the complete actual non-terminal.

Ambiguous syntax is a typed packed-CST node. Its alternatives are typed non-terminal references
whose named fields may share the same terminal nodes; the alternatives are excluded from the
primary concrete-order projection so sharing cannot duplicate formatting output. The ambiguity
node's primary fields own the token coverage exactly once, and its alternative fields expose each
candidate shape to binding.

`REP-CST-004`: Every terminal occurrence selected by the active macro-expanded view appears exactly
once in the parsed root's primary terminal projection, either as a whole-token terminal or as a
complete ordered set of token-slice terminals. Alternative ambiguity edges do not contribute a
second occurrence. A real terminal is never dropped, retyped, or used as a fabricated missing
terminal.

`REP-CST-005`: The generated schema defines a unique source-order position for every structural
terminal/non-terminal occurrence within its product, variant, and repetition element. For each
non-terminal, `cstOperands(node)` equals the source-order traversal of its active shape value.
Punctuation cannot be omitted merely because it has no semantic AST meaning.

`REP-CST-006`: Primary structural fields reachable from a snapshot root form a finite rooted tree:
the root has no structural parent and every other primary occurrence has exactly one. Packed
ambiguity alternatives use the distinct `Alternative` edge category and may share primary
terminals; predecessor references use `Provenance`. Neither alternative nor provenance edges can
create a primary parent or a structural cycle. Two equal primary occurrences have distinct local
indices even when their immutable record storage is hash-consed; `withCSTField` therefore edits one
field-path occurrence. Only explicitly non-primary alternative edges may share an existing primary
terminal ID.

`REP-CST-007`: Descriptor lookup of `CSTOriginField` succeeds exactly once for every terminal and
non-terminal and returns its typed `CSTNodeOrigin`. A terminal descriptor likewise exposes exactly
one `CSTTerminalValueField`; its `NodeKind` is the unique `terminalKind` admitted for the terminal's
stage and value class. Serialization, generic copying, and functional editing cannot omit or
disagree with the kind, value, or origin.

`REP-CST-008`: A `MacroExpanded` snapshot's `primaryList` is in bijection with the token/trivia
terminal projection of its root: each list element has exactly one primary terminal referring to
that exact `(list, index)`, in the same order, and every such terminal appears in the projection.
Its `TokenActivityMap` is total over that list. `PreprocessorStructured` retains the predecessor
`TokenList` as its `primaryList` but need not wrap trivia that has no syntactic role in a second
terminal occurrence; those elements remain reachable through the `Lexed` predecessor, token
adjacency, and exact `TokenListRange` fields. `Parsed` reuses the macro-expanded lists and may split
a token only through `TokenSlice`, never by creating a competing owning token sequence.

### CST-to-AST translation

The complete representation pipeline is therefore:

```text
SourceView
  -> TokenList
  -> CSTSnapshot<Lexed>
  -> initial CSTSnapshot<PreprocessorStructured>
  -> ordered PreprocessorStep values and invocation fragments
  -> PreprocessorExpansionResult { CSTSnapshot<MacroExpanded>, final state }
  -> CSTSnapshot<Parsed>
  -> ASTSnapshot<Surface>
  -> ASTSnapshot<Scoped>
  -> ASTSnapshot<Bound>
  -> ASTSnapshot<Typed>
  -> ASTSnapshot<Elaborated>
  -> ASTSnapshot<IRReady>
```

Every arrow is a pure query from immutable inputs to a new immutable representation. CST rewrites
name predecessor CST nodes; AST origins name parsed CST nodes or previous-stage AST nodes. Identity
formatting starts from the `Lexed` or `PreprocessorStructured` predecessor rather than relying on a
parallel source tree. Macro-expanded and parsed snapshots remain navigable back to written macro
calls, definitions, paste operators, includes, inactive regions, tokens, trivia, and physical
source bytes through the same rewrite graph.

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
RepresentationStage = Concrete(CSTStage) | Abstract(Stage) | SemanticStage
StageSet = BitSet<RepresentationStage>

FieldName = {
    text: Utf8Identifier,
    wireTag: UInt32
}

NodeKind = {
    family: TerminalNode | NonTerminalNode | AST | Semantic,
    wireTag: UInt32,
    stableName: QualifiedName
}

ASTNodeType<S> = {
    k: NodeKind |
        k.family = AST and
        k in currentNodeSchemaRegistry.stageKinds[Abstract(S)]
}
NonTerminalKind<S> = {
    k: NodeKind |
        k.family = NonTerminalNode and
        k in currentNodeSchemaRegistry.stageKinds[Concrete(S)]
}
NodeFields<S> = CanonicallyOrderedMap<FieldName, FieldValue>

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

CSTRewriteProjectionSource = RewriteInputProjection
                           | RewriteValueProjection
                           | RewriteOutputBindingProjection

CSTRewriteProjectionDescriptor = {
    operationKind: QualifiedName,
    operationPath: NonEmpty<FieldName>,
    source: CSTRewriteProjectionSource,
    rule: RuleId
}

CSTShapeProjectionDescriptor = {
    production: ProductionId,
    field: FieldName,
    rule: RuleId
}

FieldWirePolicy = SerializedField
                | DerivedField(rule: RuleId, inputs: NonEmpty<FieldName>)
                | CSTShapeProjectedField(CSTShapeProjectionDescriptor)
                | CSTRewriteProjectedField(CSTRewriteProjectionDescriptor)

FieldAccess = Editable | ReadOnly

FieldDescriptor = {
    name: FieldName,
    valueKind: FieldValueKind,
    edge: Structural | Alternative | Semantic | Provenance,
    stages: StageSet,
    wire: FieldWirePolicy,
    access: FieldAccess
}

NodeDescriptor = {
    kind: NodeKind,
    baseKind: Option<NodeKind>,
    fields: NodeList<FieldDescriptor>,
    invariants: NodeList<RuleId>
}

CSTRewriteOperationDescriptor = {
    kind: QualifiedName,
    inputs: NodeList<FieldDescriptor>,
    outputRule: RuleId,
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

OriginUpdateRule = PreserveExplicitOrigin
                 | DeriveOrigin(rule: RuleId)
                 | ReplaceOrigin(origin: Origin)

ProductionId = {
    grammarVersion: SchemaVersion,
    qualifiedName: QualifiedName
}

CSTCategoryDescriptor = {
    category: CSTCategoryId,
    kind: NodeKind where kind.family = NonTerminalNode,
    members: CanonicallyOrderedSet<ProductionId>
}

NonTerminalKind<Lexed> = TokenizedSource

NonTerminalKind<PreprocessorStructured> =
    PreprocessorUnit | PreprocessorFragment | TextRegion | DefineDirective | MacroDefinition |
    MacroDefinitionParameterClause | MacroDefinitionParameterTail | MacroDefinitionParam |
    MacroInvocation | MacroInvocationArgumentClause | MacroInvocationArgumentTail |
    MacroInvocationArg | MacroRawSpan | MacroParamReference |
    MacroStringize | TokenPaste | IncludeDirective | ConditionalGroup |
    DiagnosticDirective | LineDirective | PragmaDirective | LanguageDirective |
    UndefDirective | UnknownDirective | PreprocessorRecovery |
    RegisteredPreprocessorKind(NodeKind)

NonTerminalKind<MacroExpanded> =
    PreprocessorUnit | MacroExpansion | TokenPasteExpansion | IncludeExpansion |
    SuppressedExpansion | FailedExpansion | SuppressedIncludeExpansion |
    FailedIncludeExpansion | ExpandedRecovery |
    RegisteredExpansionKind(NodeKind)

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
    cstRewriteOperations:
        CanonicallyOrderedMap<QualifiedName, CSTRewriteOperationDescriptor>,
    cstCategories:
        CanonicallyOrderedMap<CSTCategoryId, CSTCategoryDescriptor>,
    grammarProductions: CanonicallyOrderedMap<ProductionId, NodeKind>,
    cstProductionDescriptors:
        CanonicallyOrderedMap<ProductionId, CSTProductionDescriptor>,
    stageKinds: NodeMap<RepresentationStage, CanonicallyOrderedSet<NodeKind>>,
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
and base-kind role are validated, but they occur in no `stageKinds` set and have no constructor.
Only concrete production and terminal kinds occur in `stageKinds[Concrete(stage)]`. This keeps an
accepted-kind constraint distinct from a constructible `NonTerminalKind<S>` or
`TerminalNodeKind<S>`.

Every named production in `grammar.ebnf` has exactly one `ProductionId`, `grammarProductions`
entry, and `cstProductionDescriptors` entry. A production descriptor names every terminal and
non-terminal role, including punctuation, and its closed shape states how those roles compose. A
terminal is a leaf and the role is a named field on its containing non-terminal; neither fact
substitutes for the other. A `CSTCategoryDescriptor` is an abstract accepted-kind constraint whose
members are productions; it is not itself a constructible syntax occurrence. Recovery and
ambiguity use the dedicated closed kinds above. Every `ASTNodeType<S>` and semantic value
constructor likewise has exactly one descriptor. Stable names are diagnostic labels;
`(family, wireTag)` is the wire discriminator, and wire tags are never reused after publication.

Every `(CSTStage, NonTerminalKind)` pair has one `cstConstructors` entry naming all rules permitted
to produce it. A rule that creates a node absent from that entry, or a registered kind with no
constructor, fails schema generation.

`terminalKinds[(stage, class)]` is total exactly for the terminal classes admitted by
`TerminalValue<stage>`, and its values are unique within a stage. `terminalKind` is this lookup;
`terminalClass` is its generated inverse after validating that the referenced
`NodeDescriptor.kind.family` is `TerminalNode` and its kind occurs in
`stageKinds[Concrete(stage)]`. Thus terminal record validation depends only on serialized registry
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
`NodeFields` has exactly the descriptor's field-name domain at the node's stage. For a parsed
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
authority. A `CSTRewriteProjectedField` is permitted only on a CST node with `RewriteOutput`
origin. Its descriptor names the exact operation kind/path and whether reconstruction reads a
rewrite input,
an immutable operation value, or `CSTSnapshot.outputBindings`; the implicit dependencies are the
node's `CSTOriginField`, the content-identified rewrite, and, only for an output-binding projection,
the snapshot's serialized binding map. The operation must match and the projection must be total
and kind-correct. The result is then compared with the normal node validator. A field with no
serialized bytes and no derivation/projection policy is forbidden, and other
provenance/structural semantic fields default to `SerializedField`. Thus every exact `NodeFields`
entry is reconstructed before a node is published.

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
schemaOrigin(node) -> CSTOrigin(CSTNodeOrigin) | ASTOrigin(Origin) | NoSchemaOrigin
origin(node: SyntaxNodeRef) -> Origin
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

The parsed-production portion is generated exhaustively from `grammar.ebnf` and
`cst-production-profile.json`; the paired-schema validator proves that every grammar leaf has a
named typed field and grouped cardinality. Preprocessor transformation nodes, AST stages, and
semantic values still require exhaustive registry instances before implementation begins. That
remaining scope is tracked as a blocking specification item in chapter 12, not silently treated as
an implementation detail.

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
