# Lexical and syntactic specification

This chapter specifies the lossless syntax boundary and the parser's contract. The companion
[`grammar.ebnf`](grammar.ebnf) is a structural EBNF baseline for the full surface grammar. It is
derived from official source at `4f4ec505761e2e56a45da873d5c169ff6e512f52` and corrects known
errors in the older generated grammar.
Its productions and island predicates are mechanically readable; exhaustive `@recover`,
`@version`, and `@dialect` annotations remain an explicitly blocking grammar-freeze item in
chapter 12 rather than an implicit parser-generator default.

The grammar is not allowed to call the type checker. Where compatibility syntax is genuinely
ambiguous, the parser produces a named ambiguous CST node and binding resolves it later.

## Inputs and outputs

```text
Lex(SourceView, LexOptions)
    -> CheckResult<TokenList>

BuildLexedCST(TokenList)
    -> CSTSnapshot<Lexed>

StructurePreprocessor(CSTSnapshot<Lexed>, PreprocessorOptions)
    -> CheckResult<CSTSnapshot<PreprocessorStructured>>

ExpandPreprocessor(CSTSnapshot<PreprocessorStructured>, IncludeSystem,
                   PreprocessorState, PreprocessorOptions)
    -> CheckResult<PreprocessorExpansionResult>

Parse(CSTSnapshot<MacroExpanded>, GrammarVocabulary, SyntaxParseInfoSet, ParserOptions)
    -> CheckResult<CSTSnapshot<Parsed>>

LexOptions = {
    languageRules: LanguageRuleSetId,
    recognizeLineContinuations: Bool,
    preserveInvalidTokens: True
}

PreprocessorOptions = {
    languageRules: LanguageRuleSetId,
    retainInactiveRegions: True,
    expansionDepthLimit: UInt32,
    expandedTokenLimit: UInt64,
    includeDepthLimit: UInt32
}

GrammarWordId = QualifiedName

GrammarWord = {
    id: GrammarWordId,
    spelling: Utf8String,
    role: FixedGrammarWord | ContextualGrammarWord,
    rule: RuleId
}

GrammarVocabulary = {
    languageRules: LanguageRuleSetId,
    words: CanonicallyOrderedMap<GrammarWordId, GrammarWord>,
    revision: ContentId<SchemaValue>
}

SyntaxParseInfoId = QualifiedName
SyntaxClassId = QualifiedName

SerializedSyntaxParseInfo = {
    id: SyntaxParseInfoId,
    spelling: Utf8String,
    production: ProductionId,
    syntaxClass: SyntaxClassId,
    rule: RuleId
}

SyntaxParseInfoSet = {
    languageRules: LanguageRuleSetId,
    entries: CanonicallyOrderedMap<SyntaxParseInfoId, SerializedSyntaxParseInfo>,
    revision: ContentId<SchemaValue>
}

ParserOptions = {
    preserveAmbiguities: Bool,
    parseInactiveRegionsSpeculatively: Bool,
    recoveryActionLimit: UInt32,
    ambiguityAlternativeLimit: UInt32,
    nestingDepthLimit: UInt32
}
```

`PreprocessorOptions` is intentionally not the current pointer-bearing `PreprocessorDesc`.
`PreprocessorDesc` remains the public adapter that assembles the pure query: `sink` receives the
returned diagnostics; `namePool` is replaced by content-identified `PreprocessorName` interning;
`fileSystem`/`sourceManager`/`includeSystem` become the versioned `IncludeSystem`; `defines` build the
initial `preprocessor::Environment`; and handler/content-assist callbacks observe the published
rewrite trace rather than participating in semantics.

The formal `ParserOptions` is the normalized parser-only projection of the existing same-named
record. Current `enableEffectAnnotations` and `allowGLSLInput` contribute to `LanguageRuleSetId`;
`isInLanguageServer` contributes to an explicit diagnostic/recovery policy; `ParsingStage` selects
the parse query; and `CompilerOptionSet` is part of `EnvironmentRevision`. The remaining resource
and ambiguity controls above are serialized query inputs. No current field is silently discarded or
read ambiently.

Each function is independently unit-testable from immutable inputs. `Lex` does not require a name
pool or compiler session. Its product remains exactly the plain `TokenList` of `Token | Trivia`
values and does not acquire producer metadata. `BuildLexedCST` mechanically creates one terminal
per list element under a single `TokenizedSource` non-terminal; it does not copy those elements.
`StructurePreprocessor` recognizes directives, definitions, replacement-list operations,
conditionals, and text regions without consulting a macro environment. `ExpandPreprocessor` scans
those regions in source order, recognizes a `MacroInvocation` only against its current immutable
`PreprocessorState`, and replaces invocation/include occurrences in new snapshots with typed
predecessor edges. This scan/recognize/expand loop is also used for macro-produced and included
token streams, so a definition introduced by an include is visible to following parent-file text.
Included files inherit the same `LexOptions`, and all preprocessing queries require matching
`languageRules`. `Parse` consumes the active terminal projection of the returned
`PreprocessorExpansionResult.snapshot` and does not receive a semantic visitor, declaration table,
or mutable scope.

All option/vocabulary/parse-info fields and `includeSystemRevision(IncludeSystem)` participate in
the corresponding query key. Both registry revisions resolve to and verify their exact canonical
entry bytes under chapter 1's `ContentId` rule; neither is
a bare hash. Resource limits are deterministic semantic recovery inputs, never wall-clock budgets.
The literal `True` fields state required losslessness rather than caller-selectable modes.

## Source decoding and physical fidelity

The current compiler decodes input and strips a BOM before allocating source locations, so current
offsets refer to decoded UTF-8 rather than original file bytes. The replacement stores both views
when decoding is required. `SourceFileRecord` and `SourceView` have their single authoritative
schemas in chapter 3; the lexer consumes the exact view and resolves its physical/decoded file pair.

`LEX-SRC-001`: Diagnostics and grammar operate on decoded UTF-8 byte offsets. Identity formatting
of an unmodified document writes `physicalBytes`; formatting an edited document writes UTF-8 unless
the caller selects a supported output encoding.

`LEX-SRC-002`: Invalid encoding sequences produce explicit decoding-error spans and replacement
scalar values in the decoded snapshot; no source bytes disappear from `SourceFileRecord`.

This closes the “byte-exact versus decoded-text-exact” item in the compatibility ledger while
preserving today's semantic offset domain.

## Token vocabulary

The fixed lexical discriminator vocabulary is:

```text
Token.type special:    Unknown EndOfFile Invalid
Token.type content:    Identifier IntegerLiteral FloatingPointLiteral StringLiteral CharLiteral
Token.type separators: ; , . .. ... { } [ ] ( ) ? : @ $ $$ # ## :: #?
Token.type operators:  = + - * / % ! ~ << >> == != > < >= <= && || & | ^ ++ --
Token.type compound:   += -= *= /= %= <<= >>= &= |= ^= -> =>
Trivia.type:           WhiteSpace NewLine LineComment BlockComment LineContinuation
```

The lexer emits the one flat `TokenList = NodeList<Token | Trivia>` from chapter 3. The established
`TokenType` values `WhiteSpace`, `NewLine`, `LineComment`, and `BlockComment`, plus the explicit
`LineContinuation` value, discriminate `Trivia` alternatives in the replacement schema rather than
ordinary `Token` alternatives. This principled split lets every view share one lossless sequence.
Documentation comments set `Trivia.isDocumentation`. `Unknown` is an
internal sentinel; `Invalid` is a source token with physical spelling and a diagnostic.

`LineContinuation` is the `TokenType` of an independently emitted trivia element. A
backslash-newline absorbed while recognizing one token is instead a line-continuation splice in
that token's spelling map; it is not a hidden `Trivia` value.

All language words are initially `Identifier` tokens. The parser recognizes fixed and contextual
spellings through `GrammarVocabulary`; callback/source-declared syntax is separately provided by
`SyntaxParseInfoSet`. Builtin type and function names remain ordinary declarations
in the standard environment.

`LEX-TOK-001`: Longest matching punctuation wins. In a generic closing context, `>>` remains one
`Token` and is exposed to the grammar CST as two zero-copy `TokenSliceId` leaves whose spelling
ranges partition the parent token. The parent token is never mutated.

`LEX-TOK-002`: Every non-EOF token returned by `Lex` stores one contiguous physical spelling and its
logical spelling. Backslash-newline splicing affects the logical spelling only; exact removed
subranges remain in `Token.removedLineContinuations`. The ordered
`Token | Trivia` spellings, not a parallel piece table, partition the source. Removed ranges are
relative to `physicalSpelling`, strictly ordered, disjoint, in bounds, and each spells one accepted
backslash-newline sequence.

## Identifiers

Compatibility lexing accepts an underscore, ASCII letter, or non-ASCII scalar as the first
character, followed by those characters or ASCII digits. This matches the current lexer more
closely than claiming Unicode XID behavior it does not implement.

```text
identifier-start    ::= '_' | ASCII-LETTER | NON-ASCII-SCALAR ;
identifier-continue ::= identifier-start | ASCII-DIGIT ;
identifier          ::= identifier-start { identifier-continue } ;
```

`LEX-ID-001`: Identifier equality is defined on the decoded scalar sequence without Unicode
normalization in compatibility mode. A future modern mode may adopt XID and normalization only as
an intentional language-version change.

## Literals

The lexical grammar distinguishes spelling from semantic validation:

```text
integer-literal ::= decimal-integer integer-suffix?
                  | binary-integer integer-suffix?
                  | hex-integer integer-suffix?
                  | legacy-octal integer-suffix? ;

floating-literal ::= decimal-float float-suffix?
                   | hex-float float-suffix?
                   | '#INF' float-suffix? ;

string-literal ::= ordinary-string | raw-string ;
char-literal   ::= "'" character-or-escape "'" ;
```

Digit separators, exponent forms, escape syntax, raw-string delimiters, recognized suffixes, range
selection, and malformed-literal diagnostics are rule-table data generated from the lexical schema.
Compatibility tokenization accepts an alphanumeric suffix and leaves unsupported-suffix rejection
to literal checking, matching current source behavior.

`LEX-LIT-001`: The token stores exact physical and logical spelling. The pure, memoizable
`DecodeLiteral(TokenRef, LanguageRuleSetId)` query from chapter 6 produces the decoded value or
structured failure, exact radix/format, and suffix spelling; those derived facts are not duplicated
in `Token`. Numeric negation is a prefix expression, not part of the literal token.

`LEX-LIT-002`: Adjacent string literal concatenation is a parser/semantic construct. Each source
literal remains independently addressable with its own spelling and trivia.

## Trivia ownership

Trivia elements occur directly in `TokenList`. Classification rules are:

- horizontal whitespace and other non-newline spacing → `WhiteSpace`;
- each source newline sequence → `NewLine` with exact physical spelling;
- backslash followed by a newline sequence → `LineContinuation`;
- `//` through its terminating newline boundary → `LineComment` plus the separate newline trivia;
- `/* ... */` → `BlockComment`; comments do not nest in compatibility mode; and
- a comment matching a versioned documentation marker retains `LineComment`/`BlockComment` and sets
  `isDocumentation=true`.

A `LineContinuation` between logical tokens is a `Trivia` element. When line splicing joins
characters into one logical token, the continuation instead lies inside that token's contiguous
physical spelling and its relative range occurs in `removedLineContinuations`; it is not duplicated
as a top-level `Trivia`. This is the explicit splice-before-tokenization rule, not a second ownership
representation.

`LEX-TRI-001`: Unterminated block comments produce a `BlockComment` `Trivia` element spanning to EOF
and diagnostic `unterminated-block-comment`. The current lexer has a TODO and often relies on a
later parser error; this is an intentional diagnostic improvement.

Documentation attachment is a semantic view over adjacent list elements:

```text
LeadingDocumentation(declToken) = maximal documentation-comment group in LeadingTrivia(declToken)
                                  not separated by a blank-line boundary
TrailingDocumentation(token) = documentation comment in TrailingTrivia(token)
                               on the same logical line
```

Attachment never moves, copies, or re-owns a `Trivia` element.

## Preprocessor syntax

The `PreprocessorStructured` CST recognizes these directive spellings:

```text
#if #ifdef #ifndef #elif #else #endif
#include #define #undef
#warning #error #line #pragma
#language #lang
#version #extension
```

Known pragmas include `once` and `warning`; unknown pragmas are preserved even when ignored
semantically.

Preprocessor constant expressions have this precedence, from lowest to highest:

```text
||  &&  |  ^  &  == !=  < <= > >=  << >>  + -  * / %  prefix(- ! ~)
```

Atoms are integer literals, parenthesized expressions, `defined`, `__has_feature`, and identifiers
whose replacement is evaluated under preprocessor rules.

```text
PreprocessorElement = TextRegion
                    | IncludeDirective
                    | DefineDirective
                    | UndefDirective
                    | ConditionalGroup
                    | DiagnosticDirective
                    | LineDirective
                    | PragmaDirective
                    | LanguageDirective
                    | MacroInvocation
                    | UnknownDirective
```

`PP-TREE-001`: All directives, macro definitions/invocations, arguments, paste operators,
delimiters, line endings, inactive branches, and text regions have typed non-terminal structure in
one or more topologically ordered `CSTSnapshot<PreprocessorStructured>` values. Initial structuring
is environment-independent; invocation structure is published when the ordered expansion scan can
resolve it. Every grammar token is reached through a named terminal field. A significant trivia
element such as a directive line ending may also be referenced by a named terminal. All such
terminals remain zero-copy references into `TokenList`, which is the sole value owner; other trivia
is reached through adjacency or an exact range, never an anonymous gap field.

`PP-EXP-001`: Every macro-produced `Token` has `CSTRewriteTokenOrigin` naming the exact output of
one `ExpandMacroDefinitionOp` rewrite. Its `MacroDefinition::Op.opcode` is the established
`RawSpan`, `ExpandedParam`, `UnexpandedParam`, `StringizedParam`, `TokenPaste`, `BuiltinLine`, or
`BuiltinFile`, and its dependent input has the same tag. The rewrite has typed inputs for the exact
`MacroInvocation` non-terminal, replacement-operation non-terminal, argument, and any prior
expansion output it consumes. The containing
`MacroExpansion` non-terminal exposes its invocation as `expandedFrom`; a
`TokenPasteExpansion` exposes the exact earlier `TokenPaste` non-terminal. Recursion suppression is
an explicit `SuppressedExpansion` decision, not a missing provenance edge or mutable flag on the
invocation node.

Stringization and paste use executable spelling functions:

```text
stringizePayload(range) =
    trim leading/trailing Trivia;
    replace each remaining maximal nonempty Trivia run with one U+0020;
    concatenate Token.logicalSpelling in order;
    within StringLiteral and CharLiteral spellings, prefix each '\\' and '"' with '\\'

stringize(range) = '"' + stringizePayload(range) + '"'

pasteSpelling(left, right) =
    logicalSpelling(left) if present, else ""
  + logicalSpelling(right) if present, else ""

PasteLexeme = ValidPasteToken(type: TokenType where not isTrivia(type), spelling: Text)
             | InvalidPasteToken(spelling: Text)

pasteTokens(left, right) = LexPasteSequence(pasteSpelling(left, right))
```

Comments, newlines, and line continuations are `Trivia` for whitespace folding; a line continuation
inside a token has already been removed from that token's `logicalSpelling`. The escaping step does
not decode then re-encode a literal. It scans the exact logical spelling bytes of that token.

`PP-EXP-002`: A stringized output is one `StringLiteral` token whose `logicalSpelling` equals
`stringize(argumentSpelling(argumentNode))`, where `argumentSpelling` enumerates every `Token |
Trivia` element in the exact `MacroInvocationArg.writtenRange`. It never reconstructs trivia from
`AfterWhitespace`, a terminal-only projection, or another one-bit flag. The `StringizedParam`
opcode input retains that argument node and the exact `MacroStringize` predecessor containing the `#`
and parameter occurrence.

`LexPasteSequence` is a preprocessing-token lexer, not the lossless source lexer. It emits no EOF or
`Trivia`. A source-lexer spelling that would begin whitespace, a comment, or another trivia form is
one `InvalidPasteToken` covering the offending bytes; for example `/ ## *` produces invalid `/*`,
not `BlockComment` trivia. Materialization turns `ValidPasteToken` into its stated `TokenType` and
`InvalidPasteToken` into an `Invalid` `Token`; both have `physicalSpelling=None` and receive a
`TokenTerminalBundle` output of the current `ExpandMacroDefinitionOp(TokenPaste)` rewrite as their
origin.

`PP-EXP-003`: A token paste uses `pasteTokens`. Zero results are valid exactly when
`pasteSpelling(left, right) == ""`, which requires both operands to be absent. One valid result is a
successful paste. Any invalid result or more than one result emits `invalid-token-paste-result` and
retains the exact materialized sequence for recovery. The `TokenPaste` opcode input records the
exact earlier `TokenPaste` non-terminal, both optional typed input edges, and `pasteSpelling`; a valid re-lexed token keeps its
`TokenType`, while a spelling that is not a preprocessing token uses the explicit `Invalid`
alternative above. Every emitted token has a distinct `CSTRewriteOutput` ordinal of that same
rewrite, and the wrapping `TokenPasteExpansion.result` field contains those terminal nodes in that
order.

`PP-EXP-004`: The primary diagnostic anchor of a macro-derived token is the outermost invocation
name. The complete structured trace retains nested invocation, definition, argument, stringize,
paste, and physical-spelling ranges as diagnostic notes; choosing the primary range discards none
of them.

`PP-INC-001`: Each include use has a distinct `SourceView` and its own
`Lexed -> PreprocessorStructured -> MacroExpanded` CST chain. Repeated uses may share one file
record and decoded snapshot while retaining distinct views. The including `IncludeExpansion`
non-terminal refers both to the written `IncludeDirective` predecessor and the included expanded
root. Each spliced token has a `CSTRewriteTokenOrigin` rooted at that `IncludeExpansion` rewrite, so
two inclusions of the same snapshot retain distinct include paths. Tooling may parse an included
view separately; that creates a distinct `CSTSnapshot<Parsed>` without changing either include
chain.

`PP-INC-002`: Include traversal is a scoped `PreprocessorStep`. It pushes the resolved file's
`PreprocessorInputFrame`, replays the included unit under the caller's current environment, and pops
that exact frame. The included unit's resulting macro bindings, `#undef` tombstones,
`pragmaOnceUniqueIdentities`, loaded source versions, and declared directive state become the state
for following parent-file text; its conditional and busy-invocation stacks cannot leak. A cyclic
identity is a failed include, while an ordinary written include guard is evaluated as conditional
activity rather than a separate suppression mechanism.

## CST production fields

EBNF specifies accepted ordering and repetition; the paired node schema assigns every symbol
occurrence a stable field role and category. A production is incomplete and cannot generate a
parser until both parts exist. The checked-in
[`cst-production-profile.json`](cst-production-profile.json)
is the compact schema authority paired with [`grammar.ebnf`](grammar.ebnf), and
[`generate-cst-production-schema.py`](generate-cst-production-schema.py) expands those two inputs
into the complete production portion of `NodeSchemaRegistry`. It rejects an unrecognized terminal,
an undefined production reference, an unmatched override selector, an unnamed occurrence, or a
grammar digest that changed without a corresponding schema review.

The generated schema retains EBNF structure instead of flattening it. `sequence` generates an
ordered product; `choice` generates one closed variant whose alternatives are products; `optional`
generates `Option`; `repeat` generates `NodeList`; and `oneOrMore` generates `NonEmpty`. The
cardinality constructor always wraps the complete child shape. Thus `{ ",", parameter }` is
`NodeList<{ comma, parameter }>` and can represent only the interleaved source sequence; it is never
lowered to unrelated `NodeList<comma>` and `NodeList<parameter>` fields. Every leaf has a
whitespace-independent occurrence identity, terminal/non-terminal sort, symbol constraint,
source-order position, and field role. The deterministic naming rule covers ordinary productions;
an explicit override names semantically significant roles or merges mutually exclusive leaves into
one category-typed field.

The generated representation is:

```text
GrammarOccurrenceId = (production: ProductionId, path: StructuralEBNFPath)
GrammarChoiceGroupId = GrammarOccurrenceId
GrammarQuantifierGroupId = GrammarOccurrenceId
CSTCategoryId = QualifiedName

CSTVariantTag = { stableName: QualifiedName, wireTag: UInt32 }
CSTGroupTag = { stableName: QualifiedName, wireTag: UInt32 }

CSTShapeGroup = {
    stableName: QualifiedName,
    wireTag: UInt32,
    field: {
        name: FieldName,
        edge: Structural,
        stages: { Concrete(Parsed) },
        wire: SerializedField,
        access: Editable
    }
}

CSTTypedReference =
    Terminal(stage: CSTStage)
  | Production(stage: CSTStage, production: ProductionId)
  | Category(stage: CSTStage, category: CSTCategoryId)

CSTProductionOccurrence = {
    id: GrammarOccurrenceId,
    leafKind: LiteralTerminal | TokenTerminal | SoftKeywordTerminal | NonTerminal,
    symbol: Utf8String | ProductionId,
    sourceOrder: UInt32,
    variantPath: NodeList<(group: CSTGroupTag, alternative: CSTVariantTag)>,
    cardinalityPath: NodeList<(group: CSTGroupTag,
                               kind: Optional | Repeat | OneOrMore)>
}

CSTProductionFieldDescriptor = FieldDescriptor & {
    typedReference: CSTTypedReference,
    sourceOrder: UInt32,
    occurrences: NonEmpty<CSTProductionOccurrence>
}

CSTProductionShape =
    Field(field: FieldName,
          terminalConstraint: Option<TerminalConstraint>)
  | Product(NodeList<CSTProductionShape>)
  | ClosedVariant(CSTShapeGroup,
        NonEmpty<(tag: CSTVariantTag, value: CSTProductionShape)>)
  | Optional(CSTShapeGroup, value: CSTProductionShape)
  | List(CSTShapeGroup, element: CSTProductionShape)
  | NonEmpty(CSTShapeGroup, element: CSTProductionShape)
  | OptionalField(sourceGroup: CSTGroupTag, value: Field)
  | ListField(sourceGroup: CSTGroupTag, element: Field)
  | NonEmptyField(sourceGroup: CSTGroupTag, element: Field)
  | Difference(CSTProductionShape, excluded: TerminalConstraint)
  | SemanticPredicate(GrammarPredicateId)

CSTProductionConstraint =
    CoPresent(fields: NonEmpty<FieldName>, rule: RuleId)

CSTProductionDescriptor = {
    production: ProductionId,
    kind: NodeKind where kind.family = NonTerminalNode,
    fields: NodeList<CSTProductionFieldDescriptor>,
    shape: CSTProductionShape,
    constraints: NodeList<CSTProductionConstraint>,
    invariants: NodeList<RuleId>
}
```

`StructuralEBNFPath` is computed from named `sequence`, `choice`, and quantifier boundaries after
discarding whitespace and comments. It identifies an occurrence for profile selection; it is not a
runtime child index. `fields` groups occurrences with the same approved role; the closed `shape`,
not per-leaf cardinality wrappers, composes those roles into the runtime product/variant type. A
node is valid against exactly one alternative at every `ClosedVariant`; fields from unselected
alternatives do not exist in that value. Generic operand enumeration recursively visits the selected
alternative and each list element's complete product in source order. The registry stores these
typed descriptors, not the generator's untyped EBNF parse tree.

The typed compilation functions are structural. `compileShape` produces the complete product value
for a production, choice alternative, or quantifier element; `compileFields` produces the named
slots directly owned by that product:

```text
compileShape(s) = ProductKind(compileFields(s))

compileFields(Field(f)) =
    [FieldSlotKind(name: f, valueKind: descriptor(f).valueKind)]
compileFields(Product(s...)) = concat(compileFields(s)...)
compileFields(ClosedVariant(g, (tag_i, s_i)...)) =
    [FieldSlotKind(name: g.field.name,
        valueKind: VariantKind(group: CSTGroupTag(g.stableName, g.wireTag),
            alternatives: (tag_i, compileShape(s_i))...))]
compileFields(Optional(g, s)) =
    [FieldSlotKind(name: g.field.name,
                   valueKind: OptionalKind(compileShape(s)))]
compileFields(List(g, s)) =
    [FieldSlotKind(name: g.field.name,
                   valueKind: ListKind(compileShape(s)))]
compileFields(NonEmpty(g, s)) =
    [FieldSlotKind(name: g.field.name,
                   valueKind: NonEmptyListKind(compileShape(s)))]
compileFields(OptionalField(_, Field(f))) =
    [FieldSlotKind(name: f,
                   valueKind: OptionalKind(descriptor(f).valueKind))]
compileFields(ListField(_, Field(f))) =
    [FieldSlotKind(name: f,
                   valueKind: ListKind(descriptor(f).valueKind))]
compileFields(NonEmptyField(_, Field(f))) =
    [FieldSlotKind(name: f,
                   valueKind: NonEmptyListKind(descriptor(f).valueKind))]
compileFields(Difference(s, _)) = compileFields(s)
compileFields(SemanticPredicate(_)) = []
```

At a product, `NodeFields` contains exactly its direct leaf fields and shape-group fields. A variant
group contains its tag and only the selected alternative payload; unselected alternatives contribute
no active fields. A list group contains complete element values. Serialization writes a variant tag
before its selected payload and writes a list count followed by each complete element product in
order. Generic reflection follows the same recursion, so `{ ",", parameter }` enumerates
`comma[0], parameter[0], comma[1], parameter[1], ...`; it cannot expose separately editable parallel
lists. An exact reviewed override may replace a source group with named category/optional fields,
as `IfStatement` does, but must state the equivalent co-presence invariant.

The emitted JSON is a `NodeSchemaRegistry` fragment with a chapter-3-compatible
`SchemaVersion { major, minor }`, typed `cstCategories`, `grammarProductions`, and
`cstProductionDescriptors`. Every category/production kind, field, choice/quantifier group, and
variant alternative carries a non-zero stable wire tag. Tags are the big-endian UInt32 prefix of
SHA-256 over the versioned namespace, tag domain, and stable semantic name; an explicit profile
override may pin a reviewed value. Zero is reserved, and generation rejects a collision instead of
probing for a different value. Renaming a published semantic role or changing the derivation
namespace requires a schema-version change and an explicit migration; adding an unrelated
production cannot renumber existing tags.

For example, the exact override for `if-statement` generates:

```text
IfStatement = {
    ifKeyword: TerminalNodeId<Parsed>,
    leftParenthesis: TerminalNodeId<Parsed>,
    conditionExpr: ExprCSTNodeId<Parsed>,
    rightParenthesis: TerminalNodeId<Parsed>,
    trueBranch: StmtCSTNodeId<Parsed>,
    elseKeyword: Option<TerminalNodeId<Parsed>>,
    falseBranch: Option<StmtCSTNodeId<Parsed>>
}
```

The schema constrains `ifKeyword`/`elseKeyword` to identifier terminals with those logical
spellings, constrains the parentheses to `LParent`/`RParent`, and requires
`isSome(elseKeyword) = isSome(falseBranch)`. The generic operand sequence is the flattening of these
fields in displayed order. It is not separately stored. Chapter 3 defines the stage-indexed node,
snapshot, rewrite, and reflection domains that carry this product.

`IfLetBinding` implements `ExprCSTCategory` for the purpose of `conditionExpr`, but its
production is admitted only in that contextual position; it is not added to the general
`expression` production. CST category membership describes a typed field contract, not unrestricted
grammar reachability.

`PAR-CST-001`: For every leaf occurrence in every `grammar.ebnf` production, generation yields
exactly one named terminal or non-terminal field occurrence. No delimiter, separator, operator, or
keyword leaf is elided. Two leaves may feed one field only when the profile explicitly proves that
they occupy different alternatives of the same `choice` and gives their common CST category. The
generated grouped shape, not an independently stored child list, is the source of generic operand
order and optional/repeated co-presence constraints. A choice has exactly one selected tagged
alternative. A repeated product is one ordered list of product values; parallel lists for its
component fields are not a conforming representation.

`PAR-CST-002`: The profile pins the exact digest of the grammar's canonical UTF-8/LF text, so
checkout line-ending policy is not a schema change. Changing that canonical grammar requires a
schema version change and comparison of the old and new generated descriptors. A published field name may
remain unchanged or be covered by an explicit `SchemaMigrationDescriptor.fieldRemaps` entry; a
collision suffix or structural-path shift may not silently rename it. The profile override is the
authority for preserving a semantic role when grammar structure changes. Published kind, field,
group, and alternative wire tags obey the same no-reuse rule.

## Surface grammar

[`grammar.ebnf`](grammar.ebnf) defines declarations, statements, expressions, types, generics,
attributes, semantics, and internal compatibility forms. Important boundaries are:

- a `module` declaration accepts no name, one identifier, or one string literal; dotted module
  names are not part of the current grammar;
- `import`, `__import`, `__include`, and `implementing` accept dotted identifier paths or strings;
- `struct`, `enum`, interface, extension, and callable forms may have the generic syntax shown in
  the grammar; current `class` parsing does **not** accept inline generics;
- colon clauses have role-specific productions: struct/extension clauses are interface
  conformances, interface clauses are refinements, class clauses may contain one class base plus
  conformances, and enum clauses describe their registered base roles;
- lambda syntax begins with a parenthesized traditional parameter list and uses `=>` followed by a
  block or expression;
- `sizeof` and `alignof` accept an expression-like operand and optional data-layout expression, not
  only a type;
- a property or subscript accessor block accepts the soft spellings `get`, `set`, `ref`, and
  `constref`; the last two are distinct reference-accessor roles rather than modifiers;
- attribute separators are optional for compatibility;
- `__require_capability` declaration syntax is an unparenthesized `+`/`,`-separated name list;
- `syntax` and `attribute_syntax` use the forms in `grammar.ebnf`, not the forms previously shown in
  generated grammar; and
- builtin type names are resolved declarations, not grammar terminals.

`PAR-AGG-001`: The proposed grammar has no concrete struct-inheritance production. The tokens after
a struct colon are retained as a `conformance-clause`; binding accepts only interface contracts.
A compatibility parser may recognize a concrete struct base to issue a migration diagnostic, but
it does not construct a successful surface/checked inheritance node or a base facet.

`PAR-INI-001`: A braced initializer occurs only in an initializer grammar position and may nest.
It is not a `primary-expression`. `T(args)` remains postfix syntax until binding classifies `T` as a
type, while `(T)e` is represented by the cast alternative of
`AmbiguousCastOrParenthesized`. Both successful one-input forms map to chapter 15's
`ExplicitSingle` initialization request.

### Reference-accessor spellings

The accessor spelling is retained by the CST and normalized to a semantic role only after the
property or subscript product is bound:

```text
normalizeAccessorSpelling("get")      = Getter
normalizeAccessorSpelling("set")      = Setter
normalizeAccessorSpelling("constref") = RefAccessor(ReadAccess)
normalizeAccessorSpelling("ref")      = RefAccessor(ReadWriteAccess)
```

`PAR-ACC-001`: `constref` is a soft keyword only in the accessor-name position of a property or
subscript accessor declaration. It maps exactly to `RefAccessor(ReadAccess)`; `ref` maps
exactly to `RefAccessor(ReadWriteAccess)`. The two spellings may occur in the same accessor
block, retain distinct CST tokens, and normalize to distinct map keys. Duplicate detection compares
the complete normalized role, including its access index.

`PAR-ACC-002`: The unbracketed accessor spelling `constref`, the parameter modifier
`__constref`, and the callable/receiver attribute `[constref]` are three distinct productions.
`__constref` is normalized by header checking to `ConstRefMode(locationRequirement)`;
`[constref]` remains an attribute that selects the registered receiver rule; neither can construct
a property/subscript accessor role. Conversely, an accessor-name token cannot alter its containing callable's
receiver mode. CST-to-Surface normalization preserves which of the three productions supplied the
token so serialization, formatting, and diagnostics never infer the distinction from spelling
alone.

## Expression precedence and associativity

From lowest to highest:

| Level          | Forms                                                       | Associativity                                          |
| -------------- | ----------------------------------------------------------- | ------------------------------------------------------ |
| comma          | `,`                                                         | left (Slang 2026 uses tuple syntax inside parentheses) |
| assignment     | `=` and compound assignment                                 | right                                                  |
| conditional    | `?:`                                                        | right by grammar                                       |
| logical        | `\|\|`, `&&`                                                | left                                                   |
| bitwise        | `\|`, `^`, `&`                                              | left                                                   |
| equality       | `==`, `!=`                                                  | left                                                   |
| relational     | `<`, `>`, `<=`, `>=`, `is`, `as`                            | left                                                   |
| shift          | `<<`, `>>`                                                  | left                                                   |
| additive       | `+`, `-`                                                    | left                                                   |
| multiplicative | `*`, `/`, `%`                                               | left                                                   |
| prefix         | registered prefix operators, `new`, keyword prefix forms    | right                                                  |
| postfix        | call, index, member, generic application, postfix operators | left                                                   |

`PAR-EXP-001`: Operator spellings resolve through the standard environment after parsing. Parsing
constructs an operator-application CST non-terminal and does not select a builtin or user declaration.

## Named ambiguities

The CST contains explicit alternatives for these compatibility conflicts:

```text
AmbiguousGenericOrRelational
AmbiguousCastOrParenthesized
AmbiguousDeclarationOrExpressionStatement
AmbiguousTypeOrValueGenericArgument
AmbiguousModernOrTraditionalParameter
```

Each ambiguity node owns one primary ordered terminal projection and stores typed alternative
non-terminal references over those same terminals. Every alternative has the named fields of its
production; equal terminals are shared by reference. Alternative edges are excluded from the
primary concrete-order projection and therefore cannot duplicate formatting output.

`PAR-AMB-001`: Modern Slang resolves an ambiguity by syntax, dialect, and language version only.
Legacy HLSL compatibility may request name-classification facts during the later
`ResolveSyntaxAmbiguity` query, but initial parsing still succeeds without them.

`PAR-AMB-002`: Resolution produces a `SurfaceAST` origin pointing at the ambiguous CST and records
the chosen alternative plus rule ID. If more than one alternative remains valid, binding emits an
ambiguity diagnostic instead of using declaration order accidentally.

### Generic closing tokens

The parser may view a `>>` token as two closers when inside generic arguments. The first terminal
node refers to a `TokenSlice` covering the first spelling byte and owns no trivia; the second refers
to a slice covering the second byte. Any `TrailingTrivia(parent)` remains an adjacency view after
the unsplit parent token. In expression shift context the same token is one whole-token terminal.

### Syntax declarations

The fixed/contextual grammar is parameterized by immutable `GrammarVocabulary`. The separate
`SyntaxParseInfoSet` contains builtin entries corresponding to
today's `g_parseSyntaxEntries` are versioned standard-environment data. A
`SerializedSyntaxParseInfo` is the immutable/callback-free form of the existing `SyntaxParseInfo`;
its `syntaxClass` retains the established `SyntaxClass` classification. A source `SyntaxDecl`
remains a declaration and contributes an entry when its compatibility scope is active; none of
these terms is renamed to a generic “syntax feature.”

Source-defined `syntax` declarations are an unresolved compatibility feature. The proposed safe
model is:

1. `syntax` declarations always parse using fixed grammar;
2. binding a `SyntaxDecl` functionally extends `SyntaxParseInfoSet` for subsequent declaration
   ranges;
3. compatibility parsing may interpret an identifier through that set; and
4. modern mode restricts aliases to fixed parse shapes or rejects them.

This preserves a testable transformation and makes order-dependence explicit. The ledger must close
the modern-mode policy before parser implementation freezes.

## Recovery grammar

Every production declares:

- tokens that can begin a construct;
- tokens that can follow it;
- an insertion preference for expected delimiters/separators;
- a synchronization set; and
- whether nested delimiters are balanced during skipping.

Recovery emits only these terminal/non-terminal forms:

```text
RecoverMissing(expected, anchor) -> MissingTerminal
RecoverSkipped(tokens) -> SkippedTokens
RecoverUnexpected(node, expectedCategory) -> UnexpectedConstruct
```

The enclosing `CSTRewrite.rule` supplies `rule`; the recovery node/terminal exposes these arguments
as read-only rewrite projections rather than storing a second copy.

`PAR-REC-001`: A recovery action must consume a token, insert a missing token, or return to a caller
that will do so. Progress is a structural invariant; there is no global “advance after 64 tries”
escape hatch.

`PAR-REC-002`: A missing closer is inserted before a token in the production's follow set. A real
unexpected closer is never consumed as the missing closer of another delimiter level.

`PAR-REC-003`: Skipped tokens remain in source order under the smallest enclosing CST non-terminal whose
recovery rule consumed them.

`PAR-REC-004`: At EOF, every open delimiter produces one `MissingTerminal` with a rewrite input
that reaches the related opening terminal. Recovery terminates in time linear in remaining token
count for a fixed grammar.

## CST-to-surface normalization

Parsing does not perform semantic desugaring. In particular:

- `if (let ...)` remains an `IfStatement` whose `conditionExpr` is `IfLetBinding`; CST-to-Surface
  does not immediately rewrite it into temporaries;
- cbuffer/tbuffer syntax remains a dedicated surface declaration rather than parser-synthesized
  struct/wrapper/variable declarations;
- default interface methods remain their written generic shape and are never reparsed from copied
  tokens;
- declaration/expression ambiguities remain explicit until binding; and
- function bodies have immutable CST roots, whether parsed eagerly or on demand.

`PAR-NRM-001`: CST-to-SurfaceAST may remove punctuation from AST structural fields, but every output
node has `Parsed(cstId: CSTNodeId<Parsed>)` provenance and every written distinction needed by
diagnostics remains a named field or is reachable through CST rewrite predecessors.

## Machine-checkable completeness

The eventual grammar/schema source generates token enums, `GrammarVocabulary` and
`SyntaxParseInfoSet` tables, stage-indexed
non-terminal kinds, typed terminal/non-terminal field products, parser production IDs, reflection
metadata, documentation tables, and test skeletons. CI checks:

1. every token kind is classified by the lexical schema;
2. every builtin syntax spelling maps to a grammar production or declared extension hook;
3. every parser spelling and dialect/version gate maps back to the grammar;
4. every non-terminal kind has a production/transformation/recovery constructor;
5. every terminal and non-terminal occurrence in every production has one named, typed field;
6. every grammar alternative has positive and recovery witnesses;
7. undeclared FIRST/FOLLOW conflicts and backtracking fail generation; and
8. differential parsing covers repository `.slang`, standard-module, prelude, and test sources.

The required properties are exact ordered `Token | Trivia` physical-spelling concatenation from the
authoritative lexed `TokenList`, identity-format round trip, no token loss on invalid input,
full/incremental parse equivalence, and CST serialization stability.

## Current implementation evidence

The principal evidence for this chapter is:

- `source/compiler-core/slang-token.h` and `slang-token-defs.h`;
- `source/compiler-core/slang-lexer.{h,cpp}`;
- `source/compiler-core/slang-source-loc.{h,cpp}`;
- `source/slang/slang-preprocessor.{h,cpp}`;
- `source/slang/slang-parser.cpp`, especially `g_parseSyntaxEntries`;
- `source/slang/slang-ast-stmt.h` (`UnparsedStmt`);
- `source/slang/slang-check-decl.cpp` (deferred body reparse); and
- formatter/doc extractor sources that currently re-lex independently.

Known source/document discrepancies are listed in chapter 12 and must remain differential tests.
