# Lexical and syntactic specification

This chapter specifies the lossless syntax boundary and the parser's contract. The companion
[`grammar.ebnf`](grammar.ebnf) is a structural EBNF baseline for the full surface grammar. It is
derived from official source at `aaa07fe296560ffefeaf2e39d0aed5658b641a21` and corrects known
errors in the older generated grammar.
Its productions and island predicates are mechanically readable; exhaustive `@recover`,
and `@language-version` annotations remain an explicitly blocking grammar-freeze item in
chapter 13 rather than an implicit parser-generator default.

`SYN-SCOPE-001`: This grammar accepts the Slang 2026 source language. Legacy HLSL and GLSL input
dialects are outside its normative language, even when the current parser happens to share a path
with them. A traditional declaration or cast spelling appears here only when Slang 2026 itself
retains that spelling. A source form whose only justification is input-dialect compatibility must
be rejected or handled by a separate compatibility frontend, never surfaced as a successful node
of this grammar.

Declaration outlining is syntax-only. Fine parsing is a scheduler query and may request name
lookup or checked semantic facts when the language's grammar is name-directed. Every such request
goes through a narrow explicit interface; no parser reads mutable checker state ambiently.

## Inputs, outputs, and parsing stages

```text
Lex(SourceView, LexOptions) -> CheckResult<TokenList>
BuildLexedCST(TokenList, LexicalContextId) -> CSTSnapshot<Lexed>

ParseDecls(CSTSnapshot<MacroExpanded>, DeclGrammar,
           GrammarVocabulary, DeclParserOptions)
    -> CheckResult<DeclParseResult>

ResolveImportOutlines(DeclParseResult, ModuleId,
                      ModuleResolutionProvider, ModuleResolutionRevision,
                      LanguageRuleSetId)
    -> QueryStep<ImportResolutionIndex>

WireLookupScopes(DeclParseResult, ImportResolutionIndex,
                 ScopeWiringEnvironment)
    -> QueryStep<ScopeWiring>

ParseAndCheckExpression(UnparsedContentId, ScopePosition,
                        ExpressionCheckContextId, ScopeWiringId,
                        SyntaxDisambiguationProvider)
    -> QueryStep<CheckedExpressionContent>

ParseAndCheckStatement(...) -> QueryStep<CheckedStatementContent>
ParseAndCheckDeclHeader(DeclHeaderFineParseSubject,
                        SyntaxDisambiguationProvider)
    -> QueryStep<CheckedDeclHeaderContent>

LexOptions = {
    languageRules: LanguageRuleSetId,
    recognizeLineContinuations: Bool,
    preserveInvalidTokens: True
}

DeclParserOptions = {
    recoveryActionLimit: UInt32,
    nestingDepthLimit: UInt32
}

ParserOptions = {
    preserveRecoveredAmbiguities: Bool,
    recoveryActionLimit: UInt32,
    ambiguityAlternativeLimit: UInt32,
    nestingDepthLimit: UInt32
}

DeclGrammar = {
    stage: DeclParsed,
    grammarSource: ContentId<Utf8String>,
    productionProfile: ContentId<SchemaValue>,
    registry: NodeSchemaRegistryFragmentId,
    root: ProductionId
}

GrammarWord = {
    id: QualifiedName,
    spelling: Utf8String,
    role: ReservedGrammarWord | ContextualGrammarWord,
    rule: RuleId
}

GrammarVocabulary = {
    languageRules: LanguageRuleSetId,
    words: CanonicallyOrderedMap<QualifiedName, GrammarWord>,
    revision: ContentId<SchemaValue>
}

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

SyntaxParseInfoSetId = ContentId<SyntaxParseInfoSet>
```

`BuildLexedCST` mechanically creates one terminal per element of the one flat `Token | Trivia`
list and puts those terminals under a single `TokenizedSource` non-terminal. It does not copy
tokens or create a second physical-token list. Its `LexicalContextId` is the content identity of
the source view and exact `LexOptions` already supplied to `Lex`. Preprocessing then produces the
`MacroExpanded` input under the state and expansion rules of the
[preprocessing chapter](04-preprocessing.md).

`ParseDecls` runs the coarse declaration grammar. Its `DeclParsed` snapshot contains the declaration
hierarchy, names, direct generic markers, delimiters, and exact `UnparsedContent` ranges. It
does not parse every expression or check a declaration header. `ResolveImportOutlines` resolves the
exact import module-name fields through its revisioned provider. `WireLookupScopes` uses the local
outlines plus that typed resolution product to publish the lookup topology and the exact
`ScopePosition` at which each deferred region begins.

Fine parse/check queries operate on one deferred region at a time. Their scheduler dependencies may
interleave parsing, lookup, type checking, overload resolution, and further parsing. A completed
query publishes a `Parsed` CST fragment and node-local immutable AST results. `Parsed` therefore
does not mean that the entire file passed through a bulk phase. A whole-file parsed view is an
optional derived tooling/serialization assembly.

`SyntaxDisambiguationProvider` is injectable. Unit tests can answer generic-head, registered-syntax,
member, blocked, and recovery queries without constructing a compiler session. The production
provider delegates to the centralized scheduler. Every option, vocabulary revision, scope-wiring
identity, and semantic context used by a query participates in its key; resource limits are
deterministic recovery inputs, never wall-clock budgets.

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

All language words are initially `Identifier` tokens. `GrammarVocabulary` then classifies a spelling
as reserved or contextual for the selected Slang language rules. Reservedness is a parser/name
formation rule rather than a second lexer token kind: a `ReservedGrammarWord` cannot be accepted by
an `IDENTIFIER` field, while a `ContextualGrammarWord` is recognized only in the production position
that requests it. Versioned compiler-provided syntax metadata is separately provided by
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

Slang 2026 lexing accepts an underscore, ASCII letter, or non-ASCII scalar as the first character,
followed by those characters or ASCII digits. This states the language accepted by this edition
rather than claiming Unicode XID behavior the language has not adopted.

```text
identifier-start    ::= '_' | ASCII-LETTER | NON-ASCII-SCALAR ;
identifier-continue ::= identifier-start | ASCII-DIGIT ;
identifier          ::= identifier-start { identifier-continue } ;
```

`LEX-ID-001`: Identifier equality is defined on the decoded scalar sequence without Unicode
normalization. A later language edition may adopt XID and normalization only as an intentional
language-version change.

### Reserved and contextual words

The following `GrammarVocabulary` entries are `ReservedGrammarWord` values in Slang 2026:

```text
declaration introducers:
    module import implementing namespace using typedef typealias
    struct class enum interface extension func operator property
    get set ref constref associatedtype cbuffer tbuffer

statement/control introducers:
    if else for while do catch switch case default
    break continue return discard defer throw try

binding introducers:
    var let
```

The corresponding implementation-reserved spellings beginning with `__` are also reserved.
`syntax`, `attribute_syntax`, and `type_param` are reserved for compiler-owned source but are not
user-definable declaration forms. Other grammar words remain `ContextualGrammarWord` unless a rule
explicitly adds them to the versioned reserved set.

`LEX-ID-002`: An `IDENTIFIER` terminal cannot consume a reserved word, including in a declaration
name, parameter name, member name, or qualified-name component. A contextual word remains a valid
identifier outside the exact production position that recognizes it. Reservedness therefore cannot
depend on name lookup, declaration order, or which overload is selected.

## Literals

The lexical grammar distinguishes spelling from semantic validation:

```text
integer-literal ::= decimal-integer integer-suffix?
                  | binary-integer integer-suffix?
                  | hex-integer integer-suffix? ;

floating-literal ::= decimal-float float-suffix?
                   | hex-float float-suffix?
                   | '#INF' float-suffix? ;

string-literal ::= ordinary-string | raw-string ;
char-literal   ::= "'" character-or-escape "'" ;
```

Digit separators, exponent forms, escape syntax, raw-string delimiters, recognized suffixes, range
selection, and malformed-literal diagnostics are rule-table data generated from the lexical schema.
Slang tokenization accepts an alphanumeric suffix and leaves unsupported-suffix rejection to
literal checking. A multi-digit leading-zero integer is tokenizable but is not included in the
successful literal forms above while the separately named chapter 13 language-owner decision
remains open; current implementation acceptance alone cannot make it a Slang 2026 value.

`LEX-LIT-001`: The token stores exact physical and logical spelling. The pure, memoizable
`DecodeLiteral(TokenRef, LanguageRuleSetId)` query from chapter 7 produces the decoded value or
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
- `/* ... */` → `BlockComment`; comments do not nest; and
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

## Preprocessing

The [preprocessing chapter](04-preprocessing.md) specifies preprocessing as its own immutable
translation, including directive spelling,
structured CST, persistent `PreprocessorPersistentState`, ordered scan, macro invocation recognition,
argument collection, prescan, substitution, stringizing, token paste, rescan, recursion suppression,
conditionals, includes, diagnostics, and direct provenance. This syntax chapter does not maintain a
second partial description of those rules.

## Declaration-outline grammar

The first parser uses the checked-in
[`decl-outline-grammar.ebnf`](decl-outline-grammar.ebnf) paired with
[`decl-cst-production-profile.json`](decl-cst-production-profile.json). Its only semantic purpose is
to establish declaration membership and the facts required for initial lookup wiring. In summary:

```text
outline-unit        ::= layout* (outline-declaration layout*)* EOF
layout              ::= active-trivia | maximal-inactive-content

outline-declaration ::= import | namespace | aggregate | interface | extension
                      | buffer | callable | property | variable | type-alias
                      | associated | explicit-generic | empty
                      | c-style/fallback | recovered

known-decl-head     ::= modifiers? introducer trivia* identifier? unparsed-header
direct-generic-marker(binding) =
    firstActiveToken(genericMarkerContent(binding.header)) is the token '<'

genericMarkerContent(OrdinaryDeclHeader(content)) = content
genericMarkerContent(CStyleDeclHeader(_, _, _, suffix)) = suffix
genericMarkerContent(NoDeclHeader) = none

import              ::= modifiers? '__exported'? ('import' | '__import')
                        trivia* (identifier (trivia* '.' trivia* identifier)*
                                 | string-literal) trivia* ';'

declaration-container ::= '{' layout* (outline-declaration layout*)* '}'
deferred-body          ::= one semicolon | one balanced brace body

c-style-group ::= declaration-specifiers
                  ( variable-declarator (',' variable-declarator)* ';'
                  | function-declarator deferred-body )

variable-declarator ::= unparsed-prefix name:IDENTIFIER unparsed-suffix
function-declarator ::= unparsed-prefix name:IDENTIFIER unparsed-suffix
```

Every exact-introducer production exposes its introducer/modifier terminals, name terminal when
present, exact header `UnparsedContent`, body delimiters, and nested outline list as named fields.
The C-style fallback exposes one shared declaration-specifier range, an optional structured inline
type declaration, and a source-ordered product for every declarator. Each declarator product has a
direct `name` terminal plus exact prefix and suffix `UnparsedContent` fields. `DeclOutline.bindings`
projects the optional inline-type binding first and then one binding per declarator, so
`struct S {} x, y;` wires heterogeneous `S`, `x`, and `y` without copying the shared spelling or
collapsing their declaration kinds. `direct-generic-marker` examines only the ordinary header or
C-style suffix selected by `genericMarkerContent`. It neither searches for a closing `>` nor counts
generic parameters.

Namespace, aggregate, interface, and extension bodies use `declaration-container` and are
recursively outlined. Callable bodies, expression and statement regions, initializers, type
spellings, defaults, attributes, and constraints use `UnparsedContent`. Local declarations are
discovered by the fine parser for their containing body and extend scope wiring immutably.

`TRIVIA`, `TOKEN`, `CST_ELEMENT`, and `INACTIVE_ELEMENT` in the outline artifact are stage-local
selectors over the one `MacroExpanded.primaryList`; they are not lexer token kinds. `TRIVIA`
selects an active `Trivia` element, `TOKEN` an active non-trivia `Token`, `CST_ELEMENT` either
active alternative, and `INACTIVE_ELEMENT` either alternative when the snapshot's one activity
map marks it inactive. The grammar recognizer makes syntax decisions through `ActiveTokenView`.
The structural translator walks the base list: active trivia becomes ordinary layout, while each
maximal contiguous inactive run becomes one `outline-inactive-content` non-terminal and cannot
start a declaration or affect a delimiter stack. Output terminals always refer to the selected
predecessor element. Named leaves, `outline-unparsed-content`, and
`outline-inactive-content` therefore partition the complete base sequence, including inactive
tokens and trivia, exactly once.

`ScanOutlineHeader` advances over active `CST_ELEMENT` values while retaining intervening inactive
content structurally. It balances only active parentheses, brackets, and braces. It does not
balance `<`/`>`: angle punctuation stays opaque, which is the reason this stage
cannot confuse a generic clause with relational operators inside a deferred expression. At depth
zero it stops before the declaration-kind-specific boundary: `;`, a recursively outlined aggregate/
namespace/interface/extension/buffer body, or a callable/property deferred brace body. The selected
boundary is a named terminal or non-terminal of the enclosing production, never part of two nodes.
`ScanDeferredBody` then consumes exactly the selected semicolon or one brace group, including nested
balanced groups, into a single `UnparsedContent` for later fine parsing.

Outline alternatives have a fixed precedence: exact introducer productions, then the retained
C-style declaration fallback, then recovery. A grammar word counts as an introducer only when the
exact `GrammarVocabulary` input assigns it that role. The fallback is selected by this pure
primitive:

```text
FallbackDeclaratorPartition = {
    prefix: TokenListRange,
    name: TokenRef,
    suffix: TokenListRange
}

FallbackInlineTypeBinding = {
    kind: DeclKind where kind is StructDecl | ClassDecl | EnumDecl,
    name: Option<TokenRef>,
    header: TokenListRange,
    body: TokenListRange
}

FallbackDeclPlan =
    VariableDeclGroup {
        declarationSpecifiers: TokenListRange,
        inlineType: Option<FallbackInlineTypeBinding>,
        declarators: NonEmpty<FallbackDeclaratorPartition>,
        commas: NodeList<TokenRef>,
        semicolon: TokenRef
    }
  | TraditionalFunctionDecl {
        declarationSpecifiers: TokenListRange,
        inlineType: Option<FallbackInlineTypeBinding>,
        declarator: FallbackDeclaratorPartition,
        body: TokenListRange
    }

ScanFallbackDecl(subject: TokenListRange,
                 activity: TokenActivityMapId,
                 languageRules: LanguageRuleSetId)
    -> Unique(FallbackDeclPlan)
     | NoPlan
     | Ambiguous(NonEmpty<FallbackDeclPlan>)
```

The scan enumerates active-token split points and accepts a plan only when the declaration-specifier
prefix is nonempty, each declarator matches the surface grammar's pointer/direct-declarator/suffix
skeleton with exactly one identifier selected as `name`, top-level commas and the body boundary
consume the complete active subject, and all parentheses, brackets, and braces are balanced.
Parameter types, declaration-specifier types, generic-angle content, and initializer
assignment-expressions remain opaque balanced islands; no name or type lookup is permitted.
When the declaration specifiers contain an inline `struct`, `class`, or `enum` declaration, the
plan also selects its introducer, optional direct name terminal, header, and balanced body as one
`FallbackInlineTypeBinding`. The ordinary aggregate-outline alternative is inapplicable when active
tokens after that body form a declarator group, so `struct S {} x;` is planned as one heterogeneous
`DeclGroup` instead of two broken outlines. Inactive elements are retained in the structural ranges
but ignored by these acceptance tests.
The grammar's semantic predicates select the exact ranges and identifier terminals in the unique
plan, which the generated `name` fields make machine-checkable. `NoPlan` falls through to ordinary
recovery. `Ambiguous` publishes a recovered declaration group with all competing partitions for
diagnostics; it never guesses a scope member from iteration order.

`PAR-OUT-001`: Every element of `MacroExpanded.primaryList` is structurally covered exactly once by
the outline root: as a named active terminal, within one exact active/deferred `UnparsedContent`,
or within one maximal `outline-inactive-content`. Deferred and inactive content references
predecessor elements; neither owns a copied `List<Token>`.

`PAR-OUT-002`: `DirectGeneric` means only that one declaration binding's name suffix begins with the written
direct generic marker. It neither searches for the matching `>` nor splits or counts parameters.
It is sufficient for early parser lookup but is not a checked `GenericBinder`; `GetGenericBinder`
later fine-parses the complete header and checks parameter sorts, defaults, and constraints.

`PAR-OUT-003`: Delimiter recovery may publish `RecoveredGeneric` or a recovered declaration outline,
but an unknown outline is not silently classified as a successful non-generic declaration.

`PAR-OUT-004`: `DeclGrammar` is the content-identified product generated from the exact declaration
EBNF and profile. `ParseDecls` rejects a grammar whose stage is not `DeclParsed`, whose root is not
`slang.declOutline.outlineUnit`, or whose registry/profile/source hashes disagree. Grammar file
names and process-local parser tables are not query identity.

`PAR-OUT-005`: Outlining opaque header content is not language acceptance. Fine parsing and checking
must still apply the complete production and semantic rules. In particular, a `struct` colon clause
can denote only interface conformance in the proposed language; concrete struct inheritance is not
a declaration alternative and recovery from its legacy spelling publishes no base facet, subobject,
initialization slot, subtype witness, or IR conversion.

`PAR-OUT-006`: `outline-inactive-content` contributes no `DeclOutlineBinding`, `DeclFragmentId`,
`Scope`, import edge, generic presence, delimiter event, or fine-parse subject. Changing only text
inside an inactive run may change lossless CST/provenance identity, but cannot change active scope
wiring until the preprocessor activity result changes.

`PAR-OUT-007`: For a successful C-style fallback, the stored declaration-specifier, optional inline
type, declarator,
separator, and boundary fields are a bijection with the unique `FallbackDeclPlan`. Every
declarator has exactly one direct `name` terminal and produces exactly one source-ordered binding.
An inline type specifier produces one preceding binding with its own `DeclKind` and optional direct
name; declarator bindings carry their own variable/function kinds. The gap-free binding ordinal,
not a map traversal or checker completion order, distinguishes heterogeneous members of a
`DeclGroup`.

## CST production fields

EBNF specifies accepted ordering and repetition; the paired node schema assigns every symbol
occurrence a stable field role and category. A production is incomplete and cannot generate a
parser until both parts exist. The checked-in
[`cst-production-profile.json`](cst-production-profile.json) and
[`decl-cst-production-profile.json`](decl-cst-production-profile.json) are the compact schema
authorities paired with [`grammar.ebnf`](grammar.ebnf) and
[`decl-outline-grammar.ebnf`](decl-outline-grammar.ebnf), respectively.
[`generate-cst-production-schema.py`](generate-cst-production-schema.py) expands either explicit
profile into the complete production portion of `NodeSchemaRegistry`. It rejects an unrecognized terminal,
an undefined production reference, an unmatched override selector, an unnamed occurrence, or a
grammar digest that changed without a corresponding schema review.

Each profile names its `CSTStage`, a valid `grammarNamespace` used as the `ProductionId` prefix, the
schema version, and the canonical UTF-8/LF digest of its grammar. Production names are normalized to
schema identifiers within that namespace and generation rejects a collision. The profile path is an
explicit generator input; neither the file name nor a hard-coded `Parsed` stage participates in the
emitted registry identity.

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
        domains: { Concrete(Parsed) },
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
`cstProductionDescriptors`, plus any profile-declared `derivedViews`. A derived-view descriptor
names its source category, result value kind, and normative projection rule; it owns no parallel
node data. Every category/production kind, field, choice/quantifier group, and
variant alternative carries a non-zero stable wire tag. Tags are the big-endian UInt32 prefix of
SHA-256 over the versioned namespace, tag domain, and stable semantic name; an explicit profile
override may pin a reviewed value. Zero is reserved, and generation rejects a collision instead of
probing for a different value. Renaming a semantic role or changing the derivation namespace
requires a compiler/schema-version change; adding an unrelated production cannot renumber existing
tags within that version. Older serialized artifacts are rejected rather than migrated implicitly.

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
snapshot, transformation, and reflection domains that carry this product.

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
compiler/schema-version change and comparison of the old and new generated descriptors. A field name
may remain unchanged when its semantic role is unchanged; a collision suffix or structural-path
shift may not silently rename it inside one schema. The profile override is the authority for
preserving a semantic role when grammar structure changes. This review discipline supports
determinism and tooling but does not promise cross-compiler deserialization.

## Surface grammar

[`grammar.ebnf`](grammar.ebnf) defines Slang 2026 declarations, statements, expressions, types,
generics, attributes, semantics, and retained traditional Slang forms. Important boundaries are:

- a `module` declaration accepts no name, one identifier, or one string literal; dotted module
  names are not part of the current grammar;
- `import`, `__import`, `__include`, and `implementing` accept dotted identifier paths or strings;
- `struct`, `class`, `enum`, interface, extension, and callable forms may have the generic syntax
  shown in the grammar;
- colon clauses have role-specific productions: struct/extension clauses are interface
  conformances, interface clauses are refinements, class clauses may contain one class base plus
  conformances, and enum clauses describe their registered base roles;
- lambda syntax begins with a parenthesized traditional parameter list and uses `=>` followed by a
  block or expression;
- `sizeof` and `alignof` accept an expression-like operand and optional data-layout expression, not
  only a type;
- a property or subscript accessor block accepts the soft spellings `get`, `set`, `ref`, and
  `constref`; the last two are distinct reference-accessor roles rather than modifiers;
- adjacent attribute items require an explicit comma; `[A B]` is recovered invalid syntax rather
  than an alternate spelling of `[A, B]`;
- `__require_capability` declaration syntax is an unparenthesized `+`/`,`-separated name list;
- user-defined `syntax` and `attribute_syntax` declarations are not Slang language forms; and
- builtin type names are resolved declarations, not grammar terminals.

`PAR-AGG-001`: The proposed grammar has no concrete struct-inheritance production. The tokens after
a struct colon are retained as a `conformance-clause`; binding accepts only interface contracts.
A compatibility parser may recognize a concrete struct base to issue a migration diagnostic, but
it does not construct a successful surface/checked inheritance node or a base facet.

`PAR-INI-001`: A braced initializer occurs only in an initializer grammar position and may nest.
It is not a `primary-expression`. `T(args)` remains postfix syntax until binding classifies `T` as a
type and may then form an initialization request. `(T)e` is represented by the cast alternative of
`AmbiguousCastOrParenthesized` and is checked by the cast/conversion rules. In particular, `(T)0`
has no aggregate-initialization meaning: it succeeds only when the ordinary Slang cast from the
integer operand to `T` succeeds.

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

| Level          | Forms                                                       | Associativity    |
| -------------- | ----------------------------------------------------------- | ---------------- |
| assignment     | `=` and compound assignment                                 | right            |
| conditional    | `?:`                                                        | right by grammar |
| logical        | `\|\|`, `&&`                                                | left             |
| bitwise        | `\|`, `^`, `&`                                              | left             |
| equality       | `==`, `!=`                                                  | left             |
| relational     | `<`, `>`, `<=`, `>=`, `is`, `as`                            | left             |
| shift          | `<<`, `>>`                                                  | left             |
| additive       | `+`, `-`                                                    | left             |
| multiplicative | `*`, `/`, `%`                                               | left             |
| prefix         | registered prefix operators, `new`, keyword prefix forms    | right            |
| postfix        | call, index, member, generic application, postfix operators | left             |

`PAR-EXP-001`: Operator spellings resolve through the standard environment after parsing. Parsing
constructs an operator-application CST non-terminal and does not select a builtin or user declaration.

`PAR-EXP-002`: Slang 2026 has no comma operator. A comma is accepted only by a production that
names a separated sequence, such as an argument list, tuple expression, initializer list, generic
argument list, or declarator group. Such punctuation belongs to that enclosing non-terminal and
never constructs a binary operator application. Consequently `a, b;` is not a valid expression
statement, while `(a, b)` is the explicitly delimited tuple form.

## Named ambiguities

Fine parsing retains explicit alternatives only for name-directed conflicts whose active language
rules permit more than one syntax after the available lookup facts have been requested:

```text
AmbiguousCastOrParenthesized
AmbiguousDeclarationOrExpressionStatement
AmbiguousTypeOrValueGenericArgument
AmbiguousModernOrTraditionalParameter
```

Each ambiguity node owns one primary ordered terminal projection and stores typed alternative
non-terminal references over those same terminals. Every alternative has the named fields of its
production; equal terminals are shared by reference. Alternative edges are excluded from the
primary concrete-order projection and therefore cannot duplicate formatting output.

`PAR-AMB-001`: Fine parsing first requests the name/scope/type facts declared by the production's
disambiguation rule. An ambiguity node is published only when the active Slang language rules
preserve alternatives after those facts are available or when recovery from a failed
lookup must retain both interpretations. A blocked lookup blocks the parse query rather than
silently choosing an alternative.

`PAR-AMB-002`: Resolution produces a node-local surface result whose `ASTNodeOrigin` points at the
ambiguous CST and records the chosen alternative plus rule ID. If more than one alternative remains
valid, the query emits an ambiguity diagnostic instead of using declaration order accidentally.

### Generic closing tokens

Generic application is name-directed:

```text
ClassifyGenericApplicationHead(head, position, ScopeWiring, semanticContext)
    -> QueryStep<GenericHeadClassification>

GenericHeadClassification =
    GenericHead(genericCandidates: NonEmpty<ParserLookupCandidate>,
                otherCandidates: NodeList<ParserLookupCandidate>)
  | NonGenericHead(candidates: NodeList<ParserLookupCandidate>)
  | UnresolvedHead(failure: ParserLookupFailure)
```

`PAR-GEN-001`: When at least one visible candidate projects to `IsGeneric`, the following
balanced `<...>` is generic application syntax. A local candidate projects `DirectGeneric` to that
summary; an imported candidate reads the summary from its `ImportedDeclOutline`. A mixed generic/
non-generic overload set selects generic syntax; supplied generic arguments later filter the
non-generic candidates.

`PAR-GEN-002`: When lookup completes with no generic candidate, `<` remains relational syntax. A
namespace-qualified head is classified from scope wiring. A value-member head may require checking
the base and performing member lookup; this is a legal scheduler dependency of the fine parser.

`PAR-GEN-003`: When classification is blocked, parsing is blocked. It must not publish the result of
a speculative FOLLOW-set parse. `UnresolvedHead` may produce a recovery ambiguity only after an
actual lookup error. `RecoveredGenericPresence` is such a recovery input and is never treated as
successful evidence that a declaration is non-generic.

`PAR-GEN-004`: Only after generic syntax is selected may one `>>` token be viewed as two closers.
The first terminal refers to a `TokenSlice` covering the first spelling byte and owns no trivia; the
second covers the second byte. `TrailingTrivia(parent)` remains an adjacency view after the unsplit
parent token. In shift context the same token remains one whole-token terminal.

### Explicit generic wrapper syntax

The retained `__generic<...> declaration` spelling has a concrete wrapper non-terminal so its
keyword, binder delimiters, parameters, and enclosed declaration remain lossless. That wrapper is
only a source-syntax arrangement; it does not introduce a semantic `GenericDecl` that owns the
enclosed declaration.

`PAR-GEN-005`: Outlining projects the enclosed declaration's name and `DeclKind` into its normal
scope position. Fine header checking translates both `__generic<P...> D` and an inline generic
clause on `D` to the same `GenericBinder` field of `D`, with source provenance identifying the
spelling used. Every later declaration, declaration-reference, partial-application, and function-
type rule consumes that binder representation. A declaration with both wrapper and inline binder
syntax is ill-formed rather than producing nested semantic generic declarations.

### Syntax declarations

The fixed/contextual grammar is parameterized by immutable `GrammarVocabulary`. The separate
`SyntaxParseInfoSet` contains versioned compiler-provided entries corresponding to today's
`g_parseSyntaxEntries`. A `SerializedSyntaxParseInfo` is the immutable/callback-free form of the
existing `SyntaxParseInfo`; its `syntaxClass` retains the established `SyntaxClass` classification.

`PAR-SYN-001`: `syntax` and `attribute_syntax` are not user-definable declarations in Slang 2026.
They do not appear in the public surface grammar, do not create declaration outlines or scope
bindings, and cannot change how later user tokens are parsed. A written occurrence is diagnosed as
an implementation-reserved construct and retained only through ordinary recovery nodes.

`PAR-SYN-002`: An implementation may bootstrap `SyntaxParseInfoSet` from compiler-owned tables or
compiler-owned source, but that translation occurs while constructing the versioned standard
environment, before parsing a user module. Its result is an explicit immutable parser input. The
bootstrap representation and any internal `SyntaxDecl` nodes are implementation details and cannot
be observed through source lookup, imported outlines, or user module serialization.

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

The recovery node or terminal stores a direct `CSTTranslationOrigin` with the rule and consumed
predecessor inputs (or an exact empty anchor). No separate recovery-operation object or projected
output table exists.

`PAR-REC-001`: A recovery action must consume a token, insert a missing token, or return to a caller
that will do so. Progress is a structural invariant; there is no global “advance after 64 tries”
escape hatch.

`PAR-REC-002`: A missing closer is inserted before a token in the production's follow set. A real
unexpected closer is never consumed as the missing closer of another delimiter level.

`PAR-REC-003`: Skipped tokens remain in source order under the smallest enclosing CST non-terminal whose
recovery rule consumed them.

`PAR-REC-004`: At EOF, every open delimiter produces one `MissingTerminal` with a provenance input
that reaches the related opening terminal. Recovery terminates in time linear in remaining token
count for a fixed grammar.

## CST-to-surface translation

Parsing does not perform semantic desugaring. In particular:

- `if (let ...)` remains an `IfStatement` whose `conditionExpr` is `IfLetBinding`; CST-to-Surface
  does not immediately rewrite it into temporaries;
- cbuffer/tbuffer syntax remains a dedicated surface declaration rather than parser-synthesized
  struct/wrapper/variable declarations;
- default interface methods remain their written generic shape and are never reparsed from copied
  tokens;
- name-directed declaration/expression ambiguities remain explicit until their checking query; and
- function bodies have immutable CST roots, whether parsed eagerly or on demand.

`PAR-NRM-001`: A CST-to-surface translation may remove punctuation from AST structural fields, but
every output node has `FromCST(cstId)` provenance and every written distinction needed by
diagnostics remains a named field or is reachable through direct CST/token predecessor origins.

## Machine-checkable completeness

The two paired grammar/schema inputs generate the `DeclParsed` outline grammar and the fine
`Parsed` grammar, together with token selectors, `GrammarVocabulary`,
`SyntaxParseInfoSet` tables, domain-indexed non-terminal kinds, typed terminal/non-terminal field
products, parser production IDs, reflection metadata, documentation tables, and test skeletons.
The generator takes the profile path and its CST stage as explicit inputs; CI invokes it once for
each checked-in profile.
CI checks:

1. every token kind is classified by the lexical schema;
2. every builtin syntax spelling maps to a grammar production or declared extension hook;
3. every parser spelling and Slang language-version gate maps back to the grammar;
4. every non-terminal kind has a production/transformation/recovery constructor;
5. every terminal and non-terminal occurrence in every production has one named, typed field;
6. every grammar alternative has positive and recovery witnesses;
7. undeclared FIRST/FOLLOW conflicts and backtracking fail generation; and
8. declaration outlining followed by required fine parse/check queries covers every input terminal;
9. scope wiring gives every `UnparsedContent` one exact entry position; and
10. differential parsing covers repository `.slang`, standard-module, prelude, and test sources.

The required properties are exact ordered `Token | Trivia` physical-spelling concatenation from the
authoritative lexed `TokenList`, identity-format round trip, no token loss on invalid input,
full/incremental query equivalence, allocation/scheduler-order independence, and CST serialization
stability.

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

Known source/document discrepancies are listed in chapter 13 and must remain differential tests.
