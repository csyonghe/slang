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
LexPhysical(SourceDocument, LexOptions)
    -> CheckResult<PhysicalTokenTape>

Preprocess(PhysicalTokenTape, IncludeProvider, MacroEnvironment, PpOptions)
    -> CheckResult<(PreprocessorTree, ExpandedTokenView)>

Parse(ExpandedTokenView, SyntaxFeatureSet, ParseOptions)
    -> CheckResult<LosslessCST>

LexOptions = {
    languageRules: LanguageRuleSetId,
    recognizeLineContinuations: Bool,
    preserveInvalidTokens: True
}

PpOptions = {
    languageRules: LanguageRuleSetId,
    retainInactiveRegions: True,
    expansionDepthLimit: UInt32,
    expandedTokenLimit: UInt64,
    includeDepthLimit: UInt32
}

SyntaxFeatureId = QualifiedName

SyntaxFeatureDescriptor = {
    id: SyntaxFeatureId,
    spelling: Utf8String,
    role: FixedGrammarWord | ContextualGrammarWord | RegisteredGrammarExtension,
    production: Option<ProductionId>,
    rule: RuleId
}

SyntaxFeatureSet = {
    languageRules: LanguageRuleSetId,
    features: CanonicallyOrderedMap<SyntaxFeatureId, SyntaxFeatureDescriptor>,
    revision: ContentId<SemanticValue>
}

ParseOptions = {
    preserveAmbiguities: Bool,
    parseInactiveRegionsSpeculatively: Bool,
    recoveryActionLimit: UInt32,
    ambiguityAlternativeLimit: UInt32,
    nestingDepthLimit: UInt32
}
```

Each function is independently callable. `LexPhysical` does not require a name pool or compiler
session. `Parse` does not receive a semantic visitor, declaration table, or mutable scope.

All option/feature fields participate in the corresponding query key. `revision` resolves to and
verifies the exact canonical feature-descriptor bytes under chapter 1's `ContentId` rule; it is not
a bare hash. Resource limits are deterministic semantic recovery inputs, never wall-clock budgets.
The literal `True` fields state required losslessness rather than caller-selectable modes.

## Source decoding and physical fidelity

The current compiler decodes input and strips a BOM before allocating source locations, so current
offsets refer to decoded UTF-8 rather than original file bytes. The replacement stores both views
when decoding is required. `SourceDocument` has the single authoritative schema in chapter 3; the
lexer consumes that exact physical/decoded pair.

`LEX-SRC-001`: Diagnostics and grammar operate on decoded UTF-8 byte offsets. Identity formatting
of an unmodified document writes `physicalBytes`; formatting an edited document writes UTF-8 unless
the caller selects a supported output encoding.

`LEX-SRC-002`: Invalid encoding sequences produce explicit decoding-error spans and replacement
scalar values in the decoded snapshot; no source bytes disappear from `SourceDocument`.

This closes the “byte-exact versus decoded-text-exact” item in the compatibility ledger while
preserving today's semantic offset domain.

## Token vocabulary

The fixed token-kind vocabulary is:

```text
special:      Unknown EndOfFile Invalid
content:      Identifier IntegerLiteral FloatingPointLiteral StringLiteral CharLiteral
trivia:       WhiteSpace NewLine LineComment BlockComment
separators:   ; , . .. ... { } [ ] ( ) ? : @ $ $$ # ## :: #?
operators:    = + - * / % ! ~ << >> == != > < >= <= && || & | ^ ++ --
compound:     += -= *= /= %= <<= >>= &= |= ^= -> =>
```

The physical lexer additionally marks documentation comments with `Trivia.isDocumentation` and
classifies line continuations as a `Trivia.kind` while retaining the current broad token vocabulary.
`Unknown` is an internal sentinel; `Invalid` is a physical token with source text and a diagnostic.

All language words are initially `Identifier` tokens. The parser recognizes fixed and contextual
spellings through `SyntaxFeatureSet`. Builtin type and function names remain ordinary declarations
in the standard environment.

`LEX-TOK-001`: Longest matching punctuation wins. In a generic closing context, `>>` remains one
physical/expanded token and is exposed to the grammar CST as two zero-copy
`ExpandedTokenSliceId` leaves whose spelling ranges partition the parent token. The parent token is
never mutated.

`LEX-TOK-002`: Every non-trivia token stores an ordered, non-empty set of physical source pieces and
a lazily decoded logical spelling/value. Backslash-newline splicing affects the logical spelling
only; all pieces and intervening trivia remain intact.

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

The physical grammar distinguishes spelling from semantic validation:

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

`LEX-LIT-001`: The token stores exact spelling, decoded value or decode failure, radix/format, and
suffix spelling. Numeric negation is a prefix expression, not part of the literal token.

`LEX-LIT-002`: Adjacent string literal concatenation is a parser/semantic construct. Each physical
literal remains independently addressable with its own spelling and trivia.

## Trivia ownership

Trivia gaps are defined in chapter 3. Classification rules are:

- horizontal whitespace and other non-newline spacing → `Whitespace`;
- each source newline sequence → `Newline` with exact raw spelling;
- backslash followed by a newline sequence → `LineContinuation`;
- `//` through its terminating newline boundary → `LineComment` plus the separate newline trivia;
- `/* ... */` → `BlockComment`; comments do not nest in compatibility mode; and
- a comment matching a versioned documentation marker retains `LineComment`/`BlockComment` and sets
  `isDocumentation=true`.

A `LineContinuation` may be an ordinary inter-token gap item or interstitial trivia inside one
logical token. For example, an identifier split by backslash-newline owns the token pieces on both
sides and references the continuation between them. The ordered physical-slice tape still owns each
byte exactly once; no contiguous token range is invented across the removed newline.

`LEX-TRI-001`: Unterminated block comments produce an `Invalid`/error-bearing comment item spanning
to EOF and diagnostic `unterminated-block-comment`. The current lexer has a TODO and often relies on
a later parser error; this is an intentional diagnostic improvement.

Documentation attachment is a semantic view over token gaps:

```text
LeadingDocumentation(declToken) = maximal documentation-comment group in leadingGap
                                  not separated by a blank-line boundary
TrailingDocumentation(token) = documentation comment in trailingGap on the same logical line
```

Storage never moves a comment from one gap to another to implement attachment.

## Preprocessor syntax

The physical preprocessor tree recognizes these directive spellings:

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
PpNode = TextRegion
       | IncludeDirective
       | DefineDirective
       | UndefDirective
       | ConditionalGroup
       | DiagnosticDirective
       | LineDirective
       | PragmaDirective
       | LanguageDirective
       | UnknownDirective
```

`PP-TREE-001`: All directives, delimiters, line endings, inactive branches, and text regions occur
exactly once in the physical ownership projection of `PreprocessorTree`.

`PP-EXP-001`: Macro expansion produces an origin DAG containing definition token, invocation,
argument origin, stringize/paste operation, and nested expansion steps. Recursion suppression is an
explicit expansion decision attached to the invocation.

`PP-EXP-002`: Stringization uses the exact physical spelling and standardized whitespace folding
defined by the preprocessor rule; the physical trivia is not reconstructed from a one-bit flag.

`PP-EXP-003`: Token paste concatenates semantic operand spellings, re-lexes exactly one resulting
preprocessing token, and records both operand origins. Failure produces an invalid expanded token
and retains the paste node.

`PP-INC-001`: Each included file has a separate `SourceDocument`, preprocessor tree, and grammar
CST. The including tree contains an `IncludeEdge`; it does not physically nest the included file's
tokens into the formatter tree. The expanded semantic view may traverse the edge.

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
normalizeAccessorSpelling("get")      = AccessorRole.Get
normalizeAccessorSpelling("set")      = AccessorRole.Set
normalizeAccessorSpelling("constref") = AccessorRole.Ref(ReadAccess)
normalizeAccessorSpelling("ref")      = AccessorRole.Ref(ReadWriteAccess)
```

`PAR-ACC-001`: `constref` is a soft keyword only in the accessor-name position of a property or
subscript accessor declaration. It maps exactly to `AccessorRole.Ref(ReadAccess)`; `ref` maps
exactly to `AccessorRole.Ref(ReadWriteAccess)`. The two spellings may occur in the same accessor
block, retain distinct CST tokens, and normalize to distinct map keys. Duplicate detection compares
the complete normalized role, including its access index.

`PAR-ACC-002`: The unbracketed accessor spelling `constref`, the parameter modifier
`__constref`, and the callable/receiver attribute `[constref]` are three distinct productions.
`__constref` is normalized by header checking to `ConstRefMode(locationRequirement)`;
`[constref]` remains an attribute that selects the registered receiver rule; neither can construct
an `AccessorRole`. Conversely, an accessor-name token cannot alter its containing callable's
receiver mode. CST-to-Surface normalization preserves which of the three productions supplied the
token so serialization, formatting, and diagnostics never infer the distinction from spelling
alone.

## Expression precedence and associativity

From lowest to highest:

| Level          | Forms                                                       | Associativity                                          |
| -------------- | ----------------------------------------------------------- | ------------------------------------------------------ | ------- | ---- |
| comma          | `,`                                                         | left (Slang 2026 uses tuple syntax inside parentheses) |
| assignment     | `=` and compound assignment                                 | right                                                  |
| conditional    | `?:`                                                        | right by grammar                                       |
| logical        | `                                                           |                                                        | `, `&&` | left |
| bitwise        | `                                                           | `, `^`, `&`                                            | left    |
| equality       | `==`, `!=`                                                  | left                                                   |
| relational     | `<`, `>`, `<=`, `>=`, `is`, `as`                            | left                                                   |
| shift          | `<<`, `>>`                                                  | left                                                   |
| additive       | `+`, `-`                                                    | left                                                   |
| multiplicative | `*`, `/`, `%`                                               | left                                                   |
| prefix         | registered prefix operators, `new`, keyword prefix forms    | right                                                  |
| postfix        | call, index, member, generic application, postfix operators | left                                                   |

`PAR-EXP-001`: Operator spellings resolve through the standard environment after parsing. Parsing
constructs an operator application syntax node and does not select a builtin or user declaration.

## Named ambiguities

The CST contains explicit alternatives for these compatibility conflicts:

```text
AmbiguousGenericOrRelational
AmbiguousCastOrParenthesized
AmbiguousDeclarationOrExpressionStatement
AmbiguousTypeOrValueGenericArgument
AmbiguousModernOrTraditionalParameter
```

Each node owns the shared expanded-token range once and stores non-owning alternative parse
descriptors over that range. Alternatives may refer to token IDs and child ranges, but are not
green subtrees in the ownership projection and cannot duplicate leaves.

`PAR-AMB-001`: Modern Slang resolves an ambiguity by syntax, dialect, and language version only.
Legacy HLSL compatibility may request name-classification facts during the later
`ResolveSyntaxAmbiguity` query, but initial parsing still succeeds without them.

`PAR-AMB-002`: Resolution produces a `SurfaceAST` origin pointing at the ambiguous CST and records
the chosen alternative plus rule ID. If more than one alternative remains valid, binding emits an
ambiguity diagnostic instead of using declaration order accidentally.

### Generic closing tokens

The parser may view physical `>>` as two closers when inside generic arguments. The first slice
covers the first spelling byte and owns no unique trivia; the second covers the second byte and
exposes the parent token's trailing gap. In expression shift context the same token is one
`>>` leaf.

### Syntax declarations

The grammar is parameterized by an immutable `SyntaxFeatureSet`. Builtin entries corresponding to
today's `g_parseSyntaxEntries` are versioned standard-environment data.

Source-defined `syntax` declarations are an unresolved compatibility feature. The proposed safe
model is:

1. `syntax` declarations always parse using fixed grammar;
2. `BuildSyntaxEnvironment` creates a persistent environment for subsequent declaration ranges;
3. compatibility parsing may interpret an identifier through that environment; and
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

Recovery emits only:

```text
MissingToken(expected, anchor, rule)
SkippedTokens(tokens, rule)
UnexpectedConstruct(node, expectedCategory, rule)
```

`PAR-REC-001`: A recovery action must consume a token, insert a missing token, or return to a caller
that will do so. Progress is a structural invariant; there is no global “advance after 64 tries”
escape hatch.

`PAR-REC-002`: A missing closer is inserted before a token in the production's follow set. A real
unexpected closer is never consumed as the missing closer of another delimiter level.

`PAR-REC-003`: Skipped tokens remain in source order under the smallest enclosing syntax node whose
recovery rule consumed them.

`PAR-REC-004`: At EOF, every open delimiter produces one missing-token node and related opening
origin. Recovery terminates in time linear in remaining token count for a fixed grammar.

## CST-to-surface normalization

Parsing does not perform semantic desugaring. In particular:

- `if (let ...)` remains `IfLetSyntax`; it is not immediately rewritten into temporaries;
- cbuffer/tbuffer syntax remains a dedicated surface declaration rather than parser-synthesized
  struct/wrapper/variable declarations;
- default interface methods remain their written generic shape and are never reparsed from copied
  tokens;
- declaration/expression ambiguities remain explicit until binding; and
- function bodies have immutable CST roots, whether parsed eagerly or on demand.

`PAR-NRM-001`: CST-to-SurfaceAST may remove punctuation from structural fields, but every output node
has `Parsed(cstId)` provenance and every written distinction needed by diagnostics remains a field
or is reachable from its CST.

## Machine-checkable completeness

The eventual grammar/schema source generates token enums, syntax feature tables, CST kinds, parser
production IDs, reflection metadata, documentation tables, and test skeletons. CI checks:

1. every token kind is classified by the lexical schema;
2. every builtin syntax spelling maps to a grammar production or declared extension hook;
3. every parser spelling and dialect/version gate maps back to the grammar;
4. every CST kind has a production/recovery constructor;
5. every grammar alternative has positive and recovery witnesses;
6. undeclared FIRST/FOLLOW conflicts and backtracking fail generation; and
7. differential parsing covers repository `.slang`, standard-module, prelude, and test sources.

The required properties are exact physical-token concatenation, identity-format round trip, no
token loss on invalid input, full/incremental parse equivalence, and CST serialization stability.

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
