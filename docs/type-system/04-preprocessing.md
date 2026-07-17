# Preprocessing

Preprocessing is the first nontrivial instance of the immutable representation-translation model
from chapter 3. It starts with a flat, lossless list of lexical elements, adds concrete structure
for directives and macro definitions, and then produces a new concrete-syntax representation in
which active macro invocations and includes have been replaced by their expansion results. Every
input representation remains available.

The chapter specifies preprocessing independently of parsing and semantic checking. In particular,
the preprocessor does not consult declaration scopes, types, generic declarations, or AST nodes.

## Specification relations are not compiler objects

This chapter writes a transition as a judgment such as:

```text
I ; O ⊢ Σ ; input ⇓ output ; Σ' ; diagnostics
```

It means that, for immutable inputs `I` and options `O`, processing `input` in state `Σ` produces
`output`, a new state `Σ'`, and diagnostics. The semicolon-separated products are mathematical
notation used to define and test the function. They are not a request to allocate a
`PreprocessorTransition`, `PreprocessorStep`, `CSTRewrite`, or similar runtime entity.

An implementation normally materializes only:

- the input and output CST snapshots;
- immutable state values or their content IDs;
- the direct provenance stored on produced CST nodes and tokens;
- diagnostics and declared dependency results; and
- derived values, such as compiled `MacroDefinition::Op` values, when a cache is useful.

The implementation may evaluate a rule with ordinary calls, an explicit work stack, or scheduler
queries. Those evaluation details do not participate in serialization or semantic identity.

`PP-MOD-001`: No successful preprocessing result depends on the identity, allocation order, or
retention of an operation or transition object. Re-evaluating a judgment with equal immutable
inputs produces structurally equal output, state, diagnostics, dependencies, and provenance.

## Phase boundaries and complete query shapes

The public phase boundary is:

```text
Lex(sourceView: SourceViewId, options: LexOptions)
    -> CheckResult<TokenList>

BuildLexedCST(tokens: TokenListId, lexicalContext: LexicalContextId)
    -> CSTSnapshot<Lexed>

StructurePreprocessor(input: CSTSnapshot<Lexed>, options: PreprocessorOptions)
    -> CheckResult<CSTSnapshot<PreprocessorStructured>>

ExpandPreprocessor(unit: PreprocessorUnitInput,
                   includeSystem: IncludeSystem,
                   includeSystemRevision: IncludeSystemRevision,
                   builtinMacros: BuiltinMacroProvider,
                   builtinMacroProviderRevision: BuiltinMacroProviderRevision,
                   features: PreprocessorFeatureSet,
                   featureSetRevision: PreprocessorFeatureSetRevision,
                   directiveProvider: PreprocessorDirectiveProvider,
                   directiveProviderRevision: PreprocessorDirectiveProviderRevision,
                   initial: PreprocessorPersistentState,
                   options: PreprocessorOptions)
    -> CheckResult<PreprocessorExpansionResult>

PreprocessorUnitInput = {
    snapshot: CSTSnapshot<PreprocessorStructured>,
    uniqueIdentity: IncludeUniqueIdentity
}

PreprocessorExpansionResult = {
    snapshot: CSTSnapshot<MacroExpanded>,
    initialPersistentState: PreprocessorPersistentStateId,
    entryState: PreprocessorStateId,
    exitState: PreprocessorStateId,
    finalPersistentState: PreprocessorPersistentStateId,
    interpretedViews: NodeMap<SourceViewId, SourceViewId>,
    dependencies: CanonicallyOrderedSet<PreprocessorDependency>
}

PreprocessorOptions = {
    includeLexPolicy: IncludeLexPolicy,
    resourceLimits: PreprocessorResourceLimits
}

IncludeLexPolicy = {
    recognizeLineContinuations: Bool,
    preserveInvalidTokens: True
}

PreprocessorDependency =
    IncludeResolutionDependency {
        request: IncludeSystemRequest,
        includeSystemRevision: IncludeSystemRevision,
        outcome: IncludeSystemResult
    }
  | BuiltinMacroProviderDependency(revision: BuiltinMacroProviderRevision)
  | FeatureSetDependency(revision: PreprocessorFeatureSetRevision)
  | RegisteredDirectiveProviderDependency(
        revision: PreprocessorDirectiveProviderRevision)

IncludeSystemRevision = ContentId<SchemaValue>
BuiltinMacroProviderRevision = ContentId<SchemaValue>
PreprocessorFeatureSetRevision = ContentId<SchemaValue>
PreprocessorDirectiveProviderRevision = ContentId<SchemaValue>
```

Each provider is a read-only service passed together with an explicit content revision. Equal
requests at an equal revision must return equal typed results. All four revisions participate in
the expansion query key and are also reported as dependencies; a service object address never
does. A provider must reject a request whose revision it cannot serve rather than silently answer
from its current mutable state. The provider request and result schemas are defined below.

`Lex` produces exactly one `TokenList = NodeList<Token | Trivia>`. `BuildLexedCST` wraps that list
in one `TokenizedSource` non-terminal whose terminal projection is a bijection with the list. The
lexer does not attach comments to AST nodes, discard whitespace, or identify macro invocations.

`StructurePreprocessor` is environment-independent. It groups directive lines, definitions,
conditional groups, and ordinary text into typed terminal and non-terminal nodes. It preserves the
same flat list and does not decide which identifiers name macros.

`ExpandPreprocessor` performs the source-ordered, stateful scan. When the current environment says
that an identifier is a macro, invocation recognition first publishes a small immutable
`PreprocessorStructured` CST fragment rooted at `MacroInvocation`, with exact name, delimiter, and
argument terminals from the stream being scanned. Expansion then publishes a `MacroExpansion`,
`SuppressedExpansion`, or `FailedExpansion` node in the next `MacroExpanded` representation; its
`expandedFrom` field refers directly to that invocation. The fragment is representation data, not
a transition or rewrite-operation object, and recognition never mutates the original structured
input. An include use recursively obtains the included file's own lexed, structured, and expanded
snapshots and publishes an
`IncludeExpansion`, `SuppressedIncludeExpansion`, or `FailedIncludeExpansion` node.

The expanded root's structural path contains the expansion node where the invocation occurred.
The invocation node is retained through `expandedFrom`, so tools can traverse either the emitted
result or the exact call spelling without mutating the invocation or retaining a separate rewrite log.

The final snapshot owns one flat primary `TokenList` in expansion order. Its CST root exposes the
nodes that produced that list, while its predecessor graph retains all source directives, inactive
branches, definitions, invocation spellings, and included-file CSTs. A derived `ActiveTokenView`
filters the primary list; it is not another owning token sequence.

`PP-MOD-002`: The terminal projection of the lexed root reproduces the source exactly. Identity
formatting of a structured or expanded representation follows predecessor fields back to that
lexed root. Expansion formatting uses the final primary list. These are different, explicitly
named views over one provenance graph, not competing trivia stores.

## Preprocessor names and hygiene

In a hygienic macro system, identifiers carry marks or scopes that prevent a name written in a
macro definition from accidentally capturing, or being captured by, a name at the invocation
site. Such a mark is often called a hygiene identity.

Slang preprocessing is deliberately textual and unhygienic. It performs no capture avoidance,
identifier renaming, declaration lookup, or binding preservation. An identifier emitted from a
macro is an ordinary identifier spelling and is interpreted by later parsing and semantic checking
in its output context. Therefore the preprocessor has no hygiene-identity field.

```text
PreprocessorName = {
    text: InternedString
}
```

`PreprocessorName` is decoded identifier text under the active lexical language rules. Its equality
does not include source location, token provenance, pointer identity, an AST `NameClass`, or a
hygiene mark. Definition identity is retained separately for recursion suppression and provenance;
it does not alter name equality.

For example:

```text
#define USE_X() x
void f() { int x = 1; USE_X(); }
```

The emitted `x` can refer to the local `x`. The preprocessor neither guarantees nor prevents that
capture.

`PP-NAM-001`: Macro definition, `#undef`, invocation, `defined`, and builtin-name lookup compare
only `PreprocessorName.text` under the selected lexical language rules.

`PP-NAM-002`: `TokenOrigin` records where an emitted identifier came from, but provenance never
changes identifier equality or later lookup. Adding hygiene would be a new, versioned language
feature rather than an interpretation of existing provenance.

## Structured preprocessor CST

The initial structured representation has the following principal shapes. Every punctuation or
keyword mentioned by a production is an explicit terminal field. `TokenListRange` fields identify
exact contiguous written spelling, including trivia, without taking ownership away from the flat
list.

The core directive names are:

```text
#if #ifdef #ifndef #elif #else #endif
#include #define #undef
#warning #error #line #pragma
#language #lang #version #extension
```

An unrecognized name after a directive introducer forms `UnknownDirective`; a missing or invalid
name forms `PreprocessorRecovery`. Known pragmas include `once` and `warning`, while other pragma
names are offered to the versioned directive provider.

```text
SourcePreprocessorElementCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, SourcePreprocessorElement>

MacroDefinitionParamCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroDefinitionParam>
MacroDefinitionParameterTailCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroDefinitionParameterTail>
MacroReplacementElementCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroReplacementElement>

PreprocessorUnitFields = {
    elements: NodeList<SourcePreprocessorElementCSTNodeId>,
    endOfFile: TerminalNodeId<PreprocessorStructured>
}

SourcePreprocessorElement =
    TextRegion
  | DefineDirective
  | UndefDirective
  | IncludeDirective
  | ConditionalGroup
  | DiagnosticDirective
  | LineDirective
  | PragmaDirective
  | LanguageDirective
  | UnknownDirective
  | PreprocessorRecovery

TextRegionFields = {
    elements: NonEmpty<TerminalNodeId<PreprocessorStructured>>,
    writtenRange: TokenListRange
}

DefineDirectiveFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    defineKeyword: TerminalNodeId<PreprocessorStructured>,
    definition: NonTerminalNodeId<PreprocessorStructured, MacroDefinition>,
    lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
}

MacroDefinitionFields = {
    name: TerminalNodeId<PreprocessorStructured>,
    parameterClause: Option<
        NonTerminalNodeId<PreprocessorStructured, MacroDefinitionParameterClause>>,
    replacement: NodeList<MacroReplacementElementCSTNodeId>,
    writtenRange: TokenListRange
}

MacroDefinitionParameterClauseFields = {
    leftParenthesis: TerminalNodeId<PreprocessorStructured>,
    parameters: Option<MacroDefinitionParameterSequence>,
    rightParenthesis: TerminalNodeId<PreprocessorStructured>
}

MacroDefinitionParameterSequence = {
    first: MacroDefinitionParamCSTNodeId,
    remaining: NodeList<MacroDefinitionParameterTailCSTNodeId>
}

MacroDefinitionParameterTailFields = {
    comma: TerminalNodeId<PreprocessorStructured>,
    parameter: MacroDefinitionParamCSTNodeId
}

MacroDefinitionParamFields = {
    form: OrdinaryMacroParameter {
              name: TerminalNodeId<PreprocessorStructured>
          }
        | NamedVariadicMacroParameter {
              name: TerminalNodeId<PreprocessorStructured>,
              ellipsis: TerminalNodeId<PreprocessorStructured>
          }
        | AnonymousVariadicMacroParameter {
              ellipsis: TerminalNodeId<PreprocessorStructured>
          }
}

MacroReplacementElement =
    MacroRawSpan
  | MacroParamReference
  | MacroStringize
  | TokenPaste
  | PreprocessorRecovery

MacroRawSpanFields = {
    terminals: NonEmpty<TerminalNodeId<PreprocessorStructured>>,
    writtenRange: TokenListRange
}

MacroParamReferenceFields = {
    parameterName: TerminalNodeId<PreprocessorStructured>
}

MacroStringizeFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    parameterName: TerminalNodeId<PreprocessorStructured>
}

TokenPasteFields = {
    doublePound: TerminalNodeId<PreprocessorStructured>
}

UndefDirectiveFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    undefKeyword: TerminalNodeId<PreprocessorStructured>,
    name: TerminalNodeId<PreprocessorStructured>,
    trailing: NodeList<TerminalNodeId<PreprocessorStructured>>,
    lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
}

IncludeDirectiveFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    includeKeyword: TerminalNodeId<PreprocessorStructured>,
    operand: NonEmpty<TerminalNodeId<PreprocessorStructured>>,
    lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
}

PreprocessorDirectiveFields = {
    form: IfDirective {
              pound: TerminalNodeId<PreprocessorStructured>,
              ifKeyword: TerminalNodeId<PreprocessorStructured>,
              operand: NodeList<TerminalNodeId<PreprocessorStructured>>,
              lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
          }
        | IfdefDirective {
              pound: TerminalNodeId<PreprocessorStructured>,
              ifdefKeyword: TerminalNodeId<PreprocessorStructured>,
              name: TerminalNodeId<PreprocessorStructured>,
              trailing: NodeList<TerminalNodeId<PreprocessorStructured>>,
              lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
          }
        | IfndefDirective {
              pound: TerminalNodeId<PreprocessorStructured>,
              ifndefKeyword: TerminalNodeId<PreprocessorStructured>,
              name: TerminalNodeId<PreprocessorStructured>,
              trailing: NodeList<TerminalNodeId<PreprocessorStructured>>,
              lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
          }
        | ElifDirective {
              pound: TerminalNodeId<PreprocessorStructured>,
              elifKeyword: TerminalNodeId<PreprocessorStructured>,
              operand: NodeList<TerminalNodeId<PreprocessorStructured>>,
              lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
          }
        | ElseDirective {
              pound: TerminalNodeId<PreprocessorStructured>,
              elseKeyword: TerminalNodeId<PreprocessorStructured>,
              trailing: NodeList<TerminalNodeId<PreprocessorStructured>>,
              lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
          }
        | EndifDirective {
              pound: TerminalNodeId<PreprocessorStructured>,
              endifKeyword: TerminalNodeId<PreprocessorStructured>,
              trailing: NodeList<TerminalNodeId<PreprocessorStructured>>,
              lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
          }
}

ConditionalGroupFields = {
    firstBranch: NonTerminalNodeId<PreprocessorStructured, ConditionalBranch>,
    elifBranches: NodeList<NonTerminalNodeId<PreprocessorStructured, ConditionalBranch>>,
    elseBranch: Option<NonTerminalNodeId<PreprocessorStructured, ConditionalBranch>>,
    endifDirective: NonTerminalNodeId<PreprocessorStructured, PreprocessorDirective>
}

ConditionalBranchFields = {
    delimiter: NonTerminalNodeId<PreprocessorStructured, PreprocessorDirective>,
    elements: NodeList<SourcePreprocessorElementCSTNodeId>
}

DiagnosticDirectiveFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    diagnosticKeyword: TerminalNodeId<PreprocessorStructured>,
    message: NodeList<TerminalNodeId<PreprocessorStructured>>,
    lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
}

LineDirectiveFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    lineKeyword: TerminalNodeId<PreprocessorStructured>,
    operand: NodeList<TerminalNodeId<PreprocessorStructured>>,
    lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
}

PragmaDirectiveFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    pragmaKeyword: TerminalNodeId<PreprocessorStructured>,
    operand: NodeList<TerminalNodeId<PreprocessorStructured>>,
    lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
}

LanguageDirectiveFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    languageKeyword: TerminalNodeId<PreprocessorStructured>,
    operand: NodeList<TerminalNodeId<PreprocessorStructured>>,
    lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
}

UnknownDirectiveFields = {
    pound: TerminalNodeId<PreprocessorStructured>,
    name: TerminalNodeId<PreprocessorStructured>,
    operand: NodeList<TerminalNodeId<PreprocessorStructured>>,
    lineEnd: Option<TerminalNodeId<PreprocessorStructured>>
}

PreprocessorRecoveryFields = {
    consumed: NonEmpty<TerminalNodeId<PreprocessorStructured>>,
    missing: NodeList<TerminalNodeId<PreprocessorStructured>>
        where every terminal value is MissingTerminal,
    writtenRange: TokenListRange
}
```

`ConditionalGroup.firstBranch.delimiter.form` must be `IfDirective`, `IfdefDirective`, or
`IfndefDirective`; every element of `elifBranches` must use `ElifDirective`; `elseBranch`, when
present, must use `ElseDirective`; and `endifDirective.form` must be `EndifDirective`. The grouped
shape gives every delimiter one structural parent, so the terminal projection does not duplicate
the opening or closing directive. `diagnosticKeyword` is constrained to `warning` or `error`, and
`languageKeyword` to `language`, `lang`, `version`, or `extension`. No directive is stored as an
untyped string.

`StructurePreprocessor` recognizes a directive introducer only when `#` is the first non-trivia
token on a logical line. A line continuation has already joined its physical lines before this
test. A `#` elsewhere belongs to `TextRegion`. The directive extends through the next unspliced
newline or EOF. The newline remains a `Trivia` element in the flat list and may simultaneously be
referenced by the directive's `lineEnd` terminal.

Conditional grouping is based only on directive spelling and nesting. It does not evaluate an
expression. An unmatched `#elif`, `#else`, or `#endif`, a repeated `#else`, or an unclosed group
produces a `PreprocessorRecovery` node with the exact offending terminals and missing-terminal
anchors. Following elements remain structurally accessible.

For a definition, `parameterClause` is present only if `(` immediately follows the macro name with
no intervening `Trivia`. Thus `#define F(x) x` is function-like and `#define F (x) x` is
object-like with replacement spelling `(x) x`. Invocation recognition has a different rule:
ordinary trivia may occur between a known function-like macro name and its `(`.

`PP-STR-001`: Structuring consumes every `Token | Trivia` element exactly once into the terminal
projection of the structured root. Non-terminals may refer to those terminals but never copy or
re-own their values.

`PP-STR-002`: Initial structuring is a pure function of the lexed snapshot and preprocessing syntax
options. Macro bindings, conditional values, include resolution, and feature queries cannot affect
its result.

`PP-STR-003`: Inactive branches, unknown directives, malformed directives, comments, and directive
line endings remain concrete syntax. Semantic inactivity never deletes source spelling.

`PP-STR-004`: `MacroDefinitionParameterClause.parameters = None` denotes the empty parameter list;
otherwise `first` exists and every comma is paired with exactly one following parameter. Each
`MacroDefinitionParam.form` is exactly one of ordinary, named variadic, or anonymous variadic, so
neither an absent name-and-ellipsis pair nor an independent optional-field combination is
representable.

## Immutable environment and complete preprocessing state

The versioned providers expose closed, mockable request/result relations. They return descriptions;
the preprocessor creates CST nodes, terminal origins, and diagnostics from those descriptions.
Provider code never receives a mutable state object or a CST builder.

```text
BuiltinMacroRule =
    BuiltinLine
  | BuiltinFile
  | RegisteredBuiltin(rule: RuleId)

BuiltinMacroRuleId = ContentId<BuiltinMacroRule>

BuiltinMacroContextField =
    InitiatingSourceView
  | InitiatingPhysicalRange
  | InitiatingLogicalLocation
  | LanguageRules

PreprocessorPresumedLocation = {
    path: Utf8String,
    line: UInt32,
    column: UInt32
}

BuiltinMacroContextValue<InitiatingSourceView> = SourceViewId
BuiltinMacroContextValue<InitiatingPhysicalRange> = SourceRange
BuiltinMacroContextValue<InitiatingLogicalLocation> = PreprocessorPresumedLocation
BuiltinMacroContextValue<LanguageRules> = LanguageRuleSetId

BuiltinMacroContext =
    DependentNodeMap<F: BuiltinMacroContextField,
                     F,
                     BuiltinMacroContextValue<F>>

BuiltinMacroDefinition = {
    name: PreprocessorName,
    flavor: ObjectLike | FunctionLike,
    parameterNames: NodeList<PreprocessorName>,
    variadic: Bool,
    rule: BuiltinMacroRuleId,
    requiredContext: CanonicallyOrderedSet<BuiltinMacroContextField>
}

BuiltinMacroDefinitionId = ContentId<BuiltinMacroDefinition>

PreprocessorTokenDescription = {
    type: TokenType where not isTrivia(type) and type != EndOfFile,
    logicalSpelling: Text
}

BuiltinMacroCatalog =
    CanonicallyOrderedMap<PreprocessorName, BuiltinMacroDefinition>

BuiltinMacroExpansionRequest = {
    definition: BuiltinMacroDefinitionId,
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    context: BuiltinMacroContext
}

BuiltinMacroExpansionDescription = {
    rule: BuiltinMacroRuleId,
    tokens: NodeList<PreprocessorTokenDescription>
}

GetBuiltinMacroCatalog(provider: BuiltinMacroProvider,
                       revision: BuiltinMacroProviderRevision)
    -> BuiltinMacroCatalog

ExpandBuiltinMacro(provider: BuiltinMacroProvider,
                   revision: BuiltinMacroProviderRevision,
                   request: BuiltinMacroExpansionRequest)
    -> CheckResult<BuiltinMacroExpansionDescription>

PreprocessorFeatureQuery = {
    name: PreprocessorName,
    languageRules: LanguageRuleSetId
}

PreprocessorFeatureQueryResult = Supported | Unsupported | Unknown

QueryPreprocessorFeature(features: PreprocessorFeatureSet,
                         revision: PreprocessorFeatureSetRevision,
                         query: PreprocessorFeatureQuery)
    -> PreprocessorFeatureQueryResult

RegisteredDirectiveStateSlot = QualifiedName

RegisteredDirectiveDefinition = {
    name: QualifiedName,
    operandGrammar: ContentId<SchemaValue>,
    stateSlot: RegisteredDirectiveStateSlot,
    stateSchema: ContentId<SchemaValue>,
    inactiveBehavior: IgnoreWithoutCallingProvider,
    rule: RuleId
}

RegisteredDirectiveDefinitionId = ContentId<RegisteredDirectiveDefinition>

RegisteredDirectiveLookupResult =
    Registered(definition: RegisteredDirectiveDefinition)
  | Unregistered

RegisteredDirectiveRequest = {
    definition: RegisteredDirectiveDefinitionId,
    directive: NonTerminalNodeId<PreprocessorStructured,
        PragmaDirective | LanguageDirective | UnknownDirective>,
    operand: TokenListRange,
    sourceView: SourceViewId,
    languageRules: LanguageRuleSetId,
    currentState: SchemaValue
}

RegisteredDirectiveResult = {
    replacementState: SchemaValue
}

LookupRegisteredDirective(provider: PreprocessorDirectiveProvider,
                          revision: PreprocessorDirectiveProviderRevision,
                          name: QualifiedName)
    -> RegisteredDirectiveLookupResult

ApplyRegisteredDirective(provider: PreprocessorDirectiveProvider,
                         revision: PreprocessorDirectiveProviderRevision,
                         request: RegisteredDirectiveRequest)
    -> CheckResult<RegisteredDirectiveResult>
```

`GetBuiltinMacroCatalog` is canonical by name, and every value's content identity is its
`BuiltinMacroDefinitionId`. `ExpandBuiltinMacro` receives exactly the context fields declared by
the definition; a missing or extra field is an invalid provider result. The returned token
descriptions have no physical spelling. The preprocessor gives them direct builtin provenance when
it materializes terminal nodes.

`QueryPreprocessorFeature` is total. `Supported` evaluates to one, while `Unsupported` and
`Unknown` evaluate to zero; a language rule may diagnose `Unknown`, but the provider does not emit
that diagnostic as a side effect. A registered directive handler receives only the value in its
declared state slot. On success the preprocessor schema-validates `replacementState` and replaces
that one slot; no other `PreprocessorDirectiveState` field can be changed by the handler. Inactive
registered directives are preserved without calling the provider.

An unavailable revision or a provider result that violates its schema is an infrastructure task
failure as defined in chapter 11. It is not a source-language `Recovered` result. These contracts
make a map-backed test double semantically equivalent to a production provider.

Macro lookup uses a persistent environment with explicit `#undef` tombstones:

```text
PredefinedMacroDefinitionId = ContentId<PredefinedMacroDefinition>

PredefinedMacroDefinition = {
    name: PreprocessorName,
    flavor: ObjectLike | FunctionLike,
    parameterNames: NodeList<PreprocessorName>,
    variadic: Bool,
    replacement: TokenListId,
    origin: PredefinedMacroOrigin
}

PredefinedMacroOrigin =
    CommandLineDefinition(index: UInt32)
  | APIDefinition(key: Utf8String)

MacroDefinitionRef =
    SourceMacroDefinition(
        NonTerminalNodeId<PreprocessorStructured, MacroDefinition>)
  | BuiltinMacroDefinition(BuiltinMacroDefinitionId)
  | PredefinedMacroDefinition(PredefinedMacroDefinitionId)

MacroBinding =
    Defined(definition: MacroDefinitionRef)
  | Undefined(undef: NonTerminalNodeId<PreprocessorStructured, UndefDirective>)

preprocessor::Environment = {
    parent: Option<preprocessor::EnvironmentId>,
    bindings: NodeMap<PreprocessorName, MacroBinding>
}

preprocessor::EnvironmentId = ContentId<preprocessor::Environment>

lookup(environment, name) =
    first binding for name while following parent links;
    Defined(d) yields d;
    Undefined(_) yields NotFound and stops the search;
    no binding yields NotFound

define(environment, name, definition) =
    Environment(parent = Some(environment), bindings = { name -> Defined(definition) })

undefine(environment, name, directive) =
    Environment(parent = Some(environment), bindings = { name -> Undefined(directive) })

boundNames(environment) =
    canonical union of every bindings-map key along the parent chain

visibleDefinedNames(environment) =
    CanonicallyOrderedSet {
        name in boundNames(environment) |
        lookup(environment, name) = Defined(_)
    }
```

An implementation may compact equivalent environment chains, but lookup must behave exactly as the
equations above. It may not mutate an environment visible to an earlier state.
`PredefinedMacroDefinition.replacement` contains only replacement-list `Token | Trivia` elements,
never an EOF element; every element already has a valid origin appropriate to its command-line or
API definition. Its parameter/flavor invariants are the same as a compiled source definition.

The complete state that can change the meaning of later input is:

```text
IncludeUniqueIdentity = Utf8String

PreprocessorInputFrame = {
    sourceView: SourceViewId,
    uniqueIdentity: IncludeUniqueIdentity,
    structuredRoot: NonTerminalNodeId<PreprocessorStructured, PreprocessorUnit>,
    includedFrom: Option<
        NonTerminalNodeId<PreprocessorStructured, IncludeDirective>>
}

preprocessor::Conditional = {
    group: NonTerminalNodeId<PreprocessorStructured, ConditionalGroup>,
    parentActive: Bool,
    anyEarlierBranchTaken: Bool,
    currentBranch: UInt32,
    currentBranchActive: Bool,
    sawElse: Bool
}

BusyMacro = {
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    definition: MacroDefinitionRef
}

PragmaWarningSpecifier = Default | Disable | Error | Once | Suppress

WarningTimelineEntry = {
    specifier: PragmaWarningSpecifier,
    location: SourceRange,
    onceConsumedAt: Option<SourceRange>
}

WarningStateTracker = {
    timelines: NodeMap<Int32, NodeList<WarningTimelineEntry>>,
    stack: NodeList<NodeMap<Int32, PragmaWarningSpecifier>>
}

WarningStateTrackerId = ContentId<WarningStateTracker>

PreprocessorLogicalLocationState = {
    lineDirectives: NodeMap<SourceViewId, NodeList<SourceLineDirective>>
}

PreprocessorLogicalLocationStateId = ContentId<PreprocessorLogicalLocationState>

PreprocessorDirectiveState = {
    warningState: WarningStateTrackerId,
    languageRules: LanguageRuleSetId,
    logicalLocations: PreprocessorLogicalLocationStateId,
    registeredDirectiveState: NodeMap<RegisteredDirectiveStateSlot, SchemaValue>
}

PreprocessorResourceUsage = {
    maximumObservedIncludeDepth: UInt32,
    maximumObservedExpansionDepth: UInt32,
    emittedTokenCount: UInt64,
    expandedInvocationCount: UInt64,
    inspectedElementCount: UInt64,
    argumentElementCount: UInt64,
    pasteByteCount: UInt64
}

PreprocessorPersistentState = {
    environment: preprocessor::EnvironmentId,
    pragmaOnceUniqueIdentities: CanonicallyOrderedSet<IncludeUniqueIdentity>,
    loadedSources: NodeMap<IncludeUniqueIdentity, SourceFileSnapshotId>,
    registeredDirectives:
        CanonicallyOrderedMap<QualifiedName, RegisteredDirectiveDefinitionId>,
    directiveState: PreprocessorDirectiveState,
    resourceUsage: PreprocessorResourceUsage
}

PreprocessorPersistentStateId = ContentId<PreprocessorPersistentState>

PreprocessorInitialMacroBinding =
    InitialBuiltinMacro(definition: BuiltinMacroDefinition)
  | InitialPredefinedMacro(definition: PredefinedMacroDefinition)

PreprocessorInitialConfiguration = {
    macros: NodeList<PreprocessorInitialMacroBinding>,
    directiveState: PreprocessorDirectiveState,
    registeredDirectives: NodeList<RegisteredDirectiveDefinition>
}

BuildPreprocessorPersistentState(
    configuration: PreprocessorInitialConfiguration)
    -> CheckResult<PreprocessorPersistentState>

PreprocessorState = {
    environment: preprocessor::EnvironmentId,
    inputStack: NonEmpty<PreprocessorInputFrame>,
    conditionalStack: NodeList<preprocessor::Conditional>,
    busyMacros: NodeList<BusyMacro>,
    pragmaOnceUniqueIdentities: CanonicallyOrderedSet<IncludeUniqueIdentity>,
    loadedSources: NodeMap<IncludeUniqueIdentity, SourceFileSnapshotId>,
    registeredDirectives:
        CanonicallyOrderedMap<QualifiedName, RegisteredDirectiveDefinitionId>,
    directiveState: PreprocessorDirectiveState,
    resourceUsage: PreprocessorResourceUsage
}

PreprocessorStateId = ContentId<PreprocessorState>

ValidatePreprocessorProviderBindings(
    persistent: PreprocessorPersistentState,
    builtinMacros: BuiltinMacroProvider,
    builtinRevision: BuiltinMacroProviderRevision,
    directiveProvider: PreprocessorDirectiveProvider,
    directiveRevision: PreprocessorDirectiveProviderRevision)
    -> Result<Unit, PreprocessorProviderBindingFailure>

BeginPreprocessorUnit(unit: PreprocessorUnitInput,
                      persistent: PreprocessorPersistentState)
    -> Result<PreprocessorState, PreprocessorUnitEntryFailure>

EndPreprocessorUnit(unit: PreprocessorUnitInput,
                    exit: PreprocessorState)
    -> Result<PreprocessorPersistentState, PreprocessorUnitExitFailure>

IncludedUnitBoundary = {
    parentInputDepth: UInt32,
    parentConditionalDepth: UInt32,
    parentBusyDepth: UInt32,
    frame: PreprocessorInputFrame
}

EnterIncludedPreprocessorUnit(parent: PreprocessorState,
                              frame: PreprocessorInputFrame)
    -> Result<{
          state: PreprocessorState,
          boundary: IncludedUnitBoundary
       }, PreprocessorIncludedUnitEntryFailure>

LeaveIncludedPreprocessorUnit(boundary: IncludedUnitBoundary,
                              childExit: PreprocessorState)
    -> Result<PreprocessorState, PreprocessorIncludedUnitExitFailure>

PreprocessorUnitEntryFailure =
    InputRootMismatch
  | LexicalLanguageMismatch
  | InvalidPrimaryUniqueIdentity
  | PrimarySnapshotConflict

PreprocessorUnitExitFailure =
    InputFrameMismatch
  | UnclosedConditionalStack
  | UnrestoredBusyStack

PreprocessorIncludedUnitEntryFailure =
    DuplicateActiveIncludeIdentity
  | IncludedRootMismatch
  | IncludedViewMismatch

PreprocessorIncludedUnitExitFailure =
    IncludedInputFrameMismatch
  | IncludedConditionalScopeLeak
  | IncludedBusyScopeLeak

PreprocessorProviderBindingFailure =
    MissingBuiltinDefinition(BuiltinMacroDefinitionId)
  | ChangedBuiltinDefinition(BuiltinMacroDefinitionId)
  | MissingRegisteredDirective(RegisteredDirectiveDefinitionId)
  | ChangedRegisteredDirective(RegisteredDirectiveDefinitionId)
```

The last input frame is the current file. Active include identities are derived from `inputStack`;
there is no independently mutable cycle-detection set. `loadedSources` freezes the source snapshot
chosen for an identity, so a single query cannot observe two versions of the same include. The
busy-macro chain names exact invocations for diagnostics while suppression compares definition
identity. Current include and expansion depth are derived from `inputStack` and `busyMacros`;
`resourceUsage` retains their maximum observed depths plus cumulative charges.

`BuildPreprocessorPersistentState` content-addresses each builtin and predefined definition and
creates one persistent environment containing them in configuration order. The binding name is
the definition's own `name`; there is no separately supplied name that can disagree. It validates
the value in `directiveState.registeredDirectiveState` for each listed definition against that
definition's `stateSchema`, requires the state map's keys to equal the distinct referenced slots,
starts with empty pragma-once/loaded-source sets, and sets every resource counter to zero. Duplicate
initial definitions follow the same
redefinition-equivalence rule as source definitions.
`ValidatePreprocessorProviderBindings` requires every builtin definition reachable through the
environment to occur identically in `GetBuiltinMacroCatalog`, and every stored registered
directive to equal `LookupRegisteredDirective` at the supplied revisions. `ExpandPreprocessor`
performs this validation before beginning the unit; a mismatch is an infrastructure task failure,
not a source diagnostic. `BeginPreprocessorUnit` derives the primary
`sourceView` from `unit.snapshot.lexicalContext`, pushes exactly one input frame for
`unit.uniqueIdentity`, freezes or validates the source-view snapshot in
`loadedSources[unit.uniqueIdentity]`, and starts with empty conditional and busy stacks.
`EndPreprocessorUnit` requires exactly that frame and empty conditional/busy stacks, removes the
frame, and returns the
six persistent fields from the exit state. Thus a reusable seed never contains a cursor, input
frame, conditional, or busy invocation.

`EnterIncludedPreprocessorUnit` records the three parent stack depths and pushes exactly the given
child frame. The child's conditional-stack suffix is initially empty; the parent's conditional
prefix stays present and determines whether the include directive itself was active. The parent's
busy prefix likewise remains present so macros active at the include site remain suppressed in the
included file. `LeaveIncludedPreprocessorUnit` requires the exact child frame and requires both
stack suffixes to be empty, then removes only that frame. It preserves the child's environment,
pragma-once additions, loaded-source choices, registered-directive catalog, directive state, and
resource usage. These two relations are the only way include expansion crosses a unit boundary.

`finalPersistentState` may be supplied explicitly as the initial state of another unit when the
caller intends a single chained preprocessing session. Starting an independent translation unit
uses a newly built seed. No final state is installed into a process-global preprocessor by
convention.

`PreprocessorOptions` supplies fixed expansion policy and limits. Language rules come from
`PreprocessorPersistentState.directiveState` and must agree with the input lexical context.
`IncludeSystem`, `BuiltinMacroProvider`, feature availability, and registered directive handlers are explicit,
versioned query inputs, not hidden global state. A diagnostic sink is an observer of the returned
diagnostic set and cannot change evaluation.

`PP-STA-001`: Before scanning an element, the state contains every fact that can affect that
element. No macro table, current file, warning mode, logical line, language mode, recursion flag,
pragma-once set, source cache, or resource counter is read from ambient mutable state.

`PP-STA-002`: Processing one element returns a new state. Earlier states, environments, and
snapshots remain unchanged and may be queried concurrently.

`PP-STA-003`: State identity is structural. Scheduler order, address identity, diagnostic emission
order, and cache hits do not participate.

`PP-STA-004`: At primary-unit entry, the sole input frame's `structuredRoot` is the input
snapshot's root,
its `sourceView` equals `resolve(input.lexicalContext).sourceView`, and
`directiveState.languageRules` equals
`resolve(input.lexicalContext).options.languageRules`. At an included-unit entry, the new frame is
the last input frame and the conditional/busy prefixes equal those captured in
`IncludedUnitBoundary`. Only suffixes created by that included unit may be popped within it.

`PP-STA-005`: `ExpandPreprocessor.entryState` equals
`BeginPreprocessorUnit(unit, initialPersistentState)`, `exitState` is the ordered scan's final
transient state, and `finalPersistentState` equals `EndPreprocessorUnit(unit, exitState)`. No caller
constructs or pops an input frame by convention.

`PP-STA-006`: A persistent or transient state is valid only when its registered-directive map and
state slots satisfy their declared schemas and every builtin binding is equal to the definition
served at the query's `BuiltinMacroProviderRevision`. Provider rebinding is an input-version change,
never mutation of an existing preprocessing state.

## Ordered scan and activity

Expansion is a left-to-right scan of the structured unit. The central judgment is:

```text
I ; O ⊢ Σ ; element ⇓ nodes ; Σ' ; diagnostics
```

where `nodes` is the ordered sequence contributed to the `MacroExpanded` CST. A unit folds this
judgment in source order:

```text
Σ0 = entryState
I ; O ⊢ Σi ; element[i] ⇓ nodes[i] ; Σi+1 ; diagnostics[i]

unitResult = concatenate(nodes[0], ..., nodes[n-1])
exitState = Σn
diagnostics = stableSourceOrderUnion(diagnostics[0], ..., diagnostics[n-1])
```

This fold defines semantic ordering even when independent queries run in parallel. An implementation
may memoize a suffix by its `(element, state, options, dependency revisions)` key.

The expanded unit and its ordinary-text/conditional nodes have these concrete shapes:

```text
MacroExpandedPreprocessorUnitFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, PreprocessorUnit>,
    elements: NodeList<CSTNodeId<MacroExpanded>>,
    endOfFile: TerminalNodeId<MacroExpanded>
}

TextExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, TextRegion>,
    activity: TokenActivity,
    result: NodeList<CSTNodeId<MacroExpanded>>
}

ConditionalExpansionSelection =
    InactiveParent
  | NoBranchSelected
  | SelectedBranch(index: UInt32)
  | RecoveredConditionalSelection(error: ErrorId)

ExpandedConditionalOperand = {
    prePredicateList: TokenListId,
    prePredicateTokens: TokenListViewId,
    nodes: NodeList<CSTNodeId<MacroExpanded>>,
    list: TokenListId,
    tokens: TokenListViewId,
    featureObservations: NodeList<PreprocessorFeatureObservation>
}

PreprocessorFeatureObservation = {
    spelling: NonEmpty<TerminalNodeId<MacroExpanded>>,
    query: PreprocessorFeatureQuery,
    result: PreprocessorFeatureQueryResult,
    replacement: TerminalNodeId<MacroExpanded>
}

ParsedPreprocessorExpressionId = ContentId<PpExpr>

ConditionalBranchEvaluation = {
    branch: NonTerminalNodeId<PreprocessorStructured, ConditionalBranch>,
    decision: SkippedConditionalBranch {
                  reason: InactiveParent | EarlierBranchTaken | AfterElse
              }
            | ExpressionConditionalBranch {
                  expandedOperand: ExpandedConditionalOperand,
                  expression: ParsedPreprocessorExpressionId,
                  environment: PpConstEnvironment,
                  evaluation: PpConstResult,
                  selected: Bool,
                  errors: NodeList<ErrorId>
              }
            | ElseConditionalBranch {
                  selected: Bool
              }
}

ConditionalExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, ConditionalGroup>,
    evaluations: NonEmpty<ConditionalBranchEvaluation>,
    selection: ConditionalExpansionSelection,
    result: NodeList<CSTNodeId<MacroExpanded>>
}

BuiltinMacroExpansionFields = {
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    definition: BuiltinMacroDefinitionId,
    rule: BuiltinMacroRuleId,
    result: NodeList<TerminalNodeId<MacroExpanded>>
}

ExpandedRecoveryFields = {
    expandedFrom: AnyCSTNodeId,
    errors: NonEmpty<ErrorId>,
    unprocessed: Option<TokenListRange>,
    result: NodeList<CSTNodeId<MacroExpanded>>
}
```

For every product above, `result`/`elements` and the unit's `endOfFile` are structural edges;
`expandedFrom`, `invocation`, and `evaluations.expandedOperand.nodes` are provenance/evaluation
edges. Conditional operand nodes live in an already frozen intermediate expansion representation
and do not contribute a second terminal copy to the unit projection. A `TextExpansion` of inactive text copies its
entire token/trivia spelling with `Inactive` activity and contains no macro-expansion child. A
`ConditionalExpansion` contains the branch contents in source order, including inactive content;
its `evaluations` are in the same order as its first, `#elif`, and optional `#else` branches. An
expression decision retains the expanded operand CST nodes, the exact token list/view parsed from
them, the immutable `PpExpr`, exact `PpConstEnvironment`, complete `PpConstResult`, recovered
diagnostic errors, and derived selection bit.
The terminal projection of `expandedOperand.nodes` is a bijection with `expandedOperand.list`, and
`expandedOperand.tokens` is a view of that list. `prePredicateTokens` is a view of
`prePredicateList`, the macro-expanded input before feature-predicate replacement. `selection`
explains the result activity map but
does not delete the unselected branches. The
expanded unit has exactly one output EOF. Included-unit EOF terminals remain reachable through
their included roots but are not spliced into an including unit.

`PP-SCN-003`: The structural terminal projection of
`MacroExpandedPreprocessorUnitFields.elements` followed by `endOfFile` is a bijection with the
unit's primary `TokenList`. Provenance fields never contribute a second copy.

`PP-SCN-004`: Every output node is one of `TextExpansion`, `ConditionalExpansion`, a macro
operation/invocation expansion, an include expansion, or `ExpandedRecovery`; directives with no
parser-facing result remain reachable in the predecessor structured unit and do not require an
empty structural placeholder.

`isActive(Σ)` is true when every entry of `Σ.conditionalStack` has
`currentBranchActive = true`. In inactive source:

- conditional delimiters are processed to maintain nesting;
- ordinary text is copied to the output CST with `Inactive` activity but is not macro-expanded;
- `#define`, `#undef`, `#include`, diagnostics, pragmas, line directives, language directives, and
  registered non-conditional directives have no semantic effect; and
- a nested conditional expression need not be expanded or evaluated while its parent is inactive.

The final primary list has one canonical `TokenActivityMap`. A token or trivia element copied from
inactive text is marked `Inactive`; an element produced by an active macro or include is `Active`.
Directives themselves remain in predecessor CST and ordinarily contribute no parser-facing
elements.

```text
ActiveElementView(snapshot) =
    TokenListView(snapshot.primaryList,
                  IsActive(snapshot.activityMaps[snapshot.primaryList]))

ActiveTokenView(snapshot) =
    TokenListView(snapshot.primaryList,
                  And(IsToken,
                      IsActive(snapshot.activityMaps[snapshot.primaryList])))

IncludedContentView(snapshot) =
    TokenListView(snapshot.primaryList,
                  And(IsActive(snapshot.activityMaps[snapshot.primaryList]),
                      IsNotEndOfFile))
```

Parser grammar decisions consume `ActiveTokenView`; lossless parser translations simultaneously
walk the base primary list and use `ActiveElementView` to distinguish active trivia from maximal
inactive runs. Chapter 2 specifies how those inactive runs remain structural CST content without
contributing declarations or delimiter events. Include splicing consumes `IncludedContentView`,
retaining active trivia and excluding the child EOF.

`PP-SCN-001`: The scanner always either consumes at least one input element, descends with a
strictly smaller remaining resource budget, or returns a structured failure. It cannot retry the
same `(position, state)` after recovery.

`PP-SCN-002`: An inactive branch cannot define, undefine, invoke, include, diagnose, change
directive state, consume builtin values, or charge macro-output resources. It is nevertheless
losslessly represented.

## Directive semantics

### Macro definition and undefinition

`CompileMacroDefinition` is a pure query over a `MacroDefinition` CST node:

```text
CompileMacroDefinition(node, languageRules)
    -> CheckResult<CompiledMacroDefinition>

MacroDefinition::Flavor = FunctionLike | ObjectLike

MacroDefinition::Param = {
    definition: MacroDefinitionRef,
    ordinal: UInt32,
    node: Option<MacroDefinitionParamCSTNodeId>,
    name: PreprocessorName,
    isVariadic: Bool
}

MacroDefinition::Opcode =
    RawSpan
  | ExpandedParam
  | UnexpandedParam
  | StringizedParam
  | TokenPaste
  | Builtin(rule: BuiltinMacroRuleId)

MacroDefinition::Op = {
    definition: MacroDefinitionRef,
    ordinal: UInt32,
    opcode: MacroDefinition::Opcode,
    source: Option<MacroReplacementElementCSTNodeId>,
    parameter: Option<MacroDefinition::Param>
}

CompiledMacroDefinition = {
    reference: MacroDefinitionRef,
    name: PreprocessorName,
    flavor: MacroDefinition::Flavor,
    parameters: NodeList<MacroDefinition::Param>,
    operations: NodeList<MacroDefinition::Op>
}
```

Parameter and operation ordinals are contiguous source-order indices. An unnamed final `...`
parameter receives the established derived name `__VA_ARGS__` without fabricating a terminal.
Named variadic parameters retain both their name and ellipsis terminals. A variadic parameter must
be last. Duplicate parameter names and a parameter named by a reserved preprocessor operator are
diagnosed and represented by typed recovery; they do not silently alter the parameter map.

In active source, a valid `#define` compiles its definition and returns a state whose environment
binds the name to that exact definition. Equivalent redefinition is accepted without a diagnostic;
non-equivalent redefinition is diagnosed and the later definition becomes the binding
for following source. Equivalence compares flavor, parameter count/variadic positions after
ordinal alpha-renaming, followed by operation opcode and parameter ordinal and then each literal
replacement token's `TokenType` and `logicalSpelling`. `Trivia` placement inside the replacement is
ignored for equivalence; the no-trivia rule that distinguishes a function-like definition was
already reflected in flavor. Equivalence never compares pointer identity.

An active `#undef name` returns a state with an `Undefined` tombstone for `name`. Undefining an
unbound name has no diagnostic. Extra non-trivia operands are diagnosed but preserved.

`PP-DIR-001`: A definition becomes visible only after its directive. An undefinition hides all
earlier bindings, including bindings in a parent environment. Neither operation retroactively
changes an already recognized invocation.

`PP-DIR-002`: `MacroDefinition::Op` is derived executable data, not a second syntax tree and not a
history record. A source macro operation has `source = Some` naming the replacement-list CST node
from which it was derived. A predefined operation has `source = None` but its emitted-token inputs
name exact elements of `PredefinedMacroDefinition.replacement`. A builtin operation also has
`source = None` and names its registered rule. Neither form fabricates source syntax.

### Conditional directives

```text
BranchConditionContext = {
    environment: preprocessor::EnvironmentId,
    busyMacros: NodeList<BusyMacro>,
    currentInput: PreprocessorInputFrame,
    logicalLocations: PreprocessorLogicalLocationStateId,
    languageRules: LanguageRuleSetId,
    parentActive: Bool,
    anyEarlierBranchTaken: Bool,
    sawElse: Bool
}

EvaluateConditionalBranch(
    branch: NonTerminalNodeId<PreprocessorStructured, ConditionalBranch>,
    context: BranchConditionContext,
    features: PreprocessorFeatureSet,
    featureSetRevision: PreprocessorFeatureSetRevision)
    -> CheckResult<ConditionalBranchEvaluation>
```

The expression grammar, from lowest to highest precedence, is:

```text
?:  ||  &&  |  ^  &  == !=  < <= > >=  << >>  + -  * / %  prefix(+ - ! ~)
```

Atoms are integer literals, parenthesized expressions, `defined name`, `defined(name)`,
`__has_feature(name)`, and identifiers. Evaluation proceeds as follows:

1. Protect the operand of each `defined` operator from macro expansion.
2. Macro-expand the remaining operand tokens under the current environment.
3. Recognize each `__has_feature(name)` predicate, query `PreprocessorFeatureSet` with that exact
   `PreprocessorName`, replace the predicate with a derived integer-literal terminal `1` or `0`, and
   retain a `PreprocessorFeatureObservation` connecting the spelling, request, answer, and
   replacement terminal.
4. Parse the resulting tokens into the chapter 7 `PpExpr` algebra. `PpIdentifier` retains
   `PreprocessorName`; it is not rewritten by a second name representation.
5. Construct the chapter 7 `PpConstEnvironment` with
   `definedNames = visibleDefinedNames(context.environment)` and the `PpIntegerModel` and
   `PpIdentifierRule` selected by `context.languageRules`.
6. Invoke `EvalPreprocessorConst` and derive `selected` from the returned `PpConstValue` using the
   chapter 7 truth conversion.

Chapter 7's `PpUnaryOperator`, `PpBinaryOperator`, `PpIntegerModel`, conversions, overflow behavior,
shift rules, short-circuiting, failures, fallback values, and `EvalPreprocessorConst` equations are
the sole authority for preprocessor arithmetic and equality. This chapter defines when that
evaluator is invoked and how its CST/provenance artifacts are retained; it does not define a second
integer semantics.

`#ifdef N` is equivalent to `defined(N)` and `#ifndef N` to `!defined(N)` without expanding `N`.

On entry to a group, `parentActive` is the activity before the group. The first branch is active
exactly when `parentActive && condition != 0`. An `#elif` is evaluated only if `parentActive`, no
earlier branch was taken, and no `#else` was seen. An `#else` is active exactly when
`parentActive && !anyEarlierBranchTaken`. `#endif` restores the enclosing activity. Structural
errors use the recovery nodes produced during structuring and cannot corrupt an outer frame.

`PP-CND-001`: Exactly zero or one branch of a well-formed conditional group is active. Branch
selection is independent of later declarations and types.

`PP-CND-002`: An expression evaluation retains its expanded operand CST and canonical parsed
expression directly in `ConditionalBranchEvaluation` for diagnostics and tests. A Boolean result
alone is not enough to explain or validate the decision.

`PP-CND-003`: `EvaluateConditionalBranch` returns `SkippedConditionalBranch` without expanding an
operand or querying a feature when its context makes evaluation unnecessary. Otherwise its
`ExpressionConditionalBranch.errors` is empty for `Success` and equals the root errors of
`Recovered`. The returned branch must be the request branch, and the selection fold consumes the
returned `selected` bit derived from its stored `PpConstResult` without reparsing, re-expanding, or
re-evaluating the operand.

`PP-CND-004`: Branch indices are zero-based in source order across the first branch, all `#elif`
branches, and the optional `#else`. `SelectedBranch(i)` names the unique evaluation at index `i`
whose condition selected it; `NoBranchSelected` means every evaluated condition was false and no
`#else` was present.

`PP-CND-005`: The operand expansion representation and parsed-expression content identities are
frozen before the containing `ConditionalExpansion`. `prePredicateList` is frozen before feature
replacement terminals are derived, and the normalized `list` is frozen before `PpExpr` is parsed.
Their references are evaluation provenance, not forward references into the snapshot whose identity
is being computed.

`PP-CND-006`: A feature-predicate replacement terminal has integer-literal type, logical spelling
`1` exactly for `Supported` and `0` otherwise, no physical spelling, and a direct derivation naming
the branch and every terminal in `PreprocessorFeatureObservation.spelling`; those terminals resolve
to `prePredicateList`, never the list containing the replacement. The observation's
request and result are the authority for validating that token.

### Other directives

An active `#error` always emits an error diagnostic; an active `#warning` emits a warning subject to
the current warning state. Their message is the lossless remainder of the directive line. They
produce no parser-facing tokens.

An active `#line` first macro-expands its operands, validates the line number and optional file
spelling, and returns a new source-view-specific logical-location state. `__LINE__`, `__FILE__`,
diagnostics, and later location queries use that state. Physical `SourceRange` values do not change.

Known `#pragma` forms update their declared part of `directiveState`; `#pragma once` adds the
current input frame's `uniqueIdentity` to `pragmaOnceUniqueIdentities`. Unknown pragmas are
preserved and ignored unless a registered handler claims them. `#language`, `#lang`, `#version`,
and `#extension` update only schema-declared language state after validating their exact operands.
Changing lexical treatment cannot reinterpret elements already lexed in the current snapshot; a
language feature that needs different tokenization must be selected before `Lex`.

`PP-DIR-003`: Each registered directive declares its operand grammar, state field, behavior in an
inactive branch, serialization schema, and dependency revision. A callback with undeclared mutable
state is not a valid directive implementation.

`PP-DIR-004`: Directive recognition occurs only in the initially structured spelling of a source
view. A `#` token produced by macro substitution or argument expansion cannot synthesize a new
directive. Macro expansion is used only where a recognized directive rule explicitly requests it,
such as an include operand or conditional expression.

`PP-DIR-005`: Applying a registered directive replaces exactly
`registeredDirectiveState[definition.stateSlot]` with the schema-valid provider result. The current
registered-directive interface produces no parser-facing tokens and cannot update macro bindings,
include state, warning state, logical locations, language rules, resources, or another registered
slot. Any future directive class with one of those effects requires a new typed result alternative.

## Macro invocation recognition and arguments

The ordered scanner considers an active identifier token at its current position. Its stream is an
immutable token list plus the CST producers of those elements; it can describe either initially
structured source text or an intermediate replacement result being rescanned:

```text
ExpansionScanStream = {
    list: TokenListId,
    view: TokenListViewId,
    producers: NodeMap<TokenListElementRef, NonEmpty<AnyCSTNodeId>>
}

RecognizeMacroInvocation(stream, position, environment, context)
    -> NotAnInvocation
     | Invocation(MacroInvocationCSTFragment)
     | MalformedInvocation(MacroInvocationCSTFragment,
                           errors: NonEmpty<ErrorId>)
```

If lookup is `NotFound`, the scanner copies the identifier and advances one token. If it resolves
an object-like source, predefined, or builtin definition, the identifier alone is the invocation spelling.
If it resolves a function-like definition, the next non-trivia token must be `(`; otherwise the
identifier is not an invocation and no input beyond it is committed. Trivia between the name and
`(` belongs to the invocation's written range.

```text
MacroExpansionContext = {
    environment: preprocessor::EnvironmentId,
    currentInput: PreprocessorInputFrame,
    initiatingName: TerminalNodeId<PreprocessorStructured>,
    languageRules: LanguageRuleSetId,
    logicalLocations: PreprocessorLogicalLocationStateId
}

MacroInvocationCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroInvocation>
MacroInvocationArgumentClauseCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroInvocationArgumentClause>
MacroInvocationArgumentTailCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroInvocationArgumentTail>
MacroInvocationArgCSTNodeId =
    NonTerminalNodeId<PreprocessorStructured, MacroInvocationArg>

MacroInvocationCSTFragment = {
    invocation: MacroInvocationCSTNodeId,
    snapshot: CSTSnapshot<PreprocessorStructured>
        where snapshot.root = invocation,
    next: TokenListIndex
}

MacroInvocationFields = {
    name: TerminalNodeId<PreprocessorStructured>,
    definition: MacroDefinitionRef,
    context: MacroExpansionContext,
    argumentClause: Option<MacroInvocationArgumentClauseCSTNodeId>,
    writtenRange: TokenListRange
}

MacroInvocationArgumentClauseFields = {
    leftParenthesis: TerminalNodeId<PreprocessorStructured>,
    arguments: Option<MacroInvocationArgumentSequence>,
    rightParenthesis: TerminalNodeId<PreprocessorStructured>
}

MacroInvocationArgumentSequence = {
    first: MacroInvocationArgCSTNodeId,
    remaining: NodeList<MacroInvocationArgumentTailCSTNodeId>
}

MacroInvocationArgumentTailFields = {
    comma: TerminalNodeId<PreprocessorStructured>,
    argument: MacroInvocationArgCSTNodeId
}

MacroInvocationArgFields = {
    elements: NodeList<CSTNodeId<PreprocessorStructured>>,
    writtenRange: TokenListRange
}
```

Arguments are split by commas at parenthesis depth zero. The opening invocation parenthesis starts
at depth zero and is not part of an argument; nested `(` increments depth and a matching `)`
decrements it. Braces and brackets do not change macro-argument parenthesis depth. The matching
depth-zero `)` ends the clause. Every comma and parenthesis is an explicit terminal field.

`M()` has zero arguments except when `M` has exactly one non-variadic parameter, in which case it
has one empty argument anchored before `)`. This preserves the established distinction without
inventing a token. For a variadic final parameter at ordinal `p`, arguments before `p` bind
one-to-one and the variadic binding is the exact range from argument `p` through the final argument,
including separating commas and trivia. It is empty when no such argument exists.

A non-variadic invocation requires exactly one argument per parameter. A variadic invocation
requires at least the number of non-variadic parameters. Missing `)`, premature EOF, and arity
mismatch produce `MalformedInvocation` with all consumed terminals and an explicit missing-terminal
or arity record.

`PP-INV-001`: Recognition uses the environment at the invocation position and stores the selected
`MacroDefinitionRef` directly on the immutable invocation node. Later `#define` or `#undef` cannot
retarget that node.

For an outermost source-written invocation, `context.initiatingName = name`. An invocation
recognized while rescanning a macro result inherits the initiating name of that expansion chain.
The context is the minimal immutable state projection needed to validate definition selection and
builtin expansion; it is not a transition record.

`PP-INV-002`: `MacroInvocationArg.writtenRange` is the sole input to stringization and unexpanded
parameter substitution. It includes exact `Token | Trivia` spelling; neither `AfterWhitespace` nor
a token-only projection can replace it.

`PP-INV-003`: Invocation recognition is syntax production, not semantic declaration lookup. It
never creates an AST name binding and does not consult parser lookup scopes.

`PP-INV-004`: Recognition publishes a new `PreprocessorStructured` fragment containing the
invocation, argument nodes, and terminals before expansion begins. The fragment's predecessor set
contains every snapshot named by `stream.producers`; its terminals refer to `stream.list` and have
direct origins pointing to those producers. The stream may come from the initial structured source
or from a `MacroExpanded` intermediate replacement result, so rescan can recognize generated calls
without pretending that they were present in the physical source. `PreprocessorStructured` denotes
the node shape here, not a globally monotone compiler phase. Both the original input snapshot and
every intermediate stream remain unchanged.

## Replacement compilation and argument forms

The replacement-list compiler groups maximal literal spans and recognizes parameter references,
`#` stringization, and `##` paste in the definition CST. It then emits the established operations:

- `RawSpan` for literal replacement terminals;
- `ExpandedParam` for an ordinary parameter occurrence;
- `UnexpandedParam` for a parameter occurrence immediately adjacent to `##`;
- `StringizedParam` for `#` followed by a parameter;
- `TokenPaste` for the exact `##` terminal and its neighboring operation results; and
- `Builtin(rule)` for the exact rule named by a builtin definition.

`#` that does not precede a parameter and `##` at the start or end of a replacement list are
diagnosed and retained in typed recovery nodes. Paste chains are evaluated in source order. A paste
combines the final token produced by its current left operation with the first token produced by
its right operation; either side may be empty. Tokens of a multi-token operand not consumed at that
boundary retain their order around the paste result.

For each invocation argument `a` the expander defines two immutable views:

```text
Written(a) = exact Token | Trivia sequence in a.writtenRange

Prescan(a, Σ) = macro-expand Written(a) under Σ.environment and Σ.busyMacros,
                    before adding the current invocation to the busy chain
```

`Prescan` is computed only when an `ExpandedParam` occurrence needs it, and equal requests may
share a cache. `UnexpandedParam`, `StringizedParam`, and a parameter operand adjacent to `##` use
`Written`. A parameter referenced several times has one semantic prescan result but each emitted
copy gets occurrence-specific provenance.

`PP-OPS-001`: Opcode selection is a total derived function of the definition CST and parameter
map. Expansion code does not rediscover adjacency to `#` or `##` from flattened tokens.

`PP-OPS-002`: Argument prescan happens in the invocation's incoming busy context. The current
definition becomes busy only for replacement playback and rescan. Consequently a nested invocation
of the same macro in an argument can expand, while a self-reference emitted by the replacement is
suppressed.

## Expansion, rescan, and recursion suppression

For a well-formed invocation whose definition is not busy, expansion is:

1. Obtain any required `Prescan` results.
2. Push `BusyMacro(invocation, definition)` for replacement playback and rescan.
3. Evaluate `MacroDefinition::Op` values in order, creating macro-operation expansion CST nodes and
   derived tokens with direct provenance.
4. Resolve paste boundaries and concatenate the operation results.
5. Rescan the resulting sequence from left to right under the busy state. Newly recognized macro
   calls are expanded recursively with the same rules.
6. Publish `MacroExpansion(expandedFrom = invocation, definition, result = rescannedNodes)`.
7. Pop the exact busy entry and continue after the invocation in the enclosing input stream.

The output representation has actual fields, not projections from an operation log:

```text
MacroExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    definition: MacroDefinitionRef,
    result: NodeList<CSTNodeId<MacroExpanded>>
}

MacroRawSpanExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroRawSpan>,
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    result: NodeList<TerminalNodeId<MacroExpanded>>
}

MacroParamExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroParamReference>,
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    argument: NonTerminalNodeId<PreprocessorStructured, MacroInvocationArg>,
    form: Written | Prescanned,
    result: NodeList<CSTNodeId<MacroExpanded>>
}

MacroStringizeExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroStringize>,
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    argument: NonTerminalNodeId<PreprocessorStructured, MacroInvocationArg>,
    result: TerminalNodeId<MacroExpanded>
}

TokenPasteExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, TokenPaste>,
    invocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    leftInput: Option<TerminalNodeId<MacroExpanded>>,
    rightInput: Option<TerminalNodeId<MacroExpanded>>,
    concatenatedSpelling: Text,
    result: NodeList<TerminalNodeId<MacroExpanded>>
}

SuppressedExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    blockingInvocation: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    result: NodeList<CSTNodeId<MacroExpanded>>
}

FailedExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, MacroInvocation>,
    failure: MacroExpansionFailure,
    result: NodeList<CSTNodeId<MacroExpanded>>
}

MacroExpansionFailure =
    InvocationSyntaxFailure(errors: NonEmpty<ErrorId>)
  | DefinitionCompilationFailure(errors: NonEmpty<ErrorId>)
  | ArgumentPrescanFailure(errors: NonEmpty<ErrorId>)
  | BuiltinProviderRecovery(errors: NonEmpty<ErrorId>)
  | MacroResourceLimitFailure(limit: ResourceLimitExceeded,
                              error: ErrorId)
  | PriorMacroFailure(error: ErrorId)
```

In these products, each `result` field is a structural edge contributing to the expanded token
sequence. `expandedFrom`, `invocation`, `argument`, `leftInput`, `rightInput`, and
`blockingInvocation` are direct provenance edges. They remain generically accessible and
serializable, but a structural source-order walk does not emit their spelling a second time.

If the selected definition is already in `busyMacros`, the occurrence is represented by
`SuppressedExpansion`. The nearest busy entry with that definition supplies
`blockingInvocation`. The blocked macro-name token is copied once and is not reconsidered at the
same rescan level. Remaining invocation spelling is scanned normally, so other macros in its
arguments may still expand. The enclosing scanner never restarts over already emitted results.

This operational rule terminates direct and indirect recursion:

```text
#define A A       // A -> Suppressed(A)
#define B A
#define A2 B      // A2 -> B -> A; only a repeated active definition is suppressed
#define X Y
#define Y X       // X -> Y -> Suppressed(X)
```

It also preserves ordinary nested calls because argument prescan precedes the current busy push.
Busy state is invocation-scoped, is restored on success or failure, and is never scheduler-global.

`PP-EXP-001`: Every expanded, suppressed, or failed invocation has one immutable output CST node
whose `expandedFrom` field is the exact invocation CST node. Every successful operation-result node
similarly refers to the exact replacement-list node it realizes.

`PP-EXP-002`: Rescan is streaming and nested. A nested expansion result is consumed once by its
caller; popping its busy entry does not cause an enclosing scanner to restart on that result.

`PP-EXP-003`: A busy definition is a normal, non-diagnostic suppression decision, not an error
witness, an omitted provenance edge, or a mutable flag on the definition.

## Stringization

Stringization uses the exact written argument, without prescan:

```text
stringizePayload(range) =
    trim leading and trailing Trivia;
    replace each remaining maximal nonempty Trivia run with one U+0020;
    concatenate Token.logicalSpelling in order;
    within StringLiteral and CharLiteral token spellings,
        prefix each '\\' and '"' with '\\'

stringize(range) = '"' + stringizePayload(range) + '"'
```

Comments, newlines, and line continuations are trivia for whitespace folding. A continuation that
occurred inside a lexical token was already removed from that token's `logicalSpelling`; the
stringizer does not reconstruct it. The escaping pass scans logical spelling bytes and does not
decode and re-encode literals. An empty or trivia-only argument produces `""`.

The result is one `StringLiteral` token with `physicalSpelling = None`. Its derivation names the
invocation, definition, `MacroStringize` CST node, argument node, and written range.

`PP-STRZ-001`: Stringization is a pure function of `MacroInvocationArg.writtenRange` and lexical
spelling rules. It cannot observe token flags, formatter attachment, source-manager line tables, or
the prescanned argument.

## Token paste

Paste first obtains the optional boundary tokens of its unexpanded operands:

```text
pasteSpelling(left, right) =
    (left.logicalSpelling if left is present else "")
  + (right.logicalSpelling if right is present else "")

LexPasteSequence(text, languageRules)
    -> NodeList<ValidPasteToken | InvalidPasteToken>

ValidPasteToken = {
    type: TokenType where not isTrivia(type) and type != EndOfFile,
    logicalSpelling: Text
}

InvalidPasteToken = {
    logicalSpelling: Text,
    failure: PasteLexFailure
}

PasteLexFailure =
    TriviaSpellingNotPermitted(type: TokenType,
                               range: ByteRange)
  | InvalidPreprocessingToken(range: ByteRange,
                              lexicalReason: ContentId<SchemaValue>)
  | UnterminatedPreprocessingToken(type: TokenType,
                                  range: ByteRange)
```

`LexPasteSequence` is a preprocessing-token lexer. It emits neither `Trivia` nor EOF. A spelling
that begins whitespace, a comment, or another trivia form is invalid rather than trivia; for
example `/ ## *` forms invalid `/*`, not a `BlockComment`.

Empty spelling produces zero tokens and is valid only when both operands are absent. Exactly one
valid token is a successful nonempty paste. An invalid token or more than one token emits
`invalid-token-paste-result`; recovery materializes the exact returned sequence in order, using
`Invalid` token type for each invalid alternative. Every result has `physicalSpelling = None` and
direct paste provenance. A diagnostic never causes the paste spelling to disappear.

`PP-PST-001`: `TokenPasteExpansion.concatenatedSpelling` equals `pasteSpelling(leftInput,
rightInput)`, and its result terminals equal materialization of `LexPasteSequence` for that spelling.

`PP-PST-002`: Paste provenance names the exact `TokenPaste` CST node and optional boundary-token
origins. In a chain, a later paste may name the prior paste result as its left input; it does not
pretend that every paste consumed only source tokens.

## Builtin macros

Builtin macros are definitions supplied by the versioned `BuiltinMacroProvider`. Each definition
declares its flavor, name, expansion rule, and required context fields; every rule returns the
fixed `BuiltinMacroExpansionDescription` schema. A builtin
does not fabricate a source `MacroDefinition` node.

For an invocation, the expander resolves its `BuiltinMacroDefinitionId` in the already validated
catalog, projects exactly `requiredContext` from `MacroExpansionContext`, and calls
`ExpandBuiltinMacro`. The returned description's `rule` must equal the definition's rule, and each
description is materialized in order as a terminal in `BuiltinMacroExpansion.result`. Empty and
multi-token builtin results are both representable; the provider does not insert them directly
into a token list.

`__LINE__` and `__FILE__` use the logical location at the outermost source-written invocation that
initiated the current expansion chain. If the builtin is written directly in source, that occurrence
is the initiating invocation. The selected source view and line-directive state are explicit fields
of the expansion context. The emitted integer or string token has no physical spelling and names
the builtin definition, invocation, rule, and context in its provenance.

`__has_feature` is a preprocessor-expression predicate supplied by a versioned feature set. It is
not an ordinary macro binding.

`PP-BLT-001`: A builtin result depends only on the builtin definition, invocation, declared context
projection, and provider revision. Time, process environment, current working directory, and
unversioned host state are forbidden inputs.

`PP-BLT-002`: The terminal descriptions returned by `ExpandBuiltinMacro` and the terminals in
`BuiltinMacroExpansion.result` are a source-order bijection. The latter add physical-spelling
absence and direct provenance; they cannot alter token type or logical spelling.

## Include expansion

An active include first macro-expands its operand tokens. The result must decode to exactly one
quote form (`"path"`) or system form (`<path>`):

```text
IncludeSystem::Mode = Quote | System

IncludeRequest = {
    path: Utf8String,
    mode: IncludeSystem::Mode
}

ResolvedInclude = {
    uniqueIdentity: IncludeUniqueIdentity,
    foundPath: Utf8String,
    source: SourceFileSnapshotId
}

IncludeResolutionFailure = {
    code: QualifiedName,
    details: ContentId<SchemaValue>
}

IncludeSystemRequest = {
    includingView: SourceViewId,
    include: IncludeRequest
}

IncludeSystemResult =
    ResolvedIncludeResult(value: ResolvedInclude)
  | IncludeNotFound
  | IncludeRejected(failure: IncludeResolutionFailure)

ResolveInclude(includeSystem: IncludeSystem,
               revision: IncludeSystemRevision,
               request: IncludeSystemRequest)
    -> IncludeSystemResult

CreateIncludedSourceView(
    directive: NonTerminalNodeId<PreprocessorStructured, IncludeDirective>,
    includingView: SourceViewId,
    resolved: ResolvedInclude)
    -> SourceView

CreateIncludedLexicalContext(parent: LexicalContextId,
                             includedView: SourceViewId,
                             languageRules: LanguageRuleSetId,
                             policy: IncludeLexPolicy)
    -> Result<LexicalContext, IncludedLexicalContextFailure>

IncludedLexicalContextFailure =
    TokenizationRuleChangeAfterPrimaryLex
  | IncompatibleIncludeLexPolicy
```

`IncludeSystem` is the only file-resolution capability used by the query. Its revision includes
search paths, path rules, and the file-system/content revision. A mock implementation is sufficient
for all include semantics tests. An unavailable revision or a response that does not satisfy the
result schema is an infrastructure failure; `IncludeNotFound` and `IncludeRejected` are ordinary
typed provider answers from which preprocessing constructs source diagnostics.

`ResolveInclude` selects file identity and immutable contents; it never creates a `SourceView`.
`CreateIncludedSourceView` is the canonical representation constructor. Its result has
`key.snapshot = resolved.source`, `key.use = IncludedSourceView(range(directive))`,
`key.viewPath = Some(resolved.foundPath)`, and an initially empty line-directive list. The
directive's range already contains `includingView`; supplying a different view is invalid. Thus
two uses of the same resolved source through distinct including views or directive occurrences
produce distinct view identities without making file resolution depend on expansion history.
`CreateIncludedLexicalContext` installs `includedView` as `LexicalContext.sourceView`, copies the
parent `LexOptions`, and applies only language-rule changes declared not to alter tokenization. It
checks the two `IncludeLexPolicy` constraints explicitly. A rule that would require reinterpreting
the already structured including file fails rather than silently lexing the child under an
incompatible language.

For a resolved include:

1. If `uniqueIdentity` is already in `pragmaOnceUniqueIdentities`, publish
   `SuppressedIncludeExpansion(PragmaOnce)` and produce no tokens.
2. If it appears in `inputStack`, publish `FailedIncludeExpansion(Cycle)` and produce no tokens.
3. Freeze or validate `loadedSources[uniqueIdentity] = source`.
4. Create the distinct included `SourceView` with `CreateIncludedSourceView`; construct a
   `LexicalContext` with `CreateIncludedLexicalContext`; lex and structure it;
   then enter it with `EnterIncludedPreprocessorUnit`.
5. Scan the included unit with the caller's current environment, pragma-once set, loaded sources,
   registered-directive catalog, directive state, and remaining resource budget. Conditional and
   busy stacks are scoped as described below.
6. Leave it with `LeaveIncludedPreprocessorUnit` and publish `IncludeExpansion` referring directly
   to the written directive, included view, and included expanded root.
7. Splice the included primary list's active `Token | Trivia` elements except its EOF into the
   including result, preserving their interleaving.

```text
IncludeExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, IncludeDirective>,
    request: IncludeRequest,
    resolved: ResolvedInclude,
    includedView: SourceViewId,
    includedRoot: NonTerminalNodeId<MacroExpanded, PreprocessorUnit>,
    result: NodeList<CSTNodeId<MacroExpanded>>
}

SuppressedIncludeExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, IncludeDirective>,
    request: IncludeRequest,
    resolved: ResolvedInclude,
    reason: PragmaOnce,
    result: Empty
}

FailedIncludeExpansionFields = {
    expandedFrom: NonTerminalNodeId<PreprocessorStructured, IncludeDirective>,
    request: Option<IncludeRequest>,
    resolved: Option<ResolvedInclude>,
    includedView: Option<SourceViewId>,
    stage: DecodeOperand | Resolve | SnapshotConflict | Cycle | LexicalContext |
           Lex | Structure | Expand | ResourceLimit,
    error: ErrorId,
    result: Empty
}
```

The child's conditional-stack suffix starts empty and must be empty at child EOF; unclosed
conditions are recovered inside the child. The caller's conditional prefix is restored exactly.
The caller's busy prefix is restored exactly; include directives cannot leak or pop macro
invocations. The child's final macro environment, pragma-once additions, loaded-source selections,
declared directive-state
changes, and resource usage flow outward. Source-view-specific logical-line entries remain keyed by
their source view. This field-by-field rule, rather than a generic "copy state back," defines include
scope.

Each non-suppressed, non-cyclic include use that reaches lexing has its own `SourceView` and staged
CST chain even when decoded file bytes and `SourceFileSnapshot` are shared. This distinction
preserves both include paths in diagnostics and
provenance. A conventional written include guard is just conditional evaluation; only
`#pragma once` uses the explicit suppression set.

`PP-INC-001`: A successful include expansion directly connects the include directive, the canonical
included view, the included expanded root, and the spliced result. Each spliced token's derivation also names its immediate
included token and this include use, so repeated includes cannot collapse provenance paths.

`PP-INC-002`: Included EOF is never spliced. Suppressed or failed includes fabricate neither a
child root nor output tokens. A failure after resolution retains the `ResolvedInclude`; a failure
after view creation also retains `includedView`; a resolution failure retains neither.

`PP-INC-003`: Include traversal is deterministic for an `IncludeSystem` revision and incoming
state. Resolver caching may change performance but not selected identity, source snapshot, state
propagation, diagnostics, or provenance.

`PP-INC-004`: `FailedIncludeExpansion` has `request = None` only at `DecodeOperand`,
`resolved = None` only at `DecodeOperand` or `Resolve`, and `includedView = Some` exactly after
`CreateIncludedSourceView` succeeded. A suppressed include always retains its request and resolved
answer and never creates a view or child root.

## Direct provenance on produced representations

Provenance is stored on the produced node or token. It is not obtained by looking up a materialized
rewrite record.

```text
macroTokenDerivation(invocation, sourceDefinition, operation,
                     sourceNode, argument, inputTokens) = TokenDerivation {
    rule: ruleForMacroOpcode(operation.opcode),
    inputs: [SourceNode(invocation),
             SourceNode(sourceDefinition),
             SourceNode(sourceNode)]
          ++ optionalSourceNode(argument)
          ++ map(SourceToken, inputTokens),
    context: Some(invocation)
}

predefinedMacroTokenDerivation(invocation, operation, inputTokens) = TokenDerivation {
    rule: ruleForMacroOpcode(operation.opcode),
    inputs: [SourceNode(invocation)] ++ map(SourceToken, inputTokens),
    context: Some(invocation)
}

tokenPasteDerivation(invocation, paste, left, right) = TokenDerivation {
    rule: PP-PST-001,
    inputs: [SourceNode(invocation), SourceNode(paste)]
          ++ optionalSourceToken(left)
          ++ optionalSourceToken(right),
    context: Some(invocation)
}

builtinTokenDerivation(invocation, rule) = TokenDerivation {
    rule: rule,
    inputs: [SourceNode(invocation)],
    context: Some(invocation)
}

featurePredicateTokenDerivation(branch, inputTerminals) = TokenDerivation {
    rule: PP-CND-006,
    inputs: [SourceNode(branch)] ++ map(SourceNode, inputTerminals),
    context: Some(branch)
}

includeTokenDerivation(directive, includedRoot, inputToken) = TokenDerivation {
    rule: PP-INC-001,
    inputs: [SourceNode(directive),
             SourceNode(includedRoot),
             SourceToken(inputToken)],
    context: Some(directive)
}

recoveryTokenDerivation(invocation, inputTokens) = TokenDerivation {
    rule: PP-ERR-001,
    inputs: [SourceNode(invocation)] ++ map(SourceToken, inputTokens),
    context: Some(invocation)
}
```

These are canonical constructors for the chapter 3 `TokenDerivation` product, not new alternatives
of its type and not operation objects. `sourceDefinition` is the source `MacroDefinition` node; a
builtin has no such node and uses `builtinTokenDerivation`. A predefined replacement uses
`predefinedMacroTokenDerivation`; its selected definition is reachable through the invocation, and
its replacement elements are the named source-token inputs. Following `SourceToken(input)` reaches
that token's own origin, so a derivation chain does not copy or flatten its predecessor.

The inputs of a raw-span or parameter copy name the actual predecessor tokens. A copied
token receives a new derived origin even when its type and logical spelling are unchanged, because
the macro or include use is semantically relevant provenance. `Trivia` values remain immutable and
are traced by their containing terminal's direct
`CSTNodeOrigin.Translated(CSTTranslationOrigin)`; a produced token does not point forward to its
containing expansion node.

Each produced non-terminal has named fields such as `expandedFrom`, `includedRoot`, and `result`,
plus the chapter 3 `CSTNodeOrigin.Translated(CSTTranslationOrigin)` containing its rule and direct
predecessor node/terminal references. Its fields are authoritative. There is no output-port table,
output-binding map, or operation list to resolve before a client can traverse the CST.

The provenance graph is acyclic: a produced value may name source ranges, predecessor snapshots,
included child snapshots, or an already frozen intermediate token list/snapshot, but never its own
owning list/snapshot or a later result. Replacement playback, paste, rescan, and final list assembly
therefore publish their immutable intermediate results in dependency order. An implementation may
co-allocate them with provisional handles, but it computes content identities only after rewriting
those handles in the topological order required by `REP-TOK-005`.

`PP-PRV-001`: Following a macro token's derivation reaches its exact invocation, selected
definition, replacement occurrence, argument when applicable, and physical source tokens. Paste and
include add their exact intermediate edge rather than flattening this path.

`PP-PRV-002`: The primary diagnostic location for a macro-derived token is the outermost initiating
invocation name. Nested invocations, definitions, arguments, paste operands, include directives,
and physical spelling are retained as ordered notes; selecting a primary location discards none of
them.

`PP-PRV-003`: A provenance validator rejects cycles, an origin that reaches its owning token list
or snapshot, invalid representation-domain references, mismatched
`MacroDefinition::Op` opcode and source-node kinds, spelling inconsistent with stringize or paste,
and an include input not
reachable from the named included root.

## Diagnostics and recovery

Diagnostics are structured values with a rule ID, primary origin, typed arguments, and related
origins. Text rendering is not semantic output and tests do not scrape it.

Recovery preserves input and guarantees progress:

- A malformed directive remains a `PreprocessorRecovery` node and has no undeclared state effect.
- A malformed or wrong-arity macro invocation publishes `FailedExpansion`; its result is the exact
  written invocation spelling copied once and marked as already recovered at that scan level.
- A busy macro publishes `SuppressedExpansion` without a diagnostic.
- Invalid stringization cannot occur after a structurally valid definition; a malformed `#`
  occurrence is compiled as recovery spelling rather than guessed as stringization.
- Invalid paste publishes `TokenPasteExpansion`, diagnostic, and the exact re-lexed recovery
  sequence.
- A failed include publishes `FailedIncludeExpansion` and no included tokens.
- `#error` produces a requested diagnostic and no parser-facing tokens; it does not abort the
  representation unless the caller's diagnostic policy chooses not to consume a recovered result.

Error recovery cannot define a macro, discharge a condition, synthesize an include path, or consume
unbounded input. `CheckResult<T>` has exactly the semantic alternatives `Success` and `Recovered`.
A scheduler evaluation is `QueryStep<T> = Complete(CheckResult<T>) | Blocked(DependencySet)`;
blocking is not serialized semantic output. Cancellation, unavailable provider revisions, invalid
provider responses, and broken invariants are task execution failures, not additional
`CheckResult` alternatives.

`PP-ERR-001`: Every diagnostic-producing case specifies its output node, copied or synthesized
tokens, state effect, next scan position, and provenance. "Emit a diagnostic and continue" is not a
complete recovery rule.

## Resource limits and termination

```text
PreprocessorResourceLimits = {
    maximumIncludeDepth: UInt32,
    maximumExpansionDepth: UInt32,
    maximumExpandedInvocations: UInt64,
    maximumEmittedTokens: UInt64,
    maximumInspectedElements: UInt64,
    maximumArgumentElements: UInt64,
    maximumPasteBytes: UInt64
}

PreprocessorResourceCharge = {
    inspectedElements: UInt64,
    argumentElements: UInt64,
    emittedTokens: UInt64,
    expandedInvocations: UInt64,
    pasteBytes: UInt64,
    observedIncludeDepth: UInt32,
    observedExpansionDepth: UInt32
}

ResourceLimitKind =
    IncludeDepth | ExpansionDepth | ExpandedInvocations | EmittedTokens |
    InspectedElements | ArgumentElements | PasteBytes

ResourceLimitExceeded = {
    kind: ResourceLimitKind,
    limit: UInt64,
    attempted: UInt64
}

ChargePreprocessorResources(usage: PreprocessorResourceUsage,
                            charge: PreprocessorResourceCharge,
                            limits: PreprocessorResourceLimits)
    -> Charged(PreprocessorResourceUsage)
     | Exceeded(ResourceLimitExceeded)
```

Limits are immutable `PreprocessorOptions`. Charging is defined by semantic events, not by how an
implementation happens to loop:

| event                                               | exact charge                                                                                                                                                                |
| --------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------- |
| advance a scan level past input                     | one inspected element for each `Token                                                                                                                                       | Trivia` element consumed at that scan level; lookahead without commitment is free                                |
| collect a macro argument                            | one argument element for each `Token                                                                                                                                        | Trivia`added to a lexical`MacroInvocationArg`; separators and a derived variadic aggregate range are not charged |
| begin playback of a well-formed non-busy invocation | one expanded invocation and observed expansion depth `length(busyMacros) + 1`                                                                                               |
| enter an included unit                              | observed include depth `length(inputStack)` before the child push, so the primary unit has depth zero and its first include has depth one                                   |
| materialize expansion output                        | one emitted token for each new active token terminal produced by macro playback, parameter copying, stringization, paste, a builtin, or conditional-predicate normalization |
| attempt token paste                                 | the UTF-8 byte length of `concatenatedSpelling`, including an invalid attempt                                                                                               |

Generated rescan input is inspected again because it is a distinct scan level. Structural reuse of
an existing terminal by a parent result, include splicing, primary-source passthrough, inactive
copying, and exact written-spelling recovery do not charge emitted tokens; they create no
expansion-amplified token payload. A token materialized by an included macro is charged in the
child and is not charged again when spliced.

`ChargePreprocessorResources` adds the five cumulative deltas, takes the maximum of the two depth
observations, and compares the resulting seven usage fields to their correspondingly named limits.
All arithmetic is checked unsigned arithmetic. The charge is atomic: if any field would overflow
or exceed its limit, `Exceeded` chooses the first kind in `ResourceLimitKind` order and returns the
attempted value; no usage field changes and no successful result node from that action is
published.

At an action boundary whose written extent is already known, exceeding a limit publishes the
applicable failed expansion and recovers with the exact written spelling, then continues after that
extent. If a limit is reached while discovering an extent (for example while collecting a macro
argument), the current scan publishes `ExpandedRecovery(unprocessed = Some(remainingRange),
result = [])` and stops that scan without inspecting the remainder. The immutable predecessor
retains the entire range. A caller therefore never performs an unbounded recovery scan merely to
find a later delimiter. Resource behavior never depends on the host call-stack limit or available
heap size.

Busy-definition suppression terminates semantic macro cycles. Include-stack identity terminates
include cycles. Resource limits bound acyclic but exponentially growing expansion. Implementations
must use an explicit work stack or scheduler continuation when host recursion could be proportional
to input nesting.

`PP-LIM-001`: Equal inputs and limits fail at the same semantic occurrence with the same partial
representation, state, diagnostics, and usage, independent of thread count or evaluator recursion
strategy.

`PP-LIM-002`: Hitting a limit cannot publish a partially filled successful node. A failed node and
its recovered result are published atomically.

`PP-LIM-003`: The fields of `PreprocessorResourceUsage` are exactly the fold of the table above.
Caching, vectorized scanning, provider implementation, and structural sharing cannot add or remove
a charge.

`PP-LIM-004`: A rejected charge leaves usage unchanged. Recovery passthrough is exempt from emitted
token charging only because it reproduces already written input without expansion; any synthesized
replacement remains chargeable.

## Validation and unit-test seams

The following primitives are independent, immutable queries and are unit-testable without a parser,
type checker, file system, or diagnostic-text renderer:

```text
StructurePreprocessor
CompileMacroDefinition
ClassifyDefinitionFlavor
CollectMacroInvocationArguments
LookupMacro / DefineMacro / UndefineMacro
PrescanMacroArgument
SubstituteMacroOperation
StringizeMacroArgument
LexPasteSequence
RescanMacroResult
EvaluateConditionalBranch
SelectConditionalBranch
DecodeIncludeRequest
ResolveInclude / CreateIncludedSourceView / CreateIncludedLexicalContext
GetBuiltinMacroCatalog / ExpandBuiltinMacro
QueryPreprocessorFeature
LookupRegisteredDirective / ApplyRegisteredDirective
BuildPreprocessorPersistentState / ValidatePreprocessorProviderBindings
BeginPreprocessorUnit / EndPreprocessorUnit
EnterIncludedPreprocessorUnit / LeaveIncludedPreprocessorUnit
ChargePreprocessorResources
ValidatePreprocessorState
ValidatePreprocessorProvenance
```

Required mocks are narrow:

- `IncludeSystem` maps an `IncludeSystemRequest` and revision to `IncludeSystemResult`;
- `BuiltinMacroProvider` exposes a catalog and maps `BuiltinMacroExpansionRequest` to token
  descriptions;
- `PreprocessingTokenLexer` implements `LexPasteSequence` for a language-rule revision;
- `PreprocessorFeatureSet` answers `PreprocessorFeatureQuery`; and
- `PreprocessorDirectiveProvider` looks up immutable directive definitions and receives only the
  declared operand and state-slot projection.

Representative table-driven tests include:

- `#define F(x)` versus `#define F (x)`;
- trivia between a function-like invocation name and `(`;
- zero arguments versus one empty argument;
- nested-parenthesis commas and variadic comma preservation;
- expanded, unexpanded, stringized, and pasted uses of the same argument;
- direct recursion, mutual recursion, and a same-macro nested argument that must prescan;
- comments and line continuations in stringization;
- empty, single-token, multi-token, and trivia-forming paste results;
- inactive definitions, nested conditionals, short-circuit expressions, and malformed groups;
- success, recovered evaluation, and every skipped-branch reason with retained expanded operand and
  parsed-expression artifacts;
- table-driven `PpExpr` cases shared with chapter 7, proving conditional selection uses the exact
  `EvalPreprocessorConst` result rather than a second arithmetic implementation;
- include cycles, `#pragma once`, repeated distinct include views, child EOF exclusion, and exact
  field-by-field state propagation;
- a resolver that returns the same source for two directive occurrences, proving that resolution
  is shared while `CreateIncludedSourceView` produces two provenance-distinct views;
- `#line` effects on direct and nested builtin expansions;
- initial builtin/predefined ordering, provider-binding mismatch, primary begin/end, nested
  include enter/leave, chained persistent states, and independent fresh seeds;
- provider unavailable-revision/schema failures as task failures, plus map-backed mocks for every
  request/result alternative;
- every resource boundary at `limit - 1`, `limit`, and `limit + 1`; and
- every semantic resource event, failed atomic multi-field charges, overflow, and unprocessed-range
  recovery while discovering an invocation extent; and
- round-trip serialization, structural copy, generic CST traversal, and full provenance validation
  for every output-node alternative.

Tests compare typed results, state values, CST fields, token sequences, activity maps, and provenance
graphs. They do not depend on allocator addresses, container iteration, cache behavior, scheduler
order, or rendered diagnostic prose.

`PP-TST-001`: Every preprocessing rule has at least one direct primitive test and one composition
test through `ExpandPreprocessor`. Every failure and suppression alternative has a serialization and
provenance-validation test.

`PP-TST-002`: A mock dependency that returns the same versioned result as production must produce
the same semantic output. Dependency injection cannot require subclassing CST nodes or mutating a
compiler-global preprocessor.
