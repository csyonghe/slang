# Calls, conversions, overload resolution, and generics

This chapter defines the semantic primitives used to select a callable and elaborate its arguments.
It separates five concerns that are intertwined in the current checker:

1. generic argument mapping and solving;
2. call argument/receiver mapping;
3. conversion search and explicit conversion plans;
4. semantic candidate comparison; and
5. failed-candidate selection for diagnostics.

A trial never mutates syntax, and committing a winner never repeats semantic search.

## Distinct type relations

The replacement frontend does not use one implementation-shaped witness domain for unrelated
relations. It does define a first-class subtype-witness algebra because interface
evidence is an operational runtime value:

```text
Δ ⊢ τ ≡ ρ       ⇝ TypeEqualityProof
Δ ⊢ τ ≤repr ρ   ⇝ RepresentationAdjustmentPath
Δ ⊢ I refines J ⇝ InterfaceRefinementProof
Σ; Δ ⊢ τ <: I   ⇝ SubtypeWitness
Σ; Δ ⊢ τ ↝ ρ    ⇝ ConversionResult
```

- equality is symmetric and substitutive;
- representation adjustment follows the single class-base chain or a registered standard rule;
- interface refinement relates contracts;
- interface subtyping is constructive witness-table evidence from a concrete/self/generic type to
  a contract; and
- conversion is a directed computation that can change representation or invoke code.

`CVR-REL-001`: A proof from one relation cannot be used as another without a named bridge rule. For
example, an interface witness can construct an existential-pack conversion, but is not itself a
representation-adjustment path.

Chapter 15 defines the witness operations and the exact one-to-one mapping from
`LookupSubtypeWitness` to frontend IR. Concrete struct inheritance is absent from the
representation relation.

## Conversion context

```text
ConversionRequest = {
    expression: TypedExpr,
    source: TypeId,
    sourceCategory: ValueCategory,
    target: TypeId,
    site: CoercionSite,
    explicitness: Implicit | Explicit,
    environment: ConversionEnvironmentId
}

ConversionEnvironment = {
    semanticEnvironment: SemanticEnvironmentId,
    genericEnvironment: GenericEnvironmentId,
    visibilityContext: VisibilityContext,
    availableEffects: EffectAllowance,
    worldAssumption: BooleanCapabilityPredicate
}

ConversionEnvironmentId = ContentId<ConversionEnvironment>

TypeCoercibilityRequest = {
    source: TypeId,
    target: TypeId,
    explicitness: Implicit | Explicit,
    environment: ConversionEnvironmentId
}

CoercionSite = General | Assignment | Argument | Return | Initializer |
               ExplicitCast | GenericConstraint
```

The source category is part of the request because loading, preserving a physical location, and
passing an abstract storage are not type-only operations.

`CVR-CTX-000`: `ConversionRequest.expression.classifier` must be
`ValueClassifier(source, sourceCategory)`. A non-value classifier is rejected before conversion
search; duplicated endpoint fields are a query-key projection validated against the expression,
not an independent authority.

`CVR-CTX-001`: `ConversionEnvironmentId` is part of the coercion query key. Two requests with equal
source/target types but different visible user conversions, access permissions, effects,
capability assumptions, generic evidence, language rules, or standard-environment revisions are
not interchangeable.

`CVR-CTX-002`: The exact boolean `worldAssumption`, including negated atoms and keyhole choices, is
part of the query key because a conversion candidate may have a genuinely concrete availability
requirement. It cannot be replaced by a positive `CapabilityRequirement`; an else branch such as
`!HasAtom(A)` would lose information. An ordinary operation or callable capability requirement is
not an applicability predicate: the selected conversion records it as a `CapabilityUse` for caller
inference even when the current symbolic region does not already imply it.

`PlanTypeCoercibility(TypeCoercibilityRequest)` searches with a symbolic `RValue` at the
`GenericConstraint` site. It rejects load, physical-storage, abstract-storage, lambda-capture, initializer, and other
expression-dependent edges. Success produces `TypeCoercibilityEvidence` containing both the typed
witness and rank under the exact environment revision; it does not manufacture a `TypedExpr`.

## Conversion plans

```text
StandardConversionId = StandardEnvironmentRuleId

ValueReadPlan<S: WitnessTableState> =
    LoadPhysicalStorage(proof: PhysicalStorageProof)
  | InvokeAbstractGetter(callable: CallableValue<S>)
  | ResolveAbstractStorageThroughReference(plan: InternalRefStoragePlanAt<S>)

ConversionOperation<S: WitnessTableState> =
    Identity
  | ReadStorage(storage: StorageRef, read: ValueReadPlan<S>)
  | Numeric(op: StandardConversionId)
  | BitCast(op: StandardConversionId)
  | PointerAdjustment(path: RepresentationAdjustmentPath)
  | ReferenceAdjustment(storage: PhysicalStorageProof, access: StorageAccessMode)
  | Aggregate(elements: NodeList<ConversionPlan<S>>)
  | Splat(element: ConversionPlan<S>, shape: ShapeValue)
  | Reshape(elements: NodeList<ConversionPlan<S>>, shape: ShapeValue)
  | OptionalInject(value: ConversionPlan<S>)
  | OptionalMap(value: ConversionPlan<S>)
  | EnumConvert(rule: StandardConversionId)
  | PackExistential(witness: SubtypeWitnessRef<S>)
  | OpenExistential(opening: OpenedTypeId, nested: ConversionPlan<S>)
  | UserDefined(callee: ResolvedDeclRefAt<S>, before: NodeList<ConversionPlan<S>>,
                after: Option<ConversionPlan<S>>)
  | CapturelessLambdaToFunction(expected: CallableSignature,
                                thunk: SynthesizedDeclId)
  | LambdaToCallable(expected: TypeId, lambdaEnvironment: SynthesizedDeclId,
                    witness: Option<SubtypeWitnessRef<S>>)
  | Initialize(plan: InitializationPlanIdAt<S>)
  | Recovery(error: ErrorId)
```

The plan includes source/target types, operation, evidence, semantic-use edges, and origin as defined
in chapter 5. It is a proof-carrying elaboration recipe, not merely a numeric cost. Primitive edges
record direct effect/capability uses; an imported user conversion records published contract uses;
a local user conversion records its stable callee identity plus the exact stage-correct witness
resolutions needed by its specialization evidence. Composite plans contain the
canonical union of their edge and nested-plan uses.

`CVR-PLAN-001`: Applying a validated conversion plan to an expression is deterministic and cannot
perform lookup, generic inference, or further conversion search.

`CVR-PLAN-002`: A plan's validator recursively proves that each operation's input/output endpoints
compose and that the operation is permitted at the request's site/explicitness.

`CVR-PLAN-003`: A lambda conversion chooses one explicit representation. A raw function conversion
requires no captures and records the exact static-thunk declaration output. A capturing lambda
produces a synthesized lambda environment and, when required, callable-interface conformance
evidence; it cannot use the raw-function alternative.

The lambda alternatives name the exact synthesized declaration output, not merely its group: one
group may contain the lambda-environment type, initializer, invocation method, thunk, and
conformance. That
output's semantic identity still contains its `SynthesisKey`, so validation can recover and check
the owning atomic group.

`CVR-PLAN-004`: Applying a conversion or access plan contributes every stored `PlanSemanticUses`
edge exactly once to its containing typed expression. No caller replaces a local user-conversion
edge with a flat effect/capability summary, and the selected main callable's use edges do not stand
in for conversion-plan edges. A callable conversion follows the same capability split as an
ordinary call: its ordinary/transitive requirement becomes a keyed use, while only its optional
concrete availability requirement is proved under `ConversionEnvironment.worldAssumption` during
selection. The ordinary use is not rejected merely because that assumption does not imply it.
`PlanSemanticUses.capabilities` retains the complete `CapabilitySelectionAt<S>`: its exact region,
keyed ordinary uses, and either no concrete source or the complete proven source set. Composing a
conversion or embedding it in an access plan uses `CAP-SEL-004` under an identical region; it cannot
union only ordinary uses, discard a concrete source, or reuse a proof from another region.

`CVR-PLAN-005`: `PackExistential` and a lambda conversion's optional callable conformance store the
exact stage-appropriate `SubtypeWitnessRef<S>`, whose semantic operand is a
`SubtypeWitnessId`. A bound generic witness, specialized generic table, lookup, or
existential witness is valid evidence; a bare `WitnessTableId` is not. When evidence is synthesized,
plan construction depends on publication of the complete atomic `SynthesisGroup` or carries the
authorized construction-stage resolutions described in chapter 15; it never invents a frozen
conformance reference for a runtime witness parameter.

`CVR-PLAN-006`: `LoadPhysicalStorage` is valid only for `PhysicalStorage(storage)` and its proof names
that exact storage. `InvokeAbstractGetter` is valid only for `AbstractStorage(storage)`, names the
selected getter in its accessor contract, and retains the getter's effects, capabilities, receiver,
and index evaluation requirements. `ResolveAbstractStorageThroughReference` is valid only when
`PlanStorageAccessAt<S>` selected it for `ReadValueAccess` under rule `EXP-STO-002`, where the getter was absent,
the fixed Slang 2026 getter-to-`constref` fallback rule authorized the operation, and the stored internal plan immediately
dereferences the raw ref-accessor result. A failed present getter can never produce this alternative.
None of these read plans changes the source expression's abstract-storage classifier or makes it
eligible for a physical operand mode.

`CVR-PLAN-007`: `ReferenceAdjustment` requires a `PhysicalStorage` and a
`PhysicalStorageProof` for that exact endpoint and requested access/lifetime. It cannot consume an
abstract property/subscript, getter/setter plan, write-back temporary, or rvalue. Passing a
physical-operand parameter normally records the proof for its invocation-instantiated physical
storage requirement in the `StorageAccessPlan`; it does not rely on an implicit conversion to manufacture
referenceability.

`CVR-PLAN-008`: An implicit conversion plan contains at most one `UserDefined` operation. The
`before` and `after` children of that operation contain only standard conversion operations; neither
may contain another `UserDefined` operation. This is a language invariant, not a configurable search
budget. An explicit cast may invoke a separately declared explicit conversion, but it does not make
a two-user-defined-step implicit path applicable.

Conversion failure is structured output, not diagnostic text:

```text
ConversionFailure<S: WitnessTableState> =
    NoConversionPath(source: TypeId, target: TypeId, site: CoercionSite)
  | ExplicitConversionRequired(rule: RuleId)
  | AmbiguousMinimalPlans(plans: NonEmpty<ConversionPlan<S>>, rank: ConversionCost)
  | EffectNotAllowed(use: EffectUse<S>, allowance: EffectAllowance)
  | ConcreteCapabilityNotAvailable(requirement: CapabilityRequirement,
                                   assumption: BooleanCapabilityPredicate,
                                   failure: CapabilityFailure)
  | AccessNotPermitted(decision: VisibilityDecision)
  | RecursiveUserConversion(declaration: DeclRef,
                             source: TypeId, target: TypeId)
  | MultipleUserDefinedImplicitConversions(path: NonEmpty<DeclRef>)
  | ConversionSearchLimit(visitedStates: UInt32,
                          configuredLimit: UInt32)
  | InvalidRecoveryOnly(error: ErrorId)
```

Every alternative preserves the request endpoints through its enclosing `ConversionResult`; a
renderer may add candidate traces, but tests compare this algebra directly.

Unqualified `ConversionOperation` and `ConversionFailure` mean their `<Published>` forms.

## Conversion rank

```text
BoundedNat = {
    value: UInt64,
    maximum: UInt64
}

ConversionCost = {
    category: ConversionCostCategory,
    distance: BoundedNat,
    tieProperties: NodeMap<RankPropertyId, BoundedNat>
}

ConversionEdgeRank = {
    cost: ConversionCost,
    isUserDefined: Bool
}

ConversionSearchRank = {
    cost: ConversionCost,
    userDefinedStepUsed: Bool
}

ConversionSearchRankComposition =
    RankedConversionPath(rank: ConversionSearchRank)
  | UserDefinedStepOverflow

ConversionCostCategory = StandardEnvironmentConversionCostCategoryId
```

Every component in one ranking query uses the same versioned `maximum` and satisfies
`value <= maximum`. Comparison first validates equal maxima, then compares exact values under the
named rank relation. The standard environment registers the established `kConversionCost_*`
categories (`None`, generic-parameter/lambda/array/layout/reference adjustments, literal and numeric
conversions, interface/optional/pointer conversions, rank/shape conversions, parameter-pack/default/
general/explicit/type-coercion categories, and `Impossible`) under stable names. Composite names such
as `ScalarIntegerToFloatMatrix` are categories in that registry rather than arithmetic expressions
in this algebra. Their numeric encodings are not an ABI, mangling input, serialized calling
convention, or promise that the implementation will preserve particular integer constants.

`CVR-RANK-000`: `ConversionCost` is canonical. `tieProperties` stores only nonzero values, is keyed
and ordered by the versioned property registry, and omits every missing/zero entry; each stored
`BoundedNat.maximum` equals the registry maximum used by the other scalar components in that
ranking query. Consequently two costs that compare equal are byte-identical. Construction,
deserialization, and registered edge loading all perform this validation before search.

The registry supplies a versioned total order over categories, preserving the existing relative cost
order. Smaller is better. After category comparison, `distance` and registered tie properties compare
lexicographically. Whether an edge is user-defined is search metadata, not another rank dimension;
the user-defined edge's registered category already supplies its semantic cost. An implicit plan
contains at most one user-defined conversion step.

Explicit-only conversions have the same rank domain but are inapplicable to implicit requests.
Recovery conversions do not have a semantic rank.

Path composition takes the single worse whole cost under that total order; it never sums costs or
constructs a synthetic component-wise tuple:

```text
zeroRank = ConversionCost(category(None), 0, {})
zeroSearchRank = ConversionSearchRank(zeroRank, false)
zeroSearchRankComposition = RankedConversionPath(zeroSearchRank)

combineSearchRanks(left, right) =
    UserDefinedStepOverflow
        when left = UserDefinedStepOverflow or right = UserDefinedStepOverflow
    UserDefinedStepOverflow
        when left = RankedConversionPath(l) and
             right = RankedConversionPath(r) and
             l.userDefinedStepUsed and r.userDefinedStepUsed
    RankedConversionPath(ConversionSearchRank(
        cost = worseByConversionCostOrder(l.cost, r.cost),
        userDefinedStepUsed = l.userDefinedStepUsed or r.userDefinedStepUsed))
        when left = RankedConversionPath(l) and
             right = RankedConversionPath(r)

edgeSearchRank(edge) =
    RankedConversionPath(ConversionSearchRank(edge.cost, edge.isUserDefined))
extendSearchRank(path, edge) =
    combineSearchRanks(RankedConversionPath(path), edgeSearchRank(edge))
```

Tie-property keys and their comparison priority are versioned standard-environment data; missing
entries are zero and vectors compare lexicographically by that declared key order after category and
distance. Every component is non-negative. `worseByConversionCostOrder` returns one of its two
operands: the greater cost, or their byte-identical canonical value when they compare equal. For an
implicit request, composition rejects a path when the prefix already used a user-defined edge and
the next edge is user-defined; the resulting bit therefore proves zero-or-one rather than recording
an additive count.

`CVR-RANK-001`: Rank values preserve the existing semantic cost categories in the standard
environment. Only their ordered comparison is observable; their numeric encoding has no ABI status.
Changing the order is a language-version change. Costs are never added either along one conversion
path or across call arguments.

`CVR-RANK-002`: Structurally different minimal plans with identical rank are an ambiguous conversion
unless the canonical-plan rule proves they denote the same operation.

`CVR-RANK-003`: `combineSearchRanks` is a closed, associative operation on
`ConversionSearchRankComposition` with `zeroSearchRankComposition` as identity and
`UserDefinedStepOverflow` as an absorbing value. For ranked inputs its cost is monotone in both
arguments under rank order; combining any path containing two user-defined steps yields overflow
independent of grouping. Search converts that overflow plus the separately accumulated edge trace
to `MultipleUserDefinedImplicitConversions(path)`. `extendSearchRank` is the left-fold specialization
for one edge. Unit/property tests establish these laws for every registered rank property;
best-first pruning is valid only because extension cannot improve an existing path.

## Conversion search

The standard environment exposes conversion edges with preconditions, rank components, and plan
constructors. Language primitives such as identity, physical load, abstract getter read,
existential pack, aggregate conversion,
and error recovery are registered by rule ID through the same interface.

```text
PlanCoercion(request) -> ConversionResult
```

Search states are `(type, valueCategory, ConversionSearchRank, site)`. A deterministic best-first
search explores edges in whole-cost and stable rule-ID order, prunes a state when an equal/better
cost with the same-or-weaker user-step usage was seen, and stops only after every path that could tie
the best result is known.

```text
edge(τ,q,ρ,q',π,r)    allowed(edge, request)
extendSearchRank(p,r) = RankedConversionPath(p')
------------------------------------------------ CVR-STEP-001
(τ,q,p) --π--> (ρ,q',p')
```

`CVR-STEP-002`: When `extendSearchRank` returns `UserDefinedStepOverflow`, that path is rejected as
`MultipleUserDefinedImplicitConversions` with the exact accumulated user-defined edge trace. It
does not enter the search-state queue with an invented worst cost.

`CVR-SRCH-001`: Conversion cycles terminate by rank/state dominance, not an “impossible” cache
sentinel that changes meaning during recursion.

`CVR-SRCH-002`: `canCoerce` is the predicate `PlanCoercion(request) is Applicable`; it does not run a
different no-output branch of the coercion implementation.

`CVR-SRCH-003`: A user-defined conversion candidate is itself resolved with a conversion-search
budget that forbids recursive reuse of the same conversion declaration/request state. A rejected
cycle returns a structured conversion failure.

## Call arguments and receiver mapping

```text
CallInput = {
    receiver: Option<TypedExpr>,
    arguments: NodeList<SourceArgument>,
    explicitGenericArguments: NodeList<CheckedGenericArgument>,
    expectedResult: Option<TypeId>,
    callKind: Ordinary | Operator | Subscript |
              InitializationCallable(strategy: InitializationStrategy)
}

CheckedGenericArgument = {
    id: AnyASTNodeId<Typed>,
    label: Option<Name>,
    value: GenericArg,
    sort: GenericParameterSort,
    origin: Origin
}

ReceiverBinding = {
    value: TypedExpr,
    source: ExplicitReceiver | ImplicitReceiver(lookupPath: LookupPath),
    origin: Origin
}

ArgumentBinding =
    ExplicitArgument(source: SourceArgumentId)
  | DefaultArgument(value: TypedExpr,
                    origin: Origin)

ArgumentMap = {
    receiver: Option<ReceiverBinding>,
    parameters: NodeMap<ParameterKey, ArgumentBinding>,
    packBindings: NodeMap<ParameterKey, NodeList<SourceArgumentId>>
}
```

Argument mapping checks positional/label rules, arity, defaults, packs, and duplicate assignments
without examining argument types. A source label is used only to choose a `ParameterKey` in this
mapping step. Labels never participate in function identity, redeclaration, overload identity,
function conversion, mangling, or ABI.

`SourceArgument`, `SourceArgumentId`, and `SourceCallRole` are the shared chapter 5 domains. The
same identities are retained when property/subscript syntax captures sources and when an accessor
call maps them; access planning never creates a parallel argument numbering scheme.

`InitializationCallable` is used only after chapter 16's initialization model admits a callable
strategy and supplies an explicit initialization target. `ExplicitSingle`, C-style casts, aggregate
initialization, and default/value initialization are not ordinary call kinds; the initialization
query may reuse this chapter's callable candidate machinery without conflating the judgments.

`OVL-MAP-001`: Each non-pack parameter has exactly one explicit or default binding. Each source
argument is consumed exactly once. Pack bindings preserve source order and are keyed by parameter
identity.

`OVL-MAP-002`: The receiver maps only to `FuncType.receiver`; it is never counted as ordinary
argument zero. Accessor/container parameters that current `getFuncType` prepends are explicit
ordinary parameters with stable IDs in the checked signature.

`OVL-MAP-003`: Every `ReceiverBinding.value` and explicit/default argument value is value-classified.
Every explicit binding resolves to exactly one `SourceArgument` in the `CallInput`; every default
binding contains the checked, substituted default expression used by the candidate. Thus committing
a winner does not look a default expression up or check it again.

`OVL-MAP-004`: The enclosing `parameters` map key is the sole parameter identity of a binding.
`defaultedParameters(map)` is the canonically ordered set of exactly those keys whose value is
`DefaultArgument`; it is derived and never serialized in `ArgumentMap`. Likewise each
`packBindings` key names a pack parameter in the same checked signature, and its source list equals
the explicit-argument sources assigned to that parameter in source order. Ranking projections must
recompute these views from the map and cannot accept an independently supplied default set.

`OVL-MAP-005`: Callable declaration identity contains the declared function `NameKey`, result type,
ordered alpha-normalized generic parameter sorts, structural receiver slot when present, and ordered
checked parameter types. A receiver/parameter type includes its structural passing mode; a
parameter label does not. Renaming a generic parameter cannot create another function or distinguish
overloads, while changing generic arity or a type/value/pack parameter sort does so even when that
parameter is otherwise unused. Generic constraints/defaults, parameter names/defaults, and
parameter labels do not independently enter declaration identity; they remain checked
declaration/applicability facts. Any bound variables occurring in the identity fields use their
canonical alpha-normalized form.

Argument-map failures are equally explicit:

```text
ArgumentMapFailure =
    MissingReceiver(required: ReceiverSlot)
  | UnexpectedReceiver
  | TooManyArguments(unconsumed: NonEmpty<SourceArgumentId>)
  | MissingArguments(parameters: NonEmpty<ParameterKey>)
  | UnknownLabel(argument: SourceArgumentId, label: Name)
  | DuplicateParameter(parameter: ParameterKey,
                       arguments: NonEmpty<SourceArgumentId>)
  | PositionalAfterNamed(argument: SourceArgumentId)
  | InvalidPackBinding(parameter: ParameterKey,
                       arguments: NodeList<SourceArgumentId>,
                       rule: RuleId)

RecoveryArgumentMap = {
    receiver: Option<ReceiverBinding>,
    parameters: NodeMap<ParameterKey, ArgumentBinding>,
    unboundParameters: CanonicallyOrderedSet<ParameterKey>,
    unconsumedArguments: NodeList<SourceArgumentId>,
    failures: NonEmpty<ArgumentMapFailure>
}
```

## Passing-mode applicability

Argument preparation branches first on the complete structural `ParamPassingMode`. `InMode` may use
ordinary conversion search; `OutMode` and `InOutMode` require exact storage identity despite sharing
the abstract operand domain. A `PhysicalOperand` selects a direct or exact accessor-produced physical
endpoint first and then checks storage identity; it never asks ordinary conversion search to
manufacture referenceability.

| Mode              | Required source                                                                              | Plan                                                            |
| ----------------- | -------------------------------------------------------------------------------------------- | --------------------------------------------------------------- |
| `InMode`          | any convertible value or storage; abstract immutable input                                   | load if needed, implicit conversion, pass value                 |
| `OutMode`         | writable physical or abstract destination of exactly the parameter value type                | abstract mutable output; no pre-read; normal-return commit only |
| `InOutMode`       | exclusive readable/writable physical or abstract storage of exactly the parameter value type | abstract mutable input/output; normal-return commit only        |
| `ConstRefMode(r)` | direct physical storage or exact `ReadAccess` reference accessor, with storage identity      | pass the exact physical endpoint through an immutable read view |
| `RefMode(r)`      | direct physical storage or exact `ReadWriteAccess` reference accessor, with storage identity | pass the exact physical endpoint under mutable exclusive access |

The receiver uses the same table with any receiver-specific restrictions.

`OVL-MODE-011`: The source parameter-mode spellings are exactly `in`, `out`, `inout`,
`__constref`, and `__ref`, mapping respectively to the five rows above. `in out` and `borrow` are not
aliases and are diagnosed. `readonly` and `writeonly` retain their separately registered
access-qualifier roles and never synthesize a `ParamPassingMode`.

```text
AccessEnvironment = {
    semanticEnvironment: SemanticEnvironmentId,
    visibilityContext: VisibilityContext,
    worldAssumption: BooleanCapabilityPredicate,
    invocationLifetime: LifetimeId,
    callOrigin: Origin
}

AccessEnvironmentId = ContentId<AccessEnvironment>

ResolvedArgumentInput =
    ExplicitCallArgumentInput(argument: SourceArgument,
                              expansion: ExpansionPath)
  | DefaultCallArgumentInput(value: TypedExpr, origin: Origin)

ResolvedCallSlotBinding =
    ReceiverCallSlotBinding(binding: ReceiverBinding)
  | ParameterCallSlotBinding(parameter: ParameterKey,
                             input: ResolvedArgumentInput)

callSlotInput(ReceiverCallSlotBinding(b)) = b.value
callSlotInput(ParameterCallSlotBinding(_, ExplicitCallArgumentInput(a, _))) = a.value
callSlotInput(ParameterCallSlotBinding(_, DefaultCallArgumentInput(v, _))) = v

callSlotSourceRole(ReceiverCallSlotBinding(_)) = Some(ReceiverSourceRole)
callSlotSourceRole(ParameterCallSlotBinding(
    _, ExplicitCallArgumentInput(a, expansion))) =
        Some(ArgumentSourceRole(a.id, expansion))
callSlotSourceRole(ParameterCallSlotBinding(_, DefaultCallArgumentInput(_, _))) = None

ArgumentPlanningContext = {
    signature: CallableSignatureId,
    input: CallInput,
    argumentMap: ArgumentMap,
    accessEnvironment: AccessEnvironmentId,
    conversionEnvironment: ConversionEnvironmentId,
    expressionContext: ExpressionCheckContextId,
    operationSite: SemanticOperationSiteAssignment
}

ArgumentPlanningContextId = ContentId<ArgumentPlanningContext>

callSlotOrdinal(signature, ReceiverSlotRole) = 0
callSlotOrdinal(signature, ParameterSlotRole(k)) =
    1 + unique(resolve(signature).parameterSlots, _.key = k).ordinal

argumentSlotPlanningRole(signature, slot) =
    { ArgumentSlotPlanningRule, callSlotOrdinal(signature, slot) }

ArgumentPlanningContextFailure =
    SlotNotPresentInSignature(slot: BoundCallSlot,
                              signature: CallableSignatureId)
  | BindingDoesNotMatchSlot(slot: BoundCallSlot,
                            binding: ResolvedCallSlotBinding)
  | BindingDoesNotMatchArgumentMap(slot: BoundCallSlot)
  | BindingDoesNotMatchCallInput(slot: BoundCallSlot)
  | PlanningInputNotValue(actual: Classifier)
  | ConversionEnvironmentProjectionMismatch(
        environment: ConversionEnvironmentId,
        context: ExpressionCheckContextId)
  | AccessEnvironmentProjectionMismatch(
        environment: AccessEnvironmentId,
        context: ExpressionCheckContextId)
  | ArgumentOperationSiteRejected(failure: SemanticOperationSiteFailure)
  | ArgumentOperationSiteRoleMismatch(expected: SemanticOperationSiteRole,
                                      actual: SemanticOperationSiteRole)

instantiatePhysicalStorageRequirement(
    mode: ParamPassingMode,
    invocationLifetime: LifetimeId)
    -> PhysicalStorageRequirement

PhysicalStorageIdentityProof = {
    storageType: TypeId,
    parameterType: TypeId,
    equality: TypeEqualityProofId
}

PhysicalParameterSourceAt<S: WitnessTableState> =
    DirectPhysicalParameterSource(input: TypedExpr,
                                  storage: PhysicalStorageRef)
  | AccessorProducedPhysicalParameterSource(
        input: TypedExpr,
        plan: ParameterReferenceAccessorPlanAt<S>)

physicalParameterStorage(DirectPhysicalParameterSource(_, s)) = s
physicalParameterStorage(AccessorProducedPhysicalParameterSource(_, p)) =
    p.endpoint.output.storage

PhysicalIdentityAdaptationAt<S: WitnessTableState> = {
    source: PhysicalParameterSourceAt<S>,
    identity: PhysicalStorageIdentityProof
}

ApplicableAbstractConversionAt<S: WitnessTableState> = {
    plan: ConversionPlan<S>,
    rank: ConversionCost
}

ExactStorageAdaptation = {
    source: TypedExpr,
    storage: PhysicalStorageRef | AbstractStorageRef,
    parameterValueType: TypeId,
    equality: TypeEqualityProofId
}

ArgumentAdaptationAt<S: WitnessTableState> =
    AbstractConversion(conversion: ApplicableAbstractConversionAt<S>)
  | ExactStorageIdentity(adaptation: ExactStorageAdaptation)
  | PhysicalIdentity(adaptation: PhysicalIdentityAdaptationAt<S>)

ArgumentAdaptationFailureAt<S: WitnessTableState> =
    InvalidArgumentPlanningContext(failure: ArgumentPlanningContextFailure)
  | AbstractConversionInapplicable(failure: ConversionFailure<S>)
  | AbstractConversionRecovered(plan: ConversionPlan<S>, error: ErrorId)
  | ExactStorageAdaptationFailed(failure: ParamPassingModeFailureAt<S>)
  | PhysicalAdaptationFailed(failure: ParamPassingModeFailureAt<S>)

ArgumentAdaptationResultAt<S: WitnessTableState> =
    AdaptedArgument(adaptation: ArgumentAdaptationAt<S>)
  | ArgumentNotAdapted(failure: ArgumentAdaptationFailureAt<S>)

ArgumentAccessFailureAt<S: WitnessTableState> =
    InvalidArgumentVisibilityContext(failure: ArgumentPlanningContextFailure)
  | AdaptationDomainMismatch(required: OperandDomain,
                             actual: OperandDomain)
  | ParamPassingModeAccessFailed(failure: ParamPassingModeFailureAt<S>)

ArgumentAccessResultAt<S: WitnessTableState> =
    PlannedArgumentAccess(plan: StorageAccessPlan<S>)
  | ArgumentAccessNotPlanned(failure: ArgumentAccessFailureAt<S>)

PlanArgumentAdaptationAt<S>(slot: BoundCallSlot,
                            binding: ResolvedCallSlotBinding,
                            parameter: FuncTypeParamInfo,
                            context: ArgumentPlanningContextId)
    -> CheckResult<ArgumentAdaptationResultAt<S>>

PlanArgumentAccessAt<S>(slot: BoundCallSlot,
                        binding: ResolvedCallSlotBinding,
                        parameter: FuncTypeParamInfo,
                        adaptation: ArgumentAdaptationAt<S>,
                        context: ArgumentPlanningContextId)
    -> CheckResult<ArgumentAccessResultAt<S>>

PhysicalParameterBindingProofAt<S: WitnessTableState> = {
    mode: ParamPassingMode,
    source: PhysicalParameterSourceAt<S>,
    storage: PhysicalStorageRef,
    parameterValueType: TypeId,
    identity: PhysicalStorageIdentityProof,
    instantiatedRequirement: PhysicalStorageRequirement,
    physicalStorage: PhysicalStorageProof,
    accessEnvironment: AccessEnvironmentId
}

PhysicalParameterSource = PhysicalParameterSourceAt<Published>
PhysicalIdentityAdaptation = PhysicalIdentityAdaptationAt<Published>
ArgumentAdaptation = ArgumentAdaptationAt<Published>
ArgumentAdaptationFailure = ArgumentAdaptationFailureAt<Published>
ArgumentAdaptationResult = ArgumentAdaptationResultAt<Published>
ArgumentAccessFailure = ArgumentAccessFailureAt<Published>
ArgumentAccessResult = ArgumentAccessResultAt<Published>
PhysicalParameterBindingProof = PhysicalParameterBindingProofAt<Published>
PlanArgumentAdaptation = PlanArgumentAdaptationAt<Published>
PlanArgumentAccess = PlanArgumentAccessAt<Published>

CheckCallAliasClaims(plans: NodeMap<BoundCallSlot, StorageAccessPlan<Published>>,
                     environment: AccessEnvironmentId)
    -> CallAliasCheck
```

The successful output is the shared `StorageAccessPlan` defined in chapter 12, including
evaluate-once behavior, any exact-type abstract-storage transport and normal-return write-back, the
exact physical endpoint for a physical mode, cleanup condition, and alias class.
Its terminal is always `PassArgument`; storage-read and storage-write terminals belong only to
chapter 7's standalone storage-access query.
Candidate evaluation interns the complete `AccessEnvironment`, stores its ID on both the candidate
and every `ApplicableCallSlotPlan`, and stores the resulting access plan. The query resolves only
that ID; elaboration never reconstructs the environment or plan from a mode, conversion, ambient
invocation lifetime, or call origin.

`OVL-MODE-000`: Both planning primitives first resolve and validate the complete
`ArgumentPlanningContext`. `context.signature` contains `slot` exactly once. A receiver binding is
byte-identical to `context.argumentMap.receiver`. A parameter binding repeats the key in
`ParameterSlotRole(k)` exactly; an explicit input names the unique `SourceArgument` in
`context.input.arguments` selected by `ExplicitArgument(a.id)`, with the same expansion path and
pack binding, while a default input is byte-identical to the `DefaultArgument` stored for `k` and
claims no source argument. `callSlotInput(binding)` is the sole typed input authority and is
value-classified.

Let `e = resolve(context.expressionContext)`, `c = resolve(context.conversionEnvironment)`, and
`a = resolve(context.accessEnvironment)`. The conversion environment's semantic environment,
generic environment, access context, effect allowance, and world assumption equal the corresponding
fields of `e`; the access environment's semantic environment, access context, and world assumption
also equal them. Its invocation lifetime and call origin remain explicit access-only facts. The
operation site satisfies
`ValidateSemanticOperationSite(callSlotInput(binding).id, context.operationSite) = Success(Unit)`
and the final role in its path is
`argumentSlotPlanningRole(context.signature, slot)`. `AccessEnvironment.callOrigin` is diagnostic
provenance and can never be used to derive or repair that site.

Any failed equation selects the corresponding `ArgumentPlanningContextFailure`; no query consults
an ambient expression, conversion, access, argument-map, or operation-site context. These are
scheduler queries: an unavailable dependency leaves the enclosing query `Blocked`, while a ready
execution returns `CheckResult` containing the closed adaptation/access success-or-failure sum.
Only `Success(AdaptedArgument(...))` followed by `Success(PlannedArgumentAccess(...))` can make an
ordinary candidate applicable. Outer recovery and inner failure alternatives feed the structured
recovered-candidate or rejection path instead of masquerading as applicable plans.

`OVL-MODE-001`: Direction failure is distinct from type-conversion failure and names the parameter,
required mode, and actual value category/access.

`OVL-MODE-002`: `OutMode` and `InOutMode` select `ExactStorageIdentity` and require storage whose
value type is exactly the substituted parameter value type. Ordinary conversion search, a conversion
temporary, and materialization of an rvalue are forbidden. An abstract property/subscript may use an
exact-type transport buffer as the
operational implementation of its selected getter/setter plan; this does not make a non-storage
argument applicable and is not a conversion. `OutMode` does not read before the call. `InOutMode`
reads exactly once before the call. Both commit through the selected abstract destination only on
normal return and never on an exceptional exit. Neither physical mode ever materializes a copy or
invokes a getter/setter merely to make a call applicable.

`OVL-MODE-003`: For a physical mode, let `pc = resolve(context)`,
`input = callSlotInput(binding)`, `environment = resolve(pc.accessEnvironment)`, and
`q = instantiatePhysicalStorageRequirement(mode, environment.invocationLifetime)`.
`PlanArgumentAdaptationAt<S>` first selects `DirectPhysicalParameterSource(input, storage)` only
when
`input.classifier = ValueClassifier(storage.valueType, Storage(PhysicalStorage(storage)))`. Otherwise,
only an input classified exactly as
`ValueClassifier(a.valueType, Storage(AbstractStorage(a)))` may proceed. It calls
`PlanParameterReferenceAccessorAt<S>` with the exact request
`(input.id, pc.operationSite, a, mode, pc.accessEnvironment, pc.expressionContext)`. That query
selects `a.accessors.referenceAccessors[mode.access]` by exact key, validates its invocation, admits
its handle to `q`, and retains the explicit dereference and endpoint in one
`ParameterReferenceAccessorPlanAt<S>` whose `accessEnvironment` is the request's exact environment.
Getter/setter presence is irrelevant. A missing exact key, failed invocation, failed handle
admission, or failed dereference is final for that physical source; the planner does not try a
sibling access key or value conversion.

Only after choosing the endpoint does that primitive construct `PhysicalStorageIdentityProof`. Its
non-recovery equality endpoints are exactly `storage.valueType` and the substituted parameter
`valueType`; it contributes no semantic uses. Numeric, qualification, reference adjustment,
user-defined, initialization, load, and recovery operations are not physical identity. The
resulting `PhysicalParameterBindingProofAt<S>` and access plan retain the exact source, endpoint,
complete `q` proof, identity proof, and `accessEnvironment`; the plan records
`ConsumedWithoutStorageCoercion(PhysicalParameterIdentityPassingRule)` as its sole ranking
authority. Elaboration performs no semantic search or reconstruction.

```text
ParamPassingModeFailureReasonAt<S: WitnessTableState> =
    NotReadable
  | NotWritable
  | NotMutable
  | AtomicityMismatch
  | DirectSourceNotPhysical
  | PhysicalReferenceAccessorMissing(required: StorageAccessMode,
                                      available: CanonicallyOrderedSet<StorageAccessMode>)
  | PhysicalReferenceAccessorFailed(
        failure: ParameterReferenceAccessorFailureAt<S>)
  | PhysicalParameterValueTypeMismatch(expected: TypeId, actual: TypeId)
  | PhysicalParameterConversionForbidden(source: TypeId, target: TypeId)
  | PhysicalAccessNotProvided(actual: StorageAccessMode, required: StorageAccessMode)
  | PhysicalLifetimeTooShort(actual: LifetimeId, required: LifetimeId)
  | PhysicalAddressSpaceNotPermitted(actual: PhysicalStorageAddressSpace,
                                     required: AddressSpaceRequirement)
  | PhysicalSourceNotPermitted(actual: PhysicalStorageSourceProvenance,
                               required: PhysicalStorageSourceRequirement)
  | AliasClaimConflict(conflict: ConflictingCallAliasClaims)
  | TemporaryForbidden
  | WriteBackForbidden

ParamPassingModeFailureAt<S: WitnessTableState> = {
    slot: BoundCallSlot,
    required: ParamPassingMode,
    instantiatedRequirement: Option<PhysicalStorageRequirement>,
    actualType: TypeId,
    actualCategory: ValueCategory,
    reason: ParamPassingModeFailureReasonAt<S>,
    origin: Origin
}

ParamPassingModeFailureReason = ParamPassingModeFailureReasonAt<Published>
ParamPassingModeFailure = ParamPassingModeFailureAt<Published>
```

`OVL-MODE-004`: For either physical mode, `instantiatedRequirement` is
`Some(instantiatePhysicalStorageRequirement(mode, environment.invocationLifetime))`; it is `None`
for every abstract mode. The structured reason records whether direct storage was absent, the exact
accessor key was missing, invocation/dereference failed, storage identity failed, or access,
lifetime, address-space, source provenance, or alias admission failed. A diagnostic renderer never
repeats selection or requirement instantiation. `PhysicalParameterConversionForbidden` is selected
if an `AbstractConversion` is supplied for a physical mode, even if its result type matches.
`ParameterReferenceAccessorMissing` is projected to the top-level
`PhysicalReferenceAccessorMissing`; every other detailed parameter-accessor failure is retained in
`PhysicalReferenceAccessorFailed`, so tests and diagnostics do not scrape a nested message.

`OVL-MODE-005`: A `PhysicalParameterBindingProofAt<S>` validates only when
`storage = physicalParameterStorage(source)`, `physicalStorage.storage = storage`, and
`physicalStorage.requirement = instantiatedRequirement`. The endpoints of
`identity.equality` are exactly `storage.valueType` and `parameterValueType` in either
direction, and the equality does not use recovery. Physical identity contributes no semantic uses.
The enclosing access plan has
`rankingCoercion = Some(ConsumedWithoutStorageCoercion(PhysicalParameterIdentityPassingRule))`,
from which chapter 8 derives comparison rank `zeroRank`. The instantiated requirement is
the result of instantiating the proof's complete, well-formed `PhysicalOperand` `mode` in its exact
`accessEnvironment`; its access equals `mode.access`. An accessor-produced source validates the
entire stored `ParameterReferenceAccessorPlanAt<S>`, requires that plan's `mode`,
`accessEnvironment`, and `instantiatedRequirement` to equal the binding's fields, and validates its
endpoint. For `AccessorProducedPhysicalParameterSource(input, plan)`,
`input.classifier` is exactly
`ValueClassifier(plan.invocation.storage.valueType,
                 Storage(AbstractStorage(plan.invocation.storage)))`, and
`ValidateSemanticOperationSite(input.id, plan.invocation.site) = Success(Unit)`; the invocation
storage is the byte-identical abstract storage from that classifier. Its dereference site is the
fixed child of that invocation site. A direct source's typed input is exactly
`ValueClassifier(storage.valueType, Storage(PhysicalStorage(storage)))`. Thus an equal-classified
sibling node, a sibling slot's site, or the enclosing call node can never be paired with the plan.
The enclosing candidate and call-slot plan store the identical environment. The access plan passes
one physical-storage runtime argument carrying this proof and stores no unused value-conversion plan.

`OVL-MODE-006`: `PlanArgumentAdaptationAt<S>` and `PlanArgumentAccessAt<S>` are the only ordered
parameter-planning pair. For `InMode`, the first constructs one `ConversionRequest` from
`callSlotInput(binding)`, the substituted parameter value type, `Argument`, `Implicit`, and the exact
conversion environment in `context`.
`Applicable(plan, rank)` becomes `AbstractConversion(ApplicableAbstractConversionAt(plan, rank))`;
`Inapplicable(failure)` becomes `AbstractConversionInapplicable(failure)`; and
`Recovered(plan, error)` becomes `AbstractConversionRecovered(plan, error)`. An inapplicable or
recovered conversion can therefore never inhabit `AbstractConversion`.

For `OutMode` or `InOutMode`, it never constructs a conversion request. It requires a physical or
abstract `Storage` classifier and a non-recovery type-equality proof with the substituted parameter
value type, producing `ExactStorageIdentity`; the subsequent access plan records
`ConsumedWithoutStorageCoercion(ExactStorageIdentityPassingRule)` and comparison rank `zeroRank`.
For `ConstRefMode` or `RefMode`, it produces `PhysicalIdentity` only after selecting and proving the
physical endpoint described above. Any other adaptation/mode pairing is invalid.

The second primitive consumes only the byte-identical successful adaptation returned for the same
slot, binding, parameter, and context; a domain mismatch is a closed
`AdaptationDomainMismatch`. It may retain named temporary/write-back machinery for
`InMode`, `OutMode`, or `InOutMode`; a physical mode instead retains the complete physical source
and proof and has exactly one physical-storage `PassArgument` terminal. Neither primitive delegates
parameter semantics to chapter 7's ordinary `PlanStorageAccessAt<S>`; only the dedicated
mode-specific reference-accessor plan may call the shared accessor-validation primitives. Both
queries preserve diagnostics in their outer `CheckResult`; dependency blocking remains a scheduler
state and cannot be collapsed into any semantic failure alternative.

`OVL-MODE-007`: `ConstRefMode(r)` is the canonical checked mode for source `__constref`. Its complete
instantiated requirement has `ReadAccess`; applicability still proves the exact lifetime,
address-space, and source predicate rather than treating read-only access as sufficient. A mutable
or immutable stored variable, explicit dereference, and registered read-only or read/write physical
subscript can be a direct source when their intrinsic physical facts discharge that requirement.
The callee receives the same physical location through a read-only access view. The proof does not
set the underlying storage's mutability to `Immutable`, create a second nonphysical read-view
category, emit begin/end lifetime operations, or permit the location to escape the invocation
requirement.

An rvalue is never applicable. A getter-only, setter-only, or get-plus-set property/subscript is not
physical and remains inapplicable. In particular, a getter-based `StructuredBuffer`-like surface is
not accepted merely because its getter reads from memory. An explicitly checked dereference is
applicable because it already produced a distinct proof-carrying `PhysicalStorage`; a bare reference
handle is not a storage and is inapplicable.

`OVL-MODE-012`: `RefMode(r)` is the canonical checked mode for source `__ref`. It requires the
same physical identity, lifetime, address-space, and source-provenance proof as the instantiated
physical requirement, supplies `ReadWriteAccess`, and establishes exclusive mutable access for the
invocation lifetime. It cannot be formed from a value conversion, temporary, getter/setter pair, or
write-back plan.

`OVL-MODE-008`: An abstract property or subscript may satisfy a physical mode only through
`AccessorProducedPhysicalParameterSource`. The selected accessor key equals `mode.access` exactly:
source `constref` contributes `RefAccessor(ReadAccess)` for `ConstRefMode`, and source `ref`
contributes `RefAccessor(ReadWriteAccess)` for `RefMode`. The plan stores the typed input, selected
`AbstractStorageRefAccessor`, complete invocation and semantic uses, admitted handle, explicit dereference,
and exact physical endpoint. It does not reclassify the original abstract storage. Access inclusion
does not select a sibling key: a `ref` accessor alone does not satisfy `ConstRefMode`, and a
`constref` accessor alone does not satisfy `RefMode`; both may coexist in the map. This implicit
parameter operation is distinct from explicit first-class reference formation but reuses the same
validated invocation/result/dereference primitives.

`OVL-MODE-009`: Both direct and accessor-produced physical sources use the same
`PhysicalParameterBindingProofAt<S>`, full `PhysicalStorageProof`, physical runtime argument, and
conversion-free physical-identity passing rule. Accessor effects and capabilities remain on the source plan and
therefore on the containing candidate; storage identity itself contributes none. A candidate never
ranks better or worse merely because its endpoint was reached through the exact mode-specific
accessor. Any nonidentity conversion, temporary, getter, write-back, access-key substitution, or
omitted access/lifetime/address/source proof rejects the candidate before comparison.

`OVL-MODE-010`: After all receiver and argument access plans are complete,
`CheckCallAliasClaims` constructs their invocation-overlap claims in canonical `BoundCallSlot`
order. `InMode` contributes no live call claim. `ConstRefMode` contributes
`SharedPhysicalRead(ReadAccess)`; `OutMode` and `InOutMode` contribute
`ExclusiveAbstractAccess` with their exact required access; and `RefMode` contributes
`ExclusivePhysicalAccess(ReadWriteAccess)`. Every claim uses
`aliasClassProvenance(plan.aliasClass)` and the exact invocation lifetime. A `UniqueAlias` is accepted
only when its stored proof derives that exact provenance under `TYP-ALS-004`.

The checker visits every unordered pair. `ProvenDisjoint` from `CompareAliasOverlap` always yields
`DisjointAliasPair`. For a `MayOverlap` pair, two `SharedPhysicalRead` claims are universally
compatible. `CommonAliasRegion` is a statically proved overlap and conflicts whenever either claim
is `ExclusiveAbstractAccess` or `ExclusivePhysicalAccess`, including a `ConstRefMode`/`RefMode` pair
on the same physical region. `OneUnknownAlias` and `BothUnknownAliases` do not prove an overlap and
therefore do not by themselves reject the call. Instead the successful comparison records
`UnprovenDisjointUnderExclusiveContract`; the call is accepted under the source-language
exclusivity contract and has undefined behavior if the arguments overlap at runtime. The selected
candidate stores the complete successful
`CompatibleCallAliasClaims`; a conflict rejects it with both slots, claims, overlap reason, and precise
`ParamPassingModeFailure` whose reason is
`AliasClaimConflict(theExactConflictingCallAliasClaims)`. Because that record stores an
`AliasOverlapReason` rather than `AliasOverlapResult`, a `ProvenDisjoint` pair cannot inhabit either
the conflict or its diagnostic payload. Neither plan iteration order nor a diagnostic heuristic can
change the result.

## Generic argument mapping

Explicit generic arguments map to parameter identities before solving:

```text
MapGenericArguments(binder: GenericBinder,
                    arguments: NodeList<CheckedGenericArgument>)
    -> PartialSpecializationFrame | GenericArgumentFailure

PartialSpecializationFrame = {
    binder: GenericBinderId,
    arguments: NodeMap<GenericParameterKey, GenericArg>,
    unbound: CanonicallyOrderedSet<GenericParameterKey>,
    writtenOrigins: NodeMap<GenericParameterKey, Origin>
}

GenericArgumentFailure =
    TooManyGenericArguments(arguments: NonEmpty<AnyASTNodeId<Typed>>)
  | UnknownGenericLabel(argument: AnyASTNodeId<Typed>, label: Name)
  | DuplicateGenericParameter(parameter: GenericParameterKey,
                              arguments: NonEmpty<AnyASTNodeId<Typed>>)
  | GenericKindMismatch(parameter: GenericParameterKey,
                        expected: GenericParameterSort,
                        actual: GenericParameterSort)
  | InvalidGenericPack(parameter: GenericParameterKey,
                       actual: GenericArg,
                       rule: RuleId)
  | ExplicitEvidenceArgumentForbidden(argument: AnyASTNodeId<Typed>)
```

Sorts must match under chapter 5's `argumentMatchesSort`. Type/value pack arguments consume the
source forms allowed by their grammar and cardinality rules. Ordinary arguments and constraint
witnesses are never concatenated into one positional suffix.

`GEN-MAP-001`: Defaults are not applied during mapping. They become low-priority solver work after
inference from call/expected-type constraints.

`GEN-MAP-002`: A named/positional argument cannot bind compiler-produced evidence. Evidence maps
are keyed by `ConstraintKey` and produced only by solving.

`GEN-MAP-003`: Freezing a successful solution combines its arguments, required evidence, and
explicit optional absence into one `SpecializationFrame`. A call, declaration reference, or
partial generic value cannot retain the argument substitution while dropping its evidence.

`GEN-MAP-004`: `MapGenericArguments` first resolves `binder` with `GetGenericBinder` in the
request's semantic environment under
`TYP-BND-004`; every produced `GenericParameterKey` names exactly one parameter in that binder.
Each checked argument's `value` satisfies its stored `sort`, and successful mapping additionally
requires that sort to equal the resolved `GenericParam.sort` after substituting any already mapped
earlier parameters. `GenericKindMismatch.expected` is that specialized parameter sort and `.actual`
is the checked argument sort. A dependent sort that is not yet decidable becomes solver work rather
than a guessed mismatch. An empty pack retains its checked pack sort, so diagnostics and matching
never infer an element domain from nonexistent elements.
The returned frame stores the input binder ID unchanged. The key sets of `arguments` and `unbound`
are disjoint with union equal to that binder's parameter keys; `writtenOrigins` has exactly the
explicitly written argument keys.

## Inference state and worklist

```text
SemanticTraceEvent = {
    rule: RuleId,
    action: QualifiedName,
    inputs: CanonicalArguments,
    origin: Option<Origin>
}

InferenceTrace = {
    events: NodeList<SemanticTraceEvent>
}

InferenceTraceId = ContentId<InferenceTrace>

CandidateTrace = {
    candidate: LookupCandidate,
    inference: Option<InferenceTraceId>,
    events: NodeList<SemanticTraceEvent>
}

CandidateTraceId = ContentId<CandidateTrace>

InferenceState = {
    binder: GenericBinderId,
    variables: NodeMap<GenericParameterKey, InferenceVariableState>,
    evidence: NodeMap<ConstraintKey, ConstraintEvidence>,
    optionalEvidence: NodeMap<ConstraintKey, OptionalEvidence>,
    work: StablePriorityQueue<InferenceWorkItem>,
    trace: InferenceTrace
}

InferenceBound = {
    relation: ExactBound | LowerBound | UpperBound,
    value: GenericArg,
    source: InferenceBindingSource
}

InferenceBindingSource =
    ExplicitGenericArgument(AnyASTNodeId<Typed>)
  | ReceiverConstraint(origin: Origin)
  | CallArgumentConstraint(argument: SourceArgumentId)
  | ExpectedResultConstraint(origin: Origin)
  | DeclaredConstraint(ConstraintKey)
  | DefaultArgumentSource(parameter: GenericParameterKey)

InferenceVariableState =
    Unbound(sort: GenericParameterSort, bounds: NodeList<InferenceBound>)
  | Bound(value: GenericArg, source: InferenceBindingSource)
  | Conflict(values: NonEmpty<GenericArg>, sources: NonEmpty<InferenceBindingSource>)

InferenceWorkItem =
    Unify(pattern, actual, mergeMode, source)
  | SolveConstraint(constraintKey)
  | ApplyDefault(parameterKey)
  | ProvePackShape(constraintKey)
```

Required argument constraints run before optional constraints, which run before defaults. Within a
priority, items use stable source/constraint identity order only for determinism; a unique solution
must be invariant under that order.

Each step returns:

```text
StepResult = Done(newState)
           | Progress(newState, newWork)
           | Blocked(needs: VariableOrQuerySet)
           | Failed(GenericFailure)

VariableOrQuerySet = {
    variables: CanonicallyOrderedSet<GenericParameterKey>,
    queries: CanonicallyOrderedSet<QueryKey>
}

GenericFailure =
    UnboundParameters(parameters: NonEmpty<GenericParameterKey>)
  | GenericKindMismatch(parameter: GenericParameterKey,
                        expected: GenericParameterSort,
                        actual: GenericParameterSort)
  | ConflictingBindings(parameter: GenericParameterKey,
                        values: NonEmpty<GenericArg>,
                        sources: NonEmpty<InferenceBindingSource>)
  | InfiniteStructuralBinding(parameter: GenericParameterKey,
                              proposed: GenericArg)
  | UnsatisfiedConstraint(constraint: ConstraintKey,
                          predicate: Constraint,
                          reason: ConstraintFailureReason)
  | PackShapeConflict(constraints: NonEmpty<ConstraintKey>,
                      observedCounts: NonEmpty<ConstValue>)
  | NoProgress(needs: VariableOrQuerySet)
  | InferenceResourceLimit(processedItems: UInt32,
                           configuredLimit: UInt32)

ConstraintFailureReason =
    UnequalTypes(left: TypeId, right: TypeId)
  | UnequalValues(left: ConstValue, right: ConstValue)
  | NoRepresentationAdjustment(sub: TypeId, sup: TypeId)
  | NoInterfaceRefinement(derived: InterfaceInstanceKey,
                          base: InterfaceInstanceKey)
  | NoConformance(type: TypeId, interface: InterfaceInstanceKey)
  | NotCoercible(failure: ConversionFailure)
  | UnequalPackCounts(left: ConstValue, right: ConstValue)
  | EmptyPack(pack: PackId)
  | DifferentialInfoUnavailable(type: TypeId)
  | IllFormed(type: TypeId, diagnostics: DiagnosticSelection)
```

A full pass with no progress invokes `ExplainBlockedInference`; it does not loop or silently pick a
default that conflicts with pending required evidence.

`GEN-SLV-001`: A `CompleteGenericSolution` requires every generic parameter to be bound, every
required constraint to have typed evidence, every optional constraint to have evidence or a
replayable absence, and every pack shape/count equation to be solved. A
`ResidualGenericSolution` is permitted only when the requested context admits a generic value; every
unbound parameter and every unresolved constraint is transferred through the unique derivation in
`TYP-BND-002c` to its `residual` binder. If that derivation has no residual parameter or constraint,
the result is complete rather than an empty partial solution.

`GEN-SLV-002`: The inference trace records the source of every bound candidate, merge, rejected
alternative, query dependency, and evidence proof. Diagnostic replay uses this same trace; it does
not rerun a declaration-order solver.

`GEN-SLV-003`: `InferenceState.binder` resolves through
`GetGenericBinder(ownerOf(InferenceState.binder), environment)`; `variables` contains exactly that
binder's inferable parameter keys. Each
initial `Unbound.sort` equals its resolved `GenericParam.sort`. Every `InferenceBound.value`,
`Bound.value`, and `Conflict.values` member satisfies that sort after applying the state's bindings
for earlier parameters. State transitions preserve the symbolic sort rather than recomputing a
weaker `Kind`. A proposed value of another sort is a typed mismatch
`GenericFailure::GenericKindMismatch` and never enters the bound set. Solver unit tests cover all
sixteen expected/actual sort
constructor pairs, dependent value sorts, both pack sorts, and empty packs.

## Unification

```text
Unify(pattern, actual, mode)
```

`mode` is `Exact`, `Join`, or a named variance position. Core rules are:

```text
var α unbound    kind(α) = kind(a)    occurs(α,a) = false
-------------------------------------------------------- GEN-UNI-001
unify(α,a) binds α := a

α bound to b    b ≡ a
--------------------- GEN-UNI-002
unify(α,a) succeeds

head(p) = head(a)    unify corresponding keyed operands
------------------------------------------------------- GEN-UNI-003
unify(p,a) succeeds
```

`Exact` rejects unequal bindings. `Join` invokes a declared least-common-expression-type operation
and records why the merged type satisfies every contributing occurrence. Variance is explicit for
function parameters/results and declared generic constructors; absent variance defaults to
invariant.

`GEN-UNI-004`: Occurs checking traverses substitutions, function receivers, constraints, packs, and
symbolic constants. A structural infinite type/value is rejected; a nominal self-reference through
`DeclId` does not bind the variable to a structural term containing itself.

`GEN-UNI-005`: Conceptually unordered fields/maps unify by identity key. Constraint or witness list
position is never used as identity.

## Constraint solving

The solver handles the constraint constructors in chapter 5:

- equality uses canonical equality proofs;
- representation adjustment and interface refinement request their distinct proof relations;
- conformance requests `FindConformance`;
- coercibility requests `PlanTypeCoercibility` and retains its environment-keyed witness/rank;
- pack count/nonempty uses symbolic integer/shape reasoning; and
- differentiability information requests the standard environment's declared evidence query.

Required or optional constraints may remain residual only when their unsolved predicates are
well-formed under the residual parameters and the owning generic construct explicitly supports
partial application. A required constraint with no residual dependency must be proved before either
solution constructor succeeds. Constraints cannot be inferred from a witness argument's physical
position.

`GEN-CON-001`: Solver query dependencies that are pending produce `Blocked`. A semantic negative
result produces `Failed` with the dependency's structured reason. Error recovery evidence cannot
make a successful public generic solution.

## Packs

Pack parameters bind immutable pack values. Pack patterns are checked under captured cardinality
variables, and `each` expansion introduces an index scoped only to the pattern.

```text
count(P) = n    count(Q) = n
-------------------------------- GEN-PACK-001
zipExpand(pattern, P, Q) has cardinality n
```

Unknown but equated symbolic counts are valid with `PackCountWitness`; unequal concrete counts fail.
`nonempty(P)` requires chapter 5's `NonEmptyPackWitness`: a
`ConcreteNonEmptyPackWitness` for a known pack, a `DeclaredNonEmptyPackWitness` tied to the exact
canonical generic constraint, or a derived positive-count proof. First/last operations consume the
same pack-specific evidence and do not rely on a runtime bounds guard.

## Candidate evaluation

Candidate ranking stores a canonical projection of every fact used by pairwise comparison:

```text
SourceAdaptationRank =
    AbstractConversionCost(ConversionCost)
  | ConversionFreeAccessRank(rule: RuleId)

comparisonRank(AbstractConversionCost(r)) = r
comparisonRank(ConversionFreeAccessRank(_)) = zeroRank

sourceAdaptationRank(plan) =
    AbstractConversionCost(r)
        when plan.rankingCoercion = Some(AppliedStorageCoercion(_, r, _))
    ConversionFreeAccessRank(rule)
        when plan.rankingCoercion = Some(ConsumedWithoutStorageCoercion(rule))

CandidateConversionRank = {
    maximum: ConversionCost,
    bySource: NodeMap<SourceCallRole, SourceAdaptationRank>
}

candidateConversionRank(candidate) = {
    bySource: comparedSourceAdaptations(candidate),
    maximum: max({ comparisonRank(r) |
                   (_, r) in comparedSourceAdaptations(candidate) },
                 default = zeroRank)
}

PackPreference = {
    parameter: SourceParameterKey,
    consumed: NodeList<SourceArgumentId>,
    greedy: Bool
}

CandidateRank = {
    genericity: NonGenericCandidate | GenericCandidate,
    defaultsUsed: CanonicallyOrderedSet<ParameterKey>,
    packs: NodeMap<SourceParameterKey, PackPreference>,
    memberOrigin: OrdinaryMember | DirectOrOverrideMember | InheritedDefaultMember,
    lookupPath: LookupPath
}
```

Trace events are in deterministic semantic-step order; each event records structured canonical
inputs rather than rendered prose. IDs are collision-safe content IDs. A retry that reaches the
same facts produces byte-identical traces, while diagnostics select trace events without rerunning
the solver.

`CandidateRank` is not a scalar score. It is an immutable, serializable cache of the non-conversion
facts whose pairwise proof is defined below. `CandidateConversionRank.maximum` is the one normative
aggregate conversion rank. Its `bySource` map is retained to validate that maximum and explain which
source adaptations produced it; it is not a second comparison order. Conversion comparison projects
only candidate `callSlots` carrying `ComparedCallSource`, keyed by their stored `SourceCallRole`; defaulted slots
are excluded and are compared by the later default-parameter relation. Thus candidates with
different parameter identities still compare corresponding source inputs. `ArgumentMap` owns
source-to-parameter binding and each
`ApplicableCallSlotPlan.access` owns the adaptation that elaboration will execute: an abstract
conversion or a proof-carrying physical identity. `sourceAdaptationRank` is defined exactly when
that candidate plan has `Some(rankingCoercion)`; `None` makes a call-slot plan invalid. The
conversion-free rule remains in `ConversionFreeAccessRank` so validators can prove why no converted
input exists even though its comparison projection is `zeroRank`.
`PhysicalParameterIdentityPassingRule` is the only conversion-free rule admitted for a
physical-domain parameter plan; `ExactStorageIdentityPassingRule` is admitted only for an abstract
`OutMode`/`InOutMode` plan. No candidate stores or accepts an independently supplied
`SourceAdaptationRank`.
`rankOf(candidate)` constructs `defaultsUsed` only as
`defaultedParameters(candidate.argumentMap)` and constructs the other fields from the specialized
signature, argument map, bound-use lookup path, and declaration origin. The candidate does not store
this projection; comparison proofs retain it only so a validator can compare it with `rankOf`.

For each lookup candidate:

1. obtain its checked declaration header, `CandidateDeclUseAt<S>`/receiver path, and pre-inference
   selection contract;
2. map checked explicit generic arguments into partial specialization frames;
3. map receiver and source arguments to identities;
4. generate inference constraints from receiver, arguments, and expected result;
5. solve generic variables and required evidence;
6. require a complete solution and invoke chapter 5's
   `FreezeDeclUse(candidateUse, genericSolution)`, producing the one `BoundDeclUseAt<S>` that every
   applicable/selected call retains;
7. project the checked `CallableSignature` through that bound use's complete specialization spine;
8. intern one `ConversionEnvironment` and one `AccessEnvironment` for this candidate, then intern a
   closed `ArgumentPlanningContext` per receiver/argument slot from those IDs, the exact signature,
   call input, argument map, expression context, and authenticated slot site. Pass that context first
   to `PlanArgumentAdaptation` and then to `PlanArgumentAccess`; only their nested successful
   alternatives construct an `ApplicableCallSlotPlan`. Every slot stores the shared access-environment
   ID and its complete `StorageAccessPlan` determines its `SourceAdaptationRank`;
9. validate `selectionEffects` and visibility; construct the direct call's exact keyed use for
   `inferredCapabilities`, resolve every source in the optional callable `concreteAvailability` set,
   and merge it with the ordinary-use sidecar and concrete applicability selection of every
   `ExtensionFacetUseAt<S>` on the bound use, under the request's exact boolean world assumption; and
10. construct an immutable `OverloadCandidateResult`.

The candidate stores that exact `AccessEnvironmentId`; neither it nor a slot repeats an ambient
invocation lifetime. The candidate-evaluation and `ResolveCall` query keys contain the complete
`ExpressionCheckContext.contractSelection.assumption`. A concrete-availability check uses that
boolean region directly; it does not cache only a positive projection. The assumption remains in
the key when no callable has concrete availability because argument conversion and access plans may
contain their own concrete registered-rule checks.

```text
CandidateFailureStage =
    FailedSignature
  | FailedExplicitGenerics
  | FailedArgumentMap
  | FailedInference
  | FailedConversion
  | FailedParamPassingMode
  | FailedEffects
  | FailedConcreteAvailability
  | FailedVisibility

CandidateFailure =
    SignatureFailure(reason: NotCallable | InvalidCallableSignature |
                             SignatureQueryFailed,
                     diagnostics: DiagnosticSelection)
  | ExplicitGenericFailure(GenericArgumentFailure)
  | ArgumentMappingFailure(ArgumentMapFailure)
  | GenericInferenceFailure(GenericFailure)
  | ArgumentConversionFailure(slot: BoundCallSlot,
                              failure: ConversionFailure)
  | ArgumentPassingFailure(ParamPassingModeFailure)
  | EffectSelectionFailure(required: EffectSet,
                           allowance: EffectAllowance,
                           excess: EffectSet)
  | ConcreteAvailabilitySelectionFailure(
        sources: NonEmpty<ResolvedConcreteAvailability>,
        combinedRequirement: CapabilityRequirement,
        assumption: BooleanCapabilityPredicate,
        failure: CapabilityFailure)
  | VisibilitySelectionFailure(VisibilityDecision)
```

The ordered list above records diagnostic progress, not semantic preference.

`OVL-CAN-001`: Candidate evaluation performs every independent cheap check useful for diagnostics
but never reports diagnostics directly. It returns a rejection trace with origins and failures.

`OVL-CAN-002`: `PreInferenceCallableContract.inferredCapabilities` and
`PreInferenceCallableContract.concreteAvailability` have disjoint roles. Selecting any applicable
call constructs exactly one keyed `CapabilityUse` representing `inferredCapabilities` and the
callee's stable identity. A local use becomes a capability-inference dependency without requesting
the callee's inferred/effective contract during call resolution; an imported use is a leaf carrying
its published ordinary requirement. Neither is an applicability premise. `InferCapabilities` later
follows local call edges under its least-fixpoint policy, and declared/effective contract validation
discharges the resulting obligations after stabilization. `selectionEffects` remains the
pre-inference effect check and `InferEffects` retains its separate call-edge policy.
The use is an entry of `candidate.capabilitySelection.inferredCapabilityUses`. That map also contains
every `candidate.use.extensionUses[*].inferredCapabilityUses` entry exactly once. Each extension's
`resolve(applicability).concreteAvailability` contributes its exact source set and proof to the
candidate selection. Call-slot conversion/access selections remain separately stored in their
`PlanSemanticUses`; committing the typed call merges them with the candidate selection under
`CAP-SEL-004`, so their uses and concrete sources remain independently addressable and are not
attributed to the main callee.

`OVL-CAN-003`: Let `A` be the request's exact
`ExpressionCheckContext.contractSelection.assumption`. For an applicable candidate `c`,

Let `callableSources(c)` be empty when
`c.selectionContract.concreteAvailability = None`, and otherwise be the exact canonical `sources`
of its `ConcreteAvailabilitySet`. Let `extensionSources(c)` be the canonical union of
`sources(resolve(u.applicability).concreteAvailability)` for every
`u` in `c.use.extensionUses`. Then:

```text
sources(NoConcreteAvailability) = []
sources(ProvenConcreteAvailability(s, _, _)) = s

c.capabilitySelection.region = A
sources(c.capabilitySelection.concreteAvailability) =
    canonicalUnion(callableSources(c), extensionSources(c))

sources = []
    iff c.capabilitySelection.concreteAvailability = NoConcreteAvailability

sources != []
    iff c.capabilitySelection.concreteAvailability =
        ProvenConcreteAvailability(sources,
                                   combineConcreteAvailability(sources),
                                   p)
        and p.region = A
        and p.requirement = combineConcreteAvailability(sources)
        and validate(p)
```

Failure to resolve any source or construct the combined proof produces
`ConcreteAvailabilitySelectionFailure(sources, combinedRequirement, A, failure)`. It is the only
callable-capability failure
that can reject a candidate at selection time. In particular, failure of `A` to imply
`inferredCapabilities` is not a candidate failure, and a concrete-availability proof is not inserted
again as the ordinary call's `CapabilityUse` unless the operation independently declares the same
ordinary requirement.

`OVL-CAN-004`: An applicable candidate stores the exact
`CallableResultAuthorityId` resolved from its `BoundDeclUse` (or registered builtin identity) and
canonical signature. Resolution follows `TYP-FUN-011` through specialization and the exact
witness/dynamic introducer when applicable. Candidate comparison ignores the authority because it
is not an overload-ranking dimension, but committing the winner copies it unchanged. A candidate
cannot be made applicable with an authority supplied by the call site, and equal signatures or
result types do not permit reusing another declaration's authority.

`OVL-CAN-005`: `FailedConversion` and `ArgumentConversionFailure` are reachable only while
constructing `AbstractConversion` for `InMode`. Failure to prove exact storage identity for
`OutMode`/`InOutMode`, or to select/prove a physical
endpoint or physical identity is `FailedParamPassingMode` with the structured `ParamPassingModeFailureReason`;
ordinary coercion search is never run merely to populate a physical-mode rejection trace.

`OVL-CAN-006`: No `ApplicableOverloadCandidate`, `Selected` result, or typed call contains a
`DeclRefCandidate`. Candidate evaluation calls `FreezeDeclUse(candidateUse, genericSolution)` after
inference and before signature substitution or argument planning. It accepts only
`CompleteGenericSolution` and stores the returned `BoundDeclUseAt<S>` unchanged. A
`ResidualGenericSolution` constructs a `PartiallyAppliedGenericValue` in a generic-value context and
is a `FailedInference` call candidate; it cannot become an incomplete `DeclRef` or be repaired while
committing the winner.

## Semantic comparison of applicable candidates

Candidate `noWorse` is a preorder; semantically equivalent candidates form its equivalence classes.
The induced order on those classes is partial, and `strictlyBetter` is its strict relation. First
compare the maximum receiver/source-argument adaptation cost:

```text
A convRank B = compare(candidateConversionRank(A).maximum,
                       candidateConversionRank(B).maximum)
A convBetter B iff A convRank B = Less
```

Defaults and absent receiver slots are represented explicitly so diagnostic/proof vectors correspond
by source argument/receiver role, not parameter array position. They do not alter which supplied
source adaptations enter the maximum.

`OVL-RANK-001`: The conversion rank of a candidate is exactly the maximum `comparisonRank` over its
receiver and supplied source-argument adaptations, with `zeroRank` for an empty set. Costs are never
summed. The per-source vector is proof and diagnostic data only; pointwise dominance is not a
semantic candidate-ranking relation.

If one maximum is smaller, that candidate wins conversion comparison. If the maxima tie, apply these
specificity relations in order, only while the preceding relation ties:

1. a candidate whose parameter/receiver types are a strict specialization of the other's after
   substitution;
2. a generic candidate whose constraints strictly imply the other's constraints;
3. a non-generic declaration over an otherwise equivalent generic instantiation;
4. fewer defaulted parameters and non-greedy pack bindings;
5. a directly declared/overriding member over an inherited default implementation;
6. a semantically closer lookup facet/scope under chapter 6's path precedence; and
7. a language-version-specific preference explicitly registered by rule ID.

`OVL-RANK-002`: Stable declaration/source order is never the final semantic tie-breaker. If maximal
candidates are not one canonical declaration, resolution is ambiguous.

`OVL-RANK-003`: Capability-specific definitions of one canonical declaration are not ordinary
overloads. The frontend preserves the canonical symbol plus capability alternatives for target-time
selection under chapter 10. Filtering those alternatives uses only their concrete availability;
their ordinary/transitive `inferredCapabilities` contribute the selected call's capability use and
never act as a specificity rank or an implicit availability predicate.

This accepted ranking intentionally replaces the current scalar-cost sum and heuristic tail. The
maximum conversion rank followed by the numbered specificity relations is the semantic order;
diagnostic ranking remains separate.

Every comparison is retained as a proof object:

```text
CandidateComparisonOutcome = LeftBetter | RightBetter |
                             SemanticallyEquivalent | Incomparable

CandidateConversionComparison = {
    leftMaximum: ConversionCost,
    rightMaximum: ConversionCost,
    result: Less | Equal | Greater,
    bySource: NodeMap<SourceCallRole, Less | Equal | Greater>
}

GenericConstraintImplicationProof = {
    stronger: CanonicalConstraintSet,
    weaker: CanonicalConstraintSet,
    substitution: CanonicalSubstitution,
    evidenceByWeakerSlot:
        NodeMap<CanonicalConstraintSlot, ConstraintEvidence>
}

SpecificityComparisonProof =
    FunctionSpecialization(moreSpecific: CallableSignatureId,
                           moreGeneral: CallableSignatureId,
                           substitution: CanonicalSubstitution,
                           strictSlots: NonEmpty<BoundCallSlot>)
  | ConstraintStrength(GenericConstraintImplicationProof)
  | NonGenericPreference(preferred: DeclRef,
                         generic: DeclRef)
  | DefaultPackPreference(preferredDefaults: CanonicallyOrderedSet<ParameterKey>,
                          otherDefaults: CanonicallyOrderedSet<ParameterKey>,
                          preferredPacks: NodeMap<SourceParameterKey, PackPreference>,
                          otherPacks: NodeMap<SourceParameterKey, PackPreference>)
  | MemberOriginPreference(preferred: DirectOrOverrideMember,
                           other: InheritedDefaultMember)
  | LookupPathPreference(preferred: LookupPath,
                         other: LookupPath,
                         rule: RuleId)
  | RegisteredLanguagePreference(rule: RuleId,
                                 inputs: CanonicalArguments,
                                 preferred: DeclRef)

CandidateComparisonProof = {
    left: DeclRef,
    right: DeclRef,
    leftRank: CandidateRank,
    rightRank: CandidateRank,
    conversions: CandidateConversionComparison,
    specificity: NodeList<SpecificityComparisonProof>,
    outcome: CandidateComparisonOutcome
}
```

`OVL-RANK-004`: A comparison validator recomputes each endpoint projection and applies specificity
rules only after all earlier rules tie. `SemanticallyEquivalent` requires mutual `noWorse` plus
canonical selected-declaration equivalence; distinct non-equivalent maxima remain ambiguous.
`strictlyBetter` is irreflexive and transitive. Antisymmetry is tested only on the quotient by
`SemanticallyEquivalent`, not on raw candidate identities.

## Selecting a result

```text
applicable = { a | Applicable(a) occurs in candidateResults }
maximal = { c ∈ applicable | no d ∈ applicable strictlyBetter(d,c) }
```

- one canonical maximal candidate → success;
- no applicable candidates → failure diagnostics from the failed-candidate algorithm;
- multiple non-equivalent maximal candidates → ambiguity with each candidate's comparison trace;
- only recovery candidates → recovered call retaining the root errors.

The winning `OverloadResult` contains the fully substituted `CallableSignature`, a specialized
`BoundDeclUse` whose `DeclRef` solely owns all frozen specialization frames, the inference
trace, argument map, unified call-slot plans, direct effect use, keyed capability use, optional
concrete-availability proof, and result type. Typed call construction is a pure projection of this
record.

## Failed-candidate diagnostics

Failure ranking is explicitly not overload semantics:

```text
FailureProgress = Signature < ExplicitGenerics < ArgumentMap < Inference <
                  Conversion < ParamPassingMode < Effects < ConcreteAvailability < DeclVisibility
```

Choose failures with greatest progress, then smallest structured edit distance (arity difference,
number of failed arguments/constraints, and lookup proximity) for concise primary diagnostics.
Other relevant candidates are notes. A deterministic cap limits note volume.

```text
FailureEditDistance = {
    arityDifference: UInt32,
    failedArguments: UInt32,
    failedConstraints: UInt32,
    lookupDistance: UInt32
}

RankedCandidateFailure = {
    candidate: LookupCandidate,
    stage: CandidateFailureStage,
    failure: CandidateFailure,
    distance: FailureEditDistance,
    trace: CandidateTraceId
}

OverloadFailureReport = {
    primary: NonEmpty<RankedCandidateFailure>,
    notes: NodeList<RankedCandidateFailure>,
    omittedNoteCount: UInt32,
    noteLimit: UInt32
}
```

All `primary` entries have maximal `FailureProgress` and minimal lexicographic
`FailureEditDistance` among candidates at that progress. `notes` use canonical diagnostic order and
`omittedNoteCount` accounts for every candidate removed by `noteLimit`.

`OVL-DIAG-001`: Changing failure ranking may change diagnostics but cannot change the selected
candidate for a successful call.

`OVL-DIAG-002`: The diagnostic renderer consumes the stored rejection/inference/conversion traces.
It never reruns generic inference or coercion under a different algorithm.

## Partial generic application

A generic function or generic type may be partially applied whenever the grammar/context admits a
generic value and the remaining parameters/constraints can be represented as a new binder. A
partially applied generic type remains a generic value until its residual binder is discharged; it
does not masquerade as a complete `TypeId`:

```text
PartiallyAppliedGenericValueId = ContentId<PartiallyAppliedGenericValue>

PartiallyAppliedGenericValue = {
    target: UnappliedDeclRef,
    residual: CanonicalPartialSpecializationFrame,
    classification: PartiallyAppliedGenericValueClassification
}

PartiallyAppliedGenericValueClassification =
    PartiallyAppliedCallableGenericValue(signature: CallableSignatureId,
                                         resultAuthority: CallableResultAuthorityId,
                                         residualEffects: EffectRequirement,
                                         residualCapabilities: CapabilityRequirement)
  | PartiallyAppliedTypeConstructorGenericValue(resultKind: Kind)
```

`GEN-PART-000`: Partial application is supported uniformly for generic callable and non-callable
type declarations. Further generic application consumes the prior `residual`, adds arguments and
evidence by residual parameter identity, and either produces another partial value or freezes a
complete specialization frame. The implementation cannot restrict this operation to functions or
require all generic type arguments at the first application site.

`GEN-PART-001`: Ordinary call resolution requires a complete solution. A residual generic cannot
reach elaborated call or IR accidentally; it must be an explicit `PartiallyAppliedGenericValue`.

`GEN-PART-002`: `target` is an `UnappliedDeclRef`, never a complete `DeclRef` with a missing direct
frame. Its `completed` prefix contains only fully applied owner frames, and its sole pending direct
binder equals `residual.binder.sourceBinder`; that pending frame's `suppliedArguments` map is empty.
Creating a partial value transfers every supplied or deduced direct-binder argument out of the
lookup candidate and into `residual.boundArguments`. `residual.binder` is a `CanonicalBinderRef`, so the
binder's only nominal identity is `GenericBinderOf(target.declaration)`; lexical/type/callable/member
role tags and a second owner field are forbidden. `residual` is the single authority for supplied
arguments/evidence and the alpha-normalized residual binder; all parameter/constraint maps and the
derived residual signature satisfy `TYP-BND-002c`.

`GEN-PART-002a`: A `PartiallyAppliedGenericValue` is constructed only from
`ResidualGenericSolution(completed, residual, ...)`. Its target's `completed` prefix is byte-identical
to that solution prefix and its stored `residual` is byte-identical to the solution residual; the
empty pending source map preserves only declaration/binder identity. Applying more generic
arguments solves the residual binder, maps its result back through the source-ordinal/source-slot
maps, and derives either a new partial frame or one total direct `SpecializationFrame`. It never
merges two independently serialized residual binders.

`GEN-PART-003`: `classification` is total and exclusive. A generic function uses
`PartiallyAppliedCallableGenericValue`, which stores its residual effect/capability contract; it does
not embed a `CallableValue`, whose direct dispatch would require a complete `ResolvedDeclRef`. A
generic type uses `PartiallyAppliedTypeConstructorGenericValue` and remains a type constructor of the
stated result kind, not a `TypeId`. No `Option<CallableValue>` or declaration-kind rediscovery
distinguishes the cases.
No residual constraint, evidence, or capability scheme is reconstructed from the declaration at
elaboration time.

## Compatibility evidence and deliberate changes

The current implementation provides valuable behavior but not the normative decomposition:

- `slang-check-constraint.cpp` already uses a `Done/Progress/Blocked/Failed` worklist idea;
- `slang-check-overload.cpp` tracks staged applicability and useful failed candidates;
- `slang-check-conversion.cpp` bottlenecks many conversions through one dispatcher; and
- `core.meta.slang` declarations carry base conversion costs.

The replacement deliberately changes positional witness arguments, mutable trial/commit checking,
conversion recursion sentinels, summed scalar costs, and diagnostic-time re-inference. Differential
tests expose the accepted observable ranking changes rather than concealing them. Conversion paths
and call candidates use maxima over the existing cost-category order; no conversion-cost number is
an ABI commitment.

One current helper, `canConvertImplicitly(Type*, QualType)` in
`source/slang/slang-check-conversion.cpp`, appears to invert a scalar predicate; its behavior must be
validated by a focused regression test before any compatibility disposition is assigned.
