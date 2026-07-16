# Initialization and construction

Initialization is a transformation from source inputs and an uninitialized destination goal to a
proof-carrying `InitializationPlan`. It is not an initializer-list special case, an ordinary call
whose callee happens to classify as a type, or a conversion fallback. Calls and conversions supply
reusable candidate machinery, but this chapter is the authority for which initialization
strategies exist and how a selected strategy initializes an object.

## Source forms

Binding classifies the following forms without selecting a strategy:

```text
InitializationForm =
    OmittedDecl
  | CopyFromExpression
  | DirectArguments
  | ExplicitSingle
  | InitializerListElements
  | RequestedDefault
  | AllocatingArguments

InitializerExpr =
    InvokeExpr(argumentCount: UInt32)       // T(e0, ... en), including T()
  | ExplicitCastExpr                       // (T)e
  | InitializerListExpr                    // { ... }, only under a target
  | NewExpr(argumentCount: UInt32)         // new T(...)

InitializationSyntax =
    DeclEqualsExpr                          // T x = e
  | DeclEqualsInitializerList               // T x = { ... }
  | InitializerExpr
  | NoWrittenInitializer

InitializationDesignator =
    MemberDesignator(name: Name)
  | ElementDesignator(index: ConstValue)
```

`INI-SYN-001`: an `InvokeExpr` for `T(e)` with exactly one argument and an `ExplicitCastExpr` for
`(T)e` both bind to `ExplicitSingle` and invoke
the same initialization-resolution relation. Their CST nodes, bound input identities, and `Origin`
values remain distinct, so separately written occurrences need not have the same memoization key.
After erasing those source identities, both forms enumerate and compare the same semantic
strategies; neither form uses a second checker path or “try cast, then constructor” fallback.

`INI-SYN-002`: an `InvokeExpr` for `T(e0, ... en)` with arity other than one binds to
`DirectArguments`. An `InvokeExpr` for `T()` has arity zero and binds to `RequestedDefault`; it is
not the same form as omitting an initializer.

`INI-SYN-003`: A braced list is an immutable syntax input, not an independently typed expression.
It is checked separately for each proposed target and initialization strategy. It cannot first
acquire a magic initializer-list type and then participate in unrestricted conversion search.

`INI-SYN-004`: Cast-versus-parenthesized-expression ambiguity is retained in the CST. Modern syntax
resolves it through grammar/name classification rules; a compatibility dialect may use a declared
ambiguity query. A successful cast alternative always produces `ExplicitSingle`.

`INI-SYN-005`: A designator preserves only the written member name or constant element index.
Resolving it to an `AggregateSlotKey` is target- and strategy-dependent and therefore occurs while
building an aggregate candidate. A designator never stores a declaration discovered under one
candidate and reuses it for another.

## Requests, goals, and results

```text
InitializationInputId = NodeId<Bound>

InitializationInputKey =
    ExpressionInput(expression: NodeId<Bound>)
  | InitializerListInput(elements: NodeList<InitializationInputId>,
                designator: Option<InitializationDesignator>)

InitializationInput = {
    id: InitializationInputId,
    key: InitializationInputKey,
    origin: Origin
}

InitializationTargetEntryState = Uninitialized | PartiallyInitialized

InitializationDestinationStorage =
    SuppliedPhysicalInitializationStorage(storage: PhysicalStorageRef,
                                          proof: PhysicalStorageProof)
  | PlanOwnedInitializationStorage(storage: PlanInitializationStorageId)
  | AllocatedObjectInitializationStorage(object: AllocationObjectId)
  | ProjectedInitializationStorage(
        projection: InitializationSubobjectStorageProjection)

InitializationDestination = {
    storage: InitializationDestinationStorage,
    entryState: InitializationTargetEntryState
}

InitializationGoal =
    ProduceValue(type: TypeId)
  | InitializeStorage(destination: InitializationDestination, type: TypeId)

InitializationSite =
    LocalDecl | GlobalDecl | FieldDecl |
    ParameterDefault | ReturnConstruction | ExplicitExpression |
    Allocation | SynthesizedStorage

InitializationEnvironment = {
    semantic: SemanticEnvironmentId,
    conversion: ConversionEnvironmentId,
    access: VisibilityContext,
    effectAllowance: EffectAllowance,
    contractSelection: ContractSelectionContext
}

InitializationEnvironmentId = ContentId<InitializationEnvironment>

InitializationRequestKey = {
    target: TypeId,
    goal: InitializationGoal,
    form: InitializationForm,
    inputs: NodeList<InitializationInputId>,
    site: InitializationSite,
    environment: InitializationEnvironmentId
}

InitializationRequestId = ContentId<InitializationRequestKey>

InitializationRequest = {
    id: InitializationRequestId,
    key: InitializationRequestKey,
    origin: Origin
}
```

`INI-REQ-001`: `InitializeStorage` accepts only fresh or explicitly delegating physical storage from
the closed `InitializationDestinationStorage` sum. A supplied alternative contains its
`PhysicalStorageRef` and proof; plan-owned, allocated-object, and projected alternatives resolve the
immutable physical endpoint introduced by the enclosing plan. A property, declared subscript,
abstract swizzle, setter-backed storage, or ephemeral write-back destination has no constructor in
this sum. Assignment to such storage is an access plan applied after a value has been constructed,
not storage initialization.

`INI-REQ-002`: The request duplicates no ambient facts. Its target, source nodes, environment,
language-rule set (through `SemanticEnvironment`), and source form are all part of
`InitializationRequestKey` and are validated against the originating typed/bound nodes.
`request.id = ContentId(request.key)`. `origin` is a diagnostic/provenance edge and is deliberately
excluded from semantic query identity.

`INI-REQ-003`: Every request input ID resolves to one `InitializationInput` with the same ID in the
request's bound snapshot. A `InitializerListInput` stores child IDs, not embedded child records; those IDs
form a finite ordered tree and each child's origin remains on its resolved input. Neither an input's
`origin` nor the request's `origin` enters `InitializationRequestId`, while the bound input IDs keep
separately written occurrences distinct for diagnostics and evaluate-once semantics.

`INI-REQ-004`: For every non-allocation form, `ProduceValue(t)` or `InitializeStorage(_, t)` has
`request.key.target = t`. For `AllocatingArguments`, `request.key.target` is the allocated object
type while `ProduceValue(h)` is the owning handle result type. The selected allocation descriptor
and plan prove that object/handle relation; `AllocatingArguments` does not admit an
`InitializeStorage` goal. Thus `new T(...)` never overloads one `TypeId` field to mean both the
initialized object and the returned handle.

```text
ApplicableInitializationCandidateKey<S: WitnessTableState> = {
    strategy: InitializationStrategy,
    plan: InitializationPlanIdAt<S>,
    rank: InitializationRank
}

ApplicableInitializationCandidateId<S: WitnessTableState> =
    ContentId<ApplicableInitializationCandidateKey<S>>

ApplicableInitializationCandidate<S: WitnessTableState> = {
    id: ApplicableInitializationCandidateId<S>,
    key: ApplicableInitializationCandidateKey<S>,
    trace: InitializationTraceId
}

InitializationCandidateResultAt<S: WitnessTableState> =
    Applicable(candidate: ApplicableInitializationCandidate<S>)
  | RejectedBeforeStrategy(failure: InitializationFailure,
                           trace: InitializationTraceId)
  | Rejected(strategy: InitializationStrategy,
             failure: InitializationFailure,
             trace: InitializationTraceId)
  | Recovered(strategy: InitializationStrategy,
              plan: InitializationPlanIdAt<S>,
              trace: InitializationTraceId,
              errors: NonEmpty<ErrorId>)

InitializationResultAt<S: WitnessTableState> =
    Selected(winner: ApplicableInitializationCandidate<S>,
             comparisons: NodeList<InitializationComparisonProofAt<S>>,
             considered: NonEmpty<InitializationCandidateResultAt<S>>)
  | NoApplicable(considered: NonEmpty<InitializationCandidateResultAt<S>>)
  | Ambiguous(maximal: NonEmpty<ApplicableInitializationCandidate<S>>,
              incomparability: NodeList<InitializationComparisonProofAt<S>>)
  | RecoveredInitialization(plan: InitializationPlanIdAt<S>,
                            errors: NonEmpty<ErrorId>)

InitializationCandidateResult = InitializationCandidateResultAt<Published>
InitializationResult = InitializationResultAt<Published>

BuildInitializationModel(type: TypeId,
                         environment: SemanticEnvironmentId)
    -> QueryStep<InitializationModel>

InitializationResolutionContextAt<Published> = PublishedInitializationResolution
InitializationResolutionContextAt<Construction> =
    ConstructionInitializationResolution(scope: ConformanceConstructionScope)

ResolveInitializationAt<S: WitnessTableState>(
    request: InitializationRequest,
    context: InitializationResolutionContextAt<S>)
    -> QueryStep<InitializationResultAt<S>>

ResolveInitialization(request) =
    ResolveInitializationAt<Published>(request, PublishedInitializationResolution)
```

No diagnostics renderer reruns resolution. Tests compare candidate results, failures, and proofs as
ordinary immutable values.

`INI-RES-001`: An applicable candidate satisfies
`candidate.id = ContentId(candidate.key)`, and its resolved plan's `key.request` equals the request
named by its trace. `Selected.winner` is an `Applicable` member of `considered`; every other
applicable member is no better under a stored comparison proof. `Ambiguous.maximal` contains at
least two applicable candidates and exactly the incomparable maxima. `NoApplicable` contains no
`Applicable` alternative. Rejected and recovered candidates can inform diagnostics but can never
be selected or appear in the maximal set. `RejectedBeforeStrategy` is used when model construction,
the source form, or the site rejects the request before any strategy exists; its trace has no
strategy. This keeps `NoApplicable.considered` nonempty even for a `NonInitializable` model or an
empty form/site intersection.

`INI-RES-002`: `ResolveInitializationAt<S>` is the sole query that turns an initialization request
into candidates and a result. Once its dependencies are available, it completes with exactly one
`InitializationResultAt<S>` alternative. `NoApplicable` and `Ambiguous` are ordinary negative
semantic results, not scheduler states; `Blocked` occurs only in the enclosing `QueryStep`.
Candidate enumeration consumes
`BuildInitializationModel(request.key.target, resolve(request.key.environment).semantic)`; it never
derives the object target from an allocation handle result type.
`RecoveredInitialization` contains a structurally valid plan whose operation and output are
`InitializationRecovery(e)` and `RecoveredInitializationOutput(e)` for a root error in its error set;
it cannot be treated as `Selected`. The query key contains `request.id`, the witness-use stage, and
its complete resolution context; a construction context names its owning synthesis/conformance
scope. No expression checker, diagnostic renderer, or lowering pass may enumerate a second candidate
set.

## Initialization models

Every initializable type has one checked model. The model is derived once from the type definition,
the semantic environment's language-rule set, and registered standard rules; failed constructor
lookup never changes it.

```text
InitializationStrategy =
    ExpressionConversionStrategy
  | DeclaredConstructorStrategy
  | SynthesizedConstructorStrategy
  | AggregateStrategy
  | StandardInitializationStrategy(rule: StandardInitializationRuleId)
  | AllocationStrategy

StandardInitializationRuleId = StandardEnvironmentRuleId
InitializationStrategyPriorityId = RuleId

InitializationStrategyPolicy = {
    priority: InitializationStrategyPriorityId
}

CallableGroupKey = {
    target: TypeId,
    members: CanonicallyOrderedSet<DeclRef>
}

CallableGroupId = ContentId<CallableGroupKey>

CallableGroup = {
    id: CallableGroupId,
    key: CallableGroupKey,
    presentationOrder: NodeList<DeclRef>
}

InitializationStrategyDescriptor =
    ExpressionConversionDescriptor(policy: RuleId)
  | DeclaredConstructorDescriptor(constructors: CallableGroupId)
  | SynthesizedConstructorDescriptor(constructors: CallableGroupId)
  | AggregateInitializationDescriptor(shape: AggregateInitializationShapeId)
  | StandardInitializationDescriptor(rule: StandardInitializationRuleId)
  | AllocationInitializationDescriptor(rule: StandardEnvironmentRuleId)

strategyOf(ExpressionConversionDescriptor(_)) = ExpressionConversionStrategy
strategyOf(DeclaredConstructorDescriptor(_)) = DeclaredConstructorStrategy
strategyOf(SynthesizedConstructorDescriptor(_)) = SynthesizedConstructorStrategy
strategyOf(AggregateInitializationDescriptor(_)) = AggregateStrategy
strategyOf(StandardInitializationDescriptor(r)) = StandardInitializationStrategy(r)
strategyOf(AllocationInitializationDescriptor(_)) = AllocationStrategy

NonInitializableReason =
    AbstractType(type: TypeId)
  | IncompleteType(type: TypeId)
  | UninhabitedType(type: TypeId)
  | RuntimeUnsizedType(type: TypeId)
  | NoAdmittedInitializationStrategy(type: TypeId,
                                     languageRules: LanguageRuleSetId)
  | InitializationForbidden(type: TypeId, rule: RuleId)
  | ErroneousInitializationModel(type: TypeId, error: ErrorId)

InitializationModel =
    InitializableModel {
        target: TypeId,
        environment: SemanticEnvironmentId,
        strategies:
            CanonicallyOrderedMap<InitializationStrategy,
                                  InitializationStrategyDescriptor>,
        policy: InitializationStrategyPolicy
    }
  | NonInitializable(reason: NonInitializableReason)

AllocationProviderRank =
    CallableAllocationProviderRank(rank: CandidateRank)
  | RegisteredAllocationProviderRank(
        rule: StandardEnvironmentRuleId,
        components: NodeMap<RuleId, BoundedNat>)

InitializationRankDetailFor<ExpressionConversionStrategy> =
    ConversionInitializationRank(rank: ConversionCost)

InitializationRankDetailFor<DeclaredConstructorStrategy> =
    CallableInitializationRank(rank: CandidateRank)

InitializationRankDetailFor<SynthesizedConstructorStrategy> =
    CallableInitializationRank(rank: CandidateRank)

InitializationRankDetailFor<AggregateStrategy> =
    AggregateInitializationRank(defaultedSlots: BoundedNat,
                                legacyFlatteningSteps: BoundedNat)

InitializationRankDetailFor<StandardInitializationStrategy(r)> =
    RegisteredInitializationRank(
        rule: r,
        components: NodeMap<RuleId, BoundedNat>)

InitializationRankDetailFor<AllocationStrategy> =
    AllocationInitializationRank(provider: AllocationProviderRank,
                                 payload: InitializationRankId)

InitializationRank =
    exists strategy: InitializationStrategy . {
        strategy: strategy,
        detail: InitializationRankDetailFor<strategy>
    }

InitializationRankId = ContentId<InitializationRank>

InitializationTrace = {
    request: InitializationRequestId,
    strategy: Option<InitializationStrategy>,
    events: NodeList<SemanticTraceEvent>
}

InitializationTraceId = ContentId<InitializationTrace>

InitializationComparisonOutcome =
    PreferLeftInitialization
  | PreferRightInitialization
  | EquivalentInitialization
  | IncomparableInitialization(reason: InitializationIncomparability)

InitializationIncomparability =
    NoStrategyPriorityRelation
  | EqualRankDistinctPlans
  | MismatchedRankDomains
  | ConflictingInitializationRules(rules: NonEmpty<RuleId>)

AllocationProviderComparisonProof =
    CallableAllocationProviderComparison(proof: CandidateComparisonProof)
  | RegisteredAllocationProviderComparison(rule: RuleId,
                                             inputs: CanonicalArguments,
                                             outcome: InitializationComparisonOutcome)
  | MixedAllocationProviderComparison(rule: RuleId,
                                      inputs: CanonicalArguments,
                                      outcome: InitializationComparisonOutcome)

InitializationRankComparisonStep =
    ConversionCostComparison(left: ConversionCost,
                             right: ConversionCost,
                             outcome: InitializationComparisonOutcome)
  | CallableRankComparison(proof: CandidateComparisonProof)
  | AggregateRankComparison(rule: RuleId,
                            inputs: CanonicalArguments,
                            outcome: InitializationComparisonOutcome)
  | RegisteredRankComparison(rule: RuleId,
                             inputs: CanonicalArguments,
                             outcome: InitializationComparisonOutcome)
  | AllocationRankComparison(
        provider: AllocationProviderComparisonProof,
        payload: InitializationRankComparisonProofId)

InitializationRankComparisonProof = {
    left: InitializationRankId,
    right: InitializationRankId,
    steps: NonEmpty<InitializationRankComparisonStep>,
    outcome: InitializationComparisonOutcome
}

InitializationRankComparisonProofId = ContentId<InitializationRankComparisonProof>

InitializationComparisonStepAt<S: WitnessTableState> =
    IdenticalInitializationCandidate(candidate: ApplicableInitializationCandidateId<S>)
  | StrategyPriorityStep(preferred: InitializationStrategy,
                         other: InitializationStrategy,
                         rule: InitializationStrategyPriorityId)
  | RankComparisonStep(proof: InitializationRankComparisonProofId)
  | CanonicalPlanEquivalenceStep(rule: RuleId, inputs: CanonicalArguments)

InitializationComparisonProofAt<S: WitnessTableState> = {
    left: ApplicableInitializationCandidateId<S>,
    right: ApplicableInitializationCandidateId<S>,
    policy: InitializationStrategyPriorityId,
    steps: NonEmpty<InitializationComparisonStepAt<S>>,
    outcome: InitializationComparisonOutcome
}

InitializationComparisonProof = InitializationComparisonProofAt<Published>
```

`INI-MOD-001`: Strategy enumeration is exactly the domain of `model.strategies` intersected with
strategies permitted by the source form and site. Every map key equals
`strategyOf(descriptor)`. The descriptor is the sole source of the callable group, aggregate shape,
standard rule, allocation rule, or conversion policy needed to construct that candidate. An
implementation cannot try constructors and then expose aggregate initialization only after they
fail. If both are present, both are evaluated and their ordering requires an
`InitializationComparisonProof` from the model's named priority relation.

`INI-MOD-002`: An extension may contribute constructor declarations only under a policy explicitly
admitting extension constructors. Model construction incorporates all applicable extensions into
the `DeclaredConstructorDescriptor` callable group before the model freezes. Later lookup cannot
create or mutate that descriptor, alter an aggregate descriptor's slots, or remove an existing
strategy. The compatibility ledger freezes the default policy per language version.

`INI-MOD-003`: A standard rule declares its operand schema, permitted forms/sites, result target,
rank, selection effects, ordinary inferred-capability requirement, optional concrete availability,
and plan constructor. “Builtin type” is not permission for a hidden checker branch, and an ordinary
requirement cannot be reinterpreted as a concrete selection filter.

`INI-MOD-004`: `CallableGroupId` is the content identity of its target and canonical member set.
`presentationOrder` is a duplicate-free bijection onto that set and affects diagnostics only. Every
member resolves to an `ConstructorCallable` for `key.target`. `NonInitializable` records a stable
property of the target definition or a named language rule; failed lookup, an inapplicable call, or
a blocked dependency is not a non-initializable model.

`INI-MOD-005`: An `InitializableModel` has a nonempty strategy map, and every descriptor resolves in
`environment` for exactly `target`. Declared and synthesized descriptors resolve callable groups
whose targets equal `target`; the aggregate descriptor resolves a shape whose target equals
`target`; and standard/allocation/conversion rules declare that same target or a target-generic
predicate that accepts it. A strategy cannot be admitted without its descriptor, and a descriptor
cannot be hidden outside the map. Consequently a model that offers both nominal and aggregate
initialization contains both executable resources rather than choosing one lossy sum alternative.

`INI-RNK-001`: `InitializationRank` is a dependent pair, not an integer cost or an independently
tagged union. Its strategy uniquely selects the only admissible detail constructor. In particular,
declared and synthesized initializers carry callable rank, aggregate initialization carries aggregate
rank, `StandardInitializationStrategy(r)` carries a registered rank for exactly `r`, and allocation
carries both its provider rank and the selected payload plan's complete nested rank. No generic
“exact” or composite detail may be attached to an unrelated strategy. All `BoundedNat` components
satisfy chapter 7's common-maximum invariant. A trace is the content hash of its request, strategy,
and deterministic semantic events, so retrying a query cannot change its identity by scheduling or
enumeration order. An applicable, per-strategy rejected, or recovered candidate has
`Some(candidateStrategy)`; only `RejectedBeforeStrategy` has `None`.

`INI-RNK-002`: A comparison proof names two applicable candidates from the same request, uses that
request model's priority policy, and contains only steps whose endpoints and rank domains validate.
A `RankComparisonStep` resolves ranks equal to its candidate endpoints and uses exactly the step
constructor admitted by their dependent detail family. Allocation comparison recursively proves both
provider and payload ranking; it cannot discard the payload rank after choosing an allocator. The
proof establishes one edge of the strategy-specific partial order. Equivalent candidates need an
explicit canonical-plan equivalence step; equal scalar-looking components or stable source order
cannot make distinct plans equivalent. Incomparable maxima remain ambiguous.

## Aggregate initialization shapes

```text
ShapeIndex = {
    coordinates: NonEmpty<UInt32>
}

AggregateSlotKey =
    FieldSlot(field: DeclId)
  | ArraySlot(index: ConstValue)
  | TupleSlot(index: UInt32)
  | ShapeSlot(index: ShapeIndex)

DefaultMemberRecipe = {
    owner: DeclId,
    slot: AggregateSlotKey,
    binder: Option<CanonicalGenericBinder>,
    expression: NodeId<Typed>,
    resultType: TypeId,
    readablePredecessors: CanonicallyOrderedSet<AggregateSlotKey>,
    origin: Origin
}

DefaultMemberRecipeId = ContentId<DefaultMemberRecipe>

AggregateSlot = {
    key: AggregateSlotKey,
    type: TypeId,
    writtenName: Option<Name>,
    defaultRecipe: Option<DefaultMemberRecipeId>,
    required: Bool,
    origin: Origin
}

AggregateInitializationShape = {
    target: TypeId,
    slots: CanonicallyOrderedMap<AggregateSlotKey, AggregateSlot>,
    positionalOrder: NodeList<AggregateSlotKey>,
    policy: AggregateInitializationPolicy
}

AggregateInitializationShapeId = ContentId<AggregateInitializationShape>

AggregateInitializationPolicy = {
    missing: RequireAll | FillFromMemberDefaultsThenTypeDefault,
    nesting: StrictNested | VersionedLegacyFlattening(rule: RuleId),
    designators: DisallowDesignators | AllowDeclaredDesignators
}

AggregateEligibilityFailure =
    TargetHasNoAggregateShape(type: TypeId)
  | IncompleteAggregateDefinition(type: TypeId)
  | InvalidAggregateSlot(slot: AggregateSlotKey,
                         reason: NonInitializableReason)
  | InvalidDefaultMemberRecipe(slot: AggregateSlotKey,
                               error: ErrorId)
  | DuplicateAggregateSlot(slot: AggregateSlotKey)
  | AggregateRejectedByLanguageRule(type: TypeId, rule: RuleId)
  | RecursiveAggregateShape(cycle: NonEmpty<TypeId>)
  | ErroneousAggregateDefinition(type: TypeId, error: ErrorId)
```

`INI-AGG-001`: A struct shape contains its direct user-semantic stored instance fields only. It
contains no concrete base-struct subobject, method, static member, property, subscript, synthesized
backing field, or field introduced by an extension. Concrete struct inheritance is not a source of
an aggregate slot because it is excluded from the language.

`INI-AGG-002`: `positionalOrder` is a duplicate-free bijection onto `slots`. Source input evaluation
order and destination-subobject initialization order are stored separately in the selected plan;
neither is inferred from map iteration.

`INI-AGG-003`: A missing slot follows the model's exact policy: instantiate its checked
default-member recipe, request type default initialization when permitted, or return
`MissingRequiredSlot`. The checker never clones and rechecks an unchecked source expression under
the caller's context.

`INI-AGG-004`: Nested braces select a nested target shape. Flattening across subobjects exists only
under its named version rule and records the consumed input-to-slot path mapping.

`INI-AGG-005`: A `ShapeIndex` is a non-empty canonical coordinate tuple in the semantic shape's
declared axis order. It is neither a flattened storage offset nor a source-list position. Coordinate
bounds are validated against the target shape, so layout changes cannot alter slot identity.

`INI-AGG-006`: A default-member recipe is content-identified, belongs to exactly its stored owner
and slot, and is checked once under its canonical binder. Its result type equals the slot type after
specialization. `readablePredecessors` contains only slots strictly earlier in `positionalOrder` and
states the partial-target reads admitted while checking the expression. Instantiating a recipe
applies the exact specialization, creates a nested initialization plan, and retains every semantic
use of evaluating the checked expression and initializing its result.

`INI-AGG-007`: `AggregateEligibilityFailure` reports a stable property of shape derivation. A
blocked dependency is a blocked query, not an eligibility failure. The presence or failure of a
user initializer also cannot make a type aggregate-ineligible: when the model contains both a
declared/synthesized initializer descriptor and an aggregate descriptor, both remain candidates.

## Initializer declarations and fresh storage

An initializer has an explicit construction target in its checked callable type:

```text
InitializationTargetMode = FreshStorage | DelegatingStorage

ConstructorResultConvention =
    InitializedTarget(type: TypeId)
  | ReturnedValue(type: TypeId)

InitializationTargetSlot = {
    selfType: TypeId,
    mode: InitializationTargetMode,
    requiredStorage: PhysicalStorageRequirement,
    entryState: InitializationTargetEntryState,
    completion: MustBeFullyInitialized
}

PlanInitializationStorageKey = {
    request: InitializationRequestId,
    ordinal: UInt32
}

PlanInitializationStorageId = ContentId<PlanInitializationStorageKey>

PlanInitializationStorage = {
    id: PlanInitializationStorageId,
    key: PlanInitializationStorageKey,
    valueType: TypeId,
    access: StorageAccessMode,
    mutability: Mutability,
    addressSpace: AddressSpace,
    lifetime: LifetimeId
}

CallablePurpose =
    OrdinaryCallable
  | ConstructorCallable(target: InitializationTargetSlot,
                        resultConvention: ConstructorResultConvention)

InitializationTargetDestination = {
    destination: InitializationDestination,
    compatibility: InitializationTargetCompatibilityProof
}

InitializationTargetBinding = {
    slot: InitializationTargetSlot,
    destination: InitializationTargetDestination
}

InitializationTargetCompatibilityProof = {
    targetType: TypeEqualityProofId,
    requirement: PhysicalStorageRequirement,
    access: AccessProvisionProof,
    addressSpace: AddressSpaceAdmissionProof,
    lifetime: OutlivesProof,
    entryState: InitializationEntryStateEqualityProof
}

InitializationEntryStateEqualityProof = {
    required: InitializationTargetEntryState,
    actual: InitializationTargetEntryState
}
```

`CallablePurpose` is a structural `FuncType` field. The target is neither ordinary parameter
zero nor an implicit receiver recovered from declaration nesting. An ordinary instance receiver
may coexist only for a language-defined delegating form, with both roles explicit.

`INI-CTR-001`: Calling a `ConstructorCallable(target, resultConvention)` requires an explicit
`InitializationTargetBinding`. Its destination is the request destination or an internal destination
created by the enclosing plan. The compatibility requirement equals `target.requiredStorage`; the
resolved physical shape has `target.selfType`, provides the required effective access, belongs to a
permitted address space, outlives the required lifetime, and has the exact target entry state.
Supplied storage retains its `PhysicalStorageProof` inside the destination. Plan-owned,
allocated-object, and projected destinations derive the same facts from their immutable records and
never fabricate a source-storage proof. Internal storage is admitted only for `FreshStorage` with
`Uninitialized` entry state; delegating storage must be the request's explicitly partial destination.
Normal completion produces the stored `resultConvention`; exceptional completion leaves only the
cleanup state described by the plan.

The compatibility proof's endpoints are exact: `targetType` relates the resolved storage value type
and `target.selfType`; `requirement = target.requiredStorage`; `access` proves that shape's effective
access provides `requirement.access`; `addressSpace` proves the shape's exact address space is
admitted by `requirement.addressSpace`; `lifetime` proves the shape lifetime outlives
`requirement.minimumLifetime`; and `entryState` compares the actual destination state with
`target.entryState`. No access proof, target equality, or capability-availability proof can stand in
for the address-space admission premise.

`INI-CTR-002`: Constructor argument mapping reuses `ArgumentMap`, generic deduction, overload
comparison, and keyed access plans from chapter 7. The initialization target is a separate role and
is never consumed as receiver/argument zero. Aggregate slot mapping uses its own keyed map and is
not disguised as a synthesized callable invocation.

`INI-CTR-003`: A default-member initializer is checked once as a persistent recipe parameterized by
the enclosing type's canonical binder and the partially initialized target. Instantiation applies
the exact specialization and records which earlier fields may be read.

`INI-CTR-004`: `ConstructorCallable(target, InitializedTarget(T))` has logical result `VoidType` and
requires `target.selfType = T`; the initialized storage is observed through the separate target
role. `ConstructorCallable(target, ReturnedValue(T))` has logical result `T`, and its selected
initializer operation contains an explicit transfer from that returned value into the target. The
`FuncType.result`, result convention, target type, and stored completion operation are validated
together and cannot be independent authorities.

## Plans

```text
OperationQualifiedEvaluationOrder<R> = {
    operation: InitializationPath,
    operands: NodeList<R>
}

OperationQualifiedInitializationOrder<R> = {
    operation: InitializationPath,
    subobjects: NodeList<R>
}

ConstructorCallOperandRole =
    InitializationTargetCallOperand
  | BoundCallOperand(slot: BoundCallSlot)

RegisteredInitializationOperandKey = {
    rule: StandardEnvironmentRuleId,
    stableName: QualifiedName,
    ordinal: UInt32
}

RegisteredInitializationResultKey = {
    rule: StandardEnvironmentRuleId,
    stableName: QualifiedName,
    ordinal: UInt32
}

PhysicalStorageEndpointShape = {
    valueType: TypeId,
    access: StorageAccessMode,
    mutability: Mutability,
    addressSpace: PhysicalStorageAddressSpace,
    lifetime: LifetimeId,
    alias: AliasProvenance,
    sourceProvenance: PhysicalStorageSourceProvenance
}

InitializationEndpointShape =
    ValueInitializationEndpoint(type: TypeId)
  | PhysicalStorageInitializationEndpoint(shape: PhysicalStorageEndpointShape)
  | AllocationHandleInitializationEndpoint(object: AllocationObjectId,
                                           handleType: TypeId,
                                           lifetime: LifetimeId)

InitializationStorageRoot =
    SuppliedInitializationStorageRoot(storage: PhysicalStorageRef)
  | PlanInitializationStorageRoot(storage: PlanInitializationStorageId)
  | AllocatedObjectStorageRoot(object: AllocationObjectId)

InitializationStorageProjectionRule =
    AggregateSlotStorageProjection(shape: AggregateInitializationShapeId,
                                   slot: AggregateSlotKey)
  | NominalFieldStorageProjection(owner: DeclId, field: DeclId)
  | ClassBaseStorageProjection(derived: DeclId, base: DeclId)
  | RegisteredInitializationStorageProjection(
        rule: StandardEnvironmentRuleId,
        inputs: CanonicalArguments)

InitializationSubobjectStorageProjection = {
    root: InitializationStorageRoot,
    subobject: InitializationSubobjectKey,
    rule: InitializationStorageProjectionRule,
    shape: PhysicalStorageEndpointShape
}

InitializationEndpointSourceAt<S: WitnessTableState> =
    RequestInputEndpoint(input: InitializationInputId)
  | CheckedExpressionEndpoint(expression: NodeId<Typed>)
  | NestedInitializationResultEndpoint(plan: InitializationPlanIdAt<S>)
  | ConstructorCallResultEndpoint(call: ConstructorCallPlanId<S>)
  | RegisteredInitializationResultEndpoint(
        execution: RegisteredInitializationExecutionId<S>,
        result: RegisteredInitializationResultKey)
  | InitializationPlanResultEndpoint(request: InitializationRequestId)
  | RequestedInitializationStorageEndpoint(destination: InitializationDestination)
  | PlanInitializationStorageEndpoint(storage: PlanInitializationStorageId)
  | AllocatedObjectStorageEndpoint(object: AllocationObjectId)
  | ProjectedInitializationStorageEndpoint(
        projection: InitializationSubobjectStorageProjection)
  | AllocationHandleEndpoint(object: AllocationObjectId)

InitializationEndpointAt<S: WitnessTableState> = {
    source: InitializationEndpointSourceAt<S>,
    shape: InitializationEndpointShape
}

ConstructorCallPlanKeyAt<S: WitnessTableState> = {
    operation: InitializationPath,
    call: TypedCallAt<S>,
    operands:
        CanonicallyOrderedMap<ConstructorCallOperandRole,
                              InitializationEndpointAt<S>>,
    evaluationOrder:
        OperationQualifiedEvaluationOrder<ConstructorCallOperandRole>
}

ConstructorCallPlanId<S: WitnessTableState> =
    ContentId<ConstructorCallPlanKeyAt<S>>

ConstructorCallPlanAt<S: WitnessTableState> = {
    id: ConstructorCallPlanId<S>,
    key: ConstructorCallPlanKeyAt<S>
}

ConstructorCallPlan = ConstructorCallPlanAt<Published>

RegisteredInitializationSelectionAt<S: WitnessTableState> = {
    registration: RegisteredDataOperationRegistration,
    selectionEffects: EffectSet,
    effectAllowance: EffectAllowanceValidation,
    effectUse: EffectUse<S>,
    capabilities: CapabilitySelectionAt<S>
}

RegisteredInitializationExecutionKeyAt<S: WitnessTableState> = {
    operation: InitializationPath,
    selection: RegisteredInitializationSelectionAt<S>,
    operands:
        CanonicallyOrderedMap<RegisteredInitializationOperandKey,
                              InitializationEndpointAt<S>>,
    results:
        CanonicallyOrderedMap<RegisteredInitializationResultKey,
                              InitializationEndpointShape>,
    evaluationOrder:
        OperationQualifiedEvaluationOrder<RegisteredInitializationOperandKey>
}

RegisteredInitializationExecutionId<S: WitnessTableState> =
    ContentId<RegisteredInitializationExecutionKeyAt<S>>

RegisteredInitializationExecutionAt<S: WitnessTableState> = {
    id: RegisteredInitializationExecutionId<S>,
    key: RegisteredInitializationExecutionKeyAt<S>
}

TransferOperationAt<S: WitnessTableState> =
    TrivialValueTransfer(type: TypeId, rule: StandardEnvironmentRuleId)
  | CopyTransfer(call: ConstructorCallPlanId<S>)
  | MoveTransfer(call: ConstructorCallPlanId<S>)
  | RegisteredTransfer(execution: RegisteredInitializationExecutionId<S>)

TransferEvaluationRole = TransferSourceEvaluation | TransferDestinationEvaluation

TransferPlanAt<S: WitnessTableState> = {
    operation: InitializationPath,
    source: InitializationEndpointAt<S>,
    destination: InitializationEndpointAt<S>,
    transfer: TransferOperationAt<S>,
    evaluationOrder: OperationQualifiedEvaluationOrder<TransferEvaluationRole>
}

AllocationObjectKey = {
    request: InitializationRequestId,
    operation: InitializationPath,
    allocatedType: TypeId
}

AllocationObjectId = ContentId<AllocationObjectKey>

AllocationObject = {
    id: AllocationObjectId,
    key: AllocationObjectKey
}

AllocationObjectStorage = {
    object: AllocationObjectId,
    shape: PhysicalStorageEndpointShape
}

AllocationHandle = {
    object: AllocationObjectId,
    handleType: TypeId,
    lifetime: LifetimeId,
    ownershipRule: StandardEnvironmentRuleId
}

AllocationProviderAt<S: WitnessTableState> =
    CallableAllocator(call: ConstructorCallPlanId<S>)
  | RegisteredAllocator(execution: RegisteredInitializationExecutionId<S>)

AllocationCleanupAt<S: WitnessTableState> =
    CallableDeallocator(call: ConstructorCallPlanId<S>)
  | RegisteredDeallocator(execution: RegisteredInitializationExecutionId<S>)

AllocationProviderResultBindingAt<S: WitnessTableState> = {
    providerResult: InitializationEndpointAt<S>,
    handle: AllocationHandle,
    storage: AllocationObjectStorage,
    projectionRule: StandardEnvironmentRuleId
}

AllocationEvaluationRole =
    AllocationProviderEvaluation
  | AllocationPayloadEvaluation

AllocationPlanKeyAt<S: WitnessTableState> = {
    object: AllocationObject,
    provider: AllocationProviderAt<S>,
    result: AllocationProviderResultBindingAt<S>,
    cleanup: AllocationCleanupAt<S>,
    failureEffects: EffectSet
}

AllocationPlanId<S: WitnessTableState> = ContentId<AllocationPlanKeyAt<S>>

AllocationPlanAt<S: WitnessTableState> = {
    id: AllocationPlanId<S>,
    key: AllocationPlanKeyAt<S>,
    origin: Origin
}

ConstructorCallCompletionAt<S: WitnessTableState> =
    InitializedTargetCompletion
  | TransferReturnedValueToTarget(transfer: TransferPlanAt<S>)

InitializationPlanOutputAt<S: WitnessTableState> =
    InitializedRequestedStorage
  | ProducedDirectValue
  | ProducedFromPlanStorage(storage: PlanInitializationStorageId,
                            transfer: TransferPlanAt<S>)
  | ProducedAllocationHandle(allocation: AllocationPlanId<S>)
  | RecoveredInitializationOutput(error: ErrorId)

AggregateBindingAt<S: WitnessTableState> =
    WrittenAggregateBinding(input: InitializationInputId,
                            destination: InitializationEndpointAt<S>,
                            plan: InitializationPlanIdAt<S>)
  | DefaultMemberAggregateBinding(recipe: DefaultMemberRecipeId,
                                  destination: InitializationEndpointAt<S>,
                                  plan: InitializationPlanIdAt<S>)
  | TypeDefaultAggregateBinding(rule: RuleId,
                                destination: InitializationEndpointAt<S>,
                                plan: InitializationPlanIdAt<S>)

InitializationOperationAt<S: WitnessTableState> =
    ExpressionInitialization(operation: InitializationPath,
                             source: InitializationInputId,
                             conversion: ConversionPlan<S>,
                             transfer: TransferPlanAt<S>)
  | ConstructorCallInitialization(call: ConstructorCallPlanId<S>,
                                   target: InitializationTargetBinding,
                                   completion: ConstructorCallCompletionAt<S>)
  | AggregateInitialization(
        operation: InitializationPath,
        shape: AggregateInitializationShapeId,
        bindings: CanonicallyOrderedMap<AggregateSlotKey,
                                        AggregateBindingAt<S>>,
        sourceEvaluationOrder:
            OperationQualifiedEvaluationOrder<AggregateSlotKey>,
        storageInitializationOrder:
            OperationQualifiedInitializationOrder<AggregateSlotKey>)
  | StandardInitialization(execution: RegisteredInitializationExecutionId<S>)
  | AllocationInitialization(allocation: AllocationPlanId<S>,
                             payload: InitializationPlanIdAt<S>,
                             evaluationOrder:
                                 OperationQualifiedEvaluationOrder<AllocationEvaluationRole>)
  | InitializationRecovery(error: ErrorId)

InitializationSubobjectKey =
    RootInitializationSubobject(type: TypeId)
  | PlanStorageInitializationSubobject(storage: PlanInitializationStorageId)
  | AllocatedObjectInitializationSubobject(object: AllocationObjectId)
  | AggregateSlotInitializationSubobject(shape: AggregateInitializationShapeId,
                                         slot: AggregateSlotKey)
  | NominalFieldInitializationSubobject(owner: DeclId, field: DeclId)
  | ClassBaseInitializationSubobject(derived: DeclId, base: DeclId)
  | RegisteredInitializationSubobject(rule: StandardEnvironmentRuleId,
                                      key: CanonicalArguments)

SubobjectInitializationState =
    Uninitialized
  | Initializing
  | Initialized
  | MovedFrom
  | Destroyed
  | InitializationError(ErrorId)

AllocationOwnershipState =
    AllocationNotAcquired
  | AllocationOwnedByPlan
  | AllocationTransferredToResult
  | AllocationReleased

PlanStorageLifetimeState =
    PlanStorageNotCreated
  | PlanStorageLive
  | PlanStorageLifetimeEnded

InitializationState = {
    subobjects:
        CanonicallyOrderedMap<InitializationSubobjectKey,
                              SubobjectInitializationState>,
    allocations:
        CanonicallyOrderedMap<AllocationObjectId, AllocationOwnershipState>,
    planStorage:
        CanonicallyOrderedMap<PlanInitializationStorageId,
                              PlanStorageLifetimeState>
}

InitializationExceptionalExitCause =
    ThrownInitializationError(errorType: TypeId)
  | AllocationFailure(errorType: TypeId)
  | RegisteredInitializationFailure(rule: StandardEnvironmentRuleId,
                                    inputs: CanonicalArguments)

InitializationExitKey =
    NormalInitializationExit
  | ExceptionalInitializationExit(path: InitializationPath,
                                  cause: InitializationExceptionalExitCause)

SubobjectInitializationTransitionCauseAt<S: WitnessTableState> =
    BeginSubobjectInitialization(path: InitializationPath)
  | CompleteSubobjectInitialization(path: InitializationPath)
  | MoveFromSubobject(path: InitializationPath,
                      transfer: TransferPlanAt<S>)
  | DelegateObjectInitialization(path: InitializationPath,
                                 call: ConstructorCallPlanId<S>)
  | RecoverSubobjectInitialization(path: InitializationPath,
                                   error: ErrorId)
  | DestroySubobject(path: InitializationPath,
                     destruction: DestructionExecutionAt<S>)

AllocationOwnershipTransitionCause =
    AcquireAllocation(allocation: AllocationObjectId)
  | TransferAllocationToResult(allocation: AllocationObjectId)
  | ReleaseAllocation(allocation: AllocationObjectId)

PlanStorageLifetimeTransitionCause =
    CreatePlanStorage(storage: PlanInitializationStorageId)
  | EndPlanStorageLifetime(storage: PlanInitializationStorageId)

DestructionPlanAt<S: WitnessTableState> =
    CallableDestructor(call: ConstructorCallPlanId<S>)
  | RegisteredDestructor(execution: RegisteredInitializationExecutionId<S>)
  | TrivialDestructor(rule: StandardEnvironmentRuleId)

NonThrowingDestructionProof = {
    effects: EffectSet
}

DestructionExecutionAt<S: WitnessTableState> = {
    plan: DestructionPlanAt<S>,
    selectionEffects: EffectSet,
    nonThrowing: NonThrowingDestructionProof,
    semanticUses: PlanSemanticUses<S>
}

InitializationStateTransitionAt<S: WitnessTableState> =
    SubobjectStateTransition {
        subobject: InitializationSubobjectKey,
        before: SubobjectInitializationState,
        after: SubobjectInitializationState,
        cause: SubobjectInitializationTransitionCauseAt<S>
    }
  | AllocationStateTransition {
        allocation: AllocationObjectId,
        before: AllocationOwnershipState,
        after: AllocationOwnershipState,
        cause: AllocationOwnershipTransitionCause
    }
  | PlanStorageStateTransition {
        storage: PlanInitializationStorageId,
        before: PlanStorageLifetimeState,
        after: PlanStorageLifetimeState,
        cause: PlanStorageLifetimeTransitionCause
    }

InitializationExecutionTargetAt<S: WitnessTableState> =
    RequestedStorageExecutionTarget(destination: InitializationDestination)
  | PlanStorageExecutionTarget(storage: PlanInitializationStorageId)
  | AllocatedObjectExecutionTarget(allocation: AllocationPlanId<S>)
  | DirectValueExecutionTarget(type: TypeId)

InitializationEntryStateEvidenceAt<S: WitnessTableState> =
    RequestedStorageEntry(
        request: InitializationRequestId,
        destination: InitializationDestination,
        targetType: TypeEqualityProofId,
        entryState: InitializationEntryStateEqualityProof)
  | FreshPlanStorageEntry(request: InitializationRequestId,
                          storage: PlanInitializationStorageId)
  | FreshAllocatedObjectEntry(request: InitializationRequestId,
                              allocation: AllocationPlanId<S>)
  | DirectValueEntry(request: InitializationRequestId, type: TypeId)

RequiredSubobjectDerivationAt<S: WitnessTableState> =
    RootValueRequirement(type: TypeId)
  | ConstructorTargetRequirement(target: InitializationTargetSlot)
  | AggregateShapeRequirement(shape: AggregateInitializationShapeId)
  | StandardRuleRequirement(execution: RegisteredInitializationExecutionId<S>)
  | AllocationPayloadRequirement(allocation: AllocationPlanId<S>,
                                 payload: InitializationPlanIdAt<S>)

RequiredInitializationSubobjectsAt<S: WitnessTableState> = {
    target: InitializationExecutionTargetAt<S>,
    subobjects: CanonicallyOrderedSet<InitializationSubobjectKey>,
    derivation: RequiredSubobjectDerivationAt<S>
}

InitializationStateProjection = {
    subobjects:
        CanonicallyOrderedMap<InitializationSubobjectKey,
                              InitializationSubobjectKey>,
    allocations:
        CanonicallyOrderedMap<AllocationObjectId, AllocationObjectId>,
    planStorage:
        CanonicallyOrderedMap<PlanInitializationStorageId,
                              PlanInitializationStorageId>
}

NestedInitializationCompositionAt<S: WitnessTableState> = {
    operation: InitializationPath,
    plan: InitializationPlanIdAt<S>,
    stateProjection: InitializationStateProjection,
    exitProjection:
        CanonicallyOrderedMap<InitializationExitKey, InitializationExitKey>
}

InitializationExitCompletion =
    CompletedAtTransition(boundary: UInt32,
                          state: InitializationState)
  | DidNotCompleteInitialization

InitializationExitStateProofAt<S: WitnessTableState> = {
    exit: InitializationExitKey,
    transitions: NodeList<InitializationStateTransitionAt<S>>,
    completion: InitializationExitCompletion,
    state: InitializationState
}

InitializationCleanupStepAt<S: WitnessTableState> =
    DestroyInitializationSubobject(
        subobject: InitializationSubobjectKey,
        expected: Initialized | MovedFrom,
        destruction: DestructionExecutionAt<S>,
        transition: InitializationStateTransitionAt<S>)
  | RunAllocationCleanup(
        allocation: AllocationPlanId<S>,
        expected: AllocationOwnedByPlan,
        cleanup: AllocationCleanupAt<S>,
        transition: InitializationStateTransitionAt<S>)
  | EndInitializationStorageLifetime(
        storage: PlanInitializationStorageId,
        expected: PlanStorageLive,
        transition: InitializationStateTransitionAt<S>)

InitializationExitCleanupAt<S: WitnessTableState> = {
    exit: InitializationExitKey,
    entryState: InitializationState,
    steps: NodeList<InitializationCleanupStepAt<S>>,
    finalState: InitializationState
}

InitializationExecutionContractAt<S: WitnessTableState> = {
    request: InitializationRequestId,
    target: InitializationExecutionTargetAt<S>,
    entryState: InitializationState,
    entryEvidence: InitializationEntryStateEvidenceAt<S>,
    requiredSubobjects: RequiredInitializationSubobjectsAt<S>,
    nestedExecutions:
        CanonicallyOrderedMap<InitializationPath,
                              NestedInitializationCompositionAt<S>>,
    exits: CanonicallyOrderedMap<InitializationExitKey,
                                 InitializationExitStateProofAt<S>>,
    cleanupByExit:
        CanonicallyOrderedMap<InitializationExitKey,
                              InitializationExitCleanupAt<S>>
}

InitializationPlanKeyAt<S: WitnessTableState> = {
    request: InitializationRequestId,
    planStorage:
        CanonicallyOrderedMap<PlanInitializationStorageId,
                              PlanInitializationStorage>,
    operation: InitializationOperationAt<S>,
    output: InitializationPlanOutputAt<S>,
    targetType: TypeId,
    semanticUses: PlanSemanticUses<S>,
    execution: InitializationExecutionContractAt<S>
}

InitializationPlanIdAt<S: WitnessTableState> = ContentId<InitializationPlanKeyAt<S>>

InitializationPlanAt<S: WitnessTableState> = {
    id: InitializationPlanIdAt<S>,
    key: InitializationPlanKeyAt<S>
}

TemporaryInitializationPlanApplicationAt<S: WitnessTableState> = {
    plan: InitializationPlanIdAt<S>,
    sourceInput: InitializationInputId,
    destination: PlanInitializationStorageId,
    site: SemanticOperationSiteAssignment,
    identity: TemporaryStorageIdentity,
    rankedConversion: InitializationPath
}

InitializationPlan = InitializationPlanAt<Published>
InitializationPlanId = InitializationPlanIdAt<Published>
TransferPlan = TransferPlanAt<Published>
TemporaryInitializationPlanApplication =
    TemporaryInitializationPlanApplicationAt<Published>
```

`INI-PLN-001`: A plan satisfies `plan.id = ContentId(plan.key)` and is executable without name
lookup, overload resolution, generic inference, conversion search, initialization-model discovery,
or endpoint reconstruction. Every referenced call, registered execution, allocation, transfer, and
nested initialization plan resolves by content ID. Their target/operand mappings, operation-qualified
orders, semantic uses, state transitions, exit states, and cleanup are complete. The selecting
checked node's presentation origin is not a separate plan-key field. Occurrence-bearing input IDs
and semantic-use origins remain in the key because they define evaluate-once identity and graph-use
identity, respectively. The referenced content graph is finite: a call/registered/allocation record
cannot consume its own result ID, and recursive construction is returned as
`RecursiveInitialization` before content identity is formed.

`INI-PLN-002`: Every `TransferPlanAt<S>` names its exact source and destination endpoint, operation
path, executable transfer, and source/destination evaluation order. The destination is either a
physical-storage endpoint whose effective access permits the write or the unique
`InitializationPlanResultEndpoint(plan.key.request)` for a produce-value result. A callable
copy/move resolves a `ConstructorCallPlanAt<S>` whose operand mapping connects those endpoints to
the call's exact slots. A registered transfer resolves a schema-validated registered execution with
the same endpoints. A trivial transfer names the standard rule defining its value, overlap,
lifetime, and bit-preservation semantics. The endpoint types equal the transfer operation's declared
types. Copy initialization is not merely loading a storage, and move initialization is never inferred
later from absence of uses.

`INI-PLN-003`: `ConstructorCallInitialization.call` resolves the complete selected typed call,
including defaults, packs, access plans, witness values, contract uses, endpoint mapping, and
evaluation order. Its callable purpose and mapped initialization-target operand equal the stored
`InitializationTargetBinding`. `InitializedTarget` requires `InitializedTargetCompletion`;
`ReturnedValue` requires `TransferReturnedValueToTarget`, whose transfer source is exactly the call
result endpoint and whose destination is exactly the mapped target endpoint. Lowering never guesses
from the logical result whether a returned value must be stored.

`INI-PLN-004`: Construction-stage plans may contain operational witness values only from their
authorized synthesis/conformance scope. Atomic publication rewrites them to published witness
values without changing form, strategy, target, mapping, or execution order.

`INI-PLN-005`: `semanticUses` is the exact canonical union of uses introduced directly by the
operation and by every resolved nested conversion, call plan, registered execution, default recipe,
allocation provider/cleanup, destructor, transfer, and initialization plan. It is rootless because
the request's checking context already assigns each use owner and because the plan is awaiting
aggregation, not defining a second callable contract. When elaboration installs the selected plan in
an enclosing callable or global-initializer root, it unions the maps into that root's
`EffectUseGraph<S>` and `CapabilityUseGraph<S>` without re-keying: every use owner must equal the
enclosing root, equal IDs must have equal payloads, and any conflicting payload is invalid. Only the
selected executable plan is aggregated; rejected candidates, comparison traces, and recovery-only
diagnostic alternatives do not become semantic uses.

`INI-PLN-006`: `execution.request` equals `plan.key.request` and `plan.key.targetType` equals that
request's explicit target. Its execution target, entry evidence, and entry state are the unique ones
admitted by that request goal and selected operation. A requested storage
entry repeats the request's exact destination and entry-state proof. Fresh plan/allocation storage
starts with its required subobject `Uninitialized`, and with respectively `PlanStorageNotCreated` or
`AllocationNotAcquired`; a direct-value entry is admitted only for `ProduceValue`. The
`requiredSubobjects` set is recomputed from its closed derivation and must equal the complete target
representation required at the initialization-completion checkpoint. A client cannot omit a field,
class base, registered subobject, or root merely to make an exit proof pass.

`INI-PLN-007`: `ClassBaseInitializationSubobject` is valid only for a declared class-base
subobject. Concrete struct inheritance is excluded and cannot acquire a subobject key through this
schema. Delegating initialization is a state transition over the root and declared subobjects; an
initializer declaration is not fabricated as a storage subobject.
`AllocatedObjectInitializationSubobject(object)` is keyed by allocation-object identity rather than
allocated type, so two allocations of the same type cannot alias definite-initialization state.

`INI-PLN-008`: Each `planStorage` map key equals `storage.id`,
`storage.id = ContentId(storage.key)`, every key's request equals `plan.key.request`, and ordinals are
dense in deterministic creation order. The map domain is exactly the storage IDs reachable from the
operation and output. The storage's effective access provides the bound target's
requirement, its address-space proof satisfies the requirement's symbolic predicate, and its lifetime proof has the
stored endpoints. A `PlanOwnedInitializationStorage` destination refers to exactly one such entry and
cannot use the supplied-storage alternative to carry a `PhysicalStorageProof` for storage it does not
denote. IRReady creates this storage explicitly before the constructor call and derives its alias provenance
from the storage ID.

`INI-PLN-009`: `output` agrees with the request goal. `InitializeStorage` uses
`InitializedRequestedStorage` and every final target is the request's exact physical destination.
Non-allocation `ProduceValue` uses `ProducedDirectValue` only when the selected operation directly
returns the initialized target value; otherwise it uses `ProducedFromPlanStorage` with an existing
fully initialized plan storage and an explicit transfer plan. That plan's source is the named storage
endpoint and its destination is `InitializationPlanResultEndpoint(plan.key.request)`. Extracting by
move records the `SubobjectStateTransition` whose subobject is
`PlanStorageInitializationSubobject(storage)` and whose cause is `MoveFromSubobject` with that exact
transfer. `AllocatingArguments` uses `ProducedAllocationHandle(allocation)`; the allocation object's
type equals `plan.key.targetType`, its handle type equals the request's `ProduceValue` type, and the
normal exit transfers its ownership to the result. No lowering pass may introduce an unrecorded
result temporary, call, or load merely because the goal is `ProduceValue`.
`InitializationRecovery(error)` uses only
`RecoveredInitializationOutput(error)`; that output satisfies neither goal and is accepted solely in
the `RecoveredInitialization` result governed by `INI-IR-006`.

`INI-PLN-010`: The operation algebra contains no `DefaultInitialization(strategy, optionalPlan)` or
equivalent flag-like wrapper. A default/value/omitted-site policy must select one mandatory executable
alternative: a zero-input constructor call, aggregate bindings whose default source is explicit, a
registered standard execution, or another model-declared closed operation. If no such alternative
exists, resolution rejects the candidate. Strategy identity is retained by the candidate/rank and is
never consulted by lowering to reinterpret an operation.

`INI-PLN-011`: An aggregate operation's binding-map domain equals the selected shape's complete slot
domain. `WrittenAggregateBinding` names exactly the mapped source input;
`DefaultMemberAggregateBinding` names the slot's specialized checked recipe; and
`TypeDefaultAggregateBinding` names the rule that admitted type default. Every alternative contains
a mandatory nested plan whose request goal is `InitializeStorage` of its exact projected physical
slot destination and whose target type equals the slot type. The source-evaluation and
storage-initialization orders are independent
duplicate-free bijections onto the applicable binding/slot domains. There is no `Option<input>` whose
absence lowering must reinterpret.

`INI-PLN-012`: A `RegisteredInitializationExecutionAt<S>` satisfies `id = ContentId(key)` and is
executable only when its operand/result key sets, endpoint shapes, registration static inputs, and
evaluation order exactly match the versioned standard rule schema. `StandardInitialization` stores
that execution ID rather than a rule plus unkeyed nested plans. The same record is used for
registered transfer, allocation, deallocation, and destruction, so none of those operations may
rerun rule lookup, infer result projections, or invent operand order during lowering.
Every operand/result key's `rule` equals `selection.registration.rule`.

`INI-PLN-013`: `RegisteredInitializationSelectionAt<S>.registration` is the sole registered-rule,
standard-environment, and static-input authority. `selectionEffects` equals that resolved rule's
pre-inference selection effects and `effectAllowance` validates it against the initialization
request's effect context. `effectUse` is the rule's one ordinary effect use. `capabilities.region`
equals `InitializationEnvironment.contractSelection.assumption`; its ordinary-use map contains the
rule's exact inferred-capability use, and its concrete sources/proof are exactly the resolved
optional rule availability. The enclosing `InitializationPlan.semanticUses` contains the exact
effect use and the merged capability-selection product of every registered and nested operation,
so lowering never reruns selection or loses an explicitly true availability source.

`INI-PLN-014`: A `TemporaryInitializationPlanApplicationAt<S>` is the only way an enclosing access
plan applies chapter 15 initialization to compiler-owned temporary storage. Resolving `plan` yields
an `InitializeStorage(PlanOwnedInitializationStorage(destination), targetType)` request whose
`planStorage` map contains that exact destination, whose `sourceInput` is the single externally
captured source input, and whose operation contains the exact `ExpressionInitialization` conversion
at `rankedConversion`. Its output is `InitializedRequestedStorage`. The enclosing access plan binds
that input to one already captured value, physical storage, or abstract storage. The
initialization plan does not reevaluate the source expression or recapture a receiver/index; its
stored conversion performs the bound storage's ordinary read, if any, exactly once and then performs
the selected value conversion. Thus a getter/read-through-ref operation belongs to this one nested
execution rather than to a second outer preparation recipe.
`site` is the authenticated semantic child assigned by the enclosing access plan and
`identity = temporaryStorageIdentity(site.site)`. The destination remains the initialization plan's
local storage key; its content identity is not reused as an alias root. Instantiating the plan for
this application binds every internal storage endpoint rooted at `destination` to
`ExactAliasRoot(temporaryStorageAliasRoot(identity))`. The enclosing temporary and this application
therefore retain the same nominal `TemporaryStorageIdentity`, so neither checking nor lowering
invents a second ownership identity from an ordinal, node, or storage-map position.

On the normal exit, the execution checkpoint proves the destination fully initialized and transfers
its live storage plus destruction obligation to the enclosing access plan. Every exceptional exit
before that checkpoint remains owned by the initialization plan: its `cleanupByExit` destroys
exactly the initialized subobjects, never destroys an uninitialized whole object, and ends the plan
storage lifetime. Consequently an outer plan may activate its temporary lifetime only after the
normal checkpoint and must not run its whole-object destructor on an initialization failure.

`INI-DST-001`: A `DestructionExecutionAt<S>` is complete selected cleanup, not a request to look up a
destructor from a type. `plan` resolves its exact callable, registered, or trivial execution;
`semanticUses` is the canonical union of that execution's effect and capability uses; and
`selectionEffects` is its exact closed selection effect set. `nonThrowing.effects` equals
`selectionEffects` and does not contain `MayThrow`. At publication, every callable edge in the
execution resolves to a constrained effective contract that also excludes `MayThrow`. This
non-throwing cleanup contract is what permits the same destruction execution on both normal return
and error propagation without an implicit second-error policy.

`INI-END-001`: An initialization endpoint's source uniquely determines its shape. Request and checked
expression endpoints use the resolved typed classifier; nested-plan, call, and registered-result
endpoints use the exact stored result; a plan-result endpoint is an rvalue of a non-allocation
request target;
requested storage resolves its closed destination alternative; plan storage repeats its immutable
storage record with `ConcretePhysicalAddressSpace(storage.addressSpace)`, its nominal plan-storage
alias root, and empty physical-source provenance; and allocated storage/handle repeat the records for
the same `AllocationObjectId`. A physical endpoint therefore retains value type, access, mutability,
physical address space, lifetime, alias provenance, and typed source provenance together.
Deserialization or subplan composition cannot relabel an rvalue as storage, change provenance, or
recover endpoint facts from a nominal type.

`INI-END-002`: `ProjectedInitializationStorageEndpoint` is the only way a plan denotes a physical
aggregate slot, nominal field, class base, or registered subobject. Its semantic subobject key and
projection-rule endpoints agree, its root resolves the supplied/plan/allocation storage that owns the
subobject, and its shape is the exact physical projection of that root. Projection preserves the
root alias provenance and cannot widen access, mutability, address space, or lifetime. Ordinary
field/slot/base projections preserve physical-source provenance exactly; a registered projection may
change it only through its stored versioned source-component rule. Aggregate
bindings, destructor/deallocator calls, and nested initialization targets use this endpoint rather
than treating a whole-object storage endpoint as an unnamed field address.

`INI-CAL-001`: An initialization call plan satisfies `id = ContentId(key)`. Its bound-call operand
domain equals `call.callSlots`; it additionally contains `InitializationTargetCallOperand` exactly
when the callable purpose is an initializer. Each mapped endpoint satisfies that slot's stored access
plan and the target endpoint equals the separately validated target binding. Its qualified evaluation
order has exactly this operand domain. `ConstructorCallResultEndpoint(call.id)` has the call's
stored result type and is available only on its normal completion. This one schema applies to
initializers, copy/move calls, allocators, deallocators, and destructors.

`INI-EVL-001`: Every evaluation or storage-initialization order is qualified by the exact
`InitializationPath` of the operation it orders. Its role list is a duplicate-free bijection onto
that operation's endpoint occurrences requiring runtime evaluation or onto its subobjects, and it
preserves the language-defined order. Call orders cover target, receiver, and parameter roles;
registered orders cover schema operand keys; transfer orders cover the source and any pre-existing
physical destination, while a plan-result destination is the instruction result rather than an
operand; aggregate orders separately cover source evaluation and storage initialization; allocation
orders cover provider and payload. Nested operations keep their own qualified orders. Bare input
IDs, slot positions, or map iteration cannot act as a cross-operation order.

`INI-EXE-001`: Replaying an exit starts from the exact `entryState`. A completion checkpoint records
the replay boundary and the state reached there; every derived required subobject is `Initialized` in
that checkpoint state. Every state in the proof has the same domains: exactly the reachable
subobject keys, allocation-object IDs, and plan-storage IDs. Each transition changes only its named
cell. Every normal exit has exactly one such checkpoint. An exceptional exit may
have one only when the failure occurs after initialization completed. The exit's stored state equals
the state after all its transitions, including output moves and ownership transfer. A successful
operation that can return has exactly one `NormalInitializationExit`; its exceptional-exit domain
equals its executable call/registered/allocation/transfer failure channels. A recovery-only plan may
have no executable exit.

`INI-EXE-002`: State transitions obey this closed relation:

- `BeginSubobjectInitialization`: `Uninitialized -> Initializing`;
- `CompleteSubobjectInitialization`: `Initializing -> Initialized`;
- `MoveFromSubobject`: `Initialized -> MovedFrom`;
- `DelegateObjectInitialization`: `Initializing -> Initialized`, with the declared partial-entry map
  and nested state projection proving every newly completed subobject;
- recovery: `Uninitialized | Initializing -> InitializationError`;
- destruction: `Initialized | MovedFrom -> Destroyed`;
- allocation: `AllocationNotAcquired -> AllocationOwnedByPlan`, then exactly one of
  `AllocationTransferredToResult` or `AllocationReleased`; and
- plan storage: `PlanStorageNotCreated -> PlanStorageLive -> PlanStorageLifetimeEnded`.

No constructor admits any other before/after pair. Endpoints in a cause equal the transition key,
and each callable/registered/transfer cause resolves its complete executable subplan.

`INI-EXE-003`: `nestedExecutions` is exactly the set of nested initialization-plan IDs reachable
from the operation, endpoint mappings, transfers, and allocation payload. Each map key equals the
composition's operation path. `stateProjection` maps every nested subobject,
allocation-ownership cell, and plan-storage-lifetime cell exposed to the parent to its unique parent
cell; internal cells must reach their closed state inside the nested exit instead. `exitProjection`
has exactly the nested exit domain. Replay expands the nested transitions at that operation point,
projects the selected exit state, and runs the nested exit's cleanup before continuing the parent
path. Parent cleanup cannot duplicate an obligation owned by the nested plan. This composition,
rather than a pair of optimistic begin/complete markers, is the proof that a nested plan initialized
its parent subobject.

`INI-CLN-001`: `cleanupByExit` has exactly the same key domain as `exits`, including the normal exit.
Each cleanup entry starts at that exit proof's state, replays its step transitions, and ends at its
stored final state. Its steps are the exact obligations derived from initialized or moved-from
subobjects, plan-owned allocations, and live plan storage at that exit. A destruction call or
registered destructor has an endpoint map naming the exact subobject; a deallocator map names the
exact allocation handle/storage. Each stored transition must be respectively the matching
subobject-to-`Destroyed`, owned-allocation-to-`AllocationReleased`, or live-storage-to-lifetime-ended
constructor with identical keys and executable plan IDs. On a completed normal exit, requested
storage and produced values/handles transfer to the enclosing owner and are not cleanup obligations;
on an exceptional pre-completion exit, any partially constructed target still owned by the plan has
the exact destruction obligations required by its initialization contract. `MovedFrom` is not
silently treated as either `Initialized` or
already destroyed: the type's destruction rule determines whether its explicit destructor step is
required. Owned allocations are released exactly once; transferred allocations are never released
by the plan. Every live plan storage lifetime ends exactly once after any required destruction.
Every destruction step carries its complete `DestructionExecutionAt<S>` and its semantic uses occur
in the enclosing plan exactly once; cleanup never reselects a destructor or its effects from the
subobject type.

`INI-ALC-001`: An allocation plan satisfies `id = ContentId(key)` and
`object.id = ContentId(object.key)`. Its provider is a complete callable or registered execution.
`result.providerResult` is exactly that execution's result endpoint; `projectionRule` derives both
the owning `AllocationHandle` and `AllocationObjectStorage` for the same object. The storage shape's
value type is `object.key.allocatedType`, which equals the enclosing request's explicit target. The
handle type equals that request's produce-value goal. The storage alias provenance is
`ExactAliasRoot(StableAliasRegionIdentity(ContentIdentity(object.id)))`, and its
access, address space, and lifetime satisfy the payload target. The cleanup is likewise a complete
call/registered execution whose operands map that same handle/storage. Provider success performs the
ownership-acquire transition; payload initialization targets the allocated storage; returning the
handle transfers ownership; every other acquired exit has one cleanup transition. Allocation handle,
object storage, and initialized payload value are distinct endpoints and cannot be reconstructed from
one opaque allocator result during lowering. Handle/storage endpoints refer to `AllocationObjectId`,
not the enclosing `AllocationPlanId`; a deallocator call plan can therefore map those endpoints
without creating a recursive content-hash equation for the allocation plan.

## Form-specific strategy rules

`INI-FRM-001`: `CopyFromExpression` admits only implicit expression-conversion/initializer edges and
copy/move strategies declared usable for copy initialization. An explicit-only initializer or
conversion is rejected with its exact reason.

`INI-FRM-002`: `ExplicitSingle` enumerates all registered explicit conversion and single-input
initializer strategies in one candidate set. `T(e)` and `(T)e` therefore use the same strategy and
rank relation. Equal request keys select the same `InitializationPlanId`; separately written
occurrences retain distinct bound input IDs and may therefore have occurrence-specific plan IDs.
The surface syntax alone contributes no candidate and chooses no preference.

`INI-FRM-003`: `DirectArguments` enumerates declared, synthesized, witness-provided, aggregate, and
standard strategies admitted by the target model. Argument mapping occurs before conversions;
strategy comparison is proof-carrying and independent of enumeration order.

`INI-FRM-004`: `InitializerListElements` is target-directed. `{}` is an explicit request for value/default
initialization under the target model. It is not equivalent to no initializer unless a named
site/version rule says so.

`INI-FRM-005`: `OmittedDecl` is decided by `InitializationSite`. Local `let`, local `var`,
field, global/static, parameter, and synthesized storage have separate registered policies. The
policy returns a plan or an explicit `OmittedInitializationNotPermitted`; target backend defaults
and command-line zeroing options do not silently define source semantics.

`INI-FRM-006`: The legacy `(Struct)0` to empty aggregate initialization rewrite is not a core rule.
If retained in a compatibility dialect, one rule ID records the exact target eligibility, literal
spelling/value, warning, and produced empty-brace plan. It never participates in ordinary modern
conversion search.

`INI-FRM-007`: `RequestedDefault` enumerates the target model's registered default/value
initialization strategies with zero source inputs. The compatibility profile that equates `T()`
with an empty initializer list gives those two source forms the same candidate set and comparison
relation, while preserving their distinct origins. Neither is equivalent to
`OmittedDecl`.

`INI-FRM-008`: `AllocatingArguments` first selects the allocation strategy and then nests the
zero-, one-, or many-input initialization form appropriate to the written arguments. Allocation
failure, destination lifetime, initialization failure, and partial cleanup remain separate plan
edges; `new T(e)` is not modeled as an ordinary `T(e)` followed by hidden allocation.

## Failure algebra

```text
InitializationPathStep =
    SourceInputStep(input: InitializationInputId)
  | AggregateSlotStep(slot: AggregateSlotKey)
  | ConstructorParameterStep(parameter: ParameterKey)
  | DefaultMemberStep(recipe: DefaultMemberRecipeId)
  | AllocationPayloadStep
  | ResultTransferStep

InitializationPath = {
    request: InitializationRequestId,
    steps: NodeList<InitializationPathStep>
}

InitializationFailure =
    MissingTargetType
  | FormNotPermitted(form: InitializationForm,
                     target: TypeId,
                     site: InitializationSite)
  | NoInitializationStrategy(target: TypeId, form: InitializationForm)
  | ConstructorOverloadFailure(result: OverloadResult)
  | ExplicitConversionFailure(failure: ConversionFailure)
  | AggregateNotEligible(reason: AggregateEligibilityFailure)
  | TooManyElements(inputs: NodeList<InitializationInputId>)
  | MissingRequiredSlot(path: InitializationPath, slot: AggregateSlotKey)
  | DuplicateSlot(path: InitializationPath, slot: AggregateSlotKey)
  | UnknownDesignator(path: InitializationPath, name: Name)
  | ElementFailure(path: InitializationPath, nested: InitializationFailure)
  | DefaultInitializationUnavailable(path: InitializationPath, type: TypeId)
  | InaccessibleInitializationMember(declaration: DeclId,
                                     decision: VisibilityDecision)
  | InvalidInitializationDestination(actual: StorageRef)
  | CopyOrMoveUnavailable(source: TypeId, target: TypeId)
  | RecursiveInitialization(cycle: NonEmpty<QueryKey>)
  | DefiniteInitializationFailure(path: InitializationPath,
                                  state: InitializationState)
  | OmittedInitializationNotPermitted(site: InitializationSite)
  | AmbiguousInitialization(candidates: NonEmpty<InitializationStrategy>)
```

Every failure retains a target/path and source origins through its enclosing result/trace. Recovery
does not make an unavailable strategy applicable.

`INI-FAL-001`: The empty `InitializationPath` denotes its request root. Each appended step names a
semantic child role that exists in the preceding request or selected nested plan; path construction
never uses a rendered field name, source-list position, storage offset, or traversal ordinal. Paths
compare structurally and are extended immutably, so diagnostics can render them without rerunning
aggregate mapping, argument mapping, or plan selection.

## Definite initialization

`INI-DEF-001`: Reading a subobject requires `Initialized`. Initializing a `const` subobject is
permitted exactly once and is distinct from assignment. A move changes the source state according
to its type's transfer contract.

`INI-DEF-002`: Every normal exit from an initializer proves all required target subobjects
initialized. Delegation begins from the declared partial state and cannot double-initialize a slot.
Every exit executes exactly its `cleanupByExit` entry. Destruction is permitted only from the
recorded `Initialized` or `MovedFrom` state and must follow the type's exact destruction contract;
exceptional cleanup cannot infer obligations from source order or from a final boolean.

`INI-DEF-003`: Control-flow joins use the declared finite initialization-state lattice. A normal
join cannot claim a field initialized unless every incoming normal path initializes it; recovery
states remain error-tagged and do not establish definite initialization.

`INI-DEF-004`: `InitializationSubobjectKey` is the sole definite-initialization key family.
Aggregate checking projects an `AggregateSlotKey` to
`AggregateSlotInitializationSubobject(shape, slot)`; nominal fields and class bases use declaration
identity. `PlanStorageInitializationSubobject(storage)` tracks compiler-owned construction storage
through initialization, result extraction, and cleanup; allocated payloads use
`AllocatedObjectInitializationSubobject(object)`. The root key records whole-object/delegation state.
Storage offsets, declaration order, rendered names, and deprecated concrete struct bases cannot act
as subobject identity.

## IRReady and IR lowering

Lowering consumes a validated plan directly:

1. follow each operation-qualified evaluation order and evaluate each mapped endpoint exactly once;
2. obtain the requested storage and explicitly create every owner-plan/allocation storage endpoint;
3. execute calls, registered operations, transfers, and nested plans using their stored mappings;
4. replay the selected exit to its completion checkpoint and perform the explicit output transfer;
   and
5. select the exact `InitializationExitKey` and execute that exit's cleanup, including normal-exit
   destruction/lifetime obligations.

The IRReady form is a closed plan-step sum. Frontend IR emits actual codebase instructions and
attaches a stage-free initialization plan to each emitted instruction; it does not invent
initialization opcodes:

```text
InitializationRuntimeOperandRole =
    TransferSourceOperand(operation: InitializationPath)
  | TransferDestinationOperand(operation: InitializationPath)
  | ConstructorCallOperand(call: ConstructorCallPlanId,
                              role: ConstructorCallOperandRole)
  | RegisteredInitializationOperand(
        execution: RegisteredInitializationExecutionId<Published>,
        operand: RegisteredInitializationOperandKey)
  | AggregateInitializationOperand(operation: InitializationPath,
                                   slot: AggregateSlotKey)
  | InitializationNestedResultOperand(path: InitializationPath)
  | AllocationProviderResultOperand(allocation: AllocationPlanId<Published>)
  | InitializationCleanupOperand(exit: InitializationExitKey,
                                 ordinal: UInt32)

IRReadyInitializationPlanStep =
    CreatePlanInitializationStorageStep(storage: PlanInitializationStorageId)
  | TransferInitializationStep(operation: InitializationPath)
  | ConstructorCallInitializationStep(call: ConstructorCallPlanId<Published>,
                                      callRegion: NodeId<IRReady>)
  | AggregateInitializationStep(operation: InitializationPath,
                                shape: AggregateInitializationShapeId)
  | RegisteredInitializationStep(
        execution: RegisteredInitializationExecutionId<Published>)
  | AllocationInitializationStep(allocation: AllocationPlanId<Published>)
  | CleanupInitializationStep(exit: InitializationExitKey, ordinal: UInt32)
  | RecoveryInitializationStep(error: ErrorId)

IRReadyInitialization = {
    plan: InitializationPlanId,
    step: IRReadyInitializationPlanStep,
    operands:
        CanonicallyOrderedMap<InitializationRuntimeOperandRole, IRReadyValueId>,
    results: NodeList<IRReadyValueShape>
}

InitializationInstOperandLayout =
    CanonicallyOrderedMap<InitializationRuntimeOperandRole,
                          NonEmpty<NodeList<UInt32>>>

InitializationEmissionPlanStep =
    CreatePlanInitializationStorageEmission(
        storage: PlanInitializationStorageId)
  | TransferInitializationEmission(operation: InitializationPath)
  | ConstructorCallInitializationEmission(call: ConstructorCallPlanId<Published>)
  | AggregateInitializationEmission(operation: InitializationPath,
                                    shape: AggregateInitializationShapeId)
  | RegisteredInitializationEmission(
        execution: RegisteredInitializationExecutionId<Published>)
  | AllocationInitializationEmission(allocation: AllocationPlanId<Published>)
  | CleanupInitializationEmission(exit: InitializationExitKey, ordinal: UInt32)

InitializationInstSemanticPlan = {
    plan: InitializationPlanId,
    step: InitializationEmissionPlanStep,
    emissionOrdinal: UInt32,
    emissionCount: UInt32,
    operandLayout: InitializationInstOperandLayout
}
```

`INI-IR-001`: The `IRReadyAST` has distinct closed plan steps for plan-storage creation, transfer,
constructor call, aggregate construction, registered execution, allocation, and cleanup. These are
operational plans, not source strategies. `IRReadyExpr.Initialize` contains
`IRReadyInitialization`. Each emitted `IRInst` carries `InitializationInstSemanticPlan` in the
`IRInstSemanticMetadata` sidecar, and `selectedIROp(plan)` equals that instruction's actual generated
`IROp`. A generic `Construct` node, default/strategy flag, optional nested plan that lowering
reinterprets, or invented initialization opcode is forbidden. Recovery is the explicitly
tooling-only IRReady plan step governed by `INI-IR-006`.

`INI-IR-002`: Direct-to-destination initialization preserves the physical destination identity.
Lowering cannot construct a value, assign it later, and thereby change copy/move, aliasing,
lifetime, or exceptional-cleanup semantics unless the selected plan explicitly requires that
temporary.

`INI-IR-003`: Aggregate IR uses semantic slot keys and the plan's two operation-qualified orders.
Layout lowering may map slot keys to offsets only after semantic initialization is fixed;
declaration/storage position never substitutes for `AggregateSlotKey` in the frontend. Call,
registered, transfer, and allocation lowering likewise follow their own qualified operand orders.

`INI-IR-004`: Lowering executes one `CreatePlanInitializationStorageStep` for each plan-storage entry before
its first use. It returns an IR-ready physical storage whose value type, access, physical address space,
lifetime, alias provenance, and empty physical-source provenance are derived from the entry; it is
`ExactAliasRoot(StableAliasRegionIdentity(ContentIdentity(storage.id)))` for an independently
created plan-owned entry. The
corresponding actual-instruction emission returns
`PhysicalStorageValueShape(IRPhysicalStorageShape{...})` with exactly the same value type, access,
mutability, address space, lifetime, alias provenance, and source provenance. Allocation storage uses the same lossless
shape with
`ExactAliasRoot(StableAliasRegionIdentity(ContentIdentity(allocation.key.object.id)))`. A supplied destination emits no
creation operation and retains its incoming physical-storage value and shape; an internal request
destination reuses the storage/projection operation emitted once by its owning plan.
For a `TemporaryInitializationPlanApplicationAt<Published>`, chapter 11's
`MaterializeTemporaryInstPlan` is the one lowering of its destination's `CreatePlanStorage`
transition; no second create operation is emitted. Every internal endpoint rooted at that
destination uses `ExactAliasRoot(temporaryStorageAliasRoot(application.identity))`, exactly matching
the materialized temporary, rather than the independent plan-storage alias above. The plan's
initialization instructions retain the complete internal physical endpoint while the enclosing
access plan exposes only the opaque temporary-storage value, so this projection cannot make the
temporary available to source-level physical-storage or address-space rules.

`INI-IR-005`: Every successful IRReady initialization node resolves exactly one component of its plan:
a transfer operation path, call-plan ID, aggregate operation/shape, registered-execution ID,
allocation-plan ID, storage ID, or exit/cleanup ordinal. Its operand-map domain is exactly that
component's mapped runtime roles. An initializer-call target equals the call region's
`IRReadyCallInputs.initializationTarget`; returned-value completion is a separate transfer whose source
equals the call region's normal result. A physical transfer destination is an operand; an
`InitializationPlanResultEndpoint` is represented by the transfer instruction's result and cannot
also appear as `TransferDestinationOperand`. Cleanup nodes follow the selected exit's stored steps. The
result list is empty for cleanup and for an operation that only initializes an existing physical
destination. `CreatePlanInitializationStorageStep` has exactly one lossless physical-storage result. A
transfer to `InitializationPlanResultEndpoint` has exactly one value result. Allocation projection
produces one `RuntimeValueShape(handle.handleType)` endpoint and one lossless physical-storage
endpoint for its object; the eventual allocation-expression result is the handle. Every other
component has exactly its declared endpoint shapes, and non-allocation value results have
`targetType`.

The lowering rule for that component declares a nonempty sequence of actual `IROp` values. The
sidecar entries for the sequence have the same `plan` and `step`, have
`emissionCount > 0`, and their `emissionOrdinal` values are a bijection onto
`0 .. emissionCount-1`. Each entry's `selectedIROp(plan)` equals its instruction opcode. A
constructor-call emission is an `IRCall` and also has complete `call` metadata; a registered
emission uses the opcode resolved from its `RegisteredInitializationExecutionAt<Published>`.
Aggregate, allocation, transfer, and cleanup recipes may use multiple existing instructions but
cannot collapse the recipe into an invented aggregate or initialization opcode. Across the recipe,
the operand-layout domain covers every mapped runtime role and no other role. Each role's IRReady
producer is evaluated exactly once in its operation-qualified evaluation order; subsequent layout
occurrences reuse that SSA value, and their multiplicity must equal the declared emission recipe.
Every occurrence preserves its physical-storage shape. Neither IRReady nor IR consults
`InitializationStrategy`. Every emitted successful initialization instruction contributes the
exact `InitializationPlanDependency(plan)` required by chapter 11; canonical dependency-map merging
prevents a multi-instruction recipe from creating distinct authorities.

`INI-IR-006`: `InitializationRecovery(error)` and `RecoveryInitializationStep(error)` exist only so
diagnostic/tooling elaboration remains structurally total. They do not lower to
`InitializationInstSemanticPlan`, do not contribute `InitializationPlanDependency`, and cannot
appear in a publishable frontend-IR fragment. Under chapter 11's `IR-005`, tooling lowering emits
the existing `IRPoison` opcode with `recoveryError = Some(error)` instead. Thus an
initialization-plan dependency always
resolves an applicable `Selected` winner, never a recovered plan whose operation would need to be
reinterpreted as successful code.

## Validation obligations and freeze decisions

Unit/property suites cover every form × strategy × admissible-rank-detail × goal combination;
physical versus abstract endpoints; all aggregate binding/missing/nesting policies; executable
copy/move/registered/call mappings and qualified orders; initializer overloads;
generic/witness-provided initializers; allocation object/storage/handle ownership; legal and illegal
state transitions; nested state/exit composition; normal/exceptional/moved-from cleanup; lossless
physical-storage IR shapes; mutation of each target-compatibility proof endpoint, including a
correct access proof paired with the wrong `AddressSpaceAdmissionProof`; registered initialization
selection with independent ordinary capability use and concrete availability (including explicit
true availability); capability-selection merge/replay; recovery-tooling rejection; and
serialization/lowering replay.

Before schema freeze, chapter 12 must choose per language version:

- omitted local/field/global initialization and zero-initialization options;
- which type definitions admit nominal, aggregate, extension, and synthesized strategies;
- partial and flattened brace policy;
- copy/move eligibility and explicitness;
- the legacy `(Struct)0` rule; and
- throwing/delegating initializer cleanup.

Those choices populate `InitializationModel` and registered site policies; they do not change the
algebra in this chapter.
