# Expressions, statements, and constant evaluation

Expression checking is a bidirectional transformation from bound syntax to immutable typed syntax.
Statement checking carries an explicit control context and produces typed statements plus flow
facts. Neither operation mutates its input or a surrounding declaration.

## Main judgments

```text
P; Σ; Γ; Δ; κ ⊢ e ⇑ expected ⇝ e' :: c ! ε ▷ D
P; Σ; Γ; Δ; C; κ ⊢ s ⇝ s' ! ε ⇒ F ▷ D
```

`expected` is `NoExpectation` or an `ExpectedType` with a coercion site and origin. `ε` is an effect
set. `c` is the expression's `Classifier`; `e' : τ @ q` is the value-only shorthand for
`e' :: ValueClassifier(τ, q)`. `F` is a flow summary. Capabilities directly used by a node are
recorded alongside its typed result and later accumulated by chapter 9.

```text
ExpectedType = {
    type: TypeId,
    site: Assignment | Argument | Return | Initializer | ExplicitCast | Pattern,
    strength: Hint | Required,
    origin: Origin
}

ReceiverContext = {
    declaration: CanonicalDeclRef,
    selfType: TypeId,
    mode: PassingMode,
    category: ValueCategory,
    origin: Origin
}

ExpressionCheckContext = {
    scope: ScopeId,
    expected: Option<ExpectedType>,
    receiver: Option<ReceiverContext>,
    genericEnvironment: GenericEnvironmentId,
    semanticUseOwner: CanonicalDeclRef,
    accessContext: AccessContext,
    availableEffects: EffectAllowance,
    evaluationLifetime: LifetimeId,
    contractSelection: ContractSelectionContext,
    semanticEnvironment: SemanticEnvironmentId
}

ExpressionCheckContextId = ContentId<ExpressionCheckContext>
```

A hint may guide literal, lambda, initializer, or overload inference but cannot make an otherwise
invalid expression valid. A required expectation applies an implicit conversion after intrinsic
checking.

`EXP-CHK-001`: Every successful/recovered expression result contains a classifier, effects, direct
capability uses, and origin. A value category exists exactly when the classifier is
`ValueClassifier`. There is no `checked` bit.

`EXP-CHK-002`: Checking the same bound node under distinct expected types uses distinct query keys.
Context-dependent results cannot overwrite each other on the input node.

`EXP-CHK-003`: `contractSelectionContext(c) = c.contractSelection`, and
`worldAssumption(c) = c.contractSelection.assumption`. The optional concrete world and symbolic
branch assumption are independent fields of that one context value and of the expression query
key; an accessor, operator, conversion, initializer, or ordinary call cannot obtain either from
ambient mutable target state.

`EXP-CHK-004`: `ExpressionCheckContext.evaluationLifetime` is the minimum lifetime required merely
to produce and consume a value in that expression context. It is derived from lexical/control
context and is part of the query key. Reference formation may preserve a longer source lifetime,
but it cannot accept an endpoint that expires before this lifetime or replace it with a lifetime
inferred from an expected parameter mode.

`EXP-CHK-005`: `semanticUseOwner` is the declaration whose direct effect/capability-use graphs own
operations selected while checking this expression. Every use key constructed for the result has
this owner. Child contexts preserve it unless a named declaration-body boundary constructs a new
context; a top-level or synthesized evaluation first creates an explicit synthetic owner. Candidate
plans therefore cannot discover an ambient owner or re-key a selected use during aggregation.

## Error propagation

```text
Γ ⊢ e ⇝ ErrorExpr(eid) :: ErrorClassifier(eid, UnknownRecovery)
------------------------------------------------ EXP-ERR-001
Γ ⊢ parent(e) ⇝ recoveredParent(eid)
```

Rules inspect the root `ErrorId` and avoid diagnostics whose only failed premise is that recovery
value. Independent children and side conditions continue checking. Error compatibility used for
recovery has no witness and no favorable conversion rank.

`EXP-ERR-002`: A rule that cannot construct its ordinary typed node constructs the node-family's
`Error` alternative with the strongest known type and all checked children. It does not return the
unchanged bound node with a mutated error type.

## Literals

Literal checking is split into decoding and contextual typing:

```text
DecodeLiteral(token) -> LiteralValue | LiteralFailure
ChooseLiteralType(value, suffix, expected, Σ) -> TypeId
```

An explicit suffix selects a standard-environment literal type or reports an unsupported suffix.
Without a suffix, an expected compatible scalar type may be selected under its literal-conversion
rule; otherwise language-version defaults apply. Range checking uses arbitrary-precision decoded
values before conversion to the selected type.

```text
decode(tok) = v    chooseType(v, suffix(tok), expected, Σ) = τ
---------------------------------------------------------------- EXP-LIT-001
Γ ⊢ tok ⇝ Literal(v, τ, origin(tok)) : τ @ RValue
```

Adjacent string tokens form `ConcatenatedString` with one child per token. Character literals remain
distinct from strings even if their decoded payload is one scalar.

## Names and declaration references

Binding has already produced a `BoundName`:

```text
BoundName = Resolved(use)    typeOf(use.target) = (τ,q)
------------------------------------------------------ EXP-NAME-001
Γ ⊢ BoundName ⇝ DeclUseExpr(use) : τ @ q
```

An overload set checks to `OverloadClassifier` only in a context that will resolve it, such as a call,
explicit function-value conversion, or generic application. Using it as an ordinary value produces
an ambiguity/no-context diagnostic.

The decl-ref retains its lookup path. Selected member paths are elaborated after overload selection
so implicit receiver, base conversion, and dereference behavior is not duplicated for every
candidate.

## `this` and type-level `This`

The surrounding checked callable supplies an explicit receiver:

```text
currentFunction(Γ).receiver = Receiver(selfType=τ, mode=m, ...)
---------------------------------------------------------------- EXP-THIS-001
Γ ⊢ this ⇝ ReceiverExpr(function, m) : τ @ receiverCategory(m)
```

Static/free functions have `NoReceiver`; `this` is rejected. A nested lambda captures the receiver
under the lambda capture rules instead of discovering a parent declaration during lowering.

## Parameter uses and physical reference formals

`EXP-PAR-001`: Resolving a parameter or receiver whose checked mode is `ConstRefMode(r)` constructs
one `PhysicalStorageRef` rooted at the exact `ConstRefFormalRoot(signature, role)`. Its value type is
the substituted formal value type; its access is `ReadAccess`; its mutability is
`UnknownMutability`; its lifetime is `CallableActivationLifetime(signature)`; and its alias is
`UnknownAliasRoot`. Its symbolic address space and typed source-provenance facts come from the exact
`PhysicalFormalEntryProof` for that signature/role. The name expression is classified as
`Place(PhysicalPlace(storage))`. Read-only access is a view restriction, not a claim that the
caller's underlying location is immutable.

`EXP-PAR-002`: A `RefMode(r)` formal analogously constructs `PhysicalPlace` rooted at
`RefFormalRoot(signature, role)`, with `ReadWriteAccess`, `Mutable`, activation lifetime, unknown
alias, and the checked formal entry's address/source evidence. A `ConstRefMode` formal supports
loads and ordinary proof-carrying physical projections but cannot be written, passed to
`OutMode`/`InOutMode`/`RefMode`, or escape its activation. A `RefMode` formal permits operations
proved by its read/write view. A property reached through either physical receiver still produces
its ordinary `AbstractPlace`; it does not expose the receiver location as the property's storage.

`EXP-PAR-003`: Stored-field, builtin-element, vector-element, dereference, and registered projection
rules applied to a physical formal use the same ordinary physical-projection applications as any
other `PhysicalPlace`. They preserve the formal lifetime/access/source ceilings unless a registered
rule proves an exact refinement. There is no borrowed-place classifier, borrowed projection
application, or target-dependent borrowed-storage category.

`This` in type position resolves to the current aggregate nominal type, extension target type, or
interface-bound `SelfType`, as established when building the surrounding declaration header. The
type checker does not walk declaration parents to calculate it ad hoc.

## Type expressions

```text
Γ; Δ ⊢ te ⇝ TypeExpr(τ) :: TypeKind
```

Identifier/member/generic applications at type level use the same bound declaration identities and
substitution algebra as value expressions, but their classifier is a kind. Array counts and generic
value arguments invoke constant evaluation. Intersection types use the canonical set rules in
chapter 4.

`TYP-EXPR-001`: A value-classified term in required type position produces `expected-type`; a
type-classified term in ordinary value position produces `expected-value`. No `TypeType` coercion
hides the category error.

## Places, loads, and assignment

Name, stored-field, builtin-element, dereference, and registered physical-projection rules may
produce `PhysicalPlace`. Properties, declared subscripts, multi-element swizzles, and other
getter/setter projections produce `AbstractPlace`. Reading either in value context inserts an
explicit load/accessor plan during elaboration. Preserving a place for assignment, `out`, or
`inout` does not by itself make abstract storage physical. `__constref` and `__ref` require a
physical endpoint and never turn an ordinary value/getter result into storage through a temporary.

```text
Γ ⊢ lhs ⇝ l : τ @ Place(place)
Γ ⊢ rhs ⇑ Required(τ, Assignment) ⇝ r : τ @ q
writable(effectiveAccess(place))
PlanCoercion(ConversionRequest(r, τ, q, τ, Assignment, Implicit,
                               conversionEnvironment(context(Γ)))) = Applicable(c, rank)
w = WriteValueAccessAt<S>(source = r, conversion = c,
                          completion = OnNormalCompletion)
PlanStorageAccessAt<S>(StorageAccessRequestAt<S>(
    stable child of assignment with role StorageWrite,
    physical projection site of assignment with role StorageWrite,
    l, WriteValueAccess(w), context(Γ))) = PlannedStorageAccess(p)
------------------------------------------------ EXP-ASN-001
Γ ⊢ lhs = rhs ⇝ Assign(l, r, p) : τ @ RValue
```

The required RHS check makes `r` the already coerced value, so the displayed `PlanCoercion` is the
canonical identity plan at the storage boundary; the implicit source conversion remains explicit
inside `r`. Other write-producing language forms may supply a non-identity `c`, but they use the same
payload-complete request and never ask the storage planner to rediscover it.

Assignment to immutable storage, a temporary, a non-writable swizzle, or an inaccessible accessor
has distinct structured failures. Compound assignment binds and resolves its operator exactly once,
then elaborates read/operation/write-back with a single evaluation of the left side.

`EXP-PLC-001`: Place paths preserve single-evaluation semantics. An elaboration may materialize a
temporary but cannot clone a side-effecting base/index expression.

`EXP-PLC-002`: `isPhysicalStorage` is derived from the `PlaceRef` alternative. Assignment and
write-back may target an `AbstractPlace` through a setter plan, but physical-operand argument passing and fresh
initialization storage require `PhysicalPlace` and the proof defined in chapter 4. A setter does not
manufacture that proof. A mode-specific reference accessor may instead be invoked and explicitly
dereferenced to construct a distinct physical endpoint under `EXP-REF-004`.

## Member and subscript expressions

Member checking requests `LookupMember` on the checked base classifier. A single non-callable
candidate can be selected immediately; overloadable candidates remain an overload set with a
receiver path. Subscript syntax first considers declared subscript members and standard-environment
indexing primitives. A declared property/subscript yields `AbstractPlace` from its accessor
contract; a builtin/registered indexing primitive yields `PhysicalPlace` only when its rule proves
a stable endpoint.

`EXP-MEM-001`: A selected member expression contains the normalized decl-ref, chosen lookup path,
checked base, substituted member type, and resulting place/value category.

`EXP-MEM-002`: Explicit syntax may produce a first-class reference value from a
property/subscript reference accessor. Separately, physical-parameter planning may select the exact
access-indexed accessor and immediately dereference its result to a new `PhysicalPlace`. This
implicit operation exists only inside `ParameterReferenceAccessorPlanAt<S>` and never exposes the
handle or reclassifies the original abstract place. Ordinary read/write fallbacks remain separately
authorized storage-access plans.

`EXP-MEM-003`: Checking a property or declared subscript constructs one `AbstractStorageRef` whose
`capturedSources` contains the already checked receiver and source-index arguments. Its projection
stores only the selected property/subscript identity. The capture map/order follows `TYP-PLC-005`
and `TYP-PLC-006`, and getter/setter/reference-accessor plans must all consume that same value. Merely
forming the abstract place invokes no accessor and evaluates no captured runtime expression a
second time.

`EXP-MEM-004`: `PlanStorageAccessAt<S>` is total over `StorageAccessIntentAt<S>`. `ReadValueAccess`
uses a getter when present and may use a ref-accessor call plus explicit internal dereference only
under the named language fallback. `WriteValueAccess` carries the already checked source,
conversion, and completion condition and analogously uses a setter before its named ref-accessor
fallback. Parameter-mode planning is not a storage-access intent; chapter 7's `PlanArgumentAccess`
owns the parameter type, structural domain/access mode, adaptation, invocation environment,
abstract-mode materialization/write-back, or `PhysicalParameterBindingProofAt<S>`. Explicit reference
formation is likewise not a storage-access intent: it uses `CheckReferenceFormationAt<S>` and a
written `ReferenceFormationRequest`.
No boolean “aggressive address” flag or fallback order shared across these operations is permitted.

`EXP-MEM-005`: A registered member/subscript can produce `PhysicalPlace` only through
`ValidateRegisteredPhysicalProjectionAt<S>`. The request contains the exact checked base and index
expressions; a success stores one `RegisteredPhysicalProjectionApplicationAt<S>` on the typed
projection expression. It first requires
`ValidatePhysicalProjectionSite(request.id, request.site) = Success(Unit)`. Its
`runtimeOperands` domain is the registered endpoint schema, with at
most one `PhysicalProjectionBaseOperand` and dense
`PhysicalProjectionIndexOperand(0..n-1)` roles. `evaluationOrder` is a duplicate-free bijection
onto that domain and preserves written base-then-index source order. Each entry retains the
executable `TypedExpr` and complete `AccessPlan<S>` that produces its registered runtime endpoint,
whose terminal is `PassArgument`; neither checking nor lowering may reconstruct an operand from
`PhysicalPlacePath` or substitute a standalone storage terminal.

The application stores `site = request.site`, and its identity is
`registeredPhysicalProjectionIdentity(site.site)`; `request.id` remains only typed-node provenance.
Its output proof satisfies the standard-environment schema in
`registration.environment` with exactly `registration.staticInputs` and those runtime endpoints:
`output.outputTypeEquality` has endpoints
`(output.registeredResultType, output.storage.valueType)`, and
`output.storage.path = RegisteredPhysicalProjection(identity)`. The proof's access, lifetime,
address-space, mutability, alias, and source-provenance derivations are exact; in particular,
`output.sourceProvenance.result = output.storage.sourceProvenance`. Each derivation's source is a
registered schema value, one named runtime operand, or a named nonempty operand meet and replays the
exact registered component rule; no output component is copied from the checking context. The
typed expression is
classified as `Place(PhysicalPlace(output.storage))`; a bare registration, a same-typed result, or
an old `(rule, basePath, staticInputs)` tuple cannot manufacture that category. Control is one
physical result, no successor, and nonthrowing; a throwing registered surface is a call instead.

`EXP-MEM-006`: An expected physical mode does not change intrinsic member/subscript checking. A
stored field, registered physical projection, builtin physical subscript, or explicit dereference
may remain `PhysicalPlace` and qualify directly. A property or declared subscript remains
`AbstractPlace`; chapter 7 may select only its exact `referenceAccessors[mode.access]` entry and the
dedicated invocation/dereference plan. Getter/setter availability, ordinary read fallback, value
conversion, and temporary materialization are irrelevant to this selection. The original property
remains abstract in the selected typed call.
Selection effects/capabilities and every operand-plan use form the stored `semanticUses` exactly
once. This intrinsic result proof deliberately is not a `PhysicalStorageProof`: a later read,
write, `Ref`, initialization, or address operation calls `provePhysicalStorage` with its own
`PhysicalStorageRequirement`. Consequently the projection's identity and classifier do not depend
on a later use-specific access, lifetime, or address-space requirement.

Swizzle/member syntax is represented as a declared or primitive member plan. Writeability and
duplicate-component restrictions are properties of that plan, not string tests scattered through
assignment and call checking.

## Reference formation and properties

A property or declared subscript denotes abstract storage even when it declares a ref accessor.
Explicit reference formation is a separately written first-class-value operation. A physical
parameter may implicitly invoke the same validated accessor surface only through its distinct
mode-specific consume-and-dereference plan; it never synthesizes explicit reference syntax.

```text
ExplicitReferenceSyntax =
    SelectedBuiltinAddressOf(registration: StandardEnvironmentRuleId,
                             staticInputs: CanonicalArguments)
  | GetAddressBuiltin
  | RegisteredReferenceSyntax(rule: StandardEnvironmentRuleId,
                              staticInputs: CanonicalArguments)

ReferenceSyntaxDirectStrategy =
    CoreAddressOfStrategy
  | RegisteredDirectReferenceStrategy(rule: StandardEnvironmentRuleId,
                                      staticInputs: CanonicalArguments)

ReferenceSyntaxAccessorStrategy =
    RejectAbstractStorage
  | InvokeAccessorResult
  | InvokeAccessorThenRegistered(
        rule: StandardEnvironmentRuleId,
        staticInputs: CanonicalArguments)

ReferenceSyntaxPolicyAt<S: WitnessUseStage> = {
    languageRule: RuleId,
    syntax: ExplicitReferenceSyntax,
    resultKind: ReferenceHandleKind,
    requirement: PhysicalStorageRequirement,
    expectedLifetimeCoverage: Option<OutlivesProof>,
    direct: ReferenceSyntaxDirectStrategy,
    accessor: ReferenceSyntaxAccessorStrategy,
    capabilities: CapabilitySelectionAt<S>
}

ReferenceSyntaxPolicy = ReferenceSyntaxPolicyAt<Published>

WriteValueAccessAt<S: WitnessUseStage> = {
    source: TypedExpr,
    conversion: ConversionPlan<S>,
    completion: CompletionCondition
}

StorageAccessIntentAt<S: WitnessUseStage> =
    ReadValueAccess
  | WriteValueAccess(WriteValueAccessAt<S>)

WriteValueAccess = WriteValueAccessAt<Published>
StorageAccessIntent = StorageAccessIntentAt<Published>

RegisteredDataOperationSelectionAt<S: WitnessUseStage> = {
    selectionEffects: EffectSet,
    effectAllowance: EffectAllowanceValidation,
    capabilities: CapabilitySelectionAt<S>
}

BuiltinPhysicalProjectionOperandRole =
    BuiltinPhysicalBaseOperand
  | BuiltinPhysicalIndexOperand

BuiltinPhysicalProjectionOperation =
    ProjectBuiltinPhysicalElement(rule: RuleId)

BuiltinPhysicalProjectionRuntimeOperandAt<S: WitnessUseStage> = {
    source: TypedExpr,
    endpointType: TypeId,
    endpointCategory: ValueCategory
}

BuiltinPhysicalProjectionControlShape =
    BinaryInputsOnePhysicalResultNoSuccessors

BuiltinPhysicalProjectionControlProof = {
    shape: BuiltinPhysicalProjectionControlShape
}

BuiltinPhysicalProjectionResultProof = {
    identity: BuiltinPhysicalProjectionIdentity,
    operation: BuiltinPhysicalProjectionOperation,
    inputStorage: PhysicalStorageRef,
    projectedType: TypeId,
    outputTypeEquality: TypeEqualityProofId,
    storage: PhysicalStorageRef
}

BuiltinPhysicalProjectionApplicationAt<S: WitnessUseStage> = {
    identity: BuiltinPhysicalProjectionIdentity,
    site: PhysicalProjectionSiteAssignment,
    operation: BuiltinPhysicalProjectionOperation,
    runtimeOperands:
        CanonicallyOrderedMap<BuiltinPhysicalProjectionOperandRole,
                              BuiltinPhysicalProjectionRuntimeOperandAt<S>>,
    evaluationOrder: NodeList<BuiltinPhysicalProjectionOperandRole>,
    output: BuiltinPhysicalProjectionResultProof,
    control: BuiltinPhysicalProjectionControlProof,
    semanticUses: PlanSemanticUses<S>
}

BuiltinPhysicalProjectionApplication =
    BuiltinPhysicalProjectionApplicationAt<Published>

BuiltinPhysicalProjectionRequest = {
    id: NodeId<Typed>,
    site: PhysicalProjectionSiteAssignment,
    operation: BuiltinPhysicalProjectionOperation,
    base: TypedExpr,
    index: TypedExpr,
    context: ExpressionCheckContextId
}

BuiltinPhysicalProjectionValidationFailure =
    BuiltinPhysicalProjectionBaseRejected(actual: ValueCategory)
  | BuiltinPhysicalProjectionIndexRejected(expected: TypeId,
                                            actual: TypeId,
                                            actualCategory: ValueCategory)
  | BuiltinPhysicalProjectionOperationRejected(
        operation: BuiltinPhysicalProjectionOperation)
  | BuiltinPhysicalProjectionOutputRejected(input: PhysicalStorageRef,
                                             output: PhysicalStorageRef)
  | BuiltinPhysicalProjectionControlRejected(
        expected: BuiltinPhysicalProjectionControlShape,
        actual: BuiltinPhysicalProjectionControlShape)

BuiltinPhysicalProjectionValidationResultAt<S: WitnessUseStage> =
    ValidBuiltinPhysicalProjection(
        application: BuiltinPhysicalProjectionApplicationAt<S>)
  | InvalidBuiltinPhysicalProjection(
        failure: BuiltinPhysicalProjectionValidationFailure)

ValidateBuiltinPhysicalProjectionAt<S>(request: BuiltinPhysicalProjectionRequest)
    -> CheckResult<BuiltinPhysicalProjectionValidationResultAt<S>>

ValidateBuiltinPhysicalProjection = ValidateBuiltinPhysicalProjectionAt<Published>

`EXP-MEM-007`: A valid builtin physical-element application has exactly the
`BuiltinPhysicalBaseOperand` and `BuiltinPhysicalIndexOperand` entries, in that written order. The
base source is classified as `Place(PhysicalPlace(output.inputStorage))`; the index has already
been checked and converted to the operation rule's index type as an `RValue`. Validation first
requires `ValidatePhysicalProjectionSite(request.id, request.site) = Success(Unit)`. The application
stores `site = request.site`, and its identity is
`builtinPhysicalProjectionIdentity(site.site)`; `request.id` remains only typed-node provenance.
Its output type and every access, mutability, lifetime, address-space, and alias
component replay the named builtin rule from the exact two endpoint values. In particular, a
dynamic index cannot acquire a fresh disjoint alias merely from its syntax identity. The output
path is exactly `BuiltinElement(output.inputStorage.path, identity)`, and the typed expression is
classified as `Place(PhysicalPlace(output.storage))`. The control proof is one nonthrowing physical
result with no successors. The complete application, not the path, is retained by the typed
projection expression.

`EXP-MEM-008`: `runtimeOperands` is the sole executable source authority for builtin physical
indexing. Each source is evaluated once in `evaluationOrder`, and all effects, conversions, and
direct capability uses enter `semanticUses` exactly once. Checking, elaboration, and lowering may
not recover the base or index from `PhysicalPlacePath`, the request node, an origin, or an
equal-typed sibling expression. Registered resource/target projections remain exclusively in
`RegisteredPhysicalProjectionApplicationAt<S>`; neither application kind can be retagged as the
other merely because both produce `PhysicalPlace`.

RegisteredPhysicalProjectionOperandRole =
    PhysicalProjectionBaseOperand
  | PhysicalProjectionIndexOperand(ordinal: UInt32)

RegisteredPhysicalProjectionRuntimeOperandAt<S: WitnessUseStage> = {
    source: TypedExpr,
    access: AccessPlan<S>,
    endpointType: TypeId,
    endpointCategory: ValueCategory
}

RegisteredPhysicalProjectionControlShape =
    RuntimeInputsOnePhysicalResultNoSuccessors(inputCount: UInt32)

RegisteredPhysicalProjectionControlProof = {
    shape: RegisteredPhysicalProjectionControlShape
}

RegisteredPhysicalProjectionComponentSource =
    RegisteredProjectionSchemaValue
  | RegisteredProjectionOperandValue(
        role: RegisteredPhysicalProjectionOperandRole)
  | RegisteredProjectionOperandMeet(
        roles: NonEmpty<RegisteredPhysicalProjectionOperandRole>)

RegisteredPhysicalProjectionAccessDerivation = {
    source: RegisteredPhysicalProjectionComponentSource,
    result: AccessMode
}

RegisteredPhysicalProjectionMutabilityDerivation = {
    source: RegisteredPhysicalProjectionComponentSource,
    result: Mutability
}

RegisteredPhysicalProjectionLifetimeDerivation = {
    source: RegisteredPhysicalProjectionComponentSource,
    result: LifetimeId
}

RegisteredPhysicalProjectionAddressSpaceDerivation = {
    source: RegisteredPhysicalProjectionComponentSource,
    result: AddressSpace
}

RegisteredPhysicalProjectionAliasDerivation = {
    source: RegisteredPhysicalProjectionComponentSource,
    result: AliasProvenance
}

RegisteredPhysicalProjectionSourceDerivation = {
    source: RegisteredPhysicalProjectionComponentSource,
    result: PhysicalStorageSourceProvenance
}

RegisteredPhysicalProjectionResultProof = {
    identity: RegisteredPhysicalProjectionIdentity,
    registration: RegisteredDataOperationRegistration,
    registeredResultType: TypeId,
    outputTypeEquality: TypeEqualityProofId,
    storage: PhysicalStorageRef,
    access: RegisteredPhysicalProjectionAccessDerivation,
    mutability: RegisteredPhysicalProjectionMutabilityDerivation,
    lifetime: RegisteredPhysicalProjectionLifetimeDerivation,
    addressSpace: RegisteredPhysicalProjectionAddressSpaceDerivation,
    alias: RegisteredPhysicalProjectionAliasDerivation,
    sourceProvenance: RegisteredPhysicalProjectionSourceDerivation
}

RegisteredPhysicalProjectionApplicationAt<S: WitnessUseStage> = {
    identity: RegisteredPhysicalProjectionIdentity,
    site: PhysicalProjectionSiteAssignment,
    registration: RegisteredDataOperationRegistration,
    runtimeOperands:
        CanonicallyOrderedMap<RegisteredPhysicalProjectionOperandRole,
                              RegisteredPhysicalProjectionRuntimeOperandAt<S>>,
    evaluationOrder: NodeList<RegisteredPhysicalProjectionOperandRole>,
    output: RegisteredPhysicalProjectionResultProof,
    selection: RegisteredDataOperationSelectionAt<S>,
    control: RegisteredPhysicalProjectionControlProof,
    semanticUses: PlanSemanticUses<S>
}

RegisteredPhysicalProjectionApplication =
    RegisteredPhysicalProjectionApplicationAt<Published>

RegisteredPhysicalProjectionRequest = {
    id: NodeId<Typed>,
    site: PhysicalProjectionSiteAssignment,
    registration: RegisteredDataOperationRegistration,
    base: Option<TypedExpr>,
    indices: NodeList<TypedExpr>,
    context: ExpressionCheckContextId
}

RegisteredPhysicalProjectionValidationFailure =
    RegisteredPhysicalProjectionRuleUnavailable(
        registration: RegisteredDataOperationRegistration)
  | RegisteredPhysicalProjectionStaticInputsRejected(
        registration: RegisteredDataOperationRegistration)
  | RegisteredPhysicalProjectionOperandDomainMismatch(
        expected: CanonicallyOrderedSet<RegisteredPhysicalProjectionOperandRole>,
        actual: CanonicallyOrderedSet<RegisteredPhysicalProjectionOperandRole>)
  | RegisteredPhysicalProjectionOperandRejected(
        role: RegisteredPhysicalProjectionOperandRole,
        expectedType: TypeId,
        actualType: TypeId,
        actualCategory: ValueCategory)
  | RegisteredPhysicalProjectionControlRejected(
        expected: RegisteredPhysicalProjectionControlShape,
        actual: RegisteredPhysicalProjectionControlShape)
  | RegisteredPhysicalProjectionOutputRejected(
        registeredType: TypeId,
        storage: PhysicalStorageRef)
  | RegisteredPhysicalProjectionEffectNotAllowed(
        required: EffectSet,
        allowance: EffectAllowance,
        excess: EffectSet)
  | RegisteredPhysicalProjectionConcreteRegionUnavailable(
        failure: CapabilityFailure)

RegisteredPhysicalProjectionValidationResultAt<S: WitnessUseStage> =
    ValidRegisteredPhysicalProjection(
        application: RegisteredPhysicalProjectionApplicationAt<S>)
  | InvalidRegisteredPhysicalProjection(
        failure: RegisteredPhysicalProjectionValidationFailure)

ReferenceFormationRequest = {
    id: NodeId<Typed>,
    syntax: ExplicitReferenceSyntax,
    operand: TypedExpr,
    context: ExpressionCheckContextId
}

ReferenceHandleTypeProjection =
    ReferenceTypeProjection(type: TypeId)
  | PointerTypeProjection(type: TypeId)

ReferenceHandleProof = {
    resultType: TypeId,
    shape: ReferenceHandleShape,
    expectedReferent: TypeId,
    referentEquality: TypeEqualityProofId,
    requirement: PhysicalStorageRequirement,
    typeProjection: ReferenceHandleTypeProjection,
    accessProof: AccessProvisionProof,
    lifetimeProof: OutlivesProof,
    addressSpaceProof: AddressSpaceAdmissionProof,
    sourceProof: PhysicalSourceProvenanceAdmissionProof
}

referenceHandleValue(p: ReferenceHandleProof) =
    ReferenceHandleValueShape(p.resultType, p.shape)

AddressSpaceEqualityProof = {
    left: AddressSpace,
    right: AddressSpace
}

AliasProvenanceEqualityProof = {
    left: AliasProvenance,
    right: AliasProvenance
}

SourceProvenanceEqualityProof = {
    left: PhysicalStorageSourceProvenance,
    right: PhysicalStorageSourceProvenance
}

MutabilityEqualityProof = {
    left: Mutability,
    right: Mutability
}

DirectStorageHandleProof = {
    handle: ReferenceHandleProof,
    storage: PhysicalStorageRef,
    sourceAccessProof: AccessProvisionProof,
    sourceMutabilityProof: MutabilityEqualityProof,
    sourceLifetimeProof: OutlivesProof,
    sourceAddressSpaceProjection: ConcreteAddressSpaceProjectionProof,
    sourceAliasProof: AliasProvenanceEqualityProof,
    sourceProvenanceProof: SourceProvenanceEqualityProof
}

AccessorReferenceResultInstantiationProof = {
    contract: AccessorReferenceResultContractId,
    invocationIdentity: AccessorInvocationIdentity,
    sources: CapturedStorageSources,
    provenanceSources: AccessorProvenanceSourceMapId,
    result: ReferenceHandleValueShape,
    addressSpaceRule: AccessorReferenceAddressSpaceRule,
    mutabilityRule: AccessorReferenceMutabilityRule,
    lifetimeRule: AccessorReferenceLifetimeRule,
    aliasRule: AccessorReferenceAliasRule,
    sourceRule: AccessorReferenceSourceRule
}

AccessorReferenceResultCertificate = {
    contract: AccessorReferenceResultContractId,
    invocationIdentity: AccessorInvocationIdentity,
    call: NodeId<Typed>,
    subject: CallableContractSubject,
    signature: CallableSignatureId,
    expectedReferent: TypeId,
    referentEquality: TypeEqualityProofId,
    result: ReferenceHandleValueShape,
    instantiation: AccessorReferenceResultInstantiationProof
}

AccessorHandleResultProof = {
    result: ReferenceHandleValueShape,
    callResultType: TypeId,
    resultEquality: TypeEqualityProofId,
    certificate: AccessorReferenceResultCertificate
}

AccessorHandleAdmissionProof = {
    raw: AccessorHandleResultProof,
    requirement: PhysicalStorageRequirement,
    admitted: ReferenceHandleProof
}

ReferenceOperationRegistration = RegisteredDataOperationRegistration

ReferenceOperationSelectionAt<S: WitnessUseStage> =
    RegisteredDataOperationSelectionAt<S>

ReferenceOperationSelection = ReferenceOperationSelectionAt<Published>

ReferenceDataOperationControlShape = UnaryInputUnaryResultNoSuccessors

ReferenceDataOperationControlProof = {
    shape: ReferenceDataOperationControlShape
}

PhysicalReferenceInput = {
    operand: NodeId<Typed>,
    operandType: TypeId,
    storage: PhysicalStorageRef,
    proof: PhysicalStorageProof
}

HandleReferenceInput = {
    operand: NodeId<Typed>,
    handle: ReferenceHandleProof
}

PhysicalReferenceOutput = {
    valueType: TypeId,
    storage: PhysicalStorageRef
}

DereferencedStorageProof = {
    identity: DereferenceApplicationIdentity,
    handle: ReferenceHandleProof,
    output: PhysicalReferenceOutput,
    referentEquality: TypeEqualityProofId,
    sourceAccessProof: AccessProvisionProof,
    sourceMutabilityProof: MutabilityEqualityProof,
    sourceLifetimeProof: OutlivesProof,
    sourceAddressSpaceProof: AddressSpaceEqualityProof,
    sourceAliasProof: AliasProvenanceEqualityProof,
    sourceProvenanceProof: SourceProvenanceEqualityProof
}

RegisteredDirectReferenceApplicationAt<S: WitnessUseStage> = {
    registration: ReferenceOperationRegistration,
    input: PhysicalReferenceInput,
    output: ReferenceHandleProof,
    selection: ReferenceOperationSelectionAt<S>,
    control: ReferenceDataOperationControlProof,
    semanticUses: PlanSemanticUses<S>
}

RegisteredHandleTransformApplicationAt<S: WitnessUseStage> = {
    registration: ReferenceOperationRegistration,
    input: HandleReferenceInput,
    output: ReferenceHandleProof,
    selection: ReferenceOperationSelectionAt<S>,
    control: ReferenceDataOperationControlProof,
    semanticUses: PlanSemanticUses<S>
}

RegisteredDereferenceApplicationAt<S: WitnessUseStage> = {
    identity: DereferenceApplicationIdentity,
    registration: ReferenceOperationRegistration,
    input: HandleReferenceInput,
    output: DereferencedStorageProof,
    selection: ReferenceOperationSelectionAt<S>,
    control: ReferenceDataOperationControlProof,
    semanticUses: PlanSemanticUses<S>
}

DirectReferenceOperationAt<S: WitnessUseStage> =
    CoreAddressOf(result: DirectStorageHandleProof)
  | RegisteredDirectReference(application: RegisteredDirectReferenceApplicationAt<S>)

AccessorReferenceOperationAt<S: WitnessUseStage> =
    InvokeReferenceAccessor(result: AccessorHandleAdmissionProof)
  | InvokeReferenceAccessorThenRegistered(
        accessorResult: AccessorHandleResultProof,
        application: RegisteredHandleTransformApplicationAt<S>)

DereferenceOperationAt<S: WitnessUseStage> =
    BuiltinReferenceDereference(result: DereferencedStorageProof)
  | BuiltinPointerDereference(result: DereferencedStorageProof)
  | RegisteredDereference(application: RegisteredDereferenceApplicationAt<S>)

DirectReferenceOperation = DirectReferenceOperationAt<Published>
AccessorReferenceOperation = AccessorReferenceOperationAt<Published>
DereferenceOperation = DereferenceOperationAt<Published>
RegisteredDirectReferenceApplication =
    RegisteredDirectReferenceApplicationAt<Published>
RegisteredHandleTransformApplication =
    RegisteredHandleTransformApplicationAt<Published>
RegisteredDereferenceApplication =
    RegisteredDereferenceApplicationAt<Published>

ReferenceAccessorAvailabilityEvidence =
    DeclaredReferenceAccessorAccess(AccessEvidence)
  | RegisteredReferenceAccessorAccess

ReferenceAccessorDispatchDerivation =
    DirectAccessorDispatchProof
  | WitnessAccessorDispatchProof
  | DynamicAccessorDispatchProof
  | BuiltinAccessorDispatchProof

ReferenceAccessorTargetAt<S: WitnessUseStage> = {
    selector: AbstractAccessorSelector,
    dispatch: CallableDispatch<S>,
    derivation: ReferenceAccessorDispatchDerivation
}

ReferenceSourceSlotBinding = {
    projection: CapturedStorageProjection,
    slot: BoundCallSlot,
    operand: AccessOperandId,
    evaluateOnce: AccessStepId
}

ReferenceAccessorInvocationRequest = {
    id: NodeId<Typed>,
    site: SemanticOperationSiteAssignment,
    storage: AbstractStorageRef,
    accessor: AbstractRefAccessor,
    expectedReferent: TypeId,
    context: ExpressionCheckContextId
}

ReferenceAccessorInvocationAt<S: WitnessUseStage> = {
    identity: AccessorInvocationIdentity,
    site: SemanticOperationSiteAssignment,
    storage: AbstractStorageRef,
    declared: AbstractRefAccessor,
    requestContext: ExpressionCheckContextId,
    availability: ReferenceAccessorAvailabilityEvidence,
    target: ReferenceAccessorTargetAt<S>,
    sources: CapturedStorageSources,
    sourceBindings: NodeMap<SourceCallRole, ReferenceSourceSlotBinding>,
    provenanceSources: AccessorProvenanceSourceMapId,
    call: TypedCallAt<S>,
    rawResult: AccessorHandleResultProof
}

ReferenceAccessorPlanAt<S: WitnessUseStage> = {
    invocation: ReferenceAccessorInvocationAt<S>,
    operation: AccessorReferenceOperationAt<S>
}

ParameterReferenceAccessorRequest = {
    id: NodeId<Typed>,
    site: SemanticOperationSiteAssignment,
    storage: AbstractStorageRef,
    mode: PassingMode,
    accessEnvironment: AccessEnvironmentId,
    context: ExpressionCheckContextId
}

ParameterReferenceAccessorPlanAt<S: WitnessUseStage> = {
    mode: PassingMode,
    accessEnvironment: AccessEnvironmentId,
    instantiatedRequirement: PhysicalStorageRequirement,
    invocation: ReferenceAccessorInvocationAt<S>,
    handle: AccessorHandleAdmissionProof,
    dereferenceSite: PhysicalProjectionSiteAssignment,
    dereference: DereferenceOperationAt<S>,
    endpoint: DereferencedStorageProof,
    semanticUses: PlanSemanticUses<S>
}

ParameterReferenceAccessorFailureAt<S: WitnessUseStage> =
    ParameterReferenceAccessorOperationSiteRejected(
        failure: SemanticOperationSiteFailure)
  | ParameterReferenceAccessorModeNotPhysical(mode: PassingMode)
  | ParameterReferenceAccessorMissing(
        required: AccessMode,
        available: CanonicallyOrderedSet<AccessMode>)
  | ParameterReferenceAccessorInvocationFailed(
        failure: ReferenceAccessorInvocationFailureAt<S>)
  | ParameterReferenceAccessorHandleRejected(
        failure: ReferenceHandleValidationFailure)
  | ParameterReferenceAccessorDereferenceSiteRejected(
        failure: SemanticOperationSiteFailure)
  | ParameterReferenceAccessorDereferenceFailed(
        failure: DereferenceFailure)

ParameterReferenceAccessorResultAt<S: WitnessUseStage> =
    PlannedParameterReferenceAccessor(
        plan: ParameterReferenceAccessorPlanAt<S>)
  | ParameterReferenceAccessorNotPlanned(
        failure: ParameterReferenceAccessorFailureAt<S>)

ParameterReferenceAccessorPlan = ParameterReferenceAccessorPlanAt<Published>
ParameterReferenceAccessorFailure = ParameterReferenceAccessorFailureAt<Published>
ParameterReferenceAccessorResult = ParameterReferenceAccessorResultAt<Published>

StorageRefFallbackKind = ReadThroughRefAccessor | WriteThroughRefAccessor

StorageRefFallbackAuthorization = {
    languageRule: RuleId,
    kind: StorageRefFallbackKind,
    requirement: PhysicalStorageRequirement
}

InternalRefStoragePlanAt<S: WitnessUseStage> = {
    site: PhysicalProjectionSiteAssignment,
    authorization: StorageRefFallbackAuthorization,
    invocation: ReferenceAccessorInvocationAt<S>,
    handle: AccessorHandleAdmissionProof,
    dereference: DereferenceOperationAt<S>,
    endpoint: DereferencedStorageProof,
    storageProof: PhysicalStorageProof
}

StorageAccessRequestAt<S: WitnessUseStage> = {
    id: NodeId<Typed>,
    operationSite: PhysicalProjectionSiteAssignment,
    input: TypedExpr,
    intent: StorageAccessIntentAt<S>,
    context: ExpressionCheckContextId
}

StorageAccessRequest = StorageAccessRequestAt<Published>

StoragePrimaryAccessorRole = GetterStorageRole | SetterStorageRole

StorageAccessFailureAt<S: WitnessUseStage> =
    StorageInputIsNotPlace(actual: ValueCategory)
  | StorageAccessNotReadable(actual: AccessMode)
  | StorageAccessNotWritable(actual: AccessMode)
  | StorageAccessNotMutable(actual: Mutability)
  | StoragePrimaryAccessorMissing(role: StoragePrimaryAccessorRole)
  | StoragePrimaryAccessorFailed(role: StoragePrimaryAccessorRole,
                                 failure: CandidateFailure)
  | StorageRefFallbackNotAuthorized(kind: StorageRefFallbackKind,
                                    languageRule: RuleId)
  | StorageRefFallbackAccessorMissing(storage: AbstractStorageRef,
                                      required: AccessMode,
                                      available: CanonicallyOrderedSet<AccessMode>)
  | StorageRefFallbackAccessorFailed(failure: ReferenceAccessorInvocationFailureAt<S>)
  | StorageRefFallbackHandleRejected(failure: ReferenceHandleValidationFailure)
  | StorageRefFallbackDereferenceFailed(failure: DereferenceFailure)
  | StorageRefFallbackPhysicalProofFailed(requirement: PhysicalStorageRequirement,
                                          actual: PhysicalStorageRef)
  | StorageIntentPolicyRejected(intent: StorageAccessIntentAt<S>, rule: RuleId)

StorageAccessResultAt<S: WitnessUseStage> =
    PlannedStorageAccess(plan: AccessPlan<S>)
  | StorageAccessNotPlanned(failure: StorageAccessFailureAt<S>)

StorageAccessFailure = StorageAccessFailureAt<Published>
StorageAccessResult = StorageAccessResultAt<Published>
InternalRefStoragePlan = InternalRefStoragePlanAt<Published>

CheckedReferenceFormationAt<S: WitnessUseStage> =
    DirectPhysicalReference(operand: NodeId<Typed>,
                            policy: ReferenceSyntaxPolicyAt<S>,
                            storage: PhysicalStorageRef,
                            proof: PhysicalStorageProof,
                            context: ExpressionCheckContextId,
                            operation: DirectReferenceOperationAt<S>)
  | ExplicitAccessorReference(operand: NodeId<Typed>,
                              policy: ReferenceSyntaxPolicyAt<S>,
                              storage: AbstractStorageRef,
                              accessor: ReferenceAccessorPlanAt<S>)

directReferenceResult(CoreAddressOf(p)) = p.handle
directReferenceResult(RegisteredDirectReference(a)) = a.output

accessorReferenceResult(InvokeReferenceAccessor(p)) = p.admitted
accessorReferenceResult(InvokeReferenceAccessorThenRegistered(_, a)) = a.output

referenceResult(DirectPhysicalReference(_, _, _, _, _, op)) =
    directReferenceResult(op)
referenceResult(ExplicitAccessorReference(_, _, _, plan)) =
    accessorReferenceResult(plan.operation)

referencePolicy(DirectPhysicalReference(_, policy, _, _, _, _)) = policy
referencePolicy(ExplicitAccessorReference(_, policy, _, _)) = policy

CheckedReferenceFormation = CheckedReferenceFormationAt<Published>
ReferenceAccessorInvocation = ReferenceAccessorInvocationAt<Published>
ReferenceAccessorPlan = ReferenceAccessorPlanAt<Published>

ReferenceHandleValidationFailure =
    ResultIsNotReferenceOrPointer(actual: TypeId)
  | ReferenceReferentMismatch(expected: TypeId, actual: TypeId)
  | InsufficientReferenceAccess(actual: AccessMode, required: AccessMode)
  | ReferenceLifetimeFailure(required: LifetimeId, actual: LifetimeId)
  | ReferenceAddressSpaceNotPermitted(
        actual: AddressSpace,
        required: AddressSpaceRequirement)
  | ReferenceSourceNotPermitted(
        actual: PhysicalStorageSourceProvenance,
        required: PhysicalStorageSourceRequirement)
  | InvalidReferenceTypeProjection(type: TypeId, shape: ReferenceHandleShape)
  | ReferenceSourceAccessAmplification(source: AccessMode,
                                       result: AccessMode)
  | ReferenceSourceMutabilityMismatch(source: Mutability,
                                      result: Mutability)
  | ReferenceSourceLifetimeEscape(source: LifetimeId,
                                  result: LifetimeId)
  | ReferenceSourceAddressSpaceNotDenotable(source: PhysicalStorageAddressSpace)
  | ReferenceSourceAddressSpaceProjectionMismatch(
        source: PhysicalStorageAddressSpace,
        result: AddressSpace)
  | ReferenceSourceAliasMismatch(source: AliasProvenance,
                                  result: AliasProvenance)
  | ReferenceSourceProvenanceMismatch(
        source: PhysicalStorageSourceProvenance,
        result: PhysicalStorageSourceProvenance)
  | RefAccessorAccessAmplification(advertised: AccessMode,
                                   result: AccessMode)

ReferenceStaticInputValidationFailure =
    ReferenceStaticInputArityMismatch(expected: UInt32, actual: UInt32)
  | ReferenceStaticInputSortMismatch(
        ordinal: UInt32,
        expected: GenericParameterSort,
        actual: GenericParameterSort)
  | ReferenceStaticInputValueRejected(
        ordinal: UInt32,
        validator: RuleId,
        actual: GenericArg)

ReferenceOperationEndpointCategory = PhysicalStorageEndpoint | HandleValueEndpoint

ReferenceRegisteredControlShape =
    RegisteredTotalDataOperation
  | RegisteredThrowingOperation
  | RegisteredControlFlowOperation

ReferenceOperationValidationFailure =
    RegisteredReferenceOperationUnavailable(
        rule: StandardEnvironmentRuleId,
        environment: StandardEnvironmentId)
  | ReferenceOperationStaticInputsRejected(
        rule: StandardEnvironmentRuleId,
        inputs: CanonicalArguments,
        failure: ReferenceStaticInputValidationFailure)
  | ReferenceOperationInputTypeMismatch(
        rule: StandardEnvironmentRuleId,
        expected: TypeId,
        actual: TypeId)
  | ReferenceOperationInputCategoryMismatch(
        rule: StandardEnvironmentRuleId,
        expected: ReferenceOperationEndpointCategory,
        actual: ReferenceOperationEndpointCategory)
  | ReferenceOperationRuntimeInputCountMismatch(
        rule: StandardEnvironmentRuleId,
        expected: UInt32,
        actual: UInt32)
  | ReferenceOperationResultTypeMismatch(
        rule: StandardEnvironmentRuleId,
        expected: TypeId,
        actual: TypeId)
  | ReferenceOperationResultCategoryMismatch(
        rule: StandardEnvironmentRuleId,
        expected: ReferenceOperationEndpointCategory,
        actual: ReferenceOperationEndpointCategory)
  | ReferenceOperationStorageShapeMismatch(
        rule: StandardEnvironmentRuleId,
        expected: PhysicalStorageRef,
        actual: PhysicalStorageRef)
  | ReferenceOperationResultCountMismatch(
        rule: StandardEnvironmentRuleId,
        expected: UInt32,
        actual: UInt32)
  | ReferenceOperationControlShapeMismatch(
        rule: StandardEnvironmentRuleId,
        expected: ReferenceRegisteredControlShape,
        actual: ReferenceRegisteredControlShape)
  | ReferenceOperationInvalidHandle(
        rule: StandardEnvironmentRuleId,
        failure: ReferenceHandleValidationFailure)
  | ReferenceOperationEffectNotAllowed(
        rule: StandardEnvironmentRuleId,
        required: EffectSet,
        allowance: EffectAllowance,
        excess: EffectSet)
  | ReferenceOperationConcreteRegionUnavailable(
        rule: StandardEnvironmentRuleId,
        failure: CapabilityFailure)

RefAccessorInputBindingFailureAt<S: WitnessUseStage> =
    RefAccessorArgumentMappingFailure(ArgumentMapFailure)
  | RefAccessorArgumentPassingFailure(PassingModeFailureAt<S>)
  | RefAccessorArgumentConversionFailure(
        slot: BoundCallSlot,
        failure: ConversionFailure<S>)
  | RefAccessorMissingSource(role: SourceCallRole)
  | RefAccessorUnexpectedSource(role: SourceCallRole)
  | RefAccessorDuplicateSource(
        role: SourceCallRole,
        slots: NonEmpty<BoundCallSlot>)
  | RefAccessorSourceOperandMismatch(
        role: SourceCallRole,
        expected: TypedExpr,
        actual: AccessOperand)

AccessorReferenceResultContractFailure =
    AccessorReferenceContractUnavailable(AccessorReferenceResultContractId)
  | AccessorReferenceContractSelectorMismatch(expected: AbstractAccessorSelector,
                                               actual: AbstractAccessorSelector)
  | AccessorReferenceContractSignatureMismatch(expected: CallableSignatureId,
                                                actual: CallableSignatureId)
  | AccessorReferenceContractResultTypeMismatch(expected: TypeId, actual: TypeId)
  | AccessorReferenceContractReferentMismatch(expected: TypeId, actual: TypeId)
  | AccessorReferenceContractMissingProvenanceSource(AccessorProvenanceSourceRole)
  | AccessorReferenceContractSourceProvenanceUnavailable(
        role: AccessorProvenanceSourceRole,
        projection: CapturedStorageProjection)
  | AccessorReferenceContractRegisteredRuleFailure(StandardEnvironmentRuleId)
  | AccessorReferenceContractProvenanceAmplification(
        component: AddressSpaceComponent | MutabilityComponent |
                   LifetimeComponent | AliasComponent | SourceComponent)

AccessorProvenanceSourceMapFailure =
    AccessorProvenanceReceiverDomainMismatch(hasReceiver: Bool,
                                             hasBinding: Bool)
  | AccessorProvenanceParameterDomainMismatch(
        expected: CanonicallyOrderedSet<ParameterKey>,
        actual: CanonicallyOrderedSet<ParameterKey>)
  | AccessorProvenanceSlotBindingMissing(role: AccessorProvenanceSourceRole,
                                         slot: BoundCallSlot)
  | AccessorProvenanceProjectionMismatch(role: AccessorProvenanceSourceRole,
                                         expected: CapturedStorageProjection,
                                         actual: CapturedStorageProjection)
  | AccessorProvenanceProjectionNotCaptured(role: AccessorProvenanceSourceRole,
                                            projection: CapturedStorageProjection)

ReferenceAccessorInvocationFailureAt<S: WitnessUseStage> =
    RefAccessorOperationSiteRejected(failure: SemanticOperationSiteFailure)
  | RefAccessorSelectorDispatchMismatch(
        selector: AbstractAccessorSelector,
        dispatch: CallableDispatch<S>)
  | RefAccessorVisibilityFailure(decision: AccessDecision)
  | RefAccessorRegisteredRuleUnavailable(
        registration: RegisteredCallableRule)
  | RefAccessorSignatureMismatch(
        accessor: AbstractRefAccessor,
        signature: CallableSignature)
  | RefAccessorSelectionEffectNotAllowed(
        required: EffectSet,
        allowance: EffectAllowance,
        excess: EffectSet)
  | RefAccessorConcreteAvailabilityFailure(requirement: CapabilityRequirement,
                                           assumption: BooleanCapabilityPredicate,
                                           failure: CapabilityFailure)
  | RefAccessorInputBindingFailure(RefAccessorInputBindingFailureAt<S>)
  | RefAccessorProvenanceSourceMapFailure(AccessorProvenanceSourceMapFailure)
  | RefAccessorCallResultProvenanceMismatch(
        expected: TypedCallResultProvenanceAt<S>,
        actual: TypedCallResultProvenanceAt<S>)
  | RefAccessorResultContractFailure(AccessorReferenceResultContractFailure)
  | RefAccessorInvalidResult(ReferenceHandleValidationFailure)

RefAccessorPolicyFailure =
    RefAccessorPolicyHandleRejected(ReferenceHandleValidationFailure)
  | RefAccessorRegisteredOperationFailure(ReferenceOperationValidationFailure)

RefAccessorValidationFailureAt<S: WitnessUseStage> =
    RefAccessorInvocationFailed(ReferenceAccessorInvocationFailureAt<S>)
  | RefAccessorPolicyValidationFailed(RefAccessorPolicyFailure)

ReferenceAccessorInvocationResultAt<S: WitnessUseStage> =
    ValidReferenceAccessorInvocation(ReferenceAccessorInvocationAt<S>)
  | InvalidReferenceAccessorInvocation(failure: ReferenceAccessorInvocationFailureAt<S>)

RefAccessorValidationResultAt<S: WitnessUseStage> =
    ValidReferenceAccessor(plan: ReferenceAccessorPlanAt<S>)
  | InvalidReferenceAccessor(failure: RefAccessorPolicyFailure)

ReferenceAccessorInvocationFailure = ReferenceAccessorInvocationFailureAt<Published>
ReferenceAccessorInvocationResult = ReferenceAccessorInvocationResultAt<Published>
RefAccessorValidationFailure = RefAccessorValidationFailureAt<Published>
RefAccessorValidationResult = RefAccessorValidationResultAt<Published>

DirectReferenceValidationAt<S: WitnessUseStage> = {
    operation: DirectReferenceOperationAt<S>
}

DirectReferenceValidationResultAt<S: WitnessUseStage> =
    ValidDirectReference(DirectReferenceValidationAt<S>)
  | InvalidDirectReference(ReferenceOperationValidationFailure)

ReferenceSyntaxPolicyFailure =
    ReferenceSyntaxRuleUnavailable(syntax: ExplicitReferenceSyntax,
                                   environment: SemanticEnvironmentId)
  | ReferenceSyntaxOperandRejected(syntax: ExplicitReferenceSyntax,
                                   classifier: Classifier)
  | ReferenceSyntaxExpectedTypeConflict(expected: TypeId,
                                        policyKind: ReferenceHandleKind)
  | ReferenceSyntaxAddressSpacePolicyInvalid(requirement: AddressSpaceRequirement)
  | ReferenceSyntaxRegisteredRuleFailure(rule: StandardEnvironmentRuleId)
  | ReferenceSyntaxConcreteAvailabilityFailure(
        sources: NonEmpty<ResolvedConcreteAvailability>,
        combinedRequirement: CapabilityRequirement,
        assumption: BooleanCapabilityPredicate,
        failure: CapabilityFailure)

ReferenceFormationFailureAt<S: WitnessUseStage> =
    ReferenceSyntaxPolicyRejected(ReferenceSyntaxPolicyFailure)
  | OperandIsNotPlace(actual: ValueCategory)
  | AbstractStorageHasNoReferenceAccessor(
        storage: AbstractStorageRef,
        required: AccessMode,
        available: CanonicallyOrderedSet<AccessMode>)
  | DirectPhysicalStorageFailure(requirement: PhysicalStorageRequirement,
                                 actual: PhysicalStorageRef)
  | ReferenceSyntaxNotPermitted(syntax: ExplicitReferenceSyntax,
                                operand: TypeId)
  | ReferenceHandleInvalid(failure: ReferenceHandleValidationFailure)
  | RefAccessorValidationFailed(failure: RefAccessorValidationFailureAt<S>)
  | ReferenceOperationValidationFailed(
        failure: ReferenceOperationValidationFailure)

ReferenceFormationFailure = ReferenceFormationFailureAt<Published>

ReferenceFormationResultAt<S: WitnessUseStage> =
    FormedReference(CheckedReferenceFormationAt<S>)
  | ReferenceNotFormed(ReferenceFormationFailureAt<S>)

ReferenceFormationResult = ReferenceFormationResultAt<Published>

SelectedDereferenceSyntax =
    SelectedBuiltinDereference(registration: StandardEnvironmentRuleId,
                               staticInputs: CanonicalArguments)

DereferenceRequest = {
    id: NodeId<Typed>,
    site: PhysicalProjectionSiteAssignment,
    syntax: SelectedDereferenceSyntax,
    operand: TypedExpr,
    context: ExpressionCheckContextId
}

CheckedDereferenceAt<S: WitnessUseStage> = {
    identity: DereferenceApplicationIdentity,
    site: PhysicalProjectionSiteAssignment,
    operand: NodeId<Typed>,
    syntax: SelectedDereferenceSyntax,
    context: ExpressionCheckContextId,
    operation: DereferenceOperationAt<S>
}

dereferenceResult(BuiltinReferenceDereference(p)) = p
dereferenceResult(BuiltinPointerDereference(p)) = p
dereferenceResult(RegisteredDereference(a)) = a.output

CheckedDereference = CheckedDereferenceAt<Published>

DereferenceFailure =
    OperandIsNotReferenceOrPointer(actual: TypeId)
  | DereferenceSyntaxAuthorityMismatch(syntax: SelectedDereferenceSyntax,
                                       actual: TypeId)
  | InvalidDereferenceHandle(failure: ReferenceHandleValidationFailure)
  | DereferenceAccessUnavailable(actual: AccessMode)
  | DereferenceLifetimeExpired(actual: LifetimeId, required: LifetimeId)
  | DereferenceRuleUnavailable(type: TypeId)
  | DereferenceOperationValidationFailed(
        failure: ReferenceOperationValidationFailure)

DereferenceResultAt<S: WitnessUseStage> =
    Dereferenced(CheckedDereferenceAt<S>)
  | NotDereferenced(DereferenceFailure)

DereferenceResult = DereferenceResultAt<Published>

ValidateRegisteredPhysicalProjectionAt<S>(
    request: RegisteredPhysicalProjectionRequest)
    -> CheckResult<RegisteredPhysicalProjectionValidationResultAt<S>>

CheckReferenceFormationAt<S>(ReferenceFormationRequest)
    -> CheckResult<ReferenceFormationResultAt<S>>

CheckReferenceFormation = CheckReferenceFormationAt<Published>

ResolveReferenceSyntaxPolicyAt<S>(request: ReferenceFormationRequest)
    -> Result<ReferenceSyntaxPolicyAt<S>, ReferenceSyntaxPolicyFailure>

ResolveReferenceSyntaxPolicy = ResolveReferenceSyntaxPolicyAt<Published>

InstantiateAccessorReferenceResultAt<S>(
    input: AccessorReferenceResultInstantiationInputAt<S>)
    -> Result<AccessorReferenceResultCertificate,
              AccessorReferenceResultContractFailure>

ValidateReferenceAccessorInvocationAt<S>(request: ReferenceAccessorInvocationRequest)
    -> CheckResult<ReferenceAccessorInvocationResultAt<S>>

PlanParameterReferenceAccessorAt<S>(request: ParameterReferenceAccessorRequest)
    -> CheckResult<ParameterReferenceAccessorResultAt<S>>

PlanParameterReferenceAccessor = PlanParameterReferenceAccessorAt<Published>

AdmitAccessorHandle(raw: AccessorHandleResultProof,
                    requirement: PhysicalStorageRequirement,
                    expectedKind: Option<ReferenceHandleKind>)
    -> Result<AccessorHandleAdmissionProof, ReferenceHandleValidationFailure>

ValidateRefAccessorAt<S>(request: ReferenceFormationRequest,
                         policy: ReferenceSyntaxPolicyAt<S>,
                         invocation: ReferenceAccessorInvocationAt<S>)
    -> CheckResult<RefAccessorValidationResultAt<S>>

PlanStorageAccessAt<S>(request: StorageAccessRequestAt<S>)
    -> CheckResult<StorageAccessResultAt<S>>

PlanStorageAccess = PlanStorageAccessAt<Published>

DeriveStorageFallbackDereferenceAt<S>(
    identity: DereferenceApplicationIdentity,
    input: HandleReferenceInput,
    authorization: StorageRefFallbackAuthorization,
    context: ExpressionCheckContextId)
    -> CheckResult<Result<DereferenceOperationAt<S>, DereferenceFailure>>

DeriveParameterReferenceAccessorDereferenceAt<S>(
    identity: DereferenceApplicationIdentity,
    input: HandleReferenceInput,
    requirement: PhysicalStorageRequirement,
    context: ExpressionCheckContextId)
    -> CheckResult<Result<DereferenceOperationAt<S>, DereferenceFailure>>

ValidateDirectReferenceAt<S>(request: ReferenceFormationRequest,
                             policy: ReferenceSyntaxPolicyAt<S>,
                             storage: PhysicalStorageRef,
                             proof: PhysicalStorageProof)
    -> CheckResult<DirectReferenceValidationResultAt<S>>

ValidateRegisteredDirectReferenceAt<S>(
    request: ReferenceFormationRequest,
    policy: ReferenceSyntaxPolicyAt<S>,
    input: PhysicalReferenceInput,
    rule: StandardEnvironmentRuleId,
    staticInputs: CanonicalArguments)
    -> CheckResult<
        Result<RegisteredDirectReferenceApplicationAt<S>,
               ReferenceOperationValidationFailure>>

ValidateRegisteredHandleTransformAt<S>(
    request: ReferenceFormationRequest,
    policy: ReferenceSyntaxPolicyAt<S>,
    input: HandleReferenceInput,
    rule: StandardEnvironmentRuleId,
    staticInputs: CanonicalArguments)
    -> CheckResult<
        Result<RegisteredHandleTransformApplicationAt<S>,
               ReferenceOperationValidationFailure>>

ValidateRegisteredDereferenceAt<S>(
    identity: DereferenceApplicationIdentity,
    context: ExpressionCheckContextId,
    input: HandleReferenceInput,
    rule: StandardEnvironmentRuleId,
    staticInputs: CanonicalArguments)
    -> CheckResult<
        Result<RegisteredDereferenceApplicationAt<S>,
               ReferenceOperationValidationFailure>>

CheckDereferenceAt<S>(DereferenceRequest)
    -> CheckResult<DereferenceResultAt<S>>

CheckDereference = CheckDereferenceAt<Published>
```

The `ReferenceHandleProof` is the executable contract of the value produced by reference formation.
For a language reference, `ReferenceTypeProjection` resolves `resultType` to
`ReferenceType(shape.referent, shape.addressSpace, shape.access, shape.lifetime)`. For a pointer,
`PointerTypeProjection` resolves it to
`PointerType(shape.referent, shape.addressSpace, shape.access)`; `shape.lifetime` is the checked
provenance lifetime supplied by the physical input, accessor contract, or registered operation and
is retained even though raw pointer type identity does not contain a lifetime. `shape.mutability`,
`shape.alias`, and `shape.sourceProvenance` are value provenance rather than type identity and are
likewise retained by the checked handle proof.

The success rules below display the checked payload inside `FormedReference`/`Dereferenced`. The
enclosing `CheckResult` and diagnostics are omitted from judgment notation. A closed semantic
failure becomes the corresponding typed error expression under `EXP-ERR-002`; it is not scheduler
blocking.

```text
Γ ⊢ e ⇝ e' : T @ Place(PhysicalPlace(p))
p.valueType = T
q = ReferenceFormationRequest(n, syntax, e', context(Γ))
ResolveReferenceSyntaxPolicyAt<S>(q) = Success(policy)
provePhysicalStorage(p, policy.requirement, Γ) = π
ValidateDirectReferenceAt<S>(q, policy, p, π) =
    Success(ValidDirectReference(v), D)
x = DirectPhysicalReference(e'.node, policy, p, π, context(Γ), v.operation)
---------------------------------------------------------------- EXP-REF-001
Γ ⊢ explicit-reference(n, syntax, e) ⇝ x
    : referenceResult(x).resultType @ RValue

Γ ⊢ e ⇝ e' : T @ Place(AbstractPlace(a))
a.valueType = T
q = ReferenceFormationRequest(n, syntax, e', context(Γ))
ResolveReferenceSyntaxPolicyAt<S>(q) = Success(policy)
policy.accessor != RejectAbstractStorage
a.accessors.referenceAccessors[policy.requirement.access] = Some(r)
s = semantic operation site assignment carried by n for ReferenceAccessorInvocationRule
ValidateSemanticOperationSite(n, s) = Success(Unit)
u = ReferenceAccessorInvocationRequest(n, s, a, r, T, context(Γ))
ValidateReferenceAccessorInvocationAt<S>(u) =
    Success(ValidReferenceAccessorInvocation(i), D₁)
ValidateRefAccessorAt<S>(q, policy, i) =
    Success(ValidReferenceAccessor(p), D)
x = ExplicitAccessorReference(e'.node, policy, a, p)
---------------------------------------------------------------- EXP-REF-002
Γ ⊢ explicit-reference(n, syntax, e) ⇝ x
    : referenceResult(x).resultType @ RValue
```

`EXP-REF-003`: `ValidateReferenceAccessorInvocationAt<S>` is policy-neutral. It validates exactly
the request's abstract storage and the accessor declared by that storage, its
access/dispatch/signature, captured-source mapping, declaration-role-to-captured-projection mapping,
selected `TypedCallAt<S>`, and raw result contract. It has no
`ReferenceFormationRequest`, syntax policy, or storage-access fallback policy. Its
`storage = request.storage`, `declared = request.accessor`,
`sources = request.storage.capturedSources`, and
`request.storage.accessors.referenceAccessors[request.accessor.access] =
Some(request.accessor)`. Its
site is byte-identical to `request.site`, validation requires
`ValidateSemanticOperationSite(request.id, request.site) = Success(Unit)`, and its
`identity = accessorInvocationIdentity(request.site.site)`. Thus the identity is a nominal content
ID over an authenticated source-only operation site, not a stable-ID projection of `request.id`.
Its
`target.dispatch = call.dispatch`, its signature/argument map/call-slot recipes are stored in
`call`, and `call.contractContext = contractSelectionContext(resolve(requestContext))`. Checking
constructs the call through `BuildSelectedSurfaceTypedCallAt<S>` after the target proof; it does not
fabricate an overload result or require an effective callable contract. `Selection` is the intended
pre-fixpoint state for
recursive local accessors. Chapter 11 completes the call after effect/capability fixpoints and before
published elaboration. No lookup, overload resolution, contract completion, argument mapping,
conversion search, or access planning is repeated. `ValidateRefAccessorAt<S>` is the explicit-only
wrapper: it consumes a successful invocation and calls
`AdmitAccessorHandle(invocation.rawResult, policy.requirement, Some(policy.resultKind))` for the
direct accessor-result strategy, or validates the registered transform's input and output
requirements for the transform strategy. It thereby proves the final policy requirement/kind and
records any registered handle transform. The plan's raw result and every
`InvokeReferenceAccessor`/`InvokeReferenceAccessorThenRegistered` accessor result have the exact
`ReferenceHandleValueShape` stored by `plan.invocation.rawResult`; their use-specific
`ReferenceHandleProof` values are deliberately not byte-identical because they record the explicit
syntax policy or registered operation requirement. Accordingly, the policy-neutral query can return only
`ReferenceAccessorInvocationFailureAt<S>`, while the wrapper can return only
`RefAccessorPolicyFailure`; `RefAccessorValidationFailureAt<S>` is the closed sum used by
`CheckReferenceFormationAt<S>` to retain which phase failed.

Every successful invocation additionally satisfies the exact constructor equation

```text
invocation.call.resultProvenance =
    ReferenceHandleCallResult(TypedCallReferenceHandleResultAt {
        result = invocation.rawResult.result,
        authority = AccessorReferenceHandleCallResult(
            invocation.rawResult.certificate)
    })
```

and `invocation.call.resultAuthority = accessorResultAuthority(invocation.declared)`. The
certificate's contract is `invocation.declared.resultContract`, its invocation identity is
`invocation.identity`, and its call ID is `invocation.call.id`. Construction and deserialization
both recheck this byte-identical equation. An `OrdinaryCallResult`, a fixed/registered authority,
or a certificate copied from a sibling same-signature call selects
`RefAccessorCallResultProvenanceMismatch`; it cannot be paired with the raw proof and accepted by
checking only its result type.

`EXP-REF-004`: Physical-parameter binding is not explicit reference formation. For a request with
`mode.domain = PhysicalOperand(_)`, `PlanParameterReferenceAccessorAt<S>` resolves the exact
`request.accessEnvironment` and derives
`q = instantiatePhysicalStorageRequirement(request.mode,
resolve(request.accessEnvironment).invocationLifetime)`. It then selects exactly
`request.storage.accessors.referenceAccessors[request.mode.access]`. It never searches by access
inclusion: the `ReadAccess` (`constref`) entry is the only property/subscript accessor eligible for
`ConstRefMode`, and the `ReadWriteAccess` (`ref`) entry is the only one eligible for `RefMode`.

The query validates the supplied operation site and one policy-neutral accessor invocation, admits
its raw handle against the byte-identical `instantiatedRequirement`, and derives exactly one child
site with role `{ParameterReferenceAccessorDereferenceRule, 0}`. It passes the admitted handle to
`DeriveParameterReferenceAccessorDereferenceAt<S>` and stores the resulting closed operation and
`DereferencedStorageProof`. The plan satisfies all of these equations:

```text
plan.mode = request.mode
plan.accessEnvironment = request.accessEnvironment
plan.instantiatedRequirement = q
plan.invocation.storage = request.storage
plan.invocation.declared =
    request.storage.accessors.referenceAccessors[request.mode.access]
plan.handle.requirement = q
dereferenceResult(plan.dereference) = plan.endpoint
plan.endpoint.handle = plan.handle.admitted
plan.endpoint.output.storage.path = DereferencedReference(plan.endpoint.identity)
plan.semanticUses = exactSemanticUseMerge(
    semanticUsesOfTypedCall(plan.invocation.call),
    semanticUsesOfDereference(plan.dereference))
```

`semanticUsesOfTypedCall` is the keyed union of the call's `directEffectUse`, direct capability
selection, and every call-slot access plan's stored uses. `semanticUsesOfDereference` is empty for a
builtin data dereference and is the registered application's stored uses otherwise.
`exactSemanticUseMerge` rejects inconsistent equal effect-use keys and merges complete capability
selections only under `CAP-SEL-004`. The result therefore represents one execution of the accessor call
followed by one dereference. The intermediate handle is plan-internal; the original property stays
`AbstractPlace`, while `plan.endpoint.output.storage` is the new physical endpoint passed to the
callee. A direct `PhysicalPlace` bypasses this query and uses the same chapter 7
`PhysicalParameterBindingProofAt<S>` over its original endpoint. Neither route may use a getter,
setter, sibling reference-accessor key, value conversion, synthesized address syntax, temporary, or
write-back. Every failure is retained as the corresponding closed
`ParameterReferenceAccessorFailureAt<S>` alternative.

`EXP-REF-005`: `CheckReferenceFormationAt<S>` and `CheckDereferenceAt<S>` are total over semantic
inapplicability. Missing/inaccessible ref accessors, selector/dispatch mismatch, bad signatures,
source mapping/passing, invalid handle endpoints, unavailable registered rules, and registered
operation application failures select their closed failure alternatives. They cannot fall back to
a getter temporary, setter write-back, guessed backing field, same-named member found by fresh
lookup, or lowering-time reconstruction.

`EXP-STO-001`: `PlanStorageAccessAt<S>` is the sole consumer of `StorageAccessIntentAt<S>`. A
successful result contains the complete chapter 11 `AccessPlan<S>`; a failure selects one closed
`StorageAccessFailureAt<S>` alternative. The query plans only an ordinary value read or a fully
specified ordinary value write. Parameter passing and explicit reference formation are not intents,
and every success first requires
`ValidatePhysicalProjectionSite(request.id, request.operationSite) = Success(Unit)`. The site is
otherwise inert unless the selected plan contains an internal dereference child,
and this query never constructs, accepts, or calls `ReferenceFormationRequest`,
`ResolveReferenceSyntaxPolicy`, or `CheckReferenceFormationAt<S>`. A successful read plan has a
`YieldStorageRead` terminal and a successful write plan has a `CompleteStorageWrite` terminal;
neither may carry `PassArgument` or manufacture a dummy `RuntimeArgument`.

`EXP-STO-002`: For `ReadValueAccess` on `AbstractPlace(a)`, a present getter is the primary
authority. The query either validates and stores that getter invocation or returns
`StoragePrimaryAccessorFailed`; it never retries through the ref accessor after a present getter
fails. Only when the getter is absent may a versioned language rule authorize
`ReadThroughRefAccessor`. `WriteValueAccess(w)` is symmetric: a present setter is final, and the
named `WriteThroughRefAccessor` fallback is considered only when the setter is absent. Missing
primary and fallback accessors and a forbidden fallback have distinct failures. No parameter-mode
plan can inherit either fallback accidentally.

`EXP-STO-003`: An authorized ordinary-storage fallback selects
`a.accessors.referenceAccessors[authorization.requirement.access] = Some(r)` exactly, then derives
`AssignSemanticOperationSite(request.operationSite.context, request.operationSite.origin,
Some(request.operationSite.site), {StorageFallbackReferenceAccessorRule, 0}) = Success(iSite)` and
calls `ValidateReferenceAccessorInvocationAt<S>` with
`ReferenceAccessorInvocationRequest(request.id, iSite, a, r, a.valueType,
request.context)`, then immediately calls
`AdmitAccessorHandle(invocation.rawResult, authorization.requirement, None)`. It derives
`AssignSemanticOperationSite(invocation.site.context, invocation.site.origin,
Some(invocation.site.site), {StorageFallbackDereferenceRule, 0}) = Success(dSite)` and
`d = dereferenceApplicationIdentity(dSite.site)`, then passes `d`, that admission's exact handle, and
`request.context` to `DeriveStorageFallbackDereferenceAt<S>`. The
resulting `InternalRefStoragePlanAt<S>` stores the authorization, invocation, admission, closed
dereference operation, identical `DereferencedStorageProof`, and a `PhysicalStorageProof` for the
authorization's exact requirement. It stores `site = dSite`, and its dereference identity is exactly
`d`. Its
invocation context equals `request.context`, and its endpoint
has `endpoint.output.storage.valueType = a.valueType` and
`endpoint.output.storage.lifetime = resolve(request.context).evaluationLifetime`. The intermediate
endpoint's identity is `d`, its path is `DereferencedReference(endpoint.identity)`,
and `dereferenceResult(dereference) = endpoint`; the handle operand remains the exact result of the
stored invocation rather than being recovered from that path. The intermediate
handle is plan-internal: it cannot become the storage-access expression's result or a runtime call
argument. Getter/setter access, internal ref-accessor-plus-dereference access, and explicit
first-class reference formation are therefore three disjoint executable plans.

`EXP-STO-004`: `StorageAccessIntentAt<S>` deliberately has no parameter-mode alternative. Only
chapter 7's `PlanArgumentAdaptationAt<S>`/`PlanArgumentAccessAt<S>` pair may construct an abstract
`InMode`, `OutMode`, or `InOutMode` plan or a physical `ConstRefMode`/`RefMode` plan. The abstract
modes may retain their own named read, materialization, setter, and write-back operations. A physical
mode instead stores a complete `PhysicalParameterBindingProofAt<S>` and may call only the dedicated
`PlanParameterReferenceAccessorAt<S>` path defined by `EXP-REF-004` when its source is abstract.
`PlanStorageAccessAt<S>` cannot construct or partially populate that binding proof and is never
called to make a physical parameter applicable. In particular, an ordinary
`ReadThroughRefAccessor` fallback is not a hidden `__constref` argument plan, and its
`YieldStorageRead` terminal cannot become the call slot's physical-place `PassArgument` terminal.

`EXP-STO-005`: For `WriteValueAccess(w)`, `w.source` is a value-classified typed expression and
`w.conversion` has that expression's value type and the destination's `placeValueType` as its exact
source and target. The resulting `AccessPlan<S>` contains one `TypedInput` for `w.source`, evaluates
it exactly once, and retains that exact conversion and `w.completion`. Its
`CompleteStorageWrite(operation, result)` terminal names that evaluated source as both
`ComputedValue(result)` and the value yielded after a successful write. A physical destination uses
`WritePhysicalStorage`; a present setter uses `WriteAbstractStorage`; and an authorized ref fallback
uses `ResolveAbstractPlaceThroughReference` followed by `WritePhysicalStorage`. In all three cases the
stored write source, conversion, and completion condition are byte-identical to `w`; a planner may
not recover the right-hand side from syntax, replace the conversion, or import a parameter-mode
write-back policy. The plan's semantic uses include the conversion and selected accessor/reference
operations exactly once.

```text
Γ ⊢ h ⇝ h' : H @ RValue
ResolvePrefixOperator(*, h', context(Γ)) =
    SelectedDereferenceSyntax(syntax)
classifyReferenceHandle(h', context(Γ)) = η
s = physical projection site assignment carried by n for ExplicitDereferenceRule
q = DereferenceRequest(n, s, syntax, h', context(Γ))
ValidatePhysicalProjectionSite(q.id, q.site) = Success(Unit)
i = dereferenceApplicationIdentity(s.site)
CheckDereferenceAt<S>(q) =
    Success(Dereferenced(CheckedDereferenceAt<S>(i, s, h'.node, syntax, context(Γ), op)), D)
------------------------------------------------ EXP-REF-006
Γ ⊢ selected-prefix-dereference(n, syntax, h) ⇝
    CheckedDereferenceAt<S>(i, s, h'.node, syntax, context(Γ), op)
    : dereferenceResult(op).output.valueType
      @ Place(PhysicalPlace(dereferenceResult(op).output.storage))
```

The selected syntax authority is produced only by the registered standard dereference-syntax
candidate. A user-defined prefix `operator*` remains an ordinary `TypedCallAt<S>` and never enters
`CheckDereferenceAt<S>` merely because its token spelling is `*`. The common handle-derivation
primitive constructs
`PhysicalPlacePath.DereferencedReference(i)`. The stable identity is retained separately from the
exact executable handle operand `h'`; it is never the operand's node ID. A builtin
reference/pointer dereference derives
the place's access, mutability, address space, and alias provenance from `η` and its registered
representation rule. Its result lifetime is exactly
`resolve(q.context).evaluationLifetime`, and the stored source-lifetime proof proves that the
handle's lifetime outlives that required lifetime. A registered dereference has the same lifetime
equation and instead retains a
`RegisteredDereferenceApplicationAt<S>` whose `DereferencedStorageProof` is exact. That proof ties
the value type to the handle referent, prevents access or lifetime amplification, and preserves the
address space. Neither path consults the
property from which the handle might once have been obtained; the handle proof is the only
authority.

`EXP-REF-007`: `ReferenceAccessorInvocationAt<S>.target.derivation` is a checked one-to-one
correspondence between `invocation.declared.selector` and `invocation.call.dispatch`. Direct,
witness, and dynamic alternatives retain
their exact target/evidence/slot once in those two endpoints and use
`DeclaredReferenceAccessorAccess(Allowed(...))`. A builtin selector retains one
`RegisteredCallableRule`; `TYP-ENV-002` proves that its
`registration/environment/staticInputs` denote the exact logical `callableRule` in
`CallableDispatch.Builtin`, while the zero-payload `RegisteredReferenceAccessorAccess` records that
the same registration was resolved successfully. The derivation constructor is a relation tag, not
a second endpoint copy. A denied access decision, missing registration, mismatched dispatch, or
different static inputs is a failure rather than a successful target. The call's selection contract
has the same canonical signature and semantic environment used to validate the accessor. For a
builtin selector, `invocation.call.dispatch.witnessResolutions` is exactly the minimal stage-correct
projection of `invocation.storage.witnessResolutions` required by the registered callable rule's
static inputs and
specialization; it contains no ambiently discovered witness and omits no referenced witness.

`EXP-REF-008`: `plan.invocation.sources = plan.invocation.storage.capturedSources` by content
identity. Elaboration evaluates each source capture exactly once in
`plan.invocation.sources.evaluationOrder` and retains the resulting value under its
`CapturedStorageSourceRole`. The domain of `sourceBindings` is exactly the
`ComparedCallSource(role)` domain of `call.callSlots`, and the map is a bijection onto those slots;
ref accessor calls admit no defaulted source. `ReceiverSourceRole` projects the receiver capture at
the empty path. `ArgumentSourceRole(id, path)` projects
`StorageArgumentSource(id)` at the identical path. Ordinary arguments require an empty path; pack
expansions may bind multiple call roles to distinct projections of one evaluated capture, and a
zero-length expansion binds none. The named access operand and `EvaluateOnce` step consume the
projected captured value, never the original typed expression. Remaining preparation, passing,
cleanup, and write-back steps stay in the keyed access recipe and execute exactly once around the
call. `ExplicitAccessorReference.operand` is provenance for the abstract-place node, not an
additional runtime evaluation; the captured-source plan is the sole executable source authority.

`resolve(plan.invocation.provenanceSources)` satisfies `TYP-PLC-009` for
`plan.invocation.call.signature`, its `argumentMap`, `sourceBindings`, and those exact `sources`.
`AccessorReceiverProvenance` maps to the receiver binding's projection, while
`AccessorParameterProvenance(k)` maps to the unique projection whose bound call slot is
`ParameterSlotRole(k)`. The map is constructed once during invocation validation and is passed
unchanged to accessor-result instantiation; declaration checking never sees the call-site roles on
the projections' right-hand side. The same instantiation copies
`plan.invocation.identity` as its stage-free `invocationIdentity`; in particular,
`FreshAccessorAlias` never substitutes `call.id` or a later producer instruction identity.

Define `registeredReferenceUses(op)` as the stored `semanticUses` of a registered application and
the region-correct empty selection for a core operation. The effect uses of an accessor reference
are obtained from its checked syntax policy, `p.invocation.call.directEffectUse`, every
`slot.access.semanticUses.effects` in `p.invocation.call.callSlots`, and
`registeredReferenceUses(p.operation).effects`. Their maps form the canonical disjoint union. Its
capability selection instead merges the syntax policy, the call's already complete
`p.invocation.call.capabilitySelection`, and
`registeredReferenceUses(p.operation).capabilities` through `CAP-SEL-004` under the identical
request region. The call selection already contains every slot access/conversion capability
selection, so aggregating `slot.access.semanticUses.capabilities` again is invalid double counting;
those constituents are revalidated against the stored call selection without being inserted a
second time. A direct physical reference uses the same construction without an accessor call.

`EXP-REF-009`: Direct effect/capability use IDs are assigned by stable semantic child role, so those
constituent domains are disjoint and their derived union is contributed exactly once to the
enclosing callable's use graphs. A typed reference node does not store a second compatibility map
or a prematurely completed effective contract. Ordinary effective operation/accessor requirements
therefore participate in the caller's effect/capability inference. Only pre-inference selection
effects and genuinely concrete registered-rule regions are checked at selection time: a restricted
effect context uses `RestrictedSubset`. A registered reference operation's
`selection.capabilities` is the central `CapabilitySelectionAt<S>` product and is byte-identical to
`semanticUses.capabilities`. Its `inferredCapabilityUses` contains the operation's exact keyed
`Direct` ordinary use, so that requirement flows into caller inference even when an equal concrete
formula is also present; it is never rejected merely because the current symbolic region does not
imply it. `concreteAvailability` is `NoConcreteAvailability` when the registered rule declares no
concrete source. Otherwise it is `ProvenConcreteAvailability` with the exact resolved source set,
combined requirement, and proof whose region is
`worldAssumption(resolve(requestContext))`. Concrete sources and proofs never enter the inference
use map. This is the operation-level instance of `CAP-SEL-003` and `CAP-USE-002`.

`EXP-REF-010`: Each registered direct, handle-transform, or dereference query resolves
`rule` in the exact standard environment reached from the request context and validates one closed
application shape: physical-storage-to-handle, handle-to-handle, or handle-to-physical-storage,
respectively. Static input arity/sort/value, unary runtime input/result counts, input type/category,
output type/category, handle contract, storage shape, nonthrowing/no-successor control shape,
selection effects, and capability policy are all premises. A throwing operation must be represented
as a `TypedCallAt<S>` and `CallRegion`; it cannot hide exceptional control in a reference data
application. Every failure selects the corresponding `ReferenceOperationValidationFailure` with
exact endpoints. An application's `registration` is its sole registration authority; its control
proof validates that registration's schema and stores only the closed control-shape proof.
For a registered dereference, `application.identity = application.output.identity`, and the output
path is `DereferencedReference(application.identity)`; direct producers and handle transforms do
not acquire a physical-projection identity.
`InvokeReferenceAccessorThenRegistered` is valid only when its application's input handle is
an admission of `accessorResult.result` under the registered operation's exact input requirement and
its input operand is the accessor call's normal result;
`accessorResult.callResultType = call.resultType`. Its output is separately admitted under the
explicit syntax policy and is the plan's final result.
Changing either endpoint cannot be hidden as a schema-version mismatch.

`EXP-REF-011`: A `ReferenceHandleProof` is valid exactly when its type projection matches
`resultType` and `shape`, its type-equality proof has endpoints
`(expectedReferent, shape.referent)`, its access proof proves
`provides(effectiveHandleAccess(shape), requirement.access)`, its outlives proof has endpoints
`(shape.lifetime, requirement.minimumLifetime)`, and its address-space proof has
`admittedAddressSpace(addressSpaceProof) = ConcretePhysicalAddressSpace(shape.addressSpace)` and
`addressSpaceRequirement(addressSpaceProof) = requirement.addressSpace`. Its source proof has
`provenance = shape.sourceProvenance` and `requirement = requirement.source`; `AnyPhysicalSource`
is valid only for `AnyPhysicalStorage`, while `RegisteredPhysicalSourceFact(f)` requires `f` to
occur in that provenance and to match the exact registered source requirement. For every successful
reference formation, the final proof's `requirement` is byte-identical to the resolved syntax
policy's requirement and its `shape.kind` equals `policy.resultKind`.

For direct physical reference formation, the outer storage, `PhysicalStorageProof.storage`, and any
registered application's physical input storage are byte-identical; their requirement is exactly
the resolved syntax policy's requirement. The handle referent equals the operand type and its
address space/lifetime/alias provenance derive from that proven input storage.
`DirectStorageHandleProof.sourceAccessProof` proves that the storage supplies the handle's access,
`sourceMutabilityProof` preserves mutability, `sourceLifetimeProof` has endpoints
`(storage.lifetime, handle.shape.lifetime)`, and `sourceAddressSpaceProjection` has
`source = storage.addressSpace` and `result = handle.shape.addressSpace`. A symbolic physical formal
may form the handle only through `ExactFormalAddressSpace` or `SpecializedFormalAddressSpace`; an
unresolved `AnyReferenceableAddressSpace` or `OneOfAddressSpaces` selects
`ReferenceSourceAddressSpaceNotDenotable` instead of choosing a representative. The
`sourceAliasProof` preserves the physical storage's alias provenance, and
`sourceProvenanceProof` preserves its complete source-provenance set. A formal physical parameter
therefore remains symbolic in its address-space equality and cannot lose a registered source fact
while forming a handle.

For an accessor, `AccessorHandleResultProof.resultEquality` has endpoints
`(callResultType, result.type)`. Its certificate has `call = plan.invocation.call.id`,
`invocationIdentity = plan.invocation.identity`,
`subject = subjectOf(plan.invocation.call.dispatch)`, the canonical ID of
`plan.invocation.call.signature`, `contract = plan.invocation.declared.resultContract`,
`expectedReferent = plan.invocation.storage.valueType`, and
`result = result`. The certificate's result type and `callResultType` are identical, while its
expected referent equals `result.handle.referent` under the certificate's non-recovery referent
equality.
The resolved contract's selector/signature/result type are respectively the declared selector,
the canonical call-signature ID, and that same call result type; its referent equals the property's
value type.
Its instantiation has that same contract, sources, and result and exactly the address-space,
mutability, lifetime, alias, and source rules stored in the resolved contract.
Its `invocationIdentity` is byte-identical to both the certificate and invocation identity.
Its `provenanceSources` is byte-identical to `plan.invocation.provenanceSources` and to the ID in the
`AccessorReferenceResultInstantiationInputAt<S>` used to construct the certificate.
`InstantiateAccessorReferenceResultAt<S>` replays those rules against the exact captured sources;
neither the accessor call's nominal result type nor the property use may invent any non-type
provenance. A post-operation's final handle still proves the property's value type. These
equations, not token spelling or an implementation convention, define successful property
reference typing.

The invocation also revalidates
`plan.invocation.call.resultAuthority = accessorResultAuthority(plan.invocation.declared)` and the
complete `call.resultProvenance` equation in `EXP-REF-003`. These are serialization invariants, not
only builder preconditions: replacing the call provenance with `OrdinaryCallResult`, changing its
raw shape, or pairing the certificate with another call ID/identity is invalid even when all
signatures and `TypeId` values compare equal.

`AdmitAccessorHandle(raw, requirement, expectedKind)` is the sole bridge from that intrinsic raw
value shape to a use-specific `ReferenceHandleProof`. It preserves `raw.result` byte-for-byte,
sets `admitted.requirement = requirement`, uses `raw.certificate.expectedReferent`, and proves the
access, lifetime, address-space, and source-provenance obligations without changing the shape.
`Some(k)` additionally requires `raw.result.handle.kind = k`; `None` imposes no syntax-level kind.
Thus explicit reference formation, parameter binding, read fallback, write fallback, and a
registered transform may require distinct proofs of one raw accessor result without making
invocation policy-dependent.

A `DereferencedStorageProof` has equality endpoints
`(handle.shape.referent, output.valueType)`; its source-access and mutability proofs show that the
handle supplies the resulting place without amplification. Its `sourceLifetimeProof` has endpoints
`(handle.shape.lifetime, output.storage.lifetime)`. There is exactly one `a` such that
`output.storage.addressSpace = ConcretePhysicalAddressSpace(a)`, and its address-space equality has
endpoints `(handle.shape.addressSpace, a)`. Its alias proof has endpoints
`(handle.shape.alias, output.storage.alias)`. Its source-provenance equality has endpoints
`(handle.shape.sourceProvenance, output.storage.sourceProvenance)`. A registered dereference
application's input handle and output storage are byte-identical to all of those proof endpoints.
Every successful proof also has
`output.storage.valueType = output.valueType`; the enclosing dereference expression classifier uses
that identical value type. Its output path is exactly
`DereferencedReference(identity)`. For
`CheckedDereferenceAt<S>(identity, site, ..., context, operation)`,
`ValidatePhysicalProjectionSite(enclosingNode(checked), site) = Success(Unit)`,
`identity = dereferenceApplicationIdentity(site.site)`, and
`dereferenceResult(operation).identity = identity`; for an
internal fallback derived with `context`, `output.storage.lifetime` is byte-identical to
`resolve(context).evaluationLifetime`. If the source-lifetime proof cannot establish that endpoint,
the query returns `DereferenceLifetimeExpired(handle.shape.lifetime,
resolve(context).evaluationLifetime)` instead of publishing a place with a guessed or longer
lifetime.

`EXP-REF-012`: A successful `FormedReference(x)` has
`valueProvenance = ReferenceHandleProvenance(referenceResult(x))`.
`classifyReferenceHandle` consumes that exact fact (or the output proof of a registered handle
conversion) and never synthesizes mutability, lifetime, address space, alias, or physical-source
provenance from the operand's `TypeId`. Binding, store/load, argument/return, and control-flow merge
preserve or combine the fact only under `REP-TYP-002`; if the fact is absent or incompatible,
`CheckDereferenceAt<S>` returns `InvalidDereferenceHandle`.

`EXP-REF-013`: `ResolveReferenceSyntaxPolicyAt<S>` is the only source of a reference-formation
requirement or direct/accessor strategy. It resolves the written syntax in the request's exact
semantic environment and derives `requirement.minimumLifetime` from
`resolve(request.context).evaluationLifetime`. When a required expected handle type names a
different lifetime, that lifetime replaces the evaluation lifetime only after an `OutlivesProof`
shows that it covers the evaluation lifetime; otherwise policy resolution fails.
`expectedLifetimeCoverage` is `None` exactly when the resulting minimum is the evaluation lifetime;
otherwise it is `Some(p)` with endpoints `(requirement.minimumLifetime, evaluationLifetime)`.
Access, handle kind, the symbolic address-space requirement, physical-source requirement, and
registered operations come from
the selected versioned language rule and that expected handle type. The policy repeats the exact input syntax and
has a well-formed address-space requirement under `TYP-ADR-001`. `RejectAbstractStorage` makes an
abstract property/subscript inapplicable even when it has a ref accessor; either accessor strategy
is admitted only for explicitly written syntax whose language
rule names that behavior. An expected physical parameter mode, overload candidates, token-spelling
tests, and lowering cannot synthesize or weaken a policy. Every success stores the resolved value unchanged as
`referencePolicy(result)`, so validation and lowering never re-resolve syntax.
`policy.capabilities` is the complete `CapabilitySelectionAt<S>` for the versioned language rule and
has `region = worldAssumption(resolve(request.context))`. Its `inferredCapabilityUses` contains the
rule's exact keyed ordinary use, which is contributed to the enclosing expression and is never an
applicability premise. When the rule declares no concrete availability source, selection is
`NoConcreteAvailability`; otherwise `ProvenConcreteAvailability` retains the exact resolved source
set, combined requirement, and proof for that region. This selection is merged with accessor,
conversion, and registered-operation selections only under `CAP-SEL-004`; no source or ordinary use
may be dropped.
Physical storage is necessary for a direct strategy but is not by itself permission to form a
first-class pointer: a target rule may reject pointer formation or escape while the same storage
remains valid for direct `__ref` use. That rejection is a policy/availability failure and cannot be
deferred to an IR-shape validator.

`EXP-REF-014`: A source `&e` reaches `CheckReferenceFormationAt<S>` only after ordinary operator
lookup resolves the registered standard reference-syntax candidate and constructs
`SelectedBuiltinAddressOf` with that exact registration and static inputs. This candidate has a
dedicated reference-formation operand contract; it is not modeled as a circular
`operator&(__ref T)` call. A user-defined `operator&` remains an ordinary `TypedCallAt<S>` and
cannot be reclassified from token spelling. `GetAddressBuiltin` is a
distinct contextual syntax form. The two forms may resolve to the same versioned language policy,
but retain different syntax/origin provenance.

A source `*h` likewise reaches `CheckDereferenceAt<S>` only after ordinary prefix-operator lookup
resolves the registered standard dereference-syntax candidate and constructs
`SelectedBuiltinDereference` with that exact registration and static inputs. The candidate has the
dedicated handle operand contract stated by `EXP-REF-006`. A user-defined prefix `operator*` remains
an ordinary `TypedCallAt<S>` and cannot be reclassified from token spelling. The selected syntax is
stored on `CheckedDereferenceAt<S>` and must resolve in its request context to the exact builtin or
registered dereference operation; a different registration or static input selects
`DereferenceSyntaxAuthorityMismatch` rather than an equivalent-looking operation.

`EXP-REF-015`: A checked ref-accessor declaration has two deliberately different types: the
property/subscript value type is the contract's `referent`, while the accessor callable's result is
the contract's structurally checked reference/pointer `resultType`. Header checking publishes the
complete `AccessorReferenceResultContract` before body checking. Every reachable body return then
checks against that contract and supplies physical-storage/reference provenance that validates its
address-space, mutability, lifetime, alias, and source-provenance derivations. A body cannot publish
a bare referent value and rely on lowering to retrofit a pointer, nor can body inference mutate the
published signature; an omitted or inconsistent provenance derivation is a declaration error.

`EXP-REF-016`: A successful checked operation is in one-to-one correspondence with
`referencePolicy(result)`. `CoreAddressOfStrategy` selects only `CoreAddressOf`; a registered direct strategy
selects only `RegisteredDirectReference` with the identical rule/static inputs.
`InvokeAccessorResult` selects only `InvokeReferenceAccessor`; an accessor-then-registered strategy
selects only `InvokeReferenceAccessorThenRegistered` with the identical rule/static inputs; and
`RejectAbstractStorage` has no successful accessor operation. A strategy cannot be treated as a
ranking hint or replaced by an equivalent target opcode during validation or lowering.

## Calls and operators

Call-like forms delegate to chapter 7:

```text
ResolveCall(calleeCandidates, receiver, arguments, expectedResult, context)
    -> OverloadResult
```

Operator syntax produces candidates from standard-environment operator declarations, user-visible
lookup, and any named primitive registry. The typed result stores the selected candidate, complete
generic solution, argument map, access/conversion plans, witness values, and result type.

Type application, C-style explicit casts, braces, declaration initialization, and `new` delegate to
chapter 15. Initialization may reuse callable candidate machinery after its target model admits an
initializer strategy, but it is not an ordinary call kind.

`EXP-CALL-001`: Trial applicability never mutates argument nodes. The committed typed call is built
from the winning immutable candidate result; checking is not rerun “for real.”

## Differentiation expressions

`fwd_diff`, `bwd_diff`, and `no_diff` use chapter 16's closed judgments:

```text
CheckDifferentiate(mode, callable, order, environment)
    -> QueryStep<DerivativeProviderResult>

CheckStopGradient(expression, differentiabilityContext)
    -> CheckResult<DifferentiationExpr>
```

`EXP-DIF-001`: Differentiating a callable preserves its direct/witness/dynamic/closure/builtin
dispatch identity and canonical specialization, transforms the signature once, and stores the
selected derivative provider. Calling the resulting derivative callable is a later ordinary call.

`EXP-DIF-002`: `no_diff(e)` evaluates `e` once and preserves its ordinary type, effects,
capabilities, exception behavior, and place/storage operations. It creates an explicit
stop-gradient boundary; it is not an implicit conversion or a modifier hidden inside `TypeId`.

## Conditional and short-circuit expressions

`&&` and `||` either select declared overloads or use the core short-circuit rule. The core rule
coerces its operands to the standard environment's condition type and preserves conditional
evaluation in typed/Core AST.

For `c ? a : b`, checking obtains candidate branch types under any expected type, computes a
principal common type through `JoinExpressionTypes`, and records conversions for both branches.

```text
Γ ⊢ c ↝ Bool ⇝ c'
Γ ⊢ a ⇝ a' : τa       Γ ⊢ b ⇝ b' : τb
joinExprTypes(τa, τb, expected) = (τ, πa, πb)
--------------------------------------------------- EXP-COND-001
Γ ⊢ c ? a : b ⇝ Conditional(c', πa(a'), πb(b')) : τ @ RValue
```

The join operation is a named primitive with symmetric tests; it is not “try converting left to
right, then right to left” unless that policy is explicitly specified for a compatibility mode.

## Tuples and initialization syntax

Tuple expressions have one typed child per element and an ordinary `TupleType`. Empty tuple syntax
in Slang 2026 yields `Unit`; legacy comma-expression behavior is selected by language version before
typing.

A braced initializer is expectation-directed syntax and is checked only by chapter 15's published
`ResolveInitialization(request)` query. It retains nested brace/designator/source order but has no
independent classifier. `T(e)` and `(T)e` are the same `ExplicitSingle` request after binding, while
`T()` and omitted initialization remain distinct forms.

`EXP-INIT-001`: A braced initializer without enough expectation to choose a unique target remains
`MissingTargetType`; it is not a magic untyped expression accepted by arbitrary conversions.

`EXP-INIT-002`: Expression checking stores the selected `InitializationPlanId`. Its closed operation
resolves complete call/registered/allocation/transfer endpoint maps; aggregate/default bindings;
operation-qualified evaluation and storage orders; plan/allocation storage and handle identities;
the distinct allocated-object target and owning-handle result; output transfer;
entry/required-subobject/exit proofs; cleanup for every exit; effects;
capabilities; and witness values. Candidate failures, comparisons, and the considered set remain
structured data on the completed `InitializationResult`; they are not falsely hashed into the
executable plan. Elaboration consumes the winner and does not rerun the choice or infer an operation
from its strategy.

`EXP-INIT-003`: `RecoveredInitialization` produces an error-carrying typed node only for continued
diagnostics and tooling. Its recovery plan may elaborate to chapter 15's recovery Core node, but it
cannot be installed as a selected successful plan or contribute a publishable frontend-IR
initialization dependency.

## Lambdas

Lambda checking creates a typed lambda description, not a closure declaration:

```text
FreeVariableKey =
    DeclarationFreeVariable(CanonicalDeclRef)
  | ReceiverFreeVariable(owner: DeclId)

FreeVariableFact = {
    key: FreeVariableKey,
    firstUse: Origin,
    useOrigins: NonEmpty<Origin>
}

FreeVariableSet = {
    byKey: NodeMap<FreeVariableKey, FreeVariableFact>,
    order: NodeList<FreeVariableKey>
}

TypedParam = {
    declaration: DeclId,
    key: ParameterKey,
    type: ParameterType,
    origin: Origin
}

CaptureUseKind = ReadCapture | WriteCapture | BorrowCapture |
                 MoveCapture | AddressCapture

TypedCaptureUse = {
    source: FreeVariableKey,
    type: TypeId,
    category: ValueCategory,
    use: CaptureUseKind,
    requiredAccess: AccessMode,
    sourceLifetime: LifetimeId,
    origin: Origin
}

TypedLambda = {
    parameters: NodeList<TypedParam>,
    body: TypedStmt | TypedExpr,
    signature: CallableSignature,
    freeVariables: FreeVariableSet,
    captureUseFacts: NodeList<TypedCaptureUse>,
    resultSolution: LambdaResultSolution,
    origin: Origin
}

LambdaResultSolution = {
    expected: Option<TypeId>,
    contributors: NodeMap<LambdaResultContributorKey, LambdaResultContributor>,
    sourceOrder: NodeList<LambdaResultContributorKey>,
    result: TypeId,
    conversions: NodeMap<LambdaResultContributorKey, ConversionPlan>
}

LambdaResultContributorKey =
    ExpressionBodyContributor(expr: NodeId<Typed>)
  | ReturnContributor(statement: NodeId<Typed>)
  | FallthroughContributor(body: NodeId<Typed>)

LambdaResultContributor = {
    key: LambdaResultContributorKey,
    origin: Origin,
    type: TypeId
}
```

`FreeVariableSet.order` is a duplicate-free bijection onto `byKey`; it is sorted by lexical
`firstUse` and then canonical key. Every fact's map key equals `fact.key`, its first use is the first
entry in `useOrigins`, and `useOrigins` retains all uses in lexical order. Discovery therefore has
no insertion-order or pointer-identity input.

An expected function type supplies missing parameter/result information when compatible. Otherwise
parameters require sufficient annotations and the result is inferred from the expected type, all
reachable returns, and fall-through. A `Never` path contributes no result constraint; a recovery
expression preserves its `ErrorId` but cannot force an otherwise valid join to `ErrorType`.

`EXP-LAM-001`: Result inference gathers constraints from every reachable return. `Unit` is included
for a reachable statement-body fall-through. An expression body contributes one implicit return
with its origin and conversion slot. Conflicting constraints produce one result-inference diagnostic
with related contributor origins.

`EXP-LAM-003`: `LambdaResultSolution.sourceOrder` is a duplicate-free bijection onto
`contributors`, ordered by lexical source occurrence with expression body or reachable fallthrough
in its semantic execution position; each map key equals `contributor.key`. Unreachable fallthrough
has no contributor. `conversions` has exactly the contributor domain and each plan converts that
contributor's `type` to `result`. Consequently a return, expression body, or fallthrough conversion
cannot be detached from or reordered relative to the fact that required it.

`EXP-LAM-002`: Conversion to a raw function signature is applicable only when `freeVariables` is
empty and produces the static-thunk plan in chapter 7. Otherwise the lambda has closure identity;
callable-interface conversion uses an explicit closure conformance.

Binding records the lexically free declarations and receiver uses. Typing adds value category,
mutation, ownership, and lifetime facts for each use. Capture fields and modes are then produced by
the independent typed-capture analysis in chapter 11; a bound body alone is insufficient to choose
those modes.

## Existentials and type tests

Converting a concrete value to an existential records the concrete type and conformance evidence in
an `ExistentialPackPlan`. Member use opens the existential in a scoped typed region with a fresh
`OpenedTypeId` and witness. `is` and `as` use explicit runtime type-test/conversion plans supplied by
the relevant relation; they do not reuse compile-time subtype truth accidentally.

`EXP-EXT-001`: An opened existential type cannot escape its opening region in a result type, stored
declaration, or serialized module interface. Packing it again requires explicit witness evidence.

## Packs and compile-time forms

`each`, `expand`, first/last/trim/shape, pack branch, and compile-time loop forms operate on typed
pack values with cardinality evidence. A pack expansion records its pattern and captured packs
before materialization.

```text
PackValue = TypePackValue(NodeList<TypeId>)
          | ValuePackValue(NodeList<ConstValue>)
          | SymbolicPackValue(PackId)

PackCardinalityProof = ConcreteCardinality(BigNat)
                     | ConstraintCardinality(ConstraintEvidence)

PackCardinality = {
    count: ConstValue,
    proof: PackCardinalityProof
}

ExpandPlan = {
    pattern: TypedNode,
    captures: NodeMap<PackId, PackValue>,
    cardinality: PackCardinality,
    resultShape: ShapeValue
}
```

`EXP-PACK-001`: Multiple captured packs must have proven compatible cardinality/shape. Pairing by
operand position without a count witness is invalid.

## Statement context

```text
ControlTargetRole = LoopBreakTarget | LoopContinueTarget | SwitchBreakTarget |
                    LabeledBreakTarget | LabeledContinueTarget

ControlTargetKey = {
    function: CanonicalDeclRef,
    anchor: AnyNodeId,
    role: ControlTargetRole,
    label: Option<NameKey>
}

TargetId = ContentId<ControlTargetKey>

FunctionContext = {
    callable: CanonicalDeclRef,
    resultType: TypeId,
    errorType: TypeId,
    receiver: Option<ReceiverContext>,
    origin: Origin
}

BreakTarget = {
    id: TargetId,
    key: ControlTargetKey,
    origin: Origin
}

ContinueTarget = {
    id: TargetId,
    key: ControlTargetKey,
    origin: Origin
}

SwitchContext = {
    breakTarget: TargetId,
    conditionType: TypeId,
    caseScope: ScopeId,
    origin: Origin
}

CatchContext = {
    caughtErrorType: TypeId,
    scope: ScopeId,
    origin: Origin
}

ControlFlowContext = {
    function: Option<FunctionContext>,
    breakTargets: NodeList<BreakTarget>,
    continueTargets: NodeList<ContinueTarget>,
    switch: Option<SwitchContext>,
    deferDepth: UInt32,
    catchContext: Option<CatchContext>
}

StatementCheckContext = {
    expression: ExpressionCheckContext,
    control: ControlFlowContext
}

StatementCheckContextId = ContentId<StatementCheckContext>

ReturnFact = {
    origin: Origin,
    valueType: Option<TypeId>,
    conversion: Option<ConversionPlan>,
    exitsNormally: Bool
}

FlowSummary = {
    canFallThrough: Bool,
    returns: NodeList<ReturnFact>,
    breaks: NodeMap<TargetId, OriginSet>,
    continues: NodeMap<TargetId, OriginSet>,
    throws: EffectSet
}
```

Scope, generic/access/effect context, and the current world assumption have one authority in the
embedded `ExpressionCheckContext`; `ControlFlowContext` contains only control-transfer structure.
Every target record satisfies `id = ContentId(key)`, belongs to the current function, and has the
role required by its stack. Target stacks are innermost-to-outermost and duplicate-free. A
`SwitchContext.breakTarget` names the corresponding break-target entry; continue resolution never
uses it. These invariants make contexts canonical unit-test inputs rather than implicit checker
stack state.

Blocks thread scope/flow facts in source order while retaining immutable statement nodes. Branch
joins use an explicit flow lattice.

## Core statement rules

### Conditions

`if`, `while`, `do-while`, and `for` conditions use the condition coercion rule. Assignment in a
condition is rejected or warned according to a named language-version rule, not parser shape.

`if (let x = e)` remains a dedicated typed form containing the optional test, unwrapped binding,
and branch scope. Elaboration later makes `hasValue`/`value` or pattern operations explicit.

### Loops, switch, break, and continue

Entering a loop adds distinct break and continue targets. Entering a switch adds a break target but
not a continue target. Labels produce stable target IDs.

```text
resolveBreak(C, label) = target
-------------------------------- STM-BRK-001
C ⊢ break label? ⇝ Break(target)
```

No target yields a structured diagnostic and `ErrorStmt`. A `case`/`default` outside its owning
switch is invalid. Case constants use the constant-evaluation judgment and are checked for type,
duplicates, and permitted overlap.

### Return

```text
C.function.result = τ    Γ ⊢ e ⇑ Required(τ, Return) ⇝ e'
---------------------------------------------------------------- STM-RET-001
Γ; C ⊢ return e ⇝ Return(e')
```

Returning no value requires `Unit`; returning a value from `Unit` or omitting one for a non-`Unit`
result is diagnosed. Returning across a `defer` body is rejected by the explicit context rule.

### Defer and exceptional control

`defer s` checks `s` under a context that forbids control transfers escaping the defer. Typed AST
retains the structured defer; Core elaboration creates cleanup regions on every exiting edge.

`throw` checks against the function's declared error/effect type. `do ... catch` establishes a catch
context and typed error binding. The precise `try` expression propagation rule is an effect rule in
the standard environment and must preserve its error conversion plan.

### Target and stage switches

Each case checks under `worldAssumption ∧ casePredicate`. Duplicate/default/exhaustiveness rules
operate on capability formulas rather than string tokens. Branch results contribute conditional
capability requirements as defined in chapter 9.

### Shader-specific statements

`discard`, intrinsic assembly, GPU foreach, and capability-require statements are explicit typed
forms. Their availability, operand rules, and direct capability requirements come from versioned
standard-environment rule descriptors with stable rule IDs. They are not generic unchecked token
islands after `TypedAST`.

## Flow-sensitive validation

The frontend distinguishes typing from control/dataflow validation:

```text
FlowConditionId = ContentId<{
    function: CanonicalDeclRef,
    producer: NodeId<Core>,
    role: QualifiedName
}>

FlowOperationId = ContentId<{
    function: CanonicalDeclRef,
    producer: NodeId<Core>,
    ordinal: UInt32
}>

FlowCompletion = NormalCompletion | ExceptionalCompletion

FlowOperation =
    ReadStorage(id: FlowOperationId, storage: PhysicalStorageRef, origin: Origin)
  | InitializeStorage(id: FlowOperationId, storage: PhysicalStorageRef, origin: Origin)
  | WriteStorage(id: FlowOperationId, storage: PhysicalStorageRef, origin: Origin)
  | MoveFromStorage(id: FlowOperationId, storage: PhysicalStorageRef, origin: Origin)
  | BeginFlowBorrow(id: FlowOperationId, storage: PhysicalStorageRef,
                    access: AccessMode, origin: Origin)
  | EndFlowBorrow(begin: FlowOperationId, origin: Origin)
  | BeginFlowWriteback(id: FlowOperationId, source: PhysicalStorageRef,
                       destination: PhysicalStorageRef, origin: Origin)
  | EndFlowWriteback(begin: FlowOperationId, completion: FlowCompletion,
                     origin: Origin)
  | EvaluateForEffect(id: FlowOperationId, producer: NodeId<Core>, origin: Origin)

FlowTransfer =
    FallThrough(origin: Origin)
  | ReturnTransfer(value: Option<NodeId<Core>>, origin: Origin)
  | ThrowTransfer(value: NodeId<Core>, origin: Origin)
  | BreakTransfer(target: TargetId, origin: Origin)
  | ContinueTransfer(target: TargetId, origin: Origin)
  | UnreachableTransfer(origin: Origin)

StructuredFlowRegion =
    OperationRegion(operation: FlowOperation)
  | SequenceRegion(parts: NodeList<StructuredFlowRegion>, origin: Origin)
  | BranchRegion(condition: FlowConditionId,
                 thenRegion: StructuredFlowRegion,
                 elseRegion: StructuredFlowRegion,
                 origin: Origin)
  | LoopRegion(condition: Option<FlowConditionId>, body: StructuredFlowRegion,
               continueTarget: TargetId, breakTarget: TargetId, origin: Origin)
  | SwitchRegion(condition: FlowConditionId,
                 cases: NodeList<(ConstValue, StructuredFlowRegion)>,
                 defaultRegion: Option<StructuredFlowRegion>,
                 breakTarget: TargetId, origin: Origin)
  | CleanupRegion(body: StructuredFlowRegion,
                  normalCleanup: StructuredFlowRegion,
                  exceptionalCleanup: StructuredFlowRegion,
                  origin: Origin)
  | TransferRegion(transfer: FlowTransfer)

ControlFlowInput = {
    function: CanonicalDeclRef,
    resultType: TypeId,
    errorType: TypeId,
    body: StructuredFlowRegion,
    origin: Origin
}

FlowBlockKey = {
    function: CanonicalDeclRef,
    source: Origin,
    role: QualifiedName,
    ordinal: UInt32
}

FlowBlockId = ContentId<FlowBlockKey>

FlowEdgeKind = NormalEdge | TrueEdge | FalseEdge | CaseEdge(ConstValue) |
               DefaultEdge | ExceptionalEdge | CleanupEdge

FlowSuccessor = {
    target: FlowBlockId,
    kind: FlowEdgeKind,
    origin: Origin
}

FlowTerminator =
    Goto(successor: FlowSuccessor)
  | Branch(condition: FlowConditionId, whenTrue: FlowSuccessor, whenFalse: FlowSuccessor)
  | Switch(condition: FlowConditionId, successors: NonEmpty<FlowSuccessor>)
  | ReturnExit(value: Option<NodeId<Core>>, origin: Origin)
  | ThrowExit(value: NodeId<Core>, origin: Origin)
  | UnreachableExit(origin: Origin)

FlowBlock = {
    id: FlowBlockId,
    operations: NodeList<FlowOperation>,
    terminator: FlowTerminator,
    origin: Origin
}

ControlFlowGraph = {
    function: CanonicalDeclRef,
    resultType: TypeId,
    errorType: TypeId,
    entry: FlowBlockId,
    blocks: CanonicallyOrderedMap<FlowBlockId, FlowBlock>,
    origin: Origin
}

BuildControlFlow(ControlFlowInput) -> ControlFlowGraph
ValidateReturns(ControlFlowGraph) -> DiagnosticSet
ValidateDefiniteInitialization(ControlFlowGraph) -> DiagnosticSet
ValidateReachability(ControlFlowGraph) -> DiagnosticSet
ValidateBorrowAndWriteback(ControlFlowGraph) -> DiagnosticSet
```

`ControlFlowInput` is the immutable, structured projection of one Core callable body. It is derived
by schema traversal and is not a separately editable authority. Every effectful Core operation has
one `FlowOperationId`; every structured branch, transfer, cleanup, and target is represented once.
In particular, cleanup routing is input structure rather than a builder callback hidden in mutable
state. `BuildControlFlow` alone allocates block boundaries and successor edges. A graph stores
successors only in terminators; predecessor sets and exit-block collections are derived views, so
they cannot disagree with a second edge table. Each block-map key equals `block.id`, every successor
resolves in the same map, and the entry resolves. These properties are validated before any flow
analysis runs.

These are mandatory frontend queries even if implemented on initial IR. Their diagnostics cite
source/Core origins and are independently unit-testable. Expression/statement rules do not grow
ad hoc flow state to duplicate them.

## Constant evaluation

```text
PpUnaryOperator = PpPlus | PpMinus | PpLogicalNot | PpBitwiseNot

PpBinaryOperator =
    PpMultiply | PpDivide | PpRemainder | PpAdd | PpSubtract |
    PpShiftLeft | PpShiftRight |
    PpLess | PpLessEqual | PpGreater | PpGreaterEqual | PpEqual | PpNotEqual |
    PpBitwiseAnd | PpBitwiseXor | PpBitwiseOr | PpLogicalAnd | PpLogicalOr

PpName = {
    normalizedText: Utf8String
}

PpExpr =
    PpIntegerLiteral(spelling: Utf8String, origin: SourceRangeSet)
  | PpIdentifier(name: PpName, origin: SourceRangeSet)
  | PpDefined(name: PpName, origin: SourceRangeSet)
  | PpUnary(operator: PpUnaryOperator, operand: PpExpr, origin: SourceRangeSet)
  | PpBinary(operator: PpBinaryOperator, left: PpExpr, right: PpExpr,
             origin: SourceRangeSet)
  | PpConditional(condition: PpExpr, whenTrue: PpExpr, whenFalse: PpExpr,
                  origin: SourceRangeSet)
  | PpErrorExpr(error: ErrorId, origin: SourceRangeSet)

PpIntegerModel = {
    signedWidth: UInt16,
    unsignedWidth: UInt16,
    representation: TwosComplement,
    overflow: WrapModulo | DiagnoseAndWrap,
    rightShiftOfNegative: ArithmeticShift | DiagnoseAndArithmeticShift
}

PpIdentifierRule = UndefinedIdentifierIsZero | DiagnoseUndefinedIdentifierAndUseZero

PpConstEnvironment = {
    definedNames: CanonicallyOrderedSet<PpName>,
    integerModel: PpIntegerModel,
    identifierRule: PpIdentifierRule,
    languageRules: LanguageRuleSetId
}

PpInteger = {
    width: UInt16 | width >= 1,
    signed: Bool,
    bits: BigNat | bits < 2^width
}

PpConstValue = PpIntegerValue(PpInteger) | PpBooleanValue(Bool)

PpConstFailure =
    InvalidPpIntegerLiteral(spelling: Utf8String, origin: SourceRangeSet)
  | PpIntegerWidthUnsupported(width: UInt16, origin: SourceRangeSet)
  | PpArithmeticOverflow(operator: PpUnaryOperator | PpBinaryOperator,
                         origin: SourceRangeSet)
  | PpDivisionByZero(origin: SourceRangeSet)
  | PpInvalidShiftAmount(amount: BigInt, width: UInt16, origin: SourceRangeSet)
  | UndefinedPpIdentifier(name: PpName, origin: SourceRangeSet)
  | PriorPpError(error: ErrorId, origin: SourceRangeSet)

PpConstResult =
    EvaluatedPpConst(value: PpConstValue)
  | RecoveredPpConst(value: PpConstValue, failures: NonEmpty<PpConstFailure>)

EvalPreprocessorConst(ppExpr: PpExpr, environment: PpConstEnvironment)
    -> PpConstResult

EvalConst(typedExpr, phase, constEnvironment)
    -> ConstEvalResult

ConstEvalResult = Value(ConstValue)
                | Symbolic(ConstValue)
                | NotConstant(ConstFailure)
                | Error(ErrorId)

ConstPhase = GenericArgument | TypeFormation | Attribute | CaseLabel | FullCompileTime
```

Preprocessor constant evaluation is a separate pre-CST domain with its own macro-defined-name and
integer rules; it never accepts a `TypedExpr` or reads semantic declarations. `PpConstResult` is a
preprocessor integer/boolean value or structured preprocessor error.

`PpExpr` is the token-origin-preserving expression after ordinary macro expansion; `PpDefined` is
the sole form that queries `definedNames`. A remaining identifier follows `identifierRule` and does
not trigger semantic name lookup. Integer operations first apply the model's explicit usual
conversion rule, operate on mathematical integers, and then encode the result in `PpInteger.bits`;
host arithmetic is unobservable. `RecoveredPpConst` always carries the deterministic fallback used
to choose a conditional region, normally zero/false, together with every root failure in canonical
source order. The environment and result are immutable values suitable for isolated tests; neither
contains a macro table pointer, target singleton, diagnostic sink, or semantic declaration.

`PpName.normalizedText` is produced by the language rule set's preprocessor-identifier
normalization, which is distinct from chapter 1's registry-only `Utf8Identifier` grammar. Original
spelling remains available through the expression's token origins. The environment contains only
the resulting comparison keys, so macro-definition lookup is deterministic and mockable.

Both widths in `PpIntegerModel` are positive. Comparisons, `defined`, and logical operators produce
`PpBooleanValue`; integer truth is `bits != 0`, and using a boolean in an integer operation converts
it to signed zero or one before arithmetic conversion. Equal-signedness operands use the wider
width. For mixed signedness, an unsigned operand whose width is at least the signed width determines
that unsigned type; otherwise the wider signed type is used when it represents the entire unsigned
range, and its unsigned counterpart is used if it does not. This rule follows mathematical ranges,
never the host language's promotion rules.

Each phase declares allowed values, operations, declaration reads, and effects. `GenericArgument`
and `TypeFormation` accept only values representable in the generic/type domain; a broader
`FullCompileTime` evaluator cannot leak an unsupported aggregate into serialization.

```text
constBody(d) = e    request EvalConst(e, phase, constEnvironment(d)) = v
-------------------------------------------------------------------- CON-DECL-001
EvalConstDecl(CanonicalDeclRef(d), phase, environment) = v
```

`EvalConstDecl` and `EvalConst` are query kinds with the scheduler's `Reject` cycle policy. Query
code carries no private `evaluating` stack; a recursive request records a dependency edge and the
scheduler emits the complete deterministic cycle. A semantic-term growth detector and resource
ceiling may protect non-repeating expansion as chapter 10 specifies, but neither replaces the cycle
rule.

`CON-EVAL-001`: Constant operations are deterministic over specified integer widths and floating
formats. Host overflow, exception behavior, locale, and floating environment are irrelevant.

`CON-PP-001`: `EvalPreprocessorConst` is independently unit-tested and serialized only as part of
preprocessor provenance. Its result cannot be reused as a typed constant without an explicit
source-to-semantic conversion rule.

`CON-EVAL-002`: Unsupported constant evaluation returns `NotConstant(reason)`. It becomes a
diagnostic only when the requesting language rule requires a constant.

## Direct semantic capability use

Every typed node records only its direct requirement and references. For example, `discard` records
the fragment-stage atom; a call records its callee/witness dependency but does not recursively copy
the callee's current mutable capability field. `InferCapabilities` computes transitive requirements
as a separate fixpoint.

## Validation obligations

Typed expression/statement validation checks:

- child stages and origins are correct;
- each classifier alternative is legal and type/category projections exist only for values;
- place paths and access modes match the selected declaration/accessor;
- physical receiver/parameter uses have the exact `ConstRefFormalRoot` or `RefFormalRoot`, formal
  entry proof, activation lifetime, address-space requirement, and source provenance;
- every `ParameterReferenceAccessorPlanAt<S>` selects
  `referenceAccessors[mode.access]` exactly, invokes it once, admits its handle against the complete
  instantiated physical requirement, dereferences it once, and preserves the resulting physical
  endpoint through the call plan;
- no physical-parameter plan contains a getter/setter fallback, sibling accessor key, nonidentity
  conversion, temporary, write-back, or source/address/lifetime proof reconstructed from context;
- direct handle formation projects a physical storage address space to one denotable concrete
  address space, and handle/dereference proofs preserve source provenance exactly;
- calls contain complete immutable candidate results;
- conversions and expected-type applications have validated plans;
- direct-use collection traverses every selected conversion and access plan exactly once, preserving
  local/imported/witness identities for effect and capability inference;
- receiver expressions agree with the enclosing `CallableSignature.functionType`;
- control transfers target an enclosing compatible construct;
- every non-recovery type/value/effect/capability ID resolves; and
- no successful typed node contains an unresolved syntax ambiguity or overload set outside an
  explicitly permitted function-value context.

Current behavior evidence is primarily in `slang-check-expr.cpp`, `slang-check-stmt.cpp`,
`slang-check-type.cpp`, `slang-check-conversion.cpp`, and the expression/statement classes under
`slang-ast-*.h`.
