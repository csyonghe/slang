# Differentiability

This chapter defines the frontend semantics of differentiable types, callable promises, derivative
operators, custom derivative providers, activity boundaries, and the contract passed to derivative
IR transformations. Automatic-differentiation algorithms that transform a validated IR body are
downstream implementations of this contract; they are not the first layer where signature or
language semantics are defined.

Current compiler data structures—mutable type dictionaries on attributes, special witness classes,
and IR passes that rediscover frontend facts—are compatibility evidence only.

## Modes, order, and participation

```text
DifferentiationMode = Forward | Backward

DerivativeOrder = {
    value: BigNat
} where value >= 1

DifferentiationOrderPolicy =
    Exactly(order: DerivativeOrder)
  | Through(order: DerivativeOrder)
  | RegisteredOrderPolicy(rule: RuleId, inputs: CanonicalArguments)

DifferentiabilityPromise = {
    modes: CanonicalFiniteSet<DifferentiationMode>,
    order: DifferentiationOrderPolicy
}

DifferentialParticipation =
    InferFromType
  | ExcludedByNoDiff
```

Mode implication is versioned standard-environment data. If one language version declares that
backward differentiability implies forward differentiability, promise canonicalization closes the
set under that implication; the core algebra does not hard-code the implication.

`DIF-MOD-001`: An omitted differentiation order maps to the version's declared default. An explicit
zero or negative order is not a `DerivativeOrder` and produces a structured modifier diagnostic;
it cannot be interpreted by a downstream pass.

`DIF-MOD-002`: Receiver, every parameter, and result participation are structural callable-signature
fields. `no_diff` is never hidden in a `ModifiedType` or recovered from a declaration after function
type construction.

## Differential type evidence

Differentiability is constructive. A type is active only with evidence describing its differential
value and algebra:

```text
DifferentialFlavor = IDifferentiable | IDifferentiablePtrType

DifferentialAlgebraEntries = {
    differentialType:
        InterfaceRequirementKeyOf<AssociatedTypeKind>,
    zero: RuntimeInterfaceRequirementKey,
    add: RuntimeInterfaceRequirementKey,
    scale: Option<RuntimeInterfaceRequirementKey>
}

DifferentialAlgebraFailure =
    MissingAlgebraEntry(entry: SomeInterfaceRequirementKey)
  | AlgebraEntryKindMismatch(entry: SomeInterfaceRequirementKey,
                             expected: RequirementKind)
  | AlgebraEntrySignatureMismatch(entry: RuntimeInterfaceRequirementKey,
                                  expected: CallableSignatureId,
                                  actual: CallableSignatureId)
  | DifferentialAlgebraTypeMismatch(expected: TypeId, actual: TypeId)
  | DifferentialAlgebraConformanceUnavailable(
        type: TypeId,
        contract: InterfaceInstanceKey)

DifferentialInfoFailure =
    NoRegisteredDifferentialContract(type: TypeId,
                                     environment: SemanticEnvironmentId)
  | DifferentialConformanceUnavailable(type: TypeId,
                                        contract: InterfaceInstanceKey)
  | DifferentialTypeEntryUnavailable(
        witness: SubtypeWitnessId,
        entry: InterfaceRequirementKeyOf<AssociatedTypeKind>)
  | DifferentialTypeEntryInvalid(witness: SubtypeWitnessId,
                                 entry: InterfaceRequirementKeyOf<AssociatedTypeKind>)
  | DifferentialAlgebraUnavailable(type: TypeId,
                                   contract: InterfaceInstanceKey)
  | InvalidDifferentialAlgebra(failure: DifferentialAlgebraFailure)
  | IteratedDifferentialLawUnavailable(differential: TypeId,
                                       iterated: TypeId)
  | UnsupportedDifferentialFlavor(type: TypeId,
                                  flavor: DifferentialFlavor)

ValueDifferentialInfoKey = {
    primal: TypeId,
    flavor: DifferentialFlavor,
    differentiabilityWitness: SubtypeWitnessId,
    entries: DifferentialAlgebraEntries,
    differential: TypeId,
    differentialAlgebraWitness: SubtypeWitnessId,
    iteratedDifferential: TypeEqualityProofId,
    environment: SemanticEnvironmentId
}

ValueDifferentialInfoId = ContentId<ValueDifferentialInfoKey>

ValueDifferentialInfoEvidence = {
    id: ValueDifferentialInfoId,
    key: ValueDifferentialInfoKey
}

ValueDifferentialInfoAt<S: WitnessTableState> = {
    evidence: ValueDifferentialInfoEvidence,
    differentiabilityWitness: SubtypeWitnessRef<S>,
    differentialAlgebraWitness: SubtypeWitnessRef<S>
}

ValueDifferentialInfo = ValueDifferentialInfoAt<Published>

DifferentialInfoResultAt<S: WitnessTableState> =
    Available(ValueDifferentialInfoAt<S>)
  | Unavailable(DifferentialInfoFailure)
  | Ambiguous(NonEmpty<ValueDifferentialInfoAt<S>>)
  | Recovered(ErrorId)

DifferentialInfoResult = DifferentialInfoResultAt<Published>
```

The default standard environment registers `IDifferentiable` for value differentiation and
`IDifferentiablePtrType` for pointer differentiation, together with their exact interface instances
and entry keys. Semantic rules resolve those registered declaration identities rather than comparing
source spellings or assuming that an associated type is the first witness-table entry.

`DIF-TYP-001`: `BuildDifferentialInfoAt<S>(T, E)` first obtains a `SubtypeWitnessRef<S>` for the
registered differentiability contract. It obtains the
differential type by an exact witness-entry lookup, then obtains evidence that the resulting type
satisfies the required differential algebra. A bound generic witness, specialized generic table,
lookup witness, concrete table, and existential witness all use the same operations from chapter 15.

`DIF-TYP-002`: `iteratedDifferential` proves the registered idempotence/iteration law required by
the differentiation contract. It is not inferred by comparing source spellings. If a versioned
contract permits a different higher-order shape, it registers a different rule and evidence shape.

`DIF-TYP-003`: The zero/add/scale entries are keyed and signature-validated. Algebraic laws promised
by user implementations are semantic contracts just like other interface laws; the compiler may
test registered builtins and synthesized implementations, but a conformance is not a proof obtained
from entry position or method name.

`DIF-TYP-004`: A type cannot simultaneously select incompatible value- and pointer-differential
contracts in one environment. Provider specialization may choose one strictly more specific
contract; otherwise `Ambiguous` retains both candidates.

`DIF-TYP-005`: `evidence.id = ContentId(evidence.key)`. Each subtype-witness ref's stable witness ID
equals the correspondingly named ID in `evidence.key`, has the exact classifier required by that
role, and retains exactly the stage-permitted definition resolutions reachable from its operation.
`differentiabilityWitness` targets the registered differentiability contract for `primal`;
`differentialAlgebraWitness` targets the registered differential-algebra contract for
`differential`.

`DIF-TYP-006`: `ValueDifferentialInfoEvidence` is the stable proof term stored by the non-stage-
indexed constraint algebra and specialization frames in chapter 5. Executable checked products
resolve that evidence to `ValueDifferentialInfoAt<S>` before reading witness entries. Construction
publication may replace only the sidecar's operational definition resolutions; evidence ID/key,
witness IDs, entry keys, differential type, and equality proof do not change.

## Aggregate differential synthesis

```text
DifferentialFieldKey = FieldSlot(DeclId)

DifferentialExclusion =
    ExplicitlyExcludedDifferentialField(origin: Origin)
  | UnavailableDifferentialField(failure: DifferentialInfoFailure)
  | RegisteredDifferentialFieldExclusion(rule: RuleId,
                                         inputs: CanonicalArguments,
                                         origin: Origin)

DifferentialAlgebraSynthesisPlanAt<S: WitnessTableState> = {
    primalTarget: SubtypeWitnessTarget,
    differentialTarget: SubtypeWitnessTarget,
    differentialType: TypeId,
    entries: DifferentialAlgebraEntries,
    implementations:
        CanonicallyOrderedMap<RuntimeInterfaceRequirementKey,
                              CallableImplementationSubject>,
    differentiabilityWitness: SubtypeWitnessRef<S>,
    differentialAlgebraWitness: SubtypeWitnessRef<S>
}

DifferentialAlgebraSynthesisPlan =
    DifferentialAlgebraSynthesisPlanAt<Published>

DifferentialFieldPlanAt<S: WitnessTableState> = {
    primalField: DeclId,
    differentialField: SynthesizedDeclId | DeclId,
    info: ValueDifferentialInfoAt<S>,
    mappingOrigin: InferredFieldMapping | DeclaredDerivativeMember(Origin)
}

DifferentialFieldPlan = DifferentialFieldPlanAt<Published>

AggregateDifferentialPlanAt<S: WitnessTableState> = {
    primal: TypeId,
    differential: SynthesizedDeclId | TypeId,
    fields: CanonicallyOrderedMap<DifferentialFieldKey,
                                  DifferentialFieldPlanAt<S>>,
    excluded: CanonicallyOrderedMap<DeclId, DifferentialExclusion>,
    algebraEntries: DifferentialAlgebraSynthesisPlanAt<S>,
    synthesis: SynthesisKey
}

AggregateDifferentialPlan = AggregateDifferentialPlanAt<Published>

AggregateDifferentialFailureAt<S: WitnessTableState> =
    AggregateFieldDifferentialUnavailable(field: DeclId,
                                          failure: DifferentialInfoFailure)
  | AggregateFieldDifferentialAmbiguous(
        field: DeclId,
        candidates: NonEmpty<ValueDifferentialInfoAt<S>>)
  | InvalidDeclaredDerivativeMember(primal: DeclId,
                                    derivative: DeclId,
                                    reason: RuleId)
  | DuplicateDerivativeFieldMapping(field: DeclId)
  | MissingDifferentialAlgebraImplementation(
        entry: RuntimeInterfaceRequirementKey)
  | AggregateDifferentialSynthesisFailed(synthesis: SynthesisKey,
                                         error: ErrorId)

AggregateDifferentialResultAt<S: WitnessTableState> =
    SynthesizedAggregateDifferential(AggregateDifferentialPlanAt<S>)
  | RejectedAggregateDifferential(AggregateDifferentialFailureAt<S>)
  | RecoveredAggregateDifferential(AggregateDifferentialPlanAt<S>,
                                   NonEmpty<ErrorId>)

AggregateDifferentialResult =
    AggregateDifferentialResultAt<Published>
```

`DIF-AGG-001`: Automatic synthesis considers the aggregate's direct user-semantic stored fields.
An active field receives one keyed differential field; an explicitly `no_diff` or unavailable field
is recorded in `excluded`. Properties, static fields, extension members, synthesized backing
storage, and concrete base-struct subobjects are not implicit differential fields. Concrete struct
inheritance is excluded from the language.

`DIF-AGG-002`: A declared derivative-member mapping names one primal field and one field of the
declared differential type. The field types and differentiability evidence must match; duplicate,
missing, inaccessible, or cross-type mappings are structured failures. Source/member order is not
identity.

`DIF-AGG-003`: Differential type, field declarations, mappings, conformance table, and
zero/add/scale bodies are outputs of one atomic `SynthesisGroup`. Recursive aggregate graphs may
allocate all
identities first, but no incomplete differential type or witness table is observable.

`DIF-AGG-004`: `struct S : IDifferentiable`-style syntax is an interface conformance and may request
this synthesis. It is not struct representation inheritance and creates no base subobject/facet.

`DIF-AGG-005`: `algebraEntries.implementations` has exactly the `zero` and `add` keys plus `scale`
when present. Each implementation's checked signature matches its key. The differentiability
witness has `primalTarget` and satisfies `entries.differentialType` with `differentialType`; the
differential-algebra witness has `differentialTarget`, whose subtype is `differentialType`, and owns
the zero/add/scale entries. The IDs may be allocated before bodies in the same synthesis group, but
an `AggregateDifferentialPlanAt<Published>` is constructible only after the complete group freezes.

## Callable differential shape

```text
PrimalSlotKey =
    ReceiverPrimalSlot
  | ParameterPrimalSlot(ParameterKey)
  | ResultPrimalSlot
  | ErrorPrimalSlot

DifferentialInactivityReason =
    ExplicitNoDiff | NoDifferentialEvidence | RoleExcludedByRule(RuleId)

DifferentialSlotAt<S: WitnessTableState> =
    Inactive(type: TypeId, reason: DifferentialInactivityReason)
  | Active(info: ValueDifferentialInfoAt<S>)

DifferentialSlot = DifferentialSlotAt<Published>

DifferentialErrorPolicy =
    RejectThrowingCallable
  | PreserveErrorChannel
  | RegisteredDifferentialErrorPolicy(rule: RuleId,
                                      inputs: CanonicalArguments)

CallableDifferentialShapeAt<S: WitnessTableState> = {
    signature: CallableSignatureId,
    environment: SemanticEnvironmentId,
    receiver: Option<DifferentialSlotAt<S>>,
    parameters: CanonicallyOrderedMap<ParameterKey, DifferentialSlotAt<S>>,
    result: DifferentialSlotAt<S>,
    error: Option<DifferentialSlotAt<S>>,
    errorPolicy: DifferentialErrorPolicy
}

CallableDifferentialShape = CallableDifferentialShapeAt<Published>

CallableDifferentialShapeFailureAt<S: WitnessTableState> =
    SlotDifferentialInfoUnavailable(slot: PrimalSlotKey,
                                    failure: DifferentialInfoFailure)
  | SlotDifferentialInfoAmbiguous(
        slot: PrimalSlotKey,
        candidates: NonEmpty<ValueDifferentialInfoAt<S>>)
  | RequiredActiveSlotUnavailable(slot: PrimalSlotKey, type: TypeId)
  | UnsupportedDifferentialErrorChannel(error: TypeId,
                                        policy: DifferentialErrorPolicy)
  | InvalidCallableDifferentiabilityPromise(reason: RuleId)

CallableDifferentialShapeResultAt<S: WitnessTableState> =
    Shaped(CallableDifferentialShapeAt<S>)
  | RejectedShape(CallableDifferentialShapeFailureAt<S>)
  | RecoveredShape(CallableDifferentialShapeAt<S>, NonEmpty<ErrorId>)

CallableDifferentialShapeResult =
    CallableDifferentialShapeResultAt<Published>

DifferentialEvidenceRootRole =
    DifferentiabilityContractEvidence
  | DifferentialAlgebraEvidence

DifferentialEvidencePathStep =
    RootDifferentialEvidence(role: DifferentialEvidenceRootRole)
  | WitnessSpecializationArgument(owner: SubtypeWitnessId,
                                  parameter: CanonicalBoundVariable)
  | WitnessConstraintEvidence(owner: SubtypeWitnessId,
                              slot: CanonicalConstraintSlot)
  | LookupBaseWitness(owner: SubtypeWitnessId,
                      key: SubtypeWitnessLookupKey)
  | AssociatedTypeWitness(owner: SubtypeWitnessId,
                          entry: InterfaceRequirementKeyOf<AssociatedTypeKind>)
  | OpenedExistentialEvidence(owner: SubtypeWitnessId,
                             opening: OpenedTypeId)
  | RegisteredDifferentialEvidence(rule: RuleId,
                                   inputs: CanonicalArguments)

DifferentialEvidenceOperandKey = {
    primalSlot: PrimalSlotKey,
    path: NonEmpty<DifferentialEvidencePathStep>
}

DifferentialEvidenceOperandSourceAt<S: WitnessTableState> =
    GenericSubstitutionOperand(owner: SubtypeWitnessId,
                               parameter: CanonicalBoundVariable,
                               argument: GenericArg,
                               witnessResolutions: WitnessResolutionSetAt<S>)
  | ConstraintEvidenceOperand(owner: SubtypeWitnessId,
                              slot: CanonicalConstraintSlot,
                              evidence: ConstraintEvidence,
                              witnessResolutions: WitnessResolutionSetAt<S>)
  | SubtypeWitnessOperand(witness: SubtypeWitnessRef<S>)
  | AssociatedTypeWitnessOperand(
        projection: TypeId,
        witness: SubtypeWitnessRef<S>,
        entry: InterfaceRequirementKeyOf<AssociatedTypeKind>)
  | OpenedExistentialWitnessOperand(witness: SubtypeWitnessRef<S>,
                                   opening: OpenedTypeId)
  | RegisteredEvidenceOperand(rule: RuleId,
                              inputs: CanonicalArguments,
                              witnessResolutions: WitnessResolutionSetAt<S>)

DifferentialEvidenceOperandClassifier =
    GenericSubstitutionEvidence(parameter: CanonicalBoundVariable,
                                sort: GenericParameterSort)
  | ConstraintEvidenceValue(slot: CanonicalConstraintSlot,
                            kind: ConstraintKind)
  | SubtypeWitnessEvidence(SubtypeWitnessForm)
  | AssociatedTypeWitnessEvidence(projection: TypeId,
                                  classifier: SubtypeWitnessForm)
  | OpenedExistentialWitnessEvidence(SubtypeWitnessForm)
  | RegisteredDifferentialEvidenceValue(rule: RuleId,
                                        inputs: CanonicalArguments)

DifferentialEvidenceOperandAt<S: WitnessTableState> = {
    key: DifferentialEvidenceOperandKey,
    source: DifferentialEvidenceOperandSourceAt<S>,
    classifier: DifferentialEvidenceOperandClassifier,
    dependencies: CanonicallyOrderedSet<DifferentialEvidenceOperandKey>
}

DifferentialEvidenceOperandPlanAt<S: WitnessTableState> = {
    operands:
        CanonicallyOrderedMap<DifferentialEvidenceOperandKey,
                              DifferentialEvidenceOperandAt<S>>,
    materializationOrder: NodeList<DifferentialEvidenceOperandKey>
}

DifferentialEvidenceOperandPlan =
    DifferentialEvidenceOperandPlanAt<Published>
```

`DIF-CAL-001`: Shape construction visits the receiver, every `ParameterSlot`, result, and non-`BottomType`
error channel exactly
once. `ExcludedByNoDiff` always yields `Inactive(ExplicitNoDiff)`. `InferFromType` requests
`BuildDifferentialInfoAt<S>`; absence yields `NoDifferentialEvidence` only where the role permits an
inactive value, otherwise a structured callable-shape failure. `error` is present exactly when the
callable has a non-`BottomType` error type and the error policy preserves or transforms that channel;
rejecting a throwing callable produces `UnsupportedDifferentialErrorChannel`, not an omitted slot.

`DIF-CAL-002`: The shape is parameter-keyed and pack expansion creates distinct `ParameterKey`
entries. A mutable side dictionary populated opportunistically while checking the body is not the
source of callable differentiability.

`DIF-CAL-003`: A callable's structural `DifferentiabilityPromise` states which derivative surfaces
its signature promises. Whether its local body, custom provider, subtype witness, or registered
builtin fulfills that promise is an `EffectiveDifferentiabilityContract` query result and cannot
alter function-type equality after body checking.

`DIF-CAL-004`: `buildDifferentialEvidenceOperandPlan(shape)` starts two roots for every active
`PrimalSlotKey`: the slot's differentiability-contract witness and its differential-algebra witness.
It then takes the transitive closure of operational witness materialization. A specialized witness
contributes every runtime generic substitution and keyed constraint-evidence operand; a lookup
contributes its base witness; an associated-type projection contributes the exact witness and entry
key that justify the projection; and an opened existential contributes its opening witness. Evidence
nested in a `ValueDifferentialInfoEvidence` or another constraint is traversed by schema, not by a
hard-coded conformance-only case. Direct concrete tables with no runtime inputs contribute only their
root witness-table reference.

Every map key equals `operand.key`; every dependency is another key in the same map; and
`materializationOrder` is the canonical duplicate-free topological order of the complete map. Each
stage-specific source retains the exact minimal `WitnessResolutionSetAt<S>` needed to lower it. Its
classifier is derived from that source and fixes the IRReady/IR evidence shape before lowering.
Neither equal machine representations nor repeated witnesses merge distinct semantic keys; IRReady may
reuse the resulting SSA value only after preserving both keyed roles. No ambient conformance lookup,
associated-type rediscovery, or reconstruction from `TypeId` is permitted.

## Derivative signature maps

```text
DerivativeSlotRole =
    PrimalValueInput
  | PrimalDifferentialPairInput
  | PointerDifferentialPairInput
  | CotangentAccumulatorInput
  | CotangentSeedInput
  | DroppedInactiveOutput
  | PreservedInactiveInput
  | RegisteredDerivativeRole(rule: StandardEnvironmentRuleId)

DerivativeCallableSlotKey =
    DerivativeReceiverSlot
  | DerivativeParameterSlot(ParameterKey)
  | DerivativeResultSlot
  | DerivativeErrorSlot

DerivativeCallableSlotMode =
    DerivativeParamPassingMode(ParamPassingMode)
  | DerivativeResultMode
  | DerivativeErrorMode

DerivativeCallableSlotShape = {
    type: TypeId,
    mode: DerivativeCallableSlotMode
}

DerivativeSlotPlan = {
    primal: PrimalSlotKey,
    derivatives:
        CanonicallyOrderedMap<DerivativeCallableSlotKey,
                              DerivativeCallableSlotShape>,
    role: DerivativeSlotRole,
    sourceType: TypeId,
    sourceMode: DerivativeCallableSlotMode
}

ForwardDerivativeResultKind =
    PrimalOnlyForwardResult
  | PrimalDifferentialPairForwardResult

DerivativeResultPlan =
    ForwardResult(output: DerivativeCallableSlotKey,
                  kind: ForwardDerivativeResultKind)
  | BackwardVoidResult(output: DerivativeCallableSlotKey,
                      seedParameter: Option<ParameterKey>)

DerivativeSignatureMap = {
    primal: CallableSignatureId,
    derivative: CallableSignatureId,
    mode: DifferentiationMode,
    order: DerivativeOrder,
    slots: CanonicallyOrderedMap<PrimalSlotKey, DerivativeSlotPlan>,
    derivativeSlotOrder: NodeList<DerivativeCallableSlotKey>,
    result: DerivativeResultPlan,
    errorPolicy: DifferentialErrorPolicy
}

DerivativeSignatureMapId = ContentId<DerivativeSignatureMap>

DerivativeSignatureFailure =
    UnsupportedDerivativeSlot(slot: PrimalSlotKey,
                              mode: DerivativeCallableSlotMode,
                              flavor: DifferentialFlavor)
  | MissingPhysicalOperandDerivativeRule(slot: PrimalSlotKey,
                                         primalMode: ParamPassingMode,
                                         differentiationMode: DifferentiationMode,
                                         order: DerivativeOrder)
  | UnsupportedDerivativeErrorChannel(error: TypeId,
                                      policy: DifferentialErrorPolicy)
  | InvalidDerivativeOrderForCallable(order: DerivativeOrder,
                                      signature: CallableSignatureId)
  | DerivativeSlotCollision(slot: DerivativeCallableSlotKey)
  | RegisteredDerivativeSignatureRejection(rule: StandardEnvironmentRuleId,
                                           slot: PrimalSlotKey)

DerivativeSignatureResult =
    TransformedDerivativeSignature(DerivativeSignatureMap)
  | RejectedDerivativeSignature(DerivativeSignatureFailure)
  | RecoveredDerivativeSignature(DerivativeSignatureMap,
                                 NonEmpty<ErrorId>)
```

The versioned standard environment supplies canonical `DifferentialPair<T>` and
`DifferentialPtrPair<T>` type constructors. Pair construction is a named type application, not an
AST wrapper inferred by lowering.

### Forward mode

`DIF-SIG-FWD-001`: An active value-differential receiver/parameter of type `T` in the abstract
operand domain becomes the registered pair type for `T`; an active pointer-differential abstract
input becomes its registered pointer pair. Inactive abstract slots retain their primal types.
Parameter directions/modes are preserved exactly unless a registered rule rejects that
type/mode combination. This rule does not apply to `ConstRefMode` or `RefMode`: read-only access
does not turn a physical location into an `InMode` value.

`DIF-SIG-FWD-002`: An active result `R` becomes the registered pair result; an inactive result stays
`R`. Pointer-differential `OutMode`, `InOutMode`, `ConstRefMode`, `RefMode`, or result roles are
rejected unless a registered pointer-differentiation rule defines their location, aliasing, access,
and write-back semantics. `ConstRefMode` additionally obeys `DIF-SIG-FWD-004` even when its
differential flavor is value-like.

`DIF-SIG-FWD-003`: Under `PreserveErrorChannel`, a non-`BottomType` error channel is represented by
`ErrorPrimalSlot` and maps to `DerivativeErrorSlot` with the identical error type. The default
language rule does not differentiate thrown error values. A registered error policy may define a
different mapping explicitly; `RejectThrowingCallable` returns a signature failure instead of
silently dropping the channel.

`DIF-SIG-FWD-004`: Every `ConstRefMode(r)` slot, active or inactive, requires a registered
physical-operand derivative rule selected by the complete canonical passing mode (the
`PhysicalOperand(r)` domain plus `ReadAccess`), source type, differentiation mode, and order. The
resulting slot plan has
`RegisteredDerivativeRole(rule)` and the rule proves the derivative callable's location identity,
access, lifetime, address-space, source-provenance, and alias behavior. It cannot load the primal,
substitute an `InMode` parameter, create a temporary, or erase `isPhysicalStorage`. Absence of a
rule produces `MissingPhysicalOperandDerivativeRule`; it never falls through to
`DIF-SIG-FWD-001`.

### Backward mode

The proposed default backward mapping is explicit in the following table. `Pair<T>` means the
registered primal/differential pair and `D<T>` means the looked-up differential type.

| primal slot            | active backward slot                                                                 | inactive backward slot                                                               |
| ---------------------- | ------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------ |
| `InMode` parameter `T` | `InOutMode Pair<T>` accumulator                                                      | unchanged `InMode T` input                                                           |
| `OutMode T`            | `InMode D<T>` cotangent seed                                                         | dropped                                                                              |
| `InOutMode T`          | `InOutMode Pair<T>`                                                                  | `InMode T`                                                                           |
| `ConstRefMode(r) T`    | registered rule required for the complete physical mode (`r` plus `ReadAccess`)      | registered rule required for the complete physical mode (`r` plus `ReadAccess`)      |
| `RefMode(r) T`         | registered rule required for the complete physical mode (`r` plus `ReadWriteAccess`) | registered rule required for the complete physical mode (`r` plus `ReadWriteAccess`) |
| result `R`             | appended `InMode D<R>` seed                                                          | no result parameter                                                                  |
| preserved error `E`    | unchanged error output `E`                                                           | unchanged error output `E`                                                           |

Backward derivative functions return `VoidType`. The primal component of a pair accumulator is an input
and is not modified; the differential component is the output accumulator. A receiver is mapped by
the same rule as its explicit mode and remains a separate receiver-derived role in the map.

`DIF-SIG-BWD-001`: Every primal slot has exactly one `DerivativeSlotPlan`, including dropped slots
and a preserved error channel. `derivativeSlotOrder` is a duplicate-free bijection onto all produced
derivative callable slots: receiver first when present, parameters in source-key order (followed by a
result seed when backward mode creates one), then result and error outputs when present. Filtering
`DerivativeParameterSlot` alternatives gives the derivative declaration's parameter order. No
downstream pass rediscovers which parameter is a cotangent or mistakes receiver/result/error for an
ordinary parameter.

`DIF-SIG-BWD-002`: Aliasable `RefMode`, pointer-differential outputs, throwing functions, and other
unsupported role combinations fail signature transformation with named reasons. A target or IR pass
cannot silently choose a different signature.

`DIF-SIG-BWD-003`: `ConstRefMode(r)` has no default active or inactive backward mapping. A
registered physical-operand derivative rule must consume the complete structural passing mode and
state how primal and cotangent locations alias, which location requirements and access modes each
produced slot preserves, and how their lifetimes relate. Its plan uses
`RegisteredDerivativeRole(rule)` and preserves physical-location
identity unless the named rule proves a different registered transformation. Missing or rejected
rules produce the corresponding structured `DerivativeSignatureFailure`; treating the slot as
`InMode`, loading it, or manufacturing accumulator storage is invalid.

`DIF-SIG-003`: Forward/backward transformation is a pure, total query over a canonical callable
shape, mode, order, and registered rule environment. It produces the signature map or structured
failure; user-defined and synthesized derivatives are checked against the same result.

`DIF-SIG-004`: A map's `slots` domain equals the receiver, every expanded `ParameterKey`, result,
and the error channel exactly when that channel exists in the callable shape. Every
`DerivativeSlotPlan.primal` equals its map key. The union of the `derivatives` key domains is exactly
`derivativeSlotOrder` after adding `result.output`; each derivative slot occurs once in the
derivative signature, and its resolved type and passing mode equal its keyed
`DerivativeCallableSlotShape`. A forward active result maps
to `DerivativeResultSlot`; a backward result seed maps to an explicit
`DerivativeParameterSlot`; `result.output` is always `DerivativeResultSlot`, including the backward
`VoidType` result; and a preserved error maps to `DerivativeErrorSlot`. A receiver is never encoded as
parameter zero.

## Derivative providers

```text
CallableIdentity =
    DeclCallableIdentity(declaration: DeclId)
  | WitnessCallableIdentity(entry: RuntimeInterfaceRequirementKey)
  | DynamicCallableIdentity(owner: DeclId, slot: DynamicDispatchKey)
  | LambdaCallableIdentity(invoke: DeclId)
  | BuiltinCallableIdentity(rule: RuleId, operands: CanonicalArguments)

DerivativeProviderKey = {
    primal: CallableIdentity,
    specialization: CanonicalSpecializationSpine,
    mode: DifferentiationMode,
    order: DerivativeOrder,
    environment: SemanticEnvironmentId
}

DerivativeProviderSelectionContext = {
    access: VisibilityContext,
    allowedEffects: EffectAllowance,
    requiredCapabilities: CapabilityRequirement,
    contractSelection: ContractSelectionContext,
    errorPolicy: DifferentialErrorPolicy
}

DerivativeProviderRequestAt<S: WitnessTableState> = {
    key: DerivativeProviderKey,
    primal: CallableValue<S>,
    context: DerivativeProviderSelectionContext
}

DerivativeProviderRequest = DerivativeProviderRequestAt<Published>

DerivativeAssociationDirection =
    PrimalDeclaresDerivative
  | DerivativeDeclaresPrimal
  | ReciprocalDerivativeAssociation

DerivativeAssociationProof = {
    primal: CallableIdentity,
    primalSpecialization: CanonicalSpecializationSpine,
    derivative: DeclRef,
    mode: DifferentiationMode,
    order: DerivativeOrder,
    direction: DerivativeAssociationDirection,
    origin: Origin
}

DerivativeAssociationFailure =
    AssociationEndpointNotCallable(origin: Origin)
  | AssociationPrimalMismatch(expected: CallableIdentity,
                              actual: CallableIdentity)
  | AssociationDerivativeMismatch(expected: DeclRef,
                                  actual: DeclRef)
  | AssociationModeMismatch(expected: DifferentiationMode,
                            actual: DifferentiationMode)
  | AssociationOrderMismatch(expected: DerivativeOrder,
                             actual: DerivativeOrder)
  | AssociationSpecializationFailure(failure: GenericFailure)
  | AssociationSignatureMismatch(expected: CallableSignatureId,
                                 actual: CallableSignatureId)
  | ConflictingDerivativeAssociations(
        primal: CallableIdentity,
        mode: DifferentiationMode,
        order: DerivativeOrder,
        derivatives: NonEmpty<DeclRef>)
  | NonReciprocalDerivativeAssociation(primal: CallableIdentity,
                                       derivative: DeclRef)

TreatAsDifferentiableProof = {
    primal: DeclRef,
    mode: DifferentiationMode,
    order: DerivativeOrder,
    policy: RuleId,
    declarationOrigin: Origin,
    useOrigin: Origin
}

DynamicDerivativeDispatch = {
    owner: TypeId,
    primalSlot: DynamicDispatchKey,
    derivativeSlot: DynamicDispatchKey
}

DerivativeProviderAt<S: WitnessTableState> =
    UserDefinedDerivative(declaration: ResolvedDeclRefAt<S>,
                          association: DerivativeAssociationProof)
  | SynthesizedDerivative(output: SynthesizedDeclId,
                          synthesis: SynthesisKey)
  | WitnessDerivative(witness: SubtypeWitnessRef<S>,
                       entry: RuntimeInterfaceRequirementKey)
  | DynamicDerivative(dispatch: DynamicDerivativeDispatch)
  | BuiltinDerivative(rule: StandardEnvironmentRuleId,
                       inputs: CanonicalArguments,
                       witnessResolutions: WitnessResolutionSetAt<S>)
  | AssumedZeroDerivative(declaration: ResolvedDeclRefAt<S>,
                          assumption: TreatAsDifferentiableProof)

DerivativeProvider = DerivativeProviderAt<Published>

DerivativeProviderIdentity =
    UserDefinedDerivativeIdentity(declaration: DeclRef,
                                  primal: CallableIdentity,
                                  mode: DifferentiationMode,
                                  order: DerivativeOrder,
                                  direction: DerivativeAssociationDirection)
  | SynthesizedDerivativeIdentity(output: SynthesizedDeclId,
                                  synthesis: SynthesisKey)
  | WitnessDerivativeIdentity(witness: SubtypeWitnessId,
                              entry: RuntimeInterfaceRequirementKey)
  | DynamicDerivativeIdentity(dispatch: DynamicDerivativeDispatch)
  | BuiltinDerivativeIdentity(rule: StandardEnvironmentRuleId,
                              inputs: CanonicalArguments)
  | AssumedZeroDerivativeIdentity(declaration: DeclRef,
                                  mode: DifferentiationMode,
                                  order: DerivativeOrder,
                                  policy: RuleId)

DerivativeProviderCandidateKey =
    ProviderCandidateKey(request: DerivativeProviderKey,
                         provider: DerivativeProviderIdentity)
  | InvalidAssociationCandidateKey(request: DerivativeProviderKey,
                                   declaration: DeclRef,
                                   origin: Origin)

DerivativeProviderCandidateId = ContentId<DerivativeProviderCandidateKey>

DerivativeProviderCandidateAt<S: WitnessTableState> = {
    id: DerivativeProviderCandidateId,
    key: DerivativeProviderCandidateKey,
    provider: Option<DerivativeProviderAt<S>>
}

DerivativeProviderAvailabilityEvidence =
    DeclaredDerivativeProviderAccess(VisibilityEvidence)
  | RegisteredDerivativeProviderAccess(rule: StandardEnvironmentRuleId,
                                       environment: StandardEnvironmentId)

DerivativeProviderCapabilityObligationAt<S: WitnessTableState> = {
    request: DerivativeProviderRequestAt<S>,
    provider: DerivativeProviderIdentity,
    required: CapabilityRequirement,
    preInferenceActual: CapabilityRequirement,
    preInferenceProof: CapabilityImplicationProof
}

DerivativeProviderCapabilityDependencyAt<S: WitnessTableState> =
    CallableCapabilityDependency(declaration: ResolvedDeclRefAt<S>)
  | WitnessEntryCapabilityDependency(witness: SubtypeWitnessRef<S>,
                                     entry: RuntimeInterfaceRequirementKey)
  | DynamicSlotCapabilityDependency(owner: TypeId,
                                    slot: DynamicDispatchKey)
  | SynthesizedCapabilityDependency(output: SynthesizedDeclId)

DerivativeProviderEffectiveCapabilitySourceAt<S: WitnessTableState> =
    CallableEffectiveCapability(contract: EffectiveCallableContractId)
  | WitnessEntryEffectiveCapability(witness: SubtypeWitnessRef<S>,
                                    entry: RuntimeInterfaceRequirementKey,
                                    requirement: CapabilityRequirement)
  | DynamicSlotEffectiveCapability(owner: TypeId,
                                   slot: DynamicDispatchKey,
                                   requirement: CapabilityRequirement)
  | RegisteredEffectiveCapability(registration: RegisteredDataOperationRegistration,
                                  requirement: CapabilityRequirement)

DerivativeProviderEffectiveCapabilityProofAt<S: WitnessTableState> = {
    obligation: DerivativeProviderCapabilityObligationAt<S>,
    source: DerivativeProviderEffectiveCapabilitySourceAt<S>,
    effectiveActual: CapabilityRequirement,
    effectiveProof: CapabilityImplicationProof
}

DerivativeProviderCapabilityCheckAt<S: WitnessTableState> =
    PendingDerivativeProviderCapability {
        obligation: DerivativeProviderCapabilityObligationAt<S>,
        dependency: DerivativeProviderCapabilityDependencyAt<S>
    }
  | ValidatedDerivativeProviderCapability(
        DerivativeProviderEffectiveCapabilityProofAt<S>)

DerivativeProviderCompatibilityProofAt<S: WitnessTableState> = {
    request: DerivativeProviderRequestAt<S>,
    signatureMap: DerivativeSignatureMapId,
    signature: FuncTypeEqualityProof,
    providerSelectionContract: PreInferenceCallableContract,
    allowedEffects: EffectAllowance,
    effectValidation: EffectAllowanceValidation,
    effectUse: EffectUse<S>,
    capabilitySelection: CapabilitySelectionAt<S>,
    ordinaryCapabilities: DerivativeProviderCapabilityCheckAt<S>,
    availability: DerivativeProviderAvailabilityEvidence,
    errorPolicy: CanonicalFieldEquality<DifferentialErrorPolicy>,
    evidenceOperands: DifferentialEvidenceOperandPlanAt<S>
}

DerivativeProviderCompatibilityProof =
    DerivativeProviderCompatibilityProofAt<Published>

DerivativeProviderFailureAt<S: WitnessTableState> =
    NoDerivativeProvider(request: DerivativeProviderRequestAt<S>)
  | GenericDerivativeProviderFailure(provider: DerivativeProviderAt<S>,
                                     failure: GenericFailure)
  | DerivativeProviderSignatureMismatch(provider: DerivativeProviderAt<S>,
                                        expected: CallableSignatureId,
                                        actual: CallableSignatureId)
  | DerivativeProviderNotAccessible(provider: DerivativeProviderAt<S>,
                                    decision: VisibilityDecision)
  | DerivativeProviderRegisteredRuleUnavailable(
        rule: StandardEnvironmentRuleId,
        environment: StandardEnvironmentId)
  | DerivativeProviderEffectMismatch(provider: DerivativeProviderAt<S>,
                                     allowed: EffectAllowance,
                                     actual: EffectSet)
  | DerivativeProviderCapabilityMismatch(
        provider: DerivativeProviderAt<S>,
        required: CapabilityRequirement,
        preInferenceActual: CapabilityRequirement)
  | DerivativeProviderUnavailableInWorld(
        provider: DerivativeProviderAt<S>,
        world: BooleanCapabilityPredicate,
        sources: NonEmpty<ResolvedConcreteAvailability>,
        combinedRequirement: CapabilityRequirement,
        failure: CapabilityFailure)
  | DerivativeProviderEffectiveCapabilityMismatch(
        provider: DerivativeProviderAt<S>,
        obligation: DerivativeProviderCapabilityObligationAt<S>,
        effectiveActual: CapabilityRequirement,
        failure: CapabilityFailure)
  | DerivativeProviderErrorPolicyMismatch(
        provider: DerivativeProviderAt<S>,
        expected: DifferentialErrorPolicy,
        actual: DifferentialErrorPolicy)
  | InvalidDerivativeProviderAssociation(declaration: DeclRef,
                                         reason: DerivativeAssociationFailure)
  | DerivativeProviderSynthesisFailure(request: DerivativeProviderRequestAt<S>,
                                       error: ErrorId)

DerivativeProviderFailure = DerivativeProviderFailureAt<Published>

ApplicableDerivativeProviderAt<S: WitnessTableState> = {
    candidate: DerivativeProviderCandidateAt<S>,
    provider: DerivativeProviderAt<S>,
    signatureMap: DerivativeSignatureMap,
    proof: DerivativeProviderCompatibilityProofAt<S>
}

DerivativeProviderPriorityDimension =
    ExplicitAssociationPriority(policy: StandardEnvironmentRuleId)
  | GenericSpecificityPriority
  | WitnessRoutePriority
  | RegisteredDerivativeProviderPriority(rule: StandardEnvironmentRuleId,
                                         inputs: CanonicalArguments)

DerivativeProviderPriorityPremiseAt<S: WitnessTableState> =
    ExplicitAssociationPremise(preferred: DerivativeProviderCandidateId,
                               other: DerivativeProviderCandidateId,
                               association: DerivativeAssociationProof,
                               policy: StandardEnvironmentRuleId)
  | GenericSpecificityPremise(preferred: DerivativeProviderCandidateId,
                              other: DerivativeProviderCandidateId,
                              proof: GenericConstraintImplicationProof)
  | WitnessRoutePremise(preferred: DerivativeProviderCandidateId,
                        other: DerivativeProviderCandidateId,
                        proof: FacetPriorityProof)
  | RegisteredProviderPriorityPremise(
        preferred: DerivativeProviderCandidateId,
        other: DerivativeProviderCandidateId,
        rule: StandardEnvironmentRuleId,
        inputs: CanonicalArguments)

DerivativeProviderPriorityObservationAt<S: WitnessTableState> =
    LeftPreferred(DerivativeProviderPriorityPremiseAt<S>)
  | RightPreferred(DerivativeProviderPriorityPremiseAt<S>)
  | EqualPriority(rule: DerivativeProviderPriorityDimension)
  | UnorderedPriority(rule: DerivativeProviderPriorityDimension,
                      reason: RuleId)

DerivativeProviderComparisonOutcome =
    LeftBetter | RightBetter | SemanticallyEquivalent | Incomparable

DerivativeProviderComparisonProofAt<S: WitnessTableState> = {
    request: DerivativeProviderRequestAt<S>,
    left: DerivativeProviderCandidateId,
    right: DerivativeProviderCandidateId,
    observations:
        CanonicallyOrderedMap<DerivativeProviderPriorityDimension,
                              DerivativeProviderPriorityObservationAt<S>>,
    outcome: DerivativeProviderComparisonOutcome
}

DerivativeProviderComparisonProof =
    DerivativeProviderComparisonProofAt<Published>

DerivativeProviderCandidateResultAt<S: WitnessTableState> =
    ApplicableProviderCandidate(ApplicableDerivativeProviderAt<S>)
  | RejectedProviderCandidate {
        candidate: DerivativeProviderCandidateAt<S>,
        failure: DerivativeProviderFailureAt<S>,
        diagnostics: DiagnosticSet
    }

SelectedDerivativeProviderAt<S: WitnessTableState> = {
    winner: ApplicableDerivativeProviderAt<S>,
    maximality:
        CanonicallyOrderedMap<DerivativeProviderCandidateId,
                              DerivativeProviderComparisonProofAt<S>>,
    considered:
        CanonicallyOrderedMap<DerivativeProviderCandidateId,
                              DerivativeProviderCandidateResultAt<S>>
}

DerivativeProviderCandidatePair = {
    first: DerivativeProviderCandidateId,
    second: DerivativeProviderCandidateId
} where first < second

ApplicableDerivativeProvider = ApplicableDerivativeProviderAt<Published>
SelectedDerivativeProvider = SelectedDerivativeProviderAt<Published>

DerivativeProviderCapabilityValidationResultAt<S: WitnessTableState> =
    ValidatedDerivativeProviderCapabilities(SelectedDerivativeProviderAt<S>)
  | RejectedDerivativeProviderCapabilities(
        selection: SelectedDerivativeProviderAt<S>,
        failures: NonEmpty<DerivativeProviderFailureAt<S>>)
  | RecoveredDerivativeProviderCapabilities(
        selection: SelectedDerivativeProviderAt<S>,
        errors: NonEmpty<ErrorId>)

RejectedDerivativeProviderSearchAt<S: WitnessTableState> = {
    considered:
        CanonicallyOrderedMap<DerivativeProviderCandidateId,
                              DerivativeProviderCandidateResultAt<S>>,
    failure: DerivativeProviderFailureAt<S>
}

AmbiguousDerivativeProviderSearchAt<S: WitnessTableState> = {
    maximal: NonEmpty<ApplicableDerivativeProviderAt<S>>,
    incomparability:
        CanonicallyOrderedMap<DerivativeProviderCandidatePair,
                              DerivativeProviderComparisonProofAt<S>>,
    considered:
        CanonicallyOrderedMap<DerivativeProviderCandidateId,
                              DerivativeProviderCandidateResultAt<S>>
}

DerivativeProviderResultAt<S: WitnessTableState> =
    Selected(SelectedDerivativeProviderAt<S>)
  | RejectedProviderSearch(RejectedDerivativeProviderSearchAt<S>)
  | AmbiguousProviderSearch(AmbiguousDerivativeProviderSearchAt<S>)
  | RecoveredProviderSearch {
        selected: Option<SelectedDerivativeProviderAt<S>>,
        considered:
            CanonicallyOrderedMap<DerivativeProviderCandidateId,
                                  DerivativeProviderCandidateResultAt<S>>,
        errors: NonEmpty<ErrorId>
    }

DerivativeProviderResult = DerivativeProviderResultAt<Published>

DerivativeSurfaceKey = {
    mode: DifferentiationMode,
    order: DerivativeOrder
}

EffectiveDifferentiabilityContractAt<S: WitnessTableState> = {
    signature: CallableSignatureId,
    promise: DifferentiabilityPromise,
    shape: CallableDifferentialShapeAt<S>,
    surfaces:
        CanonicallyOrderedMap<DerivativeSurfaceKey,
                              SelectedDerivativeProviderAt<S>>
}

EffectiveDifferentiabilityContract =
    EffectiveDifferentiabilityContractAt<Published>

EffectiveDifferentiabilityContractFailureAt<S: WitnessTableState> =
    ContractShapeRejected(CallableDifferentialShapeFailureAt<S>)
  | PromisedSurfaceRejected(surface: DerivativeSurfaceKey,
                            failure: DerivativeProviderFailureAt<S>)
  | PromisedSurfaceAmbiguous(
        surface: DerivativeSurfaceKey,
        providers: NonEmpty<ApplicableDerivativeProviderAt<S>>)
  | ContractSignatureMismatch(expected: CallableSignatureId,
                              actual: CallableSignatureId)

EffectiveDifferentiabilityContractResultAt<S: WitnessTableState> =
    BuiltDifferentiabilityContract(EffectiveDifferentiabilityContractAt<S>)
  | RejectedDifferentiabilityContract(
        EffectiveDifferentiabilityContractFailureAt<S>)
  | RecoveredDifferentiabilityContract(
        EffectiveDifferentiabilityContractAt<S>,
        NonEmpty<ErrorId>)

EffectiveDifferentiabilityContractResult =
    EffectiveDifferentiabilityContractResultAt<Published>
```

`DIF-PRV-001`: Provider lookup consumes a `DerivativeProviderRequestAt<S>` and considers
forward/backward association spellings, primal-substitute associations, witness-table entries,
dynamic derivative slots, registered builtins, and permitted synthesis together. A provider is
applicable only when its generic binder, receiver/parameter correspondence, derivative signature
map, visibility, pre-inference selection effects, optional concrete availability, ordinary
pre-inference capability promise, and error policy validate against the request's exact callable
value and selection context. Selection never requests a local effective contract.

`DIF-PRV-002`: Bidirectional custom-derivative associations have one canonical key. Both ends name
the same specialized callable identities and mode/order; conflicting or duplicate associations are
diagnosed independently of declaration/import order.

`DIF-PRV-003`: Provider applicability and ranking are separate. Applicability constructs a complete
`DerivativeProviderCompatibilityProofAt<S>`, including the stage-specific differential-evidence
operand plan. Ranking compares only applicable candidates under the finite set of
`DerivativeProviderPriorityDimension` values registered by the request's language environment.
For every active dimension the comparison proof records `LeftPreferred`, `RightPreferred`, equal,
or unordered with its typed premise. `leftNoWorse(proof)` is derived exactly when no observation
prefers the right or is unordered; `rightNoWorse(proof)` is symmetric. `outcome` is revalidated from
those derived predicates: strict preference requires one no-worse direction and not the other, so
the quotient by `SemanticallyEquivalent` is a partial order. No stored boolean is a second ranking
authority.

A compatible explicitly associated provider may dominate automatic synthesis only when the
version policy supplies the corresponding proof. Two incomparable visible providers are ambiguous.
Source order, candidate discovery order, module load order, and “first attribute found” are not
priority dimensions.

`DIF-PRV-004`: `TreatAsDifferentiable` creates `AssumedZeroDerivative` with an explicit trust proof
and call-site provenance. It is not ordinary body synthesis, not `no_diff`, and not evidence that
the primal body obeys derivative rules.

`DIF-PRV-005`: Interface requirement matching compares the promised modes/order and derivative
signature maps. A witness derivative retains the interface-subtype witness and derivative entry
key. A dynamic derivative retains its owner plus distinct primal and derivative
`DynamicDispatchKey` values. Neither resolves to whichever concrete derivative happened to be
visible during checking.

`DIF-PRV-006`: `CallableIdentity` is the stable dispatch identity and contains no
`CanonicalSpecializationSpine`. A declaration or lambda identity stores its `DeclId`, a witness
identity stores the complete kind-indexed runtime entry key, a dynamic identity stores owner and
slot declaration identity, and a builtin identity stores its registered rule and static operands.
The specialized dynamic owner type is retained on the request's `CallableValue`; its nominal
declaration enters `CallableIdentity` and its generic arguments enter the specialization spine.
Substitutions that are
structurally part of a witness entry key or builtin operand remain in that value;
`DerivativeProviderKey.specialization` is the sole authority for the callable's generic binder
frames.

`DIF-PRV-007`: An `ApplicableDerivativeProviderAt<S>` is constructible only when its proof names the
same stage-bound request and `ContentId(signatureMap)` as the candidate. Its stored
`proof.evidenceOperands` is the exact plan derived from the request's callable shape. The signature
proof's required endpoint is `signatureMap.derivative` and its implementation endpoint is the
provider's checked signature; `providerSelectionContract.signature` is that implementation
signature. `effectValidation` checks only `providerSelectionContract.selectionEffects` against the
request allowance, and `effectUse` is the provider's exact keyed pre-inference use retained for
ordinary effect inference/post-fixpoint validation. A declared/witness/dynamic provider retains the
payload of its successful access decision; a registered builtin retains the exact rule/environment
resolution.

The `capabilitySelection.region` is exactly
`request.context.contractSelection.assumption`. Its ordinary-use map contains the provider's exact
pre-inference inferred-capability use, while its concrete selection is built only from the
provider's resolved `providerSelectionContract.concreteAvailability` sources. The
`ordinaryCapabilities` obligation proves `request.context.requiredCapabilities` entails
`providerSelectionContract.inferredCapabilities`; it does not prove availability in the current
region and does not contain a concrete source. These three proof roles cannot substitute for one
another even when their formulas are structurally equal. The obligation repeats the exact request
and provider identity, its `required`/`preInferenceActual` equal those two requirements, and its
implication proof has those endpoints in that order.

For a user-defined provider, the association's primal, specialization, mode, and order equal the
request's `key` and its derivative equals the provider declaration's `target`. For an assumed-zero
provider, the trust proof's primal equals the provider declaration's `target` and its mode/order
equal the request key. These equalities are validation obligations, not duplicate selection
authorities.

`DIF-PRV-008`: `WitnessDerivative.witness` has the classifier that owns `entry`, and its resolution
set contains exactly the stage-permitted table definitions reachable from that witness operation.
Construction publication rewrites only operational definition resolutions. Provider kind, witness
ID, entry key, signature map, and association identity remain unchanged.

Direct user/assumed providers and builtin providers obey the same dependency rule: their resolution
sidecars are exactly the definitions required by witness evidence in their specialization/static
operands. The sidecars are excluded from `CallableIdentity` and provider-search identity but are
retained by the selected executable provider.

`DIF-PRV-009`: Every provider failure names the rejected candidate and exact failed premise where a
candidate existed. `DerivativeProviderNotAccessible.decision` is `Denied`; a registered-rule
failure names the request environment in which the exact rule did not resolve; the effect actual is
the candidate's pre-inference selection effect set, and the ordinary-capability actual is its
pre-inference requirement. Signature and error-policy actuals equal its checked callable shape. A
world-unavailability failure stores the request's exact boolean region, complete concrete source
list, and recomputed combined requirement. An effective-capability failure stores the original
ordinary obligation and post-fixpoint actual. An invalid association uses an
`InvalidAssociationCandidateKey` and cannot
manufacture a `DerivativeProviderAt<S>`. No failure alternative can appear in
`ApplicableDerivativeProviderAt<S>` or a differentiation expression.

`DIF-PRV-010`: An `EffectiveDifferentiabilityContractAt<S>` repeats one signature across its
promise and callable shape. Its surface-map domain is exactly the promised mode/order set after
versioned mode implication and order-policy expansion: `Exactly(n)` requires order `n`, while
`Through(n)` requires every positive order at most `n`. Each selected provider's winner proof request key
has the map key's mode/order and the same primal signature/environment; its request has the exact
callable value being contracted and a compatible derivative signature map. Missing, failed, or
ambiguous surfaces make contract construction fail; they are not omitted from the map.

`DIF-PRV-011`: `DerivativeProviderRequestAt<S>.primal` is executable at stage `S`.
`callableIdentity(primal.dispatch) = key.primal`, and the dispatch's canonical specialization spine
equals `key.specialization`; witness calls retain the exact `SubtypeWitnessRef<S>`, dynamic calls retain
owner/slot, lambdas retain their invoke identity, and builtin/direct calls retain their resolution
sidecars. The access, effect, ordinary-capability, concrete-availability, and error-policy proofs in
a successful candidate have exactly `request.context` as their use-side endpoints. Stable identity
projection cannot be used to reconstruct or replace this operational callable value.

`DIF-PRV-012`: `DynamicDerivative(dispatch)` is applicable only when the request primal dispatch is
`DynamicSlot(dispatch.owner, dispatch.primalSlot)`, the owner's registered derivative-surface map
associates that primal slot and requested mode/order with exactly `dispatch.derivativeSlot`, and the
derivative slot's canonical signature equals the selected signature map's derivative signature.
Overrides reuse both registered keys; source order, visible concrete overrides, and compact ABI slot
indices cannot select or identify the derivative.

`DIF-PRV-013`: A provider candidate satisfies `id = ContentId(key)`. A valid provider candidate's
key contains exactly `providerIdentity(provider)`, which erases only stage-specific resolution
sidecars and source presentation. Each `considered` map key equals its candidate ID and contains
every discovered candidate exactly once, including rejected candidates. Equivalent duplicate
discoveries coalesce only when their candidate records are byte-identical; an inconsistent
duplicate is a validation failure.

`DIF-PRV-014`: Let `applicable` be the candidates whose considered result is
`ApplicableProviderCandidate`, and let `maximal` contain those for which no applicable candidate is
strictly better. `Selected.winner` is the canonical representative of the single maximal semantic-
equivalence class. Its `maximality` map compares it with every other applicable candidate and every
proof outcome is `LeftBetter` or `SemanticallyEquivalent`. If multiple non-equivalent maxima remain,
`AmbiguousProviderSearch.maximal` lists them in candidate-ID order and `incomparability` contains a
validated proof for every unordered maximal pair. Deterministic ordering is diagnostic presentation,
never semantic preference.

`DIF-PRV-015`: `RejectedProviderSearch` is returned only when no applicable candidate exists;
`NoDerivativeProvider` is permitted only when its considered set is empty. Otherwise its failure is
selected from rejected candidates by a named diagnostic-progress relation that cannot affect
provider priority. `RecoveredProviderSearch` retains all considered candidates and root errors; any
optional selected value still satisfies `DIF-PRV-014` after excluding recovery-only candidates.

`DIF-PRV-016`: Initial provider selection stores `PendingDerivativeProviderCapability` whenever the
provider's effective ordinary contract depends on a local callable, witness entry, dynamic slot, or
synthesized callable that has not reached its capability fixpoint. Its dependency alternative is
the exact scheduler subject. An imported/frozen callable, witness entry, or dynamic slot and a
registered builtin are immediately `ValidatedDerivativeProviderCapability`, because each already
has a final ordinary requirement. None of these states alters concrete availability or ranking.

After all relevant `InferCapabilities` SCCs stabilize,
`ValidateDerivativeProviderCapabilitiesAt<S>` creates a new immutable selection. For each pending
obligation it resolves the provider's exact `DerivativeProviderEffectiveCapabilitySourceAt<S>`,
projects `effectiveActual` from that source, and proves the obligation's `required` entails that
value. A callable source projects `Closed(effectiveCapabilities(contract))`; witness-entry and
dynamic sources project their published effective requirements; a registered source projects its
final registered ordinary requirement. A mismatch returns
`DerivativeProviderEffectiveCapabilityMismatch`; it never rewrites the concrete selection or drops
the provider silently. The dependency/source alternative must match the provider kind and exact
declaration, witness entry, dynamic slot, synthesized output, or registration; a contract from a
different provider with an equal formula is not valid evidence. `effectiveProof.premise` equals the
obligation's `required` and `effectiveProof.conclusion = effectiveActual`.

`DIF-PRV-017`: A `BuiltDifferentiabilityContract` and a publishable differentiation/body result
contain no pending provider capability check. Every applicable provider preserved in their selected
results has the appropriate validated alternative and endpoint-correct effective proof. The
post-fixpoint validation query depends on inference, but provider discovery/applicability/ranking
does not depend on that query, so it cannot create a cycle inside the capability-inference SCC.

## Differentiation and detach-derivative expressions

```text
DifferentiationExprAt<S: WitnessTableState> =
    ForwardDifferentiateExpr(value: CallableValue<S>,
                             selection: SelectedDerivativeProviderAt<S>)
  | BackwardDifferentiateExpr(value: CallableValue<S>,
                              selection: SelectedDerivativeProviderAt<S>)
  | DetachExpr(value: TypedExpr,
                  boundary: DetachDerivativeBoundaryAt<S>)

DifferentiationExpr = DifferentiationExprAt<Published>

DetachDerivativeBoundaryKeyAt<S: WitnessTableState> = {
    inputType: TypeId,
    outputType: TypeId,
    discarded: Option<ValueDifferentialInfoAt<S>>
}

DetachDerivativeBoundaryIdAt<S: WitnessTableState> =
    ContentId<DetachDerivativeBoundaryKeyAt<S>>

DetachDerivativeBoundaryAt<S: WitnessTableState> = {
    id: DetachDerivativeBoundaryIdAt<S>,
    key: DetachDerivativeBoundaryKeyAt<S>,
    origin: Origin
}

DetachDerivativeBoundaryKey = DetachDerivativeBoundaryKeyAt<Published>
DetachDerivativeBoundaryId = DetachDerivativeBoundaryIdAt<Published>
DetachDerivativeBoundary = DetachDerivativeBoundaryAt<Published>

DetachDerivativeFailure =
    OutsideDifferentiabilityContext(origin: Origin)
  | DetachDerivativeTypeMismatch(input: TypeId, output: TypeId)
  | DetachDerivativeDifferentialMismatch(type: TypeId,
                                     witness: SubtypeWitnessId)
  | DetachDerivativeOnUnsupportedStorage(storage: StorageRef)
  | RegisteredDetachDerivativeRejection(rule: RuleId, origin: Origin)

DifferentiationCheckFailureAt<S: WitnessTableState> =
    DifferentiationOperandNotCallable(origin: Origin, classifier: Classifier)
  | DifferentiationShapeRejected(CallableDifferentialShapeFailureAt<S>)
  | DifferentiationSignatureRejected(DerivativeSignatureFailure)
  | DifferentiationProviderRejected(RejectedDerivativeProviderSearchAt<S>)
  | DifferentiationProviderAmbiguous(AmbiguousDerivativeProviderSearchAt<S>)
  | DifferentiationModeNotPromised(mode: DifferentiationMode,
                                   promise: DifferentiabilityPromise)
  | DetachDerivativeRejected(DetachDerivativeFailure)

DifferentiationCheckResultAt<S: WitnessTableState> =
    CheckedDifferentiation(DifferentiationExprAt<S>)
  | RejectedDifferentiation(DifferentiationCheckFailureAt<S>)
  | RecoveredDifferentiation(DifferentiationExprAt<S>,
                             NonEmpty<ErrorId>)

DifferentiationCheckResult = DifferentiationCheckResultAt<Published>
```

`DIF-EXP-001`: `fwd_diff(f)` and `bwd_diff(f)` first check `f` as a callable value, preserve its
dispatch/specialization identity, transform the signature, and resolve a provider. Their result is
a callable value with the derivative signature and provider dispatch. Applying it later uses
ordinary call/overload argument rules; the operator itself does not parse or mutate the later call.

`DIF-EXP-002`: `no_diff(e)` evaluates the same primal expression once and preserves all its ordinary
effects, capabilities, exceptions, and access operations. It inserts a typed `DetachExpr`
boundary that changes derivative activity only. It is valid only in a declared differentiability
context and cannot erase a non-differentiability diagnostic unrelated to derivative flow.

`DIF-EXP-003`: Assigning an active value to an inactive storage path is a derivative-loss failure
unless the value passes through an explicit detach-derivative boundary or a registered operation whose
contract declares derivative consumption. Physical versus abstract storage remains governed by
chapter 5; activity does not make abstract storage referenceable.

`DIF-EXP-004`: A call from differentiable code to a nondifferentiable callable with active inputs or
an active result requires an explicit detach-derivative/no-diff call boundary or a registered provider.
Whether values are observably active is dataflow over `DerivativeActivityAt<S>`, not a syntactic
search for a modifier.

`DIF-EXP-005`: A successful differentiate expression contains only
`SelectedDerivativeProviderAt<S>`; rejected, ambiguous, recovered-provider-only, scheduler blocking,
and cancellation states cannot inhabit a successful typed expression. The winner proof's request has
`primal = value` and the mode written by the expression. A detach-derivative boundary satisfies
`id = ContentId(key)`, has equal input/output primal types, and carries the exact stage-appropriate
differential evidence being discarded when that evidence exists.

`DIF-EXP-006`: `CheckDifferentiationAt<S>` is total at semantic completion. It returns
`CheckedDifferentiation`, one structured `RejectedDifferentiation` alternative that preserves the
failed shape/signature/provider/detach-derivative premise, or `RecoveredDifferentiation` with a valid
error-bearing typed expression. Dependency waiting is only the enclosing scheduler
`QueryStep.Blocked`; cancellation abandons the unpublished attempt. A provider rejection or
ambiguity retains its entire considered-candidate map and therefore cannot disappear into
diagnostics while the query returns an apparently successful callable.

## Activity and body validation

```text
DerivativeActivityAt<S: WitnessTableState> =
    InactiveActivity(reason: DifferentialInactivityReason)
  | ActiveActivity(info: ValueDifferentialInfoAt<S>,
                   sources: CanonicallyOrderedSet<PrimalSlotKey>)
  | MixedActivity(active: ValueDifferentialInfoAt<S>,
                   inactiveOrigins: OriginSet)
  | ActivityError(ErrorId)

DerivativeActivity = DerivativeActivityAt<Published>

DerivativeUseKey = {
    owner: DeclRef,
    origin: Origin,
    ordinal: UInt32
}

DerivativeUseId = ContentId<DerivativeUseKey>

DerivativeUseOperationAt<S: WitnessTableState> =
    ProviderDerivativeUse(request: DerivativeProviderRequestAt<S>)
  | DetachDerivativeUse(boundary: DetachDerivativeBoundaryIdAt<S>)
  | RegisteredDerivativeUse(rule: RuleId, inputs: CanonicalArguments)

DerivativeUseAt<S: WitnessTableState> = {
    key: DerivativeUseKey,
    operation: DerivativeUseOperationAt<S>
}

DerivativeUseGraphAt<S: WitnessTableState> = {
    root: DeclRef,
    rootWitnessResolutions: WitnessResolutionSetAt<S>,
    uses: CanonicallyOrderedMap<DerivativeUseId, DerivativeUseAt<S>>
}

DerivativeUse = DerivativeUseAt<Published>
DerivativeUseGraph = DerivativeUseGraphAt<Published>

CallableDifferentiabilityValidationAt<S: WitnessTableState> = {
    callable: DeclRef,
    shape: CallableDifferentialShapeAt<S>,
    uses: DerivativeUseGraphAt<S>,
    providers:
        CanonicallyOrderedMap<DerivativeUseId, SelectedDerivativeProviderAt<S>>,
    diagnostics: DiagnosticSet
}

CallableDifferentiabilityValidation =
    CallableDifferentiabilityValidationAt<Published>

CallableDifferentiabilityValidationFailureAt<S: WitnessTableState> =
    BodyProviderRejected(use: DerivativeUseId,
                         failure: DerivativeProviderFailureAt<S>)
  | BodyProviderAmbiguous(
        use: DerivativeUseId,
        maximal: NonEmpty<ApplicableDerivativeProviderAt<S>>)
  | InvalidDerivativeActivityJoin(origin: Origin, reason: RuleId)
  | DerivativeActivityLoss(origin: Origin, destination: StorageRef)
  | UnsupportedDerivativeBodyOperation(rule: RuleId, origin: Origin)
  | RecursiveDerivativeBodyFailure(cycle: NonEmpty<QueryKey>)

CallableDifferentiabilityValidationResultAt<S: WitnessTableState> =
    ValidatedDifferentiableBody(CallableDifferentiabilityValidationAt<S>)
  | RejectedDifferentiableBody(
        NonEmpty<CallableDifferentiabilityValidationFailureAt<S>>,
        diagnostics: DiagnosticSet)
  | RecoveredDifferentiableBody(CallableDifferentiabilityValidationAt<S>,
                                NonEmpty<ErrorId>)

CallableDifferentiabilityValidationResult =
    CallableDifferentiabilityValidationResultAt<Published>
```

`DIF-BDY-001`: Activity starts at active callable slots and propagates through registered operation
rules. A detach-derivative produces inactive output while retaining the input's use edge. A join uses
the declared finite activity lattice and preserves mixed provenance for diagnostics.

`DIF-BDY-002`: Each differentiable call/use records its exact stage-bound
`DerivativeProviderRequestAt<S>`. A completed validation has one successful selected provider whose
winner's proof names that request for every `ProviderDerivativeUse` and no provider entry for detach-derivative
or registered non-provider uses. Pending provider queries exist only as scheduler dependency edges;
they are not graph payloads. Recursive and mutually recursive call graphs are solved by the
scheduler's SCC policy; mutable visited sets or attribute-local dictionaries cannot decide success.

`DIF-BDY-003`: Loop, side-effect, mutation, atomic, resource, and control-flow restrictions are
registered validation rules with structured premises. A loop-bound/max-iteration promise is stored
in the validated body and frontend IR, not consulted for the first time during backward-mode code
generation.

`DIF-BDY-004`: Every use map key equals `ContentId(use.key)`, every `use.key.owner` equals `root`,
`rootWitnessResolutions` is the minimal stage-correct set required by `root.specializations`, and
ordinals follow stable origin plus semantic child-role order. The provider-map domain is exactly
the IDs whose operation is `ProviderDerivativeUse`, and each selected provider's winner proof request
equals that operation's request. Thus task order and query-resumption order cannot affect graph
identity or provider association.

`DIF-BDY-005`: For every committed provider use, the enclosing callable's direct capability-use
graph contains the exact keyed union of
`selection.winner.proof.capabilitySelection.inferredCapabilityUses` once. The provider's concrete
source list and region proof remain selection evidence and never enter that graph. Equal ordinary
and concrete formulas still retain both roles, and repeated traversal of the selected provider's
diagnostic `considered` map cannot duplicate the winner's ordinary use. The direct effect-use graph
likewise contains `selection.winner.proof.effectUse` exactly once; its post-fixpoint validation uses
the ordinary chapter 5 effect-obligation rules rather than a concrete capability proof.

## Visibility, effects, capabilities, and interfaces

`DIF-CON-001`: A derivative surface's effective visibility is the meet of the primal, provider,
every referenced differential type/conformance, and synthesized declaration visibility. A public
surface may depend only on exported semantic environments and witness values.

`DIF-CON-002`: Provider selection uses `selectionEffects`, the pre-inference ordinary requirement,
and separately resolved concrete availability. The ordinary requirement becomes a keyed use and a
compatibility obligation; only concrete availability filters the current boolean region.
Publication runs `ValidateDerivativeProviderCapabilitiesAt<S>` after capability inference and
validates the provider's effective ordinary contract. The selected effect use participates in the
parallel effect fixpoint/obligation validation. Generated derivative bodies participate in the same
effect/capability fixpoints as other synthesized callables.

`DIF-CON-003`: A differentiable interface requirement includes promise, participation, and
derivative-signature compatibility. A satisfying method supplies direct, custom, synthesized,
witness, builtin, or explicit assumed evidence under the same provider algebra. A plain callable
match without derivative evidence is insufficient.

`DIF-CON-004`: Differential associated types/methods are ordinary kind-indexed witness entries.
Their lookup uses `SubtypeWitnessId` and exact keys; no rule assumes declaration order or
special-cases a mutable witness-table representation.

## Scheduler products

The centralized scheduler registers at least:

```text
BuildDifferentialInfoAt<S>(type, environment)
    -> QueryStep<DifferentialInfoResultAt<S>>
BuildCallableDifferentialShapeAt<S>(signature, environment)
    -> QueryStep<CallableDifferentialShapeResultAt<S>>
TransformDerivativeSignatureAt<S>(shape, mode, order)
    -> QueryStep<DerivativeSignatureResult>
ResolveDerivativeProviderAt<S>(request: DerivativeProviderRequestAt<S>)
    -> QueryStep<DerivativeProviderResultAt<S>>
ValidateDerivativeProviderCapabilitiesAt<S>(
    selection: SelectedDerivativeProviderAt<S>)
    -> QueryStep<DerivativeProviderCapabilityValidationResultAt<S>>
BuildEffectiveDifferentiabilityContractAt<S>(callable: CallableValue<S>,
                                             environment,
                                             context: DerivativeProviderSelectionContext)
    -> QueryStep<EffectiveDifferentiabilityContractResultAt<S>>
CheckDifferentiationAt<S>(syntax: ExprCSTNodeId<Parsed>,
                          context: ExpressionCheckContextId)
    -> QueryStep<DifferentiationCheckResultAt<S>>
ValidateDifferentiableBodyAt<S>(callable, mode, order)
    -> QueryStep<CallableDifferentiabilityValidationResultAt<S>>
BuildAggregateDifferentialAt<S>(type, environment)
    -> QueryStep<AggregateDifferentialResultAt<S>>
```

The unqualified query names instantiate `S = Published`. Construction-stage variants are available
only inside their owning synthesis transaction. Every query value is a total semantic sum with
explicit success, rejection/ambiguity where applicable, and recovery. `QueryStep` adds exactly the
operational `Blocked(DependencySet)` alternative. Thus, for example, a differentiation check is
observably one of `Complete(Success(Checked | Rejected | Recovered, diagnostics))` or `Blocked`;
running and cancellation remain scheduler-internal and cannot inhabit semantic data.

`DIF-QRY-001`: Query keys include the semantic/standard environment, language version, exact primal
`CallableValue<S>`, access/effect/capability/error-policy selection context, mode, order,
specialization, and witness-use stage. A construction-stage key also includes its owning
synthesis/conformance transaction. Negative, ambiguous, operational, or published evidence from
one context/environment/stage cannot be reused in another.

`DIF-QRY-002`: Type/conformance and synthesized derivative SCCs use atomic identity allocation plus
validated publication. Body/provider recursion uses the declared scheduler policy and cannot expose
an incomplete derivative signature or witness table.

`DIF-QRY-003`: A query never converts a semantic rejection into `CheckResult.Recovered` merely to
make its result type inhabitable. `RejectedShape`, `RejectedDerivativeSignature`,
`RejectedProviderSearch`, `RejectedDifferentiation`, rejected contract/body/aggregate alternatives,
and every ambiguity are ordinary values inside `CheckResult.Success`; `CheckResult.Recovered` is
reserved for a structurally valid error-bearing value and retains its root `ErrorId`s. Consequently
every declared failure constructor is reachable through a producing query and unit-testable without
scraping diagnostics.

## IRReady and frontend IR

The `IRReady` node carries the selected provider and `DerivativeSignatureMap` explicitly:

```text
IRReadyDerivativeProviderOperands =
    StaticDerivativeProviderOperands
  | WitnessDerivativeProviderOperands(witness: IRReadyValueId)
  | DynamicDerivativeProviderOperands

IRReadyDifferentialEvidenceOperands = {
    values: CanonicallyOrderedMap<DifferentialEvidenceOperandKey, IRReadyValueId>,
    materializationOrder: NodeList<DifferentialEvidenceOperandKey>
}

IRReadyDerivativeEmissionPlan =
    ForwardDerivativeEmissionPlan(base: IRReadyValueId)
  | BackwardDerivativeEmissionPlan(applyFunction: IRReadyValueId,
                                   contextType: IRReadyValueId,
                                   backwardPropagateFunction: IRReadyValueId)

IRReadyDerivativeSelectionPlan = {
    primalCallable: IRReadyValueId,
    provider: ApplicableDerivativeProvider,
    providerOperands: IRReadyDerivativeProviderOperands,
    differentialEvidence: IRReadyDifferentialEvidenceOperands,
    emission: IRReadyDerivativeEmissionPlan
}

IRReadyDifferentiationPlan =
    ForwardDerivativeSelectionPlan(selection: IRReadyDerivativeSelectionPlan)
  | BackwardDerivativeSelectionPlan(selection: IRReadyDerivativeSelectionPlan)
  | DetachDerivativePlan(value: IRReadyValueId,
                         boundary: DetachDerivativeBoundaryId)

DerivativePrimalMaterialization =
    DirectPrimalCallable(ordinal: UInt32, target: IRSymbolRef)
  | WitnessPrimalCallable(ordinal: UInt32,
                          entry: RuntimeInterfaceRequirementKey)
  | DynamicPrimalCallable(ordinal: UInt32,
                          owner: TypeId,
                          slot: DynamicDispatchKey)
  | LambdaPrimalCallable(ordinal: UInt32, invoke: IRSymbolRef)
  | BuiltinPrimalCallable(ordinal: UInt32,
                          data: IRStaticData<IRBuiltinPrimalData>)

IRBuiltinPrimalData = {
    rule: RuleId,
    inputs: CanonicalArguments
}

IRDerivativeAssociationData = {
    mode: DifferentiationMode,
    order: DerivativeOrder,
    direction: DerivativeAssociationDirection
}

IRAssumedZeroDerivativeData = {
    mode: DifferentiationMode,
    order: DerivativeOrder,
    policy: RuleId
}

IRBuiltinDerivativeData = {
    rule: StandardEnvironmentRuleId,
    inputs: CanonicalArguments
}

DerivativeProviderInstSemanticMetadata =
    UserDefinedDerivativeProviderMetadata(
        target: IRSymbolRef,
        data: IRStaticData<IRDerivativeAssociationData>)
  | SynthesizedDerivativeProviderMetadata(
        target: IRSymbolRef,
        data: IRStaticData<SynthesisKey>)
  | WitnessDerivativeProviderMetadata(
        data: IRStaticData<RuntimeInterfaceRequirementKey>)
  | DynamicDerivativeProviderMetadata(
        data: IRStaticData<DynamicDerivativeDispatch>)
  | BuiltinDerivativeProviderMetadata(
        data: IRStaticData<IRBuiltinDerivativeData>)
  | AssumedZeroDerivativeProviderMetadata(
        target: IRSymbolRef,
        data: IRStaticData<IRAssumedZeroDerivativeData>)

DerivativeProviderMaterialization =
    NoAdditionalDerivativeProviderOperands
  | WitnessDerivativeProviderOperand(ordinal: UInt32,
                                     classifier: SubtypeWitnessForm)
  | DynamicDerivativeProviderOperand(primalOrdinal: UInt32,
                                     dispatch: DynamicDerivativeDispatch)

DifferentialEvidenceMaterialization = {
    key: DifferentialEvidenceOperandKey,
    ordinal: UInt32,
    shape: IRValueShape
}

DerivativeSelectionMaterializationPlan = {
    primal: DerivativePrimalMaterialization,
    provider: DerivativeProviderMaterialization,
    differentialEvidence:
        CanonicallyOrderedMap<DifferentialEvidenceOperandKey,
                              DifferentialEvidenceMaterialization>,
    differentialEvidenceOrder: NodeList<DifferentialEvidenceOperandKey>,
    resultType: TypeId
}

DerivativeInstOperandLayout =
    ForwardDerivativeInstOperands(base: UInt32)
  | BackwardDerivativeInstOperands(applyFunction: UInt32,
                                   contextType: UInt32,
                                   backwardPropagateFunction: UInt32)

DerivativeSelectionInstSemanticPlan = {
    mode: DifferentiationMode,
    provider: DerivativeProviderInstSemanticMetadata,
    signature: DerivativeSignatureMapId,
    materialization: DerivativeSelectionMaterializationPlan,
    operands: DerivativeInstOperandLayout
}
```

Frontend IR uses the existing generated `IRForwardDifferentiate`, `IRBackwardDifferentiate`, and
`IRDetachDerivative` instructions. Provider identity, signature maps, and materialization proofs
live in `IRInstSemanticMetadata`; activity seeds, aggregate field mappings, loop bounds, and custom
provider associations use their registered codebase operations/decorations. Each has a closed
operand/result schema and direct semantic dependencies.

`DIF-IR-001`: Lowering a derivative selection plan preserves provider kind in
`metadata.derivativeSelection`. Direct/custom/builtin, witness-table, dynamic, assumed, and
synthesized providers remain distinguishable. The materialization plan emits explicit prerequisite
instructions for specialization, witness lookup, dynamic callable selection, lambda-environment
state, and differential evidence. It then emits exactly one generated differentiation instruction. A forward
plan emits `IRForwardDifferentiate` with exactly one operand, `base`, and records
`ForwardDerivativeInstOperands(base = 0)`. A backward plan emits `IRBackwardDifferentiate` with
exactly three operands in this order: `applyFunction`, `contextType`, and
`backwardPropagateFunction`; its recorded ordinals are `0`, `1`, and `2`. Provider or evidence
values are not appended as extra differentiation operands and no provider payload is hidden in
`IROp`.

`DIF-IR-002`: The `DerivativeSignatureMap` is serialized or reproducibly referenced by content ID.
Any downstream derivative body must have exactly that logical signature and slot map. A pass cannot
derive parameter roles again from wrapper types, modifiers, or parameter position.

`DIF-IR-003`: Lowering an IRReady `DetachDerivativePlan` produces one `IRDetachDerivative`. The IR
instruction
has the same primal result type and ordinary effects as its
operand while terminating derivative activity. Optimizations may remove it only when they prove no
derivative transformation or diagnostic consumer observes the boundary.

`DIF-IR-004`: `IRReadyDerivativeSelectionPlan.differentialEvidence` has exactly the keys and
topological order of `provider.proof.evidenceOperands`. Each value is produced by structural lowering
of its stage-specific source: table reference, bound ABI witness, specialization with explicit
generic and constraint operands, one lookup operation, associated-type witness lookup, or
existential opening. `DerivativeSelectionMaterializationPlan` has the same key set/order and assigns
consecutive materialization ordinals. Every recorded `IRValueShape` equals the lowered evidence
shape. Those values feed the explicit prerequisite graph that produces the one or three actual
differentiation operands; they are not implicit extra operands of the final instruction.
Differential type dictionaries, if used as an optimization, are derived from these explicit values
and lookup operations. They are not semantic side tables and cannot be the only representation of
generic, conformance, associated-type, or existential differential evidence.

`DIF-IR-005`: An `IRReadyDerivativeSelectionPlan` has an applicable-provider proof whose request
primal equals the callable represented by `primalCallable`, and its forward/backward emission plan
agrees with that request's mode. Typed-AST maximality proofs and rejected diagnostic candidates do
not enter the executable IRReady node.
`providerOperands` is `WitnessDerivativeProviderOperands` exactly for a
`WitnessDerivative`, `DynamicDerivativeProviderOperands` exactly for a
`DynamicDerivative`, and `StaticDerivativeProviderOperands` otherwise. The forward `base`, or the
backward apply/context/propagate triple, is the exact output of that plan's prerequisite
materialization and cannot be replaced by an equal-typed value. The final instruction has exactly one
`RuntimeValueShape(functionTypeOf(provider.signatureMap.derivative))` result.

`DIF-IR-006`: `IRDetachDerivative` consumes `value` as operand zero and returns one value of the
same runtime type. `DetachDerivativeBoundaryId` appears only in
`metadata.detachDerivative = Some(DetachDerivativeInstSemanticPlan{boundary})`; it is not an
operand or `IROp` payload. Ordinary effects come from the generated instruction schema, and
evaluation order comes from the SSA graph. There is no zero-operand decoration form from which a
consumer must rediscover the stopped value.

`DIF-IR-007`: The semantic `DerivativeProviderAt<Published>` is exhaustively lowered to the matching
`DerivativeProviderInstSemanticMetadata`. User-defined and synthesized callable providers resolve to
function `IRSymbolRef`s. Witness, dynamic, builtin, association, synthesis, and trust-policy facts
use the metadata alternative's exact `IRStaticData<T>` payload type with
`id = ContentId(value)`. An assumed provider's callable endpoint is also an `IRSymbolRef`. Every
symbol ref occurs in `FrontendIRFragment.references` and resolves under `IR-RES-001`; no metadata
contains `ResolvedDeclRef`, `DeclRef`, `CallableValue`, witness-resolution sidecars, or AST
nodes. Every standard-environment rule mentioned by the provider metadata alternative or its
static data appears as a `StandardRuleDependency` in the fragment requirements.

`DIF-IR-008`: Provider semantic metadata is sufficient to validate provider kind, requested mode/order,
witness entry or dynamic slot, builtin registration, and association/trust policy without semantic
lookup. It does not duplicate a callable symbol identity: the `IRSymbolRef` is the sole IR authority
for callable targets. Conversely, non-callable provider facts never masquerade as symbol refs.
Serialization round-trips the metadata and static data byte-for-byte, and linking rewrites only
`IRSymbolRef.linkage` under the ordinary symbol-resolution rules.

## Failure algebra and validation

```text
DifferentiabilityFailureAt<S: WitnessTableState> =
    DifferentialInfoQueryFailure(DifferentialInfoFailure)
  | AggregateDifferentialQueryFailure(AggregateDifferentialFailureAt<S>)
  | CallableDifferentialShapeQueryFailure(
        CallableDifferentialShapeFailureAt<S>)
  | DerivativeSignatureQueryFailure(DerivativeSignatureFailure)
  | DerivativeProviderQueryFailure(RejectedDerivativeProviderSearchAt<S>)
  | DerivativeProviderCapabilityValidationQueryFailure(
        selection: SelectedDerivativeProviderAt<S>,
        failures: NonEmpty<DerivativeProviderFailureAt<S>>)
  | EffectiveDifferentiabilityContractQueryFailure(
        EffectiveDifferentiabilityContractFailureAt<S>)
  | DifferentiationCheckQueryFailure(DifferentiationCheckFailureAt<S>)
  | DifferentiableBodyQueryFailure(
        CallableDifferentiabilityValidationFailureAt<S>)

DifferentiabilityFailure = DifferentiabilityFailureAt<Published>
```

`DIF-FAL-001`: `DifferentiabilityFailureAt<S>` is a diagnostic-facing disjoint union of the exact
failure values returned by the producing total query sums; it is not a second authority with
unreachable variants. Every wrapper preserves the original typed failure unchanged. Provider
ambiguity remains the proof-carrying `AmbiguousProviderSearch` result rather than being flattened to
a list of provider names, and scheduler `Blocked` is never wrapped as a language failure.

Unit/property suites cover every type evidence constructor (including generic and existential
witnesses), field synthesis, all slot × mode × activity × differentiation-mode combinations,
custom-provider coherence, interface dispatch, detach-derivative effect preservation, recursive
queries, serialization, and exact IRReady/IR slot mapping. Provider tests independently vary
pre-inference selection effects, ordinary inferred requirements, and concrete availability; cover
`None` versus explicit `TrueFormula` sources; prove that an unavailable concrete source rejects
before ranking while an ordinary requirement becomes a use; and mutate post-fixpoint effective
contracts so a previously selected local provider fails validation without changing the winner or
its concrete proof.

The compatibility ledger separately records legacy spellings and current restrictions. It cannot
substitute downstream IR behavior for any rule above.
