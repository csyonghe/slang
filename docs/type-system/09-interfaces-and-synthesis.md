# Interfaces, conformances, witnesses, and synthesis

This chapter defines checked interface declarations as typed requirement sets and conformance as immutable,
proof-carrying evidence. It is normative for requirement identity, requirement matching, associated
type projection, defaults, conformance discovery, and synthesis. Existential representation and
calls are elaborated in chapter 12, but the evidence they consume is defined here.

The central invariant is that a conformance is not a boolean. It is a typed graph whose entries say
how one particular type satisfies every requirement occurrence of one particular specialized
interface. The graph is keyed by semantic identity, never by source or storage position.

## Checked interface declarations and instances

An interface declaration checks to an `InterfaceDecl<Typed>`. Using a generic interface with
canonical arguments creates an `InterfaceInstanceKey`:

`GenericConditionSet` is chapter 5's canonical-constraint-set alias; this chapter does not define a
second condition representation.

```text
ThisTypeBinderRole = InterfaceThisRole

ThisTypeBinderId = {
    interface: DeclId,
    role: ThisTypeBinderRole
}

CanonicalInterfaceInheritanceClauseEncoding = {
    basePattern: InterfaceInstanceKey,
    conditions: GenericConditionSet
}

InterfaceInheritanceClauseId = {
    declaringInterface: DeclId,
    encoding: CanonicalInterfaceInheritanceClauseEncoding,
    duplicateOrdinal: UInt32
}

InterfaceDecl<Typed> = {
    declaration: DeclId,
    binder: CanonicalGenericBinder,
    thisTypeBinder: ThisTypeBinderId,
    directRequirements: NodeList<SomeRequirementDecl>,
    baseInterfaces: NodeList<InterfaceInheritanceClause>,
    origin: Origin
}

InterfaceInheritanceClause = {
    id: InterfaceInheritanceClauseId,
    basePattern: InterfaceInstanceKey,
    conditions: GenericConditionSet,
    origin: Origin
}
```

`InterfaceInstanceKey` has the single authoritative schema in chapter 5. It is canonical after
applying defaults and solving the interface binder. A
source spelling with unresolved, ill-kinded, or residual arguments produces an error instance and
cannot identify a successful conformance.

`IFC-INS-001`: Specializations of one interface are distinct instances. `I<int>` and `I<float>` do
not share requirement keys, witness-table identities, or witness entries merely because their source
requirements have the same `DeclId`.

`IFC-INS-002`: Within a requirement signature, `This` is the bound
`ThisType(interface, thisTypeBinder)`. Instantiating a requirement for a candidate conformance replaces
that `This` with the conforming type and applies the interface and lexical substitutions exactly
once.

`IFC-INS-003`: Interface-inheritance clauses must denote well-formed base-interface instances. A
cyclic interface-inheritance graph is rejected; interface identity does not make a refinement
proof coinductive.

`IFC-INS-004`: `ThisTypeBinderId` is the structural pair of the declaring interface's stable `DeclId`
and the one fixed `InterfaceThisRole`; it is never allocated from a snapshot counter. Copying or
deserializing an interface therefore reconstructs the same bound `This` identity.

`IFC-INS-005`: An interface-inheritance clause ID contains its declaring interface and full canonical
base-pattern/condition encoding. `duplicateOrdinal` is assigned after grouping equal encodings and
sorting their source token ranges, so byte-equivalent duplicate clauses remain distinct without
depending on allocation or worker order. `basePattern` is an `InterfaceInstanceKey`; its canonical
arguments may reference the declaring interface's bound variables but contain no unresolved source
arguments. The clause fields must reproduce the encoding stored in its ID.

## Kind-indexed requirements

Requirements are a closed, kind-indexed sum. The kind determines both the signature comparison and
the shape of acceptable evidence:

```text
RequirementKind =
    AssociatedTypeKind
  | AssociatedValueKind
  | CallableKind
  | PropertyKind
  | SubscriptKind
  | ConstructorKind
  | ConformanceRequirementKind

SomeRequirementDecl = exists K: RequirementKind . RequirementDecl<K>
SomeRequirementKey = exists K: RequirementKind . RequirementKey<K>

SubtypeWitnessTarget = {
    subtype: TypeId,
    superInterface: InterfaceInstanceKey
}

LookupRequirement<K: RequirementKind> = {
    base: TypeId,
    witness: SubtypeWitnessId,
    requirement: InterfaceRequirementKeyOf<K>
}

LookupRequirementResultDomain<AssociatedTypeKind> = Type
LookupRequirementResultDomain<AssociatedValueKind> =
    ConstValue when signature.constantRequired
  | TypedExpr otherwise
LookupRequirementResultDomain<CallableKind> = CallableValue
LookupRequirementResultDomain<PropertyKind> = NodeMap<AccessorRole, CallableValue>
LookupRequirementResultDomain<SubscriptKind> = NodeMap<AccessorRole, CallableValue>
LookupRequirementResultDomain<ConstructorKind> = CallableValue
LookupRequirementResultDomain<ConformanceRequirementKind> = SubtypeWitness

AssociatedTypeConstraint = Constraint

AssociatedConstraintSlot = {
    requirement: RequirementKey<AssociatedTypeKind>,
    constraintOrdinal: UInt32,
    kind: ConstraintKind
}

WitnessTableDefinitionRevision = {
    snapshot: SemanticSnapshotId,
    definitionOrdinal: UInt32
}

ValidatedWitnessTableRef = {
    identity: WitnessTableId,
    revision: WitnessTableDefinitionRevision
}

AccessorRole = Getter | Setter | RefAccessor(access: StorageAccessMode)

validAccessorRole(Getter) = True
validAccessorRole(Setter) = True
validAccessorRole(RefAccessor(a)) = (a = ReadAccess or a = ReadWriteAccess)

RuntimeInterfaceRequirementKey =
    CallableEntry(requirement: InterfaceRequirementKeyOf<CallableKind>)
  | ConstructorEntry(requirement: InterfaceRequirementKeyOf<ConstructorKind>)
  | PropertyAccessorEntry(requirement: InterfaceRequirementKeyOf<PropertyKind>,
                          accessor: AccessorRole)
  | SubscriptAccessorEntry(requirement: InterfaceRequirementKeyOf<SubscriptKind>,
                           accessor: AccessorRole)

InterfaceRequirementKey =
    BaseInterfaceEntry(inheritance: RefinementStepKey)
  | RequirementEntry(requirement: SomeRequirementKey)

InterfaceRequirementKeyOf<K> = RequirementEntry(requirement: RequirementKey<K>)
SomeInterfaceRequirementKey = InterfaceRequirementKey

SubtypeWitnessLookupKey =
    BaseInterfaceEntry(inheritance: RefinementStepKey)
  | ConformanceRequirementEntry(
        requirement: InterfaceRequirementKeyOf<ConformanceRequirementKind>)

WitnessTableState = Construction | Published

RequirementDictionaryEntryAt<K, S: WitnessTableState> = ConditionalRequirementWitnessAt<K, S>

RequirementDictionaryAt<S: WitnessTableState> =
    DependentNodeMap<K: RequirementKind,
                     InterfaceRequirementKeyOf<K>,
                     RequirementDictionaryEntryAt<K, S>>

RequirementDictionary = RequirementDictionaryAt<Published>

ProvisionalRequirementDictionary =
    RequirementDictionaryAt<Construction>

EffectValidatedRequirementDictionary =
    ProvisionalRequirementDictionary where no callable proof/plan contains
    PendingLocal(RequirementEffectCompatibilityObligation)

CapabilityValidatedRequirementDictionary =
    ProvisionalRequirementDictionary where no callable proof/plan contains
    PendingLocal(InferredCapabilityCompatibilityObligation)

FullyValidatedConstructionRequirementDictionary =
    ProvisionalRequirementDictionary where neither pending-check form occurs

ConformanceConstructionScope =
    ConformanceQuery(query: QueryKey)
  | SynthesisConstruction(group: SynthesisKey)

OperationalWitnessTableRef = {
    identity: WitnessTableId,
    scope: ConformanceConstructionScope
}

SubtypeWitnessRef<S: WitnessTableState> = {
    witness: SubtypeWitnessId,
    resolutions: WitnessResolutionSetAt<S>
}

CallableRequirementContract = {
    selection: PreInferenceCallableContract,
    effectAllowance: EffectAllowance
}

RequirementContract<AssociatedTypeKind> = NoCallableContract
RequirementContract<AssociatedValueKind> = NoCallableContract
RequirementContract<CallableKind> = CallableRequirementContract
RequirementContract<PropertyKind> =
    NodeMap<AccessorRole, CallableRequirementContract>
RequirementContract<SubscriptKind> =
    NodeMap<AccessorRole, CallableRequirementContract>
RequirementContract<ConstructorKind> = CallableRequirementContract
RequirementContract<ConformanceRequirementKind> = NoCallableContract

RequirementDecl<K> = {
    declaration: DeclId,
    owner: DeclId,
    kind: K,
    signature: RequirementSignature<K>,
    contract: RequirementContract<K>,
    optionality: Required | Optional(OptionalSemantics<K>),
    default: Option<RequirementDefault<K>>,
    conditions: GenericConditionSet,
    origin: Origin
}

RequirementSignature<AssociatedTypeKind> = {
    kind: Kind,
    constraints: NodeList<AssociatedTypeConstraint>
}

RequirementSignature<AssociatedValueKind> = {
    type: TypeId,
    constantRequired: Bool
}

RequirementSignature<CallableKind> = CallableSignature

RequirementSignature<PropertyKind> = {
    valueType: TypeId,
    receiver: ReceiverSlot,
    accessors: NodeMap<AccessorRole, CallableSignature>
}

RequirementSignature<SubscriptKind> = {
    indices: NodeList<FuncTypeParamInfo>,
    indexSlots: NodeList<ParameterSlot>,
    valueType: TypeId,
    receiver: ReceiverSlot,
    accessors: NodeMap<AccessorRole, CallableSignature>
}

RequirementSignature<ConstructorKind> = CallableSignature

RequirementSignature<ConformanceRequirementKind> = {
    subject: TypeId,
    interface: InterfaceInstanceKey
}

RequirementWitnessPayloadAt<AssociatedTypeKind, S: WitnessTableState> =
    TypeWitness(type: TypeId,
                constraints: NodeMap<AssociatedConstraintSlot, ConstraintEvidence>)

RequirementWitnessPayloadAt<AssociatedValueKind, S: WitnessTableState> =
    ValueWitness(value: DeclRef | ConstValue, typeProof: TypeEqualityProof)

RequirementWitnessPayloadAt<CallableKind, S: WitnessTableState> =
    CallableWitness(declaration: DeclRef, signature: CallableSignature)

RequirementWitnessPayloadAt<PropertyKind, S: WitnessTableState> =
    PropertyWitness(accessors: NodeMap<AccessorRole, RequirementWitnessPayloadAt<CallableKind, S>>)

RequirementWitnessPayloadAt<SubscriptKind, S: WitnessTableState> =
    SubscriptWitness(accessors: NodeMap<AccessorRole, RequirementWitnessPayloadAt<CallableKind, S>>)

RequirementWitnessPayloadAt<ConstructorKind, S: WitnessTableState> =
    ConstructorWitness(declaration: DeclRef, signature: CallableSignature)

RequirementWitnessPayloadAt<ConformanceRequirementKind, S: WitnessTableState> =
    NestedWitness(witness: SubtypeWitnessRef<S>)

RequirementWitnessPayload<K> = RequirementWitnessPayloadAt<K, Published>

CanonicalFieldEquality<T> = {
    left: T,
    right: T
}

ConditionalFieldEquality<T> =
    Compared(CanonicalFieldEquality<T>)
  | ExcludedByLanguageRule(rule: RuleId)

KindEqualityProof = CanonicalFieldEquality<Kind>
ConstantValueProof = CanonicalFieldEquality<ConstValue>
RequirementSignatureEqualityProof<K> =
    CanonicalFieldEquality<RequirementSignature<K>>

AdapterSourceRole =
    RequirementReceiverRole
  | RequirementParameterRole(ParameterKey)
  | ImplementationThrownErrorRole
  | SynthesizedValueRole(SynthesizedSemanticId)

AdapterTargetRole =
    ImplementationReceiverRole
  | ImplementationParameterRole(ParameterKey)
  | ErrorHandlerParameterRole(ParameterKey)

AdapterInputCategory =
    AdapterRValue
  | AdapterPhysicalStorage(requirement: PhysicalStorageRequirement)
  | AdapterAbstractStorage(access: StorageAccessMode, mutability: Mutability)

AdapterSourceEndpoint = {
    role: AdapterSourceRole,
    type: TypeId,
    category: AdapterInputCategory
}

AdapterTargetEndpoint = {
    role: AdapterTargetRole,
    type: TypeId,
    mode: ParamPassingMode
}

StorageAccessPlanBindingAt<S: WitnessTableState> = {
    source: AdapterSourceEndpoint,
    target: AdapterTargetEndpoint,
    invocationLifetime: LifetimeId,
    input: StorageAccessOperandId,
    plan: StorageAccessPlan<S>
}

StorageAccessPlanBinding = StorageAccessPlanBindingAt<Published>

ReceiverCorrespondence =
    AbsentToAbsent
  | ReceiverToReceiver(required: ReceiverSlot, implementation: ReceiverSlot)
  | ReceiverDiscardedByStatic(required: ReceiverSlot, permission: RuleId)
  | RequirementParameterToReceiver(required: ParameterKey,
                                   implementation: ReceiverSlot,
                                   permission: RuleId)
  | SynthesizedValueToReceiver(value: SynthesizedSemanticId,
                               implementation: ReceiverSlot,
                               permission: RuleId)
  | ReceiverToImplementationParameter(required: ReceiverSlot,
                                      implementation: ParameterKey,
                                      permission: RuleId)

ParameterCorrespondence = {
    required: CallableSignatureId,
    implementation: CallableSignatureId,
    receiver: ReceiverCorrespondence,
    implementationByRequirement: NodeMap<ParameterKey, ParameterKey>,
    implementationExpansionsByRequirement:
        NodeMap<SourceParameterKey, NodeList<ParameterKey>>
}

IndexParameterEndpoint = {
    parameters: NodeList<FuncTypeParamInfo>,
    slots: NodeList<ParameterSlot>
}

IndexParameterCorrespondence = {
    required: IndexParameterEndpoint,
    implementation: IndexParameterEndpoint,
    implementationByRequirement: NodeMap<ParameterKey, ParameterKey>
}

IndexParameterEqualityProof = {
    correspondence: IndexParameterCorrespondence,
    parameters: NodeMap<ParameterKey, FuncTypeParamInfoEqualityProof>
}

ReceiverEqualityProof =
    BothAbsent
  | BothPresent(required: ReceiverSlot,
                implementation: ReceiverSlot,
                selfType: TypeEqualityProof,
                mode: CanonicalFieldEquality<ParamPassingMode>,
                differentialParticipation:
                    CanonicalFieldEquality<DifferentialParticipation>,
                isolation: CanonicalFieldEquality<ReceiverIsolation>)

FuncTypeParamInfoEqualityProof = {
    requiredKey: ParameterKey,
    implementationKey: ParameterKey,
    requiredOrdinal: UInt32,
    implementationOrdinal: UInt32,
    valueType: TypeEqualityProof,
    mode: CanonicalFieldEquality<ParamPassingMode>,
    differentialParticipation: CanonicalFieldEquality<DifferentialParticipation>,
    attributes: CanonicalFieldEquality<ParameterAttributeSet>
}

FuncTypeEqualityProof = {
    required: CallableSignatureId,
    implementation: CallableSignatureId,
    correspondence: ParameterCorrespondence,
    binder: CanonicalFieldEquality<Option<CanonicalGenericBinder>>,
    receiver: ReceiverEqualityProof,
    parameters: NodeMap<ParameterKey, FuncTypeParamInfoEqualityProof>,
    result: TypeEqualityProof,
    resultDifferentialParticipation: CanonicalFieldEquality<DifferentialParticipation>,
    error: TypeEqualityProof,
    purpose: CanonicalFieldEquality<CallablePurpose>,
    traits: CanonicalFieldEquality<CallableTraits>,
    callingConvention: CanonicalFieldEquality<CallingConvention>
}

RequirementCompatibilityProofAt<AssociatedTypeKind, S: WitnessTableState> =
    AssociatedTypeProof(kind: KindEqualityProof,
                        constraints: NodeMap<AssociatedConstraintSlot, ConstraintEvidence>)

RequirementCompatibilityProofAt<AssociatedValueKind, S: WitnessTableState> =
    AssociatedValueProof(type: TypeEqualityProof, constant: Option<ConstantValueProof>)

CallableImplementationSubject =
    SourceCallable(declaration: DeclRef, locality: Local | Imported)
  | SynthesizedCallable(declaration: SynthesizedDeclId)
  | BuiltinCallable(rule: RuleId, inputs: CanonicalArguments)

InferredCapabilityCompatibilityObligation = {
    conformance: WitnessTableId,
    entry: RuntimeInterfaceRequirementKey,
    requiredInferredCapabilities: CapabilityRequirement,
    implementation: CallableImplementationSubject,
    implementationInferredCapabilities: CapabilityRequirement,
    preInferenceProof: CapabilityImplicationProof,
    origin: Origin
}

InferredCapabilityCompatibilityProof = {
    obligation: InferredCapabilityCompatibilityObligation,
    effectiveContract: EffectiveCallableContractId,
    effectiveInferredCapabilities: CapabilitySet,
    effectiveProof: CapabilityImplicationProof
}

InferredCapabilityCompatibilityCheck =
    PendingLocal(InferredCapabilityCompatibilityObligation)
  | ValidatedLocal(InferredCapabilityCompatibilityProof)
  | ValidatedImported(InferredCapabilityCompatibilityProof)

ConcreteAvailabilityCompatibilityProof = {
    region: BooleanCapabilityPredicate,
    required: Option<ConcreteAvailabilitySet>,
    implementation: Option<ConcreteAvailabilitySet>,
    requiredAvailability: CapabilityRegionAvailabilityProof,
    implementationAvailability: CapabilityRegionAvailabilityProof
}

RequirementEffectCompatibilityObligation = {
    conformance: WitnessTableId,
    entry: RuntimeInterfaceRequirementKey,
    requirementAllowance: EffectAllowance,
    implementation: CallableImplementationSubject,
    selectionEffects: EffectSet,
    selectionProof: EffectAllowanceValidation,
    origin: Origin
}

EffectCompatibilityProof = {
    obligation: RequirementEffectCompatibilityObligation,
    effectiveContract: EffectiveCallableContractId,
    effectiveEffects: EffectSet,
    validation: EffectAllowanceValidation
}

EffectCompatibilityCheck =
    PendingLocal(RequirementEffectCompatibilityObligation)
  | ValidatedLocal(EffectCompatibilityProof)
  | ValidatedImported(EffectCompatibilityProof)

CallableContractSatisfactionProof = {
    required: PreInferenceCallableContract,
    requiredEffectAllowance: EffectAllowance,
    implementation: PreInferenceCallableContract,
    effects: EffectCompatibilityCheck,
    inferredCapabilities: InferredCapabilityCompatibilityCheck,
    concreteAvailability: ConcreteAvailabilityCompatibilityProof
}

RequirementCompatibilityProofAt<CallableKind, S: WitnessTableState> =
    CallableProof(signature: FuncTypeEqualityProof,
                  contract: CallableContractSatisfactionProof)

RequirementCompatibilityProofAt<PropertyKind, S: WitnessTableState> =
    PropertyProof(valueType: TypeEqualityProof,
                  accessors: NodeMap<AccessorRole,
                                     RequirementCompatibilityProofAt<CallableKind, S>>)

RequirementCompatibilityProofAt<SubscriptKind, S: WitnessTableState> =
    SubscriptProof(indices: IndexParameterEqualityProof,
                   valueType: TypeEqualityProof,
                   accessors: NodeMap<AccessorRole,
                                      RequirementCompatibilityProofAt<CallableKind, S>>)

RequirementCompatibilityProofAt<ConstructorKind, S: WitnessTableState> =
    ConstructorProof(signature: FuncTypeEqualityProof,
                     contract: CallableContractSatisfactionProof)

SubtypeWitnessTargetProofAt<S: WitnessTableState> = {
    evidence: SubtypeWitnessRef<S>,
    actual: SubtypeWitnessTarget,
    required: SubtypeWitnessTarget,
    conformingType: TypeEqualityProof,
    interface: CanonicalFieldEquality<InterfaceInstanceKey>
}

RequirementCompatibilityProofAt<ConformanceRequirementKind, S: WitnessTableState> =
    NestedProof(subject: TypeEqualityProof, target: SubtypeWitnessTargetProofAt<S>)

RequirementCompatibilityProof<K> = RequirementCompatibilityProofAt<K, Published>
SubtypeWitnessTargetProof = SubtypeWitnessTargetProofAt<Published>

ResultAdapterPlanAt<S: WitnessTableState> = {
    implementationResult: TypeId,
    requiredResult: TypeId,
    conversion: ConversionPlan<S>
}

ResidualErrorPlanAt<S: WitnessTableState> =
    NoResidualError(errorIsBottom: TypeEqualityProof)
  | ConvertResidualError(conversion: ConversionPlan<S>)

ErrorHandlerAdapterAt<S: WitnessTableState> = {
    handler: DeclRef,
    signature: CallableSignatureId,
    errorArgument: StorageAccessPlanBindingAt<S>,
    normalResult: ResultAdapterPlanAt<S>,
    residualError: ResidualErrorPlanAt<S>,
    permission: RuleId
}

ErrorAdapterPlanAt<S: WitnessTableState> = {
    implementationError: TypeId,
    requiredError: TypeId,
    operation: ImplementationDoesNotThrow(errorIsBottom: TypeEqualityProof)
             | PropagateExact(errorEquality: TypeEqualityProof)
             | ConvertAndPropagate(conversion: ConversionPlan<S>)
             | CatchWithHandler(ErrorHandlerAdapterAt<S>)
}

CallableContractAdapterProof = {
    required: PreInferenceCallableContract,
    requiredEffectAllowance: EffectAllowance,
    implementation: PreInferenceCallableContract,
    adapterSelection: PreInferenceCallableContract,
    operationEffects: EffectSet,
    operationInferredCapabilities: CapabilityRequirement,
    operationConcreteAvailability: Option<ConcreteAvailabilitySet>,
    effects: EffectCompatibilityCheck,
    inferredCapabilities: InferredCapabilityCompatibilityCheck,
    concreteAvailability: ConcreteAvailabilityCompatibilityProof
}

RequirementAdapterPlanAt<CallableKind, S: WitnessTableState> =
    CallableAdapter(required: CallableSignatureId,
                    implementation: DeclRef,
                    implementationSignature: CallableSignatureId,
                    correspondence: ParameterCorrespondence,
                    receiverAccess: Option<StorageAccessPlanBindingAt<S>>,
                    parameterAccessByImplementation:
                        NodeMap<ParameterKey, StorageAccessPlanBindingAt<S>>,
                    result: ResultAdapterPlanAt<S>,
                    error: ErrorAdapterPlanAt<S>,
                    contract: CallableContractAdapterProof)

RequirementAdapterPlanAt<PropertyKind, S: WitnessTableState> =
    PropertyAdapter(accessors:
        NodeMap<AccessorRole, RequirementAdapterPlanAt<CallableKind, S>>)

RequirementAdapterPlanAt<SubscriptKind, S: WitnessTableState> =
    SubscriptAdapter(indices: IndexParameterCorrespondence,
                     accessors:
                         NodeMap<AccessorRole, RequirementAdapterPlanAt<CallableKind, S>>)

RequirementAdapterPlanAt<ConstructorKind, S: WitnessTableState> =
    ConstructorAdapter(call: RequirementAdapterPlanAt<CallableKind, S>)

RequirementAdapterPlan<K> = RequirementAdapterPlanAt<K, Published>
ResultAdapterPlan = ResultAdapterPlanAt<Published>
ResidualErrorPlan = ResidualErrorPlanAt<Published>
ErrorAdapterPlan = ErrorAdapterPlanAt<Published>

DefaultUsePlan<K, S: WitnessTableState> = {
    instantiated: InstantiatedDefault<K>,
    selfConformance: SubtypeWitnessRef<S>,
    output: DefaultOutputAt<K, S>,
    entryPointRequired: Bool
}

DefaultOutputAt<K, S: WitnessTableState> = RequirementWitnessPayloadAt<K, S>
                 | RequirementAdapterPlanAt<K, S>  when K is adapter-capable

DefaultOutput<K> = DefaultOutputAt<K, Published>

BuiltinWitnessPlan<K> = {
    rule: RuleId,
    inputs: CanonicalArguments,
    outputKind: K,
    validator: StandardEnvironmentRuleId
}

BuiltinWitnessAt<K, S: WitnessTableState> = {
    rule: RuleId,
    payload: RequirementWitnessPayloadAt<K, S>,
    proof: RequirementCompatibilityProofAt<K, S>
}

BuiltinWitness<K> = BuiltinWitnessAt<K, Published>

RequirementReuseProof<K> = {
    source: RequirementKey<K>,
    target: RequirementKey<K>,
    signature: RequirementSignatureEqualityProof<K>,
    pathRelation: SameSpecialization | ValidatedOverride
}

OptionalAbsenceProof<K> = {
    requirement: RequirementKey<K>,
    semantics: OptionalSemantics<K>,
    condition: BooleanCapabilityPredicate
}

OptionalSemantics<K> = {
    rule: StandardEnvironmentRuleId,
    observation: NoneAtUse,
    permittedUses: OptionalUseSet<K>
}

OptionalUse<AssociatedTypeKind> = PresenceTest | GuardedTypeProjection
OptionalUse<AssociatedValueKind> = PresenceTest | GuardedValueRead
OptionalUse<CallableKind> = PresenceTest | GuardedInvocation
OptionalUse<PropertyKind> = PresenceTest | GuardedAccessor(AccessorRole)
OptionalUse<SubscriptKind> = PresenceTest | GuardedAccessor(AccessorRole)
OptionalUse<ConstructorKind> = PresenceTest | GuardedConstruction
OptionalUse<ConformanceRequirementKind> = PresenceTest | GuardedConstraintUse

OptionalUseSet<K> = CanonicalFiniteSet<OptionalUse<K>>

RequirementDefault<K> = {
    implementation: DefaultImplementation<K>,
    checkedSignature: RequirementSignature<K>,
    proof: RequirementCompatibilityProof<K>,
    origin: Origin
}

DefaultImplementation<K> =
    Evidence(RequirementWitnessPayload<K>)
  | MemberBody(DeclRef)       when K is a runtime member kind
  | StandardBuiltin(BuiltinWitnessPlan<K>)

InstantiatedDefault<K> = {
    source: RequirementDefault<K>,
    specializations: CanonicalSpecializationSpine,
    signature: RequirementSignature<K>
}

RecoveryWitness<K> = {
    expected: RequirementSignature<K>,
    error: ErrorId
}
```

`LookupRequirement<K>` is a schema family, not one untyped semantic node whose payload is inspected
after construction. Each specialization is embedded directly in the result domain above.
`AssociatedTypeProjection` is the codebase-aligned name of the concrete `Type` constructor whose
payload is `LookupRequirement<AssociatedTypeKind>`; therefore generic node inspection and
`as<Type>(x)` recognize it as a type without opening a witness payload. A callable specialization
constructs chapter 12's `CallableValue` with `WitnessMethod` dispatch. A constant-required
associated value constructs chapter 5's `LookupRequirementConst`; an ordinary associated value is
a typed value expression. A conformance-requirement specialization constructs the canonical
`LookupSubtypeWitness` candidate. There is no conversion among these result families merely because
they share the lookup schema.

`IFC-LOOKUP-001`: For every kind `K`, `lookup.base` is exactly the subtype endpoint of
`lookup.witness`; the witness's super-interface is exactly `lookup.requirement.view`; and the key is
an active kind-`K` entry in that view. The selected witness definition determines the operational
table lookup. Requirement declaration names, source positions, or a desired result-domain cast
cannot substitute for the complete key.

`IFC-LOOKUP-002`: Lowering any specialization performs one witness lookup with the same witness and
complete requirement key. The result-domain constructor determines how that result is consumed;
only callable-like entries become dispatchable runtime slots, and only a
`ConformanceRequirementKind` result is itself subtype evidence.

## Callable certificates and adapter endpoints

The schemas above compose the type, conversion, effect, capability, and access-plan domains from
chapters 5, 8, 10, and 12. They do not introduce alternative equality, coercion, or passing
algorithms. Every proof is an endpoint certificate revalidated against those canonical domains.
Unqualified direct-witness, compatibility-proof, adapter-plan, and access-plan-binding names mean
their `<Published>` forms; construction matching uses the explicitly staged forms.

`IFC-CALL-001`: `CanonicalFieldEquality<T>` is valid exactly when `left` and `right` are equal under
`T`'s declared canonical equality. Chapter 1 owns `CanonicalSetInclusionProof<T>`, and chapter 10
owns `CapabilityImplicationProof`; their validators replay exact endpoints rather than trusting
the stored record. A `ConditionalFieldEquality` may exclude a field only when its registered
language rule says that field does not participate in the current relation.

`IFC-CALL-002`: `FuncTypeEqualityProof` loads its two `CallableSignature` values and their
chapter 5 `FuncType` values. Its correspondence IDs must equal the proof endpoints. The binder
proof compares alpha-normalized binders and constraints; the receiver proof covers both absence or
every present receiver field; parameter proofs cover every expanded slot exactly once at the stored
ordinals; result and error `TypeEqualityProof` endpoints equal the stored function fields; and
traits and calling convention are canonically equal. Parameter labels are read only while mapping a
source argument to a `ParameterKey`; parameter and generic-parameter names never appear in this
equality proof. Effects, capabilities, visibility, dispatch, and source spelling are not
function-equality operands.

`IFC-CALL-003`: In an equality proof, receiver correspondence is only `AbsentToAbsent` or
`ReceiverToReceiver`, and ordinary parameter correspondence is a bijection after pack expansion.
In an adapter, every non-direct receiver correspondence names a rule that permits that exact role
change. `RequirementParameterToReceiver` and `SynthesizedValueToReceiver` require no required
receiver; the discarded/static and receiver-to-parameter cases require a present required receiver
and no implementation receiver; and receiver-to-receiver requires both. No implementation receiver
or ordinary parameter may be targeted twice. Every required
ordinary parameter must map once unless a distinct adapter rule explicitly consumes it as a
receiver; every implementation input must have one source. Requirement and implementation
`ParameterKey` values identify endpoints and are never compared for equality with one another.

A `StorageAccessPlanBinding` gives chapter 12's otherwise expression-local `StorageAccessPlan` explicit adapter
endpoints. Its source role denotes a formal thunk input, thrown error, or named synthesized value;
its target resolves to the implementation receiver/parameter or handler parameter. The endpoint
types and target mode must agree with the corresponding signature fields. `AdapterInputCategory`
is intentionally pathless: a generated thunk input may promise an rvalue, physical storage meeting
a complete requirement, or abstract getter/setter storage, but no concrete expression `StorageRef`
exists until a call binds that thunk. Physical and abstract promises are disjoint; a generic
"storage" promise cannot later be interpreted as referenceable storage.

| Target mode       | Permitted `RuntimeArgument` and required completion                                                                                                                                                                                               |
| ----------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `InMode`          | `ImmediateValue`; all conversions finish before the call                                                                                                                                                                                          |
| `OutMode`         | `OutDestination`, or `TemporaryAddress` with initialization/write-back on normal return                                                                                                                                                           |
| `InOutMode`       | writable abstract or physical destination under its explicit access/write-back plan; any permitted temporary has normal-return write-back and cleanup                                                                                             |
| `ConstRefMode(r)` | `PhysicalStorageArgument` from an `AdapterPhysicalStorage` whose `AdapterStorageObligation` is `instantiatePhysicalStorageRequirement(target.mode, lifetime)` with read access; no conversion, temporary, getter, write-back, or category erasure |
| `RefMode(r)`      | `PhysicalStorageArgument` whose `AdapterStorageObligation` is `instantiatePhysicalStorageRequirement(target.mode, lifetime)` with read-write access; no hidden copy/write-back                                                                    |

`IFC-CALL-004`: Validating a `StorageAccessPlanBinding` symbolically executes its chapter 12 preparation,
`PassArgument` terminal, and completion steps. A `YieldStorageRead` or `CompleteStorageWrite`
terminal is invalid in an adapter call binding. `plan.operands[input]` must be an
`AdapterInput(source.role, source.type, source.category)`; that named operand is the plan's only
entry for this formal source, and every preparation path starts from it. Every nested
`ConversionPlan` composes by its chapter 8 source/target fields; physical-location, temporary,
alias, and
lifetime IDs are balanced; the `PassArgument` payload obeys the table; and post-call conversions return
to the original abstract source storage under the declared completion condition. Receiver bindings
use the same law. Adapter validation also checks all bindings together under the exact registered
alias/access-discipline policy; it does not infer exclusivity merely from a write operation. Every
physical-storage obligation in the recipe originates at an
`AdapterPhysicalStorage` endpoint with an equal or stronger requirement; constructing the bound
thunk plan supplies a concrete `PhysicalStorageProof` for that obligation. An
`AdapterAbstractStorage` may use getter/setter plans but can never discharge such an obligation or
satisfy `ConstRefMode` or `RefMode`. For a target mode `RefMode(r)`, the exact obligation is
`instantiatePhysicalStorageRequirement(target.mode, binding.invocationLifetime)`, including the
mode's access and `r`'s minimum lifetime, address-space requirement, and source-provenance
predicate. The source endpoint must provide that full requirement and
the `PhysicalStorageArgument` runtime argument must carry its proof; comparing only access or deferring
instantiation to thunk lowering is invalid. Every binding in one adapter uses the canonical
invocation lifetime of that adapter's callable signature.

For `ConstRefMode(r)`, validation applies
`instantiatePhysicalStorageRequirement(target.mode, binding.invocationLifetime)` and requires
`target.mode.access = ReadAccess`; access is a field of `ParamPassingMode`, not of `r`. The source is an
`AdapterPhysicalStorage` whose promise entails that instantiated
requirement, and the recipe may only project and pass that same physical location with a read-only
admission proof. Its call-lifetime alias claim is a shared read, but its runtime category and ABI
remain physical storage with `isPhysicalStorage = True`; it is never recategorized as an ordinary
value or nonphysical storage view. An rvalue, abstract storage,
getter, property exposing only `RefAccessor(ReadWriteAccess)`, nonidentity conversion, or temporary cannot
satisfy the binding. A separately written expression that already produces a validated physical
storage is judged on that resulting storage rather than being treated as the original abstract
property.

`IFC-CALL-005`: A `ResultAdapterPlan` has conversion source equal to the implementation result and
target equal to the required result. An `ErrorAdapterPlan` has the stored function error endpoints:
`ImplementationDoesNotThrow` proves the implementation error is `BottomType`; `PropagateExact` proves
the error types equal; and `ConvertAndPropagate` has conversion source/target equal to the two error
types. `CatchWithHandler` is valid only under its named permission rule; the handler is a
no-receiver callable with one mapped error parameter, `errorArgument` maps the thrown implementation
error to that parameter, `normalResult` maps the handler result to the required result, and the
handler's residual error is either `BottomType` or explicitly converted to the required error. Every
handler/conversion effect and capability is included in the adapter contract.

`IFC-CALL-006`: `CallableContractSatisfactionProof.required.signature` and
`.implementation.signature` equal the enclosing function-equality endpoints. Its `required` and
`requiredEffectAllowance` fields equal the enclosing slot entry's instantiated
`CallableRequirementContract`. At selection time its effect check uses that requirement
`EffectAllowance` and the implementation's `selectionEffects`. Ordinary capability compatibility
instead proves `required.inferredCapabilities` entails
`implementation.inferredCapabilities`; this records what a call through the requirement transmits
to caller inference and is not a selection-availability test. Concrete availability compatibility
is a separate `ConcreteAvailabilityCompatibilityProof`. Its `region` equals the active
`MatchRequirement` capability region. If `U` is the contracts' common universe, its two availability
proofs have that exact region and requirements
`totalConcreteAvailability(required.concreteAvailability, U)` and
`totalConcreteAvailability(implementation.concreteAvailability, U)`, respectively. This admits a
region-specific implementation only for the region in which it is actually available; the guarded
satisfactions' coverage proof establishes compatibility over the requirement's complete availability
domain. A source subject contains one `DeclRef`, which is the sole owner of its
specialization frames and must equal the enclosing entry's direct witness declaration. Both
inferred-capability obligation entry keys equal the enclosing `RuntimeInterfaceRequirementKey`. Local
inferred-capability checks are `PendingLocal`; imported checks may use their published effective
ordinary contract. Concrete availability is fixed before body inference and its compatibility proof
is validated immediately. Final witness evidence contains only validated inferred-capability checks
and a valid concrete-availability proof.

The stored selection endpoints are exact, not explanatory duplicates. The effect obligation's
`requirementAllowance` equals `requiredEffectAllowance`, its `selectionEffects` equals
`implementation.selectionEffects`, and its implementation subject denotes that same implementation
signature. If `requiredEffectAllowance` is `RestrictedEffects(E)`, then
`required.selectionEffects = E`; if it is `InferEffects`, then `required.selectionEffects` is the
empty set for the requirement's effect universe. The inferred-capability obligation's two requirement
fields equal `required.inferredCapabilities` and `implementation.inferredCapabilities`; its
implementation subject again denotes that same implementation signature, and its pre-inference
proof has exactly those endpoints. The concrete-availability proof's optional fields equal the two
contracts' fields byte-for-byte, both nested proofs use its exact region, and their requirements are
the totalized options. All effect and capability endpoints use their respective one common universe.

For a validated check, the effective-contract ID must belong to the stored implementation subject
and signature. `EffectCompatibilityProof.effectiveEffects` equals chapter 5's
`effectiveEffects(contract)` and either the allowance is inferred or the stored subset proof shows
the effective set is allowed.
`InferredCapabilityCompatibilityProof.effectiveInferredCapabilities` equals chapter 10's
`effectiveCapabilities(contract)`, and its proof endpoints are `required.inferredCapabilities` and
that effective requirement wrapped as `Closed(effectiveInferredCapabilities)`. The pre-inference,
effective, and concrete-availability proofs have different endpoints and cannot be swapped.

`IFC-CALL-007`: `CallableContractAdapterProof.adapterSelection.signature` equals the required
signature. Its selection effects are the canonical union of the implementation selection effects,
all access/result/error conversion effects, and any handler effects. Its
`inferredCapabilities` is chapter 10's `requireAll` of the implementation's ordinary requirement,
`operationInferredCapabilities`, and handler ordinary requirements. Its `concreteAvailability` is
`None` when every contributing optional set is absent; otherwise it is one
`ConcreteAvailabilitySet` whose sources are the canonical union of all present implementation,
operation, and handler sources and whose combined requirement is recomputed with
`combineConcreteAvailability`. The two stored operation summaries must equal a schema traversal of
the complete adapter plan; an ordinary operation requirement cannot be moved into the concrete
summary to make matching reject it early. The inferred-capability pending/validated check targets
the synthesized adapter subject, so post-synthesis inference validates the actual generated body
rather than merely trusting the summary. The separate concrete-availability proof compares the
requirement against `adapterSelection.concreteAvailability` immediately.

`IFC-CALL-008`: A callable adapter's `implementation` `DeclRef` is the sole specialization
authority and resolves to `implementationSignature`. Its receiver and parameter bindings target
every implementation input exactly once according to `ParameterCorrespondence`; result/error plans
use those same signature endpoints; and its contract proof uses the required and implementation
contract endpoints. In an `Adaptable` match, the candidate declaration must equal this
implementation. A nested property, subscript, or constructor plan is validated by the same rule for
each keyed callable entry.

`IFC-CALL-009`: `SubtypeWitnessTargetProofAt<S>` resolves its stable witness through the complete
stage-appropriate `WitnessResolutionSetAt<S>`, derives the witness target, and checks that it equals
`actual`. The stage parameter propagates through surrounding adapter/call plans without changing
the witness ID. It then proves `actual.subtype = required.subtype` with `conformingType` and proves
`actual.superInterface = required.superInterface` with `interface`.
`KindEqualityProof`, `ConstantValueProof`, and `RequirementSignatureEqualityProof<K>` obey
`IFC-CALL-001`; they cannot be constructed with unequal endpoints.

`IFC-CALL-010`: Each `IndexParameterEndpoint.slots` is a bijection onto its parameter ordinals.
`IndexParameterEqualityProof` maps every required index key to one implementation index key and
contains one `FuncTypeParamInfoEqualityProof` with those exact endpoint keys, ordinals, and fields.
`SubscriptAdapter.indices` is the common restriction of every accessor callable adapter's
`ParameterCorrespondence` to index parameters; getter, setter, `RefAccessor(ReadAccess)`, and
`RefAccessor(ReadWriteAccess)` adapters cannot silently choose different index mappings. Property and
subscript proof/plan accessor maps have exactly the roles required by their product signatures, and
each `valueType` proof has the required and implementation product value types as endpoints.

`IFC-CALL-011`: A callable adapter targeting `ConstRefMode(r)` is valid only by the physical-input
case of `IFC-CALL-004`. Its source endpoint, instantiated location requirement (including
`ReadAccess` from the mode), identity-only semantics, invocation lifetime, runtime
physical-location argument shape, and
shared-read alias claim are explicit plan operands. The argument remains physical through the
adapter and callee ABI; access restriction does not erase location identity. Adapter synthesis
stores the pathless `AdapterStorageObligation`, not a fabricated concrete
`PhysicalParameterBindingProofAt<S>`; binding the generated thunk input must discharge that
obligation with the concrete access/provenance proof and then construct the ordinary binding proof
for that endpoint. It cannot repair an rvalue,
getter-only abstract storage, wrong address space, forbidden physical source provenance, or a
`RefAccessor(ReadWriteAccess)` property accessor by materializing storage or weakening the requirement.

An accessor map is keyed by `AccessorRole`; an implementation cannot satisfy a setter because it
happened to occupy the second declaration slot. `RuntimeInterfaceRequirementKey` carries that role through
runtime dispatch and contract obligations. Callable signatures use chapter 5's explicit receiver
and parameter modes. Dispatch selection is not part of a function type; it is evidence in a
selected callable or elaborated call.

`RequirementDictionary` is the authoritative all-kind semantic map. Callable-dispatch keys are a derived
projection:

```text
runtimeProjection(RequirementEntry(k), signature) =
    [CallableEntry(k)]                         when kind(k) = CallableKind
    [ConstructorEntry(k)]                      when kind(k) = ConstructorKind
    sort([PropertyAccessorEntry(k, a)
          for a in keys(signature.accessors)]) when kind(k) = PropertyKind
    sort([SubscriptAccessorEntry(k, a)
          for a in keys(signature.accessors)]) when kind(k) = SubscriptKind
    []                                         otherwise
```

`WIT-ENT-001`: A `InterfaceRequirementKeyOf<K>` and its payload carry the same `K`; the enclosed
`RequirementKey<K>` equals the active slot against which every satisfaction/proof endpoint was
validated. Every active slot has exactly one entry key before capability partitioning. Associated
types, associated values, and nested conformances therefore remain explicit keyed metadata even
though they have no callable-dispatch projection.

`WIT-ENT-002`: `runtimeProjection` is total and deterministic. Property and subscript roles come
from their coherent product signatures, not source order. The initial language model treats an
associated-value witness as compile-time/metadata evidence; a language feature needing runtime
access declares a callable/property requirement or adds a new named projection rule rather than
silently treating the associated value as a method.

`WIT-ENT-003`: Serialization and IR metadata preserve `SomeInterfaceRequirementKey` for every kind. A
backend may separately map projected `RuntimeInterfaceRequirementKey` values to callable ABI slots, but
that compact map cannot replace or renumber the all-kind witness-entry map.

`IFC-KIND-001`: Every requirement declaration has exactly one `RequirementKind`, and every match,
satisfaction, default, and synthesis plan has the same type index. Erasing the index and recovering
it from a union tag at IR generation is invalid.

`IFC-KIND-002`: Property and subscript requirements are products of named accessor roles. A partial
implementation is accepted only when every missing role is optional or has a valid default.

`IFC-KIND-003`: A nested-conformance requirement produces an `SubtypeWitnessId` with its
stage-appropriate definition resolutions. A bare `WitnessTableId`, conversion, or declaration
reference cannot occupy that slot without constructing a kind-correct witness value through a
named rule.

`IFC-KIND-004`: `RequirementAdapterPlan<K>` exists only for callable, property, subscript, and
constructor kinds. Associated types, associated values, and nested conformances require direct,
defaulted, or builtin evidence; an ordinary value conversion cannot manufacture proof of them.

`IFC-KIND-005`: Every associated-type constraint proof is keyed by an
`AssociatedConstraintSlot` whose requirement equals the enclosing associated-type requirement,
whose ordinal is in range in that requirement's instantiated constraint list, and whose `kind`
equals the tag of the constraint at that ordinal. The proof map is total for the active constraints
and contains no other slots. Each `ConstraintEvidence` validator rechecks the exact instantiated
constraint endpoints after replacing the associated-type subject with the witnessed type. A
snapshot-local `ConstraintId`, positional zip, or evidence of the right kind with different
endpoints cannot satisfy the slot.

`IFC-KIND-006`: Every callable, constructor, property accessor, and subscript accessor has one
`CallableRequirementContract`; its `selection.signature` equals that entry's callable signature.
For `RestrictedEffects(E)`, `selection.selectionEffects = E`; for `InferEffects`, it is the empty
set in the entry's effect universe. `selection.inferredCapabilities` is the requirement's ordinary
caller-visible capability promise. `selection.concreteAvailability` is `None` unless the requirement
has a distinct, explicitly registered availability condition; it is never inferred from the
ordinary promise. Property and subscript maps are total exactly for their signature's `AccessorRole`
keys. Instantiation substitutes the signature, allowance, ordinary capability promise, and optional
concrete availability together; non-callable requirement kinds carry `NoCallableContract` and
cannot acquire a callable contract by lookup side state.

`IFC-KIND-007`: Property and subscript signatures are internally coherent products. Every accessor
signature has the product's receiver; every subscript accessor has the same index parameter prefix
identified by `indexSlots`; and its role-specific remaining parameter/result shape exposes exactly
the product's `valueType` under the versioned accessor-role schema. Construction rejects a product
whose getter, setter, or reference-accessor signature disagrees with these shared fields, so
matching never has to guess which duplicate is authoritative.

`IFC-KIND-008`: `AccessorRole.RefAccessor` is keyed by its complete access mode. The only source spellings
in the initial language version are `constref` for `RefAccessor(ReadAccess)` and `ref` for
`RefAccessor(ReadWriteAccess)`, as specified by `PAR-ACC-001`. Both keys may occur concurrently in one
property or subscript signature, contract, direct witness, compatibility proof, adapter plan, and
runtime interface-requirement dictionary. Satisfaction is exact by key: a mutable `ref` accessor does not satisfy
a required `constref` accessor, and a read-only accessor does not satisfy a required mutable one.
Each reference accessor's `AccessorReferenceResultContract` has referent equal to the product's
`valueType` and access exactly equal to its key; returning a bare value or a handle with the other
access is ill formed. Defaults, synthesis, serialization, and runtime slot projection preserve the
access index; they never select one role by source position or access-strength comparison.

`ParameterCorrespondence` maps semantic roles between two independently declared signatures. Its
keys are not compared for equality across declarations: requirement and implementation
`ParameterKey` values are expected to differ. Pack-expansion paths make every mapped slot explicit.

## Requirement identity under specialization and base-interface inheritance

A requirement declaration ID is not sufficient identity. An inherited requirement can be reached
through different specializations and through multiple arms of a diamond. The semantic key retains
that transport path. Chapter 5 is the schema authority for `RefinementStepKey` and
`RequirementKey<K>`; this chapter defines the slot that consumes them:

```text
RequirementSlot<K> = {
    key: RequirementKey<K>,
    instantiatedSignature: RequirementSignature<K>,
    instantiatedContract: RequirementContract<K>,
    optionality: Required | Optional(OptionalSemantics<K>),
    default: Option<InstantiatedDefault<K>>,
    conditions: GenericConditionSet,
    overrides: NodeList<RequirementKey<K>>,
    origin: Origin
}
```

The path is empty for a requirement declared directly by `view`. Each step is oriented from the
view toward the interface that introduced the declaration. Applying an interface substitution
rewrites `view`, `declaredIn`, every path instance, the signature, and its conditions as one
schema-driven operation.

```text
direct requirement r of instance I
------------------------------------------------ IFC-KEY-001
key(I,r) = RequirementKey(I,I,r,[],kind(r))

edge e : I refines J    k = RequirementKey(J,O,r,p,K)
---------------------------------------------------------------- IFC-KEY-002
transport(e,k) = RequirementKey(I,O,r,[e] ++ p,K)
```

`IFC-KEY-003`: Two requirement keys are equal only when all canonical fields above are equal. In
particular, paths through two arms of a diamond remain distinct keys even when they end at the same
source requirement. This is requirement-occurrence identity inside one witness table; it does not
create path-distinct `SubtypeWitnessId` values. Chapter 15 still selects one canonical outer witness
and super-facet route for each endpoint pair.

`IFC-KEY-004`: Equivalent diamond occurrences may share an immutable satisfaction value, but that
sharing is recorded by a typed `Reused` satisfaction; it must not be achieved by dropping a key. If path
substitutions produce different signatures, the occurrences cannot be reused.

`IFC-KEY-005`: A direct requirement may explicitly override inherited requirement slots only when
their kinds match and `CheckOverrideCompatibility` produces a proof for each named slot. The
inherited keys remain addressable for base-interface projection; their evidence may delegate to the
override through that proof.

`EnumerateRequirementSlots(I)` traverses direct requirements and base-interface edges in canonical key
order, instantiates every slot, and preserves all path-distinct occurrences. Source order is retained
as presentation metadata but does not define identity.

## Conformance identity and definition graphs

Conformance identity is separate from its definition so mutually referencing declarations and
synthesized artifacts can refer to a stable ID before a complete witness graph is frozen:

```text
WitnessTableForm =
    ConcreteWitnessTableForm(target: SubtypeWitnessTarget)
  | GenericWitnessTableForm(binder: CanonicalGenericBinder,
                       targetPattern: SubtypeWitnessTarget)

ConformanceProvider =
    Explicit(declaration: DeclId)
  | Builtin(rule: RuleId, inputs: CanonicalArguments)
  | Synthesized(output: SynthesizedSemanticId)

WitnessTableIdentityKey = {
    form: WitnessTableForm,
    provider: ConformanceProvider
}

WitnessTableId = ContentId<WitnessTableIdentityKey>

WitnessTableIdentity = {
    id: WitnessTableId,
    key: WitnessTableIdentityKey,
    origin: Origin
}

WitnessTableDefinition = {
    identity: WitnessTableId,
    form: WitnessTableForm,
    revision: WitnessTableDefinitionRevision,
    requirements: RequirementDictionary,
    inherited: NodeMap<RefinementStepKey, WitnessTableProjection>,
    contract: EffectiveConformanceContract,
    dependencies: NodeList<ValidatedWitnessTableRef>
}

WitnessTableDefinitionPublication = {
    definition: WitnessTableDefinition,
    definitionReference: ValidatedWitnessTableRef,
    candidate: SubtypeWitnessCandidateAt<Published>
}

ConditionalRequirementWitnessAt<K, S: WitnessTableState> =
    NodeList<GuardedRequirementWitnessAt<K, S>>

GuardedRequirementWitnessAt<K, S: WitnessTableState> = {
    condition: BooleanCapabilityPredicate,
    witness: RequirementWitnessAt<K, S>
}

ConditionalRequirementWitness<K> = ConditionalRequirementWitnessAt<K, Published>
GuardedRequirementWitness<K> = GuardedRequirementWitnessAt<K, Published>
ProvisionalConditionalRequirementWitness<K> = ConditionalRequirementWitnessAt<K, Construction>

WitnessTableProjectionAt<S: WitnessTableState> = {
    derived: SubtypeWitnessRef<S>,
    inheritance: RefinementStepKey,
    proof: InterfaceRefinementProof
}

projectedWitnessTarget(p: WitnessTableProjectionAt<S>) = {
    subtype = targetOf(p.derived).subtype,
    superInterface = p.proof.base
}

projectedWitnessId(p: WitnessTableProjectionAt<S>) =
    ContentId(CanonicalSubtypeWitness(projectedWitnessTarget(p)))

projectedWitnessCandidate(p: WitnessTableProjectionAt<S>) =
    let operation = LookupSubtypeWitness(
        base = p.derived.witness,
        key = BaseInterfaceEntry(p.inheritance))
    in SubtypeWitnessCandidateAt<S>(
        identity = resolve(projectedWitnessId(p)),
        form = formFor(projectedWitnessTarget(p)),
        operation = operation,
        resolutions = requiredResolutionSetAt<S>(operation),
        origin = originOf(p.inheritance))

ProvisionalWitnessTableProjection = WitnessTableProjectionAt<Construction>
WitnessTableProjection = WitnessTableProjectionAt<Published>

EffectiveConformanceContract = {
    genericConditions: GenericConditionSet,
    availability: CapabilitySet,
    visibility: DeclVisibility,
    semanticEnvironment: SemanticEnvironmentId
}
```

`DependentNodeMap` is one canonical heterogeneous map whose key carries the kind index and whose
value must carry the same index. It may be implemented as one tagged map or one map per kind, but
the generic schema and serializer validate the dependency.

`WitnessTableIdentity.id = ContentId(WitnessTableIdentity.key)`. A `WitnessTableId` is therefore
derived from provider identity and its concrete or generic witness-table form. It identifies the
provider table, not the language-level subtype witness. Provider identities remain distinguishable
while coherence compares them; after selection, chapter 15 gives the target pair exactly one
environment-qualified `SubtypeWitnessId` whose selected operation names the winning table.

`IFC-CON-001`: Publishing a `WitnessTableIdentity` publishes no positive proof that the target
conforms. A table-backed witness can discharge a constraint, pack an existential, or dispatch only
after its required definition is validated and its candidate wins canonical coherence selection.
Bound parameters, specializations, keyed lookups, and
existential extractions are positive witness operations under their own chapter 15 constructors; they
do not require manufacturing a new `WitnessTableDefinition`, but they are still selected under the
same endpoint-uniqueness rule.

`IFC-CON-002`: The identity/definition records form an immutable graph. Serialization permits
forward and SCC references, but graph representability does not legalize circular reasoning.

`IFC-CON-003`: A successful definition contains one kind-correct `InterfaceRequirementKeyOf<K>` and payload
for every active requirement slot and one base-conformance projection for every active base-interface
edge. It contains no recovery entry and no unresolved synthesis plan.

`IFC-CON-004`: A successful definition contains no `PendingLocal` effect or capability check in
any callable proof or plan. For local implementations, adapters, and rebound defaults, the final
satisfaction records the proofs produced after effect and capability inference stabilize. Building
the provisional requirement map and validating its effective contracts are separate immutable
query products.

`IFC-CON-005`: An explicit provider is identified by the canonical declaration's `DeclId` plus its
`WitnessTableForm`. A generic form contains the alpha-normalized binder and unspecialized
target pattern, so `S<T> : I<T>` has one provider/table identity; `S<float> : I<float>` is a
`SpecializedWitnessTable` value and not a second provider. No specialization frame or evidence for
the binder being defined enters provider identity. Bound generic evidence is represented directly
by `DeclaredSubtypeWitness`, never by a `ConformanceProvider`. A synthesized provider names the exact
`SynthesizedSemanticId` output, not merely a group that may contain several conformances.

`IFC-CON-006`: A `ValidatedWitnessTableRef` is constructible only while freezing a semantic snapshot
that contains a successful, complete `WitnessTableDefinition` at the stored identity and revision.
Resolution rechecks that the definition's `identity` and `revision` equal the reference. An
allocated `WitnessTableId`, a recovered definition, or a definition containing a pending contract
check cannot be converted to this definition reference. The definition's `form` equals the
identity key's form. A snapshot may freeze mutually
referencing definitions together after validating the whole SCC; this is why the revision names a
frozen definition record rather than recursively hashing its referenced definitions. The snapshot
assigns `definitionOrdinal` after canonical `WitnessTableId` sorting, never task completion order.
`WitnessTableDefinitionPublication` requires its definition identity/revision to equal its
`definitionReference` exactly. Its candidate operation is `GenericWitnessTable(identity)` for a
`GenericWitnessTableForm` form and `WitnessTable(identity)` for a `ConcreteWitnessTableForm`
otherwise; its resolution set maps that identity to the same `definitionReference`, and its
candidate identity uses only the form target. The selection query's semantic environment controls
candidate discovery but cannot change pair-only witness identity. The
publication does not bypass coherence by claiming the pair-identified witness. Only
`SelectCanonicalSubtypeWitness` may turn this candidate into the selected witness record.

`IFC-CON-007`: `identityOf(ValidatedWitnessTableRef(id, revision)) = id`. The revision is an exact
dependency stamp used to resolve and invalidate definition consumers; it is not a proof value and
never enters `WitnessTableId` or `SubtypeWitnessId`. Canonical type, symbol, specialization-frame,
exported-signature, and mangled identity use stable semantic IDs, because a new immutable snapshot
of the same canonical provider is not a new language-level conformance. Serialization retains the
revision in witness resolution sets for dependency checking but excludes it from wire-stable
witness identity.

`IFC-CON-008`: `BuildRequirementDictionary` returns `ProvisionalRequirementDictionary`, whose default
plans and witness uses are construction-stage and whose callable checks may be pending. Effect and
capability validation return their named validated dictionaries without changing keys, guards, candidate
identity, or non-contract evidence. Combining them requires byte-identical common input and yields
`FullyValidatedConstructionRequirementDictionary`. During atomic conformance freeze,
`publishRequirementDictionary` applies the `Construction -> Published` witness-reference rewrite
to every payload, including nested direct witnesses/proofs, adapter conversions and access
bindings, builtin witnesses, default-plan self references, and derived witnesses of inherited
`WitnessTableProjectionAt<Construction>`, and returns `RequirementDictionary`; it changes no other
semantic field. A failed rewrite, pending check, error satisfaction, or uncovered guard prevents
definition/reference publication.

`IFC-CON-009`: A construction-stage projection's `derived` witness targets the conformance whose
dictionary contains it. Its `InterfaceRefinementProof.path` is exactly the singleton `[inheritance]`; the
proof's derived/base endpoints equal that step's endpoints and the step starts at the interface
target of `derived`. Thus it proves one declared base-interface edge, not an unrelated multi-step route
that merely contains the key. `projectedWitnessId` is the canonical endpoint ID;
`projectedWitnessCandidate` contributes exactly one `LookupSubtypeWitness` operation with that key.
There is no
independently selected base proof and no transitive-witness node. Publication rewrites only the
derived witness's operational definition resolutions; both the derived and projected witness IDs
remain unchanged. If another inherited route contributes the same projected endpoint, chapter 15's
canonical selection proves equivalence/specificity or diagnoses the conformance as ambiguous.

`EffectiveConformanceContract` records the conditions, capabilities, visibility, and module
environment under which the evidence is valid. These facts do not silently alter callable type
equality.

## Conformance sources and coherence

```text
FindConformance(type, interface, semanticEnvironment, genericEvidence)
    -> ConformanceSearchResult

ConformanceSearchResult =
    Unique(SubtypeWitnessRef<Published>)
  | NotFound(ConformanceFailure)
  | Ambiguous(NonEmpty<ConformanceCandidate>)
  | Recovered(WitnessTableId, ErrorId)

ConformanceCandidateSource =
    BoundWitnessCandidate(witness: SubtypeWitnessRef<Published>)
  | TableProviderCandidate(identity: WitnessTableIdentity)

ConformanceCandidate = {
    source: ConformanceCandidateSource,
    target: SubtypeWitnessTarget,
    applicability: BooleanCapabilityPredicate,
    genericConditions: GenericConditionSet,
    semanticEnvironment: SemanticEnvironmentId,
    origin: Origin
}

ConformanceProviderSpecificityProof =
    BoundEvidenceControlsAbstractTarget(
        preferred: SubtypeWitnessId,
        shadowed: WitnessTableId,
        binder: CanonicalBinderRef,
        slot: CanonicalConstraintSlot)
  | StrictConformanceApplicabilitySubset {
        preferred: ConformanceCandidateSource,
        shadowed: ConformanceCandidateSource,
        targetMatch: CanonicalSpecializationSpine,
        constraintImplication: GenericConstraintImplicationProof,
        strict: TargetStrict | ConstraintStrict | BothStrict
    }
  | RegisteredConformancePriority(rule: RuleId,
                                  inputs: CanonicalArguments)

ConformanceFailureReason =
    NoProvider | RejectedProvider | InaccessibleProvider | ProofCycle |
    UnproductiveSearchGrowth

ConformanceFailure = {
    target: SubtypeWitnessTarget,
    reason: ConformanceFailureReason,
    considered: NodeList<ConformanceCandidate>,
    dependencyTrace: NodeList<DependencyEdge>,
    origin: Origin
}
```

The search considers these sources:

1. evidence explicitly bound by the current generic context;
2. explicit conformances declared on the type or in a reachable extension;
3. projections of an already available conformance through base-interface inheritance;
4. builtin conformance rules registered by the versioned standard environment; and
5. named implicit-synthesis rules, such as the callable conformance of a checked lambda
   environment.

There is no general structural or name-only conformance inference. Adding one requires a named
language rule and a distinct provider kind.

`IFC-FIND-001`: A source interface-conformance clause is an explicit provider. Its identity is
allocated from that declaration before its requirements are matched. A rejected concrete
struct-base clause is not a conformance provider.

`IFC-FIND-002`: An implicit conformance may be created only by a registered rule that supplies a
stable synthesis key, complete target, applicability predicate, and construction plan. Failure to
find an explicit conformance does not itself authorize synthesis.

`IFC-FIND-003`: Reachable extension conformances are environment-scoped. A query key includes the
semantic-environment revision; a result cached for one import graph cannot be reused in another.

`IFC-FIND-004`: Multiple candidates for the same target are inputs to the single canonical-witness
selection. Exact rediscovery of the same bound witness or `WitnessTableId` is deduplicated. Distinct
source providers are not duplicate witnesses that may coexist: one must be strictly more specific,
all lowering-observable operations must be proved equivalent, or the target is ambiguous. Source
order and import order are never coherence rules.

`IFC-FIND-005`: Public signatures and serialized generic evidence may use only conformances
reachable through the module's exported semantic environment. A private body may capture local
extension evidence, which then becomes an explicit body and IR dependency.

`IFC-FIND-006`: A provider is strictly more specialized only when matching its target pattern
against the other's target produces a substitution, its required constraints imply the other's
after that substitution, and at least one target or constraint relation is strict. Equivalently,
the preferred provider's applicability set is a strict subset of the shadowed provider's set. A
`StrictConformanceApplicabilitySubset` records both pattern matching and constraint implication.
The current compiler's extension genericity and parameter-count heuristics are compatibility
evidence, not this proof. If neither applicability set strictly includes the other, the providers
remain ambiguous.

`IFC-FIND-007`: `Unique` contains the pair-identified canonical witness plus all definition
resolutions required by its selected operation, not the provider identity allocated by
`DeclareWitnessTableIdentity`. If a selected table provider's
definition is still under construction, `FindConformance` is blocked on that definition or
participates in proof-cycle analysis; it never reports the allocated identity as successful
evidence. `Recovered` retains a bare identity only for diagnostic graph continuity and cannot
discharge a constraint.

`IFC-FIND-008`: Every considered candidate's stored target equals the search target after its
recorded generic conditions are solved, and its source is either a target-equal bound witness or a
table provider whose witness-table form specializes to that target. Its applicability predicate belongs to
the query's capability universe and semantic environment. `Ambiguous` contains the maximal
applicable candidates after source-key deduplication (`witness` ID or provider identity) and pairwise
strict-specificity comparison; `NotFound`
retains all considered candidates and the dependency trace that rejected them.

`IFC-FIND-009`: Evidence explicitly bound by the canonical generic context returns
the `DeclaredSubtypeWitness(target)` candidate, with the source constraint slot retained only in
the generic-evidence environment and inference trace. For an abstract target controlled by that
constraint, `BoundEvidenceControlsAbstractTarget` prevents a static table from replacing the runtime
generic argument. An unspecialized generic conformance contributes `GenericWitnessTable(provider)`;
applying arguments and keyed constraint witnesses contributes `SpecializedWitnessTable`. Canonical
selection then publishes the one endpoint-identified witness. None of these cases manufactures a
nongeneric frozen conformance reference for an abstract proof.

The initial specification recognizes no negative conformance and makes no closed-world inference
from absence. Loading another module may add an extension candidate to a private environment, but
cannot retroactively change an already published module interface because its exported environment
and evidence IDs are fixed.

## Requirement matching

Matching is split into an enumeration query per slot and a pure kind-specific comparator. It does
not mutate the conformance or synthesize declarations while searching:

```text
MatchRequirement(conformanceId, slot, capabilityRegion, candidateEnvironment)
    -> CheckResult<RequirementMatch<K>>

RequirementMatch<K> =
    Exact(payload: RequirementWitnessPayloadAt<K, Construction>,
          proof: RequirementCompatibilityProofAt<K, Construction>)
  | Adaptable(candidate: RequirementWitnessPayloadAt<K, Construction>,
              plan: RequirementAdapterPlanAt<K, Construction>)
  | Defaulted(default: InstantiatedDefault<K>, plan: DefaultUsePlan<K, Construction>)
  | Builtin(rule: RuleId, plan: BuiltinWitnessPlan<K>)
  | OptionalAbsent(proof: OptionalAbsenceProof<K>)
  | Missing(failure: RequirementFailure<K>)
  | Ambiguous(candidates: NonEmpty<RequirementCandidate<K>>)
  | Recovered(error: ErrorId, placeholder: RecoveryWitness<K>)

RequirementCandidateIdentity =
    DeclCandidate(declaration: DeclRef)
  | ExplicitMappingCandidate(owner: DeclRef,
                             requirement: SomeRequirementKey)
  | InheritedCandidate(witness: SubtypeWitnessId,
                       requirement: SomeRequirementKey)
  | DefaultCandidate(requirement: SomeRequirementKey)
  | BuiltinCandidate(rule: RuleId, inputs: CanonicalArguments)

DefaultShadowPolicy =
    UseDefaultWhenNoApplicableExplicitCandidate
  | RejectDefaultWhenAnyNamedCandidateExists

RequirementCandidate<K> = {
    identity: RequirementCandidateIdentity,
    application: ExactApplication(payload: RequirementWitnessPayloadAt<K, Construction>,
                                  proof: RequirementCompatibilityProofAt<K, Construction>)
               | AdapterApplication(payload: RequirementWitnessPayloadAt<K, Construction>,
                                    plan: RequirementAdapterPlanAt<K, Construction>)
               | DefaultApplication(default: InstantiatedDefault<K>,
                                    plan: DefaultUsePlan<K, Construction>)
               | BuiltinApplication(rule: RuleId,
                                    plan: BuiltinWitnessPlan<K>),
    origin: Origin
}
```

`capabilityRegion` is a canonical `BooleanCapabilityPredicate` within the conformance's availability
formula. `BuildRequirementDictionary` obtains a match for every region in which candidates' optional
concrete availability can change the applicable set, then canonicalizes the guarded results with
`WIT-ALG-005`. Ordinary `inferredCapabilities` never partition the candidate set.

The sum is indexed by the slot kind. For example, an associated-type match contains a canonical
type and constraint proofs; a callable match contains a canonical declaration reference and a
callable-signature proof; a nested-conformance match contains a stage-appropriate
`SubtypeWitnessRef<S>` whose semantic operand is an `SubtypeWitnessId`.

Candidate discovery uses the requirement's declared lookup role and the conformance declaration's
explicit mappings. It retains inaccessible and wrong-kind candidates as structured rejection data
for diagnostics. Candidate evaluation then:

1. instantiates the requirement signature with concrete `This` and interface arguments;
2. checks declaration/value kind;
3. checks generic binder and substitution compatibility;
4. compares the full signature, including receiver presence/mode/traits, expanded parameter-slot
   structure and modes, result/error types, and differentiability traits, and records the mapping
   from requirement `ParameterKey` values to implementation `ParameterKey` values;
5. proves visibility immediately; checks `selectionEffects`; compares the requirement and
   implementation `inferredCapabilities` as an ordinary contract whose local effective check remains
   pending; and separately proves concrete-availability compatibility between the two optional
   `concreteAvailability` fields without consulting the current call world's availability;
6. constructs an adapter plan only for conversions explicitly permitted for this requirement kind;
   and
7. ranks exact, adaptable, and default candidates under the rules below.

`IFC-MAT-001`: `Exact` means no runtime adapter and no omitted semantic obligation. Alpha-renaming
of binders and canonical substitution are not adapters.

`IFC-MAT-002`: An adapter is legal only when its plan proves every receiver, parameter, result,
error, effect, ordinary inferred-capability, concrete-availability, and ownership step and records
any pending effective inferred-capability obligation. Ordinary implicit-call conversions do not
automatically become conformance adapters.

`IFC-MAT-003`: A unique exact candidate is preferred to adaptable candidates. Among adaptable
candidates, the kind-specific partial order compares complete adapter plans; unrelated minimal
plans are ambiguous. Stable declaration order is diagnostic metadata only.

`IFC-MAT-004`: A wrong-kind or incompatible same-name declaration is a rejected candidate, not a
witness. Whether it suppresses a default is determined by `DefaultShadowPolicy` in the language
version; the initial policy is `UseDefaultWhenNoApplicableExplicitCandidate`, which reports
rejected declarations as notes.

`IFC-MAT-005`: `Blocked` is scheduler state and is not a `RequirementMatch` alternative. A match
query waiting on a signature, associated projection, or nested conformance publishes nothing.

`IFC-MAT-006`: Local requirement matching must not request `InferCapabilities` or an effective
local callable contract. It compares the pre-inference `inferredCapabilities` fields and stores
`PendingLocal(InferredCapabilityCompatibilityObligation)`. After all referenced local
`InferCapabilities` queries reach their fixpoint, conformance validation creates a new immutable
result with `ValidatedLocal`, proving the requirement's ordinary promise entails the
implementation's effective requirement. An imported candidate uses its published effective
ordinary contract and stores `ValidatedImported` immediately. In both cases, matching separately
validates `ConcreteAvailabilityCompatibilityProof` from the optional pre-inference fields under the
active requirement-match region; concrete availability is not body-inferred, does not become
pending, and is not substituted for the ordinary compatibility obligation.

`IFC-MAT-007`: Effect checking uses the parallel chapter 5 split. Local matching compares only
`selectionEffects` with the requirement's `EffectAllowance` and stores a
`PendingLocal(RequirementEffectCompatibilityObligation)` in the contract proof. After
`InferEffects` stabilizes, conformance validation produces `ValidatedLocal`; imported candidates
may produce `ValidatedImported` from their published effective effect set. Requirement matching
never inserts an effective-effect query into the inference SCC.

`IFC-MAT-008`: Every applicable candidate has one canonical `RequirementCandidateIdentity`, and
the identity's source must produce the stored kind-indexed application. `Ambiguous` contains only
applicable candidates after deduplication by this identity; rejected declarations are represented
only by `RequirementCandidateFailure`. Candidate serialization and diagnostic ordering use the
identity, never discovery order or an address.

## Kind-correct satisfactions and absence

Successful matching and any required synthesis produce the following typed evidence:

```text
RequirementWitnessAt<K, S: WitnessTableState> =
    Direct(payload: RequirementWitnessPayloadAt<K, S>,
           proof: RequirementCompatibilityProofAt<K, S>)
  | Adapted(declaration: DeclRef, plan: RequirementAdapterPlanAt<K, S>)
  | Default(entryPoint: Option<DeclRef>, plan: DefaultUsePlan<K, S>)
  | Builtin(payload: BuiltinWitnessAt<K, S>)
  | Inherited(projection: WitnessTableProjectionAt<S>, nestedKey: RequirementKey<K>)
  | Reused(target: RequirementKey<K>, proof: RequirementReuseProof<K>)
  | OptionalAbsent(proof: OptionalAbsenceProof<K>)
  | Error(error: ErrorId, placeholder: RecoveryWitness<K>)

ProvisionalRequirementWitness<K> = RequirementWitnessAt<K, Construction>
RequirementWitness<K> = RequirementWitnessAt<K, Published>
```

The schema specializes this sum by kind; impossible variants are not constructible. A nested
conformance is a `Direct(NestedWitness(...), NestedProof(...))`, while `Adapted` is available only
to member kinds with a declared adapter algebra.

`WIT-KIND-001`: The validator checks the requirement key, instantiated signature, satisfaction
kind, proof endpoints, and referenced conformance target together. Matching a physical payload tag
without these endpoint checks is insufficient.

`WIT-ABS-001`: `OptionalAbsent` is a successful, deliberate absence only for a slot declared
optional and only with a proof naming its optional semantics. A consumer observes it as `None`; it
cannot be invoked, projected as a type, or used to discharge a required constraint.

`WIT-ABS-002`: `Missing` is a failed match and never occurs in a successful witness map. `Error` is
typed recovery and prevents publication of a successful module. Neither is interchangeable with
`OptionalAbsent`.

`WIT-ABS-003`: An optional witness use first performs `PresenceTest` and may unwrap evidence only
on the present branch. The subsequent operation must occur in the slot's kind-indexed
`permittedUses`; `GuardedAccessor(a)` additionally requires that exact property/subscript role.
Absence produces `NoneAtUse` and never manufactures `TypeId`, `ConstValue`, `CallableValue`, or
constraint evidence. The standard-environment rule fixes the set for the language version.

`WIT-REUSE-001`: `Reused` edges form an acyclic forest oriented to the canonical smallest
compatible target key or to an overriding direct key. Validation expands the edge and rechecks
kind/signature compatibility, so witness reuse cannot hide a diamond conflict.

## Defaults

A default is checked once under the interface's generic binder and abstract `This`. Its checked
form records all requirement dispatches it performs; applying it to a conformance substitutes the
interface instance and supplies that conformance's identity for `This` dispatch.

Defaults may be:

- a default associated type or value plus proofs of its declared constraints;
- a checked interface method/accessor/constructor body;
- a forwarding reference to another requirement key; or
- a builtin plan registered by a standard-environment rule.

`IFC-DEF-001`: A default does not itself prove that a type conforms. It is one candidate for one
requirement slot after the witness-table identity and instantiated slot are known.

`IFC-DEF-002`: A default member that needs a concrete entry point is rebound or thunked through a
`DefaultUsePlan`; it is not cloned and mutated in the source interface declaration.

`IFC-DEF-003`: Inherited defaults at incomparable base-interface paths are ambiguous unless they are
the same canonical default under equal substitution or an explicit override resolves them.

`IFC-DEF-004`: A rebound default body may call other requirements through its construction-stage
self witness. When its resolution set contains `OperationalWitnessDefinition`, it cannot close a
nested-conformance proof cycle that recursively requires the same unfinished definition.
Operational recursion is distinct from proof recursion.

`IFC-DEF-005`: Instantiating or rebinding a constrained default retains its ordered
`SpecializationFrame` values, including keyed required evidence and explicit optional absence.
Synthesis cannot reconstruct evidence from argument position or re-run conformance search under a
possibly different environment.

`IFC-DEF-006`: `DefaultUsePlan.instantiated` is the sole owner of the default's specialization
frames; the plan does not copy them. In `RequirementWitness::Default`, `entryPoint` denotes
only a synthesized callable entry point, never the source default declaration held by
`DefaultImplementation`. It is `Some` exactly when `entryPointRequired` is true, has the exact
required signature, and its body interprets the plan. With no entry point, the plan's kind-indexed
`output` is the direct evidence.

`IFC-DEF-007`: Requirement matching and synthesis carry
`DefaultUsePlan<K, Construction>`. Its self reference has a stable witness ID plus either frozen
resolutions or an `OperationalWitnessDefinition` authorized by the current construction scope.
Atomic freeze applies a total identity-preserving rewrite
`publishDefaultPlan : DefaultUsePlan<K, Construction> -> DefaultUsePlan<K, Published>`: each
operational resolution becomes the newly frozen definition reference for the same `WitnessTableId`,
and the witness ID and every other plan field remain unchanged. Only the published form may occur
in `RequirementWitness<K>`.

## Kind-indexed requirement lookup and associated type projections

Chapter 5 is the sole authority for `Type::AssociatedTypeProjection`. Its `lookup.witness` field is
the pair-identified proof used to reach the requirement, and the constructor payload is exactly
`LookupRequirement<AssociatedTypeKind>`. The containing `CanonicalTypeRecord` carries the exact
frozen definition resolutions needed by the witness's selected operation in its dependency sidecar.
Endpoint equality determines the one witness ID across semantic environments. Environments may
discover different candidate operations, but composing them must select one strict specificity
winner or diagnose a coherence error; it cannot create a second witness ID or reinterpret an
existing associated-type projection. Definition revisions and source provenance are dependencies of
the checked use, not additional operands in canonical `TypeId` hashing.

When normalizing a published `CanonicalTypeRecord`, the caller supplies a
`SubtypeWitnessRef<Published>` made from the projection's witness and
`record.directWitnessDependencies[projection.witness]`. Normalization follows the witness
operation; it never reruns conformance search or reconstructs a base-interface path from endpoint
types.

```text
W : SubtypeWitnessRef<Published>
W.witness = w
targetOf(W).subtype = B
targetOf(W).superInterface = k.view
activeAssociatedTypeEntry(targetOf(W).superInterface, k)
lookupWitnessEntry(W, RequirementEntry(k)) =
    type witnesses semantically equal to T with equivalent constraint proofs
-------------------------------------------------------------------------------- WIT-PROJ-001
normalize(AssociatedTypeProjection(LookupRequirement(B,w,RequirementEntry(k))), W) = T
```

Requirement-map payloads are already instantiated: interface and lexical specialization frames,
including their keyed constraint evidence and optional absence, were applied exactly once while
building the slot and satisfaction. The same normalization applies to defaulted and builtin type
witnesses after validating their proofs. A projection through generic evidence remains an
irreducible canonical type until that evidence is specialized. A projection through
`OptionalAbsent`, a non-type slot, or recovery evidence is ill-formed.

`WIT-PROJ-002`: Associated-type constraint proofs are stored with the type satisfaction and are
substituted with it. Consumers do not re-run conformance search to rediscover those proofs.

`WIT-PROJ-003`: Projection normalization is
`NormalizeAssociatedTypeProjection(projection, witnessUse)`, where
`witnessUse.witness = projection.lookup.witness`. The query key includes the complete resolution set, so
definition revisions invalidate the query without entering canonical projection identity. A bound
or otherwise abstract witness whose associated-type entry is not yet available leaves the
projection irreducible; missing or mismatched resolutions for a table-backed operation are a
validation failure. An alias/projection cycle with no nominal constructor is rejected as an
associated type cycle; it does not normalize to a provisional arbitrary type.

`WIT-PROJ-006`: Constructing or deserializing
`AssociatedTypeProjection(LookupRequirement(B, w, RequirementEntry(k)))` validates the
same three endpoint premises shown in `WIT-PROJ-001`: `B` is exactly the witness subtype, `k.view`
is exactly its super-interface instance, and `k` is the active kind-correct associated-type entry
under that view/base-interface path. An unrelated base or requirement cannot be retained as a hashed
operand while normalization consults only the witness. Failed endpoint validation yields an error
type and never performs witness lookup.

`WIT-PROJ-004`: Equality of unresolved projections requires equal
`LookupRequirement<AssociatedTypeKind>` payloads or an explicit type-equality proof. Definition
revisions do not change canonical type identity; declaration names without the complete specialized
requirement key are not enough.

`WIT-PROJ-007`: A value expression `a` whose checked type is an existential containing `IFoo` may be
opened at a dominated use, and `a.AssocType` constructs an `AssociatedTypeProjection` using that
opening's extracted witness and the active associated-type key. This preserves current Slang source
syntax while making the generative opening and witness lookup explicit.

`WIT-PROJ-008`: The first edition does not admit term-dependent callable signatures. A parameter
type may depend on generic parameters and other type-level binders, but not on the identity or
existential opening of an earlier value parameter. Thus
`void foo(IBar a, a.AssocType b)` is rejected even though `a.AssocType` is legal in a dominated body
scope. Supporting such signatures later requires an explicit dependent binder, substitution,
mangling, calling-convention, and separate-compilation rule; it is not approximated by retaining a
body-local `OpenedTypeId` in `FuncType`.

`WIT-PROJ-005`: All guarded satisfactions for one associated-type key must produce semantically
equal types and constraint proofs on overlapping or incomparable target alternatives. Target
selection may change an implementation entry point, but cannot make canonical type equality depend
on an unavailable future target choice. Projection normalization therefore computes the canonical
common witness without a capability context; the revisions in its witness resolution set capture
guards and their capability-universe revision.

## Witness-map algebra and completeness

Requirement maps have a partial union, not last-write-wins insertion:

```text
RequirementEvidenceConflictAt<K, S: WitnessTableState> = {
    entry: InterfaceRequirementKeyOf<K>,
    overlap: BooleanCapabilityPredicate,
    left: RequirementWitnessAt<K, S>,
    right: RequirementWitnessAt<K, S>,
    reason: DistinctEvidence | FailedReuseProof(ErrorId)
}

SomeRequirementEvidenceConflictAt<S: WitnessTableState> =
    exists K: RequirementKind . RequirementEvidenceConflictAt<K, S>

MapMergeResultAt<S: WitnessTableState> = Compatible(RequirementDictionaryAt<S>)
    | Conflicts(NonEmpty<SomeRequirementEvidenceConflictAt<S>>)

mergeMaps<S>(M,N) =
    Compatible(canonical merged condition partitions)
        if every overlapping (witness-entry key, capability region) has equal evidence or
           CheckEquivalentEvidence produces a RequirementReuseProof
    Conflicts(all incompatible key/region/evidence triples)
        otherwise
```

Unqualified conflict/result names and `mergeMaps` mean their `<Published>` forms.
`SynthesisConstruction` combines provisional fragments with `mergeMaps<Construction>`; publication
is a separate total stage rewrite after the combined construction map validates.

`WIT-ALG-001`: At either witness-use stage, `mergeMaps<S>` is commutative and associative on
compatible maps. A conflict is a typed `MapMergeResultAt<S>`, never a
`RequirementWitnessAt<K,S>`, and cannot depend on insertion order.

`WIT-ALG-002`: Conformance substitution transports each witness-entry key by applying
`IFC-KEY-002` to its enclosed requirement key, substitutes every payload and proof, and retains
evidence identity. It never zips a substituted requirement list with an old witness list.

`WIT-ALG-003`: For every target environment in which the conformance contract is available, each
active required slot has exactly one active non-error satisfaction. Optional slots have exactly one
satisfaction, which may be `OptionalAbsent`. Conditional alternatives must be disjoint or have
identical evidence on their overlap and must cover the conformance's availability formula.

`WIT-ALG-004`: A base-interface projection is keyed by its `RefinementStepKey` and constructs one
`LookupSubtypeWitness` for that key. Diamond base paths therefore remain distinguishable even when
their nested witness graphs share storage.

`WIT-ALG-005`: `ConditionalRequirementWitness` is a canonical partition over chapter 10's full
`BooleanCapabilityPredicate` domain, not the positive requirement-formula domain. Normalization may
therefore split overlaps using complement, merges adjacent/equivalent evidence regions, removes
unsatisfiable regions, and sorts by canonical predicate then evidence identity. A consumer supplies
a capability context and obtains one value or a structured uncovered/ambiguous-region failure.

## Synthesis plans and atomic groups

Requirement matching produces plans, never half-built declarations. A synthesis planner converts
all selected matches for one semantic cause into one transaction:

```text
SynthesisKey = {
    rule: RuleId,
    cause: StableSemanticId,
    semanticArguments: CanonicalArguments
}

SynthesisOutputKind =
    DeclOutput | WitnessTableIdentityOutput | WitnessTableDefinitionOutput |
    WitnessOutput | SchemaValueOutput

SynthesisOutputRole = {
    kind: SynthesisOutputKind,
    stableName: QualifiedName,
    ordinal: UInt32
}

SynthesizedSemanticId = {
    group: SynthesisKey,
    role: SynthesisOutputRole,
    requirement: Option<SomeRequirementKey>
}

SynthesizedDeclId = {
    semantic: SynthesizedSemanticId where semantic.role.kind = DeclOutput,
    declaration: DeclId
}

SemanticDependency =
    QueryDependency(QueryKey)
  | DeclDependency(DeclRef)
  | WitnessTableDependency(ValidatedWitnessTableRef)
  | SynthesisDependency(SynthesisKey)

SynthesisPlan<K> = {
    key: SynthesisKey,
    requirement: RequirementKey<K>,
    outputIds: NodeList<SynthesizedSemanticId>,
    recipe: RequirementAdapterPlanAt<K, Construction> |
            DefaultUsePlan<K, Construction> |
            BuiltinWitnessPlan<K>,
    dependencies: NodeList<QueryKey>,
    origin: Origin
}

SynthesisConstruction = {
    key: SynthesisKey,
    declarations:
        CanonicallyOrderedMap<SynthesizedDeclId, ElaboratedDeclAt<Construction>>,
    witnessTableIdentities:
        CanonicallyOrderedMap<WitnessTableId, WitnessTableIdentity>,
    provisionalRequirements:
        CanonicallyOrderedMap<WitnessTableId, ProvisionalRequirementDictionary>,
    effectUseGraphs:
        CanonicallyOrderedMap<DeclRef, EffectUseGraph<Construction>>,
    capabilityUseGraphs:
        CanonicallyOrderedMap<DeclRef, CapabilityUseGraph<Construction>>,
    contractCompletions: ContractCompletionMap,
    uses: NodeMap<AnyNodeId, SynthesizedSemanticId>,
    dependencies: NodeList<SemanticDependency>
}

SynthesisGroupDraft = {
    key: SynthesisKey,
    declarations: CanonicallyOrderedMap<SynthesizedDeclId, ElaboratedDeclAt<Published>>,
    witnessTableIdentities: CanonicallyOrderedMap<WitnessTableId, WitnessTableIdentity>,
    witnessTableDefinitions: CanonicallyOrderedMap<WitnessTableId, WitnessTableDefinition>,
    uses: NodeMap<AnyNodeId, SynthesizedSemanticId>,
    dependencies: NodeList<SemanticDependency>
}

SynthesisGroup = {
    key: SynthesisKey,
    declarations: CanonicallyOrderedMap<SynthesizedDeclId, ElaboratedDeclAt<Published>>,
    witnessTableIdentities: CanonicallyOrderedMap<WitnessTableId, WitnessTableIdentity>,
    witnessTableDefinitions: CanonicallyOrderedMap<WitnessTableId, WitnessTableDefinition>,
    uses: NodeMap<AnyNodeId, SynthesizedSemanticId>,
    dependencies: NodeList<SemanticDependency>
}
```

Output identities derive from `(group key, output role, requirement key)`, not allocation or task
order. A rule registers a canonical `(stableName, ordinal, kind)` for each output role; two outputs in one
group cannot share the same role and requirement. `SynthesisGroupDraft` does not mean a partial
witness-table definition: it is an immutable, unpublished publication candidate whose
`WitnessTableDefinition` values are already complete.

`SYN-GRP-000`: `SynthesisOutputRole` is provenance-free canonical identity. A generated
declaration may separately carry a source-facing `Name` and `Origin::Synthesized`, but neither is
copied back into its output role. This makes the `SynthesizedSemanticId`/origin graph finite and
prevents diagnostic spelling from changing semantic identity.

`SynthesisConstruction` is the sole typed owner of construction-stage generated bodies and their
operational witness effect/capability edges. It is immutable but not publishable. No
`CallableValue<Construction>`, `ConversionPlan<Construction>`, operational conformance reference,
or provisional requirement map may occur outside this value and its named validation queries.

`freeze(plans)` first builds `SynthesisConstruction`, canonicalizes identities, and reserves their
definition-revision coordinates
without constructing a `ValidatedWitnessTableRef`. It then validates generated bodies, merged
requirement fragments, and the whole raw-ID proof-dependency graph. Private provisional handles are
permitted in construction-stage witness resolution sets inside this transaction but cannot escape
in a published semantic node or query result. If
validation succeeds, freeze simultaneously materializes the complete definitions and their
frozen validated definition references, applies `publishElaboratedDecl` to every generated declaration, rewrites
every provisional effect/capability/requirement edge, and constructs `SynthesisGroupDraft`.
The final step publishes the byte-identical `SynthesisGroup`; failure before that step exposes
neither the draft nor any reference.

`SYN-GRP-001`: Validate and publish a synthesis group atomically. Its declarations, conformance
identities, complete definitions, and uses become visible together or not at all.

`SYN-GRP-002`: Group validation checks every generated body against its declared signature, every
planned satisfaction against its requirement, every intra-group reference, and the absence of
duplicate output roles. Construction requirement-map fragments combine only through
`mergeMaps<Construction>`; only after the
merged maps, effect/capability fixpoints, and complete SCC validate may the stored
`contractCompletions` freeze contract states alongside definitions, references, and the
immutable group draft. A failed group produces typed recovery for its cause and publishes no
successful artifact.

`SYN-GRP-003`: Repeating synthesis with the same key and dependency hashes is idempotent and
byte-identical. Two requests for the same key share the result; two different keys cannot capture
one another's provisional IDs.

`SYN-ADP-001`: A synthesized requirement adapter has the exact required callable signature. Its
body is a direct interpretation of the validated adapter plan and cannot perform lookup, overload
resolution, conversion search, or conformance discovery.

`SYN-ADP-002`: A witness-table definition is frozen only after all required synthesis plans have
been incorporated into its group. An `Adaptable` match is not itself a witness-map entry.

## Lambda callable and interface-wrapper synthesis

A typed lambda uses one atomic synthesis group containing its environment type, capture fields,
initializer, invoke method, callable-conformance witness-table identity and definition, and the lambda value's
uses. Capture discovery runs on the bound body; capture mode, lifetime, and result typing run on the
typed body before this group is planned.

`IFC-LAM-001`: The callable conformance target and call requirement key come from the versioned
standard environment, and runtime invocation uses its `CallableEntry` `RuntimeInterfaceRequirementKey`.
The invoke witness is matched by the same kind-indexed rules as a
source-written conformance; lambda-environment field order is never witness identity.

`IFC-LAM-002`: Lambda result inference joins all reachable returns plus normal fall-through, with
`BottomType` and recovery handled explicitly, before the callable signature or conformance is
frozen.

`IFC-LAM-003`: A captureless lambda may convert to a raw function type only through a named
`CapturelessFunctionThunk` synthesis rule. The lambda's atomic group is keyed by the lambda and
required raw function signature and contains the thunk plus any lambda-environment artifacts
required by that elaboration. The thunk does not change the environment type's callable
conformance.

An interface wrapper is similarly explicit:

```text
WrapperRepresentation =
    InlineOwned
  | BoxedOwned(boxType: TypeId, allocationRule: RuleId)
  | BorrowedReference(access: StorageAccessMode)
  | SharedHandle(handleType: TypeId)

WrapperInitializationPlan =
    InitializeWithConversion(conversion: ConversionPlan<Construction>)
  | CallInitializer(callee: DeclRef,
                    signature: CallableSignatureId,
                    arguments: NodeList<StorageAccessPlanBindingAt<Construction>>)
  | BuiltinInitializer(rule: RuleId, inputs: CanonicalArguments)

WrapperCopyPlan =
    CopyForbidden
  | TrivialCopy(rule: RuleId)
  | CopyWith(callee: DeclRef, signature: CallableSignatureId)

WrapperMovePlan =
    MoveForbidden
  | TrivialMove(rule: RuleId)
  | MoveWith(callee: DeclRef, signature: CallableSignatureId)

WrapperDestroyPlan =
    NoDestroy
  | TrivialDestroy(rule: RuleId)
  | DestroyWith(callee: DeclRef, signature: CallableSignatureId)

WrapperStoragePlan = {
    sourceType: TypeId,
    field: SynthesizedDeclId,
    storedType: TypeId,
    representation: WrapperRepresentation,
    initialize: WrapperInitializationPlan,
    copy: WrapperCopyPlan,
    move: WrapperMovePlan,
    destroy: WrapperDestroyPlan
}

LifetimePlan =
    OwnedStorage(wrapperLifetime: LifetimeId)
  | BorrowedStorage(sourceLifetime: LifetimeId,
                    wrapperLifetime: LifetimeId,
                    access: StorageAccessMode,
                    outlives: OutlivesProof)
  | SharedStorage(wrapperLifetime: LifetimeId,
                  retain: DeclRef,
                  release: DeclRef)

InterfaceWrapperPlan = {
    sourceType: TypeId,
    targetInterface: InterfaceInstanceKey,
    storage: WrapperStoragePlan,
    requirementPlans:
        DependentNodeMap<K: RequirementKind, InterfaceRequirementKeyOf<K>, SynthesisPlan<K>>,
    lifetime: LifetimePlan
}
```

`SYN-WRP-001`: A wrapper may be introduced only by a named conversion or language rule. Failure of
ordinary conformance search does not imply structural wrapper synthesis.

`SYN-WRP-002`: The wrapper type, storage/init declarations, forwarding thunks, conformance, and
existential pack operation are one synthesis group. Ownership and lifetime conversions are explicit
in `WrapperStoragePlan`.

`SYN-WRP-003`: `storage.sourceType` equals `InterfaceWrapperPlan.sourceType`; `field` is a
declaration output of the same synthesis group with `storedType`. A conversion initializer has
exact source/stored endpoints. Callable and builtin initializers, copy/move operations, and
destruction are validated against the stored representation, and all of their effects and
capability requirements enter the generated bodies' contracts. `CopyForbidden` or `MoveForbidden`
is enforced on the synthesized wrapper type rather than repaired during lowering.

`SYN-WRP-004`: Representation and lifetime are paired exactly: inline/boxed ownership requires
`OwnedStorage`; `BorrowedReference(a)` requires `BorrowedStorage(..., a, outlives)` whose proof says
the source lifetime outlives the wrapper lifetime; and `SharedHandle` requires `SharedStorage` with
validated retain/release callables. Borrowed storage cannot be packed or returned beyond its proven
lifetime. Shared and boxed cleanup must be represented by the matching destroy plan; no hidden
retain, release, allocation, or destruction may be added by IR lowering.

`SYN-WRP-005`: `requirementPlans` is total for the target interface's active
`InterfaceRequirementKeyOf<K>` values, and every map key encloses the same requirement key stored in its
`SynthesisPlan<K>`. Freeze interprets those plans into the wrapper conformance's all-kind witness
map; map order is not declaration or ABI order.

## Existentials and witness use

Packing a value as an existential requires a published `SubtypeWitness`. The package
stores the value representation plus `SubtypeWitnessRef<Published>`; this may denote a static table,
a specialized generic table, a bound witness supplied at runtime, or a lookup result. Opening
creates a fresh `OpenedTypeId`, a value of that abstract type, and an
`ExtractExistentialSubtypeWitness` projected from the package.

`WIT-USE-001`: A runtime witness member lookup is
`(SubtypeWitnessRef<Published>, RuntimeInterfaceRequirementKey)`. The resulting `CallableValue` records direct,
adapted, default, builtin, or inherited dispatch. Dispatch is not recovered from `FuncType`,
declaration nesting, witness-table position, or an allocated-but-unvalidated witness-table identity.

`WIT-USE-002`: Projecting a derived conformance to a refined interface follows the named
`RefinementStepKey`. In a diamond, every path contributes an operational
`LookupSubtypeWitness` candidate for the same endpoint. The environment publishes the one canonical
path only after deduplicating the exact same provider/path or proving one distinct path explicitly
more specific; otherwise the endpoint is ambiguous. A use therefore consumes the canonical
pair-identified witness and never chooses a path ad hoc.

`WIT-USE-003`: IR may assign compact numeric slots after canonical sorting, but serialized IR
retains the requirement key-to-slot map. Slot number is an encoding, never semantic identity.

`WIT-USE-004`: A construction-stage generated/default body may form
`(SubtypeWitnessRef<Construction>, RuntimeInterfaceRequirementKey)`. An
`OperationalWitnessDefinition(OperationalWitnessTableRef)` resolution is valid only when its scope
is the query or synthesis transaction that owns that body and its identity is one of the
transaction's allocated conformances. It may appear in construction-stage dispatch, provisional
nested witnesses, projections, and effect/capability use graphs, but cannot escape into a published
AST, existential package, or IR. Atomic freeze replaces only that resolution with
`FrozenWitnessDefinition(ValidatedWitnessTableRef)` after the referenced definition validates;
otherwise the containing body and transaction are discarded. The stable witness ID is unchanged,
and a published witness call accepts only `SubtypeWitnessRef<Published>`.

## Scheduler interaction and proof cycles

Interface checking is decomposed into policy-homogeneous queries:

| Query                                                                           | Result                                            | Cycle policy                                                                       |
| ------------------------------------------------------------------------------- | ------------------------------------------------- | ---------------------------------------------------------------------------------- |
| `CheckInterfaceDecl(decl)`                                                      | `InterfaceDecl<Typed>`                            | reject structural header cycles                                                    |
| `EnumerateRequirementSlots(instance)`                                           | instantiated slots                                | reject interface-inheritance cycles                                                |
| `DeclareWitnessTableIdentity(provider,target)`                                  | identity                                          | nominal identity allocation                                                        |
| `FindConformance(target,environment,evidence)`                                  | search result                                     | reject ungrounded search cycles                                                    |
| `MatchRequirement(conformance,key,region)`                                      | kind-indexed match                                | inherit dependency failure; no provisional match                                   |
| `BuildRequirementDictionary(conformance)`                                       | `ProvisionalRequirementDictionary`                | reject unproductive proof cycles                                                   |
| `ValidateConformanceEffects(conformance,provisional)`                           | `EffectValidatedRequirementDictionary`            | `Reject`; requests only stabilized effect results and diagnoses false promises     |
| `ValidateConformanceCapabilities(conformance,provisional)`                      | `CapabilityValidatedRequirementDictionary`        | `Reject`; requests only stabilized capability results and diagnoses false promises |
| `CombineRequirementDictionaryValidation(effectDictionary,capabilityDictionary)` | `FullyValidatedConstructionRequirementDictionary` | reject unequal provisional inputs                                                  |
| `BuildWitnessTableDefinition(id,validatedDictionary)`                           | `WitnessTableDefinitionPublication`               | reject proof cycles unless a named productive rule applies                         |
| `NormalizeAssociatedTypeProjection(projection,evidence)`                        | type                                              | reject mismatched evidence and unguarded projection/alias cycles                   |
| `PlanSynthesis(cause)`                                                          | synthesis plan/group                              | reject synthesis-key recursion                                                     |
| `PublishSynthesisGroup(key)`                                                    | frozen group                                      | atomic publication barrier                                                         |

`BuildRequirementDictionary` reads only `selectionEffects`, `inferredCapabilities`, and
`concreteAvailability`; it cannot add an effective-contract node to either inference SCC. The
ordinary capability field creates only the stored pending obligation, while the concrete field is
checked by its immediate compatibility proof. `ValidateConformanceEffects` and
`ValidateConformanceCapabilities` are downstream of all relevant stabilized results, and neither
`InferEffects` nor `InferCapabilities` depends on its validation query.
`CombineRequirementDictionaryValidation` verifies both products refine the identical provisional dictionary;
`BuildWitnessTableDefinition` consumes only the combined result and performs the publication-stage
rewrite from `IFC-CON-008`. These one-way boundaries are the cycle-safe splits defined by chapters
4 and 9.

Identity allocation and definition construction are separate query kinds because they have
different cycle policies. A query may refer to an allocated identity while constructing method
bodies or operational witness dispatch, but it may not treat that reference as a completed proof.

`IFC-CYCLE-001`: A proof-dependency SCC consisting only of `FindConformance`, nested-conformance,
projection, or reused-evidence edges is rejected. "`T : I` because `T : I`" is not evidence.

`IFC-CYCLE-002`: A cycle is accepted only by a named rule whose validator identifies a productive
constructor independent of the cyclic proof edge. Merely having an explicit declaration or a
preallocated identity is not productive.

`IFC-CYCLE-003`: Default and generated method bodies may recursively call through a witness whose
resolution contains a scoped `OperationalWitnessTableRef` after the identity is allocated; such
body-call edges are operational and do not enter the proof SCC. Their capability/effect inference
follows chapter 11's fixpoint policy over construction-stage witness-use edges.

`IFC-CYCLE-004`: Per-root budgets limit semantic term growth as well as SCC iteration. A chain such
as successively generated `I<F<T>>`, `I<F<F<T>>>`, ... receives one deterministic resource-cycle
diagnostic even though every query key is distinct.

All query keys include the immutable generic, visibility, capability, and semantic-environment
contexts they read. A requirement match cannot reuse a result computed under a different reachable
extension set or a different generic evidence map.

## Diagnostics and recovery

Failures are structured:

```text
RequirementFailureReason =
    NoCandidate | WrongKind | SignatureMismatch | GenericMismatch |
    ReceiverMismatch | ModeMismatch | EffectMismatch |
    InferredCapabilityMismatch | ConcreteAvailabilityMismatch |
    DeclVisibilityMismatch | AssociatedConstraintFailure |
    ConformanceRequirementFailure | SynthesisFailure

RequirementCandidateFailure = {
    identity: RequirementCandidateIdentity,
    observedKind: Option<RequirementKind>,
    reason: RequirementFailureReason,
    origin: Origin
}

RequirementFailure<K> = {
    key: RequirementKey<K>,
    reason: RequirementFailureReason,
    rejectedCandidates: NodeList<RequirementCandidateFailure>,
    dependencyTrace: NodeList<DependencyEdge>,
    origin: Origin
}
```

`IFC-DIAG-001`: A conformance emits at most one primary diagnostic for each unsatisfied requirement
key. Path-distinct diamond requirements may each diagnose, but equivalent failures may be grouped
under one primary with keys and base-interface paths as ordered notes.

`IFC-DIAG-002`: Diagnostics sort by conformance origin, canonical requirement key, failure-class
priority, and stable candidate identity. Worker completion, map iteration, and import discovery
order are not observable.

`IFC-DIAG-003`: Ambiguity reports every maximal candidate and the failed comparison between them.
Missing-requirement diagnostics retain wrong-kind and incompatible same-name candidates as notes.

`IFC-DIAG-004`: Recovery constructs an `Error` satisfaction with the root `ErrorId` so unrelated
requirements can still be checked. A recovered conformance cannot discharge a successful generic
constraint, cross a module-interface boundary, or be packed into a successful existential.

## Compatibility and open-world notes

The current compiler's `RequirementDictionary` is already keyed by requirement declaration, which
is the correct starting direction. `RequirementWitness` and `WitnessTable`, however, are mutable and
can expose an incomplete table while conformance checking performs several order-sensitive passes.
The replacement preserves keyed lookup while adding specialization/path identity, kind-indexed
payloads, immutable identity/definition graphs, and atomic synthesis.

The following choices are proposed normative behavior and require differential compatibility
coverage:

- path-distinct requirement keys for base-interface diamonds;
- no implicit structural conformance except named language rules;
- extension-scoped conformance coherence independent of import order;
- defaults used only after no applicable explicit candidate under `DefaultShadowPolicy`; and
- strict rejection of unproductive conformance proof cycles.

`extension IFoo` is not part of this language: chapter 15 rejects an interface or existential
extension target before it can contribute members or conformances. Generic extensions of concrete
nominal patterns may use interface constraints, but that does not reinterpret the target as the
interface or all conforming values.

## Rule-linked validation

The test manifest uses `<rule-id>/<class>/<case>`, where `class` is `positive`, `negative`,
`boundary`, `recovery`, `serialization`, `permutation`, or `mock`. At minimum it contains:

| Rule family                 | Required concrete test IDs                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| --------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| interface identity          | `IFC-INS-004/serialization/this-type-binder-id`, `IFC-INS-005/permutation/equal-inheritance-clause-discriminator`                                                                                                                                                                                                                                                                                                                                                               |
| kind indexing               | `IFC-KIND-001/negative/type-in-callable-slot`, `IFC-KIND-002/positive/accessor-role-map`, `IFC-KIND-005/serialization/associated-constraint-slot`, `IFC-KIND-006/negative/detached-callable-contract`, `IFC-KIND-007/negative/incoherent-accessor-product`, `IFC-KIND-008/positive/constref-and-ref-coexist`, `IFC-KIND-008/negative/ref-does-not-satisfy-constref`, `IFC-LOOKUP-001/positive/associated-lookup-is-type`, `IFC-LOOKUP-001/negative/callable-lookup-is-not-type` |
| callable equality/roles     | `IFC-CALL-001/negative/unequal-field-certificate`, `IFC-CALL-002/positive/alpha-equal-signatures`, `IFC-CALL-003/negative/duplicate-implementation-target`, `IFC-CALL-010/negative/accessor-index-map-disagreement`                                                                                                                                                                                                                                                             |
| callable access/error       | `IFC-CALL-004/mock/access-plan-endpoints`, `IFC-CALL-004/negative/adapter-input-mismatch`, `IFC-CALL-005/boundary/catch-residual-error`, `IFC-CALL-008/negative/frame-owner-mismatch`, `IFC-CALL-011/positive/physical-constref-forward`, `IFC-CALL-011/negative/no-constref-temporary`                                                                                                                                                                                         |
| callable contracts          | `IFC-CALL-006/mock/local-vs-imported-checks`, `IFC-CALL-007/negative/omitted-adapter-operation-contract`                                                                                                                                                                                                                                                                                                                                                                        |
| specialization and diamonds | `IFC-KEY-003/boundary/diamond-distinct-requirement-keys`, `IFC-KEY-004/permutation/shared-evidence`                                                                                                                                                                                                                                                                                                                                                                             |
| conformance graph           | `IFC-CON-001/negative/identity-is-not-proof`, `IFC-CON-002/serialization/forward-scc-refs`, `IFC-CON-006/negative/raw-id-is-not-evidence`, `IFC-CON-007/serialization/revision-not-type-identity`, `IFC-CON-008/negative/pending-map-publication`, `IFC-CON-009/positive/provisional-projection-rewrite`, `IFC-CON-009/negative/incoherent-projection-paths`                                                                                                                    |
| discovery/coherence         | `IFC-FIND-003/mock/extension-environment`, `IFC-FIND-004/permutation/import-order`, `IFC-FIND-004/negative/duplicate-endpoint-providers`, `IFC-FIND-006/positive/strict-applicability-subset`, `IFC-FIND-006/negative/incomparable-extension-providers`, `IFC-FIND-007/mock/wait-for-definition`                                                                                                                                                                                |
| matching                    | `IFC-MAT-002/negative/receiver-mode-adapter`, `IFC-MAT-003/permutation/candidate-order`, `IFC-MAT-006/mock/local-capability-fixpoint`, `IFC-MAT-007/mock/local-effect-fixpoint`, `IFC-MAT-008/serialization/candidate-identity`                                                                                                                                                                                                                                                 |
| absence/recovery            | `WIT-ABS-001/positive/optional-none`, `WIT-ABS-002/recovery/missing-is-not-absent`, `WIT-ABS-003/negative/unguarded-optional-use`                                                                                                                                                                                                                                                                                                                                               |
| associated types            | `WIT-PROJ-001/positive/instantiated-projection`, `WIT-PROJ-003/negative/projection-cycle`, `WIT-PROJ-003/negative/mismatched-evidence-identity`, `WIT-PROJ-003/serialization/evidence-revision-key`, `WIT-PROJ-007/positive/value-associated-type`, `WIT-PROJ-008/negative/value-dependent-parameter-type`                                                                                                                                                                      |
| map algebra                 | `WIT-ALG-001/permutation/merge-laws`, `WIT-ALG-004/boundary/diamond-base-projections`, `WIT-ALG-005/boundary/complement-partition`                                                                                                                                                                                                                                                                                                                                              |
| defaults                    | `IFC-DEF-003/negative/inherited-default-conflict`, `IFC-DEF-005/serialization/keyed-evidence`, `IFC-DEF-006/negative/entry-point-source-confusion`, `IFC-DEF-007/serialization/construction-to-published`                                                                                                                                                                                                                                                                       |
| synthesis                   | `SYN-GRP-001/recovery/atomic-failure`, `SYN-GRP-002/negative/provisional-ref-escape`, `SYN-GRP-003/permutation/parallel-idempotence`                                                                                                                                                                                                                                                                                                                                            |
| lambdas/wrappers            | `IFC-LAM-002/boundary/never-and-fallthrough`, `SYN-WRP-002/serialization/whole-group`, `SYN-WRP-003/negative/storage-endpoint-mismatch`, `SYN-WRP-004/negative/borrowed-wrapper-escape`, `SYN-WRP-005/serialization/all-kind-plan-map`                                                                                                                                                                                                                                          |
| runtime witness entries     | `WIT-USE-001/positive/property-get-set-distinct`, `WIT-USE-003/serialization/key-to-slot-map`, `WIT-USE-004/negative/operational-ref-in-published-ir`                                                                                                                                                                                                                                                                                                                           |
| all-kind witness entries    | `WIT-ENT-001/serialization/associated-type-entry`, `WIT-ENT-002/negative/associated-value-is-not-callable`, `WIT-ENT-003/serialization/metadata-and-runtime-projection`                                                                                                                                                                                                                                                                                                         |
| scheduler cycles            | `IFC-CYCLE-001/negative/self-proof`, `IFC-CYCLE-004/boundary/acyclic-key-growth`                                                                                                                                                                                                                                                                                                                                                                                                |
| diagnostics                 | `IFC-DIAG-002/permutation/worker-count`, `IFC-DIAG-004/recovery/no-export`                                                                                                                                                                                                                                                                                                                                                                                                      |

Pure matcher tests provide mock requirement slots, signatures, lookup results, conformance providers,
and synthesis planners; they do not parse a module or construct a compiler session. Property tests
cover substitution composition, requirement-key transport, compatible map-merge laws, evidence
reuse acyclicity, and serialization round trips. Integration tests then verify that parsing and IR
preserve the same keys and evidence identities end to end.
