# Elaboration, synthesis, and frontend IR

Elaboration turns a typed program into an explicit program. Core lowering then maps that explicit
program to frontend IR without name lookup, overload resolution, generic inference, implicit
conversion search, or ad hoc declaration synthesis.

The current compiler performs much of this work while mutating the checked AST. For example,
`SemanticsExprVisitor::visitLambdaExpr` in `source/slang/slang-check-expr.cpp` creates a mutable
`LambdaDecl`, rewrites captures, inserts it into a container, checks it through `ensureDecl`, and
returns a constructor invocation; `visitLambdaExpr` in `source/slang/slang-lower-to-ir.cpp` then
asserts that no lambda remains. The replacement preserves that semantic result but expresses it as
a named, independently testable transformation.

## Elaboration contract

```text
TypedNode     = AstNode<Typed>
ElaboratedNode = AstNode<Elaborated>
CoreNode      = AstNode<Core>

ElaborateNode : TypedNode -> CheckResult<ElaboratedNode>
LowerToCore   : ElaboratedNode -> CheckResult<CoreNode>
LowerToIR     : CoreDecl -> CheckResult<FrontendIRFragment>
```

These aliases range over the complete registered node set at exactly one representation stage.
They are not a common mutable base class and do not erase stage from `NodeId<S>`. Expression,
statement, and declaration aliases below further restrict the registered kind through the schema's
`baseKind` chain. Consequently, only the named transformations above can change a node's stage;
chapter 3's generic immutable rewrite API remains stage-preserving.

`ELB-001`: Every implicit runtime operation in a typed node becomes an explicit elaborated node.

`ELB-002`: Elaboration is deterministic and idempotent by semantic identity. Re-requesting the same
synthesis key returns the same synthesized declaration ID.

`ELB-003`: Elaboration never edits the declaration container that caused it. Generated declarations
and all semantic facts they make visible are returned in one `SynthesisGroup` and merged into the
next immutable module snapshot atomically.

Chapter 8 is the sole schema authority for `SynthesisKey`, output identities,
`SemanticDependency`, `SynthesisGroupDraft`, and `SynthesisGroup`. All declarations, conformance
identities, finalized requirement maps, and rewritten uses in a group
validate together. Publication either installs the whole group or installs none of it. Builder-only
definition drafts and operational conformance references may be used inside the pure construction
query, but atomic freeze validates and rewrites them; neither is a second authority in the published
group.

Names assigned for debugging are derived from the synthesis key and are not identity. Insertion or
parallel task order therefore cannot change mangling or capture layout.

## Explicit call form

A checked call lowers to one form:

```text
CallableValue<S: WitnessUseStage> = {
    dispatch: CallableDispatch<S>,
    contract: CallableContractStateAt<S>
}

CallableDispatch<S: WitnessUseStage> =
    Direct(ResolvedDeclRefAt<S>)
  | WitnessMethod(witness: WitnessCallRef<S>, entry: WitnessRuntimeEntryKey)
  | DynamicSlot(owner: TypeId, slot: DynamicDispatchKey)
  | ClosureInvoke(ResolvedDeclRefAt<S>)
  | Builtin(rule: RuleId,
            operands: CanonicalArguments,
            witnessResolutions: WitnessResolutionSetAt<S>)

CallableContractStateAt<Construction> =
    Selection(contract: PreInferenceCallableContract)
  | ResidualContract(effects: EffectRequirement,
                     capabilities: CapabilityRequirement)
  | Effective(contract: EffectiveCallableContract)
  | SelectedVariant(set: CallableVariantSetId,
                    proof: CapabilityVariantSelectionProof,
                    contract: EffectiveCallableContract)

CallableContractStateAt<Published> =
    ResidualContract(effects: EffectRequirement,
                     capabilities: CapabilityRequirement)
  | Effective(contract: EffectiveCallableContract)
  | SelectedVariant(set: CallableVariantSetId,
                    proof: CapabilityVariantSelectionProof,
                    contract: EffectiveCallableContract)

CallableContractState = CallableContractStateAt<Published>

CallableContractSubject =
    DirectContractSubject(CanonicalDeclRef)
  | WitnessContractSubject(witness: InterfaceSubtypeWitnessId,
                           entry: WitnessRuntimeEntryKey)
  | DynamicContractSubject(owner: TypeId, slot: DynamicDispatchKey)
  | ClosureContractSubject(CanonicalDeclRef)
  | BuiltinContractSubject(rule: RuleId, operands: CanonicalArguments)

CallableContractCompletion =
    CompletedEffective(EffectiveCallableContract)
  | CompletedSelectedVariant(set: CallableVariantSetId,
                             proof: CapabilityVariantSelectionProof,
                             contract: EffectiveCallableContract)

CallableContractCompletionKey = {
    subject: CallableContractSubject,
    context: ContractSelectionContext
}

ContractCompletionMap =
    CanonicallyOrderedMap<CallableContractCompletionKey, CallableContractCompletion>

TypedCallReferenceResultAuthorityAt<S: WitnessUseStage> =
    FixedReferenceHandleCallResult(
        authority: FixedReferenceHandleResultContractId)
  | AccessorReferenceHandleCallResult(
        certificate: AccessorReferenceResultCertificate)
  | RegisteredReferenceHandleCallResult(
        registration: ReferenceOperationRegistration,
        staticInputs: CanonicalArguments,
        environment: StandardEnvironmentId)

TypedCallReferenceHandleResultAt<S: WitnessUseStage> = {
    result: ReferenceHandleValueShape,
    authority: TypedCallReferenceResultAuthorityAt<S>
}

TypedCallResultProvenanceAt<S: WitnessUseStage> =
    OrdinaryCallResult
  | ReferenceHandleCallResult(TypedCallReferenceHandleResultAt<S>)

TypedCallAt<S: WitnessUseStage> = {
    id: NodeId<Typed>,
    dispatch: CallableDispatch<S>,
    signature: CallableSignature,
    resultAuthority: CallableResultAuthorityId,
    selectionContract: PreInferenceCallableContract,
    contractContext: ContractSelectionContext,
    accessEnvironment: AccessEnvironmentId,
    resultProvenance: TypedCallResultProvenanceAt<S>,
    argumentMap: ArgumentMap,
    callSlots: NodeMap<BoundCallSlot, ApplicableCallSlotPlan<S>>,
    aliasCompatibility: CompatibleCallAliasClaims,
    directEffectUse: EffectUse<S>,
    capabilitySelection: CapabilitySelectionAt<S>,
    resultType: TypeId,
    origin: Origin
}

TypedCall = TypedCallAt<Published>

CallableResultAuthorityResolutionFailure =
    CallableResultAuthorityUnavailable(subject: CallableContractSubject,
                                       signature: CallableSignatureId)
  | CallableResultAuthorityAnchorMismatch(
        authority: CallableResultAuthorityId,
        subject: CallableContractSubject,
        signature: CallableSignatureId)
  | CallableResultAuthorityKindMismatch(
        authority: CallableResultAuthorityId,
        requested: OrdinaryCallableResult |
                   FixedReferenceHandleCallableResult |
                   AccessorReferenceHandleCallableResult |
                   RegisteredReferenceHandleCallableResult)

ResolveCallableResultAuthorityAt<S>(dispatch: CallableDispatch<S>,
                                    signature: CallableSignatureId)
    -> Result<CallableResultAuthorityId,
              CallableResultAuthorityResolutionFailure>

BuildTypedCall(id, Selected(winner, comparisons, considered), contractContext)
    -> CheckResult<TypedCall>

AccessorReferenceResultInstantiationInputAt<S: WitnessUseStage> = {
    contract: AccessorReferenceResultContractId,
    invocationIdentity: AccessorInvocationIdentity,
    invocationSite: SemanticOperationSiteAssignment,
    call: NodeId<Typed>,
    subject: CallableContractSubject,
    signature: CallableSignatureId,
    sources: CapturedStorageSources,
    provenanceSources: AccessorProvenanceSourceMapId,
    expectedReferent: TypeId,
    context: ExpressionCheckContextId
}

InstantiateAccessorReferenceResultAt<S>(
    input: AccessorReferenceResultInstantiationInputAt<S>)
    -> Result<AccessorReferenceResultCertificate,
              AccessorReferenceResultContractFailure>

SelectedSurfaceCallResultInputAt<S: WitnessUseStage> =
    OrdinarySurfaceCallResult
  | FixedReferenceHandleSurfaceCallResult(
        result: ReferenceHandleValueShape)
  | AccessorReferenceHandleSurfaceCallResult(
        invocationIdentity: AccessorInvocationIdentity,
        invocationSite: SemanticOperationSiteAssignment,
        sources: CapturedStorageSources,
        provenanceSources: AccessorProvenanceSourceMapId,
        expectedReferent: TypeId,
        context: ExpressionCheckContextId,
        result: ReferenceHandleValueShape)
  | RegisteredReferenceHandleSurfaceCallResult(
        result: ReferenceHandleValueShape)

SelectedSurfaceCallInputAt<S: WitnessUseStage> = {
    dispatch: CallableDispatch<S>,
    signature: CallableSignature,
    selectionContract: PreInferenceCallableContract,
    accessEnvironment: AccessEnvironmentId,
    resultInput: SelectedSurfaceCallResultInputAt<S>,
    argumentMap: ArgumentMap,
    callSlots: NodeMap<BoundCallSlot, ApplicableCallSlotPlan<S>>,
    aliasCompatibility: CompatibleCallAliasClaims,
    directEffectUse: EffectUse<S>,
    capabilitySelection: CapabilitySelectionAt<S>,
    resultType: TypeId,
    origin: Origin
}

ConstructionCallInput = SelectedSurfaceCallInputAt<Construction>

BuildSelectedSurfaceTypedCallAt<S>(
    id: NodeId<Typed>,
    input: SelectedSurfaceCallInputAt<S>,
    contractContext: ContractSelectionContext)
    -> CheckResult<TypedCallAt<S>>

BuildConstructionTypedCall(id, ConstructionCallInput, contractContext)
    -> CheckResult<TypedCallAt<Construction>>

ElaborateTypedCallAt<S>(
    call: TypedCallAt<S>,
    sourceEnvironment: ElaboratedCallSourceEnvironmentAt<S>,
    bindings: NodeMap<BoundCallSlot, BoundAccessPlan<S>>,
    completions: ContractCompletionMap)
    -> CheckResult<ElaboratedCallAt<S>>

ElaboratedReceiverAt<S: WitnessUseStage> = {
    sourceType: TypeId,
    access: BoundAccessPlan<S>,
    origin: Origin
}

ElaboratedCallAt<S: WitnessUseStage> = {
    callee: CallableValue<S>,
    signature: CallableSignature,
    resultAuthority: CallableResultAuthorityId,
    contractContext: ContractSelectionContext,
    accessEnvironment: AccessEnvironmentId,
    resultProvenance: TypedCallResultProvenanceAt<S>,
    capabilitySelection: CapabilitySelectionAt<S>,
    aliasCompatibility: CompatibleCallAliasClaims,
    sourceEnvironment: ElaboratedCallSourceEnvironmentAt<S>,
    receiver: Option<ElaboratedReceiverAt<S>>,
    arguments: NodeList<ElaboratedArgumentAt<S>>,
    resultType: TypeId,
    origin: Origin
}

typedCallInvocationLifetime(call) =
    resolve(call.accessEnvironment).invocationLifetime

elaboratedCallInvocationLifetime(call) =
    resolve(call.accessEnvironment).invocationLifetime

ElaboratedArgumentAt<S: WitnessUseStage> = {
    parameter: ParameterKey,
    access: BoundAccessPlan<S>
}

ElaboratedBuiltinPhysicalProjectionOperandAt<S: WitnessUseStage> = {
    source: ElaboratedExprAt<S>,
    endpointType: TypeId,
    endpointCategory: ValueCategory
}

ElaboratedBuiltinPhysicalProjectionAt<S: WitnessUseStage> = {
    identity: BuiltinPhysicalProjectionIdentity,
    site: PhysicalProjectionSiteAssignment,
    operation: BuiltinPhysicalProjectionOperation,
    runtimeOperands:
        CanonicallyOrderedMap<BuiltinPhysicalProjectionOperandRole,
                              ElaboratedBuiltinPhysicalProjectionOperandAt<S>>,
    evaluationOrder: NodeList<BuiltinPhysicalProjectionOperandRole>,
    output: BuiltinPhysicalProjectionResultProof,
    control: BuiltinPhysicalProjectionControlProof
}

ElaborateBuiltinPhysicalProjectionAt<S>(
    application: BuiltinPhysicalProjectionApplicationAt<S>)
    -> CheckResult<ElaboratedBuiltinPhysicalProjectionAt<S>>

ElaboratedRegisteredPhysicalProjectionOperandAt<S: WitnessUseStage> = {
    source: ElaboratedExprAt<S>,
    access: BoundAccessPlan<S>,
    endpointType: TypeId,
    endpointCategory: ValueCategory
}

ElaboratedRegisteredPhysicalProjectionAt<S: WitnessUseStage> = {
    identity: RegisteredPhysicalProjectionIdentity,
    site: PhysicalProjectionSiteAssignment,
    registration: RegisteredDataOperationRegistration,
    runtimeOperands:
        CanonicallyOrderedMap<RegisteredPhysicalProjectionOperandRole,
                              ElaboratedRegisteredPhysicalProjectionOperandAt<S>>,
    evaluationOrder: NodeList<RegisteredPhysicalProjectionOperandRole>,
    output: RegisteredPhysicalProjectionResultProof,
    control: RegisteredPhysicalProjectionControlProof
}

ElaborateRegisteredPhysicalProjectionAt<S>(
    application: RegisteredPhysicalProjectionApplicationAt<S>,
    bindings:
        NodeMap<RegisteredPhysicalProjectionOperandRole, BoundAccessPlan<S>>)
    -> CheckResult<ElaboratedRegisteredPhysicalProjectionAt<S>>

AccessOperandId = { ordinal: UInt32 }
AccessStepId = { ordinal: UInt32 }
AccessCompletionStepId = { ordinal: UInt32 }
PhysicalStorageObligationId = { ordinal: UInt32 }
PlanValueId = { ordinal: UInt32 }
PlanPhysicalPlaceId = { ordinal: UInt32 }
PlanAbstractPlaceId = { ordinal: UInt32 }
TemporaryId = { ordinal: UInt32 }
ReferenceCaptureResultId = { ordinal: UInt32 }
CapturedStorageSourcesId = ContentId<CapturedStorageSources>

capturedSourceRole(CapturedStorageReceiver(_)) = StorageReceiverSource
capturedSourceRole(CapturedStorageArgument(a)) = StorageArgumentSource(a.id)

capturedSourceExpr(CapturedStorageReceiver(value)) = value
capturedSourceExpr(CapturedStorageArgument(argument)) = argument.value

ReferenceCaptureResultAt<S: WitnessUseStage> = {
    id: ReferenceCaptureResultId,
    source: CapturedStorageSource,
    evaluation: ElaboratedExprAt<S>
}

ReferenceCaptureEnvironmentAt<S: WitnessUseStage> = {
    sourceSet: CapturedStorageSourcesId,
    results: NodeMap<ReferenceCaptureResultId, ReferenceCaptureResultAt<S>>,
    evaluationOrder: NodeList<ReferenceCaptureResultId>
}

ElaboratedCallSourceEnvironmentAt<S: WitnessUseStage> =
    IndependentCallSources
  | CapturedReferenceSources(ReferenceCaptureEnvironmentAt<S>)

AccessPlan<S: WitnessUseStage> = {
    operands: NodeMap<AccessOperandId, AccessOperand>,
    physicalStorageObligations:
        NodeMap<PhysicalStorageObligationId, PhysicalStorageObligation>,
    preparation: NodeList<AccessStepRecord<S>>,
    terminal: AccessPlanTerminal<S>,
    completion: NodeList<AccessCompletionStepRecord<S>>,
    rankingConversion: Option<RankedAccessConversion>,
    lifetime: AccessLifetime,
    aliasClass: AliasClass,
    semanticUses: PlanSemanticUses<S>
}

AccessLifetime = {
    temporary: Option<TemporaryAccessExtent>
}

TemporaryAccessExtent = {
    temporary: TemporaryId,
    cleanup: CompletionCondition
}

ImmediateAccessLifetime = AccessLifetime(None)

UniqueAliasProof =
    FreshTemporaryAlias(temporary: TemporaryId, identity: TemporaryStorageIdentity)
  | RegisteredUniqueAlias(rule: StandardEnvironmentRuleId,
                          inputs: CanonicalArguments,
                          identity: StableSemanticId)

uniqueAliasProvenance(FreshTemporaryAlias(_, i)) =
    ExactAliasRoot(temporaryStorageAliasRoot(i))
uniqueAliasProvenance(RegisteredUniqueAlias(_, _, i)) =
    ExactAliasRoot(StableAliasRegionIdentity(i))

AliasClass = UniqueAlias(proof: UniqueAliasProof)
           | SharedAlias(provenance: AliasProvenance)
           | UnknownAlias

aliasClassProvenance(UniqueAlias(p)) = uniqueAliasProvenance(p)
aliasClassProvenance(SharedAlias(p)) = p
aliasClassProvenance(UnknownAlias) = UnknownAliasRoot

AccessOperand =
    TypedInput(node: NodeId<Typed>, type: TypeId, category: ValueCategory)
  | AdapterInput(role: AdapterSourceRole,
                 type: TypeId,
                 category: AdapterInputCategory)

BoundAccessPlan<S: WitnessUseStage> = {
    recipe: AccessPlan<S>,
    bindings: NodeMap<AccessOperandId, ElaboratedAccessOperandAt<S>>,
    physicalStorageProofs:
        NodeMap<PhysicalStorageObligationId, PhysicalStorageProof>
}

PhysicalStorageObligation =
    ConcreteStorageObligation(input: AccessOperandId,
                              requirement: PhysicalStorageRequirement,
                              proof: PhysicalStorageProof)
  | AdapterStorageObligation(input: AccessOperandId,
                             requirement: PhysicalStorageRequirement)

PhysicalPlaceProjectionAuthority =
    RequiredPhysicalStorage(obligation: PhysicalStorageObligationId)

MaterializedTemporaryStorageAt<S: WitnessUseStage> = {
    id: TemporaryId,
    site: SemanticOperationSiteAssignment,
    identity: TemporaryStorageIdentity,
    valueType: TypeId,
    lifetime: LifetimeId,
    alias: AliasProvenance,
    initialization: TemporaryInitializationPlanApplicationAt<S>,
    destruction: DestructionExecutionAt<S>
}

MaterializedTemporaryStorage = MaterializedTemporaryStorageAt<Published>

TemporaryInitializationSource =
    PreparedInitializationValue(value: PlanValueId)
  | PhysicalInitializationPlace(place: PlanPhysicalPlaceId)
  | AbstractInitializationPlace(place: PlanAbstractPlaceId)

ElaboratedExprAt<S: WitnessUseStage> =
    an Elaborated-stage expression whose witness-bearing descendants all have stage S

ElaboratedDeclAt<S: WitnessUseStage> =
    an Elaborated-stage declaration whose bodies contain only ElaboratedExprAt<S>

ElaboratedFunctionBodyAt<S: WitnessUseStage> =
    an Elaborated-stage function body whose witness-bearing descendants all have stage S

ElaboratedAccessOperandAt<S: WitnessUseStage> =
    ValueSource(ElaboratedExprAt<S>)
  | PlaceSource(PlaceRef)
  | CapturedSourceProjection(result: ReferenceCaptureResultId,
                             projection: CapturedStorageProjection)

AbstractAccessorRole = Get | Set(valueParameter: ParameterKey)

AbstractAccessorInvocationAt<S: WitnessUseStage> = {
    storage: AbstractStorageRef,
    role: AbstractAccessorRole,
    callable: CallableValue<S>,
    signature: CallableSignature,
    receiver: Option<PlanValueId>,
    indices: NodeMap<ParameterKey, PlanValueId>
}

Explicit reference formation does not inhabit `AbstractAccessorRole`. It owns the separate
`ReferenceAccessorPlanAt<S>` from chapter 6, so no ordinary getter/setter access recipe can be
retagged as a ref accessor.

AccessStepRecord<S: WitnessUseStage> = {
    id: AccessStepId,
    operation: AccessStepOperation<S>
}

AccessStepOperation<S: WitnessUseStage> =
    EvaluateOnce(input: AccessOperandId, result: PlanValueId)
  | ProjectPhysicalPlace(input: AccessOperandId,
                         result: PlanPhysicalPlaceId,
                         authority: PhysicalPlaceProjectionAuthority)
  | ProjectAbstractPlace(input: AccessOperandId,
                         result: PlanAbstractPlaceId)
  | ReadAbstractPlace(input: PlanAbstractPlaceId,
                      invocation: AbstractAccessorInvocationAt<S>,
                      result: PlanValueId)
  | ResolveAbstractPlaceThroughReference(
        input: PlanAbstractPlaceId,
        plan: InternalRefStoragePlanAt<S>,
        handle: PlanValueId,
        result: PlanPhysicalPlaceId)
  | ProjectPhysicalPlaceThroughParameterAccessor(
        input: PlanAbstractPlaceId,
        plan: ParameterReferenceAccessorPlanAt<S>,
        handle: PlanValueId,
        result: PlanPhysicalPlaceId)
  | ReadPhysicalPlace(input: PlanPhysicalPlaceId,
                      result: PlanValueId)
  | ConvertValue(input: PlanValueId, plan: ConversionPlan<S>, result: PlanValueId)
  | InitializeTemporary(storage: MaterializedTemporaryStorageAt<S>,
                        source: TemporaryInitializationSource)

RuntimeArgumentAt<S: WitnessUseStage> =
    ImmediateValue(PlanValueId)
  | OutDestination(PlanPhysicalPlaceId)
  | TemporaryAddress(TemporaryId)
  | PhysicalPlaceArgument(
        place: PlanPhysicalPlaceId,
        binding: PhysicalParameterBindingProofAt<S>)

StorageWriteSource = ComputedValue(PlanValueId)

StorageWriteOperationAt<S: WitnessUseStage> =
    WritePhysicalStorage(destination: PlanPhysicalPlaceId,
                         source: StorageWriteSource,
                         conversion: ConversionPlan<S>,
                         when: CompletionCondition)
  | WriteAbstractStorage(destination: PlanAbstractPlaceId,
                         invocation: AbstractAccessorInvocationAt<S>,
                         source: StorageWriteSource,
                         conversion: ConversionPlan<S>,
                         when: CompletionCondition)

AccessPlanTerminal<S: WitnessUseStage> =
    PassArgument(argument: RuntimeArgumentAt<S>)
  | YieldStorageRead(result: PlanValueId)
  | CompleteStorageWrite(operation: StorageWriteOperationAt<S>,
                         result: PlanValueId)

AccessCompletionStepRecord<S: WitnessUseStage> = {
    id: AccessCompletionStepId,
    operation: AccessCompletionStepOperation<S>
}

AccessCompletionStepOperation<S: WitnessUseStage> =
    WritePhysicalBack(destination: PlanPhysicalPlaceId,
                      source: TemporaryValue(TemporaryId) | ComputedValue(PlanValueId),
                      conversion: ConversionPlan<S>,
                      when: CompletionCondition)
  | WriteAbstractBack(destination: PlanAbstractPlaceId,
                      invocation: AbstractAccessorInvocationAt<S>,
                      source: TemporaryValue(TemporaryId) | ComputedValue(PlanValueId),
                      conversion: ConversionPlan<S>,
                      when: CompletionCondition)
  | DestroyTemporary(temporary: TemporaryId,
                     destruction: DestructionExecutionAt<S>,
                     when: CompletionCondition)

CompletionCondition = OnNormalCompletion | OnExceptionalCompletion | Always

AccessConversionSite = PreparationConversion(AccessStepId)
                     | TemporaryInitialization(step: AccessStepId,
                                               conversion: InitializationPath)
                     | TerminalStorageWriteConversion

RankedAccessConversion =
    ConvertedAccess(site: AccessConversionSite, rank: ConversionRank,
                    environment: ConversionEnvironmentId)
  | ConsumedWithoutAccessConversion(rule: RuleId)
```

Plan- and call-local IDs are typed ordinals, not process addresses or global semantic identities.
Operand ordinals are dense in canonical operand-role order; preparation and completion step
ordinals are dense in serialized execution order; value, physical-place, abstract-place, and
temporary ordinals are dense in first-definition order within their separate domains.
Reference-capture-result ordinals are dense in the capture environment's evaluation order.
Renumbering a valid plan or environment by these rules is part of canonicalization, so
alpha-equivalent local numbering cannot create a second encoding.

`ELB-PLC-001`: `ElaborateRegisteredPhysicalProjectionAt<S>` preserves the application's identity,
authenticated site assignment,
registration (including environment and static inputs), operand-role domain, evaluation order,
intrinsic output proof, and control proof byte-for-byte. In that exact order it elaborates each
stored `runtimeOperands[role].source` once and binds the unchanged access recipe to that elaborated
source, producing the corresponding `BoundAccessPlan<S>`. The supplied binding map has exactly the
operand domain and each recipe equals the source application's recipe; it may discharge operands
and physical-storage obligations but cannot replace endpoint type/category or select another
conversion. Every operand recipe has a `PassArgument` terminal matching its registered runtime
endpoint; a storage read/write terminal is invalid. Selection effects/capabilities and operand-plan
semantic uses have already been contributed once during checking and are not rediscovered during
elaboration.

`ELB-PLC-002`: Lowering the elaborated application executes those bound plans in
`evaluationOrder` and records the resulting `CoreValueId` under the same role in one
`CoreRegisteredPhysicalProjection`. The Core output is exactly
`PhysicalPlace(application.output.storage)`. No base/index is recovered from the output place path,
and no generic Core primitive may manufacture that place. Reordering operands, dropping an index,
or replacing one with an equal-typed value invalidates the application rather than changing only
presentation order. The authenticated site has already fixed and validated the nominal identity;
Core retains that identity but removes the site assignment and its `Origin`.

`ELB-PLC-003`: `ElaborateBuiltinPhysicalProjectionAt<S>` preserves the application's identity,
authenticated site assignment, operation, operand-role domain, evaluation order, result proof, and
control proof byte-for-byte. It
elaborates the exact stored base and converted index once in that order. The base remains a
`PhysicalPlace` for `output.inputStorage`; the index remains the checked `RValue` at its endpoint
type. Semantic uses were contributed during checking and are not rediscovered. Elaboration cannot
recover either operand from `BuiltinElement`, the originating typed node, or the input storage's
type.

`ELB-PLC-004`: Lowering the elaborated builtin application records both resulting `CoreValueId`
operands under their unchanged roles and constructs exactly one
`CoreBuiltinPhysicalProjection`. Its result is `PhysicalPlace(application.output.storage)`, and the
Core node retains the identity, operation, input shapes, result proof, and control proof needed to
replay that projection. Missing, duplicated, reordered, or equal-typed replacement operands make
lowering invalid. A builtin application cannot lower as a
`CoreRegisteredPhysicalProjection`, even when a target happens to use the same eventual opcode.
The Core boundary removes the validated site assignment and its `Origin` while retaining its
nominal identity.

`ELB-ACC-010`: `AccessPlan.terminal` is the closed purpose of the recipe. A plan produced by
`PlanArgumentAccess` has exactly `PassArgument`; a plan produced by `PlanStorageAccessAt<S>` for a
request whose intent is `ReadValueAccess` has exactly `YieldStorageRead`; and a plan produced for
`WriteValueAccess(w)` has exactly `CompleteStorageWrite`. A registered physical-
projection operand also uses `PassArgument`, because it supplies one runtime operand to the
registered operation rather than performing a standalone storage access. Validators reject every
cross-purpose terminal, including a storage read represented by an `ImmediateValue` argument and a
standalone write with a dummy runtime argument.

`PassArgument` transfers its prepared argument to the enclosing call or registered operation; its
completion conditions are interpreted on that operation's normal and exceptional return edges.
`YieldStorageRead` names the result of the selected `ReadPhysicalPlace` or `ReadAbstractPlace` and
returns that prepared value from the storage-access expression; a fallback names the physical read
after its single `ResolveAbstractPlaceThroughReference`.
`CompleteStorageWrite` executes its stored physical store or abstract setter and returns the named
already-evaluated source value only after that operation completes normally. Its operation's `when`
condition is interpreted against completion of the preparation phase; completion-list conditions
are interpreted against the selected terminal's outcome. Thus `OnNormalCompletion` and
`OnExceptionalCompletion` always name the immediately preceding explicit phase boundary and do not
imply that every access plan contains a call.

`ELB-ACC-011`: A physical-domain call slot has exactly one
`PassArgument(PhysicalPlaceArgument(p, binding))` terminal. `binding.mode` is the slot's complete
substituted `PassingMode`, whose domain is `PhysicalOperand(_)`; its access is `ReadAccess` for
`ConstRefMode` and `ReadWriteAccess` for `RefMode`. The plan has no temporary extent, conversion,
write-back, borrow step, or cleanup step. The physical place `p` is produced in exactly one of two
ways. For `DirectPhysicalParameterSource`, `ProjectPhysicalPlace` discharges the stored physical
obligation for the source's existing `PhysicalPlace`. For
`AccessorProducedPhysicalParameterSource`, `ProjectAbstractPlace` is followed by exactly one
`ProjectPhysicalPlaceThroughParameterAccessor` carrying the byte-identical
`ParameterReferenceAccessorPlanAt<S>` from `binding.source`; that operation evaluates the captured
receiver and indices once, invokes the accessor whose key is exactly `binding.mode.access`, retains
its handle result and admission proof, and executes its stored dereference to produce `p`.
`plan.mode = binding.mode`, `plan.accessEnvironment = binding.accessEnvironment`, and
`plan.instantiatedRequirement = binding.instantiatedRequirement`; no caller-supplied weaker
requirement is accepted.

In both forms `physicalParameterStorage(binding)` equals the storage of `p`,
`binding.physicalStorage` proves the complete instantiated requirement for that endpoint, and
`binding.identity` proves that neither value type nor storage identity changed. A
`ReadWriteAccess` accessor cannot stand in for a `ReadAccess` accessor or conversely. A getter,
setter, getter-plus-setter pair, materialized value, temporary, ordinary conversion, or
read/write-back fallback cannot occur in this plan. The intermediate reference handle of the
accessor-produced form is consumed only by its stored dereference and cannot become the call
argument or escape the plan.

`ELB-ACC-012`: `aliasClass` is derived from the executable endpoint. A physical-domain plan stores
`SharedAlias(physicalParameterStorage(binding).alias)` for both access modes; the orthogonal
call-alias claim records `SharedPhysicalRead(ReadAccess)` for `ConstRefMode` and
`AliasablePhysicalAccess(ReadWriteAccess, rule)` for `RefMode`. `UniqueAlias(FreshTemporaryAlias(t,
i))` is valid only when the same abstract-domain plan
defines temporary `t` with identity `i`, its descriptor has
`alias = ExactAliasRoot(temporaryStorageAliasRoot(i))`, and no operation publishes an alias to it.
`RegisteredUniqueAlias` replays its named standard-environment rule and exact static inputs. Every
other plan preserves selected source provenance or uses `UnknownAlias`; it cannot mint uniqueness
from access mode, result type, node identity, or container position. `aliasClassProvenance` is the
sole alias-provenance input from an access plan to `CheckCallAliasClaims`.

`ELB-ACC-001`: Every `AccessOperandId` used by a preparation step or physical-storage obligation
exists in `operands`, and obligation ordinals are dense.
`ProjectPhysicalPlace(..., RequiredPhysicalStorage(o))` names one existing obligation whose input
equals the step input. A `ConcreteStorageObligation` is permitted only for a `TypedInput` already
classified as its proof's exact `PhysicalPlace`; an `AdapterStorageObligation` only for
`AdapterPhysicalPlace`. `ProjectPhysicalPlaceThroughParameterAccessor` is permitted only when the
terminal binding's source is `AccessorProducedPhysicalParameterSource(source, plan)`, the preceding
`ProjectAbstractPlace` projects that exact typed `source`, and its result storage is exactly
`plan.endpoint.output.storage`. The plan's mode, access environment, and derived requirement equal
the terminal binding's corresponding fields. Each
`PlanValueId`, `PlanPhysicalPlaceId`, `PlanAbstractPlaceId`, and `TemporaryId` has exactly one
definition. Preparation is SSA-ordered: every value/place use refers to an earlier definition, and
`InitializeTemporary(d, source)` defines `d.id` only at its stored initialization application's
normal checkpoint. Every terminal ID refers to a prepared value, physical place, or initialized
temporary of the exact required alternative. A validator derives the complete def-use map; no
parallel table is serialized.

`ELB-ACC-002`: Every successfully initialized materialized temporary has exactly one
`DestroyTemporary` carrying its descriptor's byte-identical `DestructionExecutionAt<S>` on every
exit selected by its `CompletionCondition`. A failed `InitializeTemporary` executes only the
chapter 15 exceptional cleanup and never activates the outer destruction obligation.
For every descriptor `d`, `d.site = d.initialization.site`,
`d.identity = d.initialization.identity = temporaryStorageIdentity(d.site.site)`, and
`d.alias = ExactAliasRoot(temporaryStorageAliasRoot(d.identity))`. Thus neither plan ordinals nor
initialization-storage content IDs become ownership/alias identities.
`AccessLifetime.temporary` has exactly the domain of the plan's initialized temporary; an immediate
or physical-domain plan has none. Abstract `OutMode`/`InOutMode` write-back reads an initialized
temporary/value, targets a defined physical or abstract place, and precedes destruction of its
source. Completion order cannot use a destroyed temporary or a value/place outside its declared
access lifetime. The validator symbolically checks the terminal-relative normal and exceptional
paths from `ELB-ACC-010`.

`ELB-ACC-003`: `Some(ConvertedAccess(...))` selects one existing `ConvertValue`, a conversion at the
`InitializationPath` stored by an `InitializeTemporary` application, or a terminal
`StorageWriteOperationAt<S>` conversion, and its stored rank must equal
`rankConversion(selectedConversion, environment)`. The environment is serialized and
must equal the candidate's registered conversion environment, so deserialization can replay the
rank without ambient target or language settings.
`Some(ConsumedWithoutAccessConversion(...))` is permitted only for a candidate-passing rule that
consumes no converted input. Every access plan installed in an overload candidate or call slot has
`Some`; `None` is permitted only when the plan is not a candidate-comparison input, including a
standalone storage read/write. Thus ranking and elaboration inspect the same conversion operation
rather than parallel plans, while a non-candidate plan carries no fabricated rank.

`ELB-ACC-004`: `BoundAccessPlan.bindings` has exactly the domain of `recipe.operands`; each bound
value/place or capture projection matches the operand's stated type and category, and an
`AdapterInput` may bind only the declared adapter role. A capture projection is checked in the
enclosing call's source environment under `ELB-ACC-007`; it is not permission to resolve the
original typed expression again. `physicalStorageProofs` has exactly the domain of
`recipe.physicalStorageObligations`. Each proof's storage is the `PhysicalPlace` bound to that
obligation's input and satisfies its requirement. For a concrete obligation it equals the proof
already selected during applicability; for an adapter obligation it discharges the pathless formal
promise when the thunk input is bound. An `AdapterPhysicalPlace` endpoint promises a requirement at
least as strong, while an `AdapterAbstractPlace` can never supply a proof. Binding
substitutes leaves and discharges obligations only; it cannot alter steps, local IDs, ranking,
lifetime, or cleanup. Lowering can therefore execute a validated recipe without re-running access
or conversion selection.

`ELB-ACC-005`: `PassArgument(PhysicalPlaceArgument(p, binding))` consumes only the
`PlanPhysicalPlaceId` for `physicalParameterStorage(binding)`. `binding.identity` is the
conversion-free physical-storage identity proof and contains its sole type-equality proof. That
proof, `binding.instantiatedRequirement`, `binding.physicalStorage`, `binding.mode`, and
`binding.accessEnvironment` are exactly those selected for that call slot; no separately supplied
lifetime, address-space selection, source-provenance fact, equality, or conversion can replace
them. A direct source uses `ProjectPhysicalPlace(..., RequiredPhysicalStorage(o))`, whose discharged
obligation requires that exact existing `PhysicalPlace`. An accessor-produced source instead uses
`ProjectPhysicalPlaceThroughParameterAccessor` and the exact access-indexed plan stored in
`binding.source`; the plan's dereference endpoint is the argument place. No ordinary getter,
setter/write-back, temporary, or nonidentity conversion satisfies either physical mode.
`WriteAbstractBack` remains available only to the separately specified abstract `OutMode` and
`InOutMode` policies. This is the elaboration invariant corresponding to `TYP-ACC-004`,
`TYP-ACC-006`, and the chapter 7 physical-mode rules.

`ELB-ACC-008`: `ResolveAbstractPlaceThroughReference` is the closed lowering hook for an ordinary
read/write fallback already selected by `PlanStorageAccessAt<S>`; it is not a physical-parameter
binding operation. Its input is the exact `AbstractPlace(plan.invocation.storage)` selected by the
stored `InternalRefStoragePlanAt<S>`. The authorization kind is `ReadThroughRefAccessor` when
followed by `ReadPhysicalPlace` and `WriteThroughRefAccessor` when its result is the destination of
a `CompleteStorageWrite(WritePhysicalStorage(...))` terminal. The stored `plan.storageProof`
satisfies that authorization's complete requirement. No terminal form changes which authorization
was selected.

Executing the step evaluates the invocation's captured sources once, performs the already selected
ref-accessor call, obtains the exact raw result and certificate stored in
`plan.invocation.rawResult`, and validates `plan.handle.raw` is byte-identical to it. The
use-specific `plan.handle.admitted` satisfies `plan.authorization.requirement` without changing the
raw shape; that admitted handle is the exact input of the stored dereference to
`plan.endpoint.output.storage`. `handle` denotes this plan-internal raw/admission pair and `result`
denotes the resulting physical place. The handle has exactly one semantic consumer: the stored
dereference (or the registered transform followed immediately by that dereference). It cannot be
named by the plan terminal, become a `RuntimeArgumentAt<S>`, be stored, returned, captured, merged, or
escape to another operation.
The invocation's `requestContext` is the originating `StorageAccessRequestAt<S>.context`,
`plan.endpoint.output.storage.lifetime` equals that context's `evaluationLifetime`, and the stored
source-lifetime proof has the admitted handle lifetime and that exact result lifetime as endpoints.
`ReadPhysicalPlace` performs the physical load and terminal `WritePhysicalStorage` performs the
physical store; neither operation changes the original property's classifier. Thus the fallback
remains an explicit ref-accessor-call/dereference/load-or-store sequence, while the source property
remains `AbstractPlace`. It is distinct from
`ProjectPhysicalPlaceThroughParameterAccessor`, which requires a
`ParameterReferenceAccessorPlanAt<S>` selected specifically for a physical-mode call and yields the
physical endpoint only to that call plan.

`ELB-ACC-009`: Applying a plan returned for `WriteValueAccess(w)` finds exactly one `TypedInput`
whose node, type, and category equal `w.source` and exactly one `EvaluateOnce` definition used as the
stored write source. Its terminal is exactly `CompleteStorageWrite(operation, sourceValue)`, where
`sourceValue` is that `EvaluateOnce` result. The selected `WritePhysicalStorage` or
`WriteAbstractStorage` operation has `source = ComputedValue(sourceValue)`,
`conversion = w.conversion`, and `when = w.completion`; a ref-accessor fallback first executes its
single `ResolveAbstractPlaceThroughReference` and then uses the same `WritePhysicalStorage`
equation. The
conversion endpoints equal the source value type and destination `placeValueType`, its semantic uses
occur exactly once in the plan union, and `rankingConversion` is `Some` naming that stored
conversion exactly when it participates in ranking and otherwise `None`. No parameter-mode
temporary/write-back or independently reconstructed
right-hand side may satisfy this rule.

`ELB-ACC-006`: `AccessPlan.semanticUses` is the exact canonical union of every
`AbstractAccessorInvocationAt<S>`, `InternalRefStoragePlanAt<S>` invocation,
`ParameterReferenceAccessorPlanAt<S>` invocation, nested conversion, and
registered preparation/terminal/completion operation in the plan. For each
`InitializeTemporary(d, _)`, it additionally contains the complete semantic uses of
`resolve(d.initialization.plan)` and `d.destruction.semanticUses`; the latter is not inferred from
`d.valueType`. Each accessor invocation contributes the call use for its stored `CallableValue<S>`
under the origins, owners, and callable contract recorded by those use values.
Applying or binding the plan copies these edges exactly once; getter/setter selection,
temporary/write-back machinery, and the selected main callee cannot replace or reconstruct them
from a flat effect or capability summary. The invocation's stored `signature` resolves to its
callable target. Receiver presence matches that signature; `indices` covers every ordinary
parameter except the `Set.valueParameter`, whose value is supplied by `WriteAbstractStorage` for a
standalone write or `WriteAbstractBack` for a call-argument write-back.

`ELB-ACC-007`: `IndependentCallSources` permits only `ValueSource` and `PlaceSource` bindings. For
`CapturedReferenceSources(environment)`, `environment.evaluationOrder` is a duplicate-free
bijection onto `environment.results`, and `environment.sourceSet` resolves the exact
`CapturedStorageSources` from which it was built. Result IDs are dense in that source set's
evaluation order, every map key equals the stored ID, and
`capturedSourceRole(result.source)` selects the byte-identical entry in `sourceSet.captures` at that
position. `result.evaluation` is the stage-correct elaboration of
`capturedSourceExpr(result.source)` and its required `Origin` points to that exact typed expression;
this relation, not equal type/category, authorizes the capture. The evaluation remains an explicit
`ElaboratedExprAt<S>` even when its classifier is a place, so lowering has one executable producer
rather than only a semantic `PlaceRef`.
`CapturedSourceProjection(result, projection)` is valid only in this environment; the result
exists, `projection.source = capturedSourceRole(result.source)`, and projecting
`projection.expansion` from the evaluation's derived classifier yields exactly the bound
`AccessOperand` type and category. No separately stored result category may disagree. An empty pack
has no projection. Multiple expansion paths may name one result and never re-evaluate it.

For an explicit reference-accessor plan, every `sourceBindings[role]` names an existing call slot,
operand, and `EvaluateOnce` step in that slot's unchanged recipe. That operand's binding is
`CapturedSourceProjection(result, sourceBindings[role].projection)`, and the step's input is the
same operand. The projection's source is the unique capture result for that role's receiver or
source argument, while its expansion path is the `SourceCallRole` expansion. The source-binding map
covers exactly the receiver and argument roles of the stored accessor call. These equations are a
contextual validator over the call, environment, and bound plans; copying a result ID into a
different environment, slot, operand, source role, expansion, or step is invalid even when the
projected `TypeId` happens to agree.

`ELB-REF-001`: Elaborating `DirectPhysicalReference` validates its stored
`PhysicalStorageProof` and `DirectStorageHandleProof` and then emits the closed
`CoreAddressOfPhysicalStorage` alternative. The latter proof retains the exact
`ConcreteAddressSpaceProjectionProof` from the possibly symbolic physical address space to the
handle's concrete address space, plus the complete source-provenance equality. A
`RegisteredDirectReferenceApplication` instead emits
`CoreRegisteredDirectReference`; its exact standard-environment registration, physical input,
handle output, unary/nonthrowing control proof, and runtime operand are retained. The Core
application stores `input.operandType`, `input.storage`, and `input.proof` in its corresponding
stage-free fields, while the elaborated physical value becomes the separate `place` operand.
Selection state, semantic-use edges, and `input.operand` are consumed rather than copied. Neither
form uses
generic Core `Primitive`, and lowering never chooses an operation from syntax or operand type.
Semantic-use edges have already entered the caller's inference graph and are not contributed a
second time during elaboration.

`ELB-REF-002`: Elaborating `ExplicitAccessorReference` constructs one
`ReferenceCaptureEnvironmentAt<S>` with
`sourceSet = ContentId(plan.invocation.sources)`: it elaborates and
evaluates every exact stored source expression once in
`plan.invocation.sources.evaluationOrder`, assigns the resulting value/place the dense
`ReferenceCaptureResultId` for that position, and projects each
`plan.invocation.sourceBindings[role].projection` through that result without re-evaluating its
source. Those
`CapturedSourceProjection` values bind the already selected `ApplicableCallSlotPlan<S>` recipes
under `ELB-ACC-007`. Let `call = plan.invocation.call`. `ElaborateTypedCallAt<S>` stores
`CapturedReferenceSources(environment)` and then completes that call using exactly
`CallableContractCompletionKey(subjectOf(call.dispatch), call.contractContext)` and forms the
ordinary `CallRegion`. No member lookup, overload resolution, argument mapping, conversion search,
or access planning is repeated. The stored `AccessorReferenceResultCertificate` must name
`call.id`, `subjectOf(call.dispatch)`, `intern(call.signature)`, and the result obtained by replaying
its contract instantiation over this same capture environment and source-binding map. Its
instantiation's `provenanceSources` is byte-identical to
`plan.invocation.provenanceSources`; resolving that map sends each declaration-stable accessor
receiver/parameter role to the captured projection validated under `TYP-PLC-009`. Before
completion, validation requires
`call.resultAuthority = accessorResultAuthority(plan.invocation.declared)` and exactly
the following provenance; deserialization rechecks the same equation:

```text
call.resultProvenance = ReferenceHandleCallResult({
    result = plan.invocation.rawResult.result,
    authority = AccessorReferenceHandleCallResult(
        plan.invocation.rawResult.certificate)
})
```

On normal completion,
the `CallRegion` result has
`ReferenceHandleValue(plan.invocation.rawResult.result.handle)` under that certificate; this is the
inner accessor call's raw result provenance, not a type-based classification or a use-specific
storage requirement. Then
`CoreAccessorReferenceResult(callResult, coreProof)` validates the checked certificate and projects
it before crossing the Core boundary. `coreProof.normalResult = callResult`; its contract,
invocation identity, subject, signature, expected referent, equalities, result, and component-rule
derivation equal the checked certificate. Every typed captured source is replaced by the exact
`CoreValueId` produced by the capture environment, and every formal-to-source projection becomes a
`CoreCallOperandProjection` naming the corresponding Core call operand and expansion path. Neither
`AccessorHandleResultProof`, `AccessorReferenceResultCertificate`, `CapturedStorageSources`, nor a
`NodeId<Typed>` is retained transitively. The wrapper preserves the already handle-shaped normal
result without re-executing or reclassifying it.
`InvokeReferenceAccessor` returns that wrapper under its stored `AccessorHandleAdmissionProof`;
`InvokeReferenceAccessorThenRegistered` feeds the wrapper to one `CoreRegisteredHandleTransform`.
The transform's stage-free Core application retains registration, input/output handle proofs, and
control proof, while the exact wrapper becomes its separate `handle` operand. It drops the typed
`input.operand`, selection state, and semantic-use edges only after validating them. The optional
data operation therefore carries its validated application rather than a bare rule tag.

`ELB-REF-003`: A typed `CheckedDereferenceAt<S>` emits `CoreReferenceDereference`,
`CorePointerDereference`, or `CoreRegisteredReferenceDereference` according to its stored closed
operation. Its `DereferencedStorageProof` supplies the complete physical result type, access,
mutability, address space, lifetime, alias provenance, and source relation. The result lifetime is
exactly `resolve(checked.context).evaluationLifetime`, and its source-lifetime proof has the input
handle lifetime and that exact result lifetime as endpoints. No pass derives that shape from the
operand type or original property. The proof identity equals `checked.identity`, its path is
`DereferencedReference(checked.identity)`, and the exact elaborated handle becomes the Core operand;
`checked.identity = dereferenceApplicationIdentity(checked.site.site)`, and the authenticated site
assignment and typed operand node are not copied into Core. A registered dereference is not erased to generic Core
`Primitive`/IR `DataOperation`.

`ELB-REF-004`: The accessor call, optional registered reference operation, and explicit dereference
remain distinct ordered operations. Lowering cannot fuse an abstract property's reference accessor
into a physical call operand or treat the handle result itself as a place. For an explicit
reference expression, only the separately checked dereference creates a physical place. For a
physical-parameter plan, `ProjectPhysicalPlaceThroughParameterAccessor` retains the same ordered
call/optional-transform/dereference sequence and passes only its proven endpoint through
`PhysicalPlaceArgument`. In neither case does the original property's classifier change from
`AbstractPlace`.

`ElaboratedCall`, `ElaboratedReceiver`, `ElaboratedArgument`, `ElaboratedExpr`, `ElaboratedDecl`,
`AccessPlan`, and `BoundAccessPlan` are shorthand for their `<Published>` forms.
`ConstructionElaboratedDecl = ElaboratedDeclAt<Construction>` is permitted only inside a synthesis
construction; `publishElaboratedDecl(decl, validatedConformances, contractCompletions)` recursively
rewrites every operational witness ref and completes every construction contract state, returning
`ElaboratedDeclAt<Published>` or failing atomically.

`subjectOf(dispatch)` projects a witness use to its stable `InterfaceSubtypeWitnessId` and otherwise
projects a direct/closure `ResolvedDeclRefAt<S>` to its stable `target`; dependency revisions remain
on the dispatch value but do not split a callable contract subject. Builtin dispatch likewise
projects away only its resolution sidecar. It otherwise preserves the exact dispatch identity
shown above. A
`Selection(pre)` state must find one completion under `(subject, contractContext)` whose signature
and stabilized effect/capability facts validate against `pre`; publication replaces it with the corresponding
`Effective` or `SelectedVariant` value. Existing completed states are revalidated. A residual state
may publish only on a partially applied generic callable value and is rejected in an
`ElaboratedCallAt<Published>`. Thus contract completion is part of the atomic stage transform, not
an ambient mutation after publication.

The optional concrete world is present exactly when target-specific variant selection is required;
`SelectedVariant` requires it and its proof's world must equal it. The Boolean assumption records
the enclosing target/stage branch. Consequently two calls to the same subject under different
branches or worlds have distinct completion keys and cannot overwrite one another.

An access recipe is stage-neutral. Typed overload resolution supplies `TypedInput` operands;
abstract interface adapters supply `AdapterInput` roles. Elaboration binds each operand to an
elaborated value/place or to a projection of one explicitly evaluated capture result, producing
`BoundAccessPlan`; it does not rerun applicability or change the recipe. This allows the same plan
algebra to be unit-tested without either a full typed expression tree or generated adapter body.

Default arguments and named/positional reordering are already reflected by `parameter`. Every
temporary, post-conversion, and write-back for an abstract-domain mode is explicit. `InMode`
prepares an ordinary value; `OutMode` and `InOutMode` may use their named temporary/write-back
policies and an abstract destination may invoke its getter/setter contract as those policies
require. `ConstRefMode` and `RefMode` instead pass only the exact physical endpoint retained by
`PhysicalParameterBindingProofAt<S>`: either an existing `PhysicalPlace` or the result of the exact
access-indexed reference-accessor call and stored dereference. Neither physical mode admits an
rvalue, ordinary getter/setter path, conversion, temporary, or write-back. The checker validates
all simultaneous `aliasClass` values and mode-specific claims before the call. A different
throw/write-back policy must be a named language rule, never an incidental lowering choice.

Dispatch is a property of `CallableValue`: a direct symbol, witness method
`(WitnessCallRef<S>, WitnessRuntimeEntryKey)`, dynamic slot, closure invocation, or builtin.
It is deliberately absent from
`FunctionType`; the same signature can be invoked through different dispatch paths.

`ELB-DYN-001`: `DynamicDispatchKey` is the canonical serialized identity of a dynamic slot. Its
`introducer` is the declaration that first creates the slot, `signature` is that declaration's
canonical callable signature, and `slotRole` distinguishes method/getter/setter/ref-accessor/
initializer surfaces. The `owner` at a use is a specialization whose dynamic member map contains
that exact key; an override reuses the introducer/key and proves signature compatibility rather
than allocating a source-order slot. Keys are sorted canonically before any compact ABI index is
assigned. A mismatched owner, signature, or role is invalid dispatch, not a lookup fallback.

`ELB-CALL-001`: The number and identity of elaborated ordinary arguments match the
`CallableSignature.parameterSlots`; each slot ordinal selects the corresponding semantic
`FunctionType` parameter. The receiver is separate; specialization frames are owned by the
canonical declaration reference, conformance, or closure identity inside `CallableValue`.
For direct, closure, or builtin dispatch, the stage-correct witness-resolution sidecar is the exact
minimal union required by all witness evidence in its specialization/static operands and is copied
from the selected bound use or synthesis input without ambient definition search.

`ELB-CALL-002`: Lowering may choose an ABI representation for a passing plan, but may not infer
direction from a wrapper type or declaration modifier.

`ELB-CALL-003`: Direct effect/capability-use collection consumes the `TypedCallAt<S>` records
defined above and completes both least fixpoints before ordinary call elaboration. The direct
effect use and every effect use in a call-slot plan enter effect inference exactly once.
`capabilitySelection.inferredCapabilityUses` is the complete keyed union of the selected callable,
retained extension uses, and every conversion/access-plan use and enters capability inference
exactly once. Its concrete sources and region proof do not enter that graph; they remain selection
evidence. An `ElaboratedCallAt<Published>` permits only
`Effective` or `SelectedVariant` contract state; `Selection` is a pre-inference typed fact and
`ResidualContract` belongs only to a partially applied generic callable value. Generated calls may
temporarily carry `Selection` in `ElaboratedCallAt<Construction>` while their group's use graphs
participate in those fixpoints; `publishElaboratedDecl` consumes the stabilized
`ContractCompletionMap`. Thus a published elaboration cannot enter the inference SCC, and the
callee has one contract authority.

`ELB-CALL-008`: `ElaborateTypedCallAt<S>` requires one `BoundAccessPlan<S>` for every key in
`call.callSlots` and no other key. Each binding discharges only the stored recipe's operands and
physical-storage obligations, and every recipe has a `PassArgument` terminal; a storage-read or
storage-write terminal is a closed elaboration failure at a call slot. `IndependentCallSources` is
required unless the caller supplies the
validated capture environment of `ELB-ACC-007`; capture-result IDs are interpreted only in that
environment. It resolves exactly the completion key formed from `subjectOf(call.dispatch)` and
`call.contractContext`; a missing, wrong-subject, wrong-context, or signature-inconsistent
completion is a closed elaboration failure, not permission to infer or select again.

`ELB-CALL-005`: `BuildTypedCall` is a pure projection of `OverloadResult.Selected.winner` plus the
typed node identity/context. It copies the winner's exact `AccessEnvironmentId`; resolving that one
authority supplies the invocation lifetime that keyed every selected call-slot plan. It copies the
winner's signature, argument map, call-slot plans, selection contract, direct effect use, and result
type, and copies `winner.aliasCompatibility` byte-for-byte. It constructs `capabilitySelection` by the exact `CAP-SEL-004` merge of
`winner.capabilitySelection` with every `slot.access.semanticUses.capabilities` in canonical
`BoundCallSlot` order; `dispatch` is the unique dispatch proven by the
winner's `BoundDeclUse.memberEvidence`/lookup path or registered builtin rule. The direct-use keys
name the enclosing callable and this call's stable child ordinal. Their requirements project the
same `subjectOf(dispatch)` and selection effect/capability facts: direct/closure calls retain their
resolved declaration target plus exact stage-correct witness resolutions, witness calls retain
their witness value and entry, and dynamic/builtin calls retain the
closed registered selection requirement. `selectionContract.signature = intern(signature)` and its
semantic environment is the one used by overload resolution. No body walk or later elaboration may
replace these facts.

The projection also copies `winner.resultAuthority` byte-for-byte and requires
`ResolveCallableResultAuthorityAt<Published>(dispatch, intern(signature))` to return that exact ID.
`BuildTypedCall` derives `resultProvenance` from the resolved authority and the already selected
call/application inputs; it no longer accepts provenance from its caller. An accessor-result
authority that needs a captured-source instantiation is constructed only by the selected-surface
builder below. A same-signature declaration, witness entry, dynamic slot, or builtin registration
cannot lend its authority to the winner.

`ELB-CALL-006`: Generated calls do not fabricate an `OverloadResult`. A synthesis recipe constructs
`ConstructionCallInput` with explicit construction-stage dispatch, plans, direct effect use, and
one complete construction-stage capability selection, and
`BuildConstructionTypedCall` validates the same signature/subject/use equations as `ELB-CALL-005`.
Its supplied `aliasCompatibility` must validate against the complete call-slot plans under their
one access environment.
It also resolves and copies the transaction-local callable's anchored result authority rather than
accepting one as synthesis input.
Every operational conformance ref must belong to the enclosing `SynthesisConstruction`; the result
remains transaction-local until `publishElaboratedDecl` rewrites it. This is the only constructor for
`TypedCallAt<Construction>`.

`ELB-CALL-007`: `BuildSelectedSurfaceTypedCallAt<S>` is used when a prior typed proof already names
one callable surface, such as a property's explicit ref accessor; it does not accept a candidate
list and cannot perform overload ranking. The caller supplies the dispatch proof, exact source map,
signature, access plans, selection contract, `AccessEnvironmentId`, direct effect use, and one
complete callable/extension `CapabilitySelectionAt<S>` plus the exact `aliasCompatibility` proof,
and the constructor validates the
same signature/subject/use equations as `ELB-CALL-005`. At `Construction`, only
`BuildConstructionTypedCall` may invoke this constructor, so transaction authorization cannot be
bypassed. Resolving the supplied access environment must reproduce the semantic environment,
access context, world assumption, invocation lifetime, and origin under which all supplied plans
were checked; no parallel lifetime field may override it.
Before interpreting `resultInput`, the constructor calls
`ResolveCallableResultAuthorityAt<S>(input.dispatch, intern(input.signature))` and stores the
returned ID. `resultInput` supplies only the call-local facts needed to instantiate that already
selected authority; it cannot contain an authority, accessor contract, registration, standard
environment, or static inputs of its own.

`ELB-CALL-009`: Let `A = contractContext.assumption`, `uses(x)` be
`x.inferredCapabilityUses`, and `sources(x)` be empty for `NoConcreteAvailability` or the stored
source list for `ProvenConcreteAvailability`. Every successfully built `TypedCallAt<S>` satisfies:

```text
call.capabilitySelection.region = A

uses(call.capabilitySelection) =
    keyedUnion(uses(baseSelection),
               [uses(slot.access.semanticUses.capabilities)
                | slot in canonicalValues(call.callSlots)])

sources(call.capabilitySelection) =
    canonicalUnion(sources(baseSelection),
                   [sources(slot.access.semanticUses.capabilities)
                    | slot in canonicalValues(call.callSlots)])
```

For `BuildTypedCall`, `baseSelection = winner.capabilitySelection`; `OVL-CAN-003` has already proved
that base selection contains exactly the callable and retained-extension concrete sources and
ordinary uses. For `BuildSelectedSurfaceTypedCallAt<S>`,
`baseSelection = input.capabilitySelection`; the prior surface-selection proof constructs and
validates that complete callable/extension product, and the builder merges it with the supplied
call-slot plans to construct `call.capabilitySelection`. In both
cases, the concrete alternative is `NoConcreteAvailability` exactly for an empty final source set.
For a nonempty final set it is `ProvenConcreteAvailability(s, combineConcreteAvailability(s), p)`,
where `p.region = A`, `p.requirement = combineConcreteAvailability(s)`, and `validate(p)`.

For `BuildTypedCall`, `contractContext` is the request's exact
`ExpressionCheckContext.contractSelection`, and
`resolve(accessEnvironment).worldAssumption = A`, so `A` is the same assumption used by candidate
selection and access planning. Each constructor invokes the central selection/merge operation; it
cannot union only flat requirements, manufacture a source-free proof, omit a conversion/access
source, or move a concrete proof into the ordinary-use map. A one-source result is not privileged:
zero, one, and multiple sources all use the same equation.

`ELB-CALL-010`: A call-result provenance is checked against `call.resultAuthority` before the call
is published. Resolving that ID must yield the exact declaration/registered anchor selected by
`call.dispatch` and `intern(call.signature)`. `OrdinaryCallResult` is valid exactly for
`OrdinaryCallableResult`. For `FixedReferenceHandleCallResult(a)`, the authority kind is
`FixedReferenceHandleCallableResult(a)` and resolving `a` yields the call result type and the
byte-identical stored `ReferenceHandleValueShape`. For a registered call result, the authority kind
names one `RegisteredReferenceHandleResultContract`; its registration, environment, and static
inputs are copied into the call-specific provenance and replay over the exact runtime inputs to
derive the stored raw result shape. Call-result provenance states what the call produces; a
consumer separately proves that shape against its own physical-storage/reference requirement.
Equal signature, result `TypeId`, or pointer-like machine representation cannot choose another
authority alternative.

The explicit-accessor path is atomic and has no construction cycle. The caller supplies the
`AccessorReferenceHandleSurfaceCallResult` alternative with `invocationIdentity`, `invocationSite`, `sources`,
`provenanceSources`, `expectedReferent`, `context`, and `result`, not an authority, contract, or
certificate containing an already-built call. The builder requires the already resolved authority kind to be
`AccessorReferenceHandleCallableResult(contract)` and constructs the following immutable input from
its own prospective identity and selected surface:

```text
AccessorReferenceResultInstantiationInputAt<S> {
    contract,
    invocationIdentity,
    invocationSite,
    call = id,
    subject = subjectOf(input.dispatch),
    signature = intern(input.signature),
    sources,
    provenanceSources,
    expectedReferent,
    context
}
```

It invokes `InstantiateAccessorReferenceResultAt<S>` once and publishes a
`ReferenceHandleCallResult` whose result is `result` and whose authority is
`AccessorReferenceHandleCallResult(certificate)` only when the returned
certificate repeats every semantic input field other than the consumed source-only
`invocationSite`, its instantiation has the identical `invocationIdentity` and `provenanceSources`,
`certificate.result = result`, and
`result.type = input.resultType`. Thus neither the certificate nor the raw result provenance
requires a
previously constructed `TypedCallAt<S>`. A selected property/subscript ref-accessor surface must use
this alternative; the ordinary, fixed, and registered alternatives cannot stand in for it. The
builder also requires `ValidateSemanticOperationSite(id, invocationSite) = Success(Unit)` and
`invocationIdentity = accessorInvocationIdentity(invocationSite.site)`, so a caller cannot choose
another fresh-alias seed or derive one from the prospective typed-call ID. The source-only site
assignment is consumed before Core; the nominal content ID is the stage-free value retained by
Core and IR.

`ELB-CALL-011`: `ElaborateTypedCallAt<S>` copies `call.accessEnvironment`,
`call.resultAuthority`, `call.resultProvenance`, `call.aliasCompatibility`, and the complete
`call.capabilitySelection`
byte-for-byte to the
`ElaboratedCallAt<S>`. A reference-handle alternative
determines the call region's handle-shaped normal result before `CoreAccessorReferenceResult` is
emitted. That wrapper validates the stored
accessor certificate and preserves the already handle-shaped result; it cannot fabricate handle
provenance, change a component of the shape, or reclassify an ordinary result.

`ELB-CALL-004`: Let `contractSignature(callee.contract)` select the effective contract's signature
and let `intern(signature)` be the canonical `CallableSignatureId`. Every
`ElaboratedCallAt<Published>` satisfies
`intern(signature) = contractSignature(callee.contract)` and
`resultType = resolve(signature.functionType).result`. In addition, resolving
`CallableContractCompletionKey(subjectOf(callee.dispatch), contractContext)` in the frozen semantic
snapshot must yield exactly the effective/selected-variant payload stored in `callee.contract`; the
contract of a same-signature but different subject is invalid. For
`SelectedVariant(set, proof, contract)`,
`proof.set = set`, the selected variant's signature is `contract.signature`, and resolving the
dispatch target through a direct declaration or validated witness entry yields `proof.selected`.
Dynamic/builtin dispatch cannot carry `SelectedVariant` unless its registered rule defines that
same target-resolution proof. These endpoint checks make signature, result, dispatch, and contract
one mechanically validated fact rather than parallel claims. In addition,
`ResolveCallableResultAuthorityAt<Published>(callee.dispatch, intern(signature))` returns the
elaborated call's exact `resultAuthority`, and `resultProvenance` validates against its kind under
`ELB-CALL-010`; callable-contract completion cannot swap either fact.

## Lambda elaboration

Lambda processing uses the following pure queries. `DiscoverFreeVariables` runs while constructing
`TypedLambda`; elaboration consumes that stored result and does not rediscover it:

```text
DiscoverFreeVariables(lambda, boundBody) -> FreeVariableSet
AnalyzeTypedCaptures(lambda, typedLambda.freeVariables, typedLambda.captureUseFacts) -> CaptureSet
BuildClosureType(lambda, captureSet, signature)
    -> ClosureDeclAt<Construction>
RewriteLambdaBody(lambda, closureDecl)
    -> ElaboratedFunctionBodyAt<Construction>
BuildClosureValue(lambda, closureDecl)
    -> ElaboratedExprAt<Construction>
```

```text
CapturePlan = {
    source: LocalCapture(CanonicalDeclRef)
          | ReceiverCapture
          | ForwardedCapture(ForwardedCaptureIdentity),
    type: TypeId,
    mode: ByValue | BorrowedReadCapture | BorrowedReadWriteCapture |
          RefCapture(access: AccessMode),
    lifetime: CaptureLifetime,
    lifetimeProof: Option<CaptureLifetimeProof>,
    firstUse: Origin
}

CaptureSet = {
    byIdentity: NodeMap<CaptureIdentity, CapturePlan>,
    order: NodeList<CaptureIdentity>
}

CaptureLayout = {
    fields: NodeMap<CaptureIdentity, SynthesizedDeclId>,
    order: NodeList<CaptureIdentity>
}

ForwardedCaptureIdentity = {
    parentLambda: NodeId<Typed>,
    parentCapture: CaptureIdentity
}

CaptureIdentity = {
    lambda: NodeId<Typed>,
    source: CanonicalDeclRef | ReceiverCapture | ForwardedCaptureIdentity
}

CaptureLifetime = OwnedByClosure | BorrowedUntil(LifetimeId)

CaptureLifetimeProof = {
    capturedSource: CaptureIdentity,
    sourceLifetime: LifetimeId,
    requiredLifetime: LifetimeId,
    outlives: OutlivesProof
}
```

`ELB-LAM-001`: `TypedLambda.captureUseFacts` is the sole typed-body projection consumed by capture
analysis. Every fact's source occurs in `freeVariables`, and every typed use of a free variable has
exactly one fact with the same origin, type, category, access, and source lifetime. The typed-lambda
constructor validates this bijection; elaboration neither walks `typedBody` to rediscover uses nor
adds an unrecorded capture.

`ELB-LAM-002`: A `ForwardedCaptureIdentity.parentLambda` is the immediate lexically enclosing
lambda, and `parentCapture.lambda` equals it. Following forwarded identities strictly decreases
lambda nesting depth and terminates at a declaration or receiver capture. Capture-set/layout maps
are keyed by the complete identity, so equal source declarations captured through different parent
chains cannot alias accidentally.

`ELB-LAM-003`: For every `CaptureLifetimeProof`, `outlives.longer = sourceLifetime` and
`outlives.shorter = requiredLifetime`. A borrowed capture's `BorrowedUntil` lifetime equals
`requiredLifetime`; an owned capture does not carry a borrowed-lifetime proof. Forwarding may reuse
an enclosing proof only when both endpoint IDs remain exactly equal.

Unqualified `CallableValue`/`CallableDispatch` mean the `<Published>` forms. Generated bodies may
use `<Construction>` only inside the draft/synthesis scope defined in chapter 8; atomic freeze
rewrites every operational reference before an `ElaboratedCall` or IR node is published.

Binding discovers only which lexical declarations are free. Capture order is the lexical order of
first source use with stable declaration identity as a tie-breaker. Nested-lambda capture forwarding
is explicit in `source`. Capture mode and lifetime are inferred from the typed uses and type
properties; they cannot be decided from a merely bound body. A non-copyable value cannot silently
become a by-value capture, and a borrowing/ref capture must carry a lifetime proof that covers every
closure use. Whether escaping borrowed captures are supported is an explicit language decision in
chapter 12.

`CaptureSet.order` is a duplicate-free bijection onto `byIdentity` keys in that semantic order;
`CaptureLayout.order` is byte-identical and is a duplicate-free bijection onto `fields` keys. The
maps provide identity lookup while the explicit lists, not map iteration, define layout.

The synthesized closure is construction-stage data until its declaration and callable conformance
freeze together:

```text
ClosureDeclAt<S: WitnessUseStage> = {
    declaration: SynthesizedDeclId,
    layout: CaptureLayout,
    initializer: CallableSignature(
        FunctionType(NoReceiver, one parameter per capture, result=Self),
        stable synthesized ParameterKeys),
    invoke: CallableSignature(
        FunctionType(receiver=Receiver(Self, selected mode),
                     parameters=lambda parameters,
                     result=lambda result),
        lambda ParameterKeys),
    callableConformance: WitnessCallRef<S>
}

ClosureDecl = ClosureDeclAt<Published>
```

The rewritten body replaces each captured reference with a field access through the explicit
receiver. The lambda expression becomes `ConstructClosure(closure, capturedValues)`. No `LambdaExpr`
reaches Core AST.

`SYN-LAM-001`: Free-variable discovery reads a bound body; capture-mode analysis reads the typed
body. Both return immutable data and neither inserts fields while walking.

`SYN-LAM-002`: The callable conformance's witness map is keyed by the standard environment's call
requirement key. Closure layout order is not used as witness identity. During construction the
field is an operational reference authorized by the closure's `SynthesisConstruction`; atomic
freeze rewrites it to the validated reference for the same conformance identity at the same time
that it publishes the closure declaration and rewritten body.

`SYN-LAM-003`: Inferred result types are solved from all reachable returns and the fall-through
path before closure synthesis. A mutable “first return fills the type” protocol is forbidden.

`SYN-LAM-004`: Capture identity excludes discovery/task order. A non-owned capture's lifetime proof
must name the same capture, source lifetime, and every closure-use requirement; validators reject a
missing/mismatched proof before assigning `CaptureLayout`. `RefCapture(access)` preserves the exact
read/write/atomic access mode established by typed use analysis.

The result solver combines the contextual expected result, every reachable `return`, the
fall-through result (`Unit` when permitted), `Never` paths, and recovery expressions using the join
rules in chapter 6. A captureless lambda may additionally elaborate to a static thunk when a raw
function type is expected; a capturing lambda is never silently converted to a raw function
pointer. The thunk and any closure declarations belong to the same atomic `SynthesisGroup`.

## Interface requirement synthesis

Conformance checking first produces the authoritative kind-indexed `RequirementMatch<K>` from
chapter 8 for every
`RequirementKey<K>`. The payload/proof shapes are parallel to `RequirementSatisfaction<K>`: an
associated type carries a `TypeId` plus constraint proofs, a callable carries a canonical
declaration plus a signature proof, an accessor aggregate carries a role-keyed accessor map, a
constant carries a checked value, and a nested conformance carries an
`InterfaceSubtypeWitnessId` plus its stage-appropriate resolution set.

`Exact` and `OptionalAbsent` never create code. `Adaptable` creates an adapter; `Defaulted` and
`Builtin` create code only when their typed plans declare generated output roles. Callable adapters
use exactly `RequirementAdapterPlan<CallableKind>` and default matching uses
`DefaultUsePlan<K, Construction>` from chapter 8. Its `ParameterCorrespondence`
maps requirement slots (including receiver and pack expansions) to independently keyed
implementation slots; the keys are not compared for equality. Its parameter access plans consume
requirement-call arguments and produce implementation-call arguments, its result conversion maps
implementation success to the required result, and its error plan proves and implements
propagation, conversion, catching, or the absence of thrown errors.

`SYN-WIT-001`: Synthesis is permitted only from a validated adapter plan. Code generation never
rediscovers how a candidate satisfies a requirement.

`SYN-WIT-002`: A synthesized thunk has the exact required `FunctionType`, including receiver,
parameter modes, result/error type, traits, and calling convention. Its separate effective callable
contract satisfies the requirement's effect and capability obligations. Its body applies the
adapter plan and calls the chosen implementation.

`SYN-WIT-003`: The resulting witness-map entry is keyed by `RequirementKey` and refers to the
synthesized declaration by stable ID. Associated-type and nested-conformance requirements produce
typed witness alternatives, not function stubs.

This same mechanism handles property/accessor adaptation, static-versus-instance adapters when the
language permits them, default interface methods, enum builtin requirements, differentiability
requirements, and synthesized constructors. Each case has a distinct rule ID and adapter-plan
constructor; they do not share a large branch that mutates arbitrary AST fields.

## Other desugarings

The initial Core AST has these explicit rewrites:

| Typed/elaborated form            | Core form                                                       |
| -------------------------------- | --------------------------------------------------------------- |
| operator syntax                  | direct call or declared primitive operation                     |
| property/subscript read          | explicit getter call                                            |
| property/subscript write         | getter/setter access plan with explicit write-back              |
| initialization syntax            | the distinct operation selected by `InitializationPlan`         |
| implicit conversion              | `Convert(plan, value)`                                          |
| existential conversion           | `PackExistential(value, type, witness)`                         |
| existential member use           | `OpenExistential` region plus witness lookup                    |
| `fwd_diff` / `bwd_diff`          | selected provider plus `DerivativeSignatureMapId`               |
| `no_diff`                        | explicit `StopGradient` boundary                                |
| `defer`                          | explicit cleanup regions on every exiting edge                  |
| lambda                           | closure declaration plus construction                           |
| default argument                 | expression cloned through provenance-preserving substitution    |
| target/stage switch              | conditional Core regions with capability presence formulas      |
| compile-time loop/pack expansion | explicit expansion nodes or materialized sequence after solving |

Desugaring order is defined by dependencies between rewrite queries, not by a mutable visitor's
incidental traversal. A rewrite consumes only the node forms listed in its input schema and produces
a strictly later Core form, preventing rewrite loops.

## Core AST

Core AST is deliberately small:

```text
CoreExpr = Constant | PhysicalPlace(CorePhysicalPlace) |
           BuiltinPhysicalProjection(CoreBuiltinPhysicalProjection) |
           RegisteredPhysicalProjection(CoreRegisteredPhysicalProjection) |
           Load(CoreLoad) | Store | TemporaryStorage(CoreTemporaryStorage) |
           ReferenceProducer(CoreReferenceProducer) | Dereference(CoreDereference) |
           Convert | Initialize(CoreInitialization) | Extract | Update | CallRegion |
           Witness | PackExistential | OpenExistential | Differentiate |
           StopGradient | Primitive | Error

CoreStmt = Let | Var | Assign | ExprStmt | DestroyTemporary(CoreDestroyTemporary) |
           If | Switch | Loop | Break | Continue | Return | Throw | Region |
           CleanupRegion | Error

CoreDecl = TypeDecl | FunctionDecl | GlobalDecl | ConformanceDecl | ImportDecl | ErrorDecl

CorePhysicalPlaceShape = {
    access: AccessMode,
    mutability: Mutability,
    addressSpace: PhysicalStorageAddressSpace,
    lifetime: LifetimeId,
    alias: AliasProvenance,
    sourceProvenance: PhysicalStorageSourceProvenance
}

CorePhysicalPlace = {
    valueType: TypeId,
    storage: PhysicalStorageRef
}

CoreTemporaryStorageShape = {
    identity: TemporaryStorageIdentity,
    lifetime: LifetimeId,
    alias: AliasProvenance
}

CoreTemporaryStorage = {
    descriptor: MaterializedTemporaryStorage,
    source: CoreValueId
}

CoreDestroyTemporary = {
    storage: CoreValueId,
    destruction: DestructionExecutionAt<Published>
}

CoreBuiltinPhysicalProjection = {
    identity: BuiltinPhysicalProjectionIdentity,
    operation: BuiltinPhysicalProjectionOperation,
    runtimeOperands:
        CanonicallyOrderedMap<BuiltinPhysicalProjectionOperandRole, CoreValueId>,
    evaluationOrder: NodeList<BuiltinPhysicalProjectionOperandRole>,
    inputShapes:
        CanonicallyOrderedMap<BuiltinPhysicalProjectionOperandRole, CoreValueShape>,
    output: BuiltinPhysicalProjectionResultProof,
    control: BuiltinPhysicalProjectionControlProof
}

CoreLoad = LoadPhysicalStorage(source: CoreValueId)

CoreRegisteredPhysicalProjection = {
    identity: RegisteredPhysicalProjectionIdentity,
    registration: RegisteredDataOperationRegistration,
    runtimeOperands:
        CanonicallyOrderedMap<RegisteredPhysicalProjectionOperandRole, CoreValueId>,
    evaluationOrder: NodeList<RegisteredPhysicalProjectionOperandRole>,
    inputShapes:
        CanonicallyOrderedMap<RegisteredPhysicalProjectionOperandRole, CoreValueShape>,
    output: RegisteredPhysicalProjectionResultProof,
    control: RegisteredPhysicalProjectionControlProof
}

CoreRegisteredDirectReferenceApplication = {
    registration: ReferenceOperationRegistration,
    operandType: TypeId,
    storage: PhysicalStorageRef,
    storageProof: PhysicalStorageProof,
    output: ReferenceHandleProof,
    control: ReferenceDataOperationControlProof
}

CoreRegisteredHandleTransformApplication = {
    registration: ReferenceOperationRegistration,
    input: ReferenceHandleProof,
    output: ReferenceHandleProof,
    control: ReferenceDataOperationControlProof
}

AccessorAddressSpaceDerivation = {
    rule: AccessorReferenceAddressSpaceRule,
    registeredEnvironment: Option<StandardEnvironmentId>,
    result: AddressSpace
}

AccessorMutabilityDerivation = {
    rule: AccessorReferenceMutabilityRule,
    registeredEnvironment: Option<StandardEnvironmentId>,
    result: Mutability
}

AccessorLifetimeDerivation = {
    rule: AccessorReferenceLifetimeRule,
    registeredEnvironment: Option<StandardEnvironmentId>,
    result: LifetimeId
}

AccessorAliasDerivation = {
    rule: AccessorReferenceAliasRule,
    registeredEnvironment: Option<StandardEnvironmentId>,
    invocationIdentity: Option<AccessorInvocationIdentity>,
    result: AliasProvenance
}

AccessorSourceProvenanceDerivation = {
    rule: AccessorReferenceSourceRule,
    registeredEnvironment: Option<StandardEnvironmentId>,
    result: PhysicalStorageSourceProvenance
}

AccessorReferenceResultDerivation = {
    addressSpace: AccessorAddressSpaceDerivation,
    mutability: AccessorMutabilityDerivation,
    lifetime: AccessorLifetimeDerivation,
    alias: AccessorAliasDerivation,
    sourceProvenance: AccessorSourceProvenanceDerivation
}

CoreCallOperandProjection = {
    slot: BoundCallSlot,
    operand: CoreValueId,
    expansion: ExpansionPath
}

CoreCapturedSourceBinding = {
    capturedValue: CoreValueId,
    projections: NodeList<CoreCallOperandProjection>
}

CoreAccessorReferenceResultProof = {
    normalResult: CoreValueId,
    contract: AccessorReferenceResultContractId,
    invocationIdentity: AccessorInvocationIdentity,
    subject: CallableContractSubject,
    signature: CallableSignatureId,
    expectedReferent: TypeId,
    referentEquality: TypeEqualityProofId,
    sources:
        CanonicallyOrderedMap<AccessorProvenanceSourceRole,
                              CoreCapturedSourceBinding>,
    derivation: AccessorReferenceResultDerivation,
    result: ReferenceHandleValueShape,
    callResultType: TypeId,
    resultEquality: TypeEqualityProofId
}

CoreReferenceProducer =
    CoreAddressOfPhysicalStorage(
        place: CoreValueId,
        proof: DirectStorageHandleProof)
  | CoreAccessorReferenceResult(
        value: CoreValueId,
        proof: CoreAccessorReferenceResultProof)
  | CoreRegisteredDirectReference(
        place: CoreValueId,
        application: CoreRegisteredDirectReferenceApplication)
  | CoreRegisteredHandleTransform(
        handle: CoreValueId,
        application: CoreRegisteredHandleTransformApplication)

CoreRegisteredDereferenceApplication = {
    identity: DereferenceApplicationIdentity,
    registration: ReferenceOperationRegistration,
    input: ReferenceHandleProof,
    output: DereferencedStorageProof,
    control: ReferenceDataOperationControlProof
}

CoreDereference =
    CoreReferenceDereference(
        handle: CoreValueId,
        proof: DereferencedStorageProof)
  | CorePointerDereference(
        handle: CoreValueId,
        proof: DereferencedStorageProof)
  | CoreRegisteredReferenceDereference(
        handle: CoreValueId,
        application: CoreRegisteredDereferenceApplication)

CoreRuntimeValueCategory =
    RValue
  | ReferenceHandleValue(ReferenceHandleShape)
  | PhysicalPlace(CorePhysicalPlaceShape)
  | TemporaryStorage(CoreTemporaryStorageShape)

CoreValueShape =
    RuntimeCoreValueShape(type: TypeId, category: CoreRuntimeValueCategory)
  | GenericMetadataCoreValueShape(variable: CanonicalBoundVariable)
  | WitnessCoreValueShape(classifier: InterfaceWitnessClassifier)
  | WitnessEntryCoreValueShape(key: SomeWitnessEntryKey)
  | OtherConstraintEvidenceCoreValueShape(slot: CanonicalConstraintSlot)

CoreGenericInputs = {
    genericArguments: NodeMap<CanonicalBoundVariable, CoreValueId>,
    constraintEvidence: NodeMap<CanonicalConstraintSlot, CoreValueId>
}

CoreWitnessOperation =
    WitnessTableReference(definition: ValidatedConformanceRef)
  | SpecializeWitness(generic: CoreValueId,
                      specialization: CanonicalSpecializationSpine,
                      inputs: CoreGenericInputs)
  | LookupWitness(base: CoreValueId, key: SubtypeWitnessLookupKey)
  | LookupWitnessEntry(base: CoreValueId, key: SomeWitnessEntryKey)
  | ExtractExistentialWitness(package: CoreValueId,
                              interface: InterfaceInstanceKey)

CoreValueKey = {
    producer: NodeId<Core>,
    resultOrdinal: UInt32,
    shape: CoreValueShape
}

CoreValueId = ContentId<CoreValueKey>

CoreCallContract = {
    signature: CallableSignatureId,
    resultAuthority: CallableResultAuthorityId,
    effective: EffectiveCallableContractId,
    callerInvocationLifetime: LifetimeId,
    aliasCompatibility: CompatibleCallAliasClaims,
    capabilitySelection: CapabilitySelection
}

CorePhysicalParameterSourceProof =
    ExistingCorePhysicalEndpoint
  | AccessorCorePhysicalEndpoint(
        dereference: DereferenceApplicationIdentity)

CorePhysicalParameterInputProof = {
    mode: PassingMode,
    storage: PhysicalStorageRef,
    parameterValueType: TypeId,
    identity: PhysicalStorageIdentityProof,
    instantiatedRequirement: PhysicalStorageRequirement,
    physicalStorage: PhysicalStorageProof,
    source: CorePhysicalParameterSourceProof
}

CoreCallInputs = {
    initializationTarget: Option<CoreValueId>,
    receiver: Option<CoreValueId>,
    parameters: NodeMap<ParameterKey, CoreValueId>,
    physicalParameters:
        NodeMap<BoundCallSlot, CorePhysicalParameterInputProof>,
    generic: CoreGenericInputs
}

DirectCall = {
    callee: ResolvedDeclRef,
    contract: CoreCallContract,
    inputs: CoreCallInputs
}

WitnessCall = {
    witness: CoreValueId,
    entry: WitnessRuntimeEntryKey,
    contract: CoreCallContract,
    inputs: CoreCallInputs
}

DynamicCall = {
    owner: TypeId,
    slot: DynamicDispatchKey,
    contract: CoreCallContract,
    inputs: CoreCallInputs
}

ClosureCall = {
    invoke: ResolvedDeclRef,
    contract: CoreCallContract,
    inputs: CoreCallInputs
}

PrimitiveCall = {
    rule: RuleId,
    registration: StandardEnvironmentRuleId,
    staticInputs: CanonicalArguments,
    witnessResolutions: WitnessResolutionStamp,
    contract: CoreCallContract,
    inputs: CoreCallInputs
}

CoreCall = Direct(DirectCall) | Witness(WitnessCall) | Dynamic(DynamicCall) |
           Closure(ClosureCall) | Primitive(PrimitiveCall)

CallRegion = {
    preparation: NodeList<CoreStmt>,
    call: CoreCall,
    normalCompletion: NodeList<CoreStmt>,
    exceptionalCompletion: NodeList<CoreStmt>,
    result: CoreValueId,
    thrownError: Option<CoreValueId>
}
```

Chapter 15 is the sole schema authority for `CoreInitialization` and its selected-operation
alternatives; the `Initialize` case above does not erase them to a generic construct flag. Its
recovery alternative is tooling-only and is not a successful initialization operation.

All Core nodes are typed. `PhysicalPlace`, `TemporaryStorage`, `ReferenceProducer`, and
`Dereference` preserve their exact value type, access, lifetime, alias, and source provenance until
IR lowering; only genuine physical storage carries mutability and a physical address-space fact.
Abstract properties and declared subscripts have already become accessor call regions. High-level
structured control remains where useful, but its exit and cleanup behavior is explicit.

`ELB-CORE-001`: Core validation rejects unresolved names, overload sets, partial generic
applications, implicit receivers, unplanned conversions, raw lambdas, and incomplete witness maps.

`ELB-CORE-002`: `LowerToCore` first lowers every access plan's preparation in order, then dispatches
on its closed terminal. `PassArgument` contributes the named runtime argument and its completion
steps to the enclosing call or registered-operation region. `YieldStorageRead` produces the named
Core value directly; it does not synthesize a call region for a physical load. `CompleteStorageWrite`
emits its exact physical `Store` or abstract-setter `CallRegion` and yields the terminal's result
value after normal completion. Completion steps are placed on the normal/exceptional edges selected
relative to that terminal. A captured-reference source environment first lowers each capture
result's explicit `evaluation` to exactly one Core producer in its stored order, and every
`CapturedSourceProjection` reads that producer. Thus no source capture, preparation, terminal, or
completion behavior remains hidden inside a call opcode or inferred from the consuming syntax.

Lowering an abstract `OutMode`/`InOutMode` temporary creates one `CoreTemporaryStorage` whose
descriptor is byte-identical to the access-plan descriptor and whose chapter 15 initialization is
the descriptor's exact plan application. This Core node projects that application's unique
`CreatePlanStorage` transition rather than allocating a second object. The nested Core
initialization owns pre-checkpoint exceptional cleanup; only its normal checkpoint produces the
temporary value. Every later write-back and `CoreDestroyTemporary` carries the checked conversion
or destruction execution from the plan, and no operation chooses either from the Core value type.
Its `CoreTemporaryStorageShape.identity` is the descriptor's nominal
`TemporaryStorageIdentity`, and its alias is the matching `temporaryStorageAliasRoot`; Core removes
the site from the runtime value shape after checking that equation, while the selected
initialization application retains its authenticated site as static validation data.

`ELB-CORE-010`: Lowering `PhysicalPlaceArgument(p, binding)` emits the Core physical-place value for
exactly `physicalParameterStorage(binding)`. A direct source reuses the lowered existing physical
producer. An accessor-produced source expands the stored
`ParameterReferenceAccessorPlanAt<S>` into its accessor `CallRegion`, optional registered handle
transform, and `CoreDereference`, in that order; the dereference's output is the physical argument.
The accessor handle has no other Core use. The resulting Core value retains access, mutability,
physical address space, lifetime, alias, and source provenance, and no Core temporary, load,
conversion, or write-back intervenes. `ConstRefMode` and `RefMode` therefore share this one physical
Core path while remaining distinguishable by `binding.mode.access` and the complete requirement
proof selected before lowering. The corresponding `CoreCallInputs.physicalParameters` entry is the
stage-free projection of `binding`: it retains mode, endpoint, parameter type, identity proof,
instantiated requirement, and physical proof, and records whether the Core operand is an existing
endpoint or the result of the exact stored dereference. It contains no typed expression or accessor
plan.

`ELB-CORE-011`: At function entry, every `PhysicalStorageAbiInput` creates one
`CorePhysicalPlace` whose `PhysicalStorageRef` is the contract's exact formal storage. A
`ConstRefMode` receiver/parameter uses its nominal `ConstRefFormalRoot`, has `ReadAccess`,
`UnknownMutability`, `CallableActivationLifetime(signature)`, and cannot be stored through. A
`RefMode` role uses its nominal `RefFormalRoot`, has `ReadWriteAccess`, `Mutable`, and may be read or
written subject to its checked contract. Both use the entry proof's formal address space, source
facts, and `UnknownAliasRoot`. Physical projections preserve those facts and may not amplify
access. There is no borrowed formal category or hidden conversion between the two roots.

`ResolveAbstractPlaceThroughReference` expands to the stored accessor `CallRegion`, its
already-proven handle result (and optional registered transform), and the stored `CoreDereference`.
The enclosing read terminal then selects the physical `Load`, while the write terminal selects the
physical `Store`. The intermediate handle is kept in that local sequence and has no escaping Core
use.

`ProjectPhysicalPlaceThroughParameterAccessor` expands through the same closed reference
primitives but from its distinct `ParameterReferenceAccessorPlanAt<S>`. It emits no load or store:
the stored `CoreDereference` result is the `PhysicalPlaceArgument` endpoint. Its accessor access key,
handle admission, dereference proof, and resulting physical storage are preserved exactly, so
ordinary storage fallback and physical-parameter preparation cannot be interchanged.

`ELB-CORE-003`: `CoreValueId = ContentId(CoreValueKey)` under chapter 1's exact encoding.
Resolving the producer node must find `resultOrdinal` and the identical stored result shape. Two
results of one node, or equal-shaped results of different nodes, therefore remain distinct without
allocation-order identity. Every Core operand resolves in the containing immutable Core snapshot.

`ELB-CORE-004`: Resolving `CoreCallContract.effective` yields an effective contract whose
signature equals `contract.signature`. Resolving that signature yields exactly the keys in
`inputs.parameters`; the receiver is present exactly when its `ReceiverSlot` is present, and
`initializationTarget` is present exactly when `CallablePurpose` is `InitializerCallable`. That
target is a physical-place Core value satisfying the stored target slot and is never receiver or
parameter zero. Each other input's type/category is valid for the corresponding `PassingMode` after
the explicit preparation steps. A mode whose domain is `PhysicalOperand(location)` has exactly a
`RuntimeCoreValueShape(valueType, PhysicalPlace(shape))` input. The originating call-slot plan has a
`PhysicalPlaceArgument` whose binding names the same endpoint and complete mode, and its
`physicalStorage` proof satisfies
`instantiatePhysicalStorageRequirement(mode, callerInvocationLifetime)`, including access,
lifetime, symbolic address space, and source provenance. `ConstRefMode` requires the read view;
`RefMode` requires the read/write view. Core validation compares the retained endpoints and never
re-instantiates a weaker requirement. An ordinary rvalue, abstract place, reference handle, or
temporary-storage value is invalid even if its `TypeId` agrees. A nonphysical-mode
reference-handle value remains
`ReferenceHandleValue(handle)` with the exact checked proof rather than becoming `RValue`.
`inputs.physicalParameters` has exactly the receiver/parameter-role domain whose modes are physical.
Each entry's storage projects to the corresponding Core input shape; its identity proof endpoints
are that storage's value type and the substituted parameter type with zero rank; and its physical
proof has the byte-identical storage and instantiated requirement. `ExistingCorePhysicalEndpoint`
requires the call operand to be the lowered direct source.
`AccessorCorePhysicalEndpoint(d)` requires it to be the output of the exact `CoreDereference` with
identity `d`. No stage-specific binding is consulted after this projection.
`generic.genericArguments` and `generic.constraintEvidence`
contain exactly the runtime binder/evidence slots selected by the call's logical ABI map.
Type/value/pack arguments use `GenericMetadataCoreValueShape` with the identical bound variable;
`Conforms` evidence uses `WitnessCoreValueShape` with the exact predicate classifier, and every
other evidence value uses `OtherConstraintEvidenceCoreValueShape` with the identical slot. The
callee's `ResolvedDeclRef.witnessResolutions` is the exact source for materializing table-backed
evidence in its canonical specialization; no ambient definition lookup is permitted. Parameter
order is derived only from `CallableSignature.parameterSlots`, never from the map's iteration order.
`contract.callerInvocationLifetime` equals
`resolve(originatingTypedCall.accessEnvironment).invocationLifetime` and is copied unchanged
specifically for call-local ABI activation binding; it never enters the callee's declaration
`FunctionAbiMap`. The same resolved access environment is the authority for the selected access
plans, so no independent lifetime can disagree with them.
`contract.aliasCompatibility` is copied from the originating elaborated call and replays over the
same physical/abstract endpoint provenances and invocation lifetime. It cannot be rebuilt from
Core operand order or dropped merely because target ABI lowering permits aliasing.
`contract.resultAuthority` is copied byte-for-byte from the originating elaborated call and
resolves under the Core dispatch target and `contract.signature` to the same anchored authority.
Core construction cannot infer it from the result value or replace it during effective-contract
completion. `contract.capabilitySelection` is copied byte-for-byte from the originating elaborated
call. It remains the complete `CAP-SEL-004` product after inference has consumed its ordinary-use
map: its region, exact keyed uses, and zero/one/multiple concrete source set with combined
requirement and proof all revalidate under `CAP-SEL-003`. Core construction cannot reconstruct it
from `effective`, a flat capability formula, or the dispatch target.

`ELB-CORE-005`: A direct target resolves to the stored signature; a witness target consumes a
`WitnessCoreValueShape(ConcreteInterfaceWitness(target))` whose target interface owns the exact
runtime-entry key and resolves that
entry to the signature; a dynamic slot and closure invocation resolve through their registered
owner/invoke declaration; and a primitive rule resolves in the versioned standard environment.
These are validation operations, not overload or conformance search. A target that resolves to a
different signature or contract is an invalid Core graph.

`ELB-CORE-006`: `result` is result ordinal zero of the `CallRegion` node and has the signature's
normal result type. Its category is the exact checked result-channel proof admitted by
`contract.resultAuthority`:
`ReferenceHandleProvenance(proof)` becomes `ReferenceHandleValue(proof.shape)`, an inner explicit
ref-accessor call uses the result shape and stage-free instantiation projected from its exact
`AccessorReferenceResultCertificate`, and
`NoAdditionalValueProvenance` becomes `RValue`. `thrownError` is ordinal one with the corresponding
checked provenance and the signature's error type exactly when that type is not `NeverType`,
matching the logical ABI channel. A physical place is never returned as a call result. The exceptional edge
exists only when the effective contract can throw; otherwise `exceptionalCompletion` is empty and
`thrownError` has no legal use. The call inputs are available after `preparation`; `result` is
visible only on the normal-completion edge and `thrownError` only on an existing exceptional edge.
A value defined on one completion edge cannot be used on the other or after a non-joining exit.

`ELB-CORE-007`: Abstract storage is eliminated before Core. Every Core `PhysicalPlace`, `Load`,
`Store`, address-of/registered-direct reference input, and dereference result has a
`CorePhysicalPlaceShape`; no Core operation can encode a property getter/setter as a physical
address or materialize a temporary to satisfy a physical-domain mode. The closed physical-storage producers are a
stored root/field or vector projection,
`CoreBuiltinPhysicalProjection` with its checked application,
`CoreRegisteredPhysicalProjection` with its validated application,
initialization/allocation storage, and one of the `CoreDereference` alternatives. Generic
`Primitive` cannot manufacture physical storage. Each `LookupSubtypeWitness` in the semantic witness key
becomes exactly one Core `LookupWitness` and remains one operation through initial IR lowering.

`CoreBuiltinPhysicalProjection.runtimeOperands` has exactly the two-role domain of `inputShapes`
and `evaluationOrder`; each value has its stored shape and is the result of the corresponding
elaborated operand. Its identity, operation, output proof, and control proof are byte-identical to
the typed application. `output.storage.path` is
`BuiltinElement(output.inputStorage.path, identity)`. This is the only Core producer for that path
alternative; `CorePhysicalPlace` cannot reconstruct a dynamic index from its path. The closed Core
physical-place provenance relation resolves the base `CoreValueId` to exactly
`output.inputStorage`; matching only its `CorePhysicalPlaceShape` is insufficient. Neither the node
nor any transitive static proof field contains `NodeId<Typed>`, `TypedExpr`, or an index-recovery
recipe.

`CoreRegisteredPhysicalProjection.runtimeOperands` has exactly the domain of `inputShapes` and
`evaluationOrder`; each value has the stored shape and is the result of the corresponding bound
operand plan from `ELB-PLC-002`. Its identity, registration, output proof, and control proof are
byte-identical to the typed application. `output.storage.path` is
`RegisteredPhysicalProjection(identity)`. This is the only Core producer for that path alternative;
an `IRLookup`, data opcode, or reconstructed resource path cannot substitute for it.

`ELB-CORE-008`: `SpecializeWitness(generic, specialization, inputs)` consumes a
`GenericInterfaceWitness` value. `inputs` contains exactly the runtime generic variables and
constraint slots of that generic witness's binder in canonical order, with the same Core shape law
as call inputs. Its witness operands are materialized from the specialization evidence plus the
stage-frozen resolution sidecar; the semantic spine alone is not treated as an SSA operand list.
The result classifier is the total concrete specialization of the generic classifier.

`ELB-CORE-009`: `CorePhysicalPlace(valueType, storage)` has
`RuntimeCoreValueShape(valueType, PhysicalPlace(shape))`, where `shape` is the exact projection of
`storage`'s access, mutability, address space, lifetime, alias, and source provenance. A
`CoreAddressOfPhysicalStorage` operand has that shape for the stored
`DirectStorageHandleProof.storage`. Every reference producer result uses its stored
`ReferenceHandleValueShape` to form
`RuntimeCoreValueShape(result.type, ReferenceHandleValue(result.handle))`, preserving the non-type
provenance fields. A direct/registered producer projects that shape from its admitted handle proof;
an accessor producer takes it directly from `proof.result`.
`CoreAccessorReferenceResult` consumes the exact handle-shaped normal result of the call named by
`proof.normalResult`. The proof's subject/signature equal that Core call, its contract is replayed
against the exact `CoreCapturedSourceBinding` values and call-operand projections, and its
derivation yields `proof.result`. `callResultType` and `resultEquality` prove that same result type.
No transitive field contains an AST node or typed captured source. The
wrapper produces the identical
handle-shaped value without a second runtime evaluation or a same-type reclassification.
Registered direct/transform operands and
results equal their application's endpoints. For a direct application,
`storageProof.storage = storage`, `operandType = storage.valueType`, the separate place operand is
that storage, and the output is the stored handle proof. For a transform, the separate handle
operand has `application.input` and the result has `application.output` exactly.
`CoreDereference` has one handle-shaped operand and one physical-place result equal to its
`DereferencedStorageProof.output`; builtin and registered alternatives are never interchangeable.
The proof's `identity` and `DereferencedReference(identity)` path are preserved in Core, while the
executable handle is the alternative's `CoreValueId`. For a registered alternative,
`application.identity = application.output.identity`; Core validation rejects a proof or
application copied from another dereference even when both endpoint shapes are equal.
Projecting the typed registered application to `CoreRegisteredDereferenceApplication` removes
`input.operand`, the site assignment, selection state, semantic-use edges, and origins only after
validation; it retains
the byte-identical identity, registration, `input.handle`, output proof, and control proof. Thus no
transitive static dereference field contains the typed handle node; the Core operand is its only
executable authority.

## Frontend IR contract

`FrontendIRFragment` separates symbol declarations from definitions. Lowering is a pure query over
Core AST and imported semantic interfaces. Fragments are merged by declaring every stable symbol in
canonical order first, then attaching definitions; mutual recursion and generated forward
references therefore never depend on fragment completion order.

```text
IRSymbolKind = FunctionSymbol | TypeSymbol | GlobalSymbol | ConformanceSymbol

IRSymbolOwner =
    DeclarationSymbolOwner(CanonicalDeclRef)
  | ConformanceSymbolOwner(ConformanceId)
  | SynthesizedSymbolOwner(SynthesizedSemanticId)
  | ExportedSymbolOwner(ExportedId)

IRSymbolRole =
    PrimarySymbol
  | WitnessRuntimeEntrySymbol(WitnessRuntimeEntryKey)
  | RegisteredSymbolRole(stableName: QualifiedName, inputs: CanonicalArguments)

IRSymbolDiscriminator =
    FunctionSymbolSignature(CallableSignatureId)
  | TypeSymbolType(TypeId)
  | GlobalSymbolType(TypeId)
  | ConformanceSymbolIdentity(ConformanceId)

IRSymbolKey = {
    owner: IRSymbolOwner,
    role: IRSymbolRole,
    discriminator: IRSymbolDiscriminator
}

IRSymbolId = ContentId<IRSymbolKey>

IRPhysicalStorageShape = {
    valueType: TypeId,
    access: AccessMode,
    mutability: Mutability,
    addressSpace: PhysicalStorageAddressSpace,
    lifetime: LifetimeId,
    alias: AliasProvenance,
    sourceProvenance: PhysicalStorageSourceProvenance
}

IRTemporaryStorageShape = {
    identity: TemporaryStorageIdentity,
    valueType: TypeId,
    lifetime: LifetimeId,
    alias: AliasProvenance
}

effectiveIRStorageAccess(s) =
    s.access                              when s.mutability = Mutable
    remove(Write, s.access)               when s.mutability = Immutable
    remove(Write, s.access)               when s.mutability = UnknownMutability

abiFormalStorageMutability(mode) =
    Mutable                               when mode.access = ReadWriteAccess
    UnknownMutability                     when mode.access = ReadAccess

IRValueShape =
    RuntimeValueShape(TypeId)
  | ReferenceHandleIRValueShape(shape: ReferenceHandleValueShape)
  | PhysicalStorageValueShape(shape: IRPhysicalStorageShape)
  | TemporaryStorageValueShape(shape: IRTemporaryStorageShape)
  | InitializationTargetShape(target: InitializationTargetSlot)
  | GenericMetadataShape(variable: CanonicalBoundVariable,
                         sort: GenericParameterSort)
  | InterfaceWitnessShape(classifier: InterfaceWitnessClassifier)
  | WitnessEntryShape(key: SomeWitnessEntryKey)
  | OtherConstraintEvidenceShape(kind: ConstraintKind)
  | ErrorValueShape(type: TypeId, error: ErrorId)

FunctionAbiInputRole =
    InitializationTargetAbiInput
  | ReceiverAbiInput
  | ParameterAbiInput(parameter: ParameterKey)
  | GenericAbiInput(variable: CanonicalBoundVariable)
  | WitnessAbiInput(slot: CanonicalConstraintSlot)

AbiReferenceHandleAddressSpaceSelection = {
    formal: AddressSpace,
    requirement: AddressSpaceRequirement,
    proof: AddressSpaceAdmissionProof
}

AbiPhysicalStorageAddressSpaceSelection = {
    formal: PhysicalStorageAddressSpace,
    requirement: AddressSpaceRequirement,
    proof: AddressSpaceAdmissionProof
}

AbiAddressSpaceSelection =
    ReferenceHandleAddressSpaceSelection(AbiReferenceHandleAddressSpaceSelection)
  | PhysicalStorageAddressSpaceSelection(AbiPhysicalStorageAddressSpaceSelection)

FunctionAbiContext = {
    activationLifetime: LifetimeId,
    addressSpaces: NodeMap<FunctionAbiInputRole, AbiAddressSpaceSelection>
}

AbiPhysicalStorageInputContract = {
    mode: PassingMode,
    parameterLocation: ParameterPhysicalLocationRequirement,
    formalEntry: PhysicalFormalEntryProofId,
    formalRequirement: PhysicalStorageRequirement,
    formalStorage: PhysicalStorageRef,
    formalShape: IRPhysicalStorageShape,
    formalProof: PhysicalStorageProof
}

AbiReferenceHandleMutabilityPolicy =
    AccessDerivedHandleMutability
  | DeclaredHandleMutability(Mutability)

accessDerivedHandleMutability(ReadAccess) = UnknownMutability
accessDerivedHandleMutability(ReadWriteAccess) = Mutable

AbiReferenceHandleLifetimePolicy =
    FormalActivationHandleLifetime
  | DeclaredHandleLifetime(LifetimeId)

AbiReferenceHandleAliasPolicy =
    ConservativeUnknownHandleAlias
  | DeclaredHandleAlias(AliasProvenance)

AbiReferenceHandleSourceProvenancePolicy =
    ConservativeUnknownHandleSourceProvenance
  | DeclaredHandleSourceProvenance(PhysicalStorageSourceProvenance)

abiFormalHandleSourceProvenance(ConservativeUnknownHandleSourceProvenance) = {}
abiFormalHandleSourceProvenance(DeclaredHandleSourceProvenance(facts)) = facts

AbiReferenceHandleInputContract = {
    valueType: TypeId,
    typeProjection: ReferenceHandleTypeProjection,
    kind: ReferenceHandleKind,
    referent: TypeId,
    addressSpace: AddressSpaceRequirement,
    access: AccessMode,
    mutability: AbiReferenceHandleMutabilityPolicy,
    lifetime: AbiReferenceHandleLifetimePolicy,
    alias: AbiReferenceHandleAliasPolicy,
    sourceProvenance: AbiReferenceHandleSourceProvenancePolicy
}

AbiFixedReferenceHandleResultContract = {
    formalShape: ReferenceHandleValueShape
}

AbiAccessorReferenceHandleResultContract = {
    resultType: TypeId,
    contract: AccessorReferenceResultContractId
}

AbiRegisteredReferenceHandleResultContract = {
    resultType: TypeId,
    registration: ReferenceOperationRegistration,
    staticInputs: CanonicalArguments,
    environment: StandardEnvironmentId
}

AbiReferenceHandleResultContract =
    FixedReferenceHandleResult(AbiFixedReferenceHandleResultContract)
  | AccessorReferenceHandleResult(AbiAccessorReferenceHandleResultContract)
  | RegisteredReferenceHandleResult(AbiRegisteredReferenceHandleResultContract)

FunctionAbiInputShape =
    RuntimeAbiInput(type: TypeId, mode: PassingMode)
  | ReferenceHandleAbiInput(contract: AbiReferenceHandleInputContract,
                            mode: PassingMode)
  | PhysicalStorageAbiInput(contract: AbiPhysicalStorageInputContract)
  | InitializationTargetAbiInputShape(target: InitializationTargetSlot)
  | GenericMetadataAbiInput(sort: GenericParameterSort)
  | InterfaceWitnessAbiInput(target: InterfaceSubtypeTarget)
  | OtherConstraintEvidenceAbiInput(kind: ConstraintKind)

FunctionAbiInput = {
    ordinal: UInt32,
    shape: FunctionAbiInputShape
}

FunctionAbiResultRole = NormalAbiResult | ErrorAbiResult

FunctionAbiResultShape =
    RuntimeAbiResult(type: TypeId)
  | ReferenceHandleAbiResult(contract: AbiReferenceHandleResultContract)

FunctionAbiResult = {
    ordinal: UInt32,
    shape: FunctionAbiResultShape
}

FunctionAbiMap = {
    signature: CallableSignatureId,
    resultAuthority: CallableResultAuthorityId,
    context: FunctionAbiContext,
    inputs: CanonicallyOrderedMap<FunctionAbiInputRole, FunctionAbiInput>,
    results: CanonicallyOrderedMap<FunctionAbiResultRole, FunctionAbiResult>
}

FunctionAbiMapId = ContentId<FunctionAbiMap>

ActivationBindingDerivation =
    OrdinaryCallActivation
  | RegisteredCallActivation(StandardEnvironmentRuleId)

ActivationBindingProof = {
    signature: CallableSignatureId,
    formalActivation: LifetimeId,
    callerInvocationExtent: LifetimeId,
    derivation: ActivationBindingDerivation
}

AbiAddressSpaceSubstitution = NodeMap<CanonicalBoundVariable, AddressSpace>

PhysicalStorageAddressSpaceEqualityProof = {
    left: PhysicalStorageAddressSpace,
    right: PhysicalStorageAddressSpace
}

AbiReferenceHandleAddressSpaceBindingProof = {
    role: FunctionAbiInputRole,
    formal: AddressSpace,
    actual: AddressSpace,
    substitution: AbiAddressSpaceSubstitution,
    substitutedFormal: AddressSpace,
    equality: AddressSpaceEqualityProof,
    admission: AddressSpaceAdmissionProof
}

AbiPhysicalStorageAddressSpaceBindingProof = {
    role: FunctionAbiInputRole,
    formal: PhysicalStorageAddressSpace,
    actual: PhysicalStorageAddressSpace,
    substitution: AbiAddressSpaceSubstitution,
    substitutedFormal: PhysicalStorageAddressSpace,
    equality: PhysicalStorageAddressSpaceEqualityProof,
    admission: AddressSpaceAdmissionProof
}

AbiAddressSpaceBindingProof =
    ReferenceHandleAddressSpaceBinding(AbiReferenceHandleAddressSpaceBindingProof)
  | PhysicalStorageAddressSpaceBinding(AbiPhysicalStorageAddressSpaceBindingProof)

AbiAliasViewProof =
    PreserveAliasView(AliasProvenanceEqualityProof)
  | ForgetAliasToUnknown(actual: AliasProvenance)

AbiMutabilityViewProof =
    PreserveMutabilityView(MutabilityEqualityProof)
  | ReadOnlyViewOfMutable
  | ForgetMutabilityToUnknown(actual: Mutability)

AbiReferenceHandleSourceProvenanceViewProof = {
    actual: PhysicalStorageSourceProvenance,
    formal: PhysicalStorageSourceProvenance,
    inclusion: CanonicalSetInclusionProof<PhysicalStorageSourceFact>
}

AbiReferenceHandleInputAdmissionProof = {
    contract: AbiReferenceHandleInputContract,
    actual: ReferenceHandleValueShape,
    instantiatedFormal: ReferenceHandleValueShape,
    typeEquality: TypeEqualityProofId,
    referentEquality: TypeEqualityProofId,
    addressSpaceBinding: AbiReferenceHandleAddressSpaceBindingProof,
    accessProof: AccessProvisionProof,
    lifetimeProof: OutlivesProof,
    mutabilityView: AbiMutabilityViewProof,
    aliasView: AbiAliasViewProof,
    sourceProvenanceView: AbiReferenceHandleSourceProvenanceViewProof
}

AbiPhysicalStorageInputAdmissionProof = {
    contract: AbiPhysicalStorageInputContract,
    actualStorage: PhysicalStorageRef,
    actual: IRPhysicalStorageShape,
    instantiatedFormal: IRPhysicalStorageShape,
    mode: PassingMode,
    identity: PhysicalStorageIdentityProof,
    addressSpaceBinding: AbiPhysicalStorageAddressSpaceBindingProof,
    accessProof: AccessProvisionProof,
    lifetimeProof: OutlivesProof,
    mutabilityView: AbiMutabilityViewProof,
    aliasView: AbiAliasViewProof,
    sourceProof: PhysicalStorageSourceAdmissionProof
}

AbiInputAdmissionProof =
    RuntimeInputAdmission(type: TypeId, mode: PassingMode)
  | ReferenceHandleInputAdmission(AbiReferenceHandleInputAdmissionProof)
  | PhysicalStorageInputAdmission(AbiPhysicalStorageInputAdmissionProof)
  | InitializationTargetInputAdmission(InitializationTargetSlot)
  | GenericMetadataInputAdmission(variable: CanonicalBoundVariable)
  | InterfaceWitnessInputAdmission(InterfaceSubtypeTarget)
  | OtherConstraintEvidenceInputAdmission(ConstraintKind)

AbiCallOperandProjection = {
    inputRole: FunctionAbiInputRole,
    operand: IRValueId,
    expansion: ExpansionPath
}

AbiCapturedSourceBinding = {
    capturedValue: IRValueId,
    projections: NodeList<AbiCallOperandProjection>
}

AbiFixedReferenceResultInstantiation = {
    contract: AbiFixedReferenceHandleResultContract,
    result: ReferenceHandleValueShape
}

AbiAccessorReferenceResultInstantiation = {
    contract: AbiAccessorReferenceHandleResultContract,
    invocationIdentity: AccessorInvocationIdentity,
    sources: CanonicallyOrderedMap<AccessorProvenanceSourceRole,
                                   AbiCapturedSourceBinding>,
    derivation: AccessorReferenceResultDerivation,
    result: ReferenceHandleValueShape
}

AbiRegisteredReferenceResultInstantiation = {
    contract: AbiRegisteredReferenceHandleResultContract,
    result: ReferenceHandleValueShape,
    derivation: RegisteredReferenceResultDerivation
}

AbiResultInstantiationProof =
    RuntimeResultInstantiation(type: TypeId)
  | FixedReferenceResultInstantiation(AbiFixedReferenceResultInstantiation)
  | AccessorReferenceResultInstantiation(AbiAccessorReferenceResultInstantiation)
  | RegisteredReferenceResultInstantiation(AbiRegisteredReferenceResultInstantiation)

AbiInstantiatedResult = {
    formal: FunctionAbiResultShape,
    shape: IRValueShape,
    proof: AbiResultInstantiationProof
}

AbiCallInstantiation = {
    abi: FunctionAbiMapId,
    activation: ActivationBindingProof,
    addressSpaces:
        NodeMap<FunctionAbiInputRole, AbiAddressSpaceBindingProof>,
    inputAdmissions:
        NodeMap<FunctionAbiInputRole, AbiInputAdmissionProof>,
    aliasCompatibility: CompatibleCallAliasClaims,
    subject: IRCallableContractSubjectEvidence,
    results:
        CanonicallyOrderedMap<FunctionAbiResultRole, AbiInstantiatedResult>
}

AbiCallInstantiationId = ContentId<AbiCallInstantiation>

AbiResultContractProof =
    RuntimeResultContractProof(type: TypeId)
  | FixedReferenceResultContractProof(AbiFixedReferenceHandleResultContract)
  | AccessorReferenceResultContractProof(
        contract: AbiAccessorReferenceHandleResultContract,
        derivation: AccessorReferenceResultDerivation)
  | RegisteredReferenceResultContractProof(
        contract: AbiRegisteredReferenceHandleResultContract,
        derivation: RegisteredReferenceResultDerivation)

instantiateAbiReferenceHandleInput(
    contract: AbiReferenceHandleInputContract,
    role: FunctionAbiInputRole,
    call: AbiCallInstantiation)
    -> ReferenceHandleValueShape

formalAbiReferenceHandleInput(
    contract: AbiReferenceHandleInputContract,
    role: FunctionAbiInputRole,
    context: FunctionAbiContext)
    -> ReferenceHandleValueShape

admitAbiInput(actual: IRValueShape,
              role: FunctionAbiInputRole,
              formal: FunctionAbiInputShape,
              call: AbiCallInstantiation)
    -> Option<AbiInputAdmissionProof>

proveAbiDefinitionResult(actual: IRValueShape,
                         role: FunctionAbiResultRole,
                         formal: FunctionAbiResultShape,
                         formalInputs: NodeMap<FunctionAbiInputRole, IRValueId>)
    -> Option<AbiResultContractProof>

IRFunctionDeclarationShape = {
    signature: CallableSignatureId,
    resultAuthority: CallableResultAuthorityId,
    contract: EffectiveCallableContractId,
    abi: FunctionAbiMap
}

IRTypeDeclarationShape = {
    type: TypeId,
    definition: ContentId<SemanticValue>
}

IRGlobalDeclarationShape = {
    type: TypeId,
    mutability: Mutability,
    addressSpace: AddressSpace
}

IRConformanceDeclarationShape = {
    definition: ValidatedConformanceRef,
    classifier: ConformanceClassifier,
    metadataEntries: CanonicallyOrderedSet<SomeWitnessEntryKey>,
    runtimeSlots: CanonicallyOrderedMap<WitnessRuntimeEntryKey, UInt32>
}

IRDeclarationShape =
    FunctionDeclarationShape(IRFunctionDeclarationShape)
  | TypeDeclarationShape(IRTypeDeclarationShape)
  | GlobalDeclarationShape(IRGlobalDeclarationShape)
  | ConformanceDeclarationShape(IRConformanceDeclarationShape)

IRDeclarationShapeId = ContentId<IRDeclarationShape>

IRSymbolDeclaration = {
    symbol: IRSymbolId,
    key: IRSymbolKey,
    shape: IRDeclarationShape,
    origin: Origin
}

IRSymbolLinkage =
    LocalModule(ModuleStableId)
  | ImportedInterface(ModuleInterfaceContentId)

IRSymbolRef = {
    symbol: IRSymbolId,
    expectedShape: IRDeclarationShapeId,
    linkage: IRSymbolLinkage
}

IRStaticData<T> = {
    id: ContentId<T>,
    value: T
}

IRCapabilityUseRequirement =
    IRDirectCapabilityRequirement(CapabilityRequirement)
  | IRLocalCallableCapabilityRequirement(CanonicalDeclRef)
  | IRImportedCallableCapabilityRequirement(CapabilityRequirement)
  | IRWitnessEntryCapabilityRequirement(witness: InterfaceSubtypeWitnessId,
                                        entry: WitnessRuntimeEntryKey)

IRCapabilityUse = {
    key: CapabilityUseKey,
    requirement: IRCapabilityUseRequirement,
    reason: DirectOperation | TypeUse | DeclUse | WitnessUse |
            AttributeUse | EntryPointStage
}

IRCapabilitySelection = {
    region: BooleanCapabilityPredicate,
    inferredCapabilityUses:
        CanonicallyOrderedMap<CapabilityUseId, IRCapabilityUse>,
    useWitnessDependencies:
        CanonicallyOrderedMap<CapabilityUseId, WitnessResolutionStamp>,
    concreteSourceWitnessDependencies:
        CanonicallyOrderedMap<ConcreteAvailabilityId, WitnessResolutionStamp>,
    concreteAvailability: ConcreteAvailabilitySelection
}

IRCapabilitySelectionProjectionRule = CanonicalCapabilitySelectionProjection

IRCapabilitySelectionProjectionProof = {
    source: ContentId<CapabilitySelection>,
    projected: ContentId<IRCapabilitySelection>,
    rule: IRCapabilitySelectionProjectionRule
}

IRCallSemanticMetadata = {
    capabilities: IRCapabilitySelection,
    projection: IRCapabilitySelectionProjectionProof
}

ProjectCapabilitySelectionToIR(selection: CapabilitySelection)
    -> CheckResult<IRCallSemanticMetadata>

IRReferenceHandleShape = ReferenceHandleValueShape

IRReferenceEndpointShape =
    IRReferenceHandleEndpoint(IRReferenceHandleShape)
  | IRPhysicalStorageEndpoint(IRPhysicalStorageShape)

IRRegisteredReferenceApplicationSite =
    DirectReferenceProducerSite
  | AccessorResultTransformSite
  | ReferenceDereferenceSite

IRRegisteredReferenceApplication = {
    registration: ReferenceOperationRegistration,
    site: IRRegisteredReferenceApplicationSite,
    input: IRReferenceEndpointShape,
    output: IRReferenceEndpointShape,
    control: ReferenceDataOperationControlShape
}

IRAddressOfDescriptor = {
    input: IRPhysicalStorageShape,
    output: IRReferenceHandleShape,
    proof: DirectStorageHandleProof
}

IRCallableContractSubjectEvidence =
    DirectIRContractSubject(
        declaration: CanonicalDeclRef,
        target: IRSymbolRef)
  | WitnessIRContractSubject(
        witness: InterfaceSubtypeWitnessId,
        entry: WitnessRuntimeEntryKey,
        witnessOperand: IRValueId,
        resolutions: WitnessResolutionStamp)
  | DynamicIRContractSubject(owner: TypeId, slot: DynamicDispatchKey)
  | ClosureIRContractSubject(invoke: CanonicalDeclRef, target: IRSymbolRef)
  | BuiltinIRContractSubject(rule: RuleId, operands: CanonicalArguments)

RegisteredReferenceResultDerivation = {
    registration: ReferenceOperationRegistration,
    environment: StandardEnvironmentId,
    staticInputs: CanonicalArguments,
    runtimeInputs: NodeList<IRValueId>,
    result: ReferenceHandleValueShape
}

IRCallNormalResultIdentity = {
    producer: IRInstId,
    role: FunctionAbiResultRole,
    ordinal: UInt32,
    instantiation: AbiCallInstantiationId
}

LoweredAccessorReferenceResultCertificate = {
    normalResult: IRCallNormalResultIdentity,
    contract: AccessorReferenceResultContractId,
    invocationIdentity: AccessorInvocationIdentity,
    subject: IRCallableContractSubjectEvidence,
    signature: CallableSignatureId,
    expectedReferent: TypeId,
    referentEquality: TypeEqualityProofId,
    sources: CanonicallyOrderedMap<AccessorProvenanceSourceRole,
                                   AbiCapturedSourceBinding>,
    derivation: AccessorReferenceResultDerivation,
    result: ReferenceHandleValueShape
}

IRDereferenceDescriptor = {
    identity: DereferenceApplicationIdentity,
    input: IRReferenceHandleShape,
    resultProof: DereferencedStorageProof,
    output: IRPhysicalStorageShape
}

IRRegisteredDereferenceApplication = {
    operation: IRRegisteredReferenceApplication,
    projection: IRDereferenceDescriptor
}

IRBuiltinPhysicalProjectionDescriptor = {
    identity: BuiltinPhysicalProjectionIdentity,
    operation: BuiltinPhysicalProjectionOperation,
    inputShapes:
        CanonicallyOrderedMap<BuiltinPhysicalProjectionOperandRole, IRValueShape>,
    evaluationOrder: NodeList<BuiltinPhysicalProjectionOperandRole>,
    resultProof: BuiltinPhysicalProjectionResultProof,
    output: IRPhysicalStorageShape,
    control: BuiltinPhysicalProjectionControlProof
}

IRRegisteredPhysicalProjectionDescriptor = {
    identity: RegisteredPhysicalProjectionIdentity,
    registration: RegisteredDataOperationRegistration,
    inputShapes:
        CanonicallyOrderedMap<RegisteredPhysicalProjectionOperandRole, IRValueShape>,
    evaluationOrder: NodeList<RegisteredPhysicalProjectionOperandRole>,
    resultProof: RegisteredPhysicalProjectionResultProof,
    output: IRPhysicalStorageShape,
    control: RegisteredPhysicalProjectionControlProof
}

IRReferenceOperation =
    AddressOfOperation(descriptor: IRStaticData<IRAddressOfDescriptor>)
  | AccessorReferenceResultOperation(
        certificate: IRStaticData<LoweredAccessorReferenceResultCertificate>)
  | RegisteredReferenceProducerOperation(
        application: IRStaticData<IRRegisteredReferenceApplication>)
  | ReferenceDereferenceOperation(
        descriptor: IRStaticData<IRDereferenceDescriptor>)
  | PointerDereferenceOperation(
        descriptor: IRStaticData<IRDereferenceDescriptor>)
  | RegisteredReferenceDereferenceOperation(
        application: IRStaticData<IRRegisteredDereferenceApplication>)

IRPhysicalStorageOperation =
    BuiltinPhysicalProjectionStorageOperation(
        descriptor: IRStaticData<IRBuiltinPhysicalProjectionDescriptor>)
  | RegisteredPhysicalProjectionOperation(
        descriptor: IRStaticData<IRRegisteredPhysicalProjectionDescriptor>)

IRTemporaryInitializationDescriptor = {
    storage: IRTemporaryStorageShape,
    application: TemporaryInitializationPlanApplicationAt<Published>,
    effects: EffectSet
}

IRTemporaryDestructionDescriptor = {
    storage: IRTemporaryStorageShape,
    plan: DestructionPlanAt<Published>,
    effects: EffectSet,
    nonThrowing: NonThrowingDestructionProof
}

IRAccessOperation =
    MaterializeTemporaryOperation(
        descriptor: IRStaticData<IRTemporaryStorageShape>)
  | InitializeTemporaryOperation(
        descriptor: IRStaticData<IRTemporaryInitializationDescriptor>)
  | DestroyTemporaryOperation(
        descriptor: IRStaticData<IRTemporaryDestructionDescriptor>)

IRBlockKey = {
    definition: IRSymbolId,
    ordinal: UInt32
}

IRBlockId = ContentId<IRBlockKey>

IRInstKey = {
    block: IRBlockId,
    ordinal: UInt32
}

IRInstId = ContentId<IRInstKey>

IRValueKey =
    BlockParameterValue(block: IRBlockId, ordinal: UInt32, shape: IRValueShape)
  | InstructionResultValue(instruction: IRInstId, ordinal: UInt32,
                           shape: IRValueShape)

IRValueId = ContentId<IRValueKey>

IRBlockParameter = {
    value: IRValueId,
    shape: IRValueShape
}

IRSuccessor = {
    block: IRBlockId,
    arguments: NodeList<IRValueId>
}

CallDispatchPrefixLayout =
    NoDispatchPrefix
  | WitnessDispatchPrefix(shape: InterfaceWitnessClassifier)

IROperation =
    DataOperation(opcode: StandardEnvironmentRuleId, immediates: CanonicalArguments)
  | InitializationOperation(instruction: IRInitializationInstruction)
  | AccessOperation(instruction: IRAccessOperation)
  | PhysicalStorageOperation(instruction: IRPhysicalStorageOperation)
  | ReferenceOperation(instruction: IRReferenceOperation)
  | DirectCallOperation(target: IRSymbolRef, abi: FunctionAbiMapId,
                        instantiation: IRStaticData<AbiCallInstantiation>,
                        semantics: IRStaticData<IRCallSemanticMetadata>)
  | WitnessTableReferenceOperation(table: IRSymbolRef)
  | SpecializeWitnessOperation(specialization: CanonicalSpecializationSpine)
  | LookupWitnessOperation(key: SubtypeWitnessLookupKey)
  | LookupWitnessEntryOperation(key: SomeWitnessEntryKey)
  | ExtractExistentialWitnessOperation(interface: InterfaceInstanceKey)
  | SelectDerivativeOperation(mode: DifferentiationMode,
                               provider: IRDerivativeProviderDescriptor,
                               signature: DerivativeSignatureMapId,
                               layout: IRDerivativeSelectionOperandLayout)
  | StopGradientOperation(boundary: StopGradientBoundaryId)
  | WitnessCallOperation(entry: WitnessRuntimeEntryKey, abi: FunctionAbiMapId,
                         instantiation: IRStaticData<AbiCallInstantiation>,
                         semantics: IRStaticData<IRCallSemanticMetadata>)
  | DynamicCallOperation(owner: TypeId, slot: DynamicDispatchKey,
                         abi: FunctionAbiMapId,
                         instantiation: IRStaticData<AbiCallInstantiation>,
                         semantics: IRStaticData<IRCallSemanticMetadata>)
  | ClosureCallOperation(invoke: IRSymbolRef, abi: FunctionAbiMapId,
                         instantiation: IRStaticData<AbiCallInstantiation>,
                         semantics: IRStaticData<IRCallSemanticMetadata>)
  | PrimitiveCallOperation(rule: RuleId, registration: StandardEnvironmentRuleId,
                            staticInputs: CanonicalArguments, abi: FunctionAbiMapId,
                            instantiation: IRStaticData<AbiCallInstantiation>,
                            semantics: IRStaticData<IRCallSemanticMetadata>)
  | BranchOperation
  | ConditionalBranchOperation
  | SwitchOperation(cases: CanonicallyOrderedMap<ConstValue, UInt32>,
                    defaultSuccessor: UInt32)
  | ReturnOperation
  | ThrowOperation
  | UnreachableOperation
  | IRErrorOperation(ErrorId)

IRInstruction = {
    id: IRInstId,
    key: IRInstKey,
    operation: IROperation,
    operands: NodeList<IRValueId>,
    results: NodeList<IRValueShape>,
    successors: NodeList<IRSuccessor>
}

IRBlock = {
    id: IRBlockId,
    key: IRBlockKey,
    parameters: NodeList<IRBlockParameter>,
    instructions: NonEmpty<IRInstruction>
}

IRControlFlowGraph = {
    entry: IRBlockId,
    blocks: NodeMap<IRBlockId, IRBlock>,
    blockOrder: NodeList<IRBlockId>
}

IRFunctionDefinitionBody = {
    abi: FunctionAbiMapId,
    graph: IRControlFlowGraph
}

IRGlobalDefinitionBody = {
    initializer: IRControlFlowGraph
}

IRConformanceDefinitionBody = {
    definition: ValidatedConformanceRef,
    metadataEntries:
        CanonicallyOrderedMap<SomeWitnessEntryKey, ContentId<SemanticValue>>,
    runtimeEntries:
        CanonicallyOrderedMap<WitnessRuntimeEntryKey, IRSymbolRef>
}

IRDefinitionBody =
    FunctionDefinitionBody(IRFunctionDefinitionBody)
  | GlobalDefinitionBody(IRGlobalDefinitionBody)
  | ConformanceDefinitionBody(IRConformanceDefinitionBody)

IRDefinition = {
    symbol: IRSymbolId,
    declaredShape: IRDeclarationShapeId,
    body: IRDefinitionBody
}

IRDependencyKey =
    TypeDependency(TypeId)
  | ContractDependency(EffectiveCallableContractId)
  | DeclarationDependency(CanonicalDeclRef)
  | ConformanceDependency(ValidatedConformanceRef)
  | InitializationPlanDependency(InitializationPlanId)
  | LanguageRuleSetDependency(LanguageRuleSetId)
  | ModuleDependency(ModuleInterfaceContentId)
  | StandardRuleDependency(StandardEnvironmentRuleId)

IRDependency = {
    key: IRDependencyKey,
    origins: OriginSet
}

FrontendIRFragment = {
    owner: DeclId,
    declarations: CanonicallyOrderedMap<IRSymbolId, IRSymbolDeclaration>,
    definitions: CanonicallyOrderedMap<IRSymbolId, IRDefinition>,
    references: CanonicallyOrderedSet<IRSymbolRef>,
    sourceMap: NodeMap<IRInstId, Origin>,
    requirements: CanonicallyOrderedMap<IRDependencyKey, IRDependency>
}
```

Chapter 15 defines `IRInitializationInstruction`, its closed operation alternatives, and its
semantic-role-to-operand layout. It is embedded here so initialization participates in the same SSA,
dependency, and result-shape validation as every other frontend-IR instruction. The IR sum contains
only successful executable alternatives; recovered initialization follows `IR-005` instead.

`IR-VAL-001`: A Core ordinary runtime rvalue lowers to `RuntimeValueShape(type)`. A Core
`ReferenceHandleValue(handle)` lowers to
`ReferenceHandleIRValueShape(ReferenceHandleValueShape(type, handle))`, and a Core
`PhysicalPlace(CorePhysicalPlaceShape)` lowers to
`PhysicalStorageValueShape(IRPhysicalStorageShape)` with the outer runtime type as `valueType` and
identical access, mutability, physical address space, lifetime, alias, and source provenance.
Physical parameter forwarding therefore remains symbolic; only first-class handle formation
consumes a separate `ConcreteAddressSpaceProjectionProof`. Generic metadata, interface
witnesses, witness entries, and other constraint evidence lower respectively to
`GenericMetadataShape(variable, variable.sort)`, `InterfaceWitnessShape`, `WitnessEntryShape`, and
`OtherConstraintEvidenceShape(slot.kind)`. The enclosing ABI/input role retains the complete
variable or constraint-slot key. A Core value cannot be reclassified among ordinary runtime data,
reference-handle provenance, physical storage, metadata, or evidence (or between evidence kinds)
merely because a target ABI uses the same machine representation.

`IR-ID-001`: Symbol, shape, block, instruction, value, and static-data IDs are the typed `ContentId`
of their complete keys. A declaration's map key equals `symbol`, `symbol = ContentId(key)`, and
`kindOf(key.discriminator)` equals the shape alternative. Function signatures, type/global types,
and conformance identities in the discriminator equal their corresponding shape fields; a type
shape's definition resolves to the canonical semantic definition of that exact type. A block's map
key, stored ID, and key agree; every block key names the containing definition, and its key ordinal
equals its index in `blockOrder`. An instruction's ID/key agree and its ordinal equals its index in
its block. A block-parameter or instruction-result value ID contains the exact producer, ordinal,
and shape found at that producer. A definition map key equals `definition.symbol`, and a
requirement map key equals `requirement.key`. No identity depends on allocation, pointer, worker,
or hash-map iteration order.

An `IRStaticData<T>` value satisfies `id = ContentId(value)`. Its schema is the closed type `T` at
the use site; it is immutable, canonically serializable data and cannot contain an AST node,
`CallableValue`, stage-specific resolution sidecar, scheduler handle, or host pointer. Symbol-bearing
semantic values are lowered separately to `IRSymbolRef` and may not be hidden inside static data.
A `WitnessResolutionStamp` stored by an IR schema is the frozen stage-free dependency stamp, not a
`WitnessResolutionSetAt<Construction>` or an executable AST-side wrapper.

`IR-RES-001`: Each local `IRSymbolRef` resolves to exactly one declaration in the merged local
module; each imported reference resolves to exactly one export in its named immutable module
interface. The resolved symbol ID and `ContentId(declaration.shape)` equal the reference's fields.
Two declarations of one symbol must be byte-identical or merging fails, and an imported symbol
cannot acquire a local definition. Every definition resolves one declaration, its
`declaredShape` matches, and its body alternative matches the declaration shape. Type declaration
shapes are complete and therefore have no separate `IRDefinition`.

`IR-RES-002`: A function body stores `ContentId(declaration.functionShape.abi)` and every block key
names that function symbol. Its entry block parameters, in ordinal order, are exactly the ABI
inputs after this shape projection: runtime input becomes `RuntimeValueShape(type)`, a
`ReferenceHandleAbiInput(contract, _)` becomes
`ReferenceHandleIRValueShape(formalAbiReferenceHandleInput(contract, role, abi.context))`, a
`PhysicalStorageAbiInput(contract)` becomes
`PhysicalStorageValueShape(contract.formalShape)`, generic input becomes
`GenericMetadataShape(role.variable, shape.sort)`, an initialization target becomes
`InitializationTargetShape(shape.target)`, and an interface-witness input becomes
`InterfaceWitnessShape(ConcreteInterfaceWitness(shape.target))`, and other constraint evidence becomes
`OtherConstraintEvidenceShape(shape.kind)`. The `WitnessAbiInput(slot)` role retains the canonical
constraint slot independently of the endpoint-shaped value. A global initializer has no entry
parameters and every normal
return supplies one runtime value of the declared global type. A conformance body is validated by
`IR-CON-001`. These endpoint checks prevent a structurally valid body from being attached to the
wrong declaration.

`IR-SSA-001`: `blockOrder` is a duplicate-free bijection onto `blocks`, starts with `entry`, and is
the deterministic structured-lowering order. Every block ends in exactly one control operation;
ordinary/data/storage/reference/call operations have no successors, `BranchOperation` has one,
`ConditionalBranchOperation` has two, and return/throw/unreachable have none. A switch has a
nonempty successor list; every case/default index is in range and every successor is selected by a
case or the default. Successor argument count and shapes equal the destination block parameters.
Every operand resolves in the same definition and is dominated by its block parameter or producing
instruction; same-block instruction uses are strictly after the producer. Instruction results,
block parameters, and symbol references occupy separate ID domains and cannot be interchanged.

`IR-SSA-002`: The standard-environment schema for a `DataOperation` or primitive rule declares its
operand roles, result shapes, immediate schema, effects, and whether it is valid in frontend IR.
An `InitializationOperation` instead uses chapter 15's closed alternative and validated operand
layout; its plan ID resolves the exact endpoint mappings, operation-qualified orders, target,
entry/required-subobject/exit proof, allocation ownership, transfer, and all-exit cleanup contract.
Every physical-storage operand/result uses `PhysicalStorageValueShape` and retains its exact value
type, access, mutability, address space, lifetime, alias, and source provenance.
Call operations use the referenced `FunctionAbiMap`, their stored `AbiCallInstantiation`, and one
`IRCallSemanticMetadata` value satisfying `IR-CALL-002`; no other operation may carry call-semantic
metadata.
`instantiation.abi` equals the operation's ABI ID, its activation and address-space bindings
validate under `IR-ABI-003`, and direct, dynamic, closure, and primitive call operands are ordered
by ABI ordinal. Each operand must produce a successful `admitAbiInput` proof for its role and formal
shape under that exact call instantiation. A witness call has
`WitnessDispatchPrefix(concreteClassifier)` at operand zero followed by those same ABI inputs at
indices `1 + ordinal`. Instruction result ordinal and shape equal the corresponding
`instantiation.results` entry; a formal result contract is never used as if it were a concrete SSA
shape. Return and throw operands instead require a successful `proveAbiDefinitionResult` for the
containing function's normal and error result contracts and formal entry inputs. This validates the
body against its reusable declaration contract without importing a caller invocation lifetime.
`IRErrorOperation` is accepted only under
`IR-005` and its result shapes retain the originating `ErrorId`.

`IR-REF-001`: Every `IRReferenceOperation` has no successors. Address-of has exactly one
`PhysicalStorageValueShape(descriptor.input)` operand and one
`ReferenceHandleIRValueShape(descriptor.output)` result; `descriptor.proof.storage` projects to the
input, `descriptor.proof.handle` projects to the output, and its access, mutability, lifetime,
concrete address-space projection, alias, and source-provenance relations all validate.
`AccessorReferenceResultOperation` has one
`ReferenceHandleIRValueShape(certificate.result)` operand and one result of that identical shape.
Builtin reference/pointer dereference has one
`ReferenceHandleIRValueShape(descriptor.input)` operand and one
`PhysicalStorageValueShape(descriptor.output)` result;
`descriptor.output.addressSpace = ConcretePhysicalAddressSpace(descriptor.input.handle.addressSpace)`
and its source provenance is the proof-preserving projection of the handle. A registered producer has one physical input
at `DirectReferenceProducerSite` or one reference-handle input at
`AccessorResultTransformSite`, and one reference-handle result. A registered dereference has one
reference-handle input, one physical result, and
`application.operation.site = ReferenceDereferenceSite`; its projection descriptor supplies those
same endpoints and the exact result proof. Operand/result counts or endpoint shapes that differ
from either static descriptor are invalid IR.

`IR-REF-002`: Projecting a checked registered application first constructs its closed stage-free
Core application, then projects that value to `IRRegisteredReferenceApplication`. The Core
boundary removes typed node IDs, diagnostic origins, semantic-use edges, and selection proofs only
after those facts have been validated and consumed. It preserves the
exact registration/environment/static inputs, operation site, runtime endpoint shapes, and
unary/nonthrowing control shape. For direct and transform producers, the separate Core place/handle
operand equals the checked `input.operand` elaboration and the Core application's stored endpoint
proofs equal the checked input/output; an equal-shaped replacement is not that projection. The
resulting `IRStaticData` contains no AST reference. Address-of
and builtin dereference descriptors similarly retain the complete handle and physical-storage
shapes needed to replay their endpoint equations. A dereference descriptor additionally retains
the stage-free physical-projection identity and complete `DereferencedStorageProof`; its executable
handle remains the instruction operand, not a path payload. A registered dereference packages that
descriptor with the projected registered operation rather than erasing either proof. The Typed-to-
Core boundary has already projected an `AccessorReferenceResultCertificate` to the stage-free
`CoreAccessorReferenceResultProof`, after validating its exact typed call, subject, signature,
referent, result shape, source set, and instantiation proof. IR lowering projects that Core proof
together with the already emitted call to `LoweredAccessorReferenceResultCertificate`: the exact producer instruction
and normal-result ordinal, the producer's `AbiCallInstantiationId`, stage-free callable-subject
evidence, declaration-stable accessor-role-to-producer-operand bindings and pack projections, the
stage-free `AccessorInvocationIdentity`, referent equality, five component derivations, and the
complete result shape. Typed node IDs, typed
source expressions, origins, semantic-use
edges, and stage-specific resolution sidecars are removed. The projection contains no AST reference
and is replayable using only the frozen IR graph and semantic/standard-environment dependencies.

`IR-REF-003`: Generic `DataOperation` never produces `PhysicalStorageValueShape`. The closed IR
producers of that shape are storage declarations/projections, initialization or allocation storage,
`PhysicalStorageOperation.BuiltinPhysicalProjectionStorageOperation`,
`PhysicalStorageOperation.RegisteredPhysicalProjectionOperation`, and the three dereference
alternatives. A registered
physical projection's descriptor validates all input shapes and its exact output against the
`RegisteredPhysicalProjectionResultProof` from `TYP-PLC-003`/`TYP-PLC-010`; sharing a target opcode with an
ordinary data operation cannot bypass this alternative.

`IR-PLC-001`: Initial lowering maps each `CoreRegisteredPhysicalProjection` one-to-one to
`RegisteredPhysicalProjectionOperation`. The instruction operands are the Core
`runtimeOperands[role]` lowered in `evaluationOrder`; the descriptor's `inputShapes` has exactly
that role domain, and each operand shape equals its named entry. Descriptor identity, registration
(including `StandardEnvironmentId` and static inputs), evaluation order, result proof, and control
proof are copied from Core. `resultProof.identity = descriptor.identity`,
`resultProof.registration = descriptor.registration`, and its storage path is
`RegisteredPhysicalProjection(identity)`. Projecting that storage yields exactly
`descriptor.output`, the instruction's sole `PhysicalStorageValueShape` result. The result proof's
type equality and access/mutability/lifetime/address-space/alias/source-provenance derivations replay against the
descriptor's named runtime endpoints and registered schema without an AST node or ambient target
lookup. A later use-specific `PhysicalStorageProof` is not serialized as part of the producer.

`IR-PLC-002`: Initial lowering maps each `CoreBuiltinPhysicalProjection` one-to-one to
`BuiltinPhysicalProjectionStorageOperation`. Its two instruction operands are the Core base and
index values lowered in the stored evaluation order, and the descriptor's `inputShapes` has exactly
those two roles with their exact shapes. Identity, operation, order, result proof, and control proof
are copied from Core. `resultProof.identity = descriptor.identity`, its input storage is the
physical storage obtained from the base operand by the closed IR physical-place provenance
relation, not merely an equal `IRPhysicalStorageShape`, and its path is
`BuiltinElement(resultProof.inputStorage.path, descriptor.identity)`. Projecting the result storage
yields exactly `descriptor.output`, the instruction's sole `PhysicalStorageValueShape` result.
Validation replays the named builtin rule against the two runtime endpoints without an AST node,
origin, or reconstructed index. The descriptor and every transitive `IRStaticData` field are
stage-free. A generic data operation or registered physical projection cannot
substitute for this producer.

`IR-REF-004`: Initial lowering maps `CoreAddressOfPhysicalStorage` one-to-one to
`AddressOfOperation`, `CoreAccessorReferenceResult` to `AccessorReferenceResultOperation`, and
registered direct and handle-transform producers to
`RegisteredReferenceProducerOperation` with their distinct site, builtin reference/pointer
dereferences to the corresponding distinct IR alternative, and registered dereference to
`RegisteredReferenceDereferenceOperation`. Every dereference descriptor copies the Core proof's
identity and complete proof; its output path is `DereferencedReference(identity)`, its input shape
is the projection of that proof's handle, and its output shape is the projection of the proof's
storage. The registered alternative additionally requires
`application.operation.input/output` to equal the projection descriptor's endpoints and packages
the exact stage-free `CoreRegisteredDereferenceApplication` registration, input/output proof, and
control shape rather than reconstructing them. Lowering does not fuse adjacent
accessor-call, transform, or dereference instructions, and it never reconstructs a registration,
endpoint, or stable identity from a runtime type or `IRInstId`.

`IR-REF-005`: For `AccessorReferenceResultOperation(certificate)`, let `c = certificate.value`.
`c.normalResult.role = NormalAbiResult`; its producer resolves to a call operation whose stored
instantiation has `id = c.normalResult.instantiation`, and its ABI maps `NormalAbiResult` to
`c.normalResult.ordinal`. The operation's sole operand is exactly
`InstructionResultValue(c.normalResult.producer, c.normalResult.ordinal,
ReferenceHandleIRValueShape(c.result))`; it cannot be a block parameter, copy, sibling call result,
or arbitrary equal-shaped value. The wrapper's one result has that identical shape.

The producer ABI signature equals `c.signature`, and `c.subject` is byte-identical to the
producer instantiation's subject evidence. A witness subject repeats the exact
`InterfaceSubtypeWitnessId`, runtime-entry key, witness SSA operand, and frozen resolution evidence;
matching only the selected method symbol is insufficient. The producer's instantiated normal
result is `AccessorReferenceResultInstantiation(i)` with `i.contract.contract = c.contract`,
`i.invocationIdentity = c.invocationIdentity`, `i.sources = c.sources`,
`i.derivation = c.derivation`, and `i.result = c.result`.
For every declaration-stable `AccessorProvenanceSourceRole`, `capturedValue` is the exact lowered
capture producer reached by resolving the invocation's formal-to-captured projection before AST
identities are erased. Each stored projection's `operand` equals the producer call operand selected
by its `inputRole` and canonical expansion path. The source-map domain is exactly the formal
receiver/parameter roles read by the contract; no `SourceArgumentId` survives in IR.

Resolving `c.contract` yields `c.signature`, its declared referent, and the five component rules;
`c.referentEquality` has that referent and `c.expectedReferent` as its non-recovery endpoints.
Replaying those rules against the exact captured SSA values and projections in `c.sources` yields
the address space, mutability, lifetime, alias, and source provenance recorded in `c.derivation`, and combining them
with the contract's result type, kind, referent, and access yields exactly `c.result`. No validation
step consults a typed AST node. The wrapper therefore preserves a proof-carrying result already
created by the call; it never creates provenance by reclassification.
For `FreshAccessorAlias`,
`c.derivation.alias.invocationIdentity = Some(c.invocationIdentity)`, and replay derives the exact
`AccessorInvocationAliasRegion(c.invocationIdentity)`. For every other alias rule the field is
`None`. An IR producer ID is never
used as a replacement seed, so moving or deduplicating instructions cannot change alias identity.

`IR-TMP-001`: `MaterializeTemporaryOperation(d)` has no operands and one
`TemporaryStorageValueShape(d)` result representing raw plan-owned storage. Its nominal
`TemporaryStorageIdentity` is copied from the authenticated application site and its alias is
exactly `ExactAliasRoot(temporaryStorageAliasRoot(d.identity))`; no Core/IR instruction identity or
raw `StableSemanticId` may replace it.
`InitializeTemporaryOperation(i)` is the normal-checkpoint marker for the exact chapter 15
application in `i.application`: it has that temporary as its sole operand and no result, and is
dominated by the complete lowered initialization operations. Every exceptional exit before the
marker executes the application's stored cleanup and cannot reach outer destruction. Before the
marker, the raw temporary value may be used only as that initialization plan's target or
exceptional-cleanup storage; the marker must dominate whole-object write-back and destruction.
`i.effects` is copied from the published initialization plan rather than reconstructed from the
value type. `DestroyTemporaryOperation(d)` consumes one
`TemporaryStorageValueShape(d.storage)`; `d.plan`, `d.effects`, and `d.nonThrowing` are the exact
stage-free projection of `CoreDestroyTemporary`. These operations support only named
abstract-domain `OutMode`/`InOutMode` preparation and cleanup. They cannot produce
`PhysicalStorageValueShape` and cannot occur in a `ConstRefMode` or `RefMode` call-slot plan.

`IR-PHY-001`: Lowering a physical-domain call operand preserves one
`PhysicalStorageValueShape(actual)` from the selected Core physical-place value through the call.
The corresponding `PhysicalStorageInputAdmission` is at the same ABI role and has
`admission.mode` byte-identical to the signature mode. Its identity proof, access proof, lifetime
proof, address-space binding, source-provenance proof, mutability view, and alias view replay the
exact stage-free `CorePhysicalParameterInputProof`, which was validated as the projection of the
selected `PhysicalParameterBindingProofAt<Published>` before stage-specific source syntax was
erased. `admission.actualStorage` is that Core proof's complete endpoint and projects to
`admission.actual`, so the source proof and nominal place path are not reconstructed from an IR
shape. Its `PhysicalStorageSourceAdmissionProof.provenanceProof` is the byte-identical generic
`PhysicalSourceProvenanceAdmissionProof` selected at checking time.
For `ConstRefMode`, the admitted view has `ReadAccess` and does not claim immutable underlying
storage; for `RefMode`, it has `ReadWriteAccess` and mutable storage. No runtime value, reference
handle, or temporary-storage result can satisfy this admission merely by sharing a `TypeId` or
machine representation.

`IR-PHY-002`: An accessor-produced physical argument retains distinct call,
`AccessorReferenceResultOperation`, optional registered handle transform, and dereference
instructions. The physical call operand is exactly the dereference instruction's
`PhysicalStorageValueShape` result, whose descriptor retains the authenticated
`DereferenceApplicationIdentity`, handle input, and `DereferencedStorageProof`. A direct physical
argument instead retains its existing physical producer. Initial lowering may not fuse either path,
substitute an equal-shaped producer, insert a load, or reconstruct the endpoint from a property
type. Thus both paths have the same physical ABI admission without erasing how the endpoint was
proved.

`IR-CALL-001`: Lowering preserves the Core call alternative exactly. `DirectCall` and
`ClosureCall` resolve their `ResolvedDeclRef.target` values to function symbol refs and consume
their frozen witness-resolution sidecars when materializing specialization evidence;
`WitnessCall` lowers
its witness value as operand zero and retains the runtime entry key;
dynamic calls retain owner and slot; primitive calls retain both their language rule and registered
standard operation. The operation's ABI map has the Core contract signature, and
`FunctionAbiMap.resultAuthority` is byte-identical to the Core contract authority and resolves to
the same callable anchor; the call-local result instantiation must select the ABI result
alternative derived from that authority kind. Core receiver,
initialization-target, parameter, residual-generic, and witness inputs are projected by ABI input
role and emitted by
ordinal. Lowering constructs exactly one call-local `AbiCallInstantiation`: its activation binds the
Core contract's `callerInvocationLifetime`, its address-space substitution is the selected call
specialization, its input admissions are the exact role-keyed proofs for the emitted operands, its
`aliasCompatibility` is byte-identical to the Core call contract, its subject evidence is the
stage-free projection of the Core dispatch, and its result entries are the
exact projection of `ElaboratedCallAt.resultProvenance`. The operation's
`instantiation.id` is `ContentId(instantiation.value)` and `instantiation.value.abi` is the
operation's ABI ID. A Core reference-handle operand remains a reference-handle operand, and every
Core operand for a mode whose domain is `PhysicalOperand(_)` remains physical storage with the
mode's exact access and location requirement; lowering may apply only the named `admitAbiInput`
view, not
reclassify an ordinary runtime value with the same `TypeId`. ABI result alternatives likewise
constrain the call-local instantiation, whose concrete result entries determine the Core/IR result
category and complete handle shape. Lowering cannot turn a
witness/dynamic/closure call into a direct call merely because one current target is known.

`IR-CALL-002`: Every call operation's `semantics` is the unique result of
`ProjectCapabilitySelectionToIR(CoreCallContract.capabilitySelection)`. Projection preserves the
region, every `CapabilityUseId`, use key/reason, and requirement, plus the concrete alternative's
exact source IDs, operational subjects, combined requirement, and availability proof. A direct or
imported requirement is copied unchanged. A local-call requirement projects its
`ResolvedDeclRefAt<Published>` to `CanonicalDeclRef`; a witness-entry requirement projects its
`WitnessCallRef<Published>` to `(InterfaceSubtypeWitnessId, WitnessRuntimeEntryKey)`. In both latter
cases `useWitnessDependencies` has exactly that use ID and its complete
`WitnessResolutionStamp`; it has no other keys. These published stamps contribute their exact
`ConformanceDependency` entries to the fragment before the stage-specific wrappers are erased.
`concreteSourceWitnessDependencies` has exactly the selected concrete source-ID domain and stores
the minimal stamp required by each source subject and its specialization/static inputs, including
an empty stamp when no witness definition is needed.
Each concrete declaration subject contributes its exact `DeclarationDependency`; a registered
subject contributes its exact `StandardRuleDependency`; and a language-rule subject contributes
its exact `LanguageRuleSetDependency`. Their source stamps add any nested conformance dependencies.
Every projected use-map key equals `ContentId(use.key)`, and the concrete alternative independently
revalidates `CAP-SEL-003` using the projected region, source set, combined requirement, and proof.

The projection proof satisfies
`source = ContentId(CoreCallContract.capabilitySelection)` and
`projected = ContentId(semantics.value.capabilities)`. Replacing each projected local/witness
requirement with the dependency stamp under its same key reconstructs byte-for-byte the published
source selection, so Core-to-IR projection is one-to-one. The metadata is immutable semantic/static
metadata: it is not a runtime operand or result, is excluded from `FunctionAbiMap` and
`AbiCallInstantiation`, and does not change executable dispatch or code shape. Lowering cannot
reconstruct it from `CoreCallContract.effective`, a flattened capability formula, or target
annotations; cannot collapse zero, one, and multiple concrete sources to an optional formula; and
cannot exchange an ordinary use for an equal concrete requirement. An invalid projection is a
lowering failure, not permission to omit the metadata.

`IR-WIT-001`: `WitnessTableReferenceOperation` has no operands, returns the declaration's
`InterfaceWitnessShape` obtained by mapping its concrete or generic conformance classifier to the
corresponding interface-witness classifier, and retains the exact definition dependency. A generic
conformance declaration therefore also materializes a generic witness value when referenced; it is
not only a symbol-definition container. Specialization consumes a `GenericInterfaceWitness` as
operand zero followed by the values from `CoreWitnessOperation.SpecializeWitness.inputs`, ordered
by the canonical binder's generic and constraint roles, and returns
`InterfaceWitnessShape(ConcreteInterfaceWitness(substitutedTarget))`.

`IR-WIT-002`: Lowering `LookupSubtypeWitness(base, key)` emits exactly one
`LookupWitnessOperation(key)` with the lowering of `base` as its sole operand and the key-derived
concrete `InterfaceWitnessShape` as its sole result. An N-key semantic lookup spine produces N operations in
the same order. Initial lowering cannot flatten, reassociate, or replace that spine with endpoint
types; later optimization may fold a lookup against a statically known table.

`IR-WIT-003`: `ExtractExistentialWitnessOperation` consumes the existential package value and
returns the requested interface-witness shape. `WitnessCallOperation` consumes an interface-witness
value as operand zero followed by the callable ABI operands. Neither operation stores an
`IRSymbolRef` as a substitute for a runtime witness value.

`IR-WIT-004`: `LookupWitnessEntryOperation(key)` consumes one concrete interface-witness value and
returns exactly `WitnessEntryShape(key)`. The dependent shape resolves the key's requirement kind:
associated types/values are metadata values, callable/constructor/accessor entries are callable
metadata, and nested conformances contain an interface witness. Consumers must use the matching
kind-indexed projection; a property/subscript bundle cannot be treated as one callable slot. A
fused `WitnessCallOperation` is permitted only for a `WitnessRuntimeEntryKey` and still consumes the
same table value and exact requirement/accessor key.

`IR-CON-001`: A conformance declaration's `definition` and its definition body carry the same
validated definition reference; its `classifier` equals that definition's concrete or generic
conformance classifier and maps to the table reference's witness classifier. The
declaration's metadata key set equals the complete active all-kind entry set of that definition;
each metadata payload resolves to the canonical kind-correct lowering of the satisfaction at the
same key. `runtimeEntries` keys equal `runtimeSlots` keys, and slot values are a bijection onto
`0 .. runtimeSlots.count-1` in canonical `WitnessRuntimeEntryKey` order. Each runtime symbol ref
resolves a function shape with the signature required by that projected entry. No metadata entry is
identified by a runtime slot.

`IR-FRG-001`: `references` is exactly the canonical set of symbol references reachable from every
instruction and definition payload. `sourceMap` has exactly one entry for every instruction ID and
no other key. Every requirement map key equals `IRDependency.key`; requirements are the exact
direct semantic/module/standard-rule inputs read by lowering, with nonempty canonically merged
origins. A local reference's module equals the fragment owner's module; an imported reference and
module dependency name the same immutable interface revision used for resolution.
Serialization follows map canonical order plus `blockOrder`, block parameter order, instruction
order, operand order, result order, and successor order, making round trips and parallel lowering
byte-identical.

`IR-DEP-001`: `IRDependencyKey` is the closed sum shown above: `TypeDependency`,
`ContractDependency`, `DeclarationDependency`, `ConformanceDependency`,
`InitializationPlanDependency`, `LanguageRuleSetDependency`, `ModuleDependency`, or
`StandardRuleDependency`.
`origins` is nonempty. Each subject resolves in the same semantic/module/standard environment used
by the fragment's lowering query; a requirement retained only from an unselected branch is invalid.
An `InitializationOperation` contributes exactly one `InitializationPlanDependency` for its stored
published plan ID, and no non-initialization instruction contributes one merely because it shares a
result type. The dependency resolves an applicable winner in the `Selected` result returned by
`ResolveInitialization`; a recovered initialization plan cannot satisfy it. A tooling
`IRErrorOperation` produced from recovery contributes no initialization-plan dependency.
When a fragment is produced inside `SynthesisConstruction`, these IR requirements do not add new
`SemanticDependency` alternatives: type, contract, initialization-plan, language-rule-set,
module-interface, and standard-rule requirements are backed by the exact producing
`QueryDependency(QueryKey)`; declaration requirements are backed by the exact
`DeclarationDependency(CanonicalDeclRef)`; and conformance requirements are backed by
`ConformanceDependency(ValidatedConformanceRef)`. The
synthesis validator resolves each
query result/direct-input selector and requires it to equal the IR dependency subject; unrelated
declaration/synthesis dependencies cannot justify an IR requirement.
Call-semantic metadata contributes exactly the conformance dependencies in its use/source witness
stamps, one declaration dependency per concrete declaration subject, one standard-rule dependency
per registered subject, and one language-rule-set dependency per language-rule subject.
Deleting a source or stamp cannot leave its dependency as dead justification, and deleting a
dependency cannot leave otherwise valid-looking metadata publishable.

A `SynthesisGroup` allocates all semantic and IR symbol identities before any generated body is
lowered, so recursive generated functions and witness entries use ordinary forward symbol refs.

`IR-001`: Initial IR preserves checked function structure. Receiver and parameter passing modes are
lowered by one documented ABI-independent mapping; later target ABI passes may transform it.

`IR-002`: Generic parameters, witness parameters, and all-kind witness-entry keys are emitted from
keyed binders/maps in canonical order. Expanded source parameters use `ParameterKey(source,
expansionPath)` in the logical-to-IR map. Semantic/metadata entries are addressed by
`SomeWitnessEntryKey` (the existential form of `WitnessEntryKey<K>`), never dictionary or
declaration position. Only callable, constructor, and property/subscript accessor ABI slots use the
`WitnessRuntimeEntryKey` projection.

`IR-003`: Type lowering consumes canonical `Type` values. It cannot query declaration parents to
reconstruct `Self`, parameter direction, or generic substitutions omitted from a type.

`IR-004`: A conformance lowers in two steps: allocate the IR witness-table identity, then emit each
all-kind keyed entry. Recursive references use the allocated identity; associated type/value and
nested-conformance metadata retain `SomeWitnessEntryKey`, while runtime callable slots retain the
derived `WitnessRuntimeEntryKey`. Missing entries are a Core validation error, not a null IR
operand.

`IR-005`: Lowering a recovered Core error, including chapter 15's
`RecoveryCoreInitialization(error)`, produces a typed `IRError` placeholder only in
diagnostic/tooling mode. It is not wrapped in `InitializationOperation` and contributes no
`InitializationPlanDependency`. A module containing such placeholders is not publishable as
successful code generation.

## Function-type lowering

The logical function type remains richer than a target ABI type:

```text
lowerLogicalFunctionType(CallableSignature, EffectiveCallableContract) = {
    optional explicit initialization target from CallablePurpose,
    optional explicit receiver parameter from ReceiverSlot,
    ordinary parameters lowered according to PassingMode and semantic value shape,
    explicit generic/witness parameters where not specialized,
    proof-carrying logical result and error shapes,
    effect/capability decorations from EffectiveCallableContract
}
```

The lowering records the `FunctionAbiMap` defined above. Calls consume the same map.

`IR-ABI-001`: Resolving `FunctionAbiMap.signature` yields one receiver role exactly when the
signature has a receiver, one initialization-target role exactly when its purpose is
`InitializerCallable`, and one parameter role for every `ParameterSlot.key`.
`FunctionAbiMap.resultAuthority` is copied byte-for-byte from the callable header; resolving it
yields that declaration/registered anchor and the same signature. A map builder never takes an
authority override and never infers one from `results`.

```text
context.activationLifetime =
    ContentId(CallableActivationLifetime(FunctionAbiMap.signature))
```

This is the reusable callee-activation variable. A caller lexical lifetime, call-node ID, scheduler
identity, or observed invocation extent is forbidden in `FunctionAbiMap`. The
`context.addressSpaces` domain is exactly the physical-storage and reference-handle input roles
whose formal contract has an address-space requirement. Each selection is made from the
target-specialized ABI environment, has `selection.requirement` equal to that formal requirement,
and validates its stored admission proof. A reference-handle selection's admission yields
`ConcretePhysicalAddressSpace(selection.formal)`; a physical-storage selection may retain a
`FormalPhysicalAddressSpace` unchanged. A call operand never chooses or mutates the declaration
map.

A receiver or parameter whose mode has `PhysicalOperand(location)` has only
`PhysicalStorageAbiInput(contract)`. `contract.mode` is the complete signature mode,
`contract.parameterLocation = location`, and
`contract.formalRequirement = instantiatePhysicalStorageRequirement(contract.mode,
context.activationLifetime)`. `contract.formalEntry` names the same signature and ABI role and
selects the nominal `ConstRefFormalRoot` when `mode.access = ReadAccess` or `RefFormalRoot` when
`mode.access = ReadWriteAccess`. `contract.formalStorage` has that root, the parameter value type,
the mode's exact access, `CallableActivationLifetime(signature)`, the entry's formal address space
and source facts, and `UnknownAliasRoot`; its mutability is `UnknownMutability` for `ConstRefMode`
and `Mutable` for `RefMode`, exactly `abiFormalStorageMutability(contract.mode)`.
`contract.formalProof` proves the complete formal requirement, and
`contract.formalShape` is its exact IR projection, retaining the nominal formal address space.

The access axis does not change the storage domain: both modes receive a physical formal root and
both callers supply `PhysicalStorageValueShape`. The constref body may load/project/pass its
read-only physical view but cannot store through it or upgrade it to `RefMode`; the ref body retains
read/write access. A physical mode encoded as `RuntimeAbiInput`, `ReferenceHandleAbiInput`, or
temporary storage is invalid even if target ABI lowering later uses the same machine pointer
representation. Conversely, `InMode`, `OutMode`, and `InOutMode` never become physical modes merely
because one actual happens to be stored in memory.

An abstract-domain formal whose structural value type is `ReferenceType` or `PointerType` uses
`ReferenceHandleAbiInput(contract, mode)`. The contract's value type, type projection, handle kind,
referent, address-space requirement, and access are derived from that structural type. A reference
type's declared lifetime selects `DeclaredHandleLifetime`; a pointer without an explicit semantic
lifetime selects `FormalActivationHandleLifetime`. In the absence of an explicit checked
provenance declaration, mutability is `AccessDerivedHandleMutability` and alias is
`ConservativeUnknownHandleAlias`, while source provenance is
`ConservativeUnknownHandleSourceProvenance`. The latter maps deliberately to the empty proven-fact
set; it is not permission for the callee body to infer facts from the referent type, address space,
or caller operand. Instantiation computes
`accessDerivedHandleMutability(ReadAccess) = UnknownMutability`, never `Immutable`, and
`accessDerivedHandleMutability(ReadWriteAccess) = Mutable`; access and underlying mutability remain
orthogonal. `formalAbiReferenceHandleInput` gives the formal handle exactly
`abiFormalHandleSourceProvenance(contract.sourceProvenance)`, and
`instantiateAbiReferenceHandleInput` substitutes every canonical argument in those facts under the
call specialization without adding facts. Only a language/standard rule recorded in the checked
formal may select a `DeclaredHandleMutability`, `DeclaredHandleLifetime`, `DeclaredHandleAlias`, or
`DeclaredHandleSourceProvenance`; every declared source fact retains its exact registered rule,
static inputs, and the standard environment selected by the callable's effective contract, and all
policy endpoints must agree with the type projection. The declared-source alternative is canonical
only for a nonempty fact set; an empty set uses
`ConservativeUnknownHandleSourceProvenance`. The ABI contract never stores a call-produced
`ReferenceHandleProof`, and body entry
cannot replace the formal policy with provenance observed at one caller.

Other abstract-domain runtime values use `RuntimeAbiInput(type, mode)`. All alternatives repeat the
exact mode and logical type from the signature. The initialization target repeats its complete
target slot.
Residual generic variables and required constraint evidence contribute their keyed roles; a closed
specialization contributes neither. A `Conforms` slot has
`InterfaceWitnessAbiInput(targetOf(slot))`; other evidence uses
`OtherConstraintEvidenceAbiInput(slot.kind)`. Input ordinals are a bijection onto
`0 .. inputs.count-1` in initialization-target, receiver, parameter-slot, residual-generic, then
canonical-constraint order.

`IR-ABI-002`: The result map always has `NormalAbiResult` at ordinal zero and has
`ErrorAbiResult` at ordinal one exactly when the error type is not `NeverType`. The checked callable
result authority in `FunctionAbiMap.resultAuthority`, not the result type's machine representation,
chooses the closed alternative.
An ordinary authority gives `RuntimeAbiResult(type)`. A fixed reference authority gives
`FixedReferenceHandleResult` with its complete reusable formal shape. A ref-accessor authority gives
`AccessorReferenceHandleResult` naming the exact `AccessorReferenceResultContractId`, signature,
and result type. A registered authority gives `RegisteredReferenceHandleResult` with the exact
registration, static inputs, semantic environment, and result type. No result contract contains a
caller SSA value or caller invocation lifetime, and physical storage is not a function-result
alternative.

Every reachable body `return`/`throw` proves its actual value against the selected formal result
contract using `proveAbiDefinitionResult` and the function's formal entry inputs. Fixed contracts
require their exact formal shape; accessor contracts replay their five rules over the named formal
receiver/parameter sources; registered contracts replay the registered rule. A bare runtime value
cannot satisfy any reference-handle contract. The effective contract in
`IRFunctionDeclarationShape` names the same signature, and the ABI map contains that signature,
result authority, context, inputs, and results with the declaration shape's byte-identical
`resultAuthority`. Target ABI lowering may erase or indirect logical values only while preserving
this mapping explicitly.

`IR-ABI-003`: Every call constructs one `AbiCallInstantiation`. Its `abi` is the referenced map;
`activation.signature` is that map's signature, `activation.formalActivation` is exactly
`abi.context.activationLifetime`, and `activation.callerInvocationExtent` is the originating
`CoreCallContract.callerInvocationLifetime`. `ActivationBindingProof` records the permitted
substitution from the reusable activation variable to this one invocation extent; it is never
cached in the declaration map or shared merely because two callers have the same lexical scope.

The instantiation's `inputAdmissions` map has exactly the ABI input-role domain, and each proof's
closed alternative matches that role's `FunctionAbiInputShape`. The instantiation's address-space
map has exactly the ABI context's address-space roles. A reference-handle selection requires the
reference-handle binding alternative; a physical-storage selection requires the physical-storage
binding alternative. The former's admission yields
`ConcretePhysicalAddressSpace(actual)` and the latter's admission yields the stored physical
`actual` (which may be formal). Each proof
substitutes the formal address under the call's canonical specialization, proves the resulting
address equal to the actual operand address, and revalidates the formal requirement. Then
`admitAbiInput` is closed and deterministic. Runtime, initialization-target, metadata, and evidence
inputs require matching alternatives and exact endpoints. A reference-handle contract is first
instantiated from its type and provenance policies using this activation/address substitution;
admission requires equal outer type, kind, referent, and address space, sufficient access, an
actual lifetime outliving the instantiated lifetime, and allowed mutability, alias, and
source-provenance views. Its `sourceProvenanceView.actual` is exactly
`actual.handle.sourceProvenance`, its `formal` is exactly
`instantiatedFormal.handle.sourceProvenance`, and its inclusion proof has that formal set as
`subset` and the actual set as `superset`. Thus admission may forget caller facts not promised by
the reusable formal, but can neither invent a required fact nor expose caller-only facts to the
callee body.

Physical storage admission requires `mode = contract.mode`, a physical operand whose endpoint is
the exact projection of `actualStorage` from the selected call-slot binding, and an identity proof
whose type endpoints equal that binding. The originating access plan's `rankingConversion` is
exactly `Some(ConsumedWithoutAccessConversion(PhysicalParameterIdentityPassingRule))`;
`sourceAdaptationRank` therefore yields
`ConversionFreeAccessRank(PhysicalParameterIdentityPassingRule)`, whose comparison rank is
`zeroRank`. Admission validates the complete instantiated physical requirement: access,
activation or declared lifetime, address-space predicate, and source-provenance predicate. Its
`sourceProof.storage` is exactly `actualStorage`,
`sourceProof.provenanceProof.provenance = actualStorage.sourceProvenance`, and the provenance
proof's requirement is exactly the instantiated formal source requirement; ABI admission cannot
reconstruct, strengthen, or substitute source facts from the operand type or address space. Its
mutability view permits mutable underlying storage to satisfy `ConstRefMode` without declaring the
storage immutable; the admitted access remains read-only. `RefMode` requires the read/write and
mutable view. The proof stores both actual and instantiated formal shapes and preserves the actual
alias for call-alias checking. Neither an abstract place, ordinary runtime value, reference handle,
nor temporary can satisfy a physical input, regardless of equal `TypeId` or layout.
`aliasCompatibility` is then revalidated against the admitted operands' preserved alias
provenances, mode-specific access claims, and bound caller invocation extent. Only two overlapping
`SharedPhysicalRead` claims are unconditionally compatible; every overlap involving
`AliasablePhysicalAccess` replays its stored versioned rule set. Abstract exclusive claims retain
their ordinary conflict rules.

`IR-ABI-004`: `AbiCallInstantiation.results` has exactly the roles of the reusable ABI result map,
and every entry repeats its formal contract. A runtime contract instantiates to the identical
runtime type. A fixed reference contract applies the call's activation/address substitution to its
formal shape. An accessor contract records the exact captured source-role-to-call-operand
projections, replays its five component derivations, and produces one concrete
`ReferenceHandleValueShape`. For a fresh alias rule, the instantiation and its IR derivation retain
the identical stage-free `AccessorInvocationIdentity`; no call instruction identity is substituted.
A registered contract stores and validates the registered derivation
over the exact runtime operands. The instruction result at each ABI ordinal has precisely that
instantiated shape.

Call-result construction cannot attach handle provenance to ordinary data or use the reusable
formal contract as a concrete SSA value. Conversely, definition `return`/`throw` validation uses
`proveAbiDefinitionResult`, not a call-local instantiation. Any intentional result conversion is an
explicit Core/IR operation before the boundary; subsequent copies and block arguments preserve the
complete instantiated shape.

This removes the current split where some paths inspect `FuncType` mode wrappers while others
iterate `ParamDecl` modifiers.

## Lowering unit tests

Every Core node lowering test constructs canonical types and a five-to-ten-node Core fragment
directly. It supplies fakes for imported symbols and layout-independent builtin operations. Tests
assert:

- exact IR opcode and operand roles;
- logical-to-IR initialization-target/receiver/parameter/generic/witness map;
- capture-result evaluation order and multiple projections from one captured receiver/index pack;
- direct and accessor-produced `ConstRefMode`/`RefMode` operands, exact physical ABI entry proofs,
  nominal formal roots, access/mutability separation, source provenance, and call-local admissions;
- reference-handle ABI formals with default-empty and declared registered source-provenance
  policies, including substitution, inclusion admission, and rejection of body-entry invention;
- rejection of getter-only properties, wrong-access reference accessors, nonidentity conversions,
  rvalues, and temporary-backed physical arguments;
- preservation and replay of overlapping constref-read proofs and versioned ref/constref alias
  decisions from overload selection through Core and call-local ABI admission;
- abstract `OutMode`/`InOutMode` temporary initialization, write-back, and destruction cleanup on
  every selected exit, nominal site-derived temporary identity/alias preservation, and rejection of
  that storage as a physical-mode operand;
- accessor-result descriptors tied to the exact producer call rather than an equal-typed value;
- registered physical projections preserve environment/static inputs, executable base/index order,
  intrinsic output derivations, and their distinct IR storage-operation alternative;
- callable result authority is byte-identical across header, typed/elaborated/Core call,
  `FunctionAbiMap`, declaration shape, and call instantiation;
- fresh accessor aliases replay one stage-free `AccessorInvocationIdentity` rather than a typed or
  IR producer ID;
- source/provenance mapping;
- witness requirement keys;
- deterministic definition ordering;
- typed error recovery; and
- serialization round trips for the fragment.

End-to-end tests remain necessary, but no lowering behavior should require parsing a full source
module merely to reach the code under test.
