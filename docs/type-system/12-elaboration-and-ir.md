# Elaboration, synthesis, and frontend IR

Elaboration turns a typed program into an explicit program. IRReady lowering then maps that explicit
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
TypedNode     = SyntaxNode<Typed>
ElaboratedNode = SyntaxNode<Elaborated>
IRReadyNode      = SyntaxNode<IRReady>

ElaborateNode : TypedNode -> CheckResult<ElaboratedNode>
LowerNodeToIRReady : ElaboratedNode -> CheckResult<IRReadyNode>
LowerToIR     : IRReadyDecl -> CheckResult<FrontendIRFragment>
```

These aliases range over the complete registered node set at exactly one node-local form.
They are not a common mutable base class and do not erase form from `ASTNodeId<F, K>`. Expression,
statement, and declaration aliases below further restrict the registered kind through the schema's
`baseKind` chain. Consequently, only the named transformations above can change a node's form;
chapter 3's generic immutable edit API remains form-preserving. This says nothing about the form of
any other node in the semantic snapshot.

`ELB-001`: Every implicit runtime operation in a typed node becomes an explicit elaborated node.

`ELB-002`: Elaboration is deterministic and idempotent by semantic identity. Re-requesting the same
synthesis key returns the same synthesized declaration ID.

`ELB-003`: Elaboration never edits the declaration container that caused it. Generated declarations
and all semantic facts they make visible are returned in one `SynthesisGroup` and merged into the
semantic snapshot atomically.

Chapter 9 is the sole schema authority for `SynthesisKey`, output identities,
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
CallableValue<S: WitnessTableState> = {
    dispatch: CallableDispatch<S>,
    contract: CallableContractStateAt<S>
}

CallableDispatch<S: WitnessTableState> =
    Direct(ResolvedDeclRefAt<S>)
  | WitnessMethod(witness: SubtypeWitnessRef<S>, entry: RuntimeInterfaceRequirementKey)
  | DynamicSlot(owner: TypeId, slot: DynamicDispatchKey)
  | LambdaInvoke(ResolvedDeclRefAt<S>)
  | Builtin(rule: RuleId,
            operands: CanonicalArguments,
            witnessResolutions: WitnessResolutionSetAt<S>)

CallableContractStateAt<Construction> =
    Selection(contract: PreInferenceCallableContract)
  | Effective(contract: EffectiveCallableContract)
  | SelectedVariant(set: CallableVariantSetId,
                    proof: CapabilityVariantSelectionProof,
                    contract: EffectiveCallableContract)

CallableContractStateAt<Published> =
    Effective(contract: EffectiveCallableContract)
  | SelectedVariant(set: CallableVariantSetId,
                    proof: CapabilityVariantSelectionProof,
                    contract: EffectiveCallableContract)

CallableContractState = CallableContractStateAt<Published>

CallableContractSubject =
    DirectContractSubject(DeclRef)
  | WitnessContractSubject(witness: SubtypeWitnessId,
                           entry: RuntimeInterfaceRequirementKey)
  | DynamicContractSubject(owner: TypeId, slot: DynamicDispatchKey)
  | LambdaContractSubject(DeclRef)
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

TypedCallReferenceResultAuthorityAt<S: WitnessTableState> =
    FixedPointerLikeCallResult(
        authority: FixedPointerLikeResultContractId)
  | AccessorPointerLikeCallResult(
        certificate: AccessorReferenceResultCertificate)
  | RegisteredPointerLikeCallResult(
        registration: ReferenceOperationRegistration,
        staticInputs: CanonicalArguments,
        environment: StandardEnvironmentId)

TypedCallPointerLikeResultAt<S: WitnessTableState> = {
    result: PointerLikeValueShape,
    authority: TypedCallReferenceResultAuthorityAt<S>
}

TypedCallResultProvenanceAt<S: WitnessTableState> =
    OrdinaryCallResult
  | PointerLikeCallResult(TypedCallPointerLikeResultAt<S>)

TypedCallAt<S: WitnessTableState> = {
    id: AnyASTNodeId<Typed>,
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
                   FixedPointerLikeCallableResult |
                   AccessorPointerLikeCallableResult |
                   RegisteredPointerLikeCallableResult)

ResolveCallableResultAuthorityAt<S>(dispatch: CallableDispatch<S>,
                                    signature: CallableSignatureId)
    -> Result<CallableResultAuthorityId,
              CallableResultAuthorityResolutionFailure>

BuildTypedCall(id, Selected(winner, comparisons, considered), contractContext)
    -> CheckResult<TypedCall>

AccessorReferenceResultInstantiationInputAt<S: WitnessTableState> = {
    contract: AccessorReferenceResultContractId,
    invocationIdentity: AccessorInvocationIdentity,
    invocationSite: SemanticOperationSiteAssignment,
    call: AnyASTNodeId<Typed>,
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

SelectedSurfaceCallResultInputAt<S: WitnessTableState> =
    OrdinarySurfaceCallResult
  | FixedPointerLikeSurfaceCallResult(
        result: PointerLikeValueShape)
  | AccessorPointerLikeSurfaceCallResult(
        invocationIdentity: AccessorInvocationIdentity,
        invocationSite: SemanticOperationSiteAssignment,
        sources: CapturedStorageSources,
        provenanceSources: AccessorProvenanceSourceMapId,
        expectedReferent: TypeId,
        context: ExpressionCheckContextId,
        result: PointerLikeValueShape)
  | RegisteredPointerLikeSurfaceCallResult(
        result: PointerLikeValueShape)

SelectedSurfaceCallInputAt<S: WitnessTableState> = {
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
    id: AnyASTNodeId<Typed>,
    input: SelectedSurfaceCallInputAt<S>,
    contractContext: ContractSelectionContext)
    -> CheckResult<TypedCallAt<S>>

BuildConstructionTypedCall(id, ConstructionCallInput, contractContext)
    -> CheckResult<TypedCallAt<Construction>>

ElaborateTypedCallAt<S>(
    call: TypedCallAt<S>,
    sourceEnvironment: ElaboratedCallSourceEnvironmentAt<S>,
    bindings: NodeMap<BoundCallSlot, BoundStorageAccessPlan<S>>,
    completions: ContractCompletionMap)
    -> CheckResult<ElaboratedCallAt<S>>

ElaboratedReceiverAt<S: WitnessTableState> = {
    sourceType: TypeId,
    access: BoundStorageAccessPlan<S>,
    origin: Origin
}

ElaboratedCallAt<S: WitnessTableState> = {
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

ElaboratedArgumentAt<S: WitnessTableState> = {
    parameter: ParameterKey,
    access: BoundStorageAccessPlan<S>
}

ElaboratedBuiltinPhysicalProjectionOperandAt<S: WitnessTableState> = {
    source: ElaboratedExprAt<S>,
    endpointType: TypeId,
    endpointCategory: ValueCategory
}

ElaboratedBuiltinPhysicalProjectionAt<S: WitnessTableState> = {
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

ElaboratedRegisteredPhysicalProjectionOperandAt<S: WitnessTableState> = {
    source: ElaboratedExprAt<S>,
    access: BoundStorageAccessPlan<S>,
    endpointType: TypeId,
    endpointCategory: ValueCategory
}

ElaboratedRegisteredPhysicalProjectionAt<S: WitnessTableState> = {
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
        NodeMap<RegisteredPhysicalProjectionOperandRole, BoundStorageAccessPlan<S>>)
    -> CheckResult<ElaboratedRegisteredPhysicalProjectionAt<S>>

StorageAccessOperandId = { ordinal: UInt32 }
StorageAccessStepId = { ordinal: UInt32 }
StorageAccessCompletionStepId = { ordinal: UInt32 }
PhysicalStorageObligationId = { ordinal: UInt32 }
PlanValueId = { ordinal: UInt32 }
PlanPhysicalStorageId = { ordinal: UInt32 }
PlanAbstractStorageId = { ordinal: UInt32 }
TemporaryId = { ordinal: UInt32 }
ReferenceCaptureResultId = { ordinal: UInt32 }
CapturedStorageSourcesId = ContentId<CapturedStorageSources>

capturedSourceRole(CapturedStorageReceiver(_)) = StorageReceiverSource
capturedSourceRole(CapturedStorageArgument(a)) = StorageArgumentSource(a.id)

capturedSourceExpr(CapturedStorageReceiver(value)) = value
capturedSourceExpr(CapturedStorageArgument(argument)) = argument.value

ReferenceCaptureResultAt<S: WitnessTableState> = {
    id: ReferenceCaptureResultId,
    source: CapturedStorageSource,
    evaluation: ElaboratedExprAt<S>
}

ReferenceCaptureEnvironmentAt<S: WitnessTableState> = {
    sourceSet: CapturedStorageSourcesId,
    results: NodeMap<ReferenceCaptureResultId, ReferenceCaptureResultAt<S>>,
    evaluationOrder: NodeList<ReferenceCaptureResultId>
}

ElaboratedCallSourceEnvironmentAt<S: WitnessTableState> =
    IndependentCallSources
  | CapturedReferenceSources(ReferenceCaptureEnvironmentAt<S>)

StorageAccessPlan<S: WitnessTableState> = {
    operands: NodeMap<StorageAccessOperandId, StorageAccessOperand>,
    physicalStorageObligations:
        NodeMap<PhysicalStorageObligationId, PhysicalStorageObligation>,
    preparation: NodeList<StorageAccessStepRecord<S>>,
    terminal: StorageAccessPlanTerminal<S>,
    completion: NodeList<StorageAccessCompletionStepRecord<S>>,
    rankingCoercion: Option<RankedStorageCoercion>,
    lifetime: StorageAccessLifetime,
    aliasClass: AliasClass,
    semanticUses: PlanSemanticUses<S>
}

StorageAccessLifetime = {
    temporary: Option<TemporaryStorageAccessExtent>
}

TemporaryStorageAccessExtent = {
    temporary: TemporaryId,
    cleanup: CompletionCondition
}

ImmediateStorageAccessLifetime = StorageAccessLifetime(None)

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

StorageAccessOperand =
    TypedInput(node: AnyASTNodeId<Typed>, type: TypeId, category: ValueCategory)
  | AdapterInput(role: AdapterSourceRole,
                 type: TypeId,
                 category: AdapterInputCategory)

BoundStorageAccessPlan<S: WitnessTableState> = {
    recipe: StorageAccessPlan<S>,
    bindings: NodeMap<StorageAccessOperandId, ElaboratedStorageAccessOperandAt<S>>,
    physicalStorageProofs:
        NodeMap<PhysicalStorageObligationId, PhysicalStorageProof>
}

PhysicalStorageObligation =
    ConcreteStorageObligation(input: StorageAccessOperandId,
                              requirement: PhysicalStorageRequirement,
                              proof: PhysicalStorageProof)
  | AdapterStorageObligation(input: StorageAccessOperandId,
                             requirement: PhysicalStorageRequirement)

PhysicalStorageProjectionAuthority =
    RequiredPhysicalStorage(obligation: PhysicalStorageObligationId)

MaterializedTemporaryStorageAt<S: WitnessTableState> = {
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
  | PhysicalInitializationStorage(storage: PlanPhysicalStorageId)
  | AbstractInitializationStorage(storage: PlanAbstractStorageId)

ElaboratedExprAt<S: WitnessTableState> =
    an Elaborated-stage expression whose witness-bearing descendants all have stage S

ElaboratedDeclAt<S: WitnessTableState> =
    an Elaborated-stage declaration whose bodies contain only ElaboratedExprAt<S>

ElaboratedFunctionBodyAt<S: WitnessTableState> =
    an Elaborated-stage function body whose witness-bearing descendants all have stage S

ElaboratedStorageAccessOperandAt<S: WitnessTableState> =
    ValueSource(ElaboratedExprAt<S>)
  | StorageSource(StorageRef)
  | CapturedSourceProjection(result: ReferenceCaptureResultId,
                             projection: CapturedStorageProjection)

AbstractAccessorRole = Get | Set(valueParameter: ParameterKey)

AbstractAccessorInvocationAt<S: WitnessTableState> = {
    storage: AbstractStorageRef,
    role: AbstractAccessorRole,
    callable: CallableValue<S>,
    signature: CallableSignature,
    receiver: Option<PlanValueId>,
    indices: NodeMap<ParameterKey, PlanValueId>
}

Explicit reference formation does not inhabit `AbstractAccessorRole`. It owns the separate
`ReferenceAccessorPlanAt<S>` from chapter 7, so no ordinary getter/setter access recipe can be
retagged as a ref accessor.

StorageAccessStepRecord<S: WitnessTableState> = {
    id: StorageAccessStepId,
    operation: StorageAccessStepOperation<S>
}

StorageAccessStepOperation<S: WitnessTableState> =
    EvaluateOnce(input: StorageAccessOperandId, result: PlanValueId)
  | ProjectPhysicalStorage(input: StorageAccessOperandId,
                         result: PlanPhysicalStorageId,
                         authority: PhysicalStorageProjectionAuthority)
  | ProjectAbstractStorage(input: StorageAccessOperandId,
                         result: PlanAbstractStorageId)
  | ReadAbstractStorage(input: PlanAbstractStorageId,
                      invocation: AbstractAccessorInvocationAt<S>,
                      result: PlanValueId)
  | ResolveAbstractStorageThroughReference(
        input: PlanAbstractStorageId,
        plan: InternalRefStoragePlanAt<S>,
        handle: PlanValueId,
        result: PlanPhysicalStorageId)
  | ProjectPhysicalStorageThroughParameterAccessor(
        input: PlanAbstractStorageId,
        plan: ParameterReferenceAccessorPlanAt<S>,
        handle: PlanValueId,
        result: PlanPhysicalStorageId)
  | ReadPhysicalStorage(input: PlanPhysicalStorageId,
                      result: PlanValueId)
  | ApplyCoercion(input: PlanValueId, plan: ConversionPlan<S>, result: PlanValueId)
  | InitializeTemporary(storage: MaterializedTemporaryStorageAt<S>,
                        source: TemporaryInitializationSource)

RuntimeArgumentAt<S: WitnessTableState> =
    ImmediateValue(PlanValueId)
  | OutDestination(PlanPhysicalStorageId)
  | TemporaryAddress(TemporaryId)
  | PhysicalStorageArgument(
        storage: PlanPhysicalStorageId,
        binding: PhysicalParameterBindingProofAt<S>)

StorageWriteSource = ComputedValue(PlanValueId)

StorageWriteOperationAt<S: WitnessTableState> =
    WritePhysicalStorage(destination: PlanPhysicalStorageId,
                         source: StorageWriteSource,
                         conversion: ConversionPlan<S>,
                         when: CompletionCondition)
  | WriteAbstractStorage(destination: PlanAbstractStorageId,
                         invocation: AbstractAccessorInvocationAt<S>,
                         source: StorageWriteSource,
                         conversion: ConversionPlan<S>,
                         when: CompletionCondition)

StorageAccessPlanTerminal<S: WitnessTableState> =
    PassArgument(argument: RuntimeArgumentAt<S>)
  | YieldStorageRead(result: PlanValueId)
  | CompleteStorageWrite(operation: StorageWriteOperationAt<S>,
                         result: PlanValueId)

StorageAccessCompletionStepRecord<S: WitnessTableState> = {
    id: StorageAccessCompletionStepId,
    operation: StorageAccessCompletionStepOperation<S>
}

StorageAccessCompletionStepOperation<S: WitnessTableState> =
    WritePhysicalBack(destination: PlanPhysicalStorageId,
                      source: TemporaryValue(TemporaryId) | ComputedValue(PlanValueId),
                      conversion: ConversionPlan<S>,
                      when: CompletionCondition)
  | WriteAbstractBack(destination: PlanAbstractStorageId,
                      invocation: AbstractAccessorInvocationAt<S>,
                      source: TemporaryValue(TemporaryId) | ComputedValue(PlanValueId),
                      conversion: ConversionPlan<S>,
                      when: CompletionCondition)
  | DestroyTemporary(temporary: TemporaryId,
                     destruction: DestructionExecutionAt<S>,
                     when: CompletionCondition)

CompletionCondition = OnNormalCompletion | OnExceptionalCompletion | Always

StorageAccessCoercionSite = PreparationCoercion(StorageAccessStepId)
                     | TemporaryInitializationCoercion(step: StorageAccessStepId,
                                               conversion: InitializationPath)
                     | TerminalStorageWriteCoercion

RankedStorageCoercion =
    AppliedStorageCoercion(site: StorageAccessCoercionSite, rank: ConversionCost,
                    environment: ConversionEnvironmentId)
  | ConsumedWithoutStorageCoercion(rule: RuleId)
```

Plan- and call-local IDs are typed ordinals, not process addresses or global semantic identities.
Operand ordinals are dense in canonical operand-role order; preparation and completion step
ordinals are dense in serialized execution order; value, physical-storage, abstract-storage, and
temporary ordinals are dense in first-definition order within their separate domains.
Reference-capture-result ordinals are dense in the capture environment's evaluation order.
Renumbering a valid plan or environment by these rules is part of canonicalization, so
alpha-equivalent local numbering cannot create a second encoding.

`ELB-STO-001`: `ElaborateRegisteredPhysicalProjectionAt<S>` preserves the application's identity,
authenticated site assignment,
registration (including environment and static inputs), operand-role domain, evaluation order,
intrinsic output proof, and control proof byte-for-byte. In that exact order it elaborates each
stored `runtimeOperands[role].source` once and binds the unchanged access recipe to that elaborated
source, producing the corresponding `BoundStorageAccessPlan<S>`. The supplied binding map has exactly the
operand domain and each recipe equals the source application's recipe; it may discharge operands
and physical-storage obligations but cannot replace endpoint type/category or select another
conversion. Every operand recipe has a `PassArgument` terminal matching its registered runtime
endpoint; a storage read/write terminal is invalid. Selection effects/capabilities and operand-plan
semantic uses have already been contributed once during checking and are not rediscovered during
elaboration.

`ELB-STO-002`: Lowering the elaborated application executes those bound plans in
`evaluationOrder` and records the resulting `IRReadyValueId` under the same role in one
`IRReadyRegisteredPhysicalProjection`. The IRReady output is exactly
`PhysicalStorage(application.output.storage)`. No base/index is recovered from the output storage path,
and no generic IRReady primitive may manufacture that storage. Reordering operands, dropping an index,
or replacing one with an equal-typed value invalidates the application rather than changing only
presentation order. The authenticated site has already fixed and validated the nominal identity;
IRReady retains that identity but removes the site assignment and its `Origin`.

`ELB-STO-003`: `ElaborateBuiltinPhysicalProjectionAt<S>` preserves the application's identity,
authenticated site assignment, operation, operand-role domain, evaluation order, result proof, and
control proof byte-for-byte. It
elaborates the exact stored base and converted index once in that order. The base remains a
`PhysicalStorage` for `output.inputStorage`; the index remains the checked `RValue` at its endpoint
type. Semantic uses were contributed during checking and are not rediscovered. Elaboration cannot
recover either operand from `BuiltinElement`, the originating typed node, or the input storage's
type.

`ELB-STO-004`: Lowering the elaborated builtin application records both resulting `IRReadyValueId`
operands under their unchanged roles and constructs exactly one
`IRReadyBuiltinPhysicalProjection`. Its result is `PhysicalStorage(application.output.storage)`, and the
IRReady node retains the identity, operation, input shapes, result proof, and control proof needed to
replay that projection. Missing, duplicated, reordered, or equal-typed replacement operands make
lowering invalid. A builtin application cannot lower as a
`IRReadyRegisteredPhysicalProjection`, even when a target happens to use the same eventual opcode.
The IRReady boundary removes the validated site assignment and its `Origin` while retaining its
nominal identity.

`ELB-ACC-010`: `StorageAccessPlan.terminal` is the closed purpose of the recipe. A plan produced by
`PlanArgumentAccess` has exactly `PassArgument`; a plan produced by `PlanStorageAccessAt<S>` for a
request whose intent is `ReadValueAccess` has exactly `YieldStorageRead`; and a plan produced for
`WriteValueAccess(w)` has exactly `CompleteStorageWrite`. A registered physical-
projection operand also uses `PassArgument`, because it supplies one runtime operand to the
registered operation rather than performing a standalone storage access. Validators reject every
cross-purpose terminal, including a storage read represented by an `ImmediateValue` argument and a
standalone write with a dummy runtime argument.

`PassArgument` transfers its prepared argument to the enclosing call or registered operation; its
completion conditions are interpreted on that operation's normal and exceptional return edges.
`YieldStorageRead` names the result of the selected `ReadPhysicalStorage` or `ReadAbstractStorage` and
returns that prepared value from the storage-access expression; a fallback names the physical read
after its single `ResolveAbstractStorageThroughReference`.
`CompleteStorageWrite` executes its stored physical store or abstract setter and returns the named
already-evaluated source value only after that operation completes normally. Its operation's `when`
condition is interpreted against completion of the preparation phase; completion-list conditions
are interpreted against the selected terminal's outcome. Thus `OnNormalCompletion` and
`OnExceptionalCompletion` always name the immediately preceding explicit phase boundary and do not
imply that every access plan contains a call.

`ELB-ACC-011`: A physical-domain call slot has exactly one
`PassArgument(PhysicalStorageArgument(p, binding))` terminal. `binding.mode` is the slot's complete
substituted `ParamPassingMode`, whose domain is `PhysicalOperand(_)`; its access is `ReadAccess` for
`ConstRefMode` and `ReadWriteAccess` for `RefMode`. The plan has no temporary extent, conversion,
write-back, access-retention step, or cleanup step. The physical storage `p` is produced in exactly
one of two
ways. For `DirectPhysicalParameterSource`, `ProjectPhysicalStorage` discharges the stored physical
obligation for the source's existing `PhysicalStorage`. For
`AccessorProducedPhysicalParameterSource`, `ProjectAbstractStorage` is followed by exactly one
`ProjectPhysicalStorageThroughParameterAccessor` carrying the byte-identical
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
`ExclusivePhysicalAccess(ReadWriteAccess)` for `RefMode`. `UniqueAlias(FreshTemporaryAlias(t,
i))` is valid only when the same abstract-domain plan
defines temporary `t` with identity `i`, its descriptor has
`alias = ExactAliasRoot(temporaryStorageAliasRoot(i))`, and no operation publishes an alias to it.
`RegisteredUniqueAlias` replays its named standard-environment rule and exact static inputs. Every
other plan preserves selected source provenance or uses `UnknownAlias`; it cannot mint uniqueness
from access mode, result type, node identity, or container position. `aliasClassProvenance` is the
sole alias-provenance input from an access plan to `CheckCallAliasClaims`.

`ELB-ACC-001`: Every `StorageAccessOperandId` used by a preparation step or physical-storage obligation
exists in `operands`, and obligation ordinals are dense.
`ProjectPhysicalStorage(..., RequiredPhysicalStorage(o))` names one existing obligation whose input
equals the step input. A `ConcreteStorageObligation` is permitted only for a `TypedInput` already
classified as its proof's exact `PhysicalStorage`; an `AdapterStorageObligation` only for
`AdapterPhysicalStorage`. `ProjectPhysicalStorageThroughParameterAccessor` is permitted only when the
terminal binding's source is `AccessorProducedPhysicalParameterSource(source, plan)`, the preceding
`ProjectAbstractStorage` projects that exact typed `source`, and its result storage is exactly
`plan.endpoint.output.storage`. The plan's mode, access environment, and derived requirement equal
the terminal binding's corresponding fields. Each
`PlanValueId`, `PlanPhysicalStorageId`, `PlanAbstractStorageId`, and `TemporaryId` has exactly one
definition. Preparation is SSA-ordered: every value/storage use refers to an earlier definition, and
`InitializeTemporary(d, source)` defines `d.id` only at its stored initialization application's
normal checkpoint. Every terminal ID refers to a prepared value, physical storage, or initialized
temporary of the exact required alternative. A validator derives the complete def-use map; no
parallel table is serialized.

`ELB-ACC-002`: Every successfully initialized materialized temporary has exactly one
`DestroyTemporary` carrying its descriptor's byte-identical `DestructionExecutionAt<S>` on every
exit selected by its `CompletionCondition`. A failed `InitializeTemporary` executes only the
chapter 16 exceptional cleanup and never activates the outer destruction obligation.
For every descriptor `d`, `d.site = d.initialization.site`,
`d.identity = d.initialization.identity = temporaryStorageIdentity(d.site.site)`, and
`d.alias = ExactAliasRoot(temporaryStorageAliasRoot(d.identity))`. Thus neither plan ordinals nor
initialization-storage content IDs become ownership/alias identities.
`StorageAccessLifetime.temporary` has exactly the domain of the plan's initialized transport buffer;
an immediate or physical-domain plan has none. An abstract `OutMode`/`InOutMode` transport has the
exact parameter/storage value type and exists only to execute the selected abstract-storage
accessor contract; it is not a conversion temporary. Write-back reads its initialized value,
targets the selected physical or abstract storage, precedes destruction, and occurs only on normal
completion. Exceptional paths destroy any live buffer without writing the destination. Completion
order cannot use destroyed storage or a value outside its declared access lifetime. The validator
symbolically checks the terminal-relative normal and exceptional paths from `ELB-ACC-010`.

`ELB-ACC-003`: `Some(AppliedStorageCoercion(...))` selects one existing `ApplyCoercion`, a conversion at the
`InitializationPath` stored by an `InitializeTemporary` application, or a terminal
`StorageWriteOperationAt<S>` conversion, and its stored rank must equal
`rankConversion(selectedConversion, environment)`. The environment is serialized and
must equal the candidate's registered conversion environment, so deserialization can replay the
rank without ambient target or language settings.
`Some(ConsumedWithoutStorageCoercion(...))` is permitted only for a candidate-passing rule that
consumes no converted input. Every access plan installed in an overload candidate or call slot has
`Some`; `None` is permitted only when the plan is not a candidate-comparison input, including a
standalone storage read/write. Thus ranking and elaboration inspect the same conversion operation
rather than parallel plans, while a non-candidate plan carries no fabricated rank.

`ELB-ACC-004`: `BoundStorageAccessPlan.bindings` has exactly the domain of `recipe.operands`; each bound
value/storage or capture projection matches the operand's stated type and category, and an
`AdapterInput` may bind only the declared adapter role. A capture projection is checked in the
enclosing call's source environment under `ELB-ACC-007`; it is not permission to resolve the
original typed expression again. `physicalStorageProofs` has exactly the domain of
`recipe.physicalStorageObligations`. Each proof's storage is the `PhysicalStorage` bound to that
obligation's input and satisfies its requirement. For a concrete obligation it equals the proof
already selected during applicability; for an adapter obligation it discharges the pathless formal
promise when the synthesized requirement witness method input is bound. An `AdapterPhysicalStorage` endpoint promises a requirement at
least as strong, while an `AdapterAbstractStorage` can never supply a proof. Binding
substitutes leaves and discharges obligations only; it cannot alter steps, local IDs, ranking,
lifetime, or cleanup. Lowering can therefore execute a validated recipe without re-running access
or conversion selection.

`ELB-ACC-005`: `PassArgument(PhysicalStorageArgument(p, binding))` consumes only the
`PlanPhysicalStorageId` for `physicalParameterStorage(binding)`. `binding.identity` is the
conversion-free physical-storage identity proof and contains its sole type-equality proof. That
proof, `binding.instantiatedRequirement`, `binding.physicalStorage`, `binding.mode`, and
`binding.accessEnvironment` are exactly those selected for that call slot; no separately supplied
lifetime, address-space selection, source-provenance fact, equality, or conversion can replace
them. A direct source uses `ProjectPhysicalStorage(..., RequiredPhysicalStorage(o))`, whose discharged
obligation requires that exact existing `PhysicalStorage`. An accessor-produced source instead uses
`ProjectPhysicalStorageThroughParameterAccessor` and the exact access-indexed plan stored in
`binding.source`; the plan's dereference endpoint is the argument storage. No ordinary getter,
setter/write-back, temporary, or nonidentity conversion satisfies either physical mode.
`WriteAbstractBack` remains available only to the separately specified abstract `OutMode` and
`InOutMode` policies. This is the elaboration invariant corresponding to `TYP-ACC-005`,
`TYP-ACC-007`, and the chapter 8 physical-mode rules.

`ELB-ACC-008`: `ResolveAbstractStorageThroughReference` is the closed lowering hook for an ordinary
read/write fallback already selected by `PlanStorageAccessAt<S>`; it is not a physical-parameter
binding operation. Its input is the exact `AbstractStorage(plan.invocation.storage)` selected by the
stored `InternalRefStoragePlanAt<S>`. The authorization kind is `ReadThroughRefAccessor` when
followed by `ReadPhysicalStorage` and `WriteThroughRefAccessor` when its result is the destination of
a `CompleteStorageWrite(WritePhysicalStorage(...))` terminal. The stored `plan.storageProof`
satisfies that authorization's complete requirement. No terminal form changes which authorization
was selected.

Executing the step evaluates the invocation's captured sources once, performs the already selected
ref-accessor call, obtains the exact raw result and certificate stored in
`plan.invocation.rawResult`, and validates `plan.handle.raw` is byte-identical to it. The
use-specific `plan.handle.admitted` satisfies `plan.authorization.requirement` without changing the
raw shape; that admitted handle is the exact input of the stored dereference to
`plan.endpoint.output.storage`. `handle` denotes this plan-internal raw/admission pair and `result`
denotes the resulting physical storage. The handle has exactly one semantic consumer: the stored
dereference (or the registered transform followed immediately by that dereference). It cannot be
named by the plan terminal, become a `RuntimeArgumentAt<S>`, be stored, returned, captured, merged, or
escape to another operation.
The invocation's `requestContext` is the originating `StorageAccessRequestAt<S>.context`,
`plan.endpoint.output.storage.lifetime` equals that context's `evaluationLifetime`, and the stored
source-lifetime proof has the admitted handle lifetime and that exact result lifetime as endpoints.
`ReadPhysicalStorage` performs the physical load and terminal `WritePhysicalStorage` performs the
physical store; neither operation changes the original property's classifier. Thus the fallback
remains an explicit ref-accessor-call/dereference/load-or-store sequence, while the source property
remains `AbstractStorage`. It is distinct from
`ProjectPhysicalStorageThroughParameterAccessor`, which requires a
`ParameterReferenceAccessorPlanAt<S>` selected specifically for a physical-mode call and yields the
physical endpoint only to that call plan.

`ELB-ACC-009`: Applying a plan returned for `WriteValueAccess(w)` finds exactly one `TypedInput`
whose node, type, and category equal `w.source` and exactly one `EvaluateOnce` definition used as the
stored write source. Its terminal is exactly `CompleteStorageWrite(operation, sourceValue)`, where
`sourceValue` is that `EvaluateOnce` result. The selected `WritePhysicalStorage` or
`WriteAbstractStorage` operation has `source = ComputedValue(sourceValue)`,
`conversion = w.conversion`, and `when = w.completion`; a ref-accessor fallback first executes its
single `ResolveAbstractStorageThroughReference` and then uses the same `WritePhysicalStorage`
equation. The
conversion endpoints equal the source value type and destination `storageValueType`, its semantic uses
occur exactly once in the plan union, and `rankingCoercion` is `Some` naming that stored
conversion exactly when it participates in ranking and otherwise `None`. No parameter-mode
temporary/write-back or independently reconstructed
right-hand side may satisfy this rule.

`ELB-ACC-006`: `StorageAccessPlan.semanticUses` is the exact canonical union of every
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

`ELB-ACC-007`: `IndependentCallSources` permits only `ValueSource` and `StorageSource` bindings. For
`CapturedReferenceSources(environment)`, `environment.evaluationOrder` is a duplicate-free
bijection onto `environment.results`, and `environment.sourceSet` resolves the exact
`CapturedStorageSources` from which it was built. Result IDs are dense in that source set's
evaluation order, every map key equals the stored ID, and
`capturedSourceRole(result.source)` selects the byte-identical entry in `sourceSet.captures` at that
position. `result.evaluation` is the stage-correct elaboration of
`capturedSourceExpr(result.source)` and its required `Origin` points to that exact typed expression;
this relation, not equal type/category, authorizes the capture. The evaluation remains an explicit
`ElaboratedExprAt<S>` even when its classifier is a storage, so lowering has one executable producer
rather than only a semantic `StorageRef`.
`CapturedSourceProjection(result, projection)` is valid only in this environment; the result
exists, `projection.source = capturedSourceRole(result.source)`, and projecting
`projection.expansion` from the evaluation's derived classifier yields exactly the bound
`StorageAccessOperand` type and category. No separately stored result category may disagree. An empty pack
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
`IRReadyAddressOfPhysicalStorage` alternative. The latter proof retains the exact
`ConcreteAddressSpaceProjectionProof` from the possibly symbolic physical address space to the
handle's concrete address space, plus the complete source-provenance equality. A
`RegisteredDirectReferenceApplication` instead emits
`IRReadyRegisteredDirectReference`; its exact standard-environment registration, physical input,
handle output, unary/nonthrowing control proof, and runtime operand are retained. The IRReady
application stores `input.operandType`, `input.storage`, and `input.proof` in its corresponding
stage-free fields, while the elaborated physical value becomes the separate `storage` operand.
Selection state, semantic-use edges, and `input.operand` are consumed rather than copied. Neither
form uses
generic IRReady `Primitive`, and lowering never chooses an operation from syntax or operand type.
Semantic-use edges have already entered the caller's inference graph and are not contributed a
second time during elaboration.

`ELB-REF-002`: Elaborating `ExplicitAccessorReference` constructs one
`ReferenceCaptureEnvironmentAt<S>` with
`sourceSet = ContentId(plan.invocation.sources)`: it elaborates and
evaluates every exact stored source expression once in
`plan.invocation.sources.evaluationOrder`, assigns the resulting value/storage the dense
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
receiver/parameter role to the captured projection validated under `TYP-STO-009`. Before
completion, validation requires
`call.resultAuthority = accessorResultAuthority(plan.invocation.declared)` and exactly
the following provenance; deserialization rechecks the same equation:

```text
call.resultProvenance = PointerLikeCallResult({
    result = plan.invocation.rawResult.result,
    authority = AccessorPointerLikeCallResult(
        plan.invocation.rawResult.certificate)
})
```

On normal completion,
the `CallRegion` result has
`PointerLikeValue(plan.invocation.rawResult.result.handle)` under that certificate; this is the
inner accessor call's raw result provenance, not a type-based classification or a use-specific
storage requirement. Then
`IRReadyAccessorReferenceResult(callResult, irReadyProof)` validates the checked certificate and projects
it before crossing the IRReady boundary. `irReadyProof.normalResult = callResult`; its contract,
invocation identity, subject, signature, expected referent, equalities, result, and component-rule
derivation equal the checked certificate. Every typed captured source is replaced by the exact
`IRReadyValueId` produced by the capture environment, and every formal-to-source projection becomes a
`IRReadyCallOperandProjection` naming the corresponding IRReady call operand and expansion path. Neither
`AccessorHandleResultProof`, `AccessorReferenceResultCertificate`, `CapturedStorageSources`, nor a
`AnyASTNodeId<Typed>` is retained transitively. The wrapper preserves the already handle-shaped normal
result without re-executing or reclassifying it.
`InvokeReferenceAccessor` returns that wrapper under its stored `AccessorHandleAdmissionProof`;
`InvokeReferenceAccessorThenRegistered` feeds the wrapper to one `IRReadyRegisteredHandleTransform`.
The transform's stage-free IRReady application retains registration, input/output handle proofs, and
control proof, while the exact wrapper becomes its separate `handle` operand. It drops the typed
`input.operand`, selection state, and semantic-use edges only after validating them. The optional
data operation therefore carries its validated application rather than a bare rule tag.

`ELB-REF-003`: A typed `CheckedDereferenceAt<S>` emits `IRReadyReferenceDereference`,
`IRReadyPointerDereference`, or `IRReadyRegisteredReferenceDereference` according to its stored closed
operation. Its `DereferencedStorageProof` supplies the complete physical result type, access,
mutability, address space, lifetime, alias provenance, and source relation. The result lifetime is
exactly `resolve(checked.context).evaluationLifetime`, and its source-lifetime proof has the input
handle lifetime and that exact result lifetime as endpoints. No pass derives that shape from the
operand type or original property. The proof identity equals `checked.identity`, its path is
`DereferencedReference(checked.identity)`, and the exact elaborated handle becomes the IRReady operand;
`checked.identity = dereferenceApplicationIdentity(checked.site.site)`, and the authenticated site
assignment and typed operand node are not copied into IRReady. A registered dereference is not
erased to a generic IRReady `Primitive` or an unproved registered-data instruction.

`ELB-REF-004`: The accessor call, optional registered reference operation, and explicit dereference
remain distinct ordered operations. Lowering cannot fuse an abstract property's reference accessor
into a physical call operand or treat the handle result itself as a storage. For an explicit
reference expression, only the separately checked dereference creates a physical storage. For a
physical-parameter plan, `ProjectPhysicalStorageThroughParameterAccessor` retains the same ordered
call/optional-transform/dereference sequence and passes only its proven endpoint through
`PhysicalStorageArgument`. In neither case does the original property's classifier change from
`AbstractStorage`.

`ElaboratedCall`, `ElaboratedReceiver`, `ElaboratedArgument`, `ElaboratedExpr`, `ElaboratedDecl`,
`StorageAccessPlan`, and `BoundStorageAccessPlan` are shorthand for their `<Published>` forms.
`ConstructionElaboratedDecl = ElaboratedDeclAt<Construction>` is permitted only inside a synthesis
construction; `publishElaboratedDecl(decl, validatedWitnessTables, contractCompletions)` recursively
rewrites every operational witness ref and completes every construction contract state, returning
`ElaboratedDeclAt<Published>` or failing atomically.

`subjectOf(dispatch)` projects a witness use to its stable `SubtypeWitnessId` and otherwise
projects a direct/lambda `ResolvedDeclRefAt<S>` to its stable `target`; dependency revisions remain
on the dispatch value but do not split a callable contract subject. Builtin dispatch likewise
projects away only its resolution sidecar. It otherwise preserves the exact dispatch identity
shown above. A
`Selection(pre)` state must find one completion under `(subject, contractContext)` whose signature
and stabilized effect/capability facts validate against `pre`; publication replaces it with the corresponding
`Effective` or `SelectedVariant` value. Existing completed states are revalidated. A partially
applied generic callable stores its residual contract in `PartiallyAppliedCallableGenericValue` and
is not a `CallableValue` or `ElaboratedCallAt<S>`. Thus contract completion is part of the atomic stage
transform, not an ambient mutation after publication.

`ELB-GEN-001`: A `PartiallyAppliedGenericValue` for either a function or a type is a valid published
elaborated compile-time value. Elaboration preserves its `UnappliedDeclRef`, canonical residual
specialization, residual binder, and explicit callable/type-constructor classification; another
generic application may consume it without reconstructing source binders or declaration kind. It
produces no runtime IR merely by existing. Only a completed callable may become an `ElaboratedCall`,
and only a completed generic type specialization may become a runtime `TypeId` use requiring layout.

The optional concrete world is present exactly when target-specific variant selection is required;
`SelectedVariant` requires it and its proof's world must equal it. The Boolean assumption records
the enclosing target/stage branch. Consequently two calls to the same subject under different
branches or worlds have distinct completion keys and cannot overwrite one another.

An access recipe is stage-neutral. Typed overload resolution supplies `TypedInput` operands;
abstract interface adapters supply `AdapterInput` roles. Elaboration binds each operand to an
elaborated value/storage or to a projection of one explicitly evaluated capture result, producing
`BoundStorageAccessPlan`; it does not rerun applicability or change the recipe. This allows the same plan
algebra to be unit-tested without either a full typed expression tree or generated adapter body.

Default arguments and named/positional reordering are already reflected by `parameter`. `InMode`
prepares an ordinary abstract immutable value and may use an implicit conversion. `OutMode` and
`InOutMode` require exact-type mutable storage; an abstract destination may use an explicit
same-type transport buffer and its getter/setter contract, but no conversion or rvalue
materialization. Their write-back is present only on normal return. `ConstRefMode` and `RefMode`
instead pass only the exact physical endpoint retained by
`PhysicalParameterBindingProofAt<S>`: either an existing `PhysicalStorage` or the result of the exact
access-indexed reference-accessor call and stored dereference. Neither physical mode admits an
rvalue, ordinary getter/setter path, conversion, temporary, or write-back. The checker diagnoses a
provable incompatible alias and otherwise preserves the exclusive `RefMode`/`OutMode`/`InOutMode`
contract; a runtime overlap not proved statically is undefined behavior. No alternative
throw/write-back policy is permitted.

Dispatch is a property of `CallableValue`: a direct symbol, witness method
`(SubtypeWitnessRef<S>, RuntimeInterfaceRequirementKey)`, dynamic slot, lambda invocation, or builtin.
It is deliberately absent from
`FuncType`; the same signature can be invoked through different dispatch paths.

`ELB-DYN-001`: `DynamicDispatchKey` is the canonical serialized identity of a dynamic slot. Its
`introducer` is the declaration that first creates the slot, `signature` is that declaration's
canonical callable signature, and `slotRole` distinguishes method/getter/setter/ref-accessor/
initializer surfaces. The `owner` at a use is a specialization whose dynamic member map contains
that exact key; an override reuses the introducer/key and proves signature compatibility rather
than allocating a source-order slot. Keys are sorted canonically before any compact ABI index is
assigned. A mismatched owner, signature, or role is invalid dispatch, not a lookup fallback.

`ELB-CALL-001`: The number and identity of elaborated ordinary arguments match the
`CallableSignature.parameterSlots`; each slot ordinal selects the corresponding semantic
`FuncType` parameter. The receiver is separate; specialization frames are owned by the
canonical declaration reference, conformance, or lambda identity inside `CallableValue`.
For direct, lambda, or builtin dispatch, the stage-correct witness-resolution sidecar is the exact
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
`Effective` or `SelectedVariant` contract state; `Selection` is a pre-inference typed fact. Generated calls may
temporarily carry `Selection` in `ElaboratedCallAt<Construction>` while their group's use graphs
participate in those fixpoints; `publishElaboratedDecl` consumes the stabilized
`ContractCompletionMap`. Thus a published elaboration cannot enter the inference SCC, and the
callee has one contract authority.

`ELB-CALL-008`: `ElaborateTypedCallAt<S>` requires one `BoundStorageAccessPlan<S>` for every key in
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
same `subjectOf(dispatch)` and selection effect/capability facts: direct/lambda calls retain their
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
`OrdinaryCallableResult`. For `FixedPointerLikeCallResult(a)`, the authority kind is
`FixedPointerLikeCallableResult(a)` and resolving `a` yields the call result type and the
byte-identical stored `PointerLikeValueShape`. For a registered call result, the authority kind
names one `RegisteredPointerLikeResultContract`; its registration, environment, and static
inputs are copied into the call-specific provenance and replay over the exact runtime inputs to
derive the stored raw result shape. Call-result provenance states what the call produces; a
consumer separately proves that shape against its own physical-storage/reference requirement.
Equal signature, result `TypeId`, or pointer-like machine representation cannot choose another
authority alternative.

The explicit-accessor path is atomic and has no construction cycle. The caller supplies the
`AccessorPointerLikeSurfaceCallResult` alternative with `invocationIdentity`, `invocationSite`, `sources`,
`provenanceSources`, `expectedReferent`, `context`, and `result`, not an authority, contract, or
certificate containing an already-built call. The builder requires the already resolved authority kind to be
`AccessorPointerLikeCallableResult(contract)` and constructs the following immutable input from
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
`PointerLikeCallResult` whose result is `result` and whose authority is
`AccessorPointerLikeCallResult(certificate)` only when the returned
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
assignment is consumed before IRReady; the nominal content ID is the stage-free value retained by
IRReady and IR.

`ELB-CALL-011`: `ElaborateTypedCallAt<S>` copies `call.accessEnvironment`,
`call.resultAuthority`, `call.resultProvenance`, `call.aliasCompatibility`, and the complete
`call.capabilitySelection`
byte-for-byte to the
`ElaboratedCallAt<S>`. A reference-handle alternative
determines the call region's handle-shaped normal result before `IRReadyAccessorReferenceResult` is
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
the `TypedLambdaInfo` carried by `LambdaExpr<Typed>`; elaboration consumes that stored result and
does not rediscover it:

```text
DiscoverFreeVariables(lambda, boundBody) -> FreeVariableSet
AnalyzeTypedCaptures(lambda, lambda.info.freeVariables, lambda.info.captureUseFacts)
    -> CheckResult<CaptureSet>
BuildLambdaSynthesis(lambda, captureSet, signature)
    -> LambdaSynthesisResultAt<Construction>
RewriteLambdaBody(lambda, synthesis)
    -> ElaboratedFunctionBodyAt<Construction>
BuildLambdaValue(lambda, synthesis)
    -> ElaboratedExprAt<Construction>
```

```text
CapturePlan = {
    source: LocalCapture(DeclRef)
          | ReceiverCapture
          | ForwardedCapture(ForwardedCaptureIdentity),
    type: TypeId,
    initialization: CopyCapture | MoveCapture,
    firstUse: Origin
}

CaptureFailure =
    BorrowedCaptureNotSupported(source: CaptureIdentity,
                                requiredAccess: StorageAccessMode,
                                origin: Origin)
  | CaptureCannotBeOwned(source: CaptureIdentity, type: TypeId, origin: Origin)

CaptureSet = {
    byIdentity: NodeMap<CaptureIdentity, CapturePlan>,
    order: NodeList<CaptureIdentity>
}

CaptureLayout = {
    fields: NodeMap<CaptureIdentity, SynthesizedDeclId>,
    order: NodeList<CaptureIdentity>
}

ForwardedCaptureIdentity = {
    parentLambda: AnyASTNodeId<Typed>,
    parentCapture: CaptureIdentity
}

CaptureIdentity = {
    lambda: AnyASTNodeId<Typed>,
    source: DeclRef | ReceiverCapture | ForwardedCaptureIdentity
}

```

`ELB-LAM-001`: `lambda.info.captureUseFacts` is the sole typed-body projection consumed by capture
analysis. Every fact's source occurs in `freeVariables`, and every typed use of a free variable has
exactly one fact with the same origin, type, category, access, and source lifetime. The typed-lambda
constructor validates this bijection; elaboration neither walks `typedBody` to rediscover uses nor
adds an unrecorded capture.

`ELB-LAM-002`: A `ForwardedCaptureIdentity.parentLambda` is the immediate lexically enclosing
lambda, and `parentCapture.lambda` equals it. Following forwarded identities strictly decreases
lambda nesting depth and terminates at a declaration or receiver capture. Capture-set/layout maps
are keyed by the complete identity, so equal source declarations captured through different parent
chains cannot alias accidentally.

`ELB-LAM-003`: Every capture is owned by the synthesized lambda environment and has exactly one
checked copy or move initialization. A typed use that would require a borrowed read, borrowed write,
or reference capture produces `BorrowedCaptureNotSupported`; capture analysis never shortens a
lifetime or emits a borrowed environment field. Forwarding an owned capture preserves its
`CaptureIdentity` chain and performs another checked owning initialization when required.

Unqualified `CallableValue`/`CallableDispatch` mean the `<Published>` forms. Generated bodies may
use `<Construction>` only inside the draft/synthesis scope defined in chapter 9; atomic freeze
rewrites every operational reference before an `ElaboratedCall` or IR node is published.

Binding discovers only which lexical declarations are free. Capture order is the lexical order of
first source use with stable declaration identity as a tie-breaker. Nested-lambda capture forwarding
is explicit in `source`. The owning initialization choice is inferred from the typed uses and type
properties; it cannot be decided from a merely bound body. The resulting plan must own the value:
a copyable source uses `CopyCapture`, an explicitly consumable source may use `MoveCapture`, and a
source that can only be borrowed is rejected. Borrowed lambda captures are not supported, whether
or not escape analysis could prove a particular lambda non-escaping.

`CaptureSet.order` is a duplicate-free bijection onto `byIdentity` keys in that semantic order;
`CaptureLayout.order` is byte-identical and is a duplicate-free bijection onto `fields` keys. The
maps provide identity lookup while the explicit lists, not map iteration, define layout.

The synthesized lambda environment is construction-stage data until its declaration and callable
conformance freeze together. `LambdaExpr` is the source AST node; `LambdaDecl` is the synthesized
`StructDecl` for the environment, matching the established codebase distinction. The following
product collects that declaration with the other results of lambda synthesis:

```text
LambdaSynthesisResultAt<S: WitnessTableState> = {
    lambdaDecl: SynthesizedDeclId,
    environmentType: TypeId,
    layout: CaptureLayout,
    initializer: CallableSignature(
        FuncType(receiver=NoReceiver,
                 parameters=one parameter per capture,
                 result=environmentType),
        stable synthesized ParameterKeys),
    invoke: CallableSignature(
        FuncType(receiver=Receiver(environmentType, selected mode),
                     parameters=lambda parameters,
                     result=lambda result),
        lambda ParameterKeys),
    callableWitness: SubtypeWitnessRef<S>
}

LambdaSynthesisResult = LambdaSynthesisResultAt<Published>
```

The rewritten body replaces each captured reference with a field access through the explicit
receiver. The lambda expression becomes an elaborated construction of
`synthesis.environmentType` from the values in `synthesis.layout.order`. No `LambdaExpr`
reaches an `IRReady` node.

`SYN-LAM-001`: Free-variable discovery reads a bound body; capture-mode analysis reads the typed
body. Both return immutable data and neither inserts fields while walking.

`SYN-LAM-002`: The callable witness table's `RequirementDictionary` is keyed by the standard
environment's call requirement key. Lambda layout order is not used as witness identity. During
construction the field is an operational reference authorized by the lambda environment's
`SynthesisConstruction`; atomic freeze rewrites it to the validated reference for the same
witness-table identity at the same time that it publishes the environment declaration and
rewritten body.

`SYN-LAM-003`: Inferred result types are solved from all reachable returns and the fall-through
path before lambda-environment synthesis. A mutable “first return fills the type” protocol is
forbidden.

`SYN-LAM-004`: Capture identity excludes discovery/task order. Each layout field's initializer is
the exact checked `CopyCapture` or `MoveCapture` operation from the corresponding `CapturePlan`.
Validators reject borrowed/reference capture requests and missing, mismatched, or duplicated owning
initializers before assigning `CaptureLayout`.

`SYN-LAM-005`: `environmentType` resolves to a `DeclRefType` whose `DeclRef` names
`lambdaDecl` under the synthesis group's canonical specialization, and that declaration resolves
to a `LambdaDecl`. The initializer result and invoke receiver use that exact `TypeId`; neither
signature contains an unnamed receiver-type placeholder or recovers its receiver type from
declaration nesting.

The result solver combines the contextual expected result, every reachable `return`, the
fall-through result (`VoidType` when permitted), `BottomType` paths, and recovery expressions using
the join rules in chapter 7. A captureless lambda may additionally elaborate to a static thunk when
a raw function type is expected; a capturing lambda is never silently converted to a raw function
pointer. The thunk and any lambda-environment declarations belong to the same atomic
`SynthesisGroup`.

## Interface requirement synthesis

Conformance checking first produces the authoritative kind-indexed `RequirementMatch<K>` from
chapter 9 for every
`RequirementKey<K>`. The payload/proof shapes are parallel to `RequirementWitness<K>`: an
associated type carries a `TypeId` plus constraint proofs, a callable carries a canonical
declaration plus a signature proof, an accessor aggregate carries a role-keyed accessor map, a
constant carries a checked value, and a nested conformance carries an
`SubtypeWitnessId` plus its stage-appropriate resolution set.

`Exact` and `OptionalAbsent` never create code. `Adaptable` creates an adapter; `Defaulted` and
`Builtin` create code only when their typed plans declare generated output roles. Callable adapters
use exactly `RequirementWitnessSynthesisPlan<CallableKind>` and default matching uses
`DefaultUsePlan<K, Construction>` from chapter 9. Its `ParameterCorrespondence`
maps requirement slots (including receiver and pack expansions) to independently keyed
implementation slots; the keys are not compared for equality. Its parameter access plans consume
requirement-call arguments and produce implementation-call arguments, its result conversion maps
implementation success to the required result, and its error plan proves and implements
propagation, conversion, catching, or the absence of thrown errors.

`SYN-WIT-001`: Synthesis is permitted only from a validated adapter plan. Code generation never
rediscovers how a candidate satisfies a requirement.

`SYN-WIT-002`: A synthesized requirement witness method has the exact required `FuncType`, including receiver,
parameter modes, result/error type, traits, and calling convention. Its separate effective callable
contract satisfies the requirement's effect and capability obligations. Its body applies the
adapter plan and calls the chosen implementation.

`SYN-WIT-003`: The resulting `RequirementDictionary` entry is keyed by `RequirementKey` and refers to the
synthesized declaration by stable ID. Associated-type and nested-conformance requirements produce
typed witness alternatives, not function stubs.

This same mechanism handles property/accessor adaptation, static-versus-instance adapters when the
language permits them, default interface methods, enum builtin requirements, differentiability
requirements, and synthesized constructors. Each case has a distinct rule ID and adapter-plan
constructor; they do not share a large branch that mutates arbitrary AST fields.

## Other desugarings

The `IRReady` node family has these explicit forms:

| Typed/elaborated form            | IRReady form                                                        |
| -------------------------------- | ------------------------------------------------------------------- |
| operator syntax                  | direct call or declared primitive operation                         |
| property/subscript read          | getter call, or exact `constref` accessor plus dereference fallback |
| property/subscript write         | setter call, or exact `ref` accessor plus dereference fallback      |
| initialization syntax            | the distinct operation selected by `InitializationPlan`             |
| implicit conversion              | `Convert(plan, value)`                                              |
| existential conversion           | `PackExistential(value, type, witness)`                             |
| existential member use           | `OpenExistential` region plus witness lookup                        |
| `fwd_diff` / `bwd_diff`          | selected provider plus `DerivativeSignatureMapId`                   |
| `no_diff`                        | explicit `DetachExpr` boundary                                      |
| `defer`                          | explicit cleanup regions on every exiting edge                      |
| lambda                           | lambda-environment declaration plus construction                    |
| default argument                 | expression cloned through provenance-preserving substitution        |
| target/stage switch              | conditional IRReady regions with capability presence formulas       |
| compile-time loop/pack expansion | explicit expansion nodes or materialized sequence after solving     |

Desugaring order is defined by dependencies between lowering queries, not by a mutable visitor's
incidental traversal. A lowering query consumes only the node forms listed in its input schema and
produces the declared later form, preventing query cycles from masquerading as progress.

## IR-ready node forms

The `IRReady` node family is deliberately small:

```text
IRReadyExpr = Constant | PhysicalStorage(IRReadyPhysicalStorage) |
           BuiltinPhysicalProjection(IRReadyBuiltinPhysicalProjection) |
           RegisteredPhysicalProjection(IRReadyRegisteredPhysicalProjection) |
           Load(IRReadyLoad) | Store | TemporaryStorage(IRReadyTemporaryStorage) |
           ReferenceProducer(IRReadyReferenceProducer) | Dereference(IRReadyDereference) |
           Convert | Initialize(IRReadyInitialization) | Extract | Update | CallRegion |
           Witness | PackExistential | OpenExistential | Differentiate |
           DetachExpr | Primitive | Error

IRReadyStmt = Let | Var | Assign | ExpressionStmt | DestroyTemporary(IRReadyDestroyTemporary) |
           If | Switch | Loop | Break | Continue | Return | Throw | Region |
           CleanupRegion | Error

IRReadyDecl = TypeDecl | FunctionDecl | GlobalDecl | WitnessTableDecl | ImportDecl | ErrorDecl

IRReadyPhysicalStorageShape = {
    access: StorageAccessMode,
    mutability: Mutability,
    addressSpace: PhysicalStorageAddressSpace,
    lifetime: LifetimeId,
    alias: AliasProvenance,
    sourceProvenance: PhysicalStorageSourceProvenance
}

IRReadyPhysicalStorage = {
    valueType: TypeId,
    storage: PhysicalStorageRef
}

IRReadyTemporaryStorageShape = {
    identity: TemporaryStorageIdentity,
    lifetime: LifetimeId,
    alias: AliasProvenance
}

IRReadyTemporaryStorage = {
    descriptor: MaterializedTemporaryStorage,
    source: IRReadyValueId
}

IRReadyDestroyTemporary = {
    storage: IRReadyValueId,
    destruction: DestructionExecutionAt<Published>
}

IRReadyBuiltinPhysicalProjection = {
    identity: BuiltinPhysicalProjectionIdentity,
    operation: BuiltinPhysicalProjectionOperation,
    runtimeOperands:
        CanonicallyOrderedMap<BuiltinPhysicalProjectionOperandRole, IRReadyValueId>,
    evaluationOrder: NodeList<BuiltinPhysicalProjectionOperandRole>,
    inputShapes:
        CanonicallyOrderedMap<BuiltinPhysicalProjectionOperandRole, IRReadyValueShape>,
    output: BuiltinPhysicalProjectionResultProof,
    control: BuiltinPhysicalProjectionControlProof
}

IRReadyLoad = LoadPhysicalStorage(source: IRReadyValueId)

IRReadyRegisteredPhysicalProjection = {
    identity: RegisteredPhysicalProjectionIdentity,
    registration: RegisteredDataOperationRegistration,
    runtimeOperands:
        CanonicallyOrderedMap<RegisteredPhysicalProjectionOperandRole, IRReadyValueId>,
    evaluationOrder: NodeList<RegisteredPhysicalProjectionOperandRole>,
    inputShapes:
        CanonicallyOrderedMap<RegisteredPhysicalProjectionOperandRole, IRReadyValueShape>,
    output: RegisteredPhysicalProjectionResultProof,
    control: RegisteredPhysicalProjectionControlProof
}

IRReadyRegisteredDirectReferenceApplication = {
    registration: ReferenceOperationRegistration,
    operandType: TypeId,
    storage: PhysicalStorageRef,
    storageProof: PhysicalStorageProof,
    output: PointerLikeProof,
    control: ReferenceDataOperationControlProof
}

IRReadyRegisteredHandleTransformApplication = {
    registration: ReferenceOperationRegistration,
    input: PointerLikeProof,
    output: PointerLikeProof,
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

IRReadyCallOperandProjection = {
    slot: BoundCallSlot,
    operand: IRReadyValueId,
    expansion: ExpansionPath
}

IRReadyCapturedSourceBinding = {
    capturedValue: IRReadyValueId,
    projections: NodeList<IRReadyCallOperandProjection>
}

IRReadyAccessorReferenceResultProof = {
    normalResult: IRReadyValueId,
    contract: AccessorReferenceResultContractId,
    invocationIdentity: AccessorInvocationIdentity,
    subject: CallableContractSubject,
    signature: CallableSignatureId,
    expectedReferent: TypeId,
    referentEquality: TypeEqualityProofId,
    sources:
        CanonicallyOrderedMap<AccessorProvenanceSourceRole,
                              IRReadyCapturedSourceBinding>,
    derivation: AccessorReferenceResultDerivation,
    result: PointerLikeValueShape,
    callResultType: TypeId,
    resultEquality: TypeEqualityProofId
}

IRReadyReferenceProducer =
    IRReadyAddressOfPhysicalStorage(
        storage: IRReadyValueId,
        proof: DirectStorageHandleProof)
  | IRReadyAccessorReferenceResult(
        value: IRReadyValueId,
        proof: IRReadyAccessorReferenceResultProof)
  | IRReadyRegisteredDirectReference(
        storage: IRReadyValueId,
        application: IRReadyRegisteredDirectReferenceApplication)
  | IRReadyRegisteredHandleTransform(
        handle: IRReadyValueId,
        application: IRReadyRegisteredHandleTransformApplication)

IRReadyRegisteredDereferenceApplication = {
    identity: DereferenceApplicationIdentity,
    registration: ReferenceOperationRegistration,
    input: PointerLikeProof,
    output: DereferencedStorageProof,
    control: ReferenceDataOperationControlProof
}

IRReadyDereference =
    IRReadyReferenceDereference(
        handle: IRReadyValueId,
        proof: DereferencedStorageProof)
  | IRReadyPointerDereference(
        handle: IRReadyValueId,
        proof: DereferencedStorageProof)
  | IRReadyRegisteredReferenceDereference(
        handle: IRReadyValueId,
        application: IRReadyRegisteredDereferenceApplication)

IRReadyRuntimeValueCategory =
    RValue
  | PointerLikeValue(PointerLikeShape)
  | PhysicalStorage(IRReadyPhysicalStorageShape)
  | TemporaryStorage(IRReadyTemporaryStorageShape)

SubtypeWitnessValueShape = {
    form: SubtypeWitnessForm
}

IRReadyValueShape =
    IRReadyRuntimeValueShape(type: TypeId, category: IRReadyRuntimeValueCategory)
  | IRReadyGenericMetadataValueShape(variable: CanonicalBoundVariable)
  | SubtypeWitnessValueShape
  | IRReadyWitnessEntryValueShape(key: SomeInterfaceRequirementKey)
  | IRReadyOtherConstraintEvidenceValueShape(slot: CanonicalConstraintSlot)

IRReadyGenericInputs = {
    genericArguments: NodeMap<CanonicalBoundVariable, IRReadyValueId>,
    constraintEvidence: NodeMap<CanonicalConstraintSlot, IRReadyValueId>
}

conformanceInputsByWitness(inputs, binder) =
    checkedUniqueMap {
        ContentId(CanonicalSubtypeWitness(targetOf(slot))) -> inputs.constraintEvidence[slot]
        | slot in binder.constraints,
          slot.kind = ConformsKind
    }

IRReadyWitnessOperation =
    WitnessTableReference(definition: ValidatedWitnessTableRef)
  | SpecializeWitness(generic: IRReadyValueId,
                      specialization: CanonicalSpecializationSpine,
                      inputs: IRReadyGenericInputs)
  | LookupWitness(base: IRReadyValueId, key: SubtypeWitnessLookupKey)
  | LookupWitnessEntry(base: IRReadyValueId, key: SomeInterfaceRequirementKey)
  | ExtractExistentialWitness(package: IRReadyValueId,
                              interface: InterfaceInstanceKey)

IRReadyValueKey = {
    producer: AnyASTNodeId<IRReady>,
    resultOrdinal: UInt32,
    shape: IRReadyValueShape
}

IRReadyValueId = ContentId<IRReadyValueKey>

IRReadyCallContract = {
    signature: CallableSignatureId,
    resultAuthority: CallableResultAuthorityId,
    effective: EffectiveCallableContractId,
    callerInvocationLifetime: LifetimeId,
    aliasCompatibility: CompatibleCallAliasClaims,
    capabilitySelection: CapabilitySelection
}

IRReadyPhysicalParameterSourceProof =
    IRReadyExistingPhysicalEndpoint
  | IRReadyAccessorPhysicalEndpoint(
        dereference: DereferenceApplicationIdentity)

IRReadyPhysicalParameterInputProof = {
    mode: ParamPassingMode,
    storage: PhysicalStorageRef,
    parameterValueType: TypeId,
    identity: PhysicalStorageIdentityProof,
    instantiatedRequirement: PhysicalStorageRequirement,
    physicalStorage: PhysicalStorageProof,
    source: IRReadyPhysicalParameterSourceProof
}

IRReadyCallInputs = {
    initializationTarget: Option<IRReadyValueId>,
    receiver: Option<IRReadyValueId>,
    parameters: NodeMap<ParameterKey, IRReadyValueId>,
    physicalParameters:
        NodeMap<BoundCallSlot, IRReadyPhysicalParameterInputProof>,
    generic: IRReadyGenericInputs
}

DirectCall = {
    callee: ResolvedDeclRef,
    contract: IRReadyCallContract,
    inputs: IRReadyCallInputs
}

WitnessCall = {
    witness: IRReadyValueId,
    entry: RuntimeInterfaceRequirementKey,
    contract: IRReadyCallContract,
    inputs: IRReadyCallInputs
}

DynamicCall = {
    owner: TypeId,
    slot: DynamicDispatchKey,
    contract: IRReadyCallContract,
    inputs: IRReadyCallInputs
}

LambdaCall = {
    invoke: ResolvedDeclRef,
    contract: IRReadyCallContract,
    inputs: IRReadyCallInputs
}

PrimitiveCall = {
    rule: RuleId,
    registration: StandardEnvironmentRuleId,
    staticInputs: CanonicalArguments,
    witnessResolutions: WitnessResolutionStamp,
    contract: IRReadyCallContract,
    inputs: IRReadyCallInputs
}

IRReadyCall = Direct(DirectCall) | Witness(WitnessCall) | Dynamic(DynamicCall) |
           Lambda(LambdaCall) | Primitive(PrimitiveCall)

CallRegion = {
    preparation: NodeList<IRReadyStmt>,
    call: IRReadyCall,
    normalCompletion: NodeList<IRReadyStmt>,
    exceptionalCompletion: NodeList<IRReadyStmt>,
    result: IRReadyValueId,
    thrownError: Option<IRReadyValueId>
}
```

Chapter 16 is the sole schema authority for `IRReadyInitialization` and its selected plan-step
alternatives; the `Initialize` case above does not erase them to a generic construct flag. Its
recovery alternative is tooling-only and is not a successful initialization operation.

All IRReady nodes are typed. `PhysicalStorage`, `TemporaryStorage`, `ReferenceProducer`, and
`Dereference` preserve their exact value type, access, lifetime, alias, and source provenance until
IR lowering; only genuine physical storage carries mutability and a physical address-space fact.
Abstract properties and declared subscripts have already become accessor call regions. High-level
structured control remains where useful, but its exit and cleanup behavior is explicit.

`ELB-IRDY-001`: Executable IRReady validation rejects unresolved names, overload sets, unconsumed
partial generic values, implicit receivers, unplanned conversions, raw lambdas, and incomplete
`RequirementDictionary` values.

`ELB-IRDY-002`: `LowerNodeToIRReady` first lowers every access plan's preparation in order, then dispatches
on its closed terminal. `PassArgument` contributes the named runtime argument and its completion
steps to the enclosing call or registered-operation region. `YieldStorageRead` produces the named
IRReady value directly; it does not synthesize a call region for a physical load. `CompleteStorageWrite`
emits its exact physical `Store` or abstract-setter `CallRegion` and yields the terminal's result
value after normal completion. Completion steps are placed on the normal/exceptional edges selected
relative to that terminal. A captured-reference source environment first lowers each capture
result's explicit `evaluation` to exactly one IRReady producer in its stored order, and every
`CapturedSourceProjection` reads that producer. Thus no source capture, preparation, terminal, or
completion behavior remains hidden inside a call opcode or inferred from the consuming syntax.

Lowering an abstract `OutMode`/`InOutMode` transport buffer creates one
`IRReadyTemporaryStorage` whose value type is exactly both the parameter and abstract-storage value
type, whose descriptor is byte-identical to the access-plan descriptor, and whose chapter 16
initialization is the descriptor's exact plan application. This IRReady node projects that application's unique
`CreatePlanStorage` transition rather than allocating a second object. The nested IRReady
initialization owns pre-checkpoint exceptional cleanup; only its normal checkpoint produces the
transport value. A later write-back exists only on the enclosing call's normal-return edge and
carries the selected setter/store execution; exceptional edges perform destruction without
write-back. No pre- or post-conversion exists, and no operation chooses cleanup from the IRReady
value type.
Its `IRReadyTemporaryStorageShape.identity` is the descriptor's nominal
`TemporaryStorageIdentity`, and its alias is the matching `temporaryStorageAliasRoot`; IRReady removes
the site from the runtime value shape after checking that equation, while the selected
initialization application retains its authenticated site as static validation data.

`ELB-IRDY-010`: Lowering `PhysicalStorageArgument(p, binding)` emits the IRReady physical-storage value for
exactly `physicalParameterStorage(binding)`. A direct source reuses the lowered existing physical
producer. An accessor-produced source expands the stored
`ParameterReferenceAccessorPlanAt<S>` into its accessor `CallRegion`, optional registered handle
transform, and `IRReadyDereference`, in that order; the dereference's output is the physical argument.
The accessor handle has no other IRReady use. The resulting IRReady value retains access, mutability,
physical address space, lifetime, alias, and source provenance, and no IRReady temporary, load,
conversion, or write-back intervenes. `ConstRefMode` and `RefMode` therefore share this one physical
IRReady path while remaining distinguishable by `binding.mode.access` and the complete requirement
proof selected before lowering. The corresponding `IRReadyCallInputs.physicalParameters` entry is the
stage-free projection of `binding`: it retains mode, endpoint, parameter type, identity proof,
instantiated requirement, and physical proof, and records whether the IRReady operand is an existing
endpoint or the result of the exact stored dereference. It contains no typed expression or accessor
plan.

`ELB-IRDY-011`: At function entry, every `PhysicalStorageAbiInput` creates one
`IRReadyPhysicalStorage` whose `PhysicalStorageRef` is the contract's exact formal storage. A
`ConstRefMode` receiver/parameter uses its nominal `ConstRefFormalRoot`, has `ReadAccess`,
`UnknownMutability`, `CallableActivationLifetime(signature)`, and cannot be stored through. A
`RefMode` role uses its nominal `RefFormalRoot`, has `ReadWriteAccess`, `Mutable`, and may be read or
written under its exclusive invocation contract. Both use the entry proof's formal address space, source
facts, and `UnknownAliasRoot`. Physical projections preserve those facts and may not amplify
access. There is no borrowed formal category or hidden conversion between the two roots.

`ResolveAbstractStorageThroughReference` expands to the stored accessor `CallRegion`, its
already-proven handle result (and optional registered transform), and the stored `IRReadyDereference`.
The enclosing read terminal then selects the physical `Load`, while the write terminal selects the
physical `Store`. The intermediate handle is kept in that local sequence and has no escaping IRReady
use.

`ProjectPhysicalStorageThroughParameterAccessor` expands through the same closed reference
primitives but from its distinct `ParameterReferenceAccessorPlanAt<S>`. It emits no load or store:
the stored `IRReadyDereference` result is the `PhysicalStorageArgument` endpoint. Its accessor access key,
handle admission, dereference proof, and resulting physical storage are preserved exactly, so
ordinary storage fallback and physical-parameter preparation cannot be interchanged.

`ELB-IRDY-003`: `IRReadyValueId = ContentId(IRReadyValueKey)` under chapter 1's exact encoding.
Resolving the producer node must find `resultOrdinal` and the identical stored result shape. Two
results of one node, or equal-shaped results of different nodes, therefore remain distinct without
allocation-order identity. Every IRReady operand resolves in the containing heterogeneous immutable
`SemanticSnapshot` and names a node or value whose schema admits the required IR-ready form.

`ELB-IRDY-004`: Resolving `IRReadyCallContract.effective` yields an effective contract whose
signature equals `contract.signature`. Resolving that signature yields exactly the keys in
`inputs.parameters`; the receiver is present exactly when its `ReceiverSlot` is present, and
`initializationTarget` is present exactly when `CallablePurpose` is `ConstructorCallable`. That
target is a physical-storage IRReady value satisfying the stored target slot and is never receiver or
parameter zero. Each other input's type/category is valid for the corresponding `ParamPassingMode` after
the explicit preparation steps. A mode whose domain is `PhysicalOperand(location)` has exactly a
`IRReadyRuntimeValueShape(valueType, PhysicalStorage(shape))` input. The originating call-slot plan has a
`PhysicalStorageArgument` whose binding names the same endpoint and complete mode, and its
`physicalStorage` proof satisfies
`instantiatePhysicalStorageRequirement(mode, callerInvocationLifetime)`, including access,
lifetime, symbolic address space, and source provenance. `ConstRefMode` requires the read view;
`RefMode` requires the read/write view. IRReady validation compares the retained endpoints and never
re-instantiates a weaker requirement. An ordinary rvalue, abstract storage, reference handle, or
temporary-storage value is invalid even if its `TypeId` agrees. A nonphysical-mode
reference-handle value remains
`PointerLikeValue(handle)` with the exact checked proof rather than becoming `RValue`.
`inputs.physicalParameters` has exactly the receiver/parameter-role domain whose modes are physical.
Each entry's storage projects to the corresponding IRReady input shape; its identity proof endpoints
are that storage's value type and the substituted parameter type with zero rank; and its physical
proof has the byte-identical storage and instantiated requirement. `IRReadyExistingPhysicalEndpoint`
requires the call operand to be the lowered direct source.
`IRReadyAccessorPhysicalEndpoint(d)` requires it to be the output of the exact `IRReadyDereference` with
identity `d`. No stage-specific binding is consulted after this projection.
`generic.genericArguments` and `generic.constraintEvidence`
contain exactly the runtime binder/evidence slots selected by the call's logical ABI map.
Type/value/pack arguments use `IRReadyGenericMetadataValueShape` with the identical bound variable;
`Conforms` evidence uses `SubtypeWitnessValueShape` with the exact predicate classifier, and every
other evidence value uses `IRReadyOtherConstraintEvidenceValueShape` with the identical slot. The
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
IRReady operand order or dropped merely because target ABI lowering permits aliasing.
`contract.resultAuthority` is copied byte-for-byte from the originating elaborated call and
resolves under the IRReady dispatch target and `contract.signature` to the same anchored authority.
IRReady construction cannot infer it from the result value or replace it during effective-contract
completion. `contract.capabilitySelection` is copied byte-for-byte from the originating elaborated
call. It remains the complete `CAP-SEL-004` product after inference has consumed its ordinary-use
map: its region, exact keyed uses, and zero/one/multiple concrete source set with combined
requirement and proof all revalidate under `CAP-SEL-003`. IRReady construction cannot reconstruct it
from `effective`, a flat capability set, or the dispatch target.

`ELB-IRDY-005`: A direct target resolves to the stored signature; a witness target consumes a
`SubtypeWitnessValueShape` whose non-error form is `ConcreteSubtypeWitness(target)` or
`AbstractSubtypeWitness(target)` and whose target interface owns the exact runtime-entry key and resolves that
entry to the signature; a dynamic slot and lambda invocation resolve through their registered
owner/invoke declaration; and a primitive rule resolves in the versioned standard environment.
These are validation operations, not overload or conformance search. A target that resolves to a
different signature or contract is an invalid IRReady graph.

`ELB-IRDY-006`: `result` is result ordinal zero of the `CallRegion` node and has the signature's
normal result type. Its category is the exact checked result-channel proof admitted by
`contract.resultAuthority`:
`PointerLikeProvenance(proof)` becomes `PointerLikeValue(proof.shape)`, an inner explicit
ref-accessor call uses the result shape and stage-free instantiation projected from its exact
`AccessorReferenceResultCertificate`, and
`NoAdditionalValueProvenance` becomes `RValue`. `thrownError` is ordinal one with the corresponding
checked provenance and the signature's error type exactly when that type is not `BottomType`,
matching the logical ABI channel. A physical storage is never returned as a call result. The exceptional edge
exists only when the effective contract can throw; otherwise `exceptionalCompletion` is empty and
`thrownError` has no legal use. The call inputs are available after `preparation`; `result` is
visible only on the normal-completion edge and `thrownError` only on an existing exceptional edge.
A value defined on one completion edge cannot be used on the other or after a non-joining exit.

`ELB-IRDY-007`: Abstract storage is eliminated before IRReady. Every IRReady `PhysicalStorage`, `Load`,
`Store`, address-of/registered-direct reference input, and dereference result has a
`IRReadyPhysicalStorageShape`; no IRReady operation can encode a property getter/setter as a physical
address or materialize a temporary to satisfy a physical-domain mode. The closed physical-storage producers are a
stored root/field or vector projection,
`IRReadyBuiltinPhysicalProjection` with its checked application,
`IRReadyRegisteredPhysicalProjection` with its validated application,
initialization/allocation storage, and one of the `IRReadyDereference` alternatives. Generic
`Primitive` cannot manufacture physical storage. Each `LookupSubtypeWitness` in the semantic witness key
becomes exactly one IRReady `LookupWitness` and remains one operation through initial IR lowering.

`IRReadyBuiltinPhysicalProjection.runtimeOperands` has exactly the two-role domain of `inputShapes`
and `evaluationOrder`; each value has its stored shape and is the result of the corresponding
elaborated operand. Its identity, operation, output proof, and control proof are byte-identical to
the typed application. `output.storage.path` is
`BuiltinElement(output.inputStorage.path, identity)`. This is the only IRReady producer for that path
alternative; `IRReadyPhysicalStorage` cannot reconstruct a dynamic index from its path. The closed IRReady
physical-storage provenance relation resolves the base `IRReadyValueId` to exactly
`output.inputStorage`; matching only its `IRReadyPhysicalStorageShape` is insufficient. Neither the node
nor any transitive static proof field contains `AnyASTNodeId<Typed>`, `TypedExpr`, or an index-recovery
recipe.

`IRReadyRegisteredPhysicalProjection.runtimeOperands` has exactly the domain of `inputShapes` and
`evaluationOrder`; each value has the stored shape and is the result of the corresponding bound
operand plan from `ELB-STO-002`. Its identity, registration, output proof, and control proof are
byte-identical to the typed application. `output.storage.path` is
`RegisteredPhysicalProjection(identity)`. This is the only IRReady producer for that path alternative;
an `IRLookupWitnessMethod`, registered data opcode, or reconstructed resource path cannot
substitute for it.

`ELB-IRDY-008`: `SpecializeWitness(generic, specialization, inputs)` consumes a
`GenericSubtypeWitness` value. `inputs` contains exactly the runtime generic variables and
constraint slots of that generic witness's binder in canonical order, with the same IRReady shape law
as call inputs. Its witness operands are materialized from the specialization evidence plus the
stage-frozen resolution sidecar; the semantic spine alone is not treated as an SSA operand list.
The result classifier is the total concrete specialization of the generic classifier.

`ELB-IRDY-009`: `IRReadyPhysicalStorage(valueType, storage)` has
`IRReadyRuntimeValueShape(valueType, PhysicalStorage(shape))`, where `shape` is the exact projection of
`storage`'s access, mutability, address space, lifetime, alias, and source provenance. A
`IRReadyAddressOfPhysicalStorage` operand has that shape for the stored
`DirectStorageHandleProof.storage`. Every reference producer result uses its stored
`PointerLikeValueShape` to form
`IRReadyRuntimeValueShape(result.type, PointerLikeValue(result.handle))`, preserving the non-type
provenance fields. A direct/registered producer projects that shape from its admitted handle proof;
an accessor producer takes it directly from `proof.result`.
`IRReadyAccessorReferenceResult` consumes the exact handle-shaped normal result of the call named by
`proof.normalResult`. The proof's subject/signature equal that IRReady call, its contract is replayed
against the exact `IRReadyCapturedSourceBinding` values and call-operand projections, and its
derivation yields `proof.result`. `callResultType` and `resultEquality` prove that same result type.
No transitive field contains an AST node or typed captured source. The
wrapper produces the identical
handle-shaped value without a second runtime evaluation or a same-type reclassification.
Registered direct/transform operands and
results equal their application's endpoints. For a direct application,
`storageProof.storage = storage`, `operandType = storage.valueType`, the separate storage operand is
that storage, and the output is the stored handle proof. For a transform, the separate handle
operand has `application.input` and the result has `application.output` exactly.
`IRReadyDereference` has one handle-shaped operand and one physical-storage result equal to its
`DereferencedStorageProof.output`; builtin and registered alternatives are never interchangeable.
The proof's `identity` and `DereferencedReference(identity)` path are preserved in IRReady, while the
executable handle is the alternative's `IRReadyValueId`. For a registered alternative,
`application.identity = application.output.identity`; IRReady validation rejects a proof or
application copied from another dereference even when both endpoint shapes are equal.
Projecting the typed registered application to `IRReadyRegisteredDereferenceApplication` removes
`input.operand`, the site assignment, selection state, semantic-use edges, and origins only after
validation; it retains
the byte-identical identity, registration, `input.handle`, output proof, and control proof. Thus no
transitive static dereference field contains the typed handle node; the IRReady operand is its only
executable authority.

## Frontend IR contract

`FrontendIRFragment` separates symbol declarations from definitions. Lowering is a pure query over
`IRReady` declarations and imported semantic interfaces. Fragments are merged by declaring every stable symbol in
canonical order first, then attaching definitions; mutual recursion and generated forward
references therefore never depend on fragment completion order.

```text
IRSymbolKind = FunctionSymbol | TypeSymbol | GlobalSymbol | WitnessTableSymbol

IRSymbolOwner =
    DeclSymbolOwner(DeclRef)
  | WitnessTableSymbolOwner(WitnessTableId)
  | SynthesizedSymbolOwner(SynthesizedSemanticId)
  | ExportedSymbolOwner(ExportedId)

IRSymbolRole =
    PrimarySymbol
  | WitnessRuntimeEntrySymbol(RuntimeInterfaceRequirementKey)
  | RegisteredSymbolRole(stableName: QualifiedName, inputs: CanonicalArguments)

IRSymbolDiscriminator =
    FunctionSymbolSignature(CallableSignatureId)
  | TypeSymbolType(TypeId)
  | GlobalSymbolType(TypeId)
  | WitnessTableSymbolIdentity(WitnessTableId)

IRSymbolKey = {
    owner: IRSymbolOwner,
    role: IRSymbolRole,
    discriminator: IRSymbolDiscriminator
}

IRSymbolId = ContentId<IRSymbolKey>

IRPhysicalStorageShape = {
    valueType: TypeId,
    access: StorageAccessMode,
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
  | PointerLikeIRValueShape(shape: PointerLikeValueShape)
  | PhysicalStorageValueShape(shape: IRPhysicalStorageShape)
  | TemporaryStorageValueShape(shape: IRTemporaryStorageShape)
  | InitializationTargetShape(target: InitializationTargetSlot)
  | GenericMetadataShape(variable: CanonicalBoundVariable,
                         sort: GenericParameterSort)
  | SubtypeWitnessValueShape
  | InterfaceRequirementKeyValueShape(key: IRInterfaceRequirementKeyValue)
  | WitnessEntryShape(key: SomeInterfaceRequirementKey)
  | OtherConstraintEvidenceShape(kind: ConstraintKind)
  | ErrorValueShape(type: TypeId, error: ErrorId)

FunctionAbiInputRole =
    InitializationTargetAbiInput
  | ReceiverAbiInput
  | ParameterAbiInput(parameter: ParameterKey)
  | GenericAbiInput(variable: CanonicalBoundVariable)
  | WitnessAbiInput(witness: SubtypeWitnessId)

AbiPointerLikeAddressSpaceSelection = {
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
    PointerLikeAddressSpaceSelection(AbiPointerLikeAddressSpaceSelection)
  | PhysicalStorageAddressSpaceSelection(AbiPhysicalStorageAddressSpaceSelection)

FunctionAbiContext = {
    activationLifetime: LifetimeId,
    addressSpaces: NodeMap<FunctionAbiInputRole, AbiAddressSpaceSelection>
}

AbiPhysicalStorageInputContract = {
    mode: ParamPassingMode,
    parameterLocation: ParameterPhysicalLocationRequirement,
    formalEntry: PhysicalFormalEntryProofId,
    formalRequirement: PhysicalStorageRequirement,
    formalStorage: PhysicalStorageRef,
    formalShape: IRPhysicalStorageShape,
    formalProof: PhysicalStorageProof
}

AbiPointerLikeMutabilityPolicy =
    AccessDerivedHandleMutability
  | DeclaredHandleMutability(Mutability)

accessDerivedHandleMutability(ReadAccess) = UnknownMutability
accessDerivedHandleMutability(ReadWriteAccess) = Mutable

AbiPointerLikeLifetimePolicy =
    FormalActivationHandleLifetime
  | DeclaredHandleLifetime(LifetimeId)

AbiPointerLikeAliasPolicy =
    ConservativeUnknownHandleAlias
  | DeclaredHandleAlias(AliasProvenance)

AbiPointerLikeSourceProvenancePolicy =
    ConservativeUnknownHandleSourceProvenance
  | DeclaredHandleSourceProvenance(PhysicalStorageSourceProvenance)

abiFormalHandleSourceProvenance(ConservativeUnknownHandleSourceProvenance) = {}
abiFormalHandleSourceProvenance(DeclaredHandleSourceProvenance(facts)) = facts

AbiPointerLikeInputContract = {
    valueType: TypeId,
    typeProjection: PointerLikeTypeProjection,
    kind: PointerLikeKind,
    referent: TypeId,
    addressSpace: AddressSpaceRequirement,
    access: StorageAccessMode,
    mutability: AbiPointerLikeMutabilityPolicy,
    lifetime: AbiPointerLikeLifetimePolicy,
    alias: AbiPointerLikeAliasPolicy,
    sourceProvenance: AbiPointerLikeSourceProvenancePolicy
}

AbiFixedPointerLikeResultContract = {
    formalShape: PointerLikeValueShape
}

AbiAccessorPointerLikeResultContract = {
    resultType: TypeId,
    contract: AccessorReferenceResultContractId
}

AbiRegisteredPointerLikeResultContract = {
    resultType: TypeId,
    registration: ReferenceOperationRegistration,
    staticInputs: CanonicalArguments,
    environment: StandardEnvironmentId
}

AbiPointerLikeResultContract =
    FixedPointerLikeResult(AbiFixedPointerLikeResultContract)
  | AccessorPointerLikeResult(AbiAccessorPointerLikeResultContract)
  | RegisteredPointerLikeResult(AbiRegisteredPointerLikeResultContract)

FunctionAbiInputShape =
    RuntimeAbiInput(type: TypeId, mode: ParamPassingMode)
  | PointerLikeAbiInput(contract: AbiPointerLikeInputContract,
                            mode: ParamPassingMode)
  | PhysicalStorageAbiInput(contract: AbiPhysicalStorageInputContract)
  | InitializationTargetAbiInputShape(target: InitializationTargetSlot)
  | GenericMetadataAbiInput(sort: GenericParameterSort)
  | SubtypeWitnessAbiInput(target: SubtypeWitnessTarget)
  | OtherConstraintEvidenceAbiInput(kind: ConstraintKind)

FunctionAbiInput = {
    ordinal: UInt32,
    shape: FunctionAbiInputShape
}

FunctionAbiResultRole = NormalAbiResult | ErrorAbiResult

FunctionAbiResultShape =
    RuntimeAbiResult(type: TypeId)
  | PointerLikeAbiResult(contract: AbiPointerLikeResultContract)

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

AbiPointerLikeAddressSpaceBindingProof = {
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
    PointerLikeAddressSpaceBinding(AbiPointerLikeAddressSpaceBindingProof)
  | PhysicalStorageAddressSpaceBinding(AbiPhysicalStorageAddressSpaceBindingProof)

AbiAliasViewProof =
    PreserveAliasView(AliasProvenanceEqualityProof)
  | ForgetAliasToUnknown(actual: AliasProvenance)

AbiMutabilityViewProof =
    PreserveMutabilityView(MutabilityEqualityProof)
  | ReadOnlyViewOfMutable
  | ForgetMutabilityToUnknown(actual: Mutability)

AbiPointerLikeSourceProvenanceViewProof = {
    actual: PhysicalStorageSourceProvenance,
    formal: PhysicalStorageSourceProvenance,
    inclusion: CanonicalSetInclusionProof<PhysicalStorageSourceFact>
}

AbiPointerLikeInputAdmissionProof = {
    contract: AbiPointerLikeInputContract,
    actual: PointerLikeValueShape,
    instantiatedFormal: PointerLikeValueShape,
    typeEquality: TypeEqualityProofId,
    referentEquality: TypeEqualityProofId,
    addressSpaceBinding: AbiPointerLikeAddressSpaceBindingProof,
    accessProof: AccessProvisionProof,
    lifetimeProof: OutlivesProof,
    mutabilityView: AbiMutabilityViewProof,
    aliasView: AbiAliasViewProof,
    sourceProvenanceView: AbiPointerLikeSourceProvenanceViewProof
}

AbiPhysicalStorageInputAdmissionProof = {
    contract: AbiPhysicalStorageInputContract,
    actualStorage: PhysicalStorageRef,
    actual: IRPhysicalStorageShape,
    instantiatedFormal: IRPhysicalStorageShape,
    mode: ParamPassingMode,
    identity: PhysicalStorageIdentityProof,
    addressSpaceBinding: AbiPhysicalStorageAddressSpaceBindingProof,
    accessProof: AccessProvisionProof,
    lifetimeProof: OutlivesProof,
    mutabilityView: AbiMutabilityViewProof,
    aliasView: AbiAliasViewProof,
    sourceProof: PhysicalStorageSourceAdmissionProof
}

AbiInputAdmissionProof =
    RuntimeInputAdmission(type: TypeId, mode: ParamPassingMode)
  | PointerLikeInputAdmission(AbiPointerLikeInputAdmissionProof)
  | PhysicalStorageInputAdmission(AbiPhysicalStorageInputAdmissionProof)
  | InitializationTargetInputAdmission(InitializationTargetSlot)
  | GenericMetadataInputAdmission(variable: CanonicalBoundVariable)
  | SubtypeWitnessInputAdmission(SubtypeWitnessTarget)
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
    contract: AbiFixedPointerLikeResultContract,
    result: PointerLikeValueShape
}

AbiAccessorReferenceResultInstantiation = {
    contract: AbiAccessorPointerLikeResultContract,
    invocationIdentity: AccessorInvocationIdentity,
    sources: CanonicallyOrderedMap<AccessorProvenanceSourceRole,
                                   AbiCapturedSourceBinding>,
    derivation: AccessorReferenceResultDerivation,
    result: PointerLikeValueShape
}

AbiRegisteredReferenceResultInstantiation = {
    contract: AbiRegisteredPointerLikeResultContract,
    result: PointerLikeValueShape,
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
  | FixedReferenceResultContractProof(AbiFixedPointerLikeResultContract)
  | AccessorReferenceResultContractProof(
        contract: AbiAccessorPointerLikeResultContract,
        derivation: AccessorReferenceResultDerivation)
  | RegisteredReferenceResultContractProof(
        contract: AbiRegisteredPointerLikeResultContract,
        derivation: RegisteredReferenceResultDerivation)

instantiateAbiPointerLikeInput(
    contract: AbiPointerLikeInputContract,
    role: FunctionAbiInputRole,
    call: AbiCallInstantiation)
    -> PointerLikeValueShape

formalAbiPointerLikeInput(
    contract: AbiPointerLikeInputContract,
    role: FunctionAbiInputRole,
    context: FunctionAbiContext)
    -> PointerLikeValueShape

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

IRFunctionDeclShape = {
    signature: CallableSignatureId,
    resultAuthority: CallableResultAuthorityId,
    contract: EffectiveCallableContractId,
    abi: FunctionAbiMap
}

IRTypeDeclShape = {
    type: TypeId,
    definition: ContentId<Val>
}

IRGlobalDeclShape = {
    type: TypeId,
    mutability: Mutability,
    addressSpace: AddressSpace
}

IRWitnessTableDeclShape = {
    definition: ValidatedWitnessTableRef,
    form: WitnessTableForm,
    metadataEntries: CanonicallyOrderedSet<SomeInterfaceRequirementKey>,
    runtimeSlots: CanonicallyOrderedMap<RuntimeInterfaceRequirementKey, UInt32>
}

IRDeclShape =
    FunctionDeclShape(IRFunctionDeclShape)
  | TypeDeclShape(IRTypeDeclShape)
  | GlobalDeclShape(IRGlobalDeclShape)
  | WitnessTableDeclShape(IRWitnessTableDeclShape)

IRDeclShapeId = ContentId<IRDeclShape>

IRSymbolDecl = {
    symbol: IRSymbolId,
    key: IRSymbolKey,
    shape: IRDeclShape,
    origin: Origin
}

IRSymbolLinkage =
    LocalModule(ModuleStableId)
  | ImportedInterface(ModuleInterfaceContentId)

IRSymbolRef = {
    symbol: IRSymbolId,
    expectedShape: IRDeclShapeId,
    linkage: IRSymbolLinkage
}

IRStaticData<T> = {
    id: ContentId<T>,
    value: T
}

IRCapabilityUseRequirement =
    IRDirectCapabilityRequirement(CapabilityRequirement)
  | IRLocalCallableCapabilityRequirement(DeclRef)
  | IRImportedCallableCapabilityRequirement(CapabilityRequirement)
  | IRWitnessEntryCapabilityRequirement(witness: SubtypeWitnessId,
                                        entry: RuntimeInterfaceRequirementKey)

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

CallCapabilitySemanticMetadata = {
    capabilities: IRCapabilitySelection,
    projection: IRCapabilitySelectionProjectionProof
}

ProjectCapabilitySelectionToIR(selection: CapabilitySelection)
    -> CheckResult<CallCapabilitySemanticMetadata>

IRPointerLikeShape = PointerLikeValueShape

IRReferenceEndpointShape =
    IRPointerLikeEndpoint(IRPointerLikeShape)
  | IRPhysicalStorageEndpoint(IRPhysicalStorageShape)

RegisteredReferenceInstApplicationSite =
    DirectReferenceProducerSite
  | AccessorResultTransformSite
  | ReferenceDereferenceSite

RegisteredReferenceInstApplication = {
    registration: ReferenceOperationRegistration,
    site: RegisteredReferenceInstApplicationSite,
    input: IRReferenceEndpointShape,
    output: IRReferenceEndpointShape,
    control: ReferenceDataOperationControlShape
}

AddressOfInstSemanticPlan = {
    input: IRPhysicalStorageShape,
    output: IRPointerLikeShape,
    proof: DirectStorageHandleProof
}

IRCallableContractSubjectEvidence =
    DirectIRContractSubject(
        declaration: DeclRef,
        target: IRSymbolRef)
  | WitnessIRContractSubject(
        witness: SubtypeWitnessId,
        entry: RuntimeInterfaceRequirementKey,
        witnessOperand: IRValueId,
        resolutions: WitnessResolutionStamp)
  | DynamicIRContractSubject(owner: TypeId, slot: DynamicDispatchKey)
  | LambdaIRContractSubject(invoke: DeclRef, target: IRSymbolRef)
  | BuiltinIRContractSubject(rule: RuleId,
                             registration: StandardEnvironmentRuleId,
                             operands: CanonicalArguments)

RegisteredReferenceResultDerivation = {
    registration: ReferenceOperationRegistration,
    environment: StandardEnvironmentId,
    staticInputs: CanonicalArguments,
    runtimeInputs: NodeList<IRValueId>,
    result: PointerLikeValueShape
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
    result: PointerLikeValueShape
}

DereferenceInstSemanticPlan = {
    identity: DereferenceApplicationIdentity,
    input: IRPointerLikeShape,
    resultProof: DereferencedStorageProof,
    output: IRPhysicalStorageShape
}

RegisteredDereferenceInstApplication = {
    operation: RegisteredReferenceInstApplication,
    projection: DereferenceInstSemanticPlan
}

BuiltinPhysicalProjectionInstSemanticPlan = {
    identity: BuiltinPhysicalProjectionIdentity,
    operation: BuiltinPhysicalProjectionOperation,
    inputShapes:
        CanonicallyOrderedMap<BuiltinPhysicalProjectionOperandRole, IRValueShape>,
    evaluationOrder: NodeList<BuiltinPhysicalProjectionOperandRole>,
    resultProof: BuiltinPhysicalProjectionResultProof,
    output: IRPhysicalStorageShape,
    control: BuiltinPhysicalProjectionControlProof
}

RegisteredPhysicalProjectionInstSemanticPlan = {
    identity: RegisteredPhysicalProjectionIdentity,
    registration: RegisteredDataOperationRegistration,
    inputShapes:
        CanonicallyOrderedMap<RegisteredPhysicalProjectionOperandRole, IRValueShape>,
    evaluationOrder: NodeList<RegisteredPhysicalProjectionOperandRole>,
    resultProof: RegisteredPhysicalProjectionResultProof,
    output: IRPhysicalStorageShape,
    control: RegisteredPhysicalProjectionControlProof
}

ReferenceInstSemanticPlan =
    AddressOfInstPlan(descriptor: IRStaticData<AddressOfInstSemanticPlan>)
  | AccessorReferenceResultInstPlan(
        certificate: LoweredAccessorReferenceResultCertificate)
  | RegisteredReferenceProducerInstPlan(
        application: IRStaticData<RegisteredReferenceInstApplication>)
  | ReferenceDereferenceInstPlan(
        descriptor: IRStaticData<DereferenceInstSemanticPlan>)
  | PointerDereferenceInstPlan(
        descriptor: IRStaticData<DereferenceInstSemanticPlan>)
  | RegisteredReferenceDereferenceInstPlan(
        application: IRStaticData<RegisteredDereferenceInstApplication>)

PhysicalStorageInstSemanticPlan =
    BuiltinPhysicalProjectionInstPlan(
        descriptor: IRStaticData<BuiltinPhysicalProjectionInstSemanticPlan>)
  | RegisteredPhysicalProjectionInstPlan(
        descriptor: IRStaticData<RegisteredPhysicalProjectionInstSemanticPlan>)

TemporaryInitializationInstSemanticPlan = {
    storage: IRTemporaryStorageShape,
    application: TemporaryInitializationPlanApplicationAt<Published>,
    effects: EffectSet
}

TemporaryDestructionInstSemanticPlan = {
    storage: IRTemporaryStorageShape,
    plan: DestructionPlanAt<Published>,
    effects: EffectSet,
    nonThrowing: NonThrowingDestructionProof
}

StorageAccessInstSemanticPlan =
    MaterializeTemporaryInstPlan(
        descriptor: IRStaticData<IRTemporaryStorageShape>)
  | InitializeTemporaryInstPlan(
        descriptor: IRStaticData<TemporaryInitializationInstSemanticPlan>)
  | DestroyTemporaryInstPlan(
        descriptor: IRStaticData<TemporaryDestructionInstSemanticPlan>)

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
  | IRInstResultValue(instruction: IRInstId, ordinal: UInt32,
                           shape: IRValueShape)

IRValueId = ContentId<IRValueKey>

IRValueOperand =
    LocalIRValue(IRValueId)
  | SymbolIRValue(IRSymbolRef)

IRInstOperand =
    ValueOperand(IRValueOperand)
  | BlockOperand(IRBlockId)

IRParam = {
    value: IRValueId,
    shape: IRValueShape
}

IRSuccessor = {
    block: IRBlockId,
    arguments: NodeList<IRValueOperand>
}

IRInterfaceRequirementKeyValue =
    SubtypeWitnessRequirementKey(key: SubtypeWitnessLookupKey)
  | GeneralInterfaceRequirementKey(key: SomeInterfaceRequirementKey)

CallInstSemanticMetadata = {
    abi: FunctionAbiMapId,
    instantiation: AbiCallInstantiation,
    capabilities: CallCapabilitySemanticMetadata
}

RegisteredDataInstSemanticPlan = {
    registration: RegisteredDataOperationRegistration,
    immediates: CanonicalArguments
}

ExistentialWitnessExtractionInstSemanticPlan = {
    interface: InterfaceInstanceKey,
    result: SubtypeWitnessForm
}

DetachDerivativeInstSemanticPlan = {
    boundary: DetachDerivativeBoundaryId
}

IRInstSemanticMetadata = {
    registeredData: Option<RegisteredDataInstSemanticPlan>,
    initialization: Option<InitializationInstSemanticPlan>,
    storageAccess: Option<StorageAccessInstSemanticPlan>,
    physicalStorage: Option<PhysicalStorageInstSemanticPlan>,
    reference: Option<ReferenceInstSemanticPlan>,
    call: Option<CallInstSemanticMetadata>,
    specialization: Option<CanonicalSpecializationSpine>,
    existentialWitnessExtraction:
        Option<ExistentialWitnessExtractionInstSemanticPlan>,
    derivativeSelection: Option<DerivativeSelectionInstSemanticPlan>,
    detachDerivative: Option<DetachDerivativeInstSemanticPlan>,
    recoveryError: Option<ErrorId>
}

IRInstSemanticMetadataEntry = {
    instruction: IRInstId,
    metadata: IRInstSemanticMetadata
}

IROp = generated codebase opcode discriminator

registeredIROp(registration: StandardEnvironmentRuleId) -> IROp
selectedIROp(plan: ReferenceInstSemanticPlan | PhysicalStorageInstSemanticPlan |
                    StorageAccessInstSemanticPlan | InitializationInstSemanticPlan)
    -> IROp

IRInstRecord = {
    id: IRInstId,
    key: IRInstKey,
    op: IROp,
    operands: NodeList<IRInstOperand>,
    results: NodeList<IRValueShape>
}

IRBlock = {
    id: IRBlockId,
    key: IRBlockKey,
    parameters: NodeList<IRParam>,
    instructions: NonEmpty<IRInstRecord>
}

IRControlFlowGraph = {
    entry: IRBlockId,
    blocks: NodeMap<IRBlockId, IRBlock>,
    blockOrder: NodeList<IRBlockId>,
    semanticMetadata:
        NodeMap<IRInstId, IRInstSemanticMetadataEntry>
}

IRFunctionDefinitionBody = {
    abi: FunctionAbiMapId,
    graph: IRControlFlowGraph
}

IRGlobalDefinitionBody = {
    initializer: IRControlFlowGraph
}

IRWitnessTableDefinitionBody = {
    definition: ValidatedWitnessTableRef,
    metadataEntries:
        CanonicallyOrderedMap<SomeInterfaceRequirementKey, ContentId<Val>>,
    runtimeEntries:
        CanonicallyOrderedMap<RuntimeInterfaceRequirementKey, IRSymbolRef>
}

IRDefinitionBody =
    FunctionDefinitionBody(IRFunctionDefinitionBody)
  | GlobalDefinitionBody(IRGlobalDefinitionBody)
  | WitnessTableDefinitionBody(IRWitnessTableDefinitionBody)

IRDefinition = {
    symbol: IRSymbolId,
    declaredShape: IRDeclShapeId,
    body: IRDefinitionBody
}

IRDependencyKey =
    TypeDependency(TypeId)
  | ContractDependency(EffectiveCallableContractId)
  | DeclDependency(DeclRef)
  | WitnessTableDependency(ValidatedWitnessTableRef)
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
    declarations: CanonicallyOrderedMap<IRSymbolId, IRSymbolDecl>,
    definitions: CanonicallyOrderedMap<IRSymbolId, IRDefinition>,
    references: CanonicallyOrderedSet<IRSymbolRef>,
    sourceMap: NodeMap<IRInstId, Origin>,
    requirements: CanonicallyOrderedMap<IRDependencyKey, IRDependency>
}
```

`IROp` is the same generated opcode discriminator used by the codebase. It has no fields: an
instruction's type, ABI map, capability proof, witness key, initialization plan, or derivative
provider is never payload inside an `IROp`. A standard-environment registration resolves to an
actual generated opcode through `registeredIROp`; `selectedIROp` applies the corresponding
registered lowering rule to a storage, reference, or initialization plan. These functions select an
opcode and do not manufacture a new `IR...` operation class.

Write `V(x)` for `ValueOperand(x)` and `B(x)` for `BlockOperand(x)`. The existing generated
instructions used directly by this frontend subset have these exact operand sequences:

| generated instruction              | operands, in order                                                            |
| ---------------------------------- | ----------------------------------------------------------------------------- |
| `IRCall`                           | `V(callee), V(argument)*`                                                     |
| `IRSpecialize`                     | `V(base), V(genericOrWitnessArgument)*`                                       |
| `IRLookupWitnessMethod`            | `V(witnessTable), V(requirementKey)`                                          |
| `IRExtractExistentialWitnessTable` | `V(existential)`                                                              |
| `IRForwardDifferentiate`           | `V(base)`                                                                     |
| `IRBackwardDifferentiate`          | `V(applyFunction), V(contextType), V(backwardPropagateFunction)`              |
| `IRDetachDerivative`               | `V(value)`                                                                    |
| `IRUnconditionalBranch`            | `B(target), V(targetArgument)*`                                               |
| `IRConditionalBranch`              | `V(condition), B(trueBlock), B(falseBlock)`                                   |
| `IRSwitch`                         | `V(condition), B(breakLabel), B(defaultLabel), (V(caseValue), B(caseLabel))*` |
| `IRReturn`                         | zero operands for a void return, otherwise `V(value)`                         |
| `IRThrow`                          | `V(error)`                                                                    |
| `IRUnreachable`                    | no operands                                                                   |
| `IRPoison`                         | no operands; diagnostic/tooling recovery only                                 |

Other actual opcodes admitted to frontend IR are selected by a registered schema that declares
their operands, results, and effects. Chapter 16 defines `InitializationInstSemanticPlan`; chapter
16 defines `DerivativeSelectionInstSemanticPlan`. They are sidecar plans, not opcode alternatives.
Every instruction has exactly one entry in `IRControlFlowGraph.semanticMetadata`, including the
all-`None` entry. The map key and `entry.instruction` both equal the instruction ID. Validation
checks every present facet against `record.op`: `call` requires `IRCall`, `specialization` requires
`IRSpecialize`, existential extraction requires `IRExtractExistentialWitnessTable`, derivative and
detach facets require their exact generated opcodes, and every registered/storage/reference/
initialization facet must select that same opcode. Orthogonal facets may coexist only when the
emission recipe requires them; for example, a constructor call has both `initialization` and `call`
metadata on one `IRCall`, and a reference-accessor call has both `reference` and `call` metadata on
its producing `IRCall`. `recoveryError` requires `IRPoison`; control-flow instructions have the
all-`None` entry. No semantic fact is reconstructed from the opcode alone.

`successors(record)` is a derived view, never stored authority. `IRUnconditionalBranch` contributes
its target and remaining value operands as block arguments; `IRConditionalBranch` contributes its
true and false targets with no block arguments; `IRSwitch` contributes its default and case labels
in operand order, while `breakLabel` is its structured reconvergence target rather than a direct
edge. Other instructions contribute no successors.

`IR-VAL-001`: A IRReady ordinary runtime rvalue lowers to `RuntimeValueShape(type)`. A IRReady
`PointerLikeValue(handle)` lowers to
`PointerLikeIRValueShape(PointerLikeValueShape(type, handle))`, and a IRReady
`PhysicalStorage(IRReadyPhysicalStorageShape)` lowers to
`PhysicalStorageValueShape(IRPhysicalStorageShape)` with the outer runtime type as `valueType` and
identical access, mutability, physical address space, lifetime, alias, and source provenance.
Physical parameter forwarding therefore remains symbolic; only first-class handle formation
consumes a separate `ConcreteAddressSpaceProjectionProof`. Generic metadata, subtype witnesses,
witness entries, and other constraint evidence lower respectively to
`GenericMetadataShape(variable, variable.sort)`, `SubtypeWitnessValueShape`, `WitnessEntryShape`, and
`OtherConstraintEvidenceShape(slot.kind)`. The enclosing ABI/input role retains the complete
variable or constraint-slot key. A IRReady value cannot be reclassified among ordinary runtime data,
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
requirement map key equals `requirement.key`. The semantic-metadata map is a duplicate-free
bijection onto the graph's instructions, and every map key equals its entry's `instruction`. No
identity depends on allocation, pointer, worker, or hash-map iteration order.

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
`PointerLikeAbiInput(contract, _)` becomes
`PointerLikeIRValueShape(formalAbiPointerLikeInput(contract, role, abi.context))`, a
`PhysicalStorageAbiInput(contract)` becomes
`PhysicalStorageValueShape(contract.formalShape)`, generic input becomes
`GenericMetadataShape(role.variable, shape.sort)`, an initialization target becomes
`InitializationTargetShape(shape.target)`, a subtype-witness input becomes
`SubtypeWitnessValueShape(AbstractSubtypeWitness(shape.target))`, and other constraint evidence becomes
`OtherConstraintEvidenceShape(shape.kind)`. The `WitnessAbiInput(witness)` role equals
`ContentId(CanonicalSubtypeWitness(shape.target))`; the source constraint slot remains binder
provenance and cannot create a second ABI role for the same endpoint pair. A global initializer has no entry
parameters and every normal
return supplies one runtime value of the declared global type. A conformance body is validated by
`IR-CON-001`. These endpoint checks prevent a structurally valid body from being attached to the
wrong declaration.

`IR-SSA-001`: `blockOrder` is a duplicate-free bijection onto `blocks`, starts with `entry`, and is
the deterministic structured-lowering order. Every block ends in exactly one of
`IRUnconditionalBranch`, `IRConditionalBranch`, `IRSwitch`, `IRReturn`, `IRThrow`, or
`IRUnreachable`, and no earlier instruction in the block is a terminator. Operand kinds and counts
are exactly those in the table above. The derived successor argument count and shapes equal the
destination block parameters; consequently the targets of `IRConditionalBranch` and the direct
default/case targets of `IRSwitch` have no parameters supplied by that edge. Every
`LocalIRValue` resolves in the same definition and is dominated by its block parameter or producing
instruction; same-block uses are strictly after the producer. Every `SymbolIRValue` resolves under
`IR-RES-001`, and every `BlockOperand` names a block in the same graph. Instruction results, block
parameters, symbol refs, and block operands occupy distinct domains and cannot be interchanged.

`IR-SSA-002`: A registered frontend-IR schema declares one actual `IROp`, its operand roles, result
shapes, immediate schema, effects, and whether that opcode is valid at this stage. Its semantic
metadata stores the resolved registration and proof plan, and `registeredIROp(registration.rule)`
must equal `record.op`. Storage, reference, and initialization metadata instead use
`selectedIROp(plan) = record.op`; their schemas validate the exact endpoint mappings,
operation-qualified orders, target and source proofs, allocation ownership, transfer, and cleanup
facts. Every physical-storage operand/result uses `PhysicalStorageValueShape` and retains its exact
value type, access, mutability, address space, lifetime, alias, and source provenance.

An `IRCall` has one `call` metadata facet and no non-call instruction may have one. Operand zero is
the callable value; ABI inputs occupy indices `1 + ordinal` for direct, witness, dynamic, lambda,
and registered-primitive dispatch alike. `call.abi = call.instantiation.abi`; activation and
address-space bindings validate under `IR-ABI-003`, and each ABI operand has the successful
`admitAbiInput` proof for its named role and formal shape under that exact instantiation. Witness
dispatch first produces the callable with `IRLookupWitnessMethod`; neither the witness table nor a
requirement key is an extra dispatch prefix of `IRCall`. Instruction result ordinal and shape equal
the corresponding `instantiation.results` entry; a formal result contract is never used as if it
were a concrete SSA shape. Return and throw operands instead require a successful
`proveAbiDefinitionResult` for the containing function's normal and error result contracts and
formal entry inputs. This validates the body against its reusable declaration contract without
importing a caller invocation lifetime. `IRPoison` is accepted only under `IR-005`, has
`recoveryError = Some(error)`, and its result shapes retain that `ErrorId`.

`IR-REF-001`: Every instruction with `metadata.reference = Some(plan)` has no successors.
`AddressOfInstPlan` has exactly one
`PhysicalStorageValueShape(descriptor.input)` operand and one
`PointerLikeIRValueShape(descriptor.output)` result; `descriptor.proof.storage` projects to the
input, `descriptor.proof.handle` projects to the output, and its access, mutability, lifetime,
concrete address-space projection, alias, and source-provenance relations all validate.
`AccessorReferenceResultInstPlan` occurs only as an orthogonal facet on the producing `IRCall`.
Its certificate identifies one existing
`PointerLikeIRValueShape(certificate.result)` call result; it emits no wrapper instruction and adds
no operand or result. Consequently `selectedIROp(AccessorReferenceResultInstPlan(_)) = IRCall`.
Builtin reference/pointer dereference has one
`PointerLikeIRValueShape(descriptor.input)` operand and one
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
IRReady application, then projects that value to `RegisteredReferenceInstApplication`. The IRReady
boundary removes typed node IDs, diagnostic origins, semantic-use edges, and selection proofs only
after those facts have been validated and consumed. It preserves the
exact registration/environment/static inputs, operation site, runtime endpoint shapes, and
unary/nonthrowing control shape. For direct and transform producers, the separate IRReady storage/handle
operand equals the checked `input.operand` elaboration and the IRReady application's stored endpoint
proofs equal the checked input/output; an equal-shaped replacement is not that projection. The
resulting `IRStaticData` contains no AST reference. Address-of
and builtin dereference descriptors similarly retain the complete handle and physical-storage
shapes needed to replay their endpoint equations. A dereference descriptor additionally retains
the stage-free physical-projection identity and complete `DereferencedStorageProof`; its executable
handle remains the instruction operand, not a path payload. A registered dereference packages that
descriptor with the projected registered operation rather than erasing either proof. The Typed-to-
IRReady boundary has already projected an `AccessorReferenceResultCertificate` to the stage-free
`IRReadyAccessorReferenceResultProof`, after validating its exact typed call, subject, signature,
referent, result shape, source set, and instantiation proof. IR lowering projects that IRReady proof
together with the already emitted call to `LoweredAccessorReferenceResultCertificate`: the exact producer instruction
and normal-result ordinal, the producer's `AbiCallInstantiationId`, stage-free callable-subject
evidence, declaration-stable accessor-role-to-producer-operand bindings and pack projections, the
stage-free `AccessorInvocationIdentity`, referent equality, five component derivations, and the
complete result shape. Typed node IDs, typed
source expressions, origins, semantic-use
edges, and stage-specific resolution sidecars are removed. The projection contains no AST reference
and is replayable using only the frozen IR graph and semantic/standard-environment dependencies.

`IR-REF-003`: A generic registered-data plan never produces `PhysicalStorageValueShape`. The closed
frontend-IR producers of that shape are storage declarations/projections, initialization or
allocation storage, instructions carrying
`PhysicalStorageInstSemanticPlan.BuiltinPhysicalProjectionInstPlan` or
`PhysicalStorageInstSemanticPlan.RegisteredPhysicalProjectionInstPlan`, and the three dereference
plans. A registered
physical projection's descriptor validates all input shapes and its exact output against the
`RegisteredPhysicalProjectionResultProof` from `TYP-STO-003`/`TYP-STO-010`; sharing a target opcode with an
ordinary data operation cannot bypass this alternative.

`IR-STO-001`: Initial lowering maps each `IRReadyRegisteredPhysicalProjection` to an instruction
carrying `RegisteredPhysicalProjectionInstPlan`; its actual opcode is
`registeredIROp(descriptor.registration.rule)`. The instruction operands are the IRReady
`runtimeOperands[role]` lowered in `evaluationOrder`; the descriptor's `inputShapes` has exactly
that role domain, and each operand shape equals its named entry. Descriptor identity, registration
(including `StandardEnvironmentId` and static inputs), evaluation order, result proof, and control
proof are copied from IRReady. `resultProof.identity = descriptor.identity`,
`resultProof.registration = descriptor.registration`, and its storage path is
`RegisteredPhysicalProjection(identity)`. Projecting that storage yields exactly
`descriptor.output`, the instruction's sole `PhysicalStorageValueShape` result. The result proof's
type equality and access/mutability/lifetime/address-space/alias/source-provenance derivations replay against the
descriptor's named runtime endpoints and registered schema without an AST node or ambient target
lookup. A later use-specific `PhysicalStorageProof` is not serialized as part of the producer.

`IR-STO-002`: Initial lowering maps each `IRReadyBuiltinPhysicalProjection` to an instruction
carrying `BuiltinPhysicalProjectionInstPlan`; the plan's registered lowering rule selects its actual
opcode. Its two instruction operands are the IRReady base and
index values lowered in the stored evaluation order, and the descriptor's `inputShapes` has exactly
those two roles with their exact shapes. Identity, operation, order, result proof, and control proof
are copied from IRReady. `resultProof.identity = descriptor.identity`, its input storage is the
physical storage obtained from the base operand by the closed IR physical-storage provenance
relation, not merely an equal `IRPhysicalStorageShape`, and its path is
`BuiltinElement(resultProof.inputStorage.path, descriptor.identity)`. Projecting the result storage
yields exactly `descriptor.output`, the instruction's sole `PhysicalStorageValueShape` result.
Validation replays the named builtin rule against the two runtime endpoints without an AST node,
origin, or reconstructed index. The descriptor and every transitive `IRStaticData` field are
stage-free. A generic data operation or registered physical projection cannot
substitute for this producer.

`IR-REF-004`: Initial lowering maps `IRReadyAddressOfPhysicalStorage` one-to-one to
`AddressOfInstPlan`, attaches `AccessorReferenceResultInstPlan` to the exact `IRCall` that produced
an `IRReadyAccessorReferenceResult`, and maps
registered direct and handle-transform producers to
`RegisteredReferenceProducerInstPlan` with their distinct site, builtin reference/pointer
dereferences to the corresponding distinct IR alternative, and registered dereference to
`RegisteredReferenceDereferenceInstPlan`. Each plan selects an existing generated or registered
`IROp`; none of these plan names is an opcode. Every dereference descriptor copies the IRReady proof's
identity and complete proof; its output path is `DereferencedReference(identity)`, its input shape
is the projection of that proof's handle, and its output shape is the projection of the proof's
storage. The registered alternative additionally requires
`application.operation.input/output` to equal the projection descriptor's endpoints and packages
the exact stage-free `IRReadyRegisteredDereferenceApplication` registration, input/output proof, and
control shape rather than reconstructing them. Lowering does not fuse adjacent
accessor-call, transform, or dereference instructions, and it never reconstructs a registration,
endpoint, or stable identity from a runtime type or `IRInstId`.

`IR-REF-005`: For an `IRCall` record `r` carrying
`AccessorReferenceResultInstPlan(certificate)`, let `c = certificate`.
`c.normalResult.role = NormalAbiResult`, `c.normalResult.producer = r.id`, and the call metadata
instantiation has `ContentId(instantiation) = c.normalResult.instantiation`. Its ABI maps
`NormalAbiResult` to `c.normalResult.ordinal`, and result ordinal `c.normalResult.ordinal` is exactly
`PointerLikeIRValueShape(c.result)`. The certificate cannot name a block parameter, copy, sibling
call, another result ordinal, or arbitrary equal-shaped value. No wrapper result exists.

The producer ABI signature equals `c.signature`, and `c.subject` is byte-identical to the
producer instantiation's subject evidence. A witness subject repeats the exact
`SubtypeWitnessId`, runtime-entry key, witness SSA operand, and frozen resolution evidence;
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
step consults a typed node. The certificate sidecar therefore authenticates a proof-carrying
result already created by the call; it never creates provenance by reclassification.
For `FreshAccessorAlias`,
`c.derivation.alias.invocationIdentity = Some(c.invocationIdentity)`, and replay derives the exact
`AccessorInvocationAliasRegion(c.invocationIdentity)`. For every other alias rule the field is
`None`. An IR producer ID is never
used as a replacement seed, so moving or deduplicating instructions cannot change alias identity.

`IR-TMP-001`: An instruction carrying `MaterializeTemporaryInstPlan(d)` has no operands and one
`TemporaryStorageValueShape(d)` result representing raw plan-owned storage. Its nominal
`TemporaryStorageIdentity` is copied from the authenticated application site and its alias is
exactly `ExactAliasRoot(temporaryStorageAliasRoot(d.identity))`; no IRReady/IR instruction identity or
raw `StableSemanticId` may replace it.
An instruction carrying `InitializeTemporaryInstPlan(i)` is the normal-checkpoint marker for the exact chapter 16
application in `i.application`: it has that temporary as its sole operand and no result, and is
dominated by the complete lowered initialization-recipe instructions. Every exceptional exit before the
marker executes the application's stored cleanup and cannot reach outer destruction. Before the
marker, the raw temporary value may be used only as that initialization plan's target or
exceptional-cleanup storage; the marker must dominate whole-object write-back and destruction.
`i.effects` is copied from the published initialization plan rather than reconstructed from the
value type. An instruction carrying `DestroyTemporaryInstPlan(d)` consumes one
`TemporaryStorageValueShape(d.storage)`; `d.plan`, `d.effects`, and `d.nonThrowing` are the exact
stage-free projection of `IRReadyDestroyTemporary`. These operations support only named
abstract-domain `OutMode`/`InOutMode` preparation and cleanup. They cannot produce
`PhysicalStorageValueShape` and cannot occur in a `ConstRefMode` or `RefMode` call-slot plan.

`IR-PHY-001`: Lowering a physical-domain call operand preserves one
`PhysicalStorageValueShape(actual)` from the selected IRReady physical-storage value through the call.
The corresponding `PhysicalStorageInputAdmission` is at the same ABI role and has
`admission.mode` byte-identical to the signature mode. Its identity proof, access proof, lifetime
proof, address-space binding, source-provenance proof, mutability view, and alias view replay the
exact stage-free `IRReadyPhysicalParameterInputProof`, which was validated as the projection of the
selected `PhysicalParameterBindingProofAt<Published>` before stage-specific source syntax was
erased. `admission.actualStorage` is that IRReady proof's complete endpoint and projects to
`admission.actual`, so the source proof and nominal storage path are not reconstructed from an IR
shape. Its `PhysicalStorageSourceAdmissionProof.provenanceProof` is the byte-identical generic
`PhysicalSourceProvenanceAdmissionProof` selected at checking time.
For `ConstRefMode`, the admitted view has `ReadAccess` and does not claim immutable underlying
storage; for `RefMode`, it has `ReadWriteAccess` and mutable storage. No runtime value, reference
handle, or temporary-storage result can satisfy this admission merely by sharing a `TypeId` or
machine representation.

`IR-PHY-002`: An accessor-produced physical argument retains a distinct `IRCall` carrying
`AccessorReferenceResultInstPlan`, followed by the optional registered handle transform and the
dereference instruction. The physical call operand is exactly the dereference instruction's
`PhysicalStorageValueShape` result, whose descriptor retains the authenticated
`DereferenceApplicationIdentity`, handle input, and `DereferencedStorageProof`. A direct physical
argument instead retains its existing physical producer. Initial lowering may not fuse either path,
substitute an equal-shaped producer, insert a load, or reconstruct the endpoint from a property
type. Thus both paths have the same physical ABI admission without erasing how the endpoint was
proved.

`IR-CALL-001`: Every IRReady `DirectCall`, `WitnessCall`, `DynamicCall`, `LambdaCall`, and
`PrimitiveCall` emits exactly one `IRCall` after explicitly materializing its callee. Direct and
lambda callees are the resolved function symbol or an `IRSpecialize` result. A witness callee is the
result of `IRLookupWitnessMethod(witnessTable, requirementKey)`. Dynamic dispatch emits its
registered callable-selection instruction first, and a primitive call obtains the registered
callable value named by its rule; each result is then operand zero of `IRCall`. No dispatch kind is
encoded by a distinct call opcode, and the witness table or dynamic receiver is not substituted for
the selected callable.

The call's ABI inputs follow the callee at indices `1 + ordinal`. Its metadata ABI map has the
IRReady contract signature, and
`FunctionAbiMap.resultAuthority` is byte-identical to the IRReady contract authority and resolves to
the same callable anchor; the call-local result instantiation must select the ABI result
alternative derived from that authority kind. IRReady receiver,
initialization-target, parameter, residual-generic, and witness inputs are projected by ABI input
role and emitted by
ordinal. Lowering constructs exactly one call-local `AbiCallInstantiation`: its activation binds the
IRReady contract's `callerInvocationLifetime`, its address-space substitution is the selected call
specialization, its input admissions are the exact role-keyed proofs for the emitted operands, its
`aliasCompatibility` is byte-identical to the IRReady call contract, its subject evidence is the
stage-free projection of the IRReady dispatch, and its result entries are the
exact projection of `ElaboratedCallAt.resultProvenance`. The sidecar's
call-instantiation identity is `ContentId(metadata.call.instantiation)`, and
`metadata.call.instantiation.abi = metadata.call.abi`. The instantiation's `subject` retains whether callee
materialization was direct, witness, dynamic, lambda, or builtin and validates operand zero against
the exact materialized value. A IRReady reference-handle operand remains a reference-handle operand, and every
IRReady operand for a mode whose domain is `PhysicalOperand(_)` remains physical storage with the
mode's exact access and location requirement; lowering may apply only the named `admitAbiInput`
view, not
reclassify an ordinary runtime value with the same `TypeId`. ABI result alternatives likewise
constrain the call-local instantiation, whose concrete result entries determine the IRReady/IR result
category and complete handle shape. Lowering cannot turn a witness/dynamic/lambda call into a direct
subject merely because one current target is known.

`IR-CALL-002`: Every `IRCall` metadata entry's `call.capabilities` is the unique result of
`ProjectCapabilitySelectionToIR(IRReadyCallContract.capabilitySelection)`. Projection preserves the
region, every `CapabilityUseId`, use key/reason, and requirement, plus the concrete alternative's
exact source IDs, operational subjects, combined requirement, and availability proof. A direct or
imported requirement is copied unchanged. A local-call requirement projects its
`ResolvedDeclRefAt<Published>` to `DeclRef`; a witness-entry requirement projects its
`SubtypeWitnessRef<Published>` to `(SubtypeWitnessId, RuntimeInterfaceRequirementKey)`. In both latter
cases `useWitnessDependencies` has exactly that use ID and its complete
`WitnessResolutionStamp`; it has no other keys. These published stamps contribute their exact
`WitnessTableDependency` entries to the fragment before the stage-specific wrappers are erased.
`concreteSourceWitnessDependencies` has exactly the selected concrete source-ID domain and stores
the minimal stamp required by each source subject and its specialization/static inputs, including
an empty stamp when no witness definition is needed.
Each concrete declaration subject contributes its exact `DeclDependency`; a registered
subject contributes its exact `StandardRuleDependency`; and a language-rule subject contributes
its exact `LanguageRuleSetDependency`. Their source stamps add any nested conformance dependencies.
Every projected use-map key equals `ContentId(use.key)`, and the concrete alternative independently
revalidates `CAP-SEL-003` using the projected region, source set, combined requirement, and proof.

The projection proof satisfies
`source = ContentId(IRReadyCallContract.capabilitySelection)` and
`projected = ContentId(call.capabilities.capabilities)`. Replacing each projected local/witness
requirement with the dependency stamp under its same key reconstructs byte-for-byte the published
source selection, so IRReady-to-IR projection is one-to-one. The metadata is immutable semantic/static
metadata: it is not a runtime operand or result, is excluded from `FunctionAbiMap` and
`AbiCallInstantiation`, and does not change executable dispatch or code shape. Lowering cannot
reconstruct it from `IRReadyCallContract.effective`, a flattened capability set, or target
annotations; cannot collapse zero, one, and multiple concrete sources to an optional formula; and
cannot exchange an ordinary use for an equal concrete requirement. An invalid projection is a
lowering failure, not permission to omit the metadata.

`IR-WIT-001`: `IRWitnessTable` is the existing global witness-table declaration/value, represented
by an `IRSymbolRef` whose declaration shape and definition body carry the validated table entries.
Referencing it does not emit a zero-operand instruction. `IRSpecialize` has no specialization payload
hidden in `IROp`; it consumes the generic witness-table value as operand zero followed by the values
from `IRReadyWitnessOperation.SpecializeWitness.inputs`, ordered by the canonical binder's generic
and constraint roles. The validated `CanonicalSpecializationSpine` is stored only as
`metadata.specialization = Some(spine)`, while the emitted instruction consists only of the opcode
and operands. Its result has
`SubtypeWitnessValueShape(ConcreteSubtypeWitness(substitutedTarget))`.

`IR-WIT-002`: Lowering `LookupSubtypeWitness(base, key)` emits exactly one
`IRLookupWitnessMethod` (`lookupWitness`) with exactly two operands, in order: the lowering of
`base`, followed by the canonical IR value whose shape is
`InterfaceRequirementKeyValueShape(SubtypeWitnessRequirementKey(key))`. The operation returns the
key-derived concrete `SubtypeWitnessValueShape` as its sole result. The requirement key is an operand,
not static data hidden in `IROp`. An N-key semantic lookup spine produces N operations in the same
order. Initial lowering cannot flatten, reassociate, or replace that spine with endpoint types;
later optimization may fold a lookup against a statically known table.

`IR-WIT-003`: `IRExtractExistentialWitnessTable` has no interface payload hidden in `IROp`; it
consumes exactly one existential-package operand and returns the requested subtype-witness shape.
The validated interface selection is stored only in
`metadata.existentialWitnessExtraction` and is reflected by the result shape. Calling an extracted
requirement emits `IRLookupWitnessMethod` to produce a callable and then `IRCall` with that callable
as operand zero. Neither instruction stores an `IRSymbolRef` as a substitute for a runtime witness
value.

`IR-WIT-004`: Lowering a general requirement lookup emits `IRLookupWitnessMethod`
(`lookupWitness`) with exactly two operands, in order: one concrete subtype-witness value and the
canonical IR value whose shape is
`InterfaceRequirementKeyValueShape(GeneralInterfaceRequirementKey(key))`. It returns exactly
`WitnessEntryShape(key)`. The dependent shape resolves the key's requirement kind:
associated types/values are metadata values, callable/constructor/accessor entries are callable
metadata, and nested conformances contain a subtype witness. Consumers must use the matching
kind-indexed projection; a property/subscript bundle cannot be treated as one callable slot. A
callable result is invoked only by a following `IRCall`. A fused witness-call opcode is forbidden:
the table and exact requirement/accessor key remain visible on `IRLookupWitnessMethod`.

`IR-CON-001`: A conformance declaration's `definition` and its definition body carry the same
validated definition reference; its `form` equals the definition's `WitnessTableForm` and the table
reference's provider-table form. The
declaration's metadata key set equals the complete active all-kind entry set of that definition;
each metadata payload resolves to the canonical kind-correct lowering of the satisfaction at the
same key. `runtimeEntries` keys equal `runtimeSlots` keys, and slot values are a bijection onto
`0 .. runtimeSlots.count-1` in canonical `RuntimeInterfaceRequirementKey` order. Each runtime symbol ref
resolves a function shape with the signature required by that projected entry. No metadata entry is
identified by a runtime slot.

`IR-FRG-001`: `references` is exactly the canonical set of symbol references reachable from every
instruction operand, semantic-metadata entry, and definition payload. `sourceMap` has exactly one entry for every instruction ID and
no other key. Every requirement map key equals `IRDependency.key`; requirements are the exact
direct semantic/module/standard-rule inputs read by lowering, with nonempty canonically merged
origins. A local reference's module equals the fragment owner's module; an imported reference and
module dependency name the same immutable interface revision used for resolution.
Serialization follows map canonical order plus `blockOrder`, block parameter order, instruction
order, operand order, result order, and semantic-metadata field order. Successor order is derived
from terminator operand order, so round trips and parallel lowering are byte-identical without a
second stored CFG authority.

`IR-DEP-001`: `IRDependencyKey` is the closed sum shown above: `TypeDependency`,
`ContractDependency`, `DeclDependency`, `WitnessTableDependency`,
`InitializationPlanDependency`, `LanguageRuleSetDependency`, `ModuleDependency`, or
`StandardRuleDependency`.
`origins` is nonempty. Each subject resolves in the same semantic/module/standard environment used
by the fragment's lowering query; a requirement retained only from an unselected branch is invalid.
Every instruction whose semantic metadata has `initialization = Some(plan)` contributes
`InitializationPlanDependency(plan.plan)`; the fragment's canonical requirement map merges repeated
contributions from a multi-instruction emission recipe. No instruction contributes that dependency
merely because it shares a result type. The dependency resolves an applicable winner in the
`Selected` result returned by `ResolveInitialization`; a recovered initialization plan cannot
satisfy it. A tooling `IRPoison` produced from recovery contributes no initialization-plan
dependency.
When a fragment is produced inside `SynthesisConstruction`, these IR requirements do not add new
`SemanticDependency` alternatives: type, contract, initialization-plan, language-rule-set,
module-interface, and standard-rule requirements are backed by the exact producing
`QueryDependency(QueryKey)`; declaration requirements are backed by the exact
`DeclDependency(DeclRef)`; and conformance requirements are backed by
`WitnessTableDependency(ValidatedWitnessTableRef)`. The
synthesis validator resolves each
query result/direct-input selector and requires it to equal the IR dependency subject; unrelated
declaration/synthesis dependencies cannot justify an IR requirement.
`IRCall` semantic metadata contributes exactly the conformance dependencies in its use/source witness
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
`SomeInterfaceRequirementKey` (the existential form of `InterfaceRequirementKeyOf<K>`), never dictionary or
declaration position. Only callable, constructor, and property/subscript accessor ABI slots use the
`RuntimeInterfaceRequirementKey` projection.

`IR-003`: Type lowering consumes canonical `Type` values. It cannot query declaration parents to
reconstruct a receiver type, parameter direction, or generic substitutions omitted from a type.

`IR-004`: A conformance lowers in two steps: allocate the IR witness-table identity, then emit each
all-kind keyed entry. Recursive references use the allocated identity; associated type/value and
nested-conformance metadata retain `SomeInterfaceRequirementKey`, while runtime callable slots retain the
derived `RuntimeInterfaceRequirementKey`. Missing entries are a IRReady validation error, not a null IR
operand.

`IR-005`: Lowering a recovered IRReady error, including chapter 16's
`RecoveryInitializationStep(error)`, produces a typed recovery placeholder only in
diagnostic/tooling mode. It emits the existing `IRPoison` opcode with
`metadata.recoveryError = Some(error)` and contributes no
`InitializationPlanDependency`. A module containing such placeholders is not publishable as
successful code generation.

## Function-type lowering

The logical function type remains richer than a target ABI type:

```text
lowerLogicalFuncType(CallableSignature, EffectiveCallableContract) = {
    optional explicit initialization target from CallablePurpose,
    optional explicit receiver parameter from ReceiverSlot,
    ordinary parameters lowered according to ParamPassingMode and semantic value shape,
    explicit generic/witness parameters where not specialized,
    proof-carrying logical result and error shapes,
    effect/capability decorations from EffectiveCallableContract
}
```

The lowering records the `FunctionAbiMap` defined above. Calls consume the same map.

`IR-ABI-001`: Resolving `FunctionAbiMap.signature` yields one receiver role exactly when the
signature has a receiver, one initialization-target role exactly when its purpose is
`ConstructorCallable`, and one parameter role for every `ParameterSlot.key`.
`FunctionAbiMap.resultAuthority` is copied byte-for-byte from the callable header; resolving it
yields that declaration/registered anchor and the same signature. A map builder never takes an
authority override and never infers one from `results`.

`IR-ABI-001a`: For each active `Conforms` constraint slot, ABI construction computes
`w = ContentId(CanonicalSubtypeWitness(targetOf(slot)))`, inserts exactly one
`WitnessAbiInput(w)` with `SubtypeWitnessAbiInput(targetOf(slot))`, and records the source slot only
in diagnostic/binder provenance. Duplicate insertion is the same
`DuplicateDeclaredConformance` error as chapter 15. The function-body generic-evidence environment
maps `w` directly to that formal IR value, so lowering `DeclaredSubtypeWitness(target)` requires no
ordinal search. `conformanceInputsByWitness` performs the corresponding checked projection for
slot-keyed specialization evidence; its value at `w` must have
`SubtypeWitnessValueShape` with target `targetOf(slot)`. Thus source constraint mapping stays keyed
for generic application while proof/ABI identity stays pair-keyed.

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
read/write access. A physical mode encoded as `RuntimeAbiInput`, `PointerLikeAbiInput`, or
temporary storage is invalid even if target ABI lowering later uses the same machine pointer
representation. Conversely, `InMode`, `OutMode`, and `InOutMode` never become physical modes merely
because one actual happens to be stored in memory.

An abstract-domain formal whose structural value type is `ExplicitRefType` or `PtrType` uses
`PointerLikeAbiInput(contract, mode)`. The contract's value type, type projection, handle kind,
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
orthogonal. `formalAbiPointerLikeInput` gives the formal handle exactly
`abiFormalHandleSourceProvenance(contract.sourceProvenance)`, and
`instantiateAbiPointerLikeInput` substitutes every canonical argument in those facts under the
call specialization without adding facts. Only a language/standard rule recorded in the checked
formal may select a `DeclaredHandleMutability`, `DeclaredHandleLifetime`, `DeclaredHandleAlias`, or
`DeclaredHandleSourceProvenance`; every declared source fact retains its exact registered rule,
static inputs, and the standard environment selected by the callable's effective contract, and all
policy endpoints must agree with the type projection. The declared-source alternative is canonical
only for a nonempty fact set; an empty set uses
`ConservativeUnknownHandleSourceProvenance`. The ABI contract never stores a call-produced
`PointerLikeProof`, and body entry
cannot replace the formal policy with provenance observed at one caller.

Other abstract-domain runtime values use `RuntimeAbiInput(type, mode)`. All alternatives repeat the
exact mode and logical type from the signature. The initialization target repeats its complete
target slot.
Residual generic variables and required constraint evidence contribute their keyed roles; a closed
specialization contributes neither. A `Conforms` slot has
`SubtypeWitnessAbiInput(targetOf(slot))` under
`WitnessAbiInput(ContentId(CanonicalSubtypeWitness(targetOf(slot))))`; inserting a second
`Conforms` slot with the same witness role is an invalid duplicate rather than another input. Other
evidence uses `OtherConstraintEvidenceAbiInput(slot.kind)`. Input ordinals are a bijection onto
`0 .. inputs.count-1` in initialization-target, receiver, parameter-slot, residual-generic, then
canonical-constraint order.

`IR-ABI-002`: The result map always has `NormalAbiResult` at ordinal zero and has
`ErrorAbiResult` at ordinal one exactly when the error type is not `BottomType`. The checked callable
result authority in `FunctionAbiMap.resultAuthority`, not the result type's machine representation,
chooses the closed alternative.
An ordinary authority gives `RuntimeAbiResult(type)`. A fixed reference authority gives
`FixedPointerLikeResult` with its complete reusable formal shape. A ref-accessor authority gives
`AccessorPointerLikeResult` naming the exact `AccessorReferenceResultContractId`, signature,
and result type. A registered authority gives `RegisteredPointerLikeResult` with the exact
registration, static inputs, semantic environment, and result type. No result contract contains a
caller SSA value or caller invocation lifetime, and physical storage is not a function-result
alternative.

Every reachable body `return`/`throw` proves its actual value against the selected formal result
contract using `proveAbiDefinitionResult` and the function's formal entry inputs. Fixed contracts
require their exact formal shape; accessor contracts replay their five rules over the named formal
receiver/parameter sources; registered contracts replay the registered rule. A bare runtime value
cannot satisfy any reference-handle contract. The effective contract in
`IRFunctionDeclShape` names the same signature, and the ABI map contains that signature,
result authority, context, inputs, and results with the declaration shape's byte-identical
`resultAuthority`. Target ABI lowering may erase or indirect logical values only while preserving
this mapping explicitly.

`IR-ABI-003`: Every call constructs one `AbiCallInstantiation`. Its `abi` is the referenced map;
`activation.signature` is that map's signature, `activation.formalActivation` is exactly
`abi.context.activationLifetime`, and `activation.callerInvocationExtent` is the originating
`IRReadyCallContract.callerInvocationLifetime`. `ActivationBindingProof` records the permitted
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
whose type endpoints equal that binding. The originating access plan's `rankingCoercion` is
exactly `Some(ConsumedWithoutStorageCoercion(PhysicalParameterIdentityPassingRule))`;
`sourceAdaptationRank` therefore yields
`CoercionFreeStorageAccessCost(PhysicalParameterIdentityPassingRule)`, whose comparison rank is
`zeroRank`. Admission validates the complete instantiated physical requirement: access,
activation or declared lifetime, address-space predicate, and source-provenance predicate. Its
`sourceProof.storage` is exactly `actualStorage`,
`sourceProof.provenanceProof.provenance = actualStorage.sourceProvenance`, and the provenance
proof's requirement is exactly the instantiated formal source requirement; ABI admission cannot
reconstruct, strengthen, or substitute source facts from the operand type or address space. Its
mutability view permits mutable underlying storage to satisfy `ConstRefMode` without declaring the
storage immutable; the admitted access remains read-only. `RefMode` requires the read/write and
mutable view. The proof stores both actual and instantiated formal shapes and preserves the actual
alias for call-alias checking. Neither an abstract storage, ordinary runtime value, reference handle,
nor temporary can satisfy a physical input, regardless of equal `TypeId` or layout.
`aliasCompatibility` is then revalidated against the admitted operands' preserved alias
provenances, mode-specific access claims, and bound caller invocation extent. Only two overlapping
`SharedPhysicalRead` claims are unconditionally compatible. A proved common alias region involving
an abstract or physical exclusive claim is rejected; unknown provenance records the accepted
exclusive source contract and is undefined behavior if it overlaps at runtime.

`IR-ABI-004`: `AbiCallInstantiation.results` has exactly the roles of the reusable ABI result map,
and every entry repeats its formal contract. A runtime contract instantiates to the identical
runtime type. A fixed reference contract applies the call's activation/address substitution to its
formal shape. An accessor contract records the exact captured source-role-to-call-operand
projections, replays its five component derivations, and produces one concrete
`PointerLikeValueShape`. For a fresh alias rule, the instantiation and its IR derivation retain
the identical stage-free `AccessorInvocationIdentity`; no call instruction identity is substituted.
A registered contract stores and validates the registered derivation
over the exact runtime operands. The instruction result at each ABI ordinal has precisely that
instantiated shape.

Call-result construction cannot attach handle provenance to ordinary data or use the reusable
formal contract as a concrete SSA value. Conversely, definition `return`/`throw` validation uses
`proveAbiDefinitionResult`, not a call-local instantiation. Any intentional result conversion is an
explicit IRReady/IR operation before the boundary; subsequent copies and block arguments preserve the
complete instantiated shape.

This removes the current split where some paths inspect `FuncType` mode wrappers while others
iterate `ParamDecl` modifiers.

## Lowering unit tests

Every IRReady node lowering test constructs canonical types and a five-to-ten-node IRReady fragment
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
- preservation and replay of overlapping constref-read proofs, statically proved exclusive-access
  conflicts, and unknown-overlap exclusivity contracts from overload selection through IRReady and
  call-local ABI admission;
- abstract `OutMode`/`InOutMode` temporary initialization, write-back, and destruction cleanup on
  every selected exit, nominal site-derived temporary identity/alias preservation, and rejection of
  that storage as a physical-mode operand;
- accessor-result descriptors tied to the exact producer call rather than an equal-typed value;
- registered physical projections preserve environment/static inputs, executable base/index order,
  intrinsic output derivations, and their distinct IR storage-operation alternative;
- callable result authority is byte-identical across header, typed/elaborated/IRReady call,
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
