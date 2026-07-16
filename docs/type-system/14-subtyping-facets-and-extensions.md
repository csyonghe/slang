# Subtyping, facets, and extensions

This chapter is normative for interface subtyping, witness-table values, member-providing facets,
extension application, and lookup disambiguation. Chapter 4 defines the shared semantic fields,
chapter 5 defines lexical lookup, and chapter 8 defines witness-table contents. This chapter defines
how those values compose operationally.

The design does not preserve a frontend representation merely because the current compiler uses it.
In particular, a binary `TransitiveSubtypeWitness(aToB, bToC)` is not a constructor in this
specification: it hides the requirement key that must be looked up in `aToB`, does not mirror the
operation emitted to IR, and admits proof shapes that lowering cannot interpret uniformly.

## Distinct relations

The following relations remain distinct:

```text
Δ ⊢ τ ≡ ρ                         ⇝ TypeEqualityProof
Δ ⊢ τ ≤representation ρ           ⇝ RepresentationAdjustmentPath
Σ; Γ; Δ ⊢ τ <: I                  ⇝ InterfaceSubtypeWitness
Δ ⊢ I refines J                   ⇝ InterfaceRefinementProof
Σ; Γ; Δ ⊢ e converts-to ρ         ⇝ ConversionPlan
```

Representation subtyping means that the same object has a language-defined base-object view. In
the proposed language it applies to class representation bases and registered standard-environment
relationships only. Interface subtyping means that a witness-table value proves that a type
satisfies an interface instance. Conversion may use either relation through a named bridge, but it
is not either relation.

`SUB-REL-001`: No proof constructor is shared by two relations above. A bridge records its source
proof and the operation performed; it cannot relabel endpoints.

`SUB-REL-002`: A struct-to-interface clause creates interface-conformance evidence. It does not
create a representation base, a base subobject, a pointer adjustment, or a representation-base
facet.

## First-class interface-subtype witnesses

An interface-subtype witness is an immutable semantic value. It can be stored in generic arguments,
substituted, serialized, reflected through the node schema, passed as a runtime generic argument,
and lowered independently of any declaration that happens to use it.

```text
InterfaceSubtypeTarget = {
    subtype: TypeId,
    superInterface: InterfaceInstanceKey
}

InterfaceWitnessClassifier =
    ConcreteInterfaceWitness(target: InterfaceSubtypeTarget)
  | GenericInterfaceWitness(binder: CanonicalGenericBinder,
                            targetPattern: InterfaceSubtypeTarget)
  | ErrorInterfaceWitnessClassifier(error: ErrorId)

SubtypeWitnessLookupKey =
    RefinementWitnessEntry(refinement: RefinementStepKey)
  | NestedConformanceWitnessEntry(
        requirement: WitnessEntryKey<NestedConformanceKind>)

WitnessDefinitionRefAt<Construction> =
    FrozenWitnessDefinition(ValidatedConformanceRef)
  | OperationalWitnessDefinition(OperationalConformanceRef)

WitnessDefinitionRefAt<Published> =
    FrozenWitnessDefinition(ValidatedConformanceRef)

WitnessResolutionSetAt<S: WitnessUseStage> =
    CanonicallyOrderedMap<ConformanceId, WitnessDefinitionRefAt<S>>

InterfaceSubtypeWitnessOperation =
    WitnessTableValue(provider: ConformanceId)
  | GenericWitnessTable(provider: ConformanceId)
  | SpecializedWitnessTable(generic: InterfaceSubtypeWitnessId,
                            specialization: CanonicalSpecializationSpine)
  | BoundWitnessParameter(binder: CanonicalBinderRef,
                          slot: CanonicalConstraintSlot)
  | LookupSubtypeWitness(base: InterfaceSubtypeWitnessId,
                         key: SubtypeWitnessLookupKey)
  | OpenedExistentialWitness(opening: OpenedTypeId,
                            source: NodeId<Typed>)
  | ErrorInterfaceWitness(error: ErrorId)

InterfaceSubtypeWitnessKey = {
    classifier: InterfaceWitnessClassifier,
    operation: InterfaceSubtypeWitnessOperation
}

InterfaceSubtypeWitnessId = ContentId<InterfaceSubtypeWitnessKey>

InterfaceSubtypeWitnessRecordAt<S: WitnessUseStage> = {
    id: InterfaceSubtypeWitnessId,
    key: InterfaceSubtypeWitnessKey,
    resolutions: WitnessResolutionSetAt<S>,
    origin: Origin
}

InterfaceSubtypeWitness = InterfaceSubtypeWitnessRecordAt<Published>

InterfaceWitnessPackClassifier =
    ConcreteWitnessTargets(targets: NodeList<InterfaceSubtypeTarget>)
  | GenericWitnessTargetPack(pattern: InterfaceSubtypeTarget,
                             captures: NonEmpty<PackId>)

InterfaceSubtypeWitnessPackOperation =
    ConcreteWitnessPack(elements: NodeList<InterfaceSubtypeWitnessId>)
  | MapWitnessPack(pattern: InterfaceSubtypeWitnessId,
                   captures: NonEmpty<PackId>)

InterfaceSubtypeWitnessPackKey = {
    classifier: InterfaceWitnessPackClassifier,
    operation: InterfaceSubtypeWitnessPackOperation
}

InterfaceSubtypeWitnessPackId = ContentId<InterfaceSubtypeWitnessPackKey>

InterfaceSubtypeWitnessPackRecordAt<S: WitnessUseStage> = {
    id: InterfaceSubtypeWitnessPackId,
    key: InterfaceSubtypeWitnessPackKey,
    resolutions: WitnessResolutionSetAt<S>
}

InterfaceSubtypeWitnessPack = InterfaceSubtypeWitnessPackRecordAt<Published>

WitnessClassificationResult =
    Classified(InterfaceWitnessClassifier)
  | InvalidWitnessOperation(WitnessValidationFailure)

WitnessValidationFailure =
    DefinitionClassifierMismatch(provider: ConformanceId)
  | IncompleteWitnessSpecialization(generic: InterfaceSubtypeWitnessId)
  | BoundSlotIsNotConformance(binder: CanonicalBinderRef,
                              slot: CanonicalConstraintSlot)
  | WitnessEntryUnavailable(base: InterfaceSubtypeWitnessId,
                            key: SubtypeWitnessLookupKey)
  | InvalidExistentialOpening(opening: OpenedTypeId)
  | WitnessResolutionMismatch(provider: ConformanceId)

classifyWitnessOperation(WitnessTableValue(p)) =
    mapConcreteClassifier(classifierOfConformance(p))
classifyWitnessOperation(GenericWitnessTable(p)) =
    mapGenericClassifier(classifierOfConformance(p))
classifyWitnessOperation(SpecializedWitnessTable(g, s)) =
    specializeGenericClassifier(classifierOf(g), s)
classifyWitnessOperation(BoundWitnessParameter(b, k)) =
    classifierOfConformsConstraint(resolveBinder(b).constraints[k])
classifyWitnessOperation(LookupSubtypeWitness(w, k)) =
    classifierOfWitnessEntry(classifierOf(w), k)
classifyWitnessOperation(OpenedExistentialWitness(o, n)) =
    classifierOfExistentialOpening(o, n)
classifyWitnessOperation(ErrorInterfaceWitness(e)) =
    ErrorInterfaceWitnessClassifier(e)

requiredDefinitions(WitnessTableValue(p)) = {p}
requiredDefinitions(GenericWitnessTable(p)) = {p}
requiredDefinitions(SpecializedWitnessTable(g, s)) =
    requiredDefinitions(g) union directWitnessDefinitions(s)
requiredDefinitions(BoundWitnessParameter(_, _)) = {}
requiredDefinitions(LookupSubtypeWitness(w, _)) = requiredDefinitions(w)
requiredDefinitions(OpenedExistentialWitness(_, _)) = {}
requiredDefinitions(ErrorInterfaceWitness(_)) = {}
```

`WitnessTableValue` is the witness table as a proof value; it is not an assertion wrapped around a
separate proof. Its stable operation names the `ConformanceId`; the stage-specific resolution set
names the exact complete definition used to validate or lower it. A generic table is a generic
semantic value whose classifier contains a binder and target pattern. Applying
`SpecializedWitnessTable` produces the concrete witness for the substituted target. For example,
the conformance declared by `S<T> : IBase<T>` is represented once as a `GenericWitnessTable`; the
evidence for `S<float> : IBase<float>` is its specialization, not a fresh nongeneric table or a
decl-ref with hidden substitution state.

`SUB-WIT-000`: Witness semantic identity is `ContentId<InterfaceSubtypeWitnessKey>` and excludes
origins and definition revisions. Construction-to-publication changes an
`OperationalWitnessDefinition` resolution into a `FrozenWitnessDefinition` for the same
`ConformanceId`; it cannot change any witness ID. Every provider reachable from the witness key has
exactly one resolution of the permitted stage, and no unrelated resolution may be retained.

`SUB-WIT-008`: `classifyWitnessOperation` is a total constructor-by-constructor validation query.
The two table constructors require the matching concrete/generic conformance classifier;
specialization is total and kind-correct; a bound slot is exactly `Conforms(sub, interface)`;
lookup uses the stored active entry key; and existential opening proves the package contains the
requested interface. `record.key.classifier` equals its `Classified` result,
`record.id = ContentId(record.key)`, and the domain of `record.resolutions` equals
`requiredDefinitions(record.operation)`. Every resolution map key equals the identity inside its
definition ref. Missing, extra, stage-invalid, or target-mismatched resolutions fail validation;
they are not recovered by ambient conformance search.

`SUB-WIT-009`: `directWitnessDefinitions(specialization)` traverses every type/value argument and
keyed constraint evidence in the canonical spine. It unions the recorded definition dependencies
of referenced types/constants and every interface-subtype witness reachable by the evidence
schema, including `InterfaceSubtypeEvidence` and `ValueDifferentialInfoEvidence`. Thus specializing a generic table
with a table-backed witness argument retains the definition needed to materialize that runtime
operand; it cannot disappear merely because the outer generic table has a different provider.

`SUB-WIT-001`: Every non-recovery operation has exactly one classifier derivable from its operands.
`WitnessTableValue` resolves a definition whose target equals the concrete classifier target.
`GenericWitnessTable` contains precisely the free variables of its binder. A specialization is
total, kind-correct, and applies ordinary arguments and constraint evidence together to the target,
requirements, inherited entries, and dependencies in the resolved definition.

`SUB-WIT-002`: `BoundWitnessParameter(binder, slot)` is valid only when `slot` denotes the active
`Conforms` constraint in that canonical binder. Its target is the binder-relative constraint
predicate. This value is the semantic and IR-level witness parameter; a synthetic
`ValidatedConformanceRef` must not be invented for it.

`SUB-WIT-003`: `LookupSubtypeWitness(base, key)` is valid only when the base table contains that
exact active key and its payload is an interface-subtype witness. Its result target is the payload
target. Requirement declaration identity, source position, or the desired result interface cannot
stand in for `key`.

`SUB-WIT-004`: There is no general transitive-witness constructor. Composing `A <: B` with a
declared `B <: C` projection means `LookupSubtypeWitness(aToB, keyOfBToC)`. A longer route is a
left-to-right spine of lookup nodes, one for each semantic witness-table lookup. The spine is the
proof and the operational plan at the same time.

`SUB-WIT-005`: A witness table, bound witness parameter, specialization, lookup result, or opened
existential witness may satisfy a `Conforms` constraint when its target matches. Static conformance
definition references are only one source of witness values; APIs such as generic solving,
existential packing, associated-type projection, and witness dispatch accept
`InterfaceSubtypeWitnessId`, not only `ValidatedConformanceRef`.

`SUB-WIT-006`: `ErrorInterfaceWitness` supports typed recovery but cannot discharge a successful
generic constraint, publish an existential, select a witness call, or enter a module interface.

`SUB-WIT-007`: Witness packs inhabit `InterfaceSubtypeWitnessPackId`, never the singular witness
classifier. `ConcreteWitnessPack` has the same length as `ConcreteWitnessTargets` and each element
has the corresponding target. `MapWitnessPack` captures exactly the packs free in its target and
witness patterns; expansion produces a concrete pack by one capture-avoiding substitution per
canonical expansion path. A consumer requesting one `Conforms` proof must select an explicit pack
element and cannot pass the pack ID as a singular witness. A witness pack is a compile-time
canonical container, not a runtime proof value: it has no standalone witness-table ABI shape.
Its stage-indexed record carries the exact canonical union of the
stage-correct resolution sets for its singular elements, and every consuming slot records the
selected element and `ExpansionPath`. Missing or unrelated definition resolutions are invalid.
The record has no runtime witness-table ABI shape; expansion lowers the selected singular values.
Its `id = ContentId(key)`, and its resolution domain is exactly the union of
`requiredDefinitions` for the element/pattern witness IDs in `key.operation`; revisions remain a
sidecar and cannot change pack identity.

## Witness lookup and lowering correspondence

Frontend IR treats witness tables as values. The canonical lowering is structural:

| witness operation          | frontend IR operation                                                                         |
| -------------------------- | --------------------------------------------------------------------------------------------- |
| `WitnessTableValue`        | `WitnessTableReferenceOperation`                                                              |
| `GenericWitnessTable`      | generic conformance symbol declaration/definition plus `WitnessTableReferenceOperation` value |
| `SpecializedWitnessTable`  | `SpecializeWitnessOperation`                                                                  |
| `BoundWitnessParameter`    | `InterfaceWitnessAbiInput` / `InterfaceWitnessShape` ABI parameter                            |
| `LookupSubtypeWitness`     | `LookupWitnessOperation`                                                                      |
| `OpenedExistentialWitness` | `ExtractExistentialWitnessOperation`                                                          |
| witness-pack expansion     | registered pack expansion producing singular witness values                                   |

`SUB-IR-001`: Lowering one `LookupSubtypeWitness(base, key)` emits exactly one
`LookupWitnessOperation(key)` whose witness-table operand is the lowering of `base`. It may constant
fold the result later, but AST-to-IR lowering neither replaces the lookup with a binary transitive
proof nor reconstructs a key from endpoint types.

`SUB-IR-002`: A witness call consumes a witness-table IR value plus a
`WitnessRuntimeEntryKey`. A static table is first materialized as a witness value; a generic
parameter, specialization, lookup result, and existential extraction use the same operand position.
The call operation does not require an `IRSymbolRef` where a runtime witness value is semantically
required.

`SUB-IR-003`: Associated type/value and other all-kind requirement lookup use
`LookupWitnessEntryOperation` with the same table operand and complete `SomeWitnessEntryKey`; its
dependent `WitnessEntryShape` is declared by that key's requirement kind. A nested-conformance
projection used as subtype evidence instead constructs `LookupSubtypeWitness` and therefore emits
`LookupWitnessOperation`. Only callable-like entries are projected to runtime callable slots.

## Aggregate clauses and deprecated struct inheritance

The written colon syntax is classified by aggregate kind; there is no common semantic
“inheritance clause” constructor:

```text
CheckedAggregateClause =
    ClassRepresentationBase(base: TypeId,
                            declaration: DeclId,
                            adjustment: RepresentationAdjustmentStep)
  | InterfaceConformance(interface: InterfaceInstanceKey,
                         provider: ConformanceId)
  | InterfaceRefinement(base: InterfaceInstanceKey,
                        clause: RefinementClauseId)
  | EnumUnderlyingType(type: TypeId)
  | ErrorAggregateClause(error: ErrorId)
```

`SUB-AGG-001`: A modern struct accepts only `InterfaceConformance` entries. A class accepts at most
one `ClassRepresentationBase` and zero or more interface conformances. An interface accepts only
interface refinements. An enum accepts its registered underlying-type form and any separately
declared interface conformances.

`SUB-AGG-002`: Concrete struct inheritance is excluded from the proposed language. Compatibility
parsing may retain the source tokens and issue a versioned migration diagnostic, but no checked
`LegacyStructBase`, representation proof, base facet, base subobject, aggregate-initialization slot,
or IR base conversion is constructed. Standard-library relationships that need representation
semantics are registered standard-environment rules, not exemptions based on source module name.

`SUB-AGG-003`: An invalid clause produces `ErrorAggregateClause` only for recovery. It contributes
no member provider or successful proof and cannot make a later lookup or conversion succeed.

## Representation adjustment paths

Class base conversion is operational too:

```text
RepresentationAdjustmentStep =
    DeclaredClassBase(clause: DeclId,
                      derived: TypeId,
                      base: TypeId)
  | StandardRepresentationStep(rule: StandardEnvironmentRuleId,
                               derived: TypeId,
                               base: TypeId)

RepresentationAdjustmentPath = {
    source: TypeId,
    target: TypeId,
    steps: NodeList<RepresentationAdjustmentStep>
}
```

The empty path is identity. A nonempty path is contiguous and ordered exactly as its pointer/base
adjustments execute.

`SUB-REP-001`: A representation path's first source equals `source`, its last target equals
`target`, and adjacent endpoints match. Every declared step resolves to an enabled class-base
clause. No step names a struct base, interface conformance, or interface refinement.

`SUB-REP-002`: Composition concatenates validated paths and then applies only declared
identity/canonical-step reductions. It does not form an unordered binary transitivity tree.

## Facet routes

A facet is one member-providing view reached through an explicit route:

```text
FacetRouteStep =
    RepresentationBaseRoute(step: RepresentationAdjustmentStep)
  | InterfaceConformanceRoute(witness: InterfaceSubtypeWitnessId)
  | InterfaceRefinementRoute(key: SubtypeWitnessLookupKey)
  | ExtensionRoute(evidence: ExtensionApplicabilityEvidenceId)
  | ExistentialOpeningRoute(evidence: ExistentialOpeningEvidence)

FacetRouteKey = {
    root: TypeId,
    steps: NodeList<FacetRouteStep>
}

FacetKey = {
    owner: TypeId,
    origin: FacetOrigin,
    kind: FacetKind,
    route: FacetRouteKey,
    conditions: GenericConditionSet
}

FacetKind = SelfFacet | RepresentationBaseFacet | ConformanceFacet |
            RefinedInterfaceFacet | ExtensionFacet | OpenedExistentialFacet
```

`SUB-FAC-001`: Folding a facet route from its root produces the facet owner and evidence. A
refinement route step applies exactly one `LookupSubtypeWitness` with the stored key. The facet's
witness value is therefore a derived view of its route, never independently composed side state.

`SUB-FAC-002`: Path-distinct diamond facets have distinct `FacetRouteKey` values even when they end
at the same interface declaration. They remain representable simultaneously. Sharing is permitted
only after a proof shows their witness values and requirement transports are equivalent.

`SUB-FAC-003`: A facet key never omits a semantic route and then relies on map-insertion conflict
handling to recover it. `FacetSet.byKey` can hold every semantically distinct path.

`SUB-FAC-004`: `Facet.witnessResolutions` is a dependency sidecar, not route identity. It is the
minimal canonical union required by every witness ID in the route and folded member evidence.
`FacetSet.equivalence` persists every nontrivial proof used to identify route classes; a producer
cannot merge facets using a transient comparison result and then discard the proof.

`SUB-FAC-005`: An extension route contains the context-dependent
`ExtensionApplicabilityEvidenceId`, not merely its intrinsic target/reachability evidence. The
evidence ID therefore commits the route to the exact boolean selection region and complete
concrete-availability selection. Two lookups under regions `A` and `not A` cannot alias one facet key
when availability selects different results. `Facet` and `FacetKey` have no second `capabilities`
field. Caller-owned ordinary uses are absent from the route ID and are attached in an
`ExtensionFacetUseAt<S>` when a member use is committed.

## Extension application

Extension applicability is two pure queries. The first is reusable across capability regions; the
second binds that intrinsic result to one exact selection context:

```text
MatchExtensionIntrinsic(extension, queriedType, environment)
    -> QueryStep<ExtensionIntrinsicApplicationResult>

ExtensionIntrinsicApplicationResult =
    IntrinsicallyApplicable(ExtensionIntrinsicApplicabilityEvidence)
  | IntrinsicallyNotApplicable(ExtensionIntrinsicMismatch)
  | IntrinsicallyErroneous(DiagnosticSet)

ApplyExtension(intrinsic, contractSelection)
    -> QueryStep<ExtensionApplicationResult>

ExtensionApplicationResult =
    Applicable(ExtensionApplicabilityEvidence)
  | NotApplicable(ExtensionSelectionMismatch)
  | Erroneous(DiagnosticSet)

ExtensionCapabilityUseInputsAt<S: WitnessUseStage> = {
    extension: CapabilityUse<S>,
    target: Option<CapabilityUse<S>>
}

ExtensionFacetUseResultAt<S: WitnessUseStage> =
    CommittedExtensionFacetUse(ExtensionFacetUseAt<S>)
  | InvalidExtensionCapabilityUses(reason: RuleId)

CommitExtensionFacetUseAt<S>(applicability, capabilityUses)
    -> CheckResult<ExtensionFacetUseResultAt<S>>

extensionCapabilitySelectionAt<S>(use) = {
    region = resolve(use.applicability).region,
    inferredCapabilityUses = use.inferredCapabilityUses,
    concreteAvailability = resolve(use.applicability).concreteAvailability
}

ReachabilityFailure =
    NoExtensionReachabilityPath(extension: DeclId,
                                rootScope: ScopeId,
                                environment: SemanticEnvironmentId)
  | QualifiedExtensionScopeMismatch(extension: DeclId,
                                    requested: ScopeId,
                                    declared: ScopeId,
                                    environment: SemanticEnvironmentId)

ExtensionIntrinsicMismatch =
    TargetPatternMismatch
  | UnsatisfiedExtensionConstraints(NodeList<Constraint>)
  | ExtensionNotReachable(ReachabilityFailure)

ExtensionSelectionMismatch =
    ConcreteExtensionAvailabilityUnsatisfied(
        sources: NonEmpty<ResolvedConcreteAvailability>,
        region: BooleanCapabilityPredicate,
        failure: CapabilityFailure)
```

Intrinsic evidence has one canonical target match, a total specialization, evidence for every
required constraint, visibility/reachability in the exact semantic environment, and a checked
member scope. It makes no claim about the worlds in which that extension may be selected. An
applicable extension additionally stores `contractSelection.assumption` and one
`ConcreteAvailabilitySelection` in `ExtensionApplicabilityEvidence`. The later committed facet use
supplies caller-owned ordinary uses.

`ReachabilityFailure` is a negative result of traversing the closed lexical/import/qualified-scope
graph from the lookup root in the named environment. It is not an access denial, target mismatch,
or malformed extension. An invalid scope/module graph or ill-formed extension is `Erroneous`;
ordinary absence of a path is `NotApplicable` and cannot contribute a partial extension facet.

`SUB-EXT-001`: Target matching, constraint solving, and reachability are separate premises retained
in `ExtensionIntrinsicApplicabilityEvidence`. Failure of target matching is not a diagnostic during
ordinary lookup; an ill-formed extension declaration is diagnosed at its source. Capability
selection consumes that frozen intrinsic evidence rather than rerunning any of those premises.

`SUB-EXT-004`: `ApplyExtension` uses the canonical union of the extension and target
`ConcreteAvailabilitySet.sources`; `NoConcreteAvailability` is valid only when both sets are absent.
For a proven selection, the proof region equals `contractSelection.assumption` and the combined
requirement is recomputed from that exact source union. Those are the same concrete proof endpoints
required by a general capability selection, but only the `ConcreteAvailabilitySelection` is
retained in route evidence; no empty caller-use product becomes part of facet identity.

`CommitExtensionFacetUseAt<S>` separately validates that
`ExtensionCapabilityUseInputsAt<S>.extension` is the one ordinary use of the specialized
extension's pre-inference requirement and `target` is present exactly when the target contributes a
separate ordinary declaration use. Their IDs are distinct, their owners/origins are the committing
body/use site, and they become exactly `ExtensionFacetUseAt<S>.inferredCapabilityUses`. Committing a
use does not rerun or copy the route's concrete proof. A `BoundDeclUseAt<S>` aggregates these maps
exactly once after candidate selection; ordinary requirements never reject the extension.

`SUB-EXT-005`: `extensionCapabilitySelectionAt<S>` is the sole projection that reunites route-level
concrete evidence with committed caller-owned ordinary uses. It is a valid general
`CapabilitySelectionAt<S>` by construction, but is not stored redundantly in either the facet or
sidecar. A selected member/call merges this projection under `CAP-SEL-004`; it cannot copy only the
ordinary map, copy only the concrete proof, or resolve availability again under a different region.

`SUB-EXT-002`: An extension never changes the nominal definition's initialization model,
representation layout, private owner, or declared conformance set retroactively. It contributes an
environment-scoped member/conformance provider whose evidence is captured by uses.

`SUB-EXT-003`: Two applicable extensions are not ordered by hash-map iteration, import order, or
source order. One may dominate another only through a named semantic priority proof, such as strict
target-pattern specialization plus constraint implication. Otherwise their same-name candidates
remain jointly visible.

## Lookup priority is a partial order

Facet enumeration order is for deterministic presentation; selection uses a proof-carrying partial
order:

```text
FacetPriorityResult =
    PreferLeft(proof: FacetPriorityProof)
  | PreferRight(proof: FacetPriorityProof)
  | Equivalent(proof: FacetEquivalenceProof)
  | Incomparable(reason: FacetIncomparability)

FacetEquivalenceProof =
    IdenticalFacetKey(key: FacetKey)
  | RegisteredFacetEquivalence(left: FacetKey,
                               right: FacetKey,
                               rule: RuleId,
                               inputs: CanonicalArguments)

FacetIncomparability =
    NoDominanceRule(left: FacetKey, right: FacetKey)
  | PathDistinctInterfaceViews(left: FacetRouteKey, right: FacetRouteKey)
  | IncomparableExtensions(left: CanonicalDeclRef, right: CanonicalDeclRef)
  | ConflictingPriorityProofs(proofs: NonEmpty<FacetPriorityProof>)

RepresentationRoutePrefixProof = {
    prefix: FacetRouteKey,
    full: FacetRouteKey,
    representationSuffix: NonEmpty<RepresentationAdjustmentStep>
}

ExtensionSpecializationProof = {
    preferred: CanonicalDeclRef,
    shadowed: CanonicalDeclRef,
    targetMatch: CanonicalSpecializationSpine,
    constraintImplication: GenericConstraintImplicationProof,
    strict: TargetStrict | ConstraintStrict | BothStrict
}

OverrideSignatureProof =
    ExactOverrideSignature(FunctionTypeEqualityProof)
  | RegisteredOverrideSignature(rule: RuleId, inputs: CanonicalArguments)

DeclaredOverrideProof = {
    overriding: DeclId,
    overridden: DeclId,
    signature: OverrideSignatureProof,
    rule: RuleId
}

FacetPriorityProof =
    SelfFacetDominatesNonSelf(self: FacetKey, other: FacetKey)
  | DeclaredMemberDominatesExtension(member: FacetKey, extension: FacetKey)
  | ShorterRepresentationPathDominates(preferred: FacetKey,
                                       shadowed: FacetKey,
                                       prefix: RepresentationRoutePrefixProof)
  | MoreSpecificExtensionDominates(preferred: FacetKey,
                                   shadowed: FacetKey,
                                   proof: ExtensionSpecializationProof)
  | RegisteredFacetPriority(preferred: FacetKey,
                            shadowed: FacetKey,
                            rule: RuleId,
                            inputs: CanonicalArguments)

MemberCandidatePriorityResult =
    PreferMemberLeft(proof: MemberCandidatePriorityProof)
  | PreferMemberRight(proof: MemberCandidatePriorityProof)
  | EquivalentMembers(proof: MemberCandidateEquivalenceProof)
  | IncomparableMembers(reason: MemberCandidateIncomparability)

MemberCandidatePriorityProof =
    ProviderFacetDominates(preferred: FacetKey,
                           shadowed: FacetKey,
                           proof: FacetPriorityProof)
  | ExplicitOverrideDominates(overridingProvider: FacetKey,
                              overriddenProvider: FacetKey,
                              overriding: DeclId,
                              overridden: DeclId,
                              declarationProof: DeclaredOverrideProof)
  | RegisteredMemberPriority(preferredProvider: FacetKey,
                             shadowedProvider: FacetKey,
                             preferredMember: DeclId,
                             shadowedMember: DeclId,
                             rule: RuleId,
                             inputs: CanonicalArguments)

MemberCandidateEquivalenceProof =
    SameBoundDeclaration(use: CanonicalDeclRef)
  | TransportedMemberEquivalence(leftProvider: FacetKey,
                                 rightProvider: FacetKey,
                                 leftMember: DeclId,
                                 rightMember: DeclId,
                                 proof: FacetEquivalenceProof)

MemberCandidateIncomparability =
    IncomparableProviders(FacetIncomparability)
  | NoMemberDominanceRule(left: DeclId, right: DeclId)
  | LegalOverloadPair(left: DeclId, right: DeclId)
```

`SUB-PRI-001`: Lookup gathers all reachable candidates, applies access and applicability filters,
and retains the maximal candidates under the partial priority relation. A single maximal candidate
is selected; overloadable maxima form an overload set; multiple non-overloadable or
indistinguishable maxima are an ambiguity.

`SUB-PRI-002`: A direct declared member of the queried type dominates same-name non-self and
extension providers unless the declarations form a legal overload set. A declaration in an
interface refinement dominates an inherited requirement only through
`ExplicitOverrideDominates`, whose provider and declaration endpoints validate the exact two
same-name candidates. Such a proof is never inserted as a global `FacetSet.priority` edge and
cannot affect other member names. Merely reaching the same declaration by a shorter interface
diamond arm does not erase the other witness route. Callable specificity is evaluated only after
lookup forms the overload set; it is not a facet-priority proof.

`SUB-PRI-003`: Lexical/import proximity decides whether an extension is reachable and supplies
diagnostic context. It is not a silent semantic tie-break between otherwise incomparable extension
members. Stable source order is used only to render deterministic ambiguity diagnostics.

`SUB-PRI-004`: A total C3 sequence is not applied across class representation bases, interface
refinements, conformances, and extensions as if they were one relation. The class representation
base is a single chain. Interface and extension candidates retain path identity and use the partial
priority relation above. A `RepresentationRoutePrefixProof` is valid only when its two routes have
the same root and
`full.steps = prefix.steps ++ map(RepresentationBaseRoute, representationSuffix)`. Consequently
`ShorterRepresentationPathDominates(preferred, shadowed, proof)` additionally requires
`preferred.route = proof.prefix` and `shadowed.route = proof.full`; it cannot be constructed by
dropping an interface-conformance, interface-refinement, existential-opening, or extension route
step.

## Validation obligations

Generated validators and unit suites cover:

- every witness-operation/classifier pair, substitution, serialization, and invalid endpoint;
- generic witness abstraction/specialization with type, value, pack, and witness arguments;
- one AST `LookupSubtypeWitness` to one frontend-IR `LookupWitnessOperation`;
- static, generic-parameter, specialized, nested-lookup, and existential witness calls;
- diamonds with equal endpoints but distinct keys, and proved reuse where permitted;
- class representation chains and rejection of every concrete struct-base spelling;
- extension target mismatch, blocked constraints, reachability, concrete availability, and
  specificity; reuse of intrinsic evidence across regions; region-sensitive facet IDs that remain
  independent of caller use origin; and exact once-only committed extension/target ordinary uses;
  and
- all four partial-priority results without source/import/container-order selection.

The current compiler's subtype/facet implementation is test evidence for compatibility, especially
where it exposes missing cases. Its mutable facet lists, `TransitiveSubtypeWitness`, and lowering
assertions are not normative representations.
