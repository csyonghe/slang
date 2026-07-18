# Subtyping, facets, and extensions

This chapter is normative for interface subtyping, witness-table values, member-providing facets,
extension application, and lookup disambiguation. Chapter 5 defines the shared semantic fields,
chapter 6 defines lexical lookup, and chapter 9 defines witness-table contents. This chapter defines
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
Σ; Γ; Δ ⊢ τ <: I                  ⇝ SubtypeWitness
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

## First-class subtype witnesses

A type-to-interface `SubtypeWitness` is an immutable semantic value. It can be stored as keyed
generic constraint evidence, substituted with a specialization frame, serialized, reflected through
the node schema, passed as a runtime generic witness argument, and lowered independently of any
declaration that happens to use it. This chapter reuses
chapter 9's `SubtypeWitnessTarget` for both witness-table forms and operational witness values;
there is no separate conformance-endpoint product.

In schema terms, `SubtypeWitnessRecordAt<S>` is a checked `Val`-family alternative. A generic
witness table is therefore a genuine generic witness value with a canonical binder and abstract
target, and `SpecializedWitnessTable` is the ordinary specialization operation on that value. It is
not a declaration reference, a mutable side table, or a special case recoverable only during IR
generation.

```text
SubtypeWitnessIdentity =
    CanonicalSubtypeWitness(target: SubtypeWitnessTarget)
  | ErrorSubtypeWitnessIdentity(error: ErrorId)

SubtypeWitnessId = ContentId<SubtypeWitnessIdentity>

SubtypeWitnessForm =
    ConcreteSubtypeWitness(target: SubtypeWitnessTarget)
  | GenericSubtypeWitness(binder: CanonicalGenericBinder,
                          targetPattern: SubtypeWitnessTarget)
  | AbstractSubtypeWitness(target: SubtypeWitnessTarget)
  | ErrorSubtypeWitnessForm(error: ErrorId)

WitnessTableDefinitionRefAt<Construction> =
    FrozenWitnessDefinition(ValidatedWitnessTableRef)
  | OperationalWitnessDefinition(OperationalWitnessTableRef)

WitnessTableDefinitionRefAt<Published> =
    FrozenWitnessDefinition(ValidatedWitnessTableRef)

WitnessResolutionSetAt<S: WitnessTableState> =
    CanonicallyOrderedMap<WitnessTableId, WitnessTableDefinitionRefAt<S>>

SubtypeWitnessOperation =
    WitnessTable(provider: WitnessTableId)
  | GenericWitnessTable(provider: WitnessTableId)
  | SpecializedWitnessTable(generic: SubtypeWitnessId,
                            specialization: CanonicalSpecializationSpine)
  | DeclaredSubtypeWitness(target: SubtypeWitnessTarget)
  | LookupSubtypeWitness(base: SubtypeWitnessId,
                         key: SubtypeWitnessLookupKey)
  | ExtractExistentialSubtypeWitness(opening: OpenedTypeId,
                             source: AnyASTNodeId<Typed>)
  | ErrorSubtypeWitness(error: ErrorId)

SubtypeWitnessCandidateAt<S: WitnessTableState> = {
    identity: SubtypeWitnessIdentity,
    form: SubtypeWitnessForm,
    operation: SubtypeWitnessOperation,
    resolutions: WitnessResolutionSetAt<S>,
    origin: Origin
}

SubtypeWitnessRecordAt<S: WitnessTableState> = {
    id: SubtypeWitnessId,
    identity: SubtypeWitnessIdentity,
    form: SubtypeWitnessForm,
    operation: SubtypeWitnessOperation,
    resolutions: WitnessResolutionSetAt<S>,
    origins: OriginSet where origins.count >= 1
}

SubtypeWitness = SubtypeWitnessRecordAt<Published>

SubtypeWitnessRegistryAt<S: WitnessTableState> =
    CanonicallyOrderedMap<SubtypeWitnessId, SubtypeWitnessRecordAt<S>>

SubtypeWitnessPublicationFailure =
    ConflictingSelectedWitnessDefinition(
        id: SubtypeWitnessId,
        existing: SubtypeWitnessOperation,
        incoming: SubtypeWitnessOperation,
        environments: NonEmpty<SemanticEnvironmentId>)

MergeSubtypeWitnessRegistriesAt<S>(
    inputs: NonEmpty<SubtypeWitnessRegistryAt<S>>)
        -> Result<SubtypeWitnessRegistryAt<S>, SubtypeWitnessPublicationFailure>

SubtypeWitnessCandidateComparison =
    SameWitnessCandidate
  | PreferWitnessLeft(proof: SubtypeWitnessSpecificityProof)
  | PreferWitnessRight(proof: SubtypeWitnessSpecificityProof)
  | IncomparableWitnessCandidates(reason: SubtypeWitnessIncomparability)

SubtypeWitnessSpecificityProof =
    MoreSpecificConformanceProvider(proof: ConformanceProviderSpecificityProof)
  | MoreSpecificSuperFacetRoute(proof: FacetPriorityProof)
  | RegisteredWitnessPriority(rule: RuleId, inputs: CanonicalArguments)

SubtypeWitnessIncomparability =
    EqualTargetDuplicateProviders(left: SubtypeWitnessOperation,
                                  right: SubtypeWitnessOperation)
  | IncomparableProviderSpecificity(left: SubtypeWitnessOperation,
                                    right: SubtypeWitnessOperation)
  | ConflictingCanonicalPaths(left: SubtypeWitnessOperation,
                              right: SubtypeWitnessOperation)
  | ConflictingWitnessPriorityProofs(NonEmpty<SubtypeWitnessSpecificityProof>)

SelectCanonicalSubtypeWitness(
    environment: SemanticEnvironmentId,
    target: SubtypeWitnessTarget,
    candidates: NonEmpty<SubtypeWitnessCandidateAt<S>>)
        -> QueryStep<CanonicalSubtypeWitnessSelectionAt<S>>

CanonicalSubtypeWitnessSelectionAt<S: WitnessTableState> =
    SelectedCanonicalWitness(record: SubtypeWitnessRecordAt<S>,
                             comparisons: NodeList<SubtypeWitnessCandidateComparison>)
  | AmbiguousCanonicalWitness(maximal: NonEmpty<SubtypeWitnessCandidateAt<S>>,
                              comparisons: NodeList<SubtypeWitnessCandidateComparison>)

TypePackSubtypeWitnessForm =
    ConcreteWitnessTargets(targets: NodeList<SubtypeWitnessTarget>)
  | GenericWitnessTargetPack(pattern: SubtypeWitnessTarget,
                             captures: NonEmpty<PackId>)

TypePackSubtypeWitnessOperation =
    ConcreteWitnessPack(elements: NodeList<SubtypeWitnessId>)
  | MapWitnessPack(pattern: SubtypeWitnessId,
                   captures: NonEmpty<PackId>)

TypePackSubtypeWitnessKey = {
    form: TypePackSubtypeWitnessForm,
    operation: TypePackSubtypeWitnessOperation
}

TypePackSubtypeWitnessId = ContentId<TypePackSubtypeWitnessKey>

TypePackSubtypeWitnessRecordAt<S: WitnessTableState> = {
    id: TypePackSubtypeWitnessId,
    key: TypePackSubtypeWitnessKey,
    resolutions: WitnessResolutionSetAt<S>
}

TypePackSubtypeWitness = TypePackSubtypeWitnessRecordAt<Published>

WitnessFormResult =
    Classified(SubtypeWitnessForm)
  | InvalidWitnessOperation(WitnessValidationFailure)

WitnessValidationFailure =
    WitnessTableFormMismatch(provider: WitnessTableId)
  | IncompleteWitnessSpecialization(generic: SubtypeWitnessId)
  | DeclaredConformanceNotActive(target: SubtypeWitnessTarget)
  | DuplicateDeclaredConformance(target: SubtypeWitnessTarget,
                                 slots: NonEmpty<CanonicalConstraintSlot>)
  | InterfaceRequirementUnavailable(base: SubtypeWitnessId,
                                    key: InterfaceRequirementKey)
  | InvalidExistentialOpening(opening: OpenedTypeId)
  | WitnessResolutionMismatch(provider: WitnessTableId)

deriveSubtypeWitnessForm(WitnessTable(p)) =
    concreteFormOfWitnessTable(p)
deriveSubtypeWitnessForm(GenericWitnessTable(p)) =
    genericFormOfWitnessTable(p)
deriveSubtypeWitnessForm(SpecializedWitnessTable(g, s)) =
    specializeGenericForm(formOf(g), s)
deriveSubtypeWitnessForm(DeclaredSubtypeWitness(t)) =
    AbstractSubtypeWitness(t)
deriveSubtypeWitnessForm(LookupSubtypeWitness(w, k)) =
    formOfInterfaceRequirement(formOf(w), k)
deriveSubtypeWitnessForm(ExtractExistentialSubtypeWitness(o, n)) =
    formOfExistentialOpening(o, n)
deriveSubtypeWitnessForm(ErrorSubtypeWitness(e)) =
    ErrorSubtypeWitnessForm(e)

deriveSubtypeWitnessTarget(WitnessTable(p)) =
    targetOfConcreteWitnessTable(p)
deriveSubtypeWitnessTarget(GenericWitnessTable(p)) =
    targetPatternOfGenericWitnessTable(p)
deriveSubtypeWitnessTarget(SpecializedWitnessTable(g, s)) =
    apply(s, targetOf(g))
deriveSubtypeWitnessTarget(DeclaredSubtypeWitness(t)) = t
deriveSubtypeWitnessTarget(LookupSubtypeWitness(w, k)) =
    targetOfInterfaceRequirement(targetOf(w), k)
deriveSubtypeWitnessTarget(ExtractExistentialSubtypeWitness(o, n)) =
    targetOfExistentialOpening(o, n)

requiredDefinitions(WitnessTable(p)) = {p}
requiredDefinitions(GenericWitnessTable(p)) = {p}
requiredDefinitions(SpecializedWitnessTable(g, s)) =
    requiredDefinitions(resolve(g).operation) union directWitnessDefinitions(s)
requiredDefinitions(DeclaredSubtypeWitness(_)) = {}
requiredDefinitions(LookupSubtypeWitness(w, k)) =
    requiredDefinitions(resolve(w).operation) union
    directDefinitionsOfLookedUpWitness(w, k)
requiredDefinitions(ExtractExistentialSubtypeWitness(_, _)) = {}
requiredDefinitions(ErrorSubtypeWitness(_)) = {}
```

`WitnessTable` is the witness table as a proof value; it is not an assertion wrapped around a
separate proof. Its stable operation names the `WitnessTableId`; the stage-specific resolution set
names the exact complete definition used to validate or lower it. A generic table is a generic
semantic value whose witness-table form contains a binder and target pattern. Applying
`SpecializedWitnessTable` produces a candidate operation for the substituted target. For example,
the conformance declared by `S<T> : IBase<T>` is represented once as a `GenericWitnessTable`; the
evidence for `S<float> : IBase<float>` is its specialization, not a fresh nongeneric table or a
decl-ref with hidden substitution state. After coherence selection, the table or specialization is
itself the selected proof value; no assertion wrapper is added around it.

`SUB-WIT-000`: Every non-recovery witness has identity
`ContentId(CanonicalSubtypeWitness(target))`. Thus there is exactly one `SubtypeWitnessId` for a
`(subtype, superInterface)` pair; provider, semantic environment, inheritance path, operation,
origin, and definition revision do not create competing IDs. They are candidate-discovery or
selected-definition facts. A semantic snapshot publishes at most one selected definition for that
ID. Combining modules or environments that selected incompatible definitions is a coherence error,
not permission to mint another witness ID. Construction-to-publication changes an
`OperationalWitnessDefinition` resolution into a `FrozenWitnessDefinition` for the same
`WitnessTableId`; it cannot change any witness ID. Every provider reachable from the selected operation has
exactly one resolution of the permitted stage, and no unrelated resolution may be retained.

`SUB-WIT-008`: `deriveSubtypeWitnessForm` is a total constructor-by-constructor validation query.
The two table constructors require the matching concrete/generic witness-table form;
specialization is total and kind-correct; declared generic evidence has exactly one active
`Conforms(sub, interface)` slot keyed by the pair-only witness ID;
lookup uses the stored active entry key; and existential opening proves the package contains the
requested interface. `record.form` equals its `Classified` result,
`deriveSubtypeWitnessTarget(record.operation)` equals the target in `record.identity`,
`record.id = ContentId(record.identity)`, and the domain of `record.resolutions` equals
`requiredDefinitions(record.operation)`. Every resolution map key equals the identity inside its
definition ref. Missing, extra, stage-invalid, or target-mismatched resolutions fail validation;
they are not recovered by ambient conformance search.
`directDefinitionsOfLookedUpWitness(base, key)` is the exact resolution set stored on the
kind-correct nested witness payload at that entry; it does not rerun conformance search. This makes
a lookup record retain both the table needed to perform the lookup and any table definitions needed
when the looked-up witness is later materialized.

`SUB-WIT-010`: `SelectCanonicalSubtypeWitness` compares every pair of target-equal candidates and
selects one unique strict maximum under explicit specificity proofs. Two byte-equal candidate
operations discovered through the same provider and path are duplicate discovery of the same
candidate, not two witnesses. Distinct source providers or operational paths for the same endpoint
remain distinct even when their output types or lowering results happen to match; one must strictly
dominate every other candidate through a named provider/path specificity proof. Otherwise the
maximal candidates are a compile-time ambiguity. Source order, import order, task completion, hash
order, arbitrary shortest-path choice, and a post-hoc equivalence assertion are never selection
rules. The selected record's `origins` is exactly the canonical union of origins from candidates
whose identity, form, operation, and resolution set are byte-identical to the winner; a distinct
shadowed provider/path is retained in comparisons, not relabeled as winner provenance.

`SUB-WIT-011`: A `SubtypeWitnessRegistryAt<S>` key equals its record's `id`, and every non-error
record ID is the content identity of only its endpoint target. Merging semantic environments accepts
duplicate records only when identity, selected operation, stage-correct resolution set, and form are
byte-identical; it unions their canonical nonempty `origins` sets. Origins diagnose where the same
proof value was used or rediscovered and never distinguish witnesses. Any different semantic record
for the same ID returns `ConflictingSelectedWitnessDefinition`; the merge cannot choose by
environment order, retain two records, or salt the ID with an environment. Provider specificity
must be resolved before publication by `SelectCanonicalSubtypeWitness`.

`SUB-WIT-009`: `directWitnessDefinitions(specialization)` traverses every type/value argument and
keyed constraint evidence in the canonical spine. It unions the recorded definition dependencies
of referenced types/constants and every `SubtypeWitness` reachable by the evidence
schema, including subtype-witness and `ValueDifferentialInfoEvidence` operands. Thus specializing a generic table
with a table-backed witness argument retains the definition needed to materialize that runtime
operand; it cannot disappear merely because the outer generic table has a different provider.

`SUB-WIT-001`: Every non-recovery operation has exactly one witness form derivable from its operands.
`WitnessTable` resolves a definition whose target equals the concrete form's target.
`GenericWitnessTable` contains precisely the free variables of its binder. A specialization is
total, kind-correct, and applies ordinary arguments and constraint evidence together to the target,
requirements, inherited entries, and dependencies in the resolved definition. Constructing any of
these operations creates or contributes a candidate; only canonical selection publishes the
pair-identified witness record.

`SUB-WIT-002`: `DeclaredSubtypeWitness(target)` is the canonical open proof value for a generic
context's active `Conforms(target)` evidence. The operation repeats only the endpoint pair and
therefore cannot distinguish two alpha-equivalent proofs by source-binder identity or constraint
ordinal. At a use, the generic-evidence environment must contain exactly one active conformance
slot whose substituted predicate is that target; absence is `DeclaredConformanceNotActive` and a
duplicate is `DuplicateDeclaredConformance`. Generic IR parameters and specialization evidence are
projected to the resulting pair-only `SubtypeWitnessId`; source `SpecializationFrame` and IR-ready
specialization maps remain keyed by `CanonicalConstraintSlot` but each `Conforms` value must have
that exact witness ID. Function ABI construction rejects duplicate projections and keys its witness
input role by the pair-only ID, while the source slot remains diagnostic/mapping provenance. A
synthetic `ValidatedWitnessTableRef` must not be invented for it.

`SUB-WIT-003`: `LookupSubtypeWitness(base, key)` is valid only when `key` is either a base-interface
entry or a conformance-requirement entry, the base table contains that exact active key, and its
payload is a `SubtypeWitness`. Its result target is the payload
target. Requirement declaration identity, source position, or the desired result interface cannot
stand in for `key`. The result ID is the canonical pair-only ID for that target; the selected
definition retains this exact `LookupSubtypeWitness(base, key)` operation.

`SUB-WIT-004`: There is no general transitive-witness constructor. Composing `A <: B` with a
declared `B <: C` projection means `LookupSubtypeWitness(aToB, keyOfBToC)`. A longer route is a
left-to-right spine of lookup nodes, one for each semantic witness-table lookup. The spine is the
candidate proof and operational plan at the same time. If another spine reaches the same `A <: C`
endpoint, canonical selection must prefer one by a named specificity rule or diagnose ambiguity;
it cannot collapse distinct operations by asserted equivalence or publish a second witness ID.

`SUB-WIT-005`: A witness table, bound witness parameter, specialization, lookup result, or opened
existential witness may satisfy a `Conforms` constraint when its target matches. Static conformance
definition references are only one source of witness values; APIs such as generic solving,
existential packing, associated-type projection, and witness dispatch accept
`SubtypeWitnessId`, not only `ValidatedWitnessTableRef`.

`SUB-WIT-006`: `ErrorSubtypeWitness` supports typed recovery but cannot discharge a successful
generic constraint, publish an existential, select a witness call, or enter a module interface.

`SUB-WIT-007`: Witness packs inhabit `TypePackSubtypeWitnessId`, never the singular witness
form. `ConcreteWitnessPack` has the same length as `ConcreteWitnessTargets` and each element
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

| witness operation                  | frontend IR operation                                                 |
| ---------------------------------- | --------------------------------------------------------------------- |
| `WitnessTable`                     | `IRWitnessTable` (`witness_table`)                                    |
| `GenericWitnessTable`              | generic `IRWitnessTable` declaration/definition                       |
| `SpecializedWitnessTable`          | `IRSpecialize` (`specialize`)                                         |
| `DeclaredSubtypeWitness`           | value parameter of `IRWitnessTableType`                               |
| `LookupSubtypeWitness`             | `IRLookupWitnessMethod` (`lookupWitness`)                             |
| `ExtractExistentialSubtypeWitness` | `IRExtractExistentialWitnessTable` (`extractExistentialWitnessTable`) |
| witness-pack expansion             | registered pack expansion producing singular witness values           |

`SUB-IR-001`: Lowering one `LookupSubtypeWitness(base, key)` emits exactly one
`IRLookupWitnessMethod` (`lookupWitness`) with operands
`[lower(base), lowerInterfaceRequirementKey(key)]` in that exact order. It may constant-fold the
result later, but semantic-to-IR lowering neither replaces the lookup with a binary transitive proof
nor reconstructs a key from endpoint types.

`SUB-IR-002`: A witness call consumes a witness-table IR value plus a
`RuntimeInterfaceRequirementKey`. A static table is first materialized as a witness value; a generic
parameter, specialization, lookup result, and existential extraction use the same operand position.
The call operation does not require an `IRSymbolRef` where a runtime witness value is semantically
required.

`SUB-IR-002a`: Lowering `DeclaredSubtypeWitness(target)` resolves the current generic IR
environment by `ContentId(CanonicalSubtypeWitness(target))` and emits that exact witness parameter.
Constraint declaration order and source binder identity cannot choose the operand. Binder lowering
rejects duplicate `Conforms` constraints that would insert two parameters under the same key, so
semantic validation and IR lookup enforce the same pair-only uniqueness rule.

`SUB-IR-003`: Every chapter 9 `LookupRequirement<K>` specialization uses
`IRLookupWitnessMethod` (`lookupWitness`) with the same table operand and complete
`SomeInterfaceRequirementKey`. A conformance-requirement
projection used as subtype evidence instead constructs `LookupSubtypeWitness` and therefore emits
the same operation. The associated-type specialization remains a `Type` constructor, the
constant-associated-value specialization remains a `ConstValue`, and only callable-like entries are
projected to runtime callable slots; lowering correspondence does not erase their frontend domains.

## Aggregate clauses and excluded struct inheritance

The written colon syntax is classified by aggregate kind; there is no common semantic
“inheritance clause” constructor:

```text
CheckedAggregateClause =
    ClassBase(base: TypeId,
              declaration: DeclId,
              adjustment: RepresentationAdjustmentStep)
  | InterfaceConformance(interface: InterfaceInstanceKey,
                         provider: WitnessTableId)
  | BaseInterface(base: InterfaceInstanceKey,
                  clause: InterfaceInheritanceClauseId)
  | EnumTagType(type: TypeId)
  | ErrorAggregateClause(error: ErrorId)
```

`SUB-AGG-001`: A modern struct accepts only `InterfaceConformance` entries. A class accepts at most
one `ClassBase` and zero or more interface conformances. An interface accepts only base-interface
clauses. An enum accepts its registered tag-type form and any separately
declared interface conformances.

`SUB-AGG-002`: Concrete struct inheritance is excluded from the proposed language. A Slang 2026
parse/check diagnoses the clause and constructs no checked `LegacyStructBase`, representation
proof, base facet, base subobject,
aggregate-initialization slot, or IR base conversion. Standard-library relationships that need
representation semantics are registered standard-environment rules, not exemptions based on source
module name.

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
clause. No step names a struct base, interface conformance, or base-interface inheritance.

`SUB-REP-002`: Composition concatenates validated paths and then applies only declared
identity/canonical-step reductions. It does not form an unordered binary transitivity tree.

## Facet routes

A facet is one member-providing view reached through an explicit route:

```text
FacetRouteStep =
    RepresentationBaseRoute(step: RepresentationAdjustmentStep)
  | InterfaceConformanceRoute(witness: SubtypeWitnessId)
  | BaseInterfaceRoute(key: SubtypeWitnessLookupKey,
                       projected: SubtypeWitnessId)
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
            BaseInterfaceFacet | ExtensionFacet | OpenedExistentialFacet

CanonicalSuperFacetKey = {
    root: TypeId,
    superInterface: InterfaceInstanceKey
}

CanonicalSuperFacetSelection = {
    key: CanonicalSuperFacetKey,
    facet: FacetKey,
    witness: SubtypeWitnessId,
    comparisons: NodeList<SubtypeWitnessCandidateComparison>
}
```

`SUB-FAC-001`: Folding a facet route from its root produces the facet owner and evidence. A
base-interface route step applies exactly one `LookupSubtypeWitness` with the stored key. Its
`projected` ID is the canonical ID for the resulting endpoint, and that ID's selected operation is
exactly `LookupSubtypeWitness(previousWitness, key)`. The facet's witness value is therefore a
validated view of its route, never independently composed side state.

`SUB-FAC-002`: Path-distinct diamond routes are representable as construction candidates, but they
do not become two published super-interface facets for the same `CanonicalSuperFacetKey`.
Byte-identical rediscovery of the same provider/path is deduplicated; genuinely distinct routes
require one route to be strictly preferred by a named priority rule or produce an ambiguity. The
selected route and pair-identified witness then form the sole canonical super facet. Thus a member
lookup, associated-type projection, and IR lowering all observe the same path.

`SUB-FAC-003`: A facet key never omits its selected semantic route and then relies on map-insertion
conflict handling to recover it. `FacetSet.byKey` may retain unrelated representation and extension
facets, but its `canonicalSuperFacets` map contains exactly one entry for every reachable
`CanonicalSuperFacetKey`. A second non-equivalent route is an error result, not another successful
map entry.

`SUB-FAC-004`: `Facet.witnessResolutions` is a dependency sidecar, not route identity. It is the
minimal canonical union required by every witness ID in the route and folded member evidence.
`FacetSet.equivalence` persists every nontrivial proof used for general member-provider route
classes, but cannot equate operationally distinct subtype-witness paths. Each
`CanonicalSuperFacetSelection.comparisons` persists the duplicate-discovery or strict-priority proof
for its witness/path choice; a producer cannot merge facets using a transient comparison result and
then discard the proof.

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

ExtensionCapabilityUseInputsAt<S: WitnessTableState> = {
    extension: CapabilityUse<S>,
    target: Option<CapabilityUse<S>>
}

ExtensionFacetUseResultAt<S: WitnessTableState> =
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

InvalidExtensionTarget =
    InterfaceExtensionTarget(interface: DeclId)
  | ExistentialExtensionTarget(type: TypeId)

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

`SUB-EXT-006`: The target of a source extension cannot be an interface declaration or existential
container; in particular, `extension IFoo` is rejected while checking the extension header and
produces no intrinsic-applicability result, member facet, or conformance provider. A generic
extension may target a concrete nominal pattern and constrain its parameters by interfaces, but the
matched target remains that concrete pattern rather than “all values of an interface.” This is a
source-language rule, not an interpretation chosen later by member lookup.

The compatibility inventory for extension priority is
`SemanticsVisitor::CompareLookupResultItems` in `source/slang/slang-check-overload.cpp`: it currently
prefers declared members over extensions, ordinary extension targets over the free-form
`extension<T : IFoo> T` pattern, nongeneric over generic extensions, and requirements from more
derived interfaces. The normative relation here states the common principle explicitly: the
preferred candidate's applicability set must be a strict subset of the shadowed candidate's set,
proved by target-pattern matching plus generic-constraint implication. The parameter-count
heuristic in `compareOverloadCandidateSpecificity` and the relaxed-C3/list order in
`source/slang/slang-check-inheritance.cpp` are implementation evidence, not semantic tie-breakers.
When applicability-set inclusion proves neither candidate more specific, witness-provider
selection diagnoses ambiguity and ordinary member lookup retains both candidates as applicable.

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
    NoPriorityRule(left: FacetKey, right: FacetKey)
  | PathDistinctInterfaceViews(left: FacetRouteKey, right: FacetRouteKey)
  | IncomparableExtensions(left: DeclRef, right: DeclRef)
  | ConflictingPriorityProofs(proofs: NonEmpty<FacetPriorityProof>)

RepresentationRoutePrefixProof = {
    prefix: FacetRouteKey,
    full: FacetRouteKey,
    representationSuffix: NonEmpty<RepresentationAdjustmentStep>
}

ExtensionSpecializationProof = {
    preferred: DeclRef,
    shadowed: DeclRef,
    targetMatch: CanonicalSpecializationSpine,
    constraintImplication: GenericConstraintImplicationProof,
    strict: TargetStrict | ConstraintStrict | BothStrict
}

OverrideSignatureProof =
    ExactOverrideSignature(FuncTypeEqualityProof)
  | RegisteredOverrideSignature(rule: RuleId, inputs: CanonicalArguments)

DeclaredOverrideProof = {
    overriding: DeclId,
    overridden: DeclId,
    signature: OverrideSignatureProof,
    rule: RuleId
}

FacetPriorityProof =
    SelfFacetHasPriorityOverNonSelf(self: FacetKey, other: FacetKey)
  | DeclaredMemberShadowsExtension(member: FacetKey, extension: FacetKey)
  | ShorterRepresentationPathHasPriority(preferred: FacetKey,
                                       shadowed: FacetKey,
                                       prefix: RepresentationRoutePrefixProof)
  | MoreSpecificExtensionHasPriority(preferred: FacetKey,
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
    ProviderFacetHasPriority(preferred: FacetKey,
                           shadowed: FacetKey,
                           proof: FacetPriorityProof)
  | ExplicitOverrideShadows(overridingProvider: FacetKey,
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
    SameBoundDecl(use: DeclRef)
  | TransportedMemberEquivalence(leftProvider: FacetKey,
                                 rightProvider: FacetKey,
                                 leftMember: DeclId,
                                 rightMember: DeclId,
                                 proof: FacetEquivalenceProof)

MemberCandidateIncomparability =
    IncomparableProviders(FacetIncomparability)
  | NoMemberPriorityRule(left: DeclId, right: DeclId)
  | LegalOverloadPair(left: DeclId, right: DeclId)
```

`SUB-PRI-001`: Lookup gathers all reachable candidates, applies access and applicability filters,
and retains the maximal candidates under the partial priority relation. A single maximal candidate
is selected; overloadable maxima form an overload set; multiple non-overloadable or
indistinguishable maxima are an ambiguity.

`SUB-PRI-002`: A direct declared member of the queried type dominates same-name non-self and
extension providers unless the declarations form a legal overload set. A declaration in an
base-interface declaration shadows an inherited requirement only through
`ExplicitOverrideShadows`, whose provider and declaration endpoints validate the exact two
same-name candidates. Such a proof is never inserted as a global `FacetSet.priority` edge and
cannot affect other member names. Merely reaching the same declaration by a shorter interface
diamond arm is not a specificity proof: canonical super-facet construction must apply a named
strict priority rule or diagnose ambiguity. Callable
specificity is evaluated only after lookup forms the overload set; it is not a facet-priority proof.

`SUB-PRI-003`: Lexical/import proximity decides whether an extension is reachable and supplies
diagnostic context. It is not a silent semantic tie-break between otherwise incomparable extension
members. Stable source order is used only to render deterministic ambiguity diagnostics.

`SUB-PRI-004`: A total C3 sequence is not applied across class representation bases, interface
base interfaces, conformances, and extensions as if they were one relation. The class representation
base is a single chain. Interface route candidates retain path identity until canonical
super-facet/witness selection; extension candidates use the partial priority relation above. A
`RepresentationRoutePrefixProof` is valid only when its two routes have
the same root and
`full.steps = prefix.steps ++ map(RepresentationBaseRoute, representationSuffix)`. Consequently
`ShorterRepresentationPathHasPriority(preferred, shadowed, proof)` additionally requires
`preferred.route = proof.prefix` and `shadowed.route = proof.full`; it cannot be constructed by
dropping an interface-conformance, base-interface, existential-opening, or extension route
step.

## Validation obligations

Generated validators and unit suites cover:

- every witness-operation/form pair, substitution, serialization, invalid endpoint, and the invariant
  that one semantic snapshot resolves one endpoint pair to one witness ID/selected definition and
  rejects incompatible definitions while composing environments;
- generic witness abstraction/specialization with type, value, pack, and witness arguments;
- one semantic `LookupSubtypeWitness` value/operation to one frontend-IR
  `IRLookupWitnessMethod`;
- static, generic-parameter, specialized, nested-lookup, and existential witness calls;
- diamonds with equal endpoints, strict route specificity, same-provider/path deduplication, and
  rejection of incomparable paths or duplicate maximal providers;
- class representation chains and rejection of every concrete struct-base spelling;
- rejection of every interface/existential extension target, including `extension IFoo`;
- extension target mismatch, blocked constraints, reachability, concrete availability, and
  specificity; reuse of intrinsic evidence across regions; region-sensitive facet IDs that remain
  independent of caller use origin; and exact once-only committed extension/target ordinary uses;
  and
- all four partial-priority results without source/import/container-order selection.

The current compiler's subtype/facet implementation is test evidence for compatibility, especially
where it exposes missing cases. Its mutable facet lists, `TransitiveSubtypeWitness`, and lowering
assertions are not normative representations.
