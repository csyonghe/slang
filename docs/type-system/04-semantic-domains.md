# Semantic domains

This chapter defines the immutable values exchanged by semantic rules. Later chapters define how
the values are computed. Keeping the domains separate from the algorithms is what makes a primitive
such as substitution, conversion comparison, or capability implication directly unit-testable.

## Names and declaration identity

```text
Name = {
    text: InternedString,
    hygiene: HygieneId,
    class: NameClass,
    origin: Origin
}

HygieneId = Unhygienic | HygienicExpansion(origin: TokenOriginId)

NameClass =
    IdentifierName
  | OperatorName
  | ConstructorName
  | AccessorName(role: GetterName | SetterName | RefAccessorName(AccessMode))
  | ContextualName(feature: SyntaxFeatureId)

NameKey = {
    normalizedText: Utf8String,
    class: NameClass,
    hygiene: HygieneId
}

DeclKind = {
    stableName: QualifiedName,
    wireTag: UInt32,
    schema: SchemaVersion
}

DeclarationPathSegment =
    NamedDeclarationSegment(name: NameKey, kind: DeclKind)
  | AnonymousDeclarationSegment(role: QualifiedName,
                                anchor: ContentId<SemanticValue>,
                                ordinal: UInt32)

CanonicalDeclarationPath = NodeList<DeclarationPathSegment>

CanonicalSignatureEncoding = {
    schema: SchemaVersion,
    bytes: ByteString
}

ModuleStableId = stable nominal module identity allocated by module-graph freezing
ModuleId = ModuleStableId

DeclarationDisambiguator =
    NonOverloadableDeclaration(kind: DeclKind)
  | OverloadableDeclaration(kind: DeclKind,
                            signature: CanonicalSignatureEncoding)
  | AnonymousDeclaration(anchor: ContentId<SemanticValue>, ordinal: UInt32)
  | SynthesizedDeclaration(SynthesizedSemanticId)

DeclId = {
    module: ModuleStableId,
    path: CanonicalDeclarationPath,
    disambiguator: DeclarationDisambiguator
}

DeclarationFragmentKey = {
    syntax: NodeId<Surface>,
    kind: DeclKind
}

DeclarationFragmentId = ContentId<DeclarationFragmentKey>

InterfaceInstanceKey = {
    interface: DeclId,
    arguments: CanonicalSubstitution
}

RefinementStepKey = {
    derived: InterfaceInstanceKey,
    clause: RefinementClauseId,
    base: InterfaceInstanceKey
}

RequirementKey<K> = {
    view: InterfaceInstanceKey,
    declaredIn: InterfaceInstanceKey,
    declaration: DeclId,
    refinementPath: NodeList<RefinementStepKey>,
    kind: K
}

SourceParameterKey = DeclId
ExpansionPath = NodeList<PackExpansionIndex>
ParameterKey = (source: SourceParameterKey, expansion: ExpansionPath)
```

`nameKey` NFC-normalizes identifier text, preserves the exact `NameClass`, and copies the hygiene
identity. Physical source and today's unhygienic macro expansion use `Unhygienic`; a language mode
that enables hygienic expansion must supply the originating `TokenOriginId`. Source spelling and
provenance remain available through `Name.origin` and the originating token but cannot affect map
identity. Operator names, constructors, accessors, and contextual syntax have declared classes
instead of magic strings.

`TYP-NAM-001`: `NameKey` equality is exact equality of all three fields. A scope map, declaration
grouping rule, or label comparison may apply a different language relation only through a named
rule; it may not compare intern-pool addresses or silently discard hygiene.

`TYP-NAM-002`: `nameKey(Name).normalizedText` is the language-rule-set normalization of
`Name.text`. `OperatorName` is a tag; its complete normalized operator spelling occurs only in
`normalizedText`. Constructor/accessor/contextual classes likewise add only the semantic role shown
by their payload. It is invalid to construct a key whose normalized text or class disagrees with
the source `Name`, so a second spelling field cannot split or alias operator identity.

`TYP-DID-001`: `DeclId` equality is exact field equality. Named path segments use canonical
`NameKey` values; anonymous anchors are collision-safe content IDs and their ordinal is assigned in
canonical field-role order, never task or map iteration order. The disambiguator is selected by the
declaration-kind registry: non-overloadable declarations use their kind, overloadable declarations
use the versioned alpha-normalized redeclaration identity shape, anonymous declarations use their
syntax anchor/role ordinal, and synthesized declarations use their synthesis identity. No hash,
source byte offset, provisional handle, or definition revision defines nominal equality.

`TYP-DID-002`: `DeclarationFragmentId` is the exact content ID of one Surface-AST declaration node
and its declared kind. Its discriminator includes the full snapshot-local `NodeId<Surface>` tuple,
so two written occurrences never alias even when their text is equal. Redeclaration freezing may map
many fragments to one `DeclId`, but neither conversion direction is implicit.

A declaration is a product of independently queryable facts:

```text
CheckedModifierKey = {
    kind: QualifiedName,
    arguments: CanonicalArguments
}

CheckedModifier = {
    key: CheckedModifierKey,
    origins: NonEmpty<Origin>
}

CheckedModifierSet =
    CanonicallyOrderedMap<CheckedModifierKey, CheckedModifier>

Declaration = {
    id: DeclId,
    kind: DeclKind,
    name: Option<Name>,
    parent: Option<DeclId>,
    lexicalScope: ScopeId,
    origin: Origin
}

DeclHeader = {
    declaration: DeclId,
    genericBinder: Option<GenericBinderId>,
    declaredType: Option<TypeId>,
    callableSignature: Option<CallableSignature>,
    callableResultAuthority: Option<CallableResultAuthorityId>,
    modifiers: CheckedModifierSet,
    visibility: Visibility,
    declaredEffects: Option<DeclaredEffectContractId>,
    declaredCapabilities: Option<DeclaredCapabilityContractId>,
    concreteAvailability: Option<ConcreteAvailabilityId>
}
```

`DeclKind` and modifier kinds come from versioned schema registries, not C++ RTTI, parser class
addresses, or rendered names. A modifier-set map key equals the stored modifier's `key`; canonical
equality ignores source order, while `origins` retains every written or synthesized occurrence for
duplicate validation and diagnostics. The declaration-kind registry also states which kinds are
overloadable and supplies their canonical signature-identity schema.

The base `Declaration` may be published before its header so mutually recursive nominal
declarations can refer to identity without observing an incomplete header.

Callable headers have a declared effect contract; another declaration kind has one only when its
kind schema defines effectful execution. `declaredCapabilities` is permitted for every capability-
bearing kind, including callables, types, extensions, conformances, and registered declaration
surfaces. The kind registry defines whether that declaration participates in body inference;
containers such as extensions that have no independently inferred body retain their declared
ordinary requirement directly as the requirement of a selected use. Any admitted kind may also
have a separately validated `concreteAvailability`; absence means that the declaration is not
filtered by the current compilation region. An unannotated callable still has concrete declared
effect/capability facts (`constrained=false`, empty effects, unconstrained/true ordinary capability
requirement), so explicit/inherited origins and caller-inference semantics are never lost in a bare
formula copied into the header. Concrete availability is never synthesized from an ordinary
contract.

`DeclHeader.genericBinder` is a reference into the semantic environment's authoritative
`GenericBinderTable`, not an embedded binder value. A present reference resolves to a binder whose
`owner` equals `DeclHeader.declaration`; absence means that declaration has no direct binder entry.

## Scopes and lookup candidates

```text
ScopeKind = ModuleScope | FileScope | NamespaceScope | TypeScope |
            GenericBinderScope | ParameterBinderScope | FunctionScope | BlockScope

ScopePolicy = UnorderedMembers | SourceOrderedMembers | SequentialBinder

ScopePosition = {
    scope: ScopeId,
    ordinal: UInt64
}

FragmentScope = {
    id: ScopeId,
    kind: ScopeKind,
    policy: ScopePolicy,
    parent: Option<ScopeId>,
    parentEntry: Option<ScopePosition>,
    lexicalMembers: NodeMap<NameKey, NodeList<DeclarationFragmentId>>,
    nodePositions: NodeMap<NodeId<Scoped>, ScopePosition>,
    bindingPoints: NodeMap<DeclarationFragmentId, ScopePosition>,
    endPosition: ScopePosition,
    origin: Origin
}

FrozenScope = {
    id: ScopeId,
    kind: ScopeKind,
    policy: ScopePolicy,
    parent: Option<ScopeId>,
    parentEntry: Option<ScopePosition>,
    lexicalMembers: NodeMap<NameKey, NodeList<DeclId>>,
    nodePositions: NodeMap<NodeId<Scoped>, ScopePosition>,
    bindingPoints: NodeMap<DeclId, ScopePosition>,
    endPosition: ScopePosition,
    importedScopes: NodeList<ImportEdge>,
    extensions: NodeList<DeclId>,
    origin: Origin
}

Scope = FrozenScope

SemanticVersion = (major: UInt32, minor: UInt32, patch: UInt32)
DialectId = QualifiedName
StandardEnvironmentId = ContentId<SemanticValue>

StandardEnvironmentRuleKey = {
    registry: QualifiedName,
    name: QualifiedName,
    schema: SchemaVersion
}

StandardEnvironmentRuleId = ContentId<StandardEnvironmentRuleKey>

RegisteredCallableRule = {
    registration: StandardEnvironmentRuleId,
    environment: StandardEnvironmentId,
    callableRule: RuleId,
    staticInputs: CanonicalArguments
}

RegisteredDataOperationRegistration = {
    rule: StandardEnvironmentRuleId,
    environment: StandardEnvironmentId,
    staticInputs: CanonicalArguments
}

LanguageRuleSet = {
    version: SemanticVersion,
    dialects: CanonicallyOrderedSet<DialectId>,
    enabledRules: CanonicallyOrderedSet<RuleId>,
    standardEnvironment: StandardEnvironmentId
}

LanguageRuleSetId = ContentId<LanguageRuleSet>

GenericEnvironmentFrame = {
    binder: GenericBinderId,
    arguments: Substitution,
    evidence: NodeMap<ConstraintKey, ConstraintEvidence>,
    optionalEvidence: NodeMap<ConstraintKey, OptionalEvidence>
}

GenericEnvironment = {
    frames: NodeList<GenericEnvironmentFrame>
}

GenericEnvironmentId = ContentId<GenericEnvironment>

SemanticEnvironment = {
    snapshot: SemanticSnapshotId,
    frozenScopes: ContentId<FrozenScopeGraph>,
    genericBinders: GenericBinderTableId,
    moduleGraph: ContentId<ModuleGraph>,
    languageRules: LanguageRuleSetId,
    standardEnvironment: StandardEnvironmentId
}

SemanticEnvironmentId = ContentId<SemanticEnvironment>

ContractSelectionContext = {
    world: Option<WorldAtomSet>,
    assumption: BooleanCapabilityPredicate
}

StableOrderKey =
    SourceOrder(document: SourceDocumentId, start: UInt64, end: UInt64,
                semanticTieBreaker: ByteString)
  | ImportedOrder(module: ModuleStableId, exported: ExportedId)
  | SynthesizedOrder(id: SynthesizedSemanticId)

LookupCandidate = {
    use: BoundDeclUse,
    lexicalDistance: UInt32,
    sourceOrder: StableOrderKey
}

LookupAmbiguityKind =
    MultipleNonOverloadableMaxima
  | IndistinguishableMaxima

LookupCandidateComparison = {
    left: BoundDeclUse,
    right: BoundDeclUse,
    result: MemberCandidatePriorityResult
}

LookupAmbiguity = {
    maximal: NonEmpty<LookupCandidate>,
    kind: LookupAmbiguityKind,
    comparisons: NodeList<LookupCandidateComparison>
}

LookupResult =
    NotFound(Name)
  | Found(NodeList<LookupCandidate>)
  | Ambiguous(LookupAmbiguity)
  | Recovered(NodeList<LookupCandidate>, ErrorId)
```

All environment IDs are `ContentId` values with chapter 1's exact discriminator bytes; a digest
collision cannot merge contexts. Generic frames are ordered lexically outer-to-inner and contain
only keys owned by their named binder. `StableOrderKey` is presentation metadata derived from a
physical/imported/synthesized origin; it never participates in semantic overload preference or
canonical declaration/type identity.

`TYP-ENV-001`: A `StandardEnvironmentRuleId` resolves to exactly one definition in the
`StandardEnvironmentId` named by the active language-rule set. The definition's registered input,
result, validation, and algebraic-law schemas have the exact `StandardEnvironmentRuleKey.schema`;
an environment cannot bind two definitions to one key. Changing semantics incompatibly requires a
new schema version, while changing an implementation without observable semantic change preserves
the ID.

`TYP-ENV-002`: A `RegisteredCallableRule` is a checked bridge between a standard-environment
registration and logical callable dispatch. Resolving `registration` in `environment` must name a
callable definition whose logical rule is exactly `callableRule` and whose accepted static inputs
are exactly `staticInputs`. Clients dispatch with `callableRule` and lower with `registration`; they
cannot guess one identity from the other or silently replace either one after selection.

`TYP-ENV-003`: A `RegisteredDataOperationRegistration` identifies one exact non-call application
schema in one standard-environment revision. It has no logical `RuleId` callable identity. A client
must validate the registered static/runtime endpoint and control schemas before constructing a
typed operation; registration alone is not evidence that arbitrary operands are applicable.

`TYP-LKP-001`: `LookupAmbiguity.maximal` is exactly the duplicate-free maximal candidate set under
chapter 14's member-priority relation. `comparisons` contains one endpoint-correct result for every
unordered pair of maxima, and none may prefer one endpoint; otherwise that endpoint set is not
maximal. A legal overload set is `Found`, not ambiguous. `MultipleNonOverloadableMaxima` contains a
non-overloadable conflicting pair; `IndistinguishableMaxima` contains a distinct pair related only
by `EquivalentMembers`. Diagnostics consume these stored results and never rerun facet priority.

A lookup path is an immutable sequence of typed edges such as lexical parent, imported module,
base facet, extension facet, transparent member, or implicit receiver. It is retained after binding
because it supplies substitutions, relation-specific member-access evidence, access context, and
diagnostics.

## Generic binders, arguments, and substitutions

```text
LocalGenericBinderIndex = UInt32

GenericBinderId = {
    snapshot: SemanticSnapshotId,
    index: LocalGenericBinderIndex
}

GenericParameterSort =
    TypeParameterSort(kind: Kind)
  | ValueParameterSort(type: TypeId)
  | TypePackParameterSort(elementKind: Kind)
  | ValuePackParameterSort(elementType: TypeId)

GenericParam = {
    id: DeclId,
    sort: GenericParameterSort,
    default: Option<GenericArg>
}

GenericBinder = {
    id: GenericBinderId,
    owner: DeclId,
    parameters: NodeList<GenericParam>,
    constraints: NodeList<ConstraintDecl>,
    parent: Option<GenericBinderId>
}

GenericBinderTable = {
    snapshot: SemanticSnapshotId,
    binders: NodeMap<GenericBinderId, GenericBinder>,
    byOwner: NodeMap<DeclId, GenericBinderId>
}

GenericBinderTableId = ContentId<GenericBinderTable>

ConstraintId = snapshot-local identity of one ConstraintDecl

ConstraintDecl = {
    id: ConstraintId,
    predicate: Constraint,
    optional: Bool,
    origin: Origin
}

GenericArg = TypeArg(TypeId) | ValueArg(ConstValue) |
             TypePackArg(NodeList<TypeId>) | ValuePackArg(NodeList<ConstValue>)

CanonicalSubstitution = NodeList<GenericArg>

GenericParameterKey = (binder: GenericBinderId, parameter: DeclId)
ConstraintKey = (binder: GenericBinderId, constraint: ConstraintId)
Substitution = NodeMap<GenericParameterKey, GenericArg>

CanonicalBoundVariable = {
    binderDepth: UInt32,
    parameterOrdinal: UInt32,
    sort: GenericParameterSort
}

PackElementDomain = TypePackElements(elementKind: Kind)
                  | ValuePackElements(elementType: TypeId)

PackId = {
    binderDepth: UInt32,
    parameterOrdinal: UInt32,
    elements: PackElementDomain
}

CanonicalGenericParameter = {
    ordinal: UInt32,
    sort: GenericParameterSort,
    default: Option<GenericArg>
}

ConstraintKind = EqualTypeKind | EqualValueKind | RepresentationAdjustmentKind |
                 InterfaceRefinesKind | ConformsKind | CoercibleKind |
                 PackCountEqualKind | PackNonEmptyKind | LifetimeOutlivesKind |
                 HasDifferentialInfoKind |
                 WellFormedKind

CanonicalConstraint = {
    slot: CanonicalConstraintSlot,
    predicate: Constraint,
    optional: Bool
}

CanonicalConstraintSet =
    CanonicallyOrderedMap<CanonicalConstraintSlot, CanonicalConstraint>

GenericConditionSet = CanonicalConstraintSet

CanonicalGenericBinder = {
    parameters: NodeList<CanonicalGenericParameter>,
    constraints: CanonicalConstraintSet,
    parentDepth: UInt32
}

CanonicalGenericBinderId = ContentId<CanonicalGenericBinder>

CanonicalConstraintSlot = {
    binderDepth: UInt32,
    constraintOrdinal: UInt32,
    kind: ConstraintKind
}

SpecializationFrameRole = LexicalBinder | TypeBinder | CallableBinder | MemberOwnerBinder

SpecializationFrameKey = {
    role: SpecializationFrameRole,
    owner: DeclId,
}

CanonicalBinderRef = {
    frame: SpecializationFrameKey,
    binder: CanonicalGenericBinderId
}

SpecializationFrame = {
    key: SpecializationFrameKey,
    binder: CanonicalGenericBinder,
    arguments: CanonicalSubstitution,
    evidence: NodeMap<CanonicalConstraintSlot, ConstraintEvidence>,
    optionalEvidence: NodeMap<CanonicalConstraintSlot, OptionalEvidence>
}

CanonicalSpecializationSpine = {
    frames: NodeMap<SpecializationFrameKey, SpecializationFrame>,
    outerToInner: NodeList<SpecializationFrameKey>
}

OptionalAbsenceReason =
    RefutedOptionalConstraint(predicate: Constraint,
                              failure: ConstraintFailureReason,
                              rule: RuleId)

OptionalEvidence = Present(ConstraintEvidence) | Absent(OptionalAbsenceReason)
```

The table lookup and the two relevant equality relations are explicit:

```text
resolveGenericBinder(table, id) = table.binders[id]
    when id.snapshot = table.snapshot and table.binders[id].id = id

sameGenericBinderId(a, b) iff
    a.snapshot = b.snapshot and a.index = b.index

sameGenericBinder(a, b) iff sameGenericBinderId(a.id, b.id)

alphaEquivalentBinder(tableA, a, tableB, b) iff
    canonicalizeBinder(tableA, a.id) = canonicalizeBinder(tableB, b.id)
```

`sameGenericBinderId` and `sameGenericBinder` are snapshot-working identity.
`alphaEquivalentBinder` first replaces source
parameter identities by depth/ordinal variables and is the relation used by canonical type,
signature, frame, and redeclaration shapes. It does not make structurally equal source binders share
a `GenericBinderId`.

Substitution is keyed by parameter identity, never binder position. Positional source arguments are
mapped to identities once during generic argument mapping. The empty substitution is `id`.
`GenericParameterKey` is a snapshot-local lookup key, not part of structural type equality. Before
hashing or comparing a type, bound parameters are alpha-normalized to `CanonicalBoundVariable`
(equivalently, de Bruijn depth plus ordinal). Renaming a generic parameter or rebuilding the same
binder in another snapshot therefore cannot change a function type.

A specialization frame retains ordinary arguments and constraint evidence together. Optional
constraints record `Absent` explicitly; absence is not an error witness. Pack expansion produces a
distinct `ParameterKey` for each expanded callable parameter. The empty expansion path identifies
an unexpanded parameter, while nested paths such as `[2, 0]` remain stable across scheduling order.

`Substitution`, `GenericParameterKey`, and `ConstraintKey` are working/snapshot views used by
mapping and solving. Freezing alpha-normalizes the binder, orders arguments by canonical parameter
ordinal, rewrites evidence to `CanonicalConstraintSlot`, and assigns a named frame role.
`SpecializationFrame` is the only applied-binder form stored in `CanonicalDeclRef`; an unapplied
constraint assumption uses `CanonicalBinderRef`. No snapshot-local binder/parameter ID leaks into
semantic hashes, query keys, or the wire format.

`TYP-BND-001`: A canonical parameter's list position equals its `ordinal`, and its `sort` is the
alpha-normalized source parameter sort. A canonical constraint map is built by alpha-normalizing
each predicate, sorting by `(ConstraintKind, canonical predicate
encoding)`, and assigning `constraintOrdinal` in that order. Canonically equal duplicates collapse;
if the same predicate is both optional and required, the required occurrence subsumes the optional
one. Source origins remain on `ConstraintDecl` for diagnostics and do not create slots. Each key
equals its entry's `slot`, and `slot.kind` is the discriminant of `predicate`. Defaults and
predicates may refer only to earlier parameters at the same binder depth or to enclosing binder
depths. Reordering source constraints therefore preserves binder/frame/provider identity, while
predicates not proven canonically equal remain distinct. These invariants make binder equality,
hashing, substitution, and evidence-map validation independent of snapshot-local declaration and
constraint IDs.

`TYP-BND-002`: A complete `SpecializationFrame.arguments` has exactly one entry for every
`binder.parameters` ordinal and no others; each argument alternative matches its parameter sort.
Defaults have already been expanded, and a pack occupies one argument entry, including an empty
pack. The domain of `evidence` is exactly the non-optional constraint slots. The domain of
`optionalEvidence` is exactly the optional slots, and the two domains are disjoint. Every present
proof validates the corresponding predicate after applying `arguments`; `Absent` is accepted only
for its declared optional slot with a registered `OptionalAbsenceReason`.

`TYP-BND-002a`: `RefutedOptionalConstraint.predicate` equals the slot predicate after applying the
frame's arguments. Replaying its named rule produces the stored `ConstraintFailureReason` for those
exact endpoints. Solver blocking, cancellation, resource exhaustion, recovery diagnostics, and an
ill-formed predicate are not refutations and cannot become `Absent`; they leave the specialization
query incomplete or erroneous. Absence therefore cannot silently stand for evidence that has not
been computed.

`TYP-BND-003`: `PackId` is an alpha-normalized bound-pack variable, not a snapshot-local
`GenericBinderId` or declaration. Its depth/ordinal selects exactly one type- or value-pack
parameter in the enclosing canonical binder stack, and `elements` equals the element domain of
that parameter's `TypePackParameterSort` or `ValuePackParameterSort`. Substitution shifts binder
depth capture-avoidantly. Lists of captured packs are
duplicate-free and ordered by first canonical occurrence in the pattern; maps key by the complete
record. Therefore binder renaming, allocation order, and local declaration IDs cannot affect a
`TypeId`, pack constraint, or expansion plan.

```text
argumentMatchesSort(TypeArg(t), TypeParameterSort(k)) iff kindOf(t) = k
argumentMatchesSort(ValueArg(v), ValueParameterSort(t)) iff typeOf(v) = t
argumentMatchesSort(TypePackArg(ts), TypePackParameterSort(k)) iff
    every t in ts has kindOf(t) = k
argumentMatchesSort(ValuePackArg(vs), ValuePackParameterSort(t)) iff
    every v in vs has typeOf(v) = t
argumentMatchesSort(_, _) = false otherwise
```

`TYP-BND-004`: `GenericBinderTable` is the sole authority for snapshot binder references. Its map
key equals each value's `id`, every ID names `table.snapshot`, `byOwner` is a bijection between
owners and binders, and every parent resolves in the same table to a strictly enclosing binder.
Freezing sorts binders by stable owner identity before assigning `LocalGenericBinderIndex` and
rewrites all provisional references. A semantic environment's table snapshot equals
`SemanticEnvironment.snapshot`. `DeclHeader.genericBinder = Some(id)` iff `byOwner[declaration] =
id`; `GenericEnvironmentFrame`, `GenericParameterKey`, and `ConstraintKey` references must resolve
through the same table. Table/ID equality is never substituted for alpha-equivalence.

`TYP-BND-005`: `GenericParam.sort`, `CanonicalGenericParameter.sort`, and
`CanonicalBoundVariable.sort` are the same four-way `GenericParameterSort` domain. Canonicalization
preserves the constructor and alpha-normalizes any earlier bound variables appearing in its kind or
type payload. A source or canonical default and every specialization/inference argument satisfy
`argumentMatchesSort`. `BoundTypeVariable` accepts only `TypeParameterSort`; constant-value uses
accept `ValueParameterSort`; and pack uses accept the corresponding pack sort. An empty pack is
well-sorted from its parameter/variable sort rather than from a guessed element. These invariants
have exhaustive constructor-pair tests plus alpha-renaming, serialization, and empty-pack property
tests. Unless a versioned language rule explicitly enables one, a source pack parameter's
`default` is `None`.

`TYP-BND-006`: `CanonicalBinderRef.frame` names the declaration/role that owns the referenced
canonical binder and `binder = ContentId(resolve(frame))`. It contains no arguments or constraint
evidence. Bound witness parameters, declared pack facts, lifetime assumptions, and generic equality
assumptions use this ref plus a `CanonicalConstraintSlot`, so naming an assumption never requires a
`CanonicalDeclRef` whose complete specialization frame would recursively require evidence for that
same slot.

Application and composition obey:

```text
apply(id, x) = x
apply(σ₂ ∘ σ₁, x) = apply(σ₂, apply(σ₁, x))
(σ₃ ∘ σ₂) ∘ σ₁ = σ₃ ∘ (σ₂ ∘ σ₁)
```

`TYP-SUB-001`: Applying a substitution traverses every semantic field declared substitutable by
the schema, including receiver types, parameter modes' domain/location fields, result/error types,
constraints, witness operands, lifetime/address-space requirements,
`PhysicalStorageSourceRequirement.staticInputs`, physical-source provenance facts, and capability
values that contain generic constants. Canonical hashing first alpha-normalizes every generic value
inside a registered source requirement/fact; a spelling-preserving but unsubstituted static input is
not a valid shortcut.

`TYP-SUB-002`: A substitution conflict is a solver result, not last-write-wins map insertion.

## Kinds and classifiers

The semantic checker distinguishes kinds from types:

```text
Kind = TypeKind
     | TypePackKind
     | WitnessKind(sub: TypeId, sup: TypeId)
     | FunctionKind
     | CapabilityKind
     | ErrorKind(ErrorId)

Classifier =
    KindClassifier(Kind)
  | ValueClassifier(TypeId, ValueCategory)
  | OverloadClassifier(OverloadSetId)
  | GenericValueClassifier(PartialGenericId)
  | NamespaceClassifier(DeclId)
  | ErrorClassifier(ErrorId, ErrorClassifierRecovery)

ErrorClassifierRecovery = UnknownRecovery
                        | ValueRecovery(TypeId, ValueCategory)
                        | KindRecovery(Kind)
```

A source term may denote either a type-level or value-level entity, but a checked expression has
one explicit classifier. The replacement model does not encode “a type whose value is a type” by a
special `TypeType` unless that becomes a deliberate user-visible universe rule.

`TYP-KIND-001`: Type expressions check against `TypeKind`; value expressions check against a
`ValueClassifier`. Crossing the two domains requires a named reflection or reification primitive.

`TYP-KIND-002`: `valueType` and `valueCategory` are partial projections defined only for
`ValueClassifier`. An overload, namespace, generic value, type/kind expression, or recovery term is
not forced to carry a fake `TypeId` or `ValueCategory` merely to inhabit `TypedExpr`.

## Canonical structural operands

Every operand admitted by structural type identity has a closed canonical representation:

```text
StandardAddressSpaceId = QualifiedName

AddressSpace =
    DefaultAddressSpace
  | StandardAddressSpace(StandardAddressSpaceId)
  | BoundAddressSpace(CanonicalBoundVariable)
  | ErrorAddressSpace(ErrorId)

SemanticModifierKey = QualifiedName

SemanticModifier = {
    key: SemanticModifierKey,
    arguments: CanonicalArguments
}

SemanticModifierSet =
    CanonicallyOrderedMap<SemanticModifierKey, SemanticModifier>

CanonicalInterfaceSet = CanonicallyOrderedSet<InterfaceInstanceKey>
CanonicalTypeSet = CanonicallyOrderedSet<TypeId>
```

`DefaultAddressSpace` is the language-defined ordinary address space after checking, not a missing
syntax value. Every `StandardAddressSpaceId` and `SemanticModifierKey` resolves in the versioned
standard environment. A modifier map key must equal its entry's `key`; two entries for one key are
rejected rather than resolved by insertion order.

`TYP-STR-001`: Structural type operands are serialized only in the forms above. Standard-environment
registration validates modifier argument schemas and address-space legality before a type is
interned. Canonical interface/type sets reject duplicates and sort by canonical semantic identity;
source order is retained separately for diagnostics.

## Type domain

The core type domain is a closed algebra whose extensible builtin families are nominal declarations
in the standard environment:

```text
OpenedTypeKey = {
    opening: NodeId<Typed>,
    interface: InterfaceInstanceKey
}

OpenedTypeId = ContentId<OpenedTypeKey>

Type =
    ErrorType(ErrorId)
  | NeverType
  | UnitType
  | NominalType(decl: DeclId, arguments: CanonicalSubstitution)
  | BoundTypeVariable(variable: CanonicalBoundVariable)
  | SelfType(interface: DeclId, binder: SelfBinderId)
  | AssociatedTypeProjection(
        base: TypeId,
        requirement: RequirementKey<AssociatedTypeKind>,
        witness: InterfaceSubtypeWitnessId)
  | FunctionTypeValue(FunctionType)
  | TupleType(NodeList<TypeId>)
  | PointerType(value: TypeId, addressSpace: AddressSpace, access: AccessMode)
  | ReferenceType(value: TypeId, addressSpace: AddressSpace,
                  access: AccessMode, lifetime: LifetimeId)
  | ArrayType(element: TypeId, count: ConstValue)
  | ExistentialType(interfaces: CanonicalInterfaceSet)
  | OpenedExistentialType(identity: OpenedTypeId, source: NodeId<Typed>)
  | PackType(NodeList<TypeId>)
  | EachType(pattern: TypeId, captures: NodeList<PackId>)
  | ModifiedType(base: TypeId, modifiers: SemanticModifierSet)
  | IntersectionType(CanonicalTypeSet)

TypeId = ContentId<Type>

CanonicalTypeRecord = {
    id: TypeId,
    value: Type,
    directWitnessDependencies:
        CanonicallyOrderedMap<InterfaceSubtypeWitnessId,
                              WitnessResolutionStamp>
}

WitnessResolutionStamp = WitnessResolutionSetAt<Published>
```

Vector, matrix, resource, optional, differentiable-function, and target-specific builtin types are
nominal applications unless a later rule proves that a dedicated primitive is required for their
algebra. This prevents the type checker from duplicating the standard module's declarations.

Nominal types are equal when their declaration IDs and canonically keyed arguments are equal.
`IntersectionType` is canonicalized by flattening, removing duplicates, and sorting by semantic ID;
further subtyping-based reduction requires an explicit proof and cannot occur during structural
hashing.

`ErrorType(e)` carries the root error identity. It is compatible with any expected type for recovery
but is not a proof for inheritance, refinement, conformance, or conversion and never wins overload
ranking over a non-error candidate.

An `AssociatedTypeProjection` is a first-class type, not an eagerly substituted spelling. Its
`RequirementKey` identifies the associated-type declaration under the exact inherited interface
specialization and its `InterfaceSubtypeWitnessId` identifies the exact operational proof term.
That term may be a concrete witness table, a bound generic witness, a specialization of a generic
table, a nested `LookupSubtypeWitness`, or an existential extraction. A projection through a bound
generic witness therefore remains representable and lowers to a lookup on the runtime witness
parameter; the checker does not invent a static conformance definition.

A published `CanonicalTypeRecord` contains one resolution stamp for every direct witness ID in its
payload. The stamp contains the exact frozen conformance-definition revisions reachable from that
witness term and no unrelated definition. Bound-witness-only terms may have an empty definition
map. Exact query/dependency equality includes those revisions, while structural `TypeId`, exported
signature, mangling, and wire-stable identity hash the witness's stable semantic key. Dependencies
of child `TypeId` values are followed transitively. This separates proof-term identity from the
snapshot revisions needed to resolve any concrete tables in it.

`TYP-ID-001`: `CanonicalTypeRecord.id = ContentId(record.value)` using chapter 1's complete exact
discriminator. For every direct associated projection in `value`, the dependency map contains
exactly the matching witness ID and resolution stamp. Definition-revision changes
invalidate/rebuild the record and its dependent queries but cannot change `TypeId`; changing the
witness operation or lookup key does change `TypeId`. Two unequal `Type` payloads never share an ID
even when their digest accelerators collide.

`TYP-OPEN-001`: An `OpenedExistentialType(identity, source)` satisfies
`resolve(identity).opening = source`. Its key's interface is one of the source existential's
canonical interfaces after specialization. The typed opening node is generative identity: two
different opening nodes produce distinct opened types even for equal existential values, while all
uses dominated by one opening reuse its exact `OpenedTypeId`. A scheduler task, process address, or
conformance-definition revision cannot enter that identity.

## Checked function types

`FunctionType` is the pure callable signature. It explicitly represents everything needed for type
identity, argument mapping, receiver checking, conformance matching, and ABI selection, while facts
inferred from the function body live in a separate contract:

```text
FunctionType = {
    binder: Option<CanonicalGenericBinder>,
    receiver: ReceiverSlot,
    parameters: NodeList<ParameterType>,
    result: TypeId,
    resultDifferentialParticipation: DifferentialParticipation,
    error: TypeId,
    purpose: CallablePurpose,
    traits: CallableTraits,
    callingConvention: CallingConvention
}

ReceiverSlot =
    NoReceiver
  | Receiver {
        selfType: TypeId,
        mode: PassingMode,
        differentialParticipation: DifferentialParticipation,
        isolation: ReceiverIsolation
    }

ParameterType = {
    valueType: TypeId,
    mode: PassingMode,
    differentialParticipation: DifferentialParticipation,
    labelIdentity: ParameterLabelIdentity,
    attributes: ParameterAttributeSet
}

ParameterLabelIdentity = LabelExcluded | IdentityLabel(NameKey)

CallableSignature = {
    functionType: FunctionTypeId,
    parameterSlots: NodeList<ParameterSlot>
}

FunctionTypeId = ContentId<FunctionType>
CallableSignatureId = ContentId<CallableSignature>

CallableSignatureRecord = {
    id: CallableSignatureId,
    value: CallableSignature,
    sourceGenericBindings:
        NodeMap<GenericParameterKey, CanonicalBoundVariable>
}

DynamicDispatchKey = {
    introducer: DeclId,
    signature: CallableSignatureId,
    slotRole: DynamicDispatchRole
}

DynamicDispatchRole = MethodDispatch | GetterDispatch | SetterDispatch |
                      RefAccessorDispatch(access: AccessMode) | InitializerDispatch

ParameterSlot = {
    key: ParameterKey,
    ordinal: UInt32
}

CallableTraits = {
    differentiability: DifferentiabilityPromise
}

ReceiverIsolation = NonisolatedReceiver
                  | StandardReceiverIsolation(StandardIsolationId)

ParameterAttribute = NoAliasParameter | NoCaptureParameter |
                     PreciseParameter | StandardParameterAttribute(StandardParameterAttributeId)

ParameterAttributeSet = CanonicalFiniteSet<ParameterAttribute>

CallingConvention = SlangCallingConvention | CCallingConvention |
                    CppCallingConvention | KernelCallingConvention |
                    ShaderEntryConvention(ShaderStage) |
                    StandardCallingConvention(StandardCallingConventionId)

Lifetime = StaticLifetime
         | LexicalLifetime(ScopeId)
         | GenericLifetime(CanonicalBoundVariable)
         | CallableActivationLifetime(CallableSignatureId)
         | StandardLifetime(StandardLifetimeId)

LifetimeId = ContentId<Lifetime>

OutlivesRelation = StaticOutlives
                 | LexicalScopeOutlives
                 | GenericConstraintOutlives(binder: CanonicalBinderRef,
                                             slot: CanonicalConstraintSlot)
                 | StandardOutlivesRule(StandardEnvironmentRuleId)

OutlivesProof = {
    longer: LifetimeId,
    shorter: LifetimeId,
    relation: OutlivesRelation
}

EffectiveCallableContract = {
    signature: CallableSignatureId,
    semanticEnvironment: SemanticEnvironmentId,
    declaredEffects: EffectSet,
    inferredEffects: EffectSet,
    declaredCapabilities: CapabilityFormula,
    inferredCapabilities: CapabilityFormula
}

EffectiveCallableContractId = ContentId<EffectiveCallableContract>

ParameterStorageLifetimeRequirement =
    InvocationExtent
  | DeclaredMinimumLifetime(LifetimeId)

AddressSpaceRequirement =
    AnyReferenceableAddressSpace(rule: StandardEnvironmentRuleId)
  | ExactAddressSpace(AddressSpace)
  | OneOfAddressSpaces(CanonicalFiniteSet<AddressSpace>)
  | AddressSpaceVariable(CanonicalBoundVariable)

PhysicalStorageSourceRequirement =
    AnyPhysicalStorage
  | RegisteredPhysicalStorageSource(rule: StandardEnvironmentRuleId,
                                    staticInputs: CanonicalArguments)

ParameterPhysicalLocationRequirement = {
    minimumLifetime: ParameterStorageLifetimeRequirement,
    addressSpace: AddressSpaceRequirement,
    source: PhysicalStorageSourceRequirement
}

OperandDomain =
    AbstractOperand
  | PhysicalOperand(location: ParameterPhysicalLocationRequirement)

PassingMode = {
    domain: OperandDomain,
    access: AccessMode
}

InMode = PassingMode(AbstractOperand, ReadAccess)
OutMode = PassingMode(AbstractOperand, WriteAccess)
InOutMode = PassingMode(AbstractOperand, ReadWriteAccess)
ConstRefMode(location) = PassingMode(PhysicalOperand(location), ReadAccess)
RefMode(location) = PassingMode(PhysicalOperand(location), ReadWriteAccess)

instantiatePhysicalStorageRequirement(mode, invocationLifetime) = {
    access = mode.access,
    minimumLifetime =
        invocationLifetime                         when mode.domain.location.minimumLifetime =
                                                          InvocationExtent
        l                                          when mode.domain.location.minimumLifetime =
                                                          DeclaredMinimumLifetime(l),
    addressSpace = mode.domain.location.addressSpace,
    source = mode.domain.location.source
}

directPhysicalLocationRequirement(rule, sourceRequirement) = {
    minimumLifetime = InvocationExtent,
    addressSpace = AnyReferenceableAddressSpace(rule),
    source = sourceRequirement
}
```

`DifferentialParticipation`, `DifferentiabilityPromise`, and the callable derivative contract are
defined in chapter 16. `CallablePurpose` and its explicit initialization target are defined in
chapter 15. They are referenced here because both are structural parts of the checked function
type, not modifiers recovered from the declaration or body.

The modes form two explicit axes rather than pointer-like type wrappers:

| source mode  | operand-contract domain | permitted access |
| ------------ | ----------------------- | ---------------- |
| `in`         | abstract value/storage  | read             |
| `out`        | abstract storage        | write            |
| `inout`      | abstract storage        | read and write   |
| `__constref` | physical storage        | read             |
| `__ref`      | physical storage        | read and write   |

The domain is a property of the formal parameter contract, not a claim that every argument to an
abstract-domain mode has an `AbstractPlace` classifier. A physical place may be read, written, or
used as the destination of an abstract-domain plan when its access permits the operation; that
plan does not promise to preserve the place's physical identity. Conversely, a physical-domain
mode must preserve one admitted physical endpoint and therefore has no value, temporary, or
write-back implementation.

`InMode` may copy or move an ordinary value and may read abstract storage through its getter plan.
`OutMode` and `InOutMode` may use explicitly planned abstract setter/write-back behavior.
`ConstRefMode(r)` and `RefMode(r)` preserve physical storage identity and require the complete
lifetime, address-space, and source-provenance contract `r`; neither may materialize or write back a
temporary. Header checking maps `__constref` to `ConstRefMode(r)` and `__ref` to `RefMode(r)`. A
read-only view does not assert `Mutability.Immutable`: mutable underlying storage may satisfy
`ConstRefMode` while the callee receives no `Write` operation.
Versioned storage-class modifiers such as `groupshared`, and registered provenance restrictions such
as varying-input-only intrinsics, refine `r.addressSpace` and `r.source` before function-type
construction. No call-site default weakens a missing field.

`TYP-LIF-001`: An `OutlivesProof` validates its endpoints by relation. `StaticOutlives` requires
`longer` to resolve to `StaticLifetime`; `LexicalScopeOutlives` requires the longer lexical scope to
be an ancestor of or equal to the shorter scope. `GenericConstraintOutlives(binder, slot)` resolves
that specialized binder slot to exactly `LifetimeOutlives(longer, shorter)`. A standard rule names
the same endpoint pair in the versioned standard environment. No unrelated constraint evidence can
stand in for a lifetime assumption.

`TYP-LIF-002`: `CallableActivationLifetime(s)` is the reusable formal dynamic extent of one
invocation of callable signature `s`. It may appear in a declaration's logical ABI map and its body
entry facts, but never in source-visible `Type`, `FunctionType`, generic substitution, or exported
contract identity; permitting it there would create a signature content-ID cycle. Each call owns a
separate activation-binding proof that relates the caller's concrete invocation lifetime to this
formal lifetime. Task order, call-node identity, and a caller lexical scope cannot enter the formal
lifetime ID.

`TYP-MODE-001`: A `PassingMode` is well formed exactly when it is one of the five canonical axis
combinations above: `AbstractOperand` with `ReadAccess`, `WriteAccess`, or `ReadWriteAccess`, or
`PhysicalOperand(_)` with `ReadAccess` or `ReadWriteAccess`. Atomic discipline, empty access, and
write-only physical operands require separately named future language modes and are rejected today.
The source spellings map respectively to `InMode`, `OutMode`, `InOutMode`, `ConstRefMode(r)`, and
`RefMode(r)`; clients test the structural fields and do not recover semantics from a spelling or
five-way tag.

`TYP-MODE-002`: `instantiatePhysicalStorageRequirement` accepts only a well-formed mode whose domain
is `PhysicalOperand(r)` and is total after function-type substitution. It combines `mode.access`
with `r`, replacing only `InvocationExtent` with the `AccessEnvironment.invocationLifetime` for
this call; a declared minimum lifetime, symbolic address-space requirement, and source predicate
are preserved exactly. The resulting value is the sole physical-storage requirement used for
`ConstRefMode` and `RefMode` applicability, access planning, ABI entry validation, and diagnostics.
Reconstructing a weaker requirement or dropping its source predicate is invalid.

`TYP-FUN-001`: A non-static member has exactly one receiver in its `FunctionType`. The receiver is
not prepended to the ordinary parameter list and is not recovered later from declaration nesting.

`TYP-FUN-002`: An interface requirement's receiver has `SelfType(interface, binder)` and witness
selection is represented by the `CallableValue` at a use, not by the function type. A satisfying
method is compared after substituting the concrete self type and applying any explicitly synthesized
adapter. The same function type can consequently be reached by a direct call or a witness call.

`TYP-FUN-003`: Alpha-normalized binders, generic constraints, receiver type/mode/differential
participation, parameter value types/modes/differential participation/semantic attributes,
result type/differential participation, error type, callable purpose and initialization
target/result convention,
callable differentiability promise, and calling convention participate in function-type equality.
`ParameterKey` exists only on
`CallableSignature`, while source spelling/origin remains on parameter AST metadata; neither is an
operand of the interned `FunctionType`. Slots associate arguments and evidence with parameters
after pack expansion. A checked language rule constructs
`IdentityLabel(NameKey)` when labels participate in callable identity and `LabelExcluded`
otherwise; source spelling/origin remains on parameter AST nodes. That compatibility decision is
tracked in chapter 12 and never leaves an undecided source `Name` inside `FunctionType`.
Mode equality is fieldwise over `PassingMode.domain` and `PassingMode.access`; a
`PhysicalOperand(location)` includes all lifetime, address-space, and source fields of `location`.
No source spelling or compatibility alias replaces those structural equality operands.

`TYP-FUN-004`: Static methods and free functions use `NoReceiver`. Initializers use
`InitializerCallable(target, resultConvention)` and a receiver only for a separately defined
delegating form; the
fresh/partial storage target is not ordinary argument zero. A hidden `this` or construction result
inferred from the parent is forbidden.

Receiver direction has one authority in `PassingMode`:

| written receiver behavior                     | canonical receiver mode                                                                          |
| --------------------------------------------- | ------------------------------------------------------------------------------------------------ |
| ordinary nonmutating                          | `InMode`                                                                                         |
| `mutating`                                    | `InOutMode`                                                                                      |
| `[constref]` receiver mode                    | `ConstRefMode(directPhysicalLocationRequirement(activeDirectReferenceRule, AnyPhysicalStorage))` |
| `ref`                                         | `RefMode(directPhysicalLocationRequirement(activeDirectReferenceRule, AnyPhysicalStorage))`      |
| explicit consuming/value receiver, if enabled | `InMode`                                                                                         |

The named rule and storage requirement are the canonical values produced by header checking as specified
above, including invocation extent and its symbolic address-space requirement. `OutMode` is never a receiver mode.
Mutating/ref-style booleans are not also stored in the signature.
Illegal modifier combinations fail receiver-mode construction, so a canonical receiver cannot be
both `ConstRefMode` and mutating. The `[constref]` receiver modifier is not the property/subscript
`constref` accessor spelling; chapter 2 normalizes them through distinct syntax roles. Differential
participation, callable promise, and isolation are
orthogonal fields.

`TYP-FUN-005`: Dispatch mode, declaration visibility, declared or inferred effects, and declared or
inferred capabilities do not participate in `FunctionType` equality. They are use-site or
`EffectiveCallableContract` facts. This separation prevents signature checking from depending on
the body whose references are being type-checked.

`TYP-FUN-006`: `CallableSignature.parameterSlots` is a bijection onto the ordinal range
`0 .. functionType.parameters.count-1`: keys are unique, ordinals are unique/in range, and every
ordinal occurs exactly once. An unexpanded source parameter has an empty expansion path; each
materialized pack element has one unique path and preserves the source parameter key. Validation,
serialization, argument mapping, adapters, and `FunctionAbiMap` all check this same invariant.
`CallableSignatureRecord.id = ContentId(record.value)`. Its `sourceGenericBindings` is a noncanonical
snapshot sidecar: keys belong to the source binder and values form a bijection onto the depth-zero
`CanonicalBoundVariable` values in `functionType.binder` by parameter ordinal. The sidecar is
serialized for source tooling but is excluded from signature/type/query identity exactly as
required by `TYP-BND-001`.

The following relations must name their fields instead of sharing an accidental byte comparison:

| relation                           | signature fields considered                                                                                                                 |
| ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------- |
| structural equality/canonical hash | all `TYP-FUN-003` fields after alpha-normalization                                                                                          |
| function conversion compatibility  | receiver and parameter variance, modes, result/error, and traits under an explicit rule                                                     |
| overload/redeclaration identity    | only chapter 5's `RedeclarationKey`/`CallableShape` input discriminators; excluded signature-field differences are diagnosed after grouping |
| interface matching                 | equality/subtyping plus an explicit adapter plan and contract compatibility                                                                 |
| symbol mangling                    | canonical binder shape, receiver, parameters, result/error, traits, and calling convention                                                  |
| ABI lowering                       | receiver, modes, value layouts, error convention, traits, and calling convention                                                            |

Any intentional difference between these rows is a named rule and a compatibility-ledger entry.

`TYP-FUN-007`: Every `Standard*Id` above is a stable declaration in the versioned standard
environment with canonical serialization and validator hooks. Extensions cannot inject process-
local enum values. Exported signatures may use only static/generic/standard lifetimes, never a
snapshot-local `LexicalLifetime`; receiver isolation, parameter attributes, differentiability, and
calling convention participate in function-type equality exactly as stated by `TYP-FUN-003`.

`TYP-FUN-008`: `FunctionTypeId` is the typed content ID of the `FunctionType` payload.
`TypeId(FunctionTypeValue(f))` is its unique embedding in the general type algebra; interning and
resolution validate both content IDs from the same canonical `f`. `CallableSignatureId` and
`EffectiveCallableContractId` likewise use the exact payload schemas above, never allocation
ordinals or digest-only equality.

`TYP-FUN-009`: Resolving a callable contract's `semanticEnvironment` selects one effect-universe
revision and one capability-universe revision from its standard environment. Both effect sets in
an `EffectiveCallableContract` use that effect revision, and every closed leaf of both capability
requirements uses that capability revision. `PreInferenceCallableContract` obeys the same law for
`selectionEffects`, `inferredCapabilities`, and every source and combined requirement in any
`concreteAvailability`. Construction rejects mixed revisions; the
`effectiveEffects`/`effectiveCapabilities` projections are therefore total and never compare atom
IDs across universes.

`TYP-FUN-010`: Every callable header has exactly one `CallableResultAuthorityId`, and every
non-callable header has none. Resolving the authority yields an anchor whose declaration and
signature are byte-identical to that header after specialization. A builtin callable instead uses
the exact `RegisteredCallableRule` anchor selected from the standard environment. The authority is
published with the header, before body checking, and is not inferred from a returned value or
supplied by a call site. `OrdinaryCallableResult` is a positive authority alternative rather than
the absence of metadata, so a caller cannot reinterpret a same-signature callable by choosing a
different result contract.

`TYP-FUN-011`: Substitution of a callable declaration substitutes its signature and result contract
in one operation and constructs the correspondingly specialized `CallableResultAuthorityId` while
preserving the anchor declaration. Fixed, accessor, and registered contracts validate their result
type against the anchored signature. The accessor alternative additionally has
`contract = AbstractRefAccessor.resultContract` for the accessor surface that owns the anchor;
fixed and registered alternatives cannot stand in for it merely because their result type or
runtime representation agrees. Witness and dynamic dispatch resolve the authority of the exact
requirement/slot introducer, while a direct or closure dispatch resolves the selected declaration;
none accepts an authority ID from the caller.

The current compiler's `FuncType` in `source/slang/slang-ast-type.h` stores parameter modes as
pointer-like wrapper types, while `getFuncType` in `source/slang/slang-syntax.cpp` omits implicit
`this`; `getTypeForThisExpr` and `calcThisType` recover it through declaration context. The proposed
domain deliberately makes both pieces structural.

## Effect algebra and contracts

Effects describe callable behavior that must be admitted by an enclosing context. They are not
function-type operands; the structural `FunctionType.error` still records the precise thrown value
type and is checked independently.

```text
EffectAtomDefinition = {
    stableName: QualifiedName
}

EffectUniverseDefinition = {
    standardEffects:
        CanonicallyOrderedMap<StandardEffectId, EffectAtomDefinition>
}

EffectUniverseRevision = ContentId<EffectUniverseDefinition>
EffectAtom = MayThrow | StandardEffect(StandardEffectId)
EffectSet = {
    universe: EffectUniverseRevision,
    atoms: CanonicalFiniteSet<EffectAtom>
}

EffectRequirement = ClosedEffects(EffectSet)
                  | GenericEffects(EffectScheme)
                  | ErrorEffectRequirement(ErrorId)

EffectScheme = {
    binder: CanonicalGenericBinder,
    root: EffectContractExprId
}

EffectContractExpr =
    Effects(EffectSet)
  | RequireAllEffects(NodeList<EffectContractExprId>)
  | IfConstEffect(predicate: SymbolicBoolValue,
                  thenExpr: EffectContractExprId,
                  elseExpr: EffectContractExprId)
  | ErrorEffect(ErrorId)

EffectContractExprId = ContentId<EffectContractExpr>

EffectAllowance = InferEffects | RestrictedEffects(EffectSet)

EffectAllowanceValidation =
    InferredAllowance
  | RestrictedSubset(CanonicalSetInclusionProof<EffectAtom>)

DeclaredEffectContract = {
    requirement: EffectRequirement,
    constrained: Bool,
    origins: NodeList<Origin>
}

DeclaredEffectContractId = ContentId<DeclaredEffectContract>

InferredEffectContract = {
    requirement: EffectRequirement,
    uses: EffectUseGraphId
}

EffectCompatibilityObligation = {
    caller: DeclId,
    callee: CanonicalDeclRef,
    allowed: EffectAllowance,
    selectionEffects: EffectSet,
    origin: Origin
}

EffectUseKey = {
    owner: CanonicalDeclRef,
    origin: Origin,
    ordinal: UInt32
}

EffectUseId = ContentId<EffectUseKey>

EffectUse<S: WitnessUseStage> = {
    key: EffectUseKey,
    requirement: DirectEffect(EffectSet)
               | LocalCallable(ResolvedDeclRefAt<S>)
               | ImportedCallable(EffectSet)
               | WitnessEntry(WitnessCallRef<S>, WitnessRuntimeEntryKey)
}

EffectUseGraph<S: WitnessUseStage> = {
    root: CanonicalDeclRef,
    rootWitnessResolutions: WitnessResolutionSetAt<S>,
    uses: CanonicallyOrderedMap<EffectUseId, EffectUse<S>>
}

EffectUseGraphId = ContentId<EffectUseGraph<Published>>
```

Unqualified `EffectUse` means `EffectUse<Published>`. Construction-stage synthesis graphs may use
`EffectUse<Construction>` whose witness resolution set contains a scope-authorized
`OperationalConformanceRef`; chapter 8's atomic freeze must rewrite only that resolution to its
frozen definition reference before the graph can enter any published
typed/elaborated snapshot, exported metadata, or IR. Construction-stage elaborated nodes
inside the synthesis transaction remain legal and cannot escape that transaction.
`rootWitnessResolutions` is the minimal stage-correct set required by `root.specializations`.
Every graph map key equals `ContentId(use.key)`, every `use.key.owner` equals `root`, and ordinals
are assigned by stable origin plus semantic child-role order rather than traversal/task order.
The use origin is projected only as `use.key.origin`; there is no second payload copy.

`TYP-EFF-007`: An `EffectUseGraph` stores only direct uses in `root`'s body. Every map ID resolves
to its payload, every payload owner equals `root`, and a `LocalCallable`/`WitnessEntry` requirement
itself names the dependency to request. Inference follows those typed requirements to the callee or
witness contract through scheduler query edges; it never copies or re-keys a callee's uses into the
caller graph. Imported and direct requirements are leaves. Diagnostic call paths are reconstructed
from the scheduler dependency trace plus direct use IDs, so arbitrary unresolved cross-graph edges
are not representable in the semantic value. A local callable edge uses `.target` as its stable
dependency subject and retains the stage-correct minimal witness-resolution sidecar for evidence in
that target's specialization; those exact definition refs become query dependencies.

Within one equal `EffectUniverseRevision`, the information order is atom subset, bottom is the
empty atom set, and join is canonical union. The domain is finite. `MayThrow` is present for an uncaught throwing
path; its value is converted to the enclosing signature's `error` type by an explicit plan.
Target/capability availability is not an effect atom.

```text
selectionEffects(d, specialization) =
    closeEffects(substitute(d.declared.requirement, specialization))
                                               when d.declared.constrained
selectionEffects(d, specialization) = emptyEffects(d.effectUniverse)
                                               otherwise

effectiveEffects(c: EffectiveCallableContract) =
    union(c.declaredEffects, c.inferredEffects)
```

For a validated constrained declaration, inference is a subset of the declaration, so this accessor
reduces to the declared set. For an unconstrained declaration, the stored declared set is empty, so
it reduces to the inferred set. The effective contract therefore needs no duplicate `constrained`
bit; that bit and origins remain on the declared-contract fact used during validation.

`TYP-EFF-001`: Overload/call selection reads `selectionEffects`, never an inferred local callee
contract. It records a typed direct effect use; restricted callers are validated after inference.
Imported callables may expose their already published effective set. A complete call specialization
must close the declared effect scheme; a residual scheme produces a `PartialGeneric`, not an
applicable ordinary call.

`TYP-EFF-002`: `InferEffects` collects direct effects and follows local call edges with current SCC
approximations, monotonically unioning until stable. It does not request an effective-contract query.
After stabilization, `ValidateDeclaredEffects` checks the declared contract, `FunctionType.error`,
interface obligations, and recorded call obligations.

`TYP-EFF-003`: Effect-set equality, subset, union, effect-scheme substitution/closure, direct-use
collection, recursive inference, declaration validation, and adapter compatibility are independent
pure/query surfaces with rule-linked tests. `EffectAtom` itself has no substitutable payload; only
the scheme's symbolic branch conditions depend on generic arguments. Task order cannot affect the
canonical set.

`TYP-EFF-004`: `FunctionType.error` is the typed error channel. Every `throw`, propagated error,
and throwing-call edge contains a checked conversion of its payload to that type. If
`FunctionType.error = NeverType`, `MayThrow` is forbidden in both declared and inferred effects; if
an effective contract contains `MayThrow`, its function error type is not `NeverType`. A non-`Never`
error type permits an error channel but does not by itself assert that the body uses it: an
unconstrained body with no reachable throwing path may infer a set without `MayThrow`, while an
explicit declared contract may conservatively promise it. This separates signature capacity from
path-sensitive effect inference.

`TYP-EFF-005`: Generic effect inference produces a canonical `EffectRequirement` decision DAG
under the declaration binder. Runtime branches combine effects with `RequireAllEffects`; a
compile-time `IfConstEffect` retains only the selected branch after complete specialization.
Exported generics publish the scheme, and imported complete specializations close it instead of
re-running an unavailable body or collapsing all compile-time alternatives together.

`TYP-EFF-006`: Before interning an `EffectContractExpr`, canonicalization recursively flattens
nested `RequireAllEffects`, merges all `Effects` leaves by canonical union in one universe, removes
the empty-set identity when another child exists, sorts remaining child IDs by exact discriminator,
and removes duplicates. Zero children canonicalize to `Effects(empty)` and one child to that child.
`IfConstEffect` with a known predicate canonicalizes to its selected branch; equal branches collapse;
otherwise its normalized predicate and two canonical child IDs remain ordered by their named roles.
An error node retains its `ErrorId` and is never erased as an identity. These reductions are
idempotent and define the only payload admitted to `EffectContractExprId`, so commutative grouping,
container order, and redundant conditions cannot produce distinct scheme identities.

## Value categories, abstract storage, and physical storage

```text
AccessOperation = Read | Write
AccessDiscipline = Ordinary | Atomic

AccessMode = {
    operations: CanonicalFiniteSet<AccessOperation>,
    discipline: AccessDiscipline
}

Mutability = Immutable | Mutable | UnknownMutability

ReadAccess = AccessMode({Read}, Ordinary)
WriteAccess = AccessMode({Write}, Ordinary)
ReadWriteAccess = AccessMode({Read, Write}, Ordinary)

SourceArgumentId = NodeId<Typed>
SourceArgumentForm = OrdinaryArgument | PackExpansionArgument

SourceArgument = {
    id: SourceArgumentId,
    label: Option<Name>,
    value: TypedExpr,
    form: SourceArgumentForm,
    origin: Origin
}

SourceCallRole =
    ReceiverSourceRole
  | ArgumentSourceRole(argument: SourceArgumentId, expansion: ExpansionPath)

CapturedStorageSourceRole =
    StorageReceiverSource
  | StorageArgumentSource(argument: SourceArgumentId)

CapturedStorageSource =
    CapturedStorageReceiver(value: TypedExpr)
  | CapturedStorageArgument(argument: SourceArgument)

CapturedStorageProjection = {
    source: CapturedStorageSourceRole,
    expansion: ExpansionPath
}

CapturedStorageSources = {
    captures: NodeMap<CapturedStorageSourceRole, CapturedStorageSource>,
    evaluationOrder: NodeList<CapturedStorageSourceRole>
}

AccessorProvenanceSourceRole =
    AccessorReceiverProvenance
  | AccessorParameterProvenance(parameter: ParameterKey)

AccessorProvenanceSourceMap = {
    bindings:
        CanonicallyOrderedMap<AccessorProvenanceSourceRole,
                              CapturedStorageProjection>
}

AccessorProvenanceSourceMapId = ContentId<AccessorProvenanceSourceMap>

AliasRegionIdentity =
    StableAliasRegionIdentity(StableSemanticId)
  | AccessorInvocationAliasRegion(AccessorInvocationIdentity)
  | TemporaryStorageAliasRegion(TemporaryStorageIdentity)

AliasProvenance =
    ExactAliasRoot(AliasRegionIdentity)
  | JoinedAliasRoots(CanonicallyOrderedSet<AliasRegionIdentity>)
  | UnknownAliasRoot

FiniteAliasRegions = CanonicallyOrderedSet<AliasRegionIdentity>

AliasRegionSet =
    KnownAliasRegions(FiniteAliasRegions)
  | AnyAliasRegion

aliasRegions(ExactAliasRoot(r)) = KnownAliasRegions({r})
aliasRegions(JoinedAliasRoots(rs)) = KnownAliasRegions(rs)
aliasRegions(UnknownAliasRoot) = AnyAliasRegion

AliasDisjointnessProof = {
    left: AliasProvenance,
    right: AliasProvenance,
    leftRegions: FiniteAliasRegions,
    rightRegions: FiniteAliasRegions
}

AliasOverlapReason =
    CommonAliasRegion(region: AliasRegionIdentity)
  | OneUnknownAlias
  | BothUnknownAliases

AliasOverlapResult =
    ProvenDisjoint(AliasDisjointnessProof)
  | MayOverlap(AliasOverlapReason)

CompareAliasOverlap(left: AliasProvenance, right: AliasProvenance)
    -> AliasOverlapResult

SemanticOperationSiteRole = {
    rule: RuleId,
    ordinal: UInt32
}

SemanticOperationSourceAnchor =
    ParsedOperationSource(source: SourceRangeSet, occurrence: UInt32)
  | ImportedOperationSource(module: ModuleInterfaceContentId, exported: ExportedId)
  | RecoveryOperationSource(source: SourceRangeSet, occurrence: UInt32)

StageFreeSynthesizedOperationAnchorKey = {
    root: SemanticOperationSourceAnchor,
    synthesisPath: NonEmpty<SemanticOperationSiteRole>
}

StageFreeSynthesizedOperationAnchorId =
    ContentId<StageFreeSynthesizedOperationAnchorKey>

SemanticOperationSiteAnchor =
    ParsedOperationSite(source: SourceRangeSet, occurrence: UInt32)
  | SynthesizedOperationSite(output: StageFreeSynthesizedOperationAnchorId)
  | ImportedOperationSite(module: ModuleInterfaceContentId, exported: ExportedId)
  | RecoveryOperationSite(source: SourceRangeSet, occurrence: UInt32)

SemanticOperationSiteKey = {
    anchor: SemanticOperationSiteAnchor,
    rolePath: NonEmpty<SemanticOperationSiteRole>
}

BuiltinPhysicalProjectionIdentity =
    BuiltinPhysicalProjectionApplicationId(ContentId<SemanticOperationSiteKey>)
DereferenceApplicationIdentity =
    DereferenceApplicationId(ContentId<SemanticOperationSiteKey>)
RegisteredPhysicalProjectionIdentity =
    RegisteredPhysicalProjectionApplicationId(ContentId<SemanticOperationSiteKey>)
AccessorInvocationIdentity =
    AccessorInvocationApplicationId(ContentId<SemanticOperationSiteKey>)
TemporaryStorageIdentity =
    TemporaryStorageApplicationId(ContentId<SemanticOperationSiteKey>)

builtinPhysicalProjectionIdentity(site: SemanticOperationSiteKey) =
    BuiltinPhysicalProjectionApplicationId(ContentId(site))

dereferenceApplicationIdentity(site: SemanticOperationSiteKey) =
    DereferenceApplicationId(ContentId(site))

registeredPhysicalProjectionIdentity(site: SemanticOperationSiteKey) =
    RegisteredPhysicalProjectionApplicationId(ContentId(site))

accessorInvocationIdentity(site: SemanticOperationSiteKey) =
    AccessorInvocationApplicationId(ContentId(site))

temporaryStorageIdentity(site: SemanticOperationSiteKey) =
    TemporaryStorageApplicationId(ContentId(site))

accessorInvocationAliasRoot(AccessorInvocationApplicationId(content)) =
    AccessorInvocationAliasRegion(
        AccessorInvocationApplicationId(content))

temporaryStorageAliasRoot(TemporaryStorageApplicationId(content)) =
    TemporaryStorageAliasRegion(TemporaryStorageApplicationId(content))

childSemanticOperationSite(parent: SemanticOperationSiteKey,
                           rule: RuleId,
                           ordinal: UInt32) =
    SemanticOperationSiteKey(parent.anchor,
                             append(parent.rolePath, {rule, ordinal}))

SemanticOperationSiteDerivation =
    RootSemanticOperationSite(anchor: SemanticOperationSiteAnchor,
                              role: SemanticOperationSiteRole)
  | ChildSemanticOperationSite(parent: SemanticOperationSiteKey,
                               role: SemanticOperationSiteRole)

SemanticOperationSiteAssignmentContext = {
    sources: CanonicallyOrderedSet<SourceSnapshotId>,
    expandedViews: CanonicallyOrderedSet<ExpandedTokenViewId>,
    provenance: SemanticSnapshotId
}

SemanticOperationSiteAssignmentContextId =
    ContentId<SemanticOperationSiteAssignmentContext>

SemanticOperationSiteAssignment = {
    context: SemanticOperationSiteAssignmentContextId,
    origin: Origin,
    site: SemanticOperationSiteKey,
    derivation: SemanticOperationSiteDerivation
}

SemanticOperationSiteFailure =
    OperationSiteContextUnavailable(context: SemanticOperationSiteAssignmentContextId)
  | OperationOriginHasNoSourceAnchor(origin: Origin)
  | OperationSiteParentInvalid(parent: SemanticOperationSiteKey)
  | OperationSiteRoleInvalid(role: SemanticOperationSiteRole)
  | OperationSiteOriginMismatch(expected: Origin, actual: Origin)
  | OperationSiteKeyMismatch(expected: SemanticOperationSiteKey,
                             actual: SemanticOperationSiteKey)

AssignSemanticOperationSite(context: SemanticOperationSiteAssignmentContextId,
                            origin: Origin,
                            parent: Option<SemanticOperationSiteKey>,
                            role: SemanticOperationSiteRole)
    -> Result<SemanticOperationSiteAssignment, SemanticOperationSiteFailure>

ValidateSemanticOperationSite(owner: NodeId<Typed>,
                              assignment: SemanticOperationSiteAssignment)
    -> Result<Unit, SemanticOperationSiteFailure>

PhysicalProjectionSiteAnchor = SemanticOperationSiteAnchor
PhysicalProjectionSiteRole = SemanticOperationSiteRole
PhysicalProjectionSiteKey = SemanticOperationSiteKey
PhysicalProjectionSiteDerivation = SemanticOperationSiteDerivation
PhysicalProjectionSiteAssignmentContext = SemanticOperationSiteAssignmentContext
PhysicalProjectionSiteAssignmentContextId = SemanticOperationSiteAssignmentContextId
PhysicalProjectionSiteAssignment = SemanticOperationSiteAssignment
PhysicalProjectionSiteFailure = SemanticOperationSiteFailure

childPhysicalProjectionSite(parent: PhysicalProjectionSiteKey,
                            rule: RuleId,
                            ordinal: UInt32) =
    childSemanticOperationSite(parent, rule, ordinal)

AssignPhysicalProjectionSite(context: PhysicalProjectionSiteAssignmentContextId,
                             origin: Origin,
                             parent: Option<PhysicalProjectionSiteKey>,
                             role: PhysicalProjectionSiteRole) =
    AssignSemanticOperationSite(context, origin, parent, role)

ValidatePhysicalProjectionSite(owner: NodeId<Typed>,
                               assignment: PhysicalProjectionSiteAssignment) =
    ValidateSemanticOperationSite(owner, assignment)

PhysicalProjectionApplicationOwner =
    TypedProjectionOwner(node: NodeId<Typed>)
  | StorageAccessProjectionOwner(plan: ContentId<InternalRefStoragePlan>,
                                 ordinal: UInt32)
  | CallSlotProjectionOwner(call: NodeId<Typed>,
                            slot: BoundCallSlot,
                            operationPath: NonEmpty<SemanticOperationSiteRole>)

PhysicalProjectionApplicationIndex = {
    builtin:
        NodeMap<BuiltinPhysicalProjectionIdentity, PhysicalProjectionApplicationOwner>,
    registered:
        NodeMap<RegisteredPhysicalProjectionIdentity, PhysicalProjectionApplicationOwner>,
    dereference:
        NodeMap<DereferenceApplicationIdentity, PhysicalProjectionApplicationOwner>
}

PhysicalProjectionApplicationIndexFailure =
    DuplicateBuiltinProjectionIdentity(identity: BuiltinPhysicalProjectionIdentity,
                                       owners: NonEmpty<PhysicalProjectionApplicationOwner>)
  | DuplicateRegisteredProjectionIdentity(identity: RegisteredPhysicalProjectionIdentity,
                                          owners: NonEmpty<PhysicalProjectionApplicationOwner>)
  | DuplicateDereferenceIdentity(identity: DereferenceApplicationIdentity,
                                 owners: NonEmpty<PhysicalProjectionApplicationOwner>)
  | ProjectionOwnerDoesNotResolve(owner: PhysicalProjectionApplicationOwner)
  | ProjectionOwnerKindMismatch(owner: PhysicalProjectionApplicationOwner)
  | ProjectionOwnerIdentityMismatch(owner: PhysicalProjectionApplicationOwner)
  | CallSlotProjectionPathMismatch(owner: PhysicalProjectionApplicationOwner)

PhysicalProjectionSemanticResultSnapshot = {
    storagePlans:
        CanonicallyOrderedMap<ContentId<InternalRefStoragePlan>, InternalRefStoragePlan>,
    queryDependencies:
        CanonicallyOrderedMap<QueryKey, ContentId<InternalRefStoragePlan>>
}

PhysicalProjectionSemanticResultSnapshotId =
    ContentId<PhysicalProjectionSemanticResultSnapshot>

PublishPhysicalProjectionSemanticResults(
    completedPlans: CanonicallyOrderedMap<QueryKey, InternalRefStoragePlan>)
    -> PhysicalProjectionSemanticResultSnapshotId

BuildPhysicalProjectionApplicationIndex(
    snapshot: AstSnapshotId<Typed>,
    semanticResults: PhysicalProjectionSemanticResultSnapshotId)
    -> Result<PhysicalProjectionApplicationIndex,
              PhysicalProjectionApplicationIndexFailure>

ReferenceHandleKind = LanguageReferenceHandle | PointerHandle

ReferenceHandleShape = {
    kind: ReferenceHandleKind,
    referent: TypeId,
    addressSpace: AddressSpace,
    access: AccessMode,
    mutability: Mutability,
    lifetime: LifetimeId,
    alias: AliasProvenance,
    sourceProvenance: PhysicalStorageSourceProvenance
}

ReferenceHandleValueShape = {
    type: TypeId,
    handle: ReferenceHandleShape
}

effectiveHandleAccess(h) =
    h.access                              when h.mutability = Mutable
    remove(Write, h.access)               when h.mutability = Immutable
    remove(Write, h.access)               when h.mutability = UnknownMutability

PhysicalPlacePath =
    StoredRoot(declaration: CanonicalDeclRef)
  | ConstRefFormalRoot(signature: CallableSignatureId,
                       role: ConstRefFormalRole)
  | RefFormalRoot(signature: CallableSignatureId,
                  role: RefFormalRole)
  | StoredField(base: PhysicalPlacePath, field: DeclId)
  | BuiltinElement(base: PhysicalPlacePath,
                   application: BuiltinPhysicalProjectionIdentity)
  | DereferencedReference(application: DereferenceApplicationIdentity)
  | VectorElement(base: PhysicalPlacePath, element: UInt8)
  | RegisteredPhysicalProjection(application: RegisteredPhysicalProjectionIdentity)

ConstRefFormalRole =
    ConstRefReceiver
  | ConstRefParameter(parameter: ParameterKey)

RefFormalRole =
    RefReceiver
  | RefParameter(parameter: ParameterKey)

PhysicalFormalEntryRole =
    ConstRefFormalEntry(role: ConstRefFormalRole)
  | RefFormalEntry(role: RefFormalRole)

PhysicalFormalEntryProof = {
    signature: CallableSignatureId,
    role: PhysicalFormalEntryRole,
    mode: PassingMode,
    semanticEnvironment: SemanticEnvironmentId
}

PhysicalFormalEntryProofId = ContentId<PhysicalFormalEntryProof>

PhysicalStorageAddressSpace =
    ConcretePhysicalAddressSpace(AddressSpace)
  | FormalPhysicalAddressSpace(entry: PhysicalFormalEntryProofId)

ConcreteAddressSpaceProjection =
    AlreadyConcreteAddressSpace
  | ExactFormalAddressSpace(entry: PhysicalFormalEntryProofId)
  | SpecializedFormalAddressSpace(entry: PhysicalFormalEntryProofId,
                                  evidence: ConstraintEvidence)

ConcreteAddressSpaceProjectionProof = {
    source: PhysicalStorageAddressSpace,
    result: AddressSpace,
    derivation: ConcreteAddressSpaceProjection
}

PhysicalStorageSourceFact =
    RegisteredPhysicalStorageSourceFact(
        rule: StandardEnvironmentRuleId,
        staticInputs: CanonicalArguments,
        environment: StandardEnvironmentId)

PhysicalStorageSourceProvenance =
    CanonicallyOrderedSet<PhysicalStorageSourceFact>

formalAddressSpaceRequirement(entry) =
    resolve(entry).mode.domain.location.addressSpace

formalSourceProvenance(entry) =
    {} when resolve(entry).mode.domain.location.source = AnyPhysicalStorage
    { RegisteredPhysicalStorageSourceFact(rule, arguments,
          standardEnvironment(resolve(entry).semanticEnvironment)) }
        when resolve(entry).mode.domain.location.source =
            RegisteredPhysicalStorageSource(rule, arguments)

PhysicalStorageRef = {
    valueType: TypeId,
    path: PhysicalPlacePath,
    access: AccessMode,
    mutability: Mutability,
    addressSpace: PhysicalStorageAddressSpace,
    lifetime: LifetimeId,
    alias: AliasProvenance,
    sourceProvenance: PhysicalStorageSourceProvenance
}

AbstractAccessor = {
    selector: AbstractAccessorSelector,
    access: AccessMode
}

AbstractAccessorSelector =
    DirectAccessor(declaration: CanonicalDeclRef)
  | WitnessAccessor(witness: InterfaceSubtypeWitnessId,
                    entry: WitnessRuntimeEntryKey)
  | DynamicAccessor(owner: TypeId, slot: DynamicDispatchKey)
  | BuiltinAccessor(registration: RegisteredCallableRule)

RegisteredAccessorProvenanceRule = {
    rule: StandardEnvironmentRuleId,
    staticInputs: CanonicalArguments,
    environment: StandardEnvironmentId
}

AccessorReferenceAddressSpaceRule =
    FixedAccessorAddressSpace(AddressSpace)
  | CapturedAccessorAddressSpace(AccessorProvenanceSourceRole)
  | RegisteredAccessorAddressSpace(RegisteredAccessorProvenanceRule)

AccessorReferenceMutabilityRule =
    FixedAccessorMutability(Mutability)
  | CapturedAccessorMutability(AccessorProvenanceSourceRole)
  | AccessDerivedAccessorMutability

accessDerivedAccessorMutability(ReadAccess) = UnknownMutability
accessDerivedAccessorMutability(ReadWriteAccess) = Mutable
accessDerivedAccessorMutability(other) = InvalidAccessorAccessMode(other)

AccessorReferenceLifetimeRule =
    StaticAccessorLifetime
  | CapturedAccessorLifetime(AccessorProvenanceSourceRole)
  | MinimumCapturedAccessorLifetime(
        sources: NonEmpty<AccessorProvenanceSourceRole>)
  | RegisteredAccessorLifetime(RegisteredAccessorProvenanceRule)

AccessorReferenceAliasRule =
    PreserveCapturedAlias(AccessorProvenanceSourceRole)
  | FreshAccessorAlias(rule: RegisteredGenerativeAccessorAliasRule)
  | ConservativeUnknownAlias
  | RegisteredAccessorAlias(RegisteredAccessorProvenanceRule)

RegisteredGenerativeAccessorAliasRule = {
    registration: RegisteredAccessorProvenanceRule,
    allocationRule: StandardEnvironmentRuleId,
    lifetimeRule: StandardEnvironmentRuleId
}

AccessorReferenceSourceRule =
    FixedAccessorSource(PhysicalStorageSourceProvenance)
  | CapturedAccessorSource(AccessorProvenanceSourceRole)
  | RegisteredAccessorSource(RegisteredAccessorProvenanceRule)

AccessorReferenceResultContract = {
    selector: AbstractAccessorSelector,
    signature: CallableSignatureId,
    resultType: TypeId,
    kind: ReferenceHandleKind,
    referent: TypeId,
    access: AccessMode,
    addressSpace: AccessorReferenceAddressSpaceRule,
    mutability: AccessorReferenceMutabilityRule,
    lifetime: AccessorReferenceLifetimeRule,
    alias: AccessorReferenceAliasRule,
    source: AccessorReferenceSourceRule
}

AccessorReferenceResultContractId = ContentId<AccessorReferenceResultContract>

FixedReferenceHandleResultContract = {
    resultType: TypeId,
    result: ReferenceHandleValueShape
}

FixedReferenceHandleResultContractId =
    ContentId<FixedReferenceHandleResultContract>

RegisteredReferenceHandleResultContract = {
    registration: RegisteredDataOperationRegistration,
    resultType: TypeId
}

RegisteredReferenceHandleResultContractId =
    ContentId<RegisteredReferenceHandleResultContract>

CallableResultAuthorityAnchor =
    DeclaredCallableResultAnchor(declaration: DeclId,
                                 signature: CallableSignatureId)
  | RegisteredCallableResultAnchor(registration: RegisteredCallableRule,
                                   signature: CallableSignatureId)

CallableResultAuthorityKind =
    OrdinaryCallableResult
  | FixedReferenceHandleCallableResult(
        contract: FixedReferenceHandleResultContractId)
  | AccessorReferenceHandleCallableResult(
        contract: AccessorReferenceResultContractId)
  | RegisteredReferenceHandleCallableResult(
        contract: RegisteredReferenceHandleResultContractId)

CallableResultAuthority = {
    anchor: CallableResultAuthorityAnchor,
    kind: CallableResultAuthorityKind
}

CallableResultAuthorityId = ContentId<CallableResultAuthority>

AbstractRefAccessor = {
    access: AccessMode,
    selector: AbstractAccessorSelector,
    resultContract: AccessorReferenceResultContractId
}

accessorResultAuthority(a: AbstractRefAccessor) =
    resolveCallableResultAuthority(a.selector,
                                   resolve(a.resultContract).signature)

AbstractAccessorContract = {
    getter: Option<AbstractAccessor>,
    setter: Option<AbstractAccessor>,
    referenceAccessors: CanonicallyOrderedMap<AccessMode, AbstractRefAccessor>
}

AbstractStorageProjection =
    PropertyProjection(property: CanonicalDeclRef)
  | DeclaredSubscriptProjection(subscript: CanonicalDeclRef)
  | AbstractSwizzleProjection(elements: NonEmpty<UInt8>)
  | RegisteredAbstractProjection(rule: StandardEnvironmentRuleId,
                                 inputs: CanonicalArguments)

AbstractStorageRef = {
    valueType: TypeId,
    projection: AbstractStorageProjection,
    accessors: AbstractAccessorContract,
    access: AccessMode,
    mutability: Mutability,
    capturedSources: CapturedStorageSources,
    evaluationIdentity: NodeId<Typed>,
    witnessResolutions: WitnessResolutionStamp
}

PlaceRef =
    PhysicalPlace(PhysicalStorageRef)
  | AbstractPlace(AbstractStorageRef)

placeValueType(PhysicalPlace(p)) = p.valueType
placeValueType(AbstractPlace(a)) = a.valueType

ValueCategory =
    RValue
  | Place(PlaceRef)

PhysicalStorageRequirement = {
    access: AccessMode,
    minimumLifetime: LifetimeId,
    addressSpace: AddressSpaceRequirement,
    source: PhysicalStorageSourceRequirement
}

AddressSpaceAdmissionProof =
    ExactAddressSpaceAdmission(actual: AddressSpace)
  | ListedAddressSpaceAdmission(actual: AddressSpace,
                                admitted: CanonicalFiniteSet<AddressSpace>)
  | StandardAddressSpaceAdmission(actual: AddressSpace,
                                  rule: StandardEnvironmentRuleId,
                                  environment: StandardEnvironmentId)
  | GenericAddressSpaceAdmission(actual: AddressSpace,
                                 variable: CanonicalBoundVariable,
                                 evidence: ConstraintEvidence)
  | FormalAddressSpaceAdmission(
        actual: PhysicalFormalEntryProofId,
        required: AddressSpaceRequirement,
        implication: AddressSpaceRequirementImplicationProof)

AddressSpaceRequirementImplicationProof = {
    provided: AddressSpaceRequirement,
    required: AddressSpaceRequirement,
    environment: SemanticEnvironmentId,
    rule: AddressSpaceImplicationRule
}

AddressSpaceImplicationRule =
    ReflexiveAddressSpaceRequirement
  | FiniteAddressSpaceSubset
  | StandardAddressSpaceImplication(StandardEnvironmentRuleId)
  | GenericAddressSpaceImplication(ConstraintEvidence)

admittedAddressSpace(ExactAddressSpaceAdmission(a)) = ConcretePhysicalAddressSpace(a)
admittedAddressSpace(ListedAddressSpaceAdmission(a, _)) = ConcretePhysicalAddressSpace(a)
admittedAddressSpace(StandardAddressSpaceAdmission(a, _, _)) = ConcretePhysicalAddressSpace(a)
admittedAddressSpace(GenericAddressSpaceAdmission(a, _, _)) = ConcretePhysicalAddressSpace(a)
admittedAddressSpace(FormalAddressSpaceAdmission(entry, _, _)) =
    FormalPhysicalAddressSpace(entry)

addressSpaceRequirement(ExactAddressSpaceAdmission(a)) = ExactAddressSpace(a)
addressSpaceRequirement(ListedAddressSpaceAdmission(_, s)) = OneOfAddressSpaces(s)
addressSpaceRequirement(StandardAddressSpaceAdmission(_, r, _)) =
    AnyReferenceableAddressSpace(r)
addressSpaceRequirement(GenericAddressSpaceAdmission(_, v, _)) = AddressSpaceVariable(v)
addressSpaceRequirement(FormalAddressSpaceAdmission(_, r, _)) = r

PhysicalSourceAdmissionEvidence =
    AnyPhysicalSource
  | RegisteredPhysicalSourceFact(fact: PhysicalStorageSourceFact)

PhysicalSourceProvenanceAdmissionProof = {
    provenance: PhysicalStorageSourceProvenance,
    requirement: PhysicalStorageSourceRequirement,
    evidence: PhysicalSourceAdmissionEvidence
}

PhysicalStorageSourceAdmissionProof = {
    storage: PhysicalStorageRef,
    provenanceProof: PhysicalSourceProvenanceAdmissionProof
}

sourceRequirement(p: PhysicalStorageSourceAdmissionProof) =
    p.provenanceProof.requirement

AccessProvisionProof = {
    actual: AccessMode,
    required: AccessMode
}

PhysicalStorageProof = {
    storage: PhysicalStorageRef,
    requirement: PhysicalStorageRequirement,
    accessProof: AccessProvisionProof,
    lifetimeProof: OutlivesProof,
    addressSpaceProof: AddressSpaceAdmissionProof,
    sourceProof: PhysicalStorageSourceAdmissionProof
}

PhysicalStorageProofId = ContentId<PhysicalStorageProof>
```

For one discipline, access modes are ordered by operation inclusion:

```text
provides(actual, required) iff
    actual.discipline = required.discipline and
    actual.operations isSupersetOf required.operations

effectiveAccess(storage: PhysicalStorageRef | AbstractStorageRef) =
    storage.access                                    when storage.mutability = Mutable
    remove(Write, storage.access)                     when storage.mutability = Immutable
    remove(Write, storage.access)                     when storage.mutability = UnknownMutability
effectiveAccess(PhysicalPlace(p)) = effectiveAccess(p)
effectiveAccess(AbstractPlace(a)) = effectiveAccess(a)

isPhysicalStorage(PhysicalPlace(_)) = true
isPhysicalStorage(AbstractPlace(_)) = false
```

Meet is operation intersection and join is operation union when disciplines match. Different
disciplines are incompatible rather than silently joining; any language bridge between atomic and
ordinary access is a named standard-environment operation with an explicit plan. Public place/ref
types require a non-empty operation set, while the empty internal meet represents `NoAccess`.

`TYP-ALS-001`: `joinAlias` is a canonical commutative, associative, and idempotent operation.
Joining equal exact roots returns that root; joining distinct exact/joined roots returns their
sorted duplicate-free `JoinedAliasRoots` set; a singleton set canonicalizes to `ExactAliasRoot`;
and any join with `UnknownAliasRoot` is unknown. The joined-root set must contain at least two IDs.

`TYP-ALS-002`: Copying, passing, returning, or binding a reference preserves its
`AliasProvenance`. A control-flow merge applies `joinAlias`; it never substitutes the merge node's
identity as a fresh root. A generic reference may use
`StableAliasRegionIdentity(parameterIdentity)` for its exact symbolic root, while an operation that cannot prove a finite provenance set uses
`UnknownAliasRoot` and is checked conservatively for conflicts.

`TYP-ALS-003`: `CompareAliasOverlap` is total, symmetric, and independent of query order. Two
`KnownAliasRegions` values are `ProvenDisjoint` exactly when their region sets have empty
intersection; the proof stores those exact sets. Otherwise the result is `MayOverlap` naming the
least common region in canonical order. `AnyAliasRegion` may overlap every value, with
`OneUnknownAlias` or `BothUnknownAliases` recording how many operands are unknown. Consequently two
distinct `ExactAliasRoot` values are disjoint, a joined provenance overlaps exactly the roots it
contains, and unknown provenance is always checked conservatively.

`TYP-ALS-004`: An exact alias-region identity is proof-relevant semantic data, not a fresh node ID.
Only a storage declaration, fresh allocation/temporary, or projection constructor whose intrinsic
rule proves a disjoint region may introduce a new `ExactAliasRoot`. Copy, read-view formation,
dereference, and
unproved projection constructors preserve the source provenance; a control-flow choice joins it;
an operation unable to justify either result produces `UnknownAliasRoot`. In particular, two
fields or elements receive different region identities only when the aggregate/registered
projection rule proves they cannot overlap. Dynamic indices and opaque pointer arithmetic do not
become disjoint merely because their syntax has different `NodeId` values.
`StableAliasRegionIdentity` is the only injection from the broad `StableSemanticId` domain;
accessor invocations use their nominal `AccessorInvocationAliasRegion` alternative directly, so
temporary allocations analogously use `TemporaryStorageAliasRegion`. No arbitrary `ContentId` can
be reinterpreted as either nominal alias-region kind.

`TYP-ADR-001`: `OneOfAddressSpaces(s)` is well formed only when `s` is nonempty.
`AddressSpaceVariable(v)` requires a value-parameter sort whose declared value type is the standard
address-space kind. An `AddressSpaceAdmissionProof` is valid only when
`admittedAddressSpace(proof)` is admitted by `addressSpaceRequirement(proof)`: exact/listed cases
use equality/membership, a standard case replays its rule in the exact stored environment, and a
generic case resolves its evidence to that variable's specialized address-space constraint. A
target-dependent set is therefore not baked into function-type identity, while every use still has
an exact proof for its actual address space.

`TYP-ADR-002`: `FormalPhysicalAddressSpace(entry)` is permitted only on a physical formal root. The
entry proof resolves the same callable signature and role as that root, contains a well-formed
physical `PassingMode`, and its mode's location requirement is the sole declared address-space and
source guarantee. `FormalAddressSpaceAdmission` proves that guarantee implies the consumer's
required address-space predicate by reflexivity, finite-set inclusion, a versioned standard rule,
or exact generic evidence. Its implication endpoints are exactly
`(formalAddressSpaceRequirement(entry), required)`. It never chooses a representative concrete address space. An operation
whose semantics require one concrete address space must either be specialized until the formal
space is concrete or consume a registered operation proof explicitly defined over the symbolic
space.

`TYP-ADR-003`: `PointerType`, `ReferenceType`, and `ReferenceHandleShape` require one concrete
`AddressSpace`. Forming a first-class pointer/reference from physical storage therefore consumes a
`ConcreteAddressSpaceProjectionProof`. `AlreadyConcreteAddressSpace` unwraps exactly
`ConcretePhysicalAddressSpace(result)`. `ExactFormalAddressSpace(entry)` is valid only when the
entry's substituted location requirement is `ExactAddressSpace(result)`.
`SpecializedFormalAddressSpace` is valid only when exact generic evidence reduces the entry's
address-space variable to `result`. `AnyReferenceableAddressSpace` and an unresolved
`OneOfAddressSpaces` do not choose an arbitrary representative and produce a structured
non-denotable-address-space failure. This restriction does not prevent passing the same symbolic
physical location to another compatible physical parameter, which needs no first-class handle.

`TYP-SRC-001`: `PhysicalStorageSourceProvenance` is a canonical proof-relevant set, not a lookup hint.
A stored declaration receives only the facts proved while checking its storage declaration; a
physical formal receives exactly `formalSourceProvenance(entry)`; dereference and ordinary
projections preserve their input facts; and a registered projection/accessor may preserve, remove,
or add facts only through its named versioned component rule. Copying a declaration modifier at the
use site, inferring provenance from value type, or treating a matching address space as a source
fact is invalid. `PhysicalSourceProvenanceAdmissionProof` with
`RegisteredPhysicalSourceFact` checks exact rule, static inputs, and
environment, so a varying-input-only or similar intrinsic cannot accept unrelated readable memory.

`TYP-PLC-001`: `PhysicalPlace` and `AbstractPlace` are disjoint closed alternatives. A stored local,
physical parameter, global, stored field, builtin element, or dereferenced reference is physical
only when its constructor proves the path, address space, lifetime, alias provenance, and typed
source provenance. A property,
declared/user subscript, or setter-backed projection is abstract even when it is readable and
writable. For every successful `ValueClassifier(t, Place(place))`,
`placeValueType(place) = t`; a place cannot rely on its enclosing expression to supply a different
storage element type. Physical/abstract projection constructors compute `valueType` from their
checked declaration, element, or dereference result, and validators compare it with the enclosing
classifier after substitution.

`TYP-PLC-002`: A reference accessor does not retroactively make its property or subscript physical.
Invoking the exact access-indexed accessor is an explicit effectful operation in the checked plan.
Explicit reference syntax may expose its result as a first-class reference value; parameter access
planning for `ConstRefMode` or `RefMode` may instead consume that result immediately with a stored
dereference. Neither operation changes the original property's classifier. Applying
`DereferencedReference` under the selected operation creates a new physical place with the returned
reference's lifetime, access, alias, address-space, and source-provenance facts. Receiver and indices
are evaluated exactly once by the access plan. A getter, setter, value conversion, or temporary can
never stand in for this operation.

`TYP-PLC-003`: A registered resource or target projection may construct `PhysicalPlace` only when
its checked `RegisteredPhysicalProjectionApplicationAt<S>` supplies stable reference semantics.
The place path contains only the application's stage-free
`RegisteredPhysicalProjectionIdentity`; resolving the enclosing typed expression must recover the
one immutable application with that identity. The application retains the exact
`RegisteredDataOperationRegistration` (including `StandardEnvironmentId` and static inputs), every
executable base/index operand and its evaluation order, the closed control proof, and the exact
intrinsic `RegisteredPhysicalProjectionResultProof`. That result proof derives the complete output
storage shape, including source provenance, from the registered schema and named runtime endpoints,
but is deliberately not a
use-specific `PhysicalStorageProof`; a later consumer proves its own requirement. A bare rule ID,
canonical static arguments, or reconstructed base path is not physical-storage evidence. Physical
referenceability is not the same as permission to form a general byte pointer.

`TYP-PLC-004`: Every ordinary `AbstractAccessor.selector` and every
`AbstractRefAccessor.selector` resolves to one callable surface whose signature matches the
getter/setter/access-indexed reference role and captured receiver/index shape. Every map key equals
the contained `AbstractRefAccessor.access`, which in turn equals its result contract's access.
Only the exact key requested by an operation may be selected: `ReadWriteAccess` is not a fallback
for a missing `ReadAccess` accessor, nor vice versa. A witness selector retains the
exact all-kind accessor entry key, not a property declaration position; dynamic and builtin
selectors validate their registered slot/rule. A builtin selector's `RegisteredCallableRule`
provides the only bridge from its standard-environment registration to its logical builtin
dispatch. `AbstractStorageRef.witnessResolutions` is the
minimal published resolution union for all witness IDs in its selectors and specialized
declaration refs. Accessor selection is therefore executable without name or conformance search,
while the abstract place itself remains nonphysical.

`TYP-PLC-005`: `AbstractStorageRef.capturedSources` is the sole runtime-source authority for every
accessor of that place. A receiver has the unique `StorageReceiverSource` key. Each source index has
one `StorageArgumentSource(argument.id)` key whose value contains the complete checked
`SourceArgument`, including label, form, and origin. Pack expansion paths are projections of that
one captured argument, not independently evaluated copies. No projection constructor stores a
second base/index list from which an accessor call could be reconstructed.

`TYP-PLC-006`: `CapturedStorageSources.evaluationOrder` is a duplicate-free bijection onto
`captures`: receiver first when present, then source arguments in source order. Each capture is
evaluated exactly once. A `CapturedStorageProjection` may then select the empty path or one expanded
element from that captured value without evaluating the original expression again; a zero-length
expansion has no projection. These facts are preserved when a getter, setter, explicit reference
formation, or authorized access-indexed reference-accessor invocation is planned, and a later stage cannot
re-read syntax to choose different
sources or evaluation order.

`TYP-PLC-007`: An `AbstractRefAccessor.resultContract` resolves to an immutable contract whose
`selector` is byte-identical to the accessor selector and whose signature is the specialized
callable signature selected for that accessor. Its result type projects to its declared handle kind,
referent, address space, access, and lifetime fields. Its five nontrivial provenance components have
one closed derivation each: fixed/captured/registered address space, fixed/captured/access-derived
mutability, static/captured/minimum-captured/registered lifetime, and preserved/fresh/unknown/
registered alias provenance, plus fixed/captured/registered physical-source provenance. Every
registered derivation stores the exact standard environment in
which its rule was validated, in addition to its static inputs. Declaration and
standard-environment validation construct these contracts; a property use cannot supply one. Every
captured provenance rule names only `AccessorReceiverProvenance` or an
`AccessorParameterProvenance(ParameterKey)` from the declaration's specialized callable signature.
A declaration contract can never contain `CapturedStorageSourceRole`, `SourceArgumentId`, or any
other call-site node identity.
`accessorResultAuthority(accessor)` resolves the selected callable surface under that same
selector/signature and its kind is exactly
`AccessorReferenceHandleCallableResult(accessor.resultContract)`. The declaration header,
requirement entry, dynamic-slot introducer, or registered builtin record that owns the surface
publishes that authority. A property use cannot replace it with an ordinary, fixed, registered, or
sibling-accessor authority.
For `AccessDerivedAccessorMutability`, `ReadAccess` derives `UnknownMutability`: a read-only view
cannot claim that its underlying storage is immutable. `ReadWriteAccess` derives `Mutable`. Every
other access/discipline is rejected unless a separately registered mutability rule defines it.

`TYP-PLC-008`: Instantiating an accessor reference-result contract is a total checked operation over
the accessor call's exact captured-source map, a stage-free `AccessorInvocationIdentity`, and an
`AccessorProvenanceSourceMapId` validated for that invocation. The identity is derived from the
authenticated `SemanticOperationSiteAssignment` stored by the checked accessor invocation:
`identity = accessorInvocationIdentity(site.site)`. It is a nominal wrapper around that site's
`ContentId`, not an allocation address, typed-node identity/serialization ordinal, unconstrained
`StableSemanticId`, or later IR producer ID. Resolving a
declaration-stable role through that map yields one
`CapturedStorageProjection`; the projection names an existing captured source and derives only from
that source's checked place or reference-handle provenance. `FreshAccessorAlias(g)` is valid only
when the versioned registration `g` proves that this invocation creates distinct storage, its
allocation semantics occur on the retained accessor call, and `g.lifetimeRule` is the same rule used
to derive the result contract's lifetime. It then derives exactly
`ExactAliasRoot(accessorInvocationAliasRoot(identity))`; it cannot accept an independently supplied
stable identity or add an implementation-chosen child role. An ordinary accessor without this
generative proof must preserve a captured alias or use `UnknownAliasRoot`;
`ConservativeUnknownAlias` yields only `UnknownAliasRoot`. A registered rule is replayed in the
exact `RegisteredAccessorProvenanceRule.environment` stored beside its static inputs. Missing source
provenance, a
mismatched result type/signature, or any attempted access, mutability, lifetime, address-space,
alias, or source-provenance amplification is a failed instantiation, never an arbitrary successful
handle shape.

`TYP-PLC-009`: An `AccessorProvenanceSourceMap` is canonical invocation evidence, not declaration
metadata. Its receiver entry is present exactly when the specialized accessor signature has a
receiver and maps to the captured projection bound to `ReceiverSlotRole`. It has one
`AccessorParameterProvenance(k)` entry for every expanded `ParameterSlotRole(k)` and no other
parameter entry; each maps to the projection on the unique source binding that the invocation's
`ArgumentMap` assigns to that slot. Every projection resolves in the invocation's exact
`CapturedStorageSources`, including its expansion path. Reordering source syntax, rebuilding a call,
or choosing a different pack element therefore cannot alter a declaration contract, while an
invalid or missing formal-to-captured binding is a closed invocation failure.

`TYP-PLC-010`: A `RegisteredPhysicalProjectionResultProof` is intrinsic construction evidence. Its
identity and registration equal the enclosing application, its storage path is exactly
`RegisteredPhysicalProjection(identity)`, and its type equality relates the registered result type
to `storage.valueType`. Its access, mutability, lifetime, address-space, alias, and source-provenance
derivations each
name only a registered schema value or runtime operand role in that same application and replay the
component rule in `registration.environment` with `registration.staticInputs`. It contains no
consumer requirement. `provePhysicalStorage(storage, requirement, context)` remains the only
constructor of a use-specific `PhysicalStorageProof`, so checking the same projection for two later
uses cannot change its place identity or intrinsic provenance.

`TYP-PLC-011`: A `ConstRefMode(r)` parameter or receiver name denotes
`PhysicalPlace(storage)` whose path is the exact `ConstRefFormalRoot(signature, role)`. Its access
view is `ReadAccess`, lifetime is `CallableActivationLifetime(signature)`, alias is
`UnknownAliasRoot`, and address space and source-provenance facts are the reusable formal facts
proved by the parameter's checked location requirement and logical ABI entry: its address space is
exactly `FormalPhysicalAddressSpace(entry)` and its source facts equal
`formalSourceProvenance(entry)`. Its mutability is
`UnknownMutability`, not `Immutable`: the formal does not know whether each caller supplied mutable
or immutable storage, while its read-only access view independently forbids writes. A call-site
admission retains the caller's more precise storage and alias proof without mutating this formal
root. Ordinary proof-carrying physical projections from the formal remain `PhysicalPlace`, preserve
the activation-lifetime ceiling and source provenance unless their registered rule proves an exact
transformation, and can never amplify `ReadAccess`. The result can be loaded, passed to another
compatible `ConstRefMode`, or used by physical read operations, but cannot satisfy `OutMode`,
`InOutMode`, or `RefMode`, be written, or escape its activation lifetime.

`TYP-PLC-012`: A `RefMode(r)` parameter or receiver analogously denotes `PhysicalPlace(storage)`
with `RefFormalRoot(signature, role)`, `ReadWriteAccess`,
`CallableActivationLifetime(signature)`, `Mutable`, and `UnknownAliasRoot`; its formal address space
and source facts use the same exact entry equations. The two physical formal
roots are nominally distinct so body checking cannot infer a mutable view from an equal value type.
For both roots, every non-root physical projection uses the ordinary proof-carrying constructors in
`PhysicalPlacePath`; there is no third nonphysical read-view path, auxiliary lifetime operation, or
hidden read-only ABI category.

`TYP-PLC-013`: Every `BuiltinElement(base, application)` names one immutable
`BuiltinPhysicalProjectionApplicationAt<S>` by `BuiltinPhysicalProjectionIdentity`. Its result
path is exactly `BuiltinElement(application.output.inputStorage.path, application.identity)`, so the
separately stored `base` must equal the application's input path. The path never stores an index
expression or any other AST identity. The named application is the sole authority for the exact
checked base, converted index, written evaluation order, builtin operation rule, result-type proof,
and complete output storage. Resolving the path identity to zero, two, a registered projection, or
an application with a different input path is an invalid typed projection. Later Core and IR
consumers retain the complete application beside the path rather than requiring a global raw-ID
resolver.

`TYP-PLC-014`: Every `DereferencedReference(application)` names one immutable dereference
application by `DereferenceApplicationIdentity`. For explicit syntax that application is the enclosing
`CheckedDereferenceAt<S>`; for an internal reference-accessor operation it is the dereference stored
in an `InternalRefStoragePlanAt<S>` or `ParameterReferenceAccessorPlanAt<S>`. In every case the exact executable handle operand and
its `ReferenceHandleProof` are retained independently of the path, and the resulting
`DereferencedStorageProof.identity = application` with
`output.storage.path = DereferencedReference(application)`. Core and IR retain that identity with
the executable handle operand and proof-derived endpoint shapes. A typed-node ID, the handle's
producer node, or an equal handle type can never substitute for the application identity.
The internal operation's dereference site is the fixed-role child of its accessor invocation's
authenticated operation site, so neither operation is derived from the fallback query's typed node.
For a parameter-reference-accessor operation, `CallSlotProjectionOwner` retains the enclosing typed
call, exact `BoundCallSlot`, and full child role path instead of pretending the dereference has a
standalone Typed projection node.

`TYP-PLC-015`: A retained operational application identity is constructed only from a serialized
`SemanticOperationSiteKey`. Parsed syntax anchors the key in its canonical physical source ranges
and deterministic same-range occurrence before a CST or AST snapshot exists. Macro-origin ranges
are projected through the immutable preprocessing origin map. Synthesized, imported, and recovery
syntax uses the corresponding closed stage-free anchor. A synthesized anchor contains only a
source/import/recovery root plus a fixed rule/ordinal synthesis path; it never embeds the source
`SynthesizedSemanticId`, `SynthesisKey`, cause, or canonical arguments. A recovery anchor contains
only canonical source ranges and an occurrence; it never embeds `ErrorId` or a semantic diagnostic
anchor. Every implicit child operation appends its
fixed `RuleId` and deterministic ordinal to `rolePath`; cloning or expansion appends a distinct
role rather than reusing the source
application. Physical projection, dereference, accessor invocation, and temporary-storage allocation
constructors content-address that complete key and wrap the result in
distinct nominal types. None accepts `StableSemanticId`, `CstNodeId`, `AnyNodeId`, `NodeId<Typed>`, a Core
value ID, or an IR instruction ID. Requests carry an authenticated site assignment explicitly, and
their successful
application identity must equal the corresponding constructor result, avoiding both an AST content-
identity cycle and a later attempt to recover a site from `Origin`.

`TYP-PLC-016`: `AssignSemanticOperationSite` normalizes the supplied origin to exactly one closed
source/synthesis/import/recovery anchor using only its explicit frozen assignment context. That
context is part of the query key and records the exact source snapshots, expanded-token views, and
earlier-stage provenance snapshot traversed; it cannot include the Typed snapshot being built, and
no ambient source manager or AST registry participates. A root
derived from synthesized or recovery `Origin` recursively projects provenance to the closed
`SemanticOperationSourceAnchor` and records only the fixed derivation path shown above. Failure to
reach exactly one such root is `OperationOriginHasNoSourceAnchor`; copying the origin's synthesis
cause or error identity into the site is invalid.
A root
assignment has the singleton requested role path; a child assignment has the parent's anchor and
appends exactly the requested role. Validation against
an owner node replays that normalization from the node's required serialized `Origin` and requires
byte-identical origin, anchor, path, and deterministic occurrence. Thus a caller cannot reuse a
valid assignment from a sibling expression. `PhysicalProjectionSiteAssignment` and its assign/
validate functions are compatibility aliases of this one schema rather than an independent
identity mechanism. A `PhysicalProjectionSemanticResultSnapshot` is
published only after its `queryDependencies` form a bijection onto the exact completed
`PlanStorageAccessAt<Published>` results that contain the keyed `storagePlans`; every content ID
resolves byte-identically. `BuildPhysicalProjectionApplicationIndex` traverses the Typed snapshot
and that frozen result snapshot, registering every builtin, registered, explicit-dereference,
storage-fallback, and physical call-slot application under its nominal identity and exact owner. A
`CallSlotProjectionOwner(call, slot, path)` resolves the selected typed call, its exact
`ApplicableCallSlotPlan`, and the unique nested parameter-reference-accessor dereference whose
stored site has exactly `path`. The path includes every fixed `RuleId`/ordinal child step, so two
implicit projections in one slot cannot alias by container order. Selected call-slot plans are
already immutable operands of the typed call and therefore are not duplicated into
`PhysicalProjectionSemanticResultSnapshot`; that side snapshot remains the authority only for
completed storage-access query plans that are not AST children. The builder never reads an ambient
or ephemeral scheduler cache. Each map is injective;
every owner resolves to one matching-kind application whose
stored site assignment validates against that owner (or the published plan's authenticated parent),
and whose identity equals the matching constructor applied to `site.site` and to the index key. For
`CallSlotProjectionOwner`, the authenticated parent is the exact typed source retained by the
slot's `PhysicalParameterSourceAt<S>`, not the enclosing call node: the accessor invocation site
validates against that source's `NodeId<Typed>`, and the stored child dereference site extends that
same anchor by the fixed dereference role. Pairing an accessor plan with an equal-classified sibling
source, or validating its site against `call`, is invalid.
Duplicate or unresolved owners make the semantic snapshot invalid. Core
and IR carry complete applications and do not serialize this Typed-snapshot index.

`TYP-PLC-017`: `StoredRoot` contains only the stage-free `CanonicalDeclRef` that owns the physical
storage. Checking a name expression obtains that root from `BoundDeclUse.target`, but retains the
complete `BoundDeclUse` separately on the typed expression for lookup, access, witnesses,
extensions, diagnostics, and origin. No `LookupPath`, `AccessDecision`, witness-resolution sidecar,
`Origin`, or AST node is copied into `PhysicalPlacePath`. Consequently copying a use of the same
specialized declaration preserves physical-storage identity, while Core/IR static storage proofs
cannot acquire an AST reference transitively through the root.

`TYP-ACC-001`: `InMode` requires an ordinary readable value preparation. `OutMode` requires write
access and performs no pre-read; `InOutMode` requires read/write access and an exclusive call claim.
Those abstract-domain modes may use their separately named getter, setter, materialization, and
write-back plans. A physical-domain mode has no such route. `ConstRefMode(r)` or `RefMode(r)` first
instantiates its complete `PhysicalStorageRequirement` from the mode and invocation. It then
requires either the argument's existing `PhysicalPlace(p)`, or an exact access-indexed reference
accessor invocation followed by an explicit dereference whose endpoint is a new
`PhysicalPlace(p)`. In either case it requires a `PhysicalStorageProof` for that exact endpoint and
requirement, a non-recovery equality between `p.valueType` and the substituted parameter value
type, and chapter 7's conversion-free `PhysicalStorageIdentityProof`. The chapter 7
`PhysicalParameterBindingProofAt<S>`
retains those facts, the exact `AccessEnvironmentId`, and whether the physical endpoint was direct
or produced by the stored accessor plan.

`TYP-ACC-002`: “Overlapping” means `CompareAliasOverlap` returned `MayOverlap`; syntax similarity or
container order is never an alias test. Two `ConstRefMode` read claims may overlap. An exclusive
`OutMode`/`InOutMode` claim conflicts with every overlapping live read/write claim. `RefMode`
aliasing is permitted only by the versioned rule stored with its exact read/write access mode and
still obeys atomic discipline. Chapter 7's
`CheckCallAliasClaims` applies this algebra to all receiver/argument plans together, and the
selected candidate stores either every pairwise compatibility proof or the structured conflict.

`TYP-ACC-003`: Access inclusion, meet/join within a discipline, immutable/unknown write removal, call-claim
compatibility, and atomic/ordinary incompatibility have exhaustive table and algebra property tests.

`TYP-ACC-004`: Neither `ConstRefMode`/`__constref` nor `RefMode`/`__ref` can use a materialized
temporary, getter, setter/write-back, value conversion, or any plan that changes the selected
physical endpoint's identity. A property or declared subscript is therefore inapplicable unless its
`AbstractAccessorContract.referenceAccessors` contains the exact required key. A
`ReadWriteAccess` (`ref`) accessor alone does not satisfy `ConstRefMode`; a `ReadAccess`
(`constref`) accessor alone does not satisfy `RefMode`; getter-only and get-plus-set surfaces satisfy
neither. Failure is reported as direct nonphysical storage, missing/wrong accessor kind, accessor
checking failure, forbidden nonidentity conversion, or the exact failed physical-proof dimension,
not collapsed to a generic l-value diagnostic. `OutMode` and `InOutMode` remain distinct because
their explicit abstract write-back contracts are valid language behavior.

`TYP-ACC-005`: A `PhysicalStorageProof` is valid only when its storage and requirement are the
stored endpoints, `accessProof` proves `provides(effectiveAccess(storage), requirement.access)`,
`lifetimeProof` proves `storage.lifetime` outlives `requirement.minimumLifetime`, and
`admittedAddressSpace(addressSpaceProof) = storage.addressSpace` with
`addressSpaceRequirement(addressSpaceProof) = requirement.addressSpace`. Its `sourceProof.storage`
is the same storage, `sourceProof.provenanceProof.provenance = storage.sourceProvenance`, and its
source requirement equals `requirement.source`. `AnyPhysicalSource` discharges only
`AnyPhysicalStorage`; `RegisteredPhysicalSourceFact(fact)` requires that exact fact to occur in the
stored provenance, requires the fact's rule and static inputs to equal the requirement, and replays
that rule in the stored standard environment. Omitting address-space or source admission is
not a weaker proof; it is an ill-formed proof value. Declaration context is never re-read to invent
source provenance at the use.

`TYP-ACC-006`: `PhysicalParameterBindingProofAt<S>` is shared by both physical modes and is indexed
by the complete `PassingMode`. Its storage equals the endpoint of either its direct-source proof or
its exact accessor-invocation-and-dereference plan; its type equality is non-recovery; its
`PhysicalStorageProof.requirement` equals
`instantiatePhysicalStorageRequirement(mode, accessEnvironment.invocationLifetime)`; and its
physical identity proof preserves both type and storage without a conversion operation.
`ConstRefMode` therefore stores a physical
read-view proof, while `RefMode` stores a physical read/write proof. Neither proof can be converted
to the other by dropping or adding access, and neither has a temporary-backed alternative.

This replaces both a single `isLeftValue` bit and an independent `isPhysicalStorage` flag. Physical
storage is a proof-carrying alternative, so generic schema inspection can derive
`isPhysicalStorage` without trusting two booleans that may disagree. A conversion/access plan
records every load, accessor invocation, dereference, materialization, and write-back explicitly.

## Constants and symbolic values

```text
FloatFormat =
    BinaryFloatFormat(semantics: StandardEnvironmentRuleId,
                      storageBits: UInt16,
                      exponentBits: UInt16,
                      significandBits: UInt16,
                      supportsSubnormals: Bool,
                      supportsInfinityAndNaN: Bool)
  | RegisteredFloatFormat(rule: StandardEnvironmentRuleId,
                          arguments: CanonicalArguments)

ConstValue =
    ErrorConst(ErrorId)
  | BoolConst(Bool)
  | IntConst(bitWidth: UInt16, signed: Bool, value: BigInt)
  | FloatConst(format: FloatFormat, bits: BitString)
  | StringConst(Utf8String)
  | EnumConst(type: TypeId, tag: BigInt)
  | TupleConst(NodeList<ConstValue>)
  | AggregateConst(type: TypeId, fields: NodeMap<DeclId, ConstValue>)
  | SymbolicConst(expression: CanonicalConstExprId)
  | PackConst(NodeList<ConstValue>)

CanonicalConstExprId = ContentId<CanonicalConstExpr>

CanonicalConstAtom =
    BoolAtom(Bool)
  | IntAtom(bitWidth: UInt16, signed: Bool, value: BigInt)
  | FloatAtom(format: FloatFormat, bits: BitString)
  | StringAtom(Utf8String)
  | EnumAtom(type: TypeId, tag: BigInt)

CanonicalConstOperation =
    LiteralConst(CanonicalConstAtom)
  | BoundConst(CanonicalBoundVariable)
  | ApplyPureConst(rule: RuleId, operands: NodeList<CanonicalConstExprId>)
  | SelectConst(condition: CanonicalConstExprId,
                whenTrue: CanonicalConstExprId,
                whenFalse: CanonicalConstExprId)
  | TupleConstExpr(NodeList<CanonicalConstExprId>)
  | AggregateConstExpr(type: TypeId,
                       fields: CanonicallyOrderedMap<DeclId, CanonicalConstExprId>)
  | PackConstExpr(NodeList<CanonicalConstExprId>)
  | PackLengthConst(CanonicalBoundVariable)

CanonicalConstExpr = {
    resultType: TypeId,
    operation: CanonicalConstOperation
}

SymbolicBoolValue = {
    expression: CanonicalConstExprId
}

ShapeAxis =
    ConcreteAxis(size: BigNat)
  | SymbolicAxis(size: CanonicalConstExprId)
  | PackAxis(variable: CanonicalBoundVariable)

ShapeValue = {
    axes: NodeList<ShapeAxis>
}
```

Symbolic constant expressions are canonical algebraic terms over generic value parameters and
allowed pure operators. Host integer overflow, host floating-point mode, or pointer identity never
defines constant semantics.

`TYP-CON-001`: `ApplyPureConst.rule` must resolve to a total, deterministic standard-environment
constant rule whose operand and result types match the expression DAG. The DAG is finite. Its
canonicalizer applies only algebraic traits declared by that rule, so commutativity or folding is
never inferred from a host operator. `SymbolicBoolValue.expression` resolves to the standard
environment's canonical Boolean type.

`TYP-CON-002`: A `BinaryFloatFormat` has positive storage/exponent/significand widths and a
versioned standard rule that defines its sign, exponent, significand, special-value, rounding, and
canonical-NaN interpretation. A `RegisteredFloatFormat` rule supplies the same complete contract.
Every `FloatConst`/`FloatAtom.bits` length equals its format's storage width. Host floating-point
types, excess precision, current rounding mode, and NaN payload rewriting cannot define constant
identity or evaluation.

`TYP-SHP-001`: Shape axes are outermost-to-innermost; an empty list is scalar shape and every
concrete axis is positive. A symbolic axis resolves to the standard environment's canonical
nonnegative-integer type and a pack axis names a value/type-pack cardinality variable. Shape
equality is structural equality after constant normalization; host container sizes are not shape
identity.

## Constraints and generic solutions

```text
Constraint =
    EqualType(TypeId, TypeId)
  | EqualValue(ConstValue, ConstValue)
  | RepresentationAdjusts(TypeId, TypeId)
  | InterfaceRefines(InterfaceInstanceKey, InterfaceInstanceKey)
  | Conforms(TypeId, InterfaceInstanceKey)
  | Coercible(TypeId, TypeId)
  | PackCountEqual(PackId, ConstValue)
  | PackNonEmpty(PackId)
  | LifetimeOutlives(LifetimeId, LifetimeId)
  | HasDifferentialInfo(TypeId)
  | WellFormed(TypeId)

ValueEqualityProofId = ContentId<ValueEqualityProof>
PackCountWitnessId = ContentId<PackCountWitness>

PackCountDerivation =
    ConcretePackCountWitness(elements: BigNat)
  | DeclaredPackCountWitness(binder: CanonicalBinderRef,
                             slot: CanonicalConstraintSlot)
  | EqualPackCountWitness(source: PackCountWitnessId,
                          equality: ValueEqualityProofId)
  | RegisteredPackCountWitness(rule: RuleId,
                               inputs: CanonicalArguments,
                               premises: NodeList<PackCountWitnessId>)

PackCountWitness = {
    pack: PackId,
    count: ConstValue,
    derivation: PackCountDerivation
}

PackNonEmptyWitnessId = ContentId<PackNonEmptyWitness>

PackNonEmptyDerivation =
    ConcreteNonEmptyPackWitness(count: BigNat)
  | DeclaredNonEmptyPackWitness(binder: CanonicalBinderRef,
                                slot: CanonicalConstraintSlot)
  | PositiveCountPackWitness(count: PackCountWitnessId,
                             proof: PositiveConstProof)
  | RegisteredNonEmptyPackWitness(rule: RuleId,
                                  inputs: CanonicalArguments,
                                  premises: NodeList<PackNonEmptyWitnessId>)

PositiveConstProof = {
    value: ConstValue,
    relation: StrictlyGreaterThanZero,
    rule: RuleId
}

PackNonEmptyWitness = {
    pack: PackId,
    derivation: PackNonEmptyDerivation
}

TypeEqualityProofId = ContentId<TypeEqualityProof>

TypeEqualityProof = {
    left: TypeId,
    right: TypeId,
    canonical: TypeId,
    derivation: TypeEqualityDerivation
}

TypeEqualityDerivation =
    CanonicalNormalization
  | GenericAssumption(binder: CanonicalBinderRef,
                      slot: CanonicalConstraintSlot)
  | DeclaredEquality(rule: RuleId,
                     inputs: CanonicalArguments,
                     premises: NodeList<TypeEqualityProofId>)
  | Congruence(constructorRule: RuleId,
               operands: NodeList<TypeEqualityProofId>)
  | Symmetry(of: TypeEqualityProofId)
  | Transitivity(left: TypeEqualityProofId,
                 right: TypeEqualityProofId)
  | RecoveryEquality(ErrorId)

ConstraintEvidence = TypeEqualityProof | ValueEqualityProof |
                     RepresentationAdjustmentPath |
                     InterfaceRefinementProof | ConformanceEvidence |
                     TypeCoercibilityEvidence | PackCountWitness |
                     PackNonEmptyWitness | OutlivesProof | ValueDifferentialInfoEvidence |
                     WellFormednessProof

ConformanceEvidence =
    InterfaceSubtypeEvidence(witness: InterfaceSubtypeWitnessId)

ValueEqualityProof = {
    left: ConstValue,
    right: ConstValue,
    canonicalValue: ConstValue
}

WellFormednessProof = {
    type: TypeId,
    checkedRules: NonEmpty<RuleId>
}

TypeCoercibilityEvidence = {
    source: TypeId,
    target: TypeId,
    witness: ConversionWitness<Published>,
    rank: ConversionRank,
    environment: ConversionEnvironmentId
}

GenericSolutionAt<S: WitnessUseStage> = {
    specializations: CanonicalSpecializationSpine,
    witnessResolutions: WitnessResolutionSetAt<S>,
    residual: NodeList<Constraint>,
    trace: InferenceTraceId
}

GenericSolution = GenericSolutionAt<Published>
```

`TYP-EQ-001`: A non-recovery `TypeEqualityProof` is constructible only when normalizing both
endpoints under its recorded assumptions yields `canonical`. Every nested proof endpoint composes
according to its constructor. `RecoveryEquality` suppresses cascades but cannot discharge a
constraint in a successful exported specialization. Equality is therefore inspectable proof data,
not an unchecked assertion that two `TypeId` values happen to match.

`TYP-PACK-001`: `ConcretePackCountWitness(n)` is valid only when resolving `pack` yields exactly
`n` concrete elements and `count` is the canonical nonnegative-integer constant for `n`.
`DeclaredPackCountWitness(binder, slot)` is valid only when the canonical slot is
`PackCountEqual(pack, count)`. Registered and equality-derived witnesses validate every premise and
endpoint; they are not opaque assertions.

`TYP-PACK-002`: `ConcreteNonEmptyPackWitness(n)` requires the concrete pack to contain exactly
`n >= 1` elements. `DeclaredNonEmptyPackWitness(binder, slot)` requires the canonical slot to be
exactly `PackNonEmpty(pack)`. `PositiveCountPackWitness` references a count witness for the same
pack and a proof that its count is strictly positive. The `PositiveConstProof.rule` must resolve to
a registered proof constructor whose instantiated conclusion is exactly
`StrictlyGreaterThanZero(resolve(count).count)`. A
`RegisteredNonEmptyPackWitness(rule, inputs, premises)` is valid only when `rule` resolves to a
registered proof-constructor schema whose instantiated conclusion is exactly
`PackNonEmpty(pack)`, whose premise slots are in a canonical-order bijection with `premises`, and
whose instantiated premise at each slot equals the conclusion of the referenced witness. The
referenced witnesses are themselves valid and their dependency graph is finite and acyclic. Thus
an abstract nonempty pack is backed by a generic-context constraint or a replayable registered
derivation, not the same placeholder used for a known concrete pack.

`TYP-PACK-003`: First/last/trim and nonempty pack-branch rules consume a
`PackNonEmptyWitnessId` whose `pack` is their exact operand. Count/nonempty evidence is substituted,
serialized, and compared structurally; container length or a runtime bounds guard cannot replace
it.

A complete call solution has no residual constraints unless the output is explicitly a partially
applied generic value. Ordinary arguments and constraint evidence remain together in each
`SpecializationFrame` and are later passed to generic IR as needed. Composed substitution and
evidence maps are derived views, not a second stored authority. A solution's
`witnessResolutions` is the stage-correct minimal union for every interface-subtype witness in its
spine; consuming the solution copies that sidecar into the selected `BoundDeclUseAt<S>`. There is no
free-standing `SolutionQuality` scalar: completeness is determined by `residual`, and any
language-defined inference preference is a proof-bearing component of the enclosing overload rank.

## Declaration identity and use provenance

```text
CanonicalDeclRef = {
    declaration: DeclId,
    specializations: CanonicalSpecializationSpine
}

ResolvedDeclRefAt<S: WitnessUseStage> = {
    target: CanonicalDeclRef,
    witnessResolutions: WitnessResolutionSetAt<S>
}

ResolvedDeclRef = ResolvedDeclRefAt<Published>

BoundDeclUseAt<S: WitnessUseStage> = {
    target: CanonicalDeclRef,
    lookupPath: LookupPath,
    memberEvidence: Option<MemberAccessEvidence>,
    extensionUses:
        CanonicallyOrderedMap<ExtensionApplicabilityEvidenceId,
                              ExtensionFacetUseAt<S>>,
    accessDecision: AccessDecision,
    witnessResolutions: WitnessResolutionSetAt<S>,
    origin: Origin
}

BoundDeclUse = BoundDeclUseAt<Published>

SubstitutionChain = CanonicalSpecializationSpine
```

Frames correspond only to named generic binder roles needed to specialize the declaration and its
owners. Member lookup paths, opened-existential identities/evidence, access results, and source
origins are properties of `BoundDeclUse`; they cannot affect canonical declaration identity. A
decl-ref normalizes to a declaration plus alpha-normalized specialization frames, and clients do
not pattern-match on an implementation linked-list shape.

`specializationRequirements(declaration)` is the sole authority for its frame spine. It walks the
lexical owner chain outermost to innermost and emits each non-empty canonical binder in the declared
role order `LexicalBinder`, `TypeBinder`, `MemberOwnerBinder`, `CallableBinder`. A requirement is
identified by `(role, owner)`; the same pair cannot occur twice.

`TYP-DRF-001`: Resolving a canonical declaration reference applies ordinary arguments and keyed
constraint evidence to every referenced semantic fact and preserves requirement identity. A bound
use through `T : I` separately carries the lookup path and evidence that justify selecting members
of `I`.

`TYP-DRF-002`: Two uses with different spellings, import routes, or diagnostics paths may have the
same `CanonicalDeclRef`. Conversely, specializations with equal ordinary arguments but different
proof-relevant constraint evidence are not silently merged. Each constraint kind declares whether
its evidence is proof-irrelevant and, if so, its canonical erasure rule.

`TYP-DRF-003`: `CanonicalSpecializationSpine.outerToInner` is a duplicate-free bijection onto
`frames`, and equals the exact key sequence from `specializationRequirements(declaration)`. Every
map key equals its frame's `key`, and every frame's binder equals the alpha-normalized required
binder for that key. Missing, extra, reordered, or duplicate frames are invalid; `TYP-BND-002`
provides argument/evidence totality. Thus equivalent references have one serialized spine and frame
application always proceeds from the outermost owner to the referenced declaration.

`TYP-DRF-004`: A `ResolvedDeclRefAt<S>` or `BoundDeclUseAt<S>` resolution map has exactly the
canonical union of `requiredDefinitions` for every interface-subtype witness reachable from its
specialization spine, lookup path, member evidence, and referenced accessor selector. Map keys and
definition refs obey chapter 14's stage rule; unrelated definitions are forbidden. The map is a
dependency/materialization sidecar and never participates in `CanonicalDeclRef`, `LookupPathRole`,
`FacetKey`, overload identity, or mangling. Projecting a selected bound use to a callable preserves
this sidecar rather than reconstructing table revisions from an ambient snapshot.

`TYP-DRF-005`: `BoundDeclUseAt<S>.extensionUses` has exactly one entry for every distinct
`ExtensionApplicabilityEvidenceId` occurring in its retained lookup path and no other entry. Each
map key equals `use.applicability`. Chapter 14 validates the ordinary capability-use map against the
specialized extension and optional target requirements. The sidecar is use provenance, not lookup-
route identity: it is excluded from `CanonicalDeclRef`, `LookupPathRole`, and `FacetKey`, but every
projection/elaboration of the committed bound use preserves and aggregates it exactly once.

## Evidence and witnesses

Evidence is typed proof data. Representation adjustment, interface refinement, interface-subtype
witness values, existential opening, and conversion are distinct relations. Chapter 14 is the
schema and operational authority for `RepresentationAdjustmentPath` and
`InterfaceSubtypeWitnessId`:

```text
RepresentationAdjustmentPathId = ContentId<RepresentationAdjustmentPath>

InterfaceRefinementProof = {
    derived: InterfaceInstanceKey,
    base: InterfaceInstanceKey,
    path: NonEmpty<RefinementStepKey>
}

InterfaceRefinementProofId = ContentId<InterfaceRefinementProof>

ExtensionReachabilityStep =
    LexicalExtensionScope(from: ScopeId, to: ScopeId)
  | ImportedExtensionModule(step: ImportPathStep)
  | QualifiedExtensionScope(scope: ScopeId)

ExtensionReachabilityProof = {
    rootScope: ScopeId,
    extension: DeclId,
    environment: SemanticEnvironmentId,
    steps: NodeList<ExtensionReachabilityStep>
}

ExtensionIntrinsicApplicabilityEvidence = {
    extension: CanonicalDeclRef,
    queriedType: TypeId,
    matchedTarget: TypeId,
    targetEquality: TypeEqualityProofId,
    environment: SemanticEnvironmentId,
    reachability: ExtensionReachabilityProof
}

ExtensionIntrinsicApplicabilityEvidenceId =
    ContentId<ExtensionIntrinsicApplicabilityEvidence>

ExtensionApplicabilityEvidence = {
    intrinsic: ExtensionIntrinsicApplicabilityEvidenceId,
    region: BooleanCapabilityPredicate,
    concreteAvailability: ConcreteAvailabilitySelection
}

ExtensionApplicabilityEvidenceId = ContentId<ExtensionApplicabilityEvidence>

ExtensionFacetUseAt<S: WitnessUseStage> = {
    applicability: ExtensionApplicabilityEvidenceId,
    inferredCapabilityUses:
        CanonicallyOrderedMap<CapabilityUseId, CapabilityUse<S>>
}

ExistentialOpeningEvidence = {
    opening: OpenedTypeId,
    existential: TypeId,
    interface: InterfaceInstanceKey,
    witness: InterfaceSubtypeWitnessId
}

MemberAccessEvidence =
    IdentityMemberAccess
  | RepresentationBase(RepresentationAdjustmentPathId)
  | RefinedInterface(InterfaceSubtypeWitnessId)
  | ConformingInterface(InterfaceSubtypeWitnessId)
  | OpenedExistential(ExistentialOpeningEvidence)
  | ApplicableExtension(ExtensionApplicabilityEvidenceId)
  | ErrorMemberAccess(ErrorId)

ConversionWitness<S: WitnessUseStage> = {
    source: TypeId,
    target: TypeId,
    operation: ConversionOperation<S>,
    declaration: Option<CanonicalDeclRef>,
    nested: NodeList<ContentId<ConversionWitness<S>>>
}
```

Proof constructors state their premises, and a debug validator rechecks them. Error evidence
supports recovery but cannot discharge a user-written generic constraint in a successfully
published module interface. No constructor implicitly converts one evidence family into another;
chapter 7 names every permitted bridge.

`TYP-EVD-001`: Resolving a proof ID yields a payload whose canonical encoding exactly matches the
typed `ContentId`; recursive proof edges form a finite DAG. `TypeEqualityProofId`,
`RepresentationAdjustmentPathId`, `InterfaceRefinementProofId`, and
`InterfaceSubtypeWitnessId` cannot resolve to another evidence family, and all premise endpoints
compose with the parent constructor. Digest equality alone never selects proof payloads.

`TYP-EVD-002`: The extension in an `ExtensionIntrinsicApplicabilityEvidence` is fully specialized,
so its canonical frames are the sole ordinary-argument and constraint-evidence authority. Applying
those frames to the extension target yields `matchedTarget`; `targetEquality` proves it equal to
`queriedType`, and `reachability` ends at that extension in `environment`. A validator replays
these projections, so member access cannot cite an extension that merely shares a name or target
spelling. Intrinsic evidence is independent of the current capability region and does not claim
that the extension is selectable there.

`TYP-EVD-003`: Representation-adjustment paths are ordered, contiguous operational step lists.
Only class representation bases and registered standard-representation rules may contribute a
step; concrete struct bases, interface conformances, and interface refinements cannot. Applying an
`InterfaceRefinementProof.path` to an interface witness folds one exact
`LookupSubtypeWitness(previous, RefinementWitnessEntry(step))` per step. There is no binary
`TransitiveSubtypeWitness` or generic transitive representation-proof constructor.

`TYP-EVD-004`: For intrinsic extension applicability, the resolved `extension.declaration` owns a
checked target pattern. Applying the canonical specialization spine to that pattern must equal
`matchedTarget`; `targetEquality` has endpoints `matchedTarget` and `queriedType` in either order.
The reachability proof has the same environment, its root is the lookup request's starting scope,
and its endpoint is `extension.declaration`. Its closed step algebra permits only lexical, import,
and qualified-scope traversal; it cannot contain a facet, member evidence, or extension-
applicability ID and therefore cannot recursively contain itself.

The context-dependent `ExtensionApplicabilityEvidence` resolves its intrinsic evidence and stores
the exact lookup region plus only the extension/target concrete-availability selection.
`NoConcreteAvailability` occurs exactly when both specialized source sets are absent; otherwise
the proven source list is their canonical union, its combined requirement is recomputed from that
union, and its proof has the stored region/requirement endpoints. It intentionally contains no caller-owned
`CapabilityUseKey`, so the same extension facet in the same region has stable route identity across
member-use origins. When a member candidate is committed, its `BoundDeclUseAt<S>.extensionUses`
contains one `ExtensionFacetUseAt<S>` for every extension applicability ID in the lookup path. Each
sidecar supplies the exact `ExtensionCapabilityUseInputsAt<S>` map: the extension use plus the
target use exactly when that target contributes one, at that committed use site.
Mixing an intrinsic target/reachability proof, region, concrete proof, or use sidecar from another
extension, specialization, or semantic environment is invalid.

## Interfaces, conformances, and evidence graphs

Chapter 8 is the sole schema authority for `ConformanceIdentity`, `ConformanceDefinitionRevision`,
`ValidatedConformanceRef`, `ConformanceDefinition`, `RequirementEvidenceMap`, and the kind-indexed
`GuardedSatisfaction<K>`/`RequirementSatisfaction<K>` families. An allocated `ConformanceId` may
name a draft identity and participate in an atomic recursive build. A
`ValidatedConformanceRef(identity, revision)` resolves one frozen definition and is a dependency
stamp, not itself a subtype proof. Positive evidence is an `InterfaceSubtypeWitnessId` together
with the stage-appropriate resolution set when its operation reads table definitions. This admits
generic, specialized, bound, lookup, and existential witnesses without inventing definition
references for abstract proof values.

`WIT-MAP-001`: A requirement map is keyed by canonical `RequirementKey`, including the viewed and
declaring interface specializations and refinement path. Interface source order is presentation
metadata only. Path-distinct diamond occurrences remain addressable; sharing requires explicit
typed reuse evidence, never map insertion order.

`WIT-MAP-002`: For every active condition, a conformance is complete only when each required
requirement has exactly one kind-correct satisfaction. Conditional alternatives form a canonical,
disjoint partition of the conformance's availability domain. Defaults and synthesized adapters
appear as ordinary keyed satisfactions with provenance.

`WIT-GRAPH-001`: Conformances and their requirement satisfactions form a graph, not a tree or DAG.
`ConformanceIdentity` may be published before `ConformanceDefinition`; an atomic definition SCC may
preallocate its revision endpoints. A complete definition is published atomically, and every
published proof consumer stores a stable witness value; table-backed operations additionally carry
exact `ValidatedConformanceRef` resolutions. Clients never observe a mutable, partially filled map
or use a raw identity as proof. A construction-stage conversion, generated body, or requirement map
may carry a scope-authorized operational definition resolution through
`WitnessCallRef<Construction>`, but it cannot escape that construction. Atomic freeze replaces the
resolution with the validated reference for the same identity without changing the witness ID.

The current `RequirementDictionary` is already keyed by requirement `Decl*`, which is the right
conceptual direction, but `RequirementWitness` is a mutable tagged union that may contain a decl-ref,
`Val`, or nested `WitnessTable`. The new domain gives each role a typed immutable alternative and a
stable, specialization-aware requirement identity.

## Facets

A facet is a member-providing view reached through an explicit operational route. Chapter 14 is the
authority for route folding and partial priority:

```text
Facet = {
    id: FacetId,
    owner: TypeId,
    origin: FacetOrigin,
    kind: FacetKind,
    route: FacetRouteKey,
    memberScope: ScopeId,
    evidence: Option<MemberAccessEvidence>,
    witnessResolutions: WitnessResolutionStamp,
    conditions: GenericConditionSet
}

FacetOrigin = TypeOrigin(TypeId, CanonicalDeclRef) | ExtensionOrigin(CanonicalDeclRef)

FacetId = ContentId<FacetKey>
FacetSet = {
    byKey: CanonicallyOrderedMap<FacetKey, Facet>,
    equivalence:
        CanonicallyOrderedSet<(left: FacetKey,
                               right: FacetKey,
                               proof: FacetEquivalenceProof)>,
    priority:
        CanonicallyOrderedSet<(preferred: FacetKey,
                               shadowed: FacetKey,
                               proof: FacetPriorityProof)>,
    presentationOrder: NodeList<FacetKey>
}
```

Distance and provider class are derived from `route`. Semantic priority is a proof-carrying partial
order; `presentationOrder` exists only for deterministic serialization and diagnostics. Uniqueness
is by the complete semantic `FacetKey`, not object address or endpoint type.

`TYP-FAC-000`: `Facet.id = ContentId(keyOf(facet))`, where `keyOf` is the exact projection shown
above. `memberScope` and relation-specific evidence are derived facts: two producers that reach the
same key must prove those facts equivalent or report a facet-construction conflict; they cannot
keep whichever entry was inserted first.

`TYP-FAC-003`: `presentationOrder` is a duplicate-free bijection onto `byKey` keys. Every
equivalence tuple stores its endpoints in canonical order, names two present keys, and contains a
validator-replayable proof for exactly those endpoints; the reflexive, symmetric, transitive
closure is the sole authority used to quotient facets. Every priority edge names two present
equivalence classes and a proof whose facet endpoints match them; the quotient edge graph is
acyclic. Maximal incomparable facets remain simultaneously visible and may produce ambiguity.
Canonical map/source/import iteration never defines semantic lookup order.

`TYP-FAC-001`: Facet closure is computed separately from the class representation chain, interface
conformances/refinements, existential openings, and applicable extensions. Every route step carries
the correctly typed representation adjustment, interface-subtype witness/lookup key,
existential-opening, or extension-applicability evidence used to reach it. Folding the route must
reproduce the facet evidence exactly. `witnessResolutions` is the minimal canonical union required
by witness IDs in the route/evidence and is excluded from `FacetKey`; a selected candidate copies
that sidecar into its `BoundDeclUseAt<S>`.

`TYP-FAC-002`: A facet skipped because one dependency is incomplete makes the facet-construction
query return chapter 10's `QueryStep::Blocked` with that dependency, not a semantic facet result or
a silently shortened inheritance list.

Path-distinct diamond routes therefore have different keys even when they end at the same provider.
This replaces the current mutable linked-list/cache state and totalized inheritance ordering with
an immutable route-keyed set and explicit partial priority.

## Conversion and overload domains

```text
ConversionResult<S: WitnessUseStage> =
    Applicable(plan: ConversionPlan<S>, rank: ConversionRank)
  | Inapplicable(reason: ConversionFailure<S>)
  | Recovered(plan: ConversionPlan<S>, error: ErrorId)

ConversionPlan<S: WitnessUseStage> = {
    source: TypeId,
    target: TypeId,
    operation: ConversionOperation<S>,
    evidence: Option<ConversionWitness<S>>,
    semanticUses: PlanSemanticUses<S>,
    origin: Origin
}

PlanSemanticUses<S: WitnessUseStage> = {
    effects: CanonicallyOrderedMap<EffectUseId, EffectUse<S>>,
    capabilities: CapabilitySelectionAt<S>
}

BoundCallSlot = ReceiverSlotRole | ParameterSlotRole(ParameterKey)

CallSlotInputRole = ComparedCallSource(SourceCallRole)
                  | DefaultedCallSource(ParameterKey)

ApplicableCallSlotPlan<S: WitnessUseStage> = {
    source: CallSlotInputRole,
    accessEnvironment: AccessEnvironmentId,
    access: AccessPlan<S>
}

CallAliasAccessKind =
    SharedPhysicalRead(access: AccessMode)
  | ExclusiveAbstractAccess(access: AccessMode)
  | AliasablePhysicalAccess(access: AccessMode,
                            rule: StandardEnvironmentRuleId)

CallAliasClaim = {
    slot: BoundCallSlot,
    provenance: AliasProvenance,
    access: CallAliasAccessKind,
    lifetime: LifetimeId
}

AliasPairCompatibilityProof =
    DisjointAliasPair(proof: AliasDisjointnessProof)
  | OverlappingPhysicalReadPair(left: BoundCallSlot, right: BoundCallSlot)
  | OverlappingVersionedPhysicalAccesses(
        left: BoundCallSlot,
        right: BoundCallSlot,
        rules: NonEmpty<CanonicallyOrderedSet<StandardEnvironmentRuleId>>)

CompatibleCallAliasClaims = {
    comparisons: NodeList<AliasPairCompatibilityProof>
}

ConflictingCallAliasClaims = {
    left: CallAliasClaim,
    right: CallAliasClaim,
    overlap: AliasOverlapReason,
    reason: ExclusiveAccessOverlap |
            PhysicalAccessRuleRejected(
                rules: NonEmpty<CanonicallyOrderedSet<
                    StandardEnvironmentRuleId>>) |
            IncompatibleReferenceDisciplines
}

CallAliasCheck =
    CompatibleAliasClaims(CompatibleCallAliasClaims)
  | ConflictingAliasClaims(conflict: ConflictingCallAliasClaims)

PreInferenceCallableContract = {
    signature: CallableSignatureId,
    semanticEnvironment: SemanticEnvironmentId,
    selectionEffects: EffectSet,
    inferredCapabilities: CapabilityRequirement,
    concreteAvailability: Option<ConcreteAvailabilitySet>
}

ApplicableOverloadCandidate = {
    use: BoundDeclUse,
    signature: CallableSignature,
    resultAuthority: CallableResultAuthorityId,
    selectionContract: PreInferenceCallableContract,
    conversionEnvironment: ConversionEnvironmentId,
    accessEnvironment: AccessEnvironmentId,
    genericTrace: InferenceTraceId,
    argumentMap: ArgumentMap,
    callSlots: NodeMap<BoundCallSlot, ApplicableCallSlotPlan<Published>>,
    aliasCompatibility: CompatibleCallAliasClaims,
    effectUse: EffectUse<Published>,
    capabilitySelection: CapabilitySelectionAt<Published>,
    resultType: TypeId,
    trace: CandidateTraceId
}

RecoveredApplicableCandidate = {
    use: Option<BoundDeclUse>,
    signature: Option<CallableSignature>,
    argumentMap: RecoveryArgumentMap,
    accessPlans: NodeMap<BoundCallSlot, AccessPlan<Published>>,
    resultType: TypeId,
    trace: CandidateTraceId
}

OverloadCandidateResult =
    Applicable(ApplicableOverloadCandidate)
  | Rejected {
        candidate: LookupCandidate,
        stage: CandidateFailureStage,
        failure: CandidateFailure,
        trace: CandidateTraceId,
        diagnostics: DiagnosticSelection
    }
  | Recovered {
        candidate: LookupCandidate,
        call: RecoveredApplicableCandidate,
        errors: NonEmpty<ErrorId>
    }

OverloadResult =
    Selected {
        winner: ApplicableOverloadCandidate,
        comparisons: NodeList<CandidateComparisonProof>,
        considered: NodeList<OverloadCandidateResult>
    }
  | NoApplicable {
        considered: NonEmpty<OverloadCandidateResult>,
        failureReport: OverloadFailureReport
    }
  | Ambiguous {
        maximal: NonEmpty<ApplicableOverloadCandidate>,
        incomparability: NodeList<CandidateComparisonProof>
    }
  | RecoveredCall {
        call: RecoveredApplicableCandidate,
        considered: NodeList<OverloadCandidateResult>,
        errors: NonEmpty<ErrorId>
}
```

Unqualified `ConversionResult`, `ConversionPlan`, `ConversionWitness`, `ApplicableCallSlotPlan`, and
`PlanSemanticUses` mean their `<Published>` forms. Construction-only forms are confined to the
synthesis transaction and are rewritten together with their operational witness edges.

There is no "committed candidate" reconstruction step: `Selected.winner` contains every plan and
piece of evidence needed to construct the typed call. Failures are structured data so diagnostics
and tests need not scrape text. Candidate ranking is the partial order defined in chapter 7; it does
not depend on container iteration order.

`ApplicableOverloadCandidate.use.target` is the sole stored owner of the selected declaration's
complete specialization frames. Freezing consumes the intermediate `GenericSolution` to construct
that canonical reference; the candidate retains only its trace ID. Signature, argument map, and
plans are validated projections of that specialized target, not competing specialization maps.

`TYP-OVL-001`: `ApplicableOverloadCandidate.callSlots` has exactly one entry for the receiver when
present and for every parameter bound by `argumentMap`, with no other slots. Each entry's `source`
is `ComparedCallSource(callSlotSourceRole(binding).value)` for the exact receiver/explicit argument
expansion mapped to that slot, or
`DefaultedCallSource(k)` exactly when slot `k` has a default binding. Defaulted sources participate
in default/specificity ranking but not pointwise source-conversion comparison. Every
`access.terminal` is `PassArgument`; a standalone storage terminal cannot inhabit a call slot.
`access.rankingConversion = Some(rankingConversion)`. Chapter 7 derives the slot's sole
`SourceAdaptationRank` from that value. `ConvertedAccess` selects the conversion operation used both
for pairwise ranking and eventual elaboration as required by `ELB-ACC-003` and records exactly
`conversionEnvironment`; `ConsumedWithoutAccessConversion(rule)` names the exact candidate-passing
rule that consumes no conversion, including physical-storage identity. A candidate contains no
parallel conversion, rank, or access-plan map. Every entry's `accessEnvironment` is exactly the
candidate's `accessEnvironment`; all invocation-lifetime, access-context, world-assumption, and
origin facts used to validate a slot are obtained by resolving that one ID. Neither a slot nor the
candidate stores a parallel invocation lifetime.

`TYP-OVL-002`: `ApplicableOverloadCandidate.capabilitySelection.region` equals the exact boolean
assumption in the candidate's access/conversion context. Its ordinary-use map contains the one
selected callable use plus the canonical union of extension-facet sidecars on `use`; its concrete
source list is the canonical union of `selectionContract.concreteAvailability` and every extension
applicability evidence on `use`, and has the endpoints required by `CAP-SEL-003`. Each
conversion/access plan separately preserves its complete
`PlanSemanticUses.capabilities`; committing the call merges those selections with the direct
candidate selection under `CAP-SEL-004`. Reconstructing concrete sources from the winner's formula,
or retaining a proof while dropping its source list, is invalid.

## Visibility and capabilities

Chapter 9 is the sole schema authority for the `Visibility` alternatives, their declaration-level
order, and the separate contextual access predicate. Composite exposure uses that order:

```text
effectiveVisibility(composite) = meet of referenced declaration visibilities
```

Capability formulas are positive formulas in disjunctive normal form, represented canonically as a
set of conjunction clauses. Atom implication and incompatibility come from the versioned standard
environment. Their full algebra is defined in chapter 9.

## Semantic validation

Every domain has a generated validator. At minimum it checks:

- IDs resolve in the declared snapshot/environment;
- maps use canonical keys and ordering;
- declaration headers resolve every concrete-availability ID through its declared producer;
- capability selections preserve exact ordinary-use maps, concrete sources, combined requirements,
  and region-proof endpoints;
- substitutions bind parameters in scope and arguments of the right kind;
- function receiver and parameter modes use one of the five well-formed domain/access combinations,
  and function-type equality and hashing include both structural axes and every physical-location
  field;
- every callable header's result authority has the exact declaration/registered anchor and
  signature, while non-callable headers have none;
- parameter/storage address-space and source requirements are well formed and every admission proof
  replays; a formal symbolic address space names an exact physical-formal entry proof and is never
  replaced by an invented concrete address space, while every first-class reference handle from
  such storage carries a valid concrete-address-space projection proof;
- reference-accessor maps have exact `ReadAccess`/`ReadWriteAccess` keys, result contracts resolve
  their exact selector/signature/access, and all five provenance derivations are closed;
- registered physical projection applications retain the exact runtime-role domain/order and their
  intrinsic result proof replays every storage component without a use-specific requirement;
- ConstRef and Ref formal roots are physical, use the declared access view and activation lifetime,
  and retain exact address/source entry evidence through lowering;
- alias-region joins, overlap results, unique-alias proofs, and successful call-pair comparisons
  replay from their exact canonical roots and versioned access rules; a conflicting call pair stores
  a `MayOverlap` reason and cannot contain disjointness evidence;
- every call-slot source agrees with its typed binding and argument map, an accessor-produced
  physical source's operation site validates against that exact source node, and its sole adaptation
  rank is derived from `AccessPlan.rankingConversion` rather than stored in parallel;
- proof endpoints match their stored `sub`, `sup`, `source`, and `target`;
- extension facet routes retain context-dependent concrete applicability while bound-use sidecars
  retain exact caller-owned ordinary uses;
- witness-map keys belong to the interface and have the right satisfaction kind; and
- no successful published fact contains an `ErrorId`, unresolved overload set, or residual generic
  constraint unless its public type explicitly permits one.
