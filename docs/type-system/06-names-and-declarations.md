# Names, declarations, lookup, and facets

This chapter defines declaration identity, scope construction, lookup, redeclaration, imports, and
extension/base member discovery. Visibility classification and access permission are defined in
chapter 10; lookup retains inaccessible candidates so diagnostics can distinguish “not found” from
“found but inaccessible.”

## Declaration outlines, scope wiring, and checked headers

Declaration parsing first publishes the hierarchy and syntax-only identity facts needed by later
parsing. Expression, statement, initializer, and body regions that the declaration grammar does not
interpret remain `UnparsedContent`. Scope wiring is a separate immutable product over those
outlines; it is not a rewritten AST whose nodes have all advanced to a common checking state:

```text
ParseDecls(CSTSnapshot<MacroExpanded>, DeclGrammar,
           GrammarVocabulary, DeclParserOptions)
    -> CheckResult<DeclParseResult>

ResolveImportOutlines(DeclParseResult, ModuleId,
                      ModuleResolutionProvider, ModuleResolutionRevision,
                      LanguageRuleSetId)
    -> QueryStep<ImportResolutionIndex>

WireLookupScopes(DeclParseResult, ImportResolutionIndex,
                 ScopeWiringEnvironment)
    -> QueryStep<ScopeWiring>

ScopeWiringEnvironment = {
    module: ModuleId,
    implementingDocuments: CanonicallyOrderedSet<SourceFileId>,
    languageRules: LanguageRuleSetId
}

RedeclarationGroup = {
    declaration: DeclId,
    key: RedeclarationKey,
    fragments: NonEmpty<DeclFragmentId>,
    presentationOrder: NodeList<DeclFragmentId>
}

RedeclarationSeed = {
    scope: ScopeId,
    name: NameKey,
    kind: DeclKind
}

RedeclarationPartition = {
    seed: RedeclarationSeed,
    groups: NodeMap<DeclId, RedeclarationGroup>,
    fragmentToDecl: NodeMap<DeclFragmentId, DeclId>
}

BuildRedeclarationKey(DeclFragmentId, ScopeWiringId, SemanticEnvironmentId)
    -> QueryStep<RedeclarationKey>

GroupRedeclarations(RedeclarationSeed, ScopeWiringId, SemanticEnvironmentId)
    -> QueryStep<RedeclarationPartition>

ResolveLogicalDecl(DeclFragmentId, ScopeWiringId, SemanticEnvironmentId)
    -> QueryStep<DeclId>

BindDeclHeader(DeclId, ParsedContent<DeclCSTCategory>,
               ScopeWiringId, SemanticEnvironmentId)
    -> QueryStep<DeclHeader>
```

`DEC-ID-001`: Chapter 5's `DeclFragmentId` is the collision-safe content identity anchored by a
`ParserDeclStub.outline`, its `binding` ordinal, and its declared kind; it identifies exactly one
source occurrence, including one declarator within a `DeclGroup`. A
`DeclId` identifies the logical entity formed from one or more compatible fragments. The two IDs
are never interchangeable, and a declaration map key must equal its stub's `fragment` field.

`DEC-ID-002`: `WireLookupScopes` uses only declaration-outline facts. In particular it does not
check a parameter type, build a `GenericBinder`, compare overload signatures, or assign a logical `DeclId`.
`BuildRedeclarationKey`, `GroupRedeclarations`, and `ResolveLogicalDecl` are ordinary scheduler
queries. They may use private provisional entity handles while solving an identity/definition
component, but publish only stable `DeclId` values and complete immutable partitions. Neither ID
depends on task execution order, and no consumer observes a fragment-local ID as nominal semantic
identity.

`DEC-ID-003`: `Scope.lexicalMembers` and `Scope.bindingPoints` in a `ScopeWiring` remain keyed by
`DeclFragmentId`. There is no bulk operation that rewrites every scope to logical declaration IDs.
Lookup collects eligible outline fragments, requests `ResolveLogicalDecl` for the candidates it
actually needs, and deduplicates equal logical declarations only after those results are available.
The resulting `BoundDeclUse` retains the selected fragment origin and lookup path. If several
fragments in one scope resolve to the same entity, its effective binding point for that lookup is
their earliest eligible point; reopened physical scopes retain their own positions.

`DEC-ID-004`: `ScopeWiring.contentEntryPositions` has exactly one entry for each
`UnparsedContent` region whose fine parser may perform lookup. The entry is the lexical
`ScopePosition` at the start of that region. Fine parsing receives this position explicitly and may
publish additional immutable local-scope wiring as it encounters source-ordered local declarations;
it never mutates the outline wiring or consults an ambient parser scope.

`DEC-HDR-001`: Publishing a `ParserDeclStub` makes only its outline identity, declared name,
declaration kind, declaring/member scopes, syntactic `DirectGenericMarker`, and origin observable.
A client needing its parameter sorts, type, bases, constraints, visibility, or modifiers must
request the corresponding fact query. Direct-generic presence is not a semantic parameter sort;
header checking replaces the opaque clause with chapter 5's `GenericParameterSort` values.

`DEC-HDR-002`: `BindDeclHeader` requests chapter 5's `GetGenericBinder` query and stores only the
resulting stable `GenericBinderId` in `DeclHeader`. The binder's `owner` equals the header
declaration, and redeclaration compatibility uses the alpha-normalized `GenericBinderShape`, never
an embedded binder copy, a snapshot-local table index, or declaration-outline arity as a semantic
parameter sort.

`DEC-HDR-003`: `BindDeclHeader` obtains `DeclHeader.concreteAvailability` only from chapter 10's
`ComputeConcreteAvailability(declaration, modifiers, environment)` product. A successful `Some`
stores that product's exact `ConcreteAvailabilityId`; `None` remains semantically distinct from an
explicit true availability. Header binding never copies `declaredCapabilities`, requests a body or
inferred contract, or guesses availability from a target/stage modifier not admitted by the
versioned availability producer.

`DEC-HDR-004`: The declaration-kind registry classifies extensions as capability-bearing containers.
`BindDeclHeader` therefore produces their ordinary `DeclaredCapabilityRequirementsId` even though an
extension has no independent callable body. Specializing an extension projects that declared
requirement directly into `ExtensionCapabilityUseInputsAt<S>.extension`; it never runs callable
body inference and never substitutes the extension's `concreteAvailability` for the ordinary use.

`DEC-HDR-005`: `BindDeclHeader` constructs `callableSignature` and
`callableResultAuthority` atomically. Every callable header has exactly one authority anchored to
that declaration and canonical signature; every non-callable header has neither field. Ordinary,
fixed-reference, ref-accessor, and registered-reference surfaces select their closed authority
alternative from the checked declaration or registered standard-environment definition, never
from a body return or use-site expectation. For a ref accessor, the authority kind is exactly
`AccessorPointerLikeCallableResult(AbstractStorageRefAccessor.resultContract)`. Redeclarations must
agree on the entire authority after alpha-normalization. Resolving a specialized header performs
the signature-and-authority substitution in `TYP-FUN-011`; it cannot reuse an equal-signature
authority anchored to another declaration.

This permits mutually recursive functions and nominal types without publishing partially filled
mutable declarations or giving two compatible redeclarations different permanent identities.

## Scope wiring and positions

Scopes in `ScopeWiring` carry the explicit `ScopePolicy` and position schema defined in chapter 5. A
`ScopePosition(scope, ordinal)` is a boundary in the deterministic source-order traversal of that
scope's declaration outlines and already fine-parsed local syntax. Ordinal zero is scope entry;
`endPosition` is one past every published position and is the entry boundary for a body nested
immediately after a binder. Every direct member's binding point names the containing scope and is at
or before `endPosition`. `ScopeWiring.contentEntryPositions` contains exactly the deferred regions
visible to that wiring, and every value names its innermost lexical scope at the region's start.
Positions are snapshot-local lookup inputs, not declaration identity. `bindingPoints` contains
exactly the distinct direct fragment identities occurring in `lexicalMembers`.

`parent` and `parentEntry` are both absent for a root and both present for a child;
`parentEntry.scope = parent`. When lookup walks from a child to its parent, it replaces the child's
use position with `parentEntry`. This preserves the lexical point at which the nested scope occurs:
a nested block cannot see declarations written after it, while a function body entered at the end
of its parameter binder sees every parameter.

- module, file-aggregation, namespace, aggregate-type, and interface member scopes use
  `UnorderedMembers`: all direct `ParserDeclStub` values are installed before headers are checked;
- function and block scopes use `SourceOrderedMembers`: a local declaration is visible only after
  the point established by its declaration rule; and
- generic parameter and parameter lists use `SequentialBinder`: a parameter may refer to earlier
  parameters, not later siblings, while the declaration body sees all parameters.

An `UnorderedMembers` scope assigns every direct member the entry binding point
`ScopePosition(S, 0)`. `SourceOrderedMembers` and `SequentialBinder` scopes assign the exact point
selected by the declaration or binder rule; they do not infer visibility from map iteration.

```text
scopePolicy(S) = UnorderedMembers    declaredIn(d,S)
---------------------------------------------------- NAM-SCP-001
d ∈ visibleLocalFragments(S, anyPosition)

scopePolicy(S) = SourceOrderedMembers    bindingPoint(S,d) ≤ usePosition
--------------------------------------------------------------------- NAM-SCP-002
d ∈ visibleLocalFragments(S, usePosition)

scopePolicy(S) = SequentialBinder    bindingPoint(S,d) ≤ usePosition
------------------------------------------------------------------- NAM-SCP-003
d ∈ visibleLocalFragments(S, usePosition)

parent(C) = S    parentEntry(C) = p
------------------------------------ NAM-SCP-004
positionInParent(C, anyPosition) = p
```

`NAM-SCP-005`: Scope wiring validates all position bounds, the exact node/member key coverage,
strict source-order traversal of node ordinals, the root/child `parentEntry` invariant, and the
policy-specific binding-point rules above. Resolving a fragment to a logical declaration cannot
move its binding point earlier to repair a lookup failure.

The exact binding point is declaration-specific: a variable is not visible in its own type or
initializer unless a named recursion rule says otherwise; a function declaration in a local scope
may become visible at the end of its signature so its body can recurse.

For a `SequentialBinder` with parameters `p_0 ... p_n` in written order, position assignment and
binding-point construction satisfy
`bindingPoint(p_i) < bindingPoint(p_j)` whenever `i < j`. Every node in `p_i`'s type, constraints,
and default that is checked before the parameter is bound has a position less than
`bindingPoint(p_i)`. Consequently those nodes may see precisely the earlier parameters whose
binding points they have passed, never `p_i` itself or a later sibling. The immediately nested
declaration body has `parentEntry = endPosition`, and every parameter binding point is at or before
that boundary, so `NAM-SCP-003/004` make all parameters visible in the body. A language rule that
permits self-reference in a particular binder must assign an earlier binding point explicitly; it
cannot bypass the position relation.

`NamespaceId = DeclId` for the logical namespace declaration. Reopened namespace declarations
contribute member maps to that one logical `NamespaceId`. Each physical
namespace body remains a distinct declaration-outline node and provenance source.

## Module graph

```text
ModuleGraph = {
    modules: NodeMap<ModuleId, ModuleInterface>,
    imports: NodeList<ImportEdge>,
    sourceFiles: NodeMap<ModuleId, NodeList<SourceFileId>>,
    augmentations: NodeList<ImplementingEdge>
}

ImportEdge = {
    from: ModuleId,
    to: ModuleId,
    exported: Bool,
    origin: Origin
}
```

Every `roots`, `declarationOrder`, `fragments`, and `presentationOrder` list is duplicate-free.
Each order list is a bijection onto the corresponding map/key set and is sorted by stable physical
source order. `DeclFragmentId` is the final tie-breaker for outline/wiring order, while `DeclId` is
the final tie-breaker only after a redeclaration partition exists. Wiring or grouping rejects
disagreeing entries for the same scope, fragment, or declaration key; it never resolves them by
task completion order.
`RedeclarationGroup.fragments` is canonically ordered for identity, while `presentationOrder`
retains source order for diagnostics.

`import` and `__import` add module-interface edges. `__exported import` additionally makes the edge
part of the importing module's public reachability closure. `__include` and preprocessor `#include`
retain separate syntax/source roots and explicit inclusion edges; any compatibility semantics that
combine declarations are a module-assembly operation, not physical token concatenation.

`implementing` associates a file with a named module augmentation. All files participating in the
same module revision are known before its unordered top-level `ScopeWiring` is published.

`NAM-MOD-001`: Import reachability is graph reachability through the direct import followed by zero
or more exported-import edges. Private source-file membership does not create cross-module access.

`NAM-MOD-002`: Import cycles are legal at the identity/interface layer only when each module
interface can be built without a definition-level cycle. A cycle requiring an unavailable exported
signature is diagnosed by the scheduler with module-edge roles.

## Unqualified lookup

```text
LookupName(wiring: ScopeWiringId, scope: ScopeId, position: ScopePosition,
           name, mask, environment)
    -> QueryStep<LookupResult>
```

The input position must name `scope`. On each outward lexical step, lookup applies `NAM-SCP-004`
before consulting the parent scope's policy.

For each scope from inner to outer:

1. collect eligible direct `DeclFragmentId` members under the scope's ordering policy;
2. request `ResolveLogicalDecl` for precisely those fragments;
3. deduplicate fragments that resolve to the same logical declaration at the same lookup role;
4. collect eligible transparent-member contributions;
5. apply the lookup mask and declaration-class filter;
6. attach import/namespace paths and provisional access decisions;
7. if the scope contains any non-overloadable eligible declaration, stop;
8. if it contains only overloadable declarations, retain them and continue only as the language's
   overload-accumulation rule allows; and
9. proceed to the lexical parent.

```text
local = candidates(S, p, n, mask)
hasNonOverloadable(local)
------------------------------------------------ NAM-LKP-001
lookup(S,p,n,mask) = local
```

If `local` is empty, lookup continues outward. If all local candidates are overloadable, the result
is the stable concatenation of the local overload set and permitted outer overload sets. The stable
order is scope distance, declaration source order, then stable `DeclId`; order is diagnostic and
tie-break metadata, not a substitute for semantic ranking.

`NAM-LKP-002`: Candidate deduplication uses normalized `(DeclRef, LookupPathRole)`.
Discovering the same declaration through semantically distinct base/witness paths retains distinct
paths until the ambiguity/identity rule proves them equivalent.

`NAM-LKP-003`: A completion query may request inaccessible or recovery candidates, but an ordinary
lookup query returns their `VisibilityDecision` and cannot silently treat them as accessible.

## Qualified and member lookup

Qualified lookup first classifies the base:

```text
LookupMember(baseClassifier, name, environment) -> LookupResult
```

- a namespace/module base queries its logical member scope;
- a nominal/type-parameter/self base queries its ordered facet set;
- an existential base opens the existential and queries interface facets with the opening evidence;
- a value base queries the facets of its value type and prefixes each path with the appropriate
  receiver/storage edge; and
- pointer/reference bases may add an explicit dereference path only under a declared lookup rule.

Every member candidate's `LookupPath` records operations required to elaborate access:

```text
LookupPathEdge =
    LexicalParent(from: ScopeId, to: ScopeId)
  | ImportedModule(ImportPathStep)
  | QualifiedScope(ScopeId)
  | MemberBase(AnyNodeId)
  | ImplicitReceiver(ParamPassingMode)
  | Dereference(TypeId)
  | FacetRoute(facet: FacetId,
               route: FacetRouteKey,
               evidence: MemberVisibilityEvidence)
  | TransparentMember(DeclId)
  | OpenExistential(OpenedTypeId, SubtypeWitnessId)

LookupPath = {
    edges: NodeList<LookupPathEdge>
}

LookupPathRoleEdge =
    LexicalParentRole(from: ScopeId, to: ScopeId)
  | ImportedModuleRole(ImportPathStep)
  | QualifiedScopeRole(ScopeId)
  | MemberBaseRole
  | ImplicitReceiverRole(ParamPassingMode)
  | DereferenceRole(TypeId)
  | FacetRouteRole(FacetKey)
  | TransparentMemberRole(DeclId)
  | OpenExistentialRole(OpenedTypeId, SubtypeWitnessId)

LookupPathRole = {
    edges: NodeList<LookupPathRoleEdge>
}
```

`roleOf(path)` preserves lexical/import/qualification steps, drops only the particular
`MemberBase` node identity, resolves each `FacetId` to its collision-safe `FacetKey`, and projects
each witness to its stable `SubtypeWitnessId`. Thus two paths deduplicate only when they
perform the same semantic lookup/elaboration roles; provenance and definition revisions remain
available in the retained `BoundDeclUseAt<S>.witnessResolutions` sidecar, while caller-owned
extension ordinary uses remain in `extensionUses`; neither sidecar manufactures an overload. A
`LookupPath` is never lowered as a proof in isolation: committing the selected use packages it
with those sidecars, including the definitions required by its facet and existential edges.

`NAM-PTH-001`: A `LookupPath` is contiguous: lexical and import endpoints connect, facet and
existential edges are applicable to the type produced by the preceding edge, and at most one
`MemberBase` begins a value-member path. Path validation occurs before a candidate enters a
`LookupResult`; elaboration consumes the stored edges without rediscovering them.

`NAM-MEM-001`: Lookup does not synthesize `MemberExpr`, dereference, cast, or receiver nodes. The
fine-grained checking query or elaboration interprets the selected path once a candidate is chosen.

`NAM-MEM-002`: Member lookup through a constrained type parameter carries the conformance or
interface-refinement evidence that made the interface facet available. Nominal base lookup carries
representation-adjustment evidence instead. Later checking cannot reconstruct any of them from a
parameter declaration by position.

## Contextual words and syntax ambiguities

A word used as fixed grammar syntax is resolved by `GrammarVocabulary`, not ordinary semantic name
lookup. Fine parsing classifies a name at the exact scope position supplied by `ScopeWiring`:

```text
ClassifySyntacticName(wiring: ScopeWiringId, scope, position, name)
    -> QueryStep<TypeName | ValueName | NamespaceName | SyntaxAlias | Unknown | Ambiguous>

ClassifyGenericApplicationHead(head, position, wiring, expressionContext)
    -> QueryStep<GenericHeadClassification>
```

For an unqualified identifier these queries read `ParserDeclStub` records and an explicit
compatibility syntax environment. They do not build a semantic `GenericBinder`, type-check an
expression, or force a declaration definition. A qualified/member head may explicitly request its
base expression's checked classifier; that dependency is part of the fine-grained query graph.

`NAM-AMB-000`: When the next balanced token sequence begins with `<`, fine parsing selects generic
application when `ClassifyGenericApplicationHead` returns `GenericHead`, meaning at least one visible
candidate has a direct generic declaration outline. Any non-generic candidates remain available for
later overload filtering. `NonGenericHead` leaves `<` to relational/operator parsing.
`UnresolvedHead` blocks or produces the grammar's explicit recovery/ambiguity form according to its
stored failure and dialect rule; the parser never guesses by declaration order or a speculative
parser copy.

`NAM-AMB-001`: If classification is `Unknown` and both syntax alternatives are structurally valid,
modern mode preserves ambiguity for semantic diagnosis; it does not choose based on whitespace or
declaration order.

Legacy HLSL behavior that requires prior type-name knowledge is isolated under a compatibility rule
and covered by differential tests.

## Redeclarations and overload groups

```text
RedeclarationClass =
    NamespaceEntity
  | CallableEntity(kind: DeclKind)
  | NonCallableEntity(kind: DeclKind)
  | StandardRedeclarationEntity(QualifiedName)

GenericBinderShape =
    NonGenericShape
  | GenericShape {
        parameters: NodeList<GenericParameterSort>,
        overloadConstraints: CanonicalConstraintSet
    }

ReceiverOverloadShape =
    NoOverloadReceiver
  | OverloadReceiver(selfType: TypeId, mode: ParamPassingMode)

OverloadParameterShape = {
    valueType: TypeId,
    mode: ParamPassingMode,
    labelIdentity: ParameterLabelIdentity
}

CallableShape = {
    receiver: ReceiverOverloadShape,
    parameters: NodeList<OverloadParameterShape>,
    registeredDiscriminators: CanonicalArguments
}

RedeclarationKey = {
    logicalParent: DeclId,
    name: NameKey,
    declarationClass: RedeclarationClass,
    genericShape: GenericBinderShape,
    callableShape: Option<CallableShape>
}

OverloadGroup = {
    name: NameKey,
    members: CanonicallyOrderedSet<DeclRef>,
    presentationOrder: NodeList<DeclRef>
}
```

`GroupRedeclarations(seed, wiring, environment)` is a query over only the outline fragments selected
by that `(scope, name, kind)` seed. It requests each fragment's `BuildRedeclarationKey` result and
partitions equal compatible keys into logical declarations; it neither scans unrelated names nor
publishes a module-wide declaration index. The key uses only facts required by the language to
decide whether declarations are attempts to denote the same entity. A checked
`CallableSignature` then validates compatible declarations/definitions.
`GenericBinderShape` is the alpha-normalized overload-identity projection: it retains parameter
sorts and only constraints that the versioned language rule declares overload-discriminating;
defaults are excluded. `CallableShape` retains receiver/input facts that can distinguish overloads.
Result/error types, parameter defaults and non-overload attributes, callable traits, calling
convention, inferred contracts, dispatch, origins, and parameter slots are excluded and are checked
later for header compatibility within a group. `registeredDiscriminators` is empty unless an
explicit ledger-approved language rule names another overload discriminator. `OverloadGroup`'s
`presentationOrder` is a duplicate-free bijection onto `members` sorted by stable source order.

`DEC-RED-000`: A successful `RedeclarationPartition.fragmentToDecl` domain is exactly the
eligible fragment set for its seed, and its range is exactly `groups.keys`. Each fragment occurs in
exactly one corresponding `RedeclarationGroup.fragments` list. `ResolveLogicalDecl(fragment)`
requests the partition for that fragment's outline seed and returns its unique mapped declaration.
A pending redeclaration-key or header dependency therefore blocks only that seed's query; it does
not prevent unrelated declarations from being parsed or checked.

`DEC-RED-001`: Two declaration fragments with a compatible redeclaration key form one canonical
entity with one `DeclId` plus multiple fragment origins. Conflicting headers produce a redeclaration error;
they do not become overloads merely because their types failed to match.

`DEC-OVL-001`: Distinct callable signatures sharing an overloadable name form an `OverloadGroup`.
The group is an immutable set of canonical declaration references. Source order is retained only as
stable presentation metadata.

`DEC-RED-002`: At most one non-external definition supplies a function body for a canonical
declaration in one module revision, except for explicitly capability-specialized definitions whose
coexistence rule is part of the standard environment.

`DEC-RED-003`: Building a redeclaration key is a named projection, not full-header equality. A
difference in result/error type, default argument, non-overload attribute, trait, or calling
convention cannot turn conflicting declarations into overloads. Such fragments first receive the
same identity key and then `BindDeclHeader` reports the field-specific compatibility error. Only a
field admitted by `CallableShape` or a registered discriminator may separate overload identities.

## Aggregate relations, facets, and extensions

```text
ComputeFacets(type, lookupEnvironment, contractSelection)
    -> QueryStep<FacetSet>
```

The direct inputs are separate, typed relations:

- the type's self member scope;
- a class's optional representation-base chain;
- interface conformances, interface refinements, and generic constraint witnesses;
- an opened existential's witness value; and
- applicable extensions reachable in `lookupEnvironment`.

The source colon clause is classified before facet computation as
`ClassBase`, `InterfaceConformance`, `InterfaceInheritance`, or
`EnumTagType`. A modern struct has no concrete representation-base alternative. Rejected
struct inheritance contributes no facet, base subobject, representation adjustment, or conformance
evidence. Chapter 15 is normative for the checked clause and route algebras.

Extension application has a context-free phase and a context-dependent phase. Target matching,
constraint evidence, specialization, and reachability produce intrinsic evidence. The second phase
selects only declared concrete-availability sources under the exact
`ContractSelectionContext.assumption`. Caller-owned ordinary capability uses are attached later in
an `ExtensionFacetUseAt<S>` when a member candidate is committed; they do not enter facet identity.

```text
match(ext.target, τ) = σ    solve(apply(σ, ext.constraints)) = evidence
reachable(ext, E)           intrinsic = ExtensionIntrinsic(ext, τ, σ, evidence, E)
selectConcreteAvailability(context.assumption, concreteSources) = availability
-------------------------------------------------------------------------------- NAM-EXT-001
ExtensionFacet(intrinsic, context.assumption, availability) ∈ directFacets(τ, E, context)
```

An extension failure is structured as non-applicable, blocked on dependencies, or erroneous. A
generic mismatch is not a diagnostic during ordinary member lookup; an ill-formed extension header
is diagnosed at the extension declaration.

## Facet routes and priority

Facet discovery produces the canonical route-keyed set from chapter 15. Selection is the maximal
set under its proof-carrying partial priority relation; enumeration order is presentation metadata
only.

`NAM-FAC-001`: Every non-self facet has a complete `FacetRouteKey`. Folding its route from the
queried type yields the facet owner and exact member-access evidence. Each interface-refinement
step performs one `LookupSubtypeWitness` with its stored requirement key.

`NAM-FAC-002`: Facets reached by different representation, conformance, refinement, existential,
or extension routes remain distinct even when their endpoint declarations and substitutions are
equal. They merge only with a typed `FacetEquivalenceProof`; map insertion, endpoint equality, and
source order are not equivalence proofs.

`NAM-FAC-003`: Lookup retains all maximal incomparable providers. One maximum is selected;
overloadable maxima form an overload set; multiple non-overloadable maxima are ambiguous. Import
proximity controls reachability and diagnostic provenance, while stable source/import order only
orders diagnostics.

`NAM-FAC-004`: There is no C3 merge across representation bases, interface refinements,
conformances, and extensions. Classes have a single representation-base chain. Interface diamonds
retain their keyed witness-lookup routes, and extensions are compared only by named semantic
specificity or override proofs.

`NAM-FAC-005`: Committing a member candidate copies every extension applicability ID in its lookup
path into the `BoundDeclUseAt<S>.extensionUses` domain and calls chapter 15's
`CommitExtensionFacetUseAt<S>` with caller-owned ordinary-use keys. Facet discovery never allocates
those keys, and candidate commitment never reruns the route's concrete-availability check.

## Interface names and `This`

An interface declaration introduces a checked `InterfaceDecl`. Its uses are classified explicitly:

- in a conformance or interface-inheritance constraint, the name denotes the interface;
- in an ordinary value type position, the name denotes an existential type containing a value and
  conformance evidence; and
- inside the interface's requirements, `This` denotes bound `ThisType(interface, binder)`.

`NAM-THIS-001`: Member facets of `This` are rooted at `ThisType`, with subtype evidence from `This`
to the interface. Member facets of an existential value are reached only after an explicit existential
opening. The two are not interchangeable `DeclRefType` interpretations.

This resolves the current dual-use limitation while keeping existing source spelling. Chapter 9
defines the corresponding conformance and existential rules.

## Extension-introduced conformances

Extension-introduced conformances are part of the semantic environment in which the extension is
reachable. They are not globally attached to the nominal declaration.

The proposed coherence rule is:

`DEC-CONF-001`: A public declaration's checked signature and body may rely only on conformances
reachable through its module's exported semantic environment. A private/internal body may use a
locally reachable conformance, but that conformance evidence is captured explicitly in its checked
body and IR dependencies.

Two reachable conformances for the same canonical `(type, interface)` pair are an ambiguity unless
one is the same canonical declaration or a language rule establishes specialization. Import order
never chooses one.

This makes separate compilation deterministic but is a proposed rule requiring review against
current extension behavior.

## Declarations as independent query products

There is no universal “checked declaration” state. Representative products are:

```text
DeclaredIdentity(d)
CheckedModifiers(d)
DeclHeader(d)
DeclaredConcreteAvailability(d)
CanonicalSignature(d)
MemberIndex(d)
FacetClosure(d, environment)
ConformanceSet(d, environment)
TypedBody(d)
InferredCapabilities(d)
ElaboratedDefinition(d)
```

Each product has a named dependency graph and typed cycle policy. A client requests the weakest fact
it needs. Declaration-outline parsing and scope wiring publish syntax facts but never raise a
declaration state. Fine parsing may request semantic facts through the scheduler, but a failed query
never marks unrelated facts as complete.

## Validation obligations

The name/declaration validator checks:

- each declaration belongs to exactly one lexical scope and logical module;
- unordered scopes contain all direct `ParserDeclStub` fragments exactly once;
- sequential scopes obey binding positions;
- every lookup-capable `UnparsedContent` has one exact entry position in `ScopeWiring`;
- each redeclaration partition covers exactly one seed's eligible fragments and maps each once;
- normalized decl-refs target declarations visible in their snapshot/module interface;
- lookup paths' substitutions and evidence compose to the selected declaration;
- overload and redeclaration groups have canonical keys and no duplicate members;
- every facet route validates and the priority graph contains only proved, acyclic dominance edges;
  presentation order is a duplicate-free view of the same facets; and
- exported facts use only exported/reachable declaration and conformance identities.

Current implementation evidence is centered in `slang-lookup.cpp`,
`slang-check-inheritance.cpp`, `slang-check-decl.cpp`, `slang-check-expr.cpp`, and the lookup/facet
support types in `slang-ast-support-types.h` and `slang-check-impl.h`.
