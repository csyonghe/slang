# Capabilities and visibility

Visibility and capabilities answer different questions. Declaration visibility determines whether a source
use may name a declaration and whether a declaration may expose another declaration. A capability
contract determines the compilation worlds in which an already accessible declaration is usable.
Neither relation changes name lookup identity or canonical function-type identity.

This chapter makes both systems finite, immutable semantic domains. All operations below are pure
except the scheduler queries that gather their inputs. The capability universe, module graph,
language version, and target profile are explicit query-key inputs.

## Visibility domain

The semantic visibility lattice is:

```text
DeclVisibility = Private | Internal | Public

Private < Internal < Public
meetVisibility(x, y) = min(x, y)
```

`Default` is syntax awaiting classification, not a fourth semantic visibility. A
`CheckedModifierSet` must resolve it before publishing a `DeclHeader`.

`VIS-DOM-001`: `meetVisibility` is associative, commutative, and idempotent, with `Public` as its
identity. Its result is the greatest visibility at which all inputs may be exposed.

`VIS-DOM-002`: `DeclVisibility` is attached to canonical declaration identity. A declaration use,
generic specialization, or lookup path cannot raise or lower the declaration's visibility.

## Declared and default visibility

```text
DeclaredVisibilityInput = {
    declaration: DeclId,
    explicitModifier: Option<DeclVisibility>,
    owner: Option<DeclId>,
    module: ModuleId,
    languageRules: LanguageRuleSetId
}

ComputeDeclaredVisibility(DeclaredVisibilityInput) -> CheckResult<DeclVisibilityFact>

VisibilityDefaultRule =
    NamespaceScopeDefault
  | LegacyPublicDefault(languageRules: LanguageRuleSetId)
  | ModuleDeclaredDefault(module: ModuleId, value: DeclVisibility)
  | ModernImplicitInternalDefault(module: ModuleId)

VisibilityDerivation =
    ExplicitModifier(origin: Origin)
  | InheritedVisibility(owner: DeclId)
  | DefaultedVisibility(rule: VisibilityDefaultRule)
  | OwnerCappedVisibility(input: VisibilityDerivation, owner: DeclId)

DeclVisibilityFact = {
    declaration: DeclId,
    module: ModuleId,
    privateOwner: Option<PrivateOwnerKey>,
    value: DeclVisibility,
    source: VisibilityDerivation
}
```

`VisibilityDefaultRule` is closed and records the exact compatibility rule that supplied an omitted
modifier. `OwnerCappedVisibility` retains the derivation it capped, including an explicit invalid
overexposure recovered by rule 6; it cannot contain the same owner twice and its chain follows
lexical ownership strictly outward. A valid or recovered fact whose `value` is `Private` has a
`Some(privateOwner)`; an invalid module-level `private` recovers to the applicable module default
rather than publishing a private fact with no access domain.

The default rules are evaluated in the following order:

1. An explicit valid modifier supplies the value.
2. An accessor, enum case, interface requirement, generic wrapper, generic parameter, or generic
   constraint inherits the visibility of the declaration it belongs to.
3. A namespace declaration is `Public` as a scope identity. This does not export its members;
   each member is classified independently.
4. In legacy language mode, an otherwise unmodified declaration defaults to `Public`.
5. In modern language mode, an otherwise unmodified declaration uses its module's declared
   default, which is `Internal` when the module does not specify one.
6. A defaulted nested declaration is capped by its enclosing named declaration using
   `meetVisibility`. An explicit nested visibility greater than its owner is diagnosed and
   recovered to the same meet.

`VIS-DEF-001`: `private` is valid only when `privateOwner(d)` exists. A module-level declaration
and a namespace declaration itself have no private owner. `internal` is valid at every named
declaration for which visibility is meaningful.

`VIS-DEF-002`: An interface requirement has the interface's visibility. A source modifier that
attempts to make a requirement less or more visible is rejected; recovery uses the interface's
visibility.

`VIS-DEF-003`: Defaults depend only on the declaration's language mode, module default, and owner
fact. Whether an unrelated declaration has an explicit visibility modifier cannot change them.

These rules preserve the current `Private < Internal < Public` ordering and legacy-public/modern
module default split. The owner cap is specified as a value rather than being reconstructed later
by `checkVisibility`.

## Reachability and access

Visibility classification is distinct from module reachability. A public declaration in a module
that was not imported is not a lookup candidate merely because it is public.

```text
ImportPathStep = {
    from: ModuleId,
    to: ModuleId,
    exported: Bool
}

ImportPath = NodeList<ImportPathStep>
ScopePath = NodeList<ScopeId>

ModuleReachability = {
    root: ModuleId,
    moduleGraph: ContentId<ModuleGraph>,
    reachable: CanonicallyOrderedSet<ModuleId>,
    canonicalPaths: CanonicallyOrderedMap<ModuleId, ImportPath>
}

ModuleReachabilityId = ContentId<ModuleReachability>

VisibilityContext = {
    useOrigin: Origin,
    useScope: ScopeId,
    module: ModuleId,
    reachableModules: ModuleReachabilityId,
    enclosingPrivateOwners: CanonicallyOrderedSet<PrivateOwnerKey>
}

PrivateOwnerKey =
    NamespaceOwner(canonicalNamespace: DeclId)
  | TypeOwner(nominalDefinition: DeclId)

VisibilityEvidence =
    PublicImport(path: ImportPath)
  | SameModule(module: ModuleId)
  | SamePrivateOwner(owner: PrivateOwnerKey, lexicalPath: ScopePath)

VisibilityFailureReason =
    PublicModuleUnreachable {
        declaration: DeclId,
        declarationModule: ModuleId,
        reachability: ModuleReachabilityId
    }
  | InternalModuleMismatch {
        declaration: DeclId,
        declarationModule: ModuleId,
        useModule: ModuleId
    }
  | PrivateOwnerMismatch {
        declaration: DeclId,
        requiredOwner: PrivateOwnerKey,
        enclosingOwners: CanonicallyOrderedSet<PrivateOwnerKey>
    }

VisibilityDecision =
    Allowed(VisibilityEvidence)
  | Denied(VisibilityFailureReason)
```

The denial alternatives are exhaustive for a validated `DeclVisibilityFact`: public access can fail
only reachability, internal access can fail only module equality, and private access can fail only
owner membership. Each alternative retains the endpoints needed to reproduce the failed premise;
diagnostics do not infer a reason later from rendered text. Malformed visibility facts are rejected
by `ComputeDeclaredVisibility`/snapshot validation and are not a fourth access outcome.

The path for the root is empty. Every other path starts at `root`, ends at its map key, and names
edges present in the exact `moduleGraph`; among semantically equivalent paths, canonical byte order
selects the stored evidence path. `reachable` is exactly the path-map key set. Duplicate physical
imports may contribute diagnostic origins, but they do not create different access truth.

`privateOwner(d)` is the nearest enclosing namespace or nominal type definition. An extension is
not a new private owner: its owner is the nominal definition at the root of its canonical target
type. Generic arguments and extension constraints do not create distinct private domains. For a
synthesized extension on a function-as-type, owner normalization continues through the function
to its enclosing nominal type. An extension whose target is not rooted in one nominal definition
has no private access.

```text
reachable(ctx, d)    visibility(d) = Public
------------------------------------------------ VIS-ACC-001
ctx |- d accessible

module(ctx) = module(d)    visibility(d) = Internal
------------------------------------------------ VIS-ACC-002
ctx |- d accessible

privateOwner(d) in ctx.enclosingPrivateOwners    visibility(d) = Private
---------------------------------------------------------------- VIS-ACC-003
ctx |- d accessible
```

`reachable` uses ordinary imports for an ordinary use and exported imports when validating an
exported surface. Core/standard-environment declarations are reachable through an explicit
prelude edge, not a special visibility exception.

`VIS-ACC-004`: Nested functions and synthesized code inherit the enclosing private-owner stack.
Derived types do not gain access to a base type's private members. Slang has no implicit
`protected` visibility.

`VIS-ACC-005`: A generic extension receives private access only after target matching proves that
its target root is the same nominal definition. Similar spelling, a conversion, inheritance, or a
user-defined equality witness is insufficient.

`VIS-ACC-006`: Lookup retains inaccessible candidates as rejected candidates with
`VisibilityDecision`; overload resolution and conformance matching may use them for diagnostics but
must not select them. Language-service recovery may display such a candidate without changing the
typed result.

## Recursive visibility of semantic values

`ComputeVisibilityFootprint` is a schema-driven traversal, not a list of ad hoc `Type` cases:

```text
ExposureRole = NameExposed | OpaqueSemanticDependency | ImplementationOnly

SemanticFieldPathStep =
    VariantPayload(variantTag: UInt32)
  | RecordField(field: FieldName)
  | ListElement(index: UInt32)
  | MapKey(key: ContentId<SchemaValue>)
  | MapValue(key: ContentId<SchemaValue>)

SemanticFieldPath = NodeList<SemanticFieldPathStep>

ExposureReference = {
    declaration: DeclRef,
    role: ExposureRole,
    origin: Origin,
    path: SemanticFieldPath
}

VisibilityFootprint = {
    maximumVisibility: DeclVisibility,
    references: CanonicallyOrderedSet<ExposureReference>
}

ComputeVisibilityFootprint(value, role) -> VisibilityFootprint
ComputeEffectiveVisibility(value) -> DeclVisibility
```

For `NameExposed` and `OpaqueSemanticDependency`, the traversal follows every structural semantic
operand in the schema. It stops at a nominal declaration reference after recording that
declaration, but continues through its specialization arguments and specialization evidence. It
does not recurse into the referenced declaration's definition. Graph-node memoization makes
recursive semantic values finite.

`VIS-TYPE-001`: The footprint of a type includes, as applicable:

- the nominal declaration and all type, value, and pack specialization arguments;
- element types and constant extents of arrays, vectors, matrices, tuples, and optionals;
- pointee, reference, access, address-space, resource-shape, and modifier operands;
- every component of union, intersection, existential, `This`, and associated-type projection
  types, including the interface requirement and evidence identities;
- generic binder kinds, defaults, and constraints;
- a function's receiver type/mode/qualifiers, parameter types/modes/traits, result and error types,
  differentiability traits, and calling-convention operands; and
- declarations referenced by symbolic constants, values embedded in types, constraints,
  attributes that affect calling/lookup/layout, and default argument expressions.

Types not named in this list are still covered by the schema traversal. Adding a type constructor
without classifying each structural field as exposed, opaque, or implementation-only is a schema
validation error.

```text
footprint(x).maximumVisibility =
    meetVisibility(visibility(r.declaration)
                   for r in footprint(x).references
                   where r.role = NameExposed)
```

An empty footprint has maximum visibility `Public`.

`VIS-TYPE-002`: Alpha-bound parameters and local symbolic variables do not contribute declaration
visibility. A free declaration referenced by a constant, constraint, substitution, or evidence
value does contribute.

`VIS-TYPE-003`: A nominal type's private fields and body are not recursively exposed merely by
naming the nominal type. Layout or specialization consumers receive those facts as
`OpaqueSemanticDependency` entries in a module artifact.

`VIS-TYPE-004`: `ComputeEffectiveVisibility` is the policy-homogeneous query named by chapter 11.
For an SCC of structurally exposed semantic values, it starts every value at `Public` and
repeatedly meets the visibility of its direct declaration references and current dependency
approximations. This is the `GreatestFixpoint` over `Private < Internal < Public`; publication is
atomic after the values stabilize. `ComputeVisibilityFootprint` separately collects the canonical
reference set while traversing the same graph, so reference provenance is not folded into the
three-element fixpoint domain.

## Declaration exposure

The exposed surface of a declaration is classified explicitly:

```text
DeclSurface = {
    nameExposed: NodeList<ContentId<SchemaValue>>,
    opaqueSemantic: NodeList<ContentId<SchemaValue>>,
    implementationOnly: NodeList<ContentId<SchemaValue>>
}
```

`nameExposed` includes the declared type or callable signature, generic binders/defaults/
constraints, base and refinement clauses, source-callable default arguments, public requirement
contracts, attributes that affect source use or ABI, the declared/effective ordinary capability
contract, and any concrete declaration availability. A function body is normally implementation-only.
A body exported for inlining, generic
specialization, constant evaluation, or witness construction is opaque semantic data: downstream
code may consume it but source lookup must not reveal its hidden declarations.

```text
visibility(d) <= footprint(DeclSurface(d).nameExposed).maximumVisibility
------------------------------------------------------------------------------- VIS-EXP-001
surface(d) is visibility-safe
```

`VIS-EXP-002`: Every `NameExposed` reference of a `Public` declaration must be reachable through
the defining module's exported semantic environment. Every external opaque dependency must have
an exported identity in its provider's module interface. A same-module private/internal opaque
dependency is permitted and is serialized under a non-source-visible exported ID.

`VIS-EXP-003`: A public alias exposes its aliased value. A public default argument exposes every
declaration that a downstream caller must bind or instantiate. Merely hiding the spelling in a
serialized expression does not make the dependency opaque.

`VIS-EXP-004`: Exposure validation reports every independent lowest-visibility reference in
canonical field-path order. Recovery replaces an invalid exposed operand with an `ErrorType`,
`ErrorValue`, or `ErrorEvidence` carrying the root diagnostic; it does not silently change the
source declaration's visibility.

## Modules, extensions, and synthesis

An exported module interface contains all public declaration surfaces, their effective ordinary
capability contracts, any separately declared concrete availability, and the opaque
semantic closure needed to consume them. Internal and private names are absent from source lookup
indexes even when an opaque identity is serialized.

`VIS-MOD-001`: Re-exporting a public declaration requires an exported import path to its defining
module. An ordinary private import is sufficient for an implementation body but never for a
public `NameExposed` reference.

An extension has both reachability and a target:

```text
ExtensionVisibilityLimit(ext) = meetVisibility(
    visibility(ext),
    footprint(ext.target).maximumVisibility,
    footprint(ext.genericBinderAndConstraints).maximumVisibility)
```

`VIS-EXT-001`: An extension member cannot be more visible than
`ExtensionVisibilityLimit(ext)`. A public extension member therefore cannot make an internal
target type or a private constraint observable. Extension import reachability remains an
independent applicability premise from chapter 6.

`VIS-EXT-002`: Private access granted by an extension is based on normalized target owner as
defined above. It does not make the extension or its members reachable from modules that did not
import the extension.

Synthesized declarations are published as an atomic `SynthesisGroup` and receive an explicit
visibility plan:

```text
SynthesisVisibilityPlan = {
    requested: DeclVisibility,
    ownerLimit: DeclVisibility,
    requirementLimit: DeclVisibility,
    exposedOperandLimit: DeclVisibility,
    result: DeclVisibility
}

result = meetVisibility(requested, ownerLimit, requirementLimit, exposedOperandLimit)
```

`VIS-SYN-001`: Synthesis never guesses visibility from the insertion location. Its rule supplies
`requested`; the other limits are computed from semantic identities. If `result != requested`, a
user-caused synthesis reports the corresponding visibility error and publishes a recovered group
at `result`. An implementation-internal mismatch fails semantic validation.

`VIS-SYN-002`: A synthesized conformance thunk may reference a private satisfying member as an
opaque witness implementation. If the thunk's signature names that member or another hidden type,
the reference is `NameExposed` and the ordinary exposure rule rejects it.

## Capability universe

Capabilities are interpreted relative to a finite, versioned standard-environment value:

```text
CapabilityAtom = QualifiedName
CapabilityName = QualifiedName
KeyholeId = QualifiedName
KeyholeBranchId = QualifiedName

AtomImplication = {
    stronger: CapabilityAtom,
    weaker: CapabilityAtom
}

CanonicalAtomPair = {
    first: CapabilityAtom,
    second: CapabilityAtom
}

AtomPreorder = CanonicallyOrderedSet<AtomImplication>
SymmetricAtomRelation = CanonicallyOrderedSet<CanonicalAtomPair>

KeyholeDefinition = {
    stableName: QualifiedName,
    branches: CanonicallyOrderedSet<KeyholeBranchId>
}

CapabilityUniverseDefinition = {
    atoms: CanonicallyOrderedMap<CapabilityAtom, AtomDefinition>,
    names: CanonicallyOrderedMap<CapabilityName, CapabilityNameDefinition>,
    keyholes: CanonicallyOrderedMap<KeyholeId, KeyholeDefinition>
}

CapabilityUniverseRevision = ContentId<CapabilityUniverseDefinition>

CapabilityUniverse = {
    revision: CapabilityUniverseRevision,
    definition: CapabilityUniverseDefinition,
    expandedNames: CanonicallyOrderedMap<CapabilityName, CapabilitySet>,
    implication: AtomPreorder,
    incompatibility: SymmetricAtomRelation
}

AtomDefinition = {
    stableName: QualifiedName,
    key: Option<KeyChoice>,
    directlyImplies: CanonicallyOrderedSet<CapabilityAtom>,
    directlyIncompatible: CanonicallyOrderedSet<CapabilityAtom>,
    rankMetadata: Option<UInt32>
}

RawCapabilityExpr =
    RawAtom(CapabilityAtom)
  | RawName(CapabilityName)
  | RawRequireAll(CanonicallyOrderedSet<RawCapabilityExpr>)
  | RawAllowEither(CanonicallyOrderedSet<RawCapabilityExpr>)

CapabilityNameDefinition = Atom(CapabilityAtom) | Alias(RawCapabilityExpr)
KeyChoice = { keyhole: KeyholeId, branch: KeyholeBranchId }
```

`target` and `stage` are standard keyholes, not hard-coded enum ranges. A universe may define
additional mutually exclusive families. Target-version or shader-model atoms normally imply the
less-specific target atom and earlier versions through ordinary implication edges.

`CAP-UNIV-001`: Atom IDs derive from stable qualified names, never generated enum ordinals.
Aliases introduce no atom identity and are fully expanded before canonical formula publication.

`CAP-UNIV-002`: The validated implication relation is reflexive and transitive. A strongly
connected component of mutually implying atom declarations is collapsed to one canonical atom or
rejected if its definitions disagree.

`CAP-UNIV-003`: Incompatibility is irreflexive, symmetric, and closed under strengthening: if
`a` is incompatible with `b` and `c` implies `a`, then `c` is incompatible with `b`. Distinct
branches of an exclusive keyhole are incompatible unless the universe explicitly relates them as
the same canonical branch. Versions in one implication chain are compatible.

`CAP-UNIV-004`: Alias expansion must terminate, keyhole references must resolve, and all standard
profiles must be satisfiable. Universe validation completes before any source capability formula
is checked.

`CAP-UNIV-005`: A universe revision is chapter 1's collision-safe `ContentId` of the complete raw
definition. Raw aliases are universe-independent expressions over stable atom/name IDs, so this ID
has no self-reference. Validation expands every acyclic alias into a formula tagged with the new
revision. The validated implication preorder is exactly the reflexive/transitive closure of
`directlyImplies`; incompatibility is exactly the symmetric strengthening closure of
`directlyIncompatible` plus distinct branches of each keyhole. These derived relations are checked
outputs, not second authorities in the raw definition. An atom map key equals its `stableName`;
name and keyhole keys are themselves their stable names. A `CanonicalAtomPair` stores its two
distinct IDs in canonical order.

```text
WorldAtomSet = {
    universe: CapabilityUniverseRevision,
    atoms: CanonicallyOrderedSet<CapabilityAtom>
}
```

An **available world** is a compatible, implication-closed `WorldAtomSet`. A concrete compilation
profile supplies such a world. A library contract denotes the set of worlds in which a declaration
may be used. `WorldAtomSet` is not a requirement clause: it retains the complete implication
closure needed to answer positive and negative region predicates.

## Canonical DNF

```text
CapabilityAtomSet = CanonicallyOrderedSet<CapabilityAtom>       // conjunction
CapabilitySet = {
    universe: CapabilityUniverseRevision,
    clauses: CanonicallyOrderedSet<CapabilityAtomSet>              // disjunction
}

TrueFormula(U)  = { universe: U, clauses: { {} } }
FalseFormula(U) = { universe: U, clauses: {} }
```

Later equations omit `(U)` only when the query key supplies one unambiguous universe revision.

A world `W` satisfies a clause when it contains every atom in the clause, and satisfies a formula
when it satisfies at least one clause.

For clauses:

```text
C entailsClause D iff
    for every d in D, some c in C satisfies atomImplies(c, d)
```

For formulas in the positive DNF domain:

```text
F entails G iff
    for every clause C in F, some clause D in G satisfies C entailsClause D
```

This criterion is complete because the universe admits atomic implication and incompatibility but
no hidden disjunctive atom implications. Disjunction belongs in named formula expansion.

`CAP-NORM-001`: Canonicalization performs these steps to a fixed point:

1. expand capability names and distribute conjunction over disjunction;
2. remove duplicate atoms;
3. remove an atom implied by another atom in the same clause;
4. discard a clause containing an incompatible atom pair;
5. deduplicate clauses; and
6. discard a clause `C` when another clause `D` exists and `C entailsClause D` (absorption).

Atoms within a clause and clauses within a formula are sorted by stable atom IDs after
canonicalization. If the empty clause occurs, it absorbs every other clause and the result is
`TrueFormula`.

`CAP-NORM-002`: `canon` is idempotent and semantic equality is structural equality of canonical
DNF under one universe revision. Formulas from different revisions are not directly comparable.

`CAP-NORM-003`: `FalseFormula` is a valid semantic value distinct from
`ErrorCapabilityRequirement(ErrorId)`. The former proves incompatibility; the latter is typed
recovery outside the formula algebra for malformed source or an invalid universe. Lattice operators
never receive an error requirement.

### Generic capability schemes

A closed specialization has a `CapabilitySet`. A generic declaration whose compile-time
control flow still depends on its parameters has a symbolic scheme instead of pretending that one
formula describes every specialization:

```text
CapabilityRequirement =
    Closed(CapabilitySet)
  | Generic(CapabilityScheme)
  | ErrorCapabilityRequirement(ErrorId)

CapabilityScheme = {
    binder: CanonicalGenericBinder,
    root: CapabilityRequirementExprId
}

CapabilityRequirementExpr =
    Formula(CapabilitySet)
  | RequireAll(NodeList<CapabilityRequirementExprId>)
  | AllowEither(NodeList<CapabilityRequirementExprId>)
  | IfConst(predicate: SymbolicBoolValue, thenExpr: CapabilityRequirementExprId,
            elseExpr: CapabilityRequirementExprId)
  | ErrorCapabilityRequirementExpr(ErrorId)

CapabilityRequirementExprId = ContentId<CapabilityRequirementExpr>

CapabilityImplicationProof = {
    premise: CapabilityRequirement,
    conclusion: CapabilityRequirement,
    universe: CapabilityUniverseRevision,
    rule: RuleId
}
```

A `CapabilityImplicationProof` is valid only in its stored universe and only when this chapter's
implication relation proves its exact premise/conclusion relation, pointwise for a generic scheme.
The record is an endpoint certificate, not a trusted boolean.

The scheme is a canonical immutable decision DAG. `RequireAll` and `AllowEither` are flattened,
sorted, deduplicated, and simplified using their identities. A decided `IfConst` is replaced by its
selected child; equal children eliminate the condition. Substitution uses the declaration's
`SpecializationFrame`, including constraint evidence, and returns either a residual scheme or a
closed formula.

`CAP-NORM-004`: A closed callable contract contains no unresolved `IfConst`. A partially applied
generic value retains the residual scheme in its `CallableValue`; dropping the condition or
combining both branches unconditionally is invalid.

`CAP-NORM-005`: Entailment between schemes is path-sensitive under the generic binder constraints.
The generic solver removes unreachable decision paths and compares every reachable pair of closed
leaves. If a condition cannot yet be decided, checking produces a serialized
`CapabilityEntailmentObligation`. An ordinary callable requirement may carry that obligation through
partial application and caller inference, but every concrete instantiation must discharge it before
declared-contract validation or module publication succeeds. A concrete-availability scheme must be
closed before it can filter a candidate, as required by `CAP-VAR-003`.

## Capability algebra

To avoid the current implementation's overloaded `join` and `union` terminology, semantic rules
use logic-bearing names:

```text
requireAll(F, G) = canon(F and G)
                 = canon({ C union D | C in F, D in G })

allowEither(F, G) = canon(F or G)
                  = canon(F union G)

incompatible(F, G) iff requireAll(F, G) = FalseFormula
```

The information order for inference is the **requirement order**:

```text
F <=req G iff G entails F
```

`G` is above `F` when `G` is at least as demanding. Under this order:

```text
bottom                 = TrueFormula
top                    = FalseFormula
joinReq(F, G)          = requireAll(F, G)
meetReq(F, G)          = allowEither(F, G)
```

`CAP-ALG-001`: `requireAll` and `allowEither` are associative, commutative, and idempotent after
canonicalization. They distribute over one another. `TrueFormula` is the identity for
`requireAll`; `FalseFormula` is the identity for `allowEither`.

`CAP-ALG-002`: Availability is logical implication:

```text
requirementView(world) = canon({ world.atoms })
requirementView(world) entails requiredFormula
------------------------------------------------
requiredFormula is available
```

Compatibility is weaker than availability. A target that is merely compatible with a requirement
does not satisfy it.

`CAP-ALG-003`: Ranking metadata is not part of implication, equality, or canonicalization. It may
break a tie between multiple already-applicable capability-specialized variants under a named
overload rule, but cannot make a concretely unavailable candidate applicable.

### Boolean capability regions

Positive `CapabilitySet` values describe monotone availability requirements. Conditional
witness maps and target/stage branch partitions additionally need complement and difference, so
they use a separate domain:

```text
CapabilityPredicateExpr =
    PredicateTrue
  | PredicateFalse
  | HasAtom(CapabilityAtom)
  | Not(CapabilityPredicateExprId)
  | And(NodeList<CapabilityPredicateExprId>)
  | Or(NodeList<CapabilityPredicateExprId>)

CapabilityPredicateExprId = ContentId<CapabilityPredicateExpr>

BooleanCapabilityPredicate = {
    universe: CapabilityUniverseRevision,
    root: CapabilityPredicateExprId
}

CapabilityRegionAvailabilityProof = {
    region: BooleanCapabilityPredicate,
    requirement: CapabilityRequirement,
    rule: RuleId
}
```

The canonical representation is a reduced ordered decision DAG using stable atom-ID order and the
universe's implication/incompatibility constraints. Two predicates are equal when they select the
same valid worlds under one universe revision. `predicate(F)` embeds a positive formula. Boolean
`and`, `or`, complement, and difference are total predicate operations.

Formula, predicate, and world operations require equal universe revisions. Cross-revision input
returns a structured revision mismatch and is never compared by atom IDs alone.

`CAP-REG-001`: A `BooleanCapabilityPredicate` is a region selector, not a declaration requirement.
It may contain negative tests. `EffectiveConformanceContract.availability`, callable effective
ordinary requirements, and closed `ConcreteAvailability` requirements remain positive
`CapabilitySet` values.

`CAP-REG-002`: Chapter 9's `ConditionalRequirementWitnessAt<K, S>` guards are canonical predicates intersected
with the conformance's positive availability formula. Guards must be disjoint or carry equivalent
evidence on their overlap, and their union must cover that availability. Complement used to split
overlap does not become a negative conformance contract.

`CAP-REG-003`: A predicate can be projected to a positive capability formula exactly when its
selected valid worlds are upward-closed under adding compatible supported atoms. Projection takes
the minimal selected worlds and canonicalizes their positive clauses. A non-upward-closed
predicate has no positive projection and returns a structured failure.

`CAP-REG-004`: Predicate canonicalization, complement, coverage, disjointness, and projection are
relative to `CapabilityUniverse.revision` and use symbolic decision operations; an implementation
must not enumerate driver profiles as an accidental definition of the region.

`CAP-REG-005`: `CapabilityRegionAvailabilityProof(region, requirement, rule)` is valid exactly when
every valid world selected by `region` satisfies `requirement`. The universe revisions must match;
a generic requirement is checked pointwise over its canonical decision regions. This proof is used
for availability under an expression's possibly negative world assumption and is not replaced by a
positive-formula implication proof.

Every declaration or registered operation keeps concrete selection availability separate from the
ordinary requirements transmitted to capability inference:

```text
ConcreteAvailabilityKey = {
    requirement: CapabilityRequirement,
    rule: RuleId
}

ConcreteAvailabilityId = ContentId<ConcreteAvailabilityKey>

ConcreteAvailability = {
    id: ConcreteAvailabilityId,
    key: ConcreteAvailabilityKey,
    origin: Origin
}

ConcreteAvailabilitySubject =
    DeclAvailability(declaration: DeclRef)
  | RegisteredStandardOperationAvailability(
        registration: RegisteredDataOperationRegistration)
  | LanguageRuleAvailability(languageRules: LanguageRuleSetId,
                             rule: RuleId,
                             staticInputs: CanonicalArguments)

ResolvedConcreteAvailability = {
    source: ConcreteAvailabilityId,
    subject: ConcreteAvailabilitySubject,
    requirement: CapabilityRequirement
}

ConcreteAvailabilitySet = {
    sources: NonEmpty<ResolvedConcreteAvailability>,
    combinedRequirement: CapabilityRequirement
}

combineConcreteAvailability(sources) =
    requireAllRequirements([s.requirement | s in canonicalUnique(sources)])

totalConcreteAvailability(None, U) = Closed(TrueFormula(U))
totalConcreteAvailability(Some(a), U) = a.combinedRequirement

ConcreteAvailabilitySelection =
    NoConcreteAvailability
  | ProvenConcreteAvailability {
        sources: NonEmpty<ResolvedConcreteAvailability>,
        combinedRequirement: CapabilityRequirement,
        proof: CapabilityRegionAvailabilityProof
    }

CapabilitySelectionAt<S: WitnessTableState> = {
    region: BooleanCapabilityPredicate,
    inferredCapabilityUses:
        CanonicallyOrderedMap<CapabilityUseId, CapabilityUse<S>>,
    concreteAvailability: ConcreteAvailabilitySelection
}

CapabilitySelection = CapabilitySelectionAt<Published>

ComputeConcreteAvailability(declaration: DeclId,
                            modifiers: CheckedModifierSet,
                            environment: SemanticEnvironmentId)
    -> CheckResult<Option<ConcreteAvailability>>

ResolveConcreteAvailability(subject: ConcreteAvailabilitySubject,
                            environment: SemanticEnvironmentId)
    -> QueryStep<Option<ResolvedConcreteAvailability>>

SelectCapabilitiesAt<S>(region: BooleanCapabilityPredicate,
                        inferredUses:
                            CanonicallyOrderedMap<CapabilityUseId, CapabilityUse<S>>,
                        concreteSources: NodeList<ResolvedConcreteAvailability>)
    -> CheckResult<CapabilitySelectionAt<S>>
```

`ConcreteAvailabilitySubject` is a closed operational subject. A declaration subject contains the
fully specialized declaration reference; a registered-operation subject contains the complete
registration/environment/static-input tuple; and a language-rule subject contains its exact
language-rule set, rule, and static inputs. Rendered names, an ambient current declaration, or a
bare requirement cannot stand in for one of these alternatives.

`requireAllRequirements` is the canonical pointwise lift of `requireAll` to
`CapabilityRequirement`: closed inputs combine their formulas, compatible generic schemes combine
the corresponding decision-DAG leaves under their shared canonical binder, and any binder/revision
mismatch or error input returns its structured requirement error. It does not close a residual
generic scheme by consulting an ambient specialization.

`CAP-SEL-001`: `ComputeConcreteAvailability` is the sole source-declaration producer used by
`BindDeclHeader`; when it returns `Some(a)`, the published header stores `Some(a.id)` and
`a.id = ContentId(a.key)`. `ResolveConcreteAvailability` validates its subject: a declaration
source must equal the availability ID stored by its `DeclHeader` and substitutes that declaration's
canonical specialization spine into the key requirement; a registered or language-rule source
must be declared by the named versioned rule with the exact static inputs. The returned requirement
is that validated specialization, never the declaration's ordinary capability requirement.

`CAP-SEL-002`: A `ConcreteAvailabilitySet.sources` list is nonempty, canonically ordered, and
duplicate-free. Its `combinedRequirement` equals `combineConcreteAvailability(sources)` byte for
byte. Thus composition preserves every contributing subject and preserves an explicitly declared
`TrueFormula`; an empty source list is represented by `None`, not by manufacturing a source-free
true availability.

`CAP-SEL-003`: A `CapabilitySelectionAt<S>` map key equals `ContentId(use.key)` and every use is at
stage `S`. `NoConcreteAvailability` is valid exactly when selection received no concrete sources.
`ProvenConcreteAvailability` has the exact canonical source list supplied to selection, recomputes
the stored combined requirement with `combineConcreteAvailability`, and has a proof whose region is
`selection.region` and whose requirement is that combined requirement. An unavailable, residual,
or cross-universe source yields a structured failed/blocked selection; it cannot be dropped from a
successful product.

`CAP-SEL-004`: Merging capability selections requires identical regions. It takes the keyed union
of ordinary uses, rejecting inconsistent equal keys, and the canonical union of all concrete
sources, then re-runs `SelectCapabilitiesAt` for that union. No ordinary use is converted into a
concrete source, and no concrete proof is inserted into the inference-use map. Calls, conversions,
access plans, extensions, initialization operations, and differentiability providers preserve this
complete product rather than copying just its requirement or proof.

`CAP-REG-006`: A `PreInferenceCallableContract.concreteAvailability` is either `None` or one
validated `ConcreteAvailabilitySet`; it is never synthesized from the callable's declared,
inferred, or effective ordinary capability contract. Candidate selection copies all of the set's
sources into `ProvenConcreteAvailability` and proves its combined requirement under the exact
symbolic region; `None` yields `NoConcreteAvailability`. Chapter 9's
`ConcreteAvailabilityCompatibilityProof` is a different proof: its two nested region proofs share
the requirement-match region and use the two optional sets after `totalConcreteAvailability`. It
therefore proves that both the requirement and implementation are available throughout that
guarded region without claiming availability outside it. Every availability record satisfies
`id = ContentId(key)`; `origin` supports diagnostics and does not change semantic identity.

## Declared, inferred, and effective capability requirements

Capability requirements are declaration facts, not function-type operands. The same canonical
`FuncType` can be called directly, through a witness, or under different capability variants.

```text
DeclaredCapabilityRequirements = {
    requirement: CapabilityRequirement,
    explicitOrigin: Option<Origin>,
    inheritedOrigins: NodeList<Origin>
}

DeclaredCapabilityRequirementsId = ContentId<DeclaredCapabilityRequirements>

InferredCapabilityRequirements = {
    requirement: CapabilityRequirement,
    uses: CapabilityUseGraphId,
    universe: CapabilityUniverseRevision
}

CapabilityRequirementProvenance = {
    contract: EffectiveCallableContractId,
    uses: CapabilityUseGraphId
}
```

`EffectiveCallableContract` is the single schema defined in chapter 5. Its `signature` field is a
`CallableSignatureId`, preserving parameter-slot identity, and its capability fields are closed
`CapabilitySet` values for one complete specialization. A generic declaration stores the
corresponding declared/inferred `CapabilityRequirement` schemes until substitution closes them.
Capability provenance is a separate fact so the callable contract schema is not duplicated.

The effective closed capability set is a pure accessor:

```text
effectiveCapabilities(c) =
    requireAll(c.declaredCapabilities, c.inferredCapabilities)
```

`CAP-CON-001`: Canonical function equality, overload identity, symbol mangling, and ABI lowering do
not read declared, inferred, or effective capability formulas. Interface matching compares the
ordinary inferred-requirement and optional concrete-availability premises separately. Call
applicability checks only concrete availability; the ordinary requirement becomes the selected
call's keyed `CapabilityUse` and participates in caller inference.

Arguments inside one `[require(a, b, ...)]` attribute denote `requireAll(a, b, ...)`. Multiple
`[require(...)]` attributes on the same declaration denote `allowEither` alternatives.
Requirements contributed by lexically enclosing declarations denote `requireAll` constraints.
Thus an incompatible parent/local combination is `FalseFormula`, not an instruction to preserve
the local target alternative. This is a proposed principled change from current
`nonDestructiveJoin` behavior and requires a compatibility decision in chapter 13.

An unconstrained declaration has `declared(d) = TrueFormula`. A declaration is **constrained** when
it has either an explicit local origin or at least one inherited origin; inherited constraints are
real promises even when the declaration itself has no `[require]` spelling.

```text
constrained(d)    declared(d) entails inferred(d)
------------------------------------------- CAP-CON-002
explicit contract of d covers its definition
```

For every closed declaration specialization, including recovery:

```text
effective(d) = requireAll(declared(d), inferred(d))
```

If `d` is constrained and the premise holds, canonicalization reduces this formula to
`declared(d)`. If it is unconstrained, `declared(d)` is `TrueFormula` and the result is
`inferred(d)`. An explicit declaration may therefore be intentionally stricter than its body. On
failure, the declaration is invalid, while the same equation remains a conservative recovery
contract so downstream compilation cannot assume missing support.

For a generic declaration, `CAP-CON-002` is applied path-by-path to its schemes as specified by
`CAP-NORM-005`. Residual entailment obligations become inputs to, rather than implicit assumptions
of, each closed specialization.

`CAP-CON-003`: Exported module metadata contains the effective contract. A body change may change
that contract and invalidate dependents, but it cannot change function type identity or mangling.

Capability-specialized definitions with the same source signature form a `CallableVariantSet`:

```text
CallableVariantSetKey = {
    canonicalSymbol: DeclId,
    signature: CallableSignatureId
}

CallableVariantSetId = ContentId<CallableVariantSetKey>

CallableVariantSet = {
    id: CallableVariantSetId,
    key: CallableVariantSetKey,
    variants: NonEmpty<CallableVariant>
}

CallableVariant = {
    declaration: DeclRef,
    signature: CallableSignatureId,
    concreteAvailability: ConcreteAvailabilityId,
    stableOrder: StableOrderKey
}

CapabilityVariantSelectionResult =
    Selected(CapabilityVariantSelectionProof)
  | NoAvailableVariant(NodeList<CallableVariant>)
  | AmbiguousVariants(NonEmpty<CallableVariant>, NodeList<CapabilityComparisonProof>)

CapabilityComparisonProof = {
    preferred: DeclRef,
    rejected: DeclRef,
    basis: StrictCapabilitySpecificity {
               preferredAvailability: CapabilityRequirement,
               rejectedAvailability: CapabilityRequirement,
               forward: CapabilityImplicationProof,
               reverseFailure: CapabilityCounterexample
           }
         | RegisteredCapabilityPreference {
               rule: StandardEnvironmentRuleId,
               inputs: CanonicalArguments
           }
}

ConcreteVariantAvailabilityProof = {
    variant: DeclRef,
    availability: ResolvedConcreteAvailability,
    world: WorldAtomSet,
    supportingClause: CapabilityAtomSet
}

CapabilityVariantSelectionProof = {
    set: CallableVariantSetId,
    world: WorldAtomSet,
    selected: DeclRef,
    applicable: NonEmpty<ConcreteVariantAvailabilityProof>,
    dominance: NodeList<CapabilityComparisonProof>,
    rankingRule: Option<StandardEnvironmentRuleId>
}
```

`CallableVariantSet.id = ContentId(CallableVariantSet.key)`. Every variant's
`declaration.declaration` equals `key.canonicalSymbol`, every variant's `signature` equals
`key.signature`, and declaration references differ only in capability-specialized definition frames
permitted by the canonical symbol. Duplicate canonical declaration references are rejected. These
invariants keep capability alternatives from becoming accidental ordinary overloads. Each
`concreteAvailability` resolves in the variant's semantic environment; an ordinary
`DeclaredCapabilityRequirements` or `EffectiveCallableContract` cannot occupy that field.

Let `availability(v)` be the closed requirement reached through `v.concreteAvailability`. A variant
is applicable in world `W` exactly when `W` satisfies `availability(v)`, witnessed by its
`ConcreteVariantAvailabilityProof`. Among applicable variants, `a` is strictly more
capability-specific than `b` when `availability(a)` entails `availability(b)` and the converse does
not hold. Remove every dominated variant. A versioned standard-environment rank may compare
remaining maximal variants only under an explicit rule; if it does not produce one canonical
declaration, selection is ambiguous. The variants' ordinary inferred/effective requirements are not
filtering or ranking inputs.

`CAP-VAR-001`: `CapabilityVariantSelectionProof.applicable` is the duplicate-free canonical list of
exactly the variants with valid availability proofs for the stored world; each proof resolves that
variant's exact `ConcreteAvailabilityId`, has
`availability.subject = DeclAvailability(variant)`, and retains the specialized closed
requirement. The selection proof also contains a checked
dominance/rank proof from every rejected maximal candidate to the selected declaration. Formula hash,
container order, and `stableOrder` are not semantic premises.

`CAP-VAR-002`: `stableOrder` is presentation metadata for deterministic diagnostics only. Two
incomparable maximal variants cannot be selected by source order, task order, or atom numeric ID.

`CAP-VAR-003`: Substitution closes every residual concrete-availability scheme before target-world
variant selection. A residual `IfConst` produces a blocked/partial generic value, not a guessed
variant. Closing the ordinary inferred requirement is independent and does not make it a selector.

`CAP-CON-004`: Variant selection first requires accessibility and ordinary signature
applicability, then filters by concrete availability, and only then applies capability-specific
ranking. The selected variant is recorded in `CallableValue`; variants do not masquerade as
distinct function types. Ordinary inferred requirements neither filter nor rank the variants.

`CAP-CON-005`: Two local variants may be distinguished by capability availability only when each
has an explicit validated `ConcreteAvailability`. `ResolveOverload` reads those pre-inference
availability facts and never requests a local body-inferred contract. An unannotated local callable
has no concrete filter; its ordinary requirement propagates through the eventual caller contract and
is checked at a constrained declaration or compilation-world boundary. An imported variant is
filterable only when its module publishes concrete availability separately; its published effective
ordinary contract cannot be reinterpreted as that filter.

The general pre-inference callable fact is:

```text
preInference(d).inferredCapabilities =
    declared(d).requirement                    when d is local and constrained
  | Closed(TrueFormula(U))                    when d is local and unconstrained
  | Closed(effectiveCapabilities(publishedEffective(d)))
                                                when d is imported

preInference(d).concreteAvailability =
    Some({
        sources = { resolveConcreteAvailability(DeclAvailability(d)) },
        combinedRequirement =
            resolveConcreteAvailability(DeclAvailability(d)).requirement
    })
                                                when d declares/imports a validated concrete filter
  | None                                        otherwise
```

Here `U` is the query's capability-universe revision. The first projection always returns a
`CapabilityRequirement`; the second returns `Option<ConcreteAvailabilitySet>`, matching
`PreInferenceCallableContract`. The singleton set is validated by `CAP-SEL-002`; synthesized
adapters and compound registered operations may retain multiple sources. A selected local use
retains its stable declaration identity, so `InferCapabilities` follows the callee even when the
pre-inference ordinary projection is `TrueFormula`.

`CAP-CON-006`: Lookup and overload resolution use only the sources in `concreteAvailability` as
callable capability-applicability predicates. A successful candidate stores chapter 5's complete
`CapabilitySelectionAt<Published>` with the exact region proof or explicit
`NoConcreteAvailability`. Local requirement matching compares both pre-inference fields under
chapter 9's distinct proof families; extension applicability likewise filters only on concrete
sources. Every selected call records exactly one keyed use for `inferredCapabilities`. None of these
queries discovers local ordinary requirements by checking a candidate body; capability inference
follows the selected declaration identity and post-inference validation rejects a false declared
promise. Failure of the current symbolic region to imply `inferredCapabilities` is never a
candidate rejection.

## Capability uses and inference

```text
CapabilityUseKey = {
    owner: DeclRef,
    origin: Origin,
    ordinal: UInt32
}

CapabilityUseId = ContentId<CapabilityUseKey>

CapabilityUse<S: WitnessTableState> = {
    key: CapabilityUseKey,
    requirement: CapabilityUseRequirement<S>,
    reason: DirectOperation | TypeUse | DeclUse | WitnessUse |
            AttributeUse | EntryPointStage
}

CapabilityUseRequirement<S: WitnessTableState> =
    Direct(CapabilityRequirement)
  | LocalCallable(declaration: ResolvedDeclRefAt<S>)
  | ImportedCallable(contract: CapabilityRequirement)
  | WitnessEntry(witness: SubtypeWitnessRef<S>, entry: RuntimeInterfaceRequirementKey)

CapabilityUseGraph<S: WitnessTableState> = {
    root: DeclRef,
    rootWitnessResolutions: WitnessResolutionSetAt<S>,
    uses: CanonicallyOrderedMap<CapabilityUseId, CapabilityUse<S>>
}

CapabilityUseGraphId = ContentId<CapabilityUseGraph<Published>>

CapabilityUsePathStep = {
    owner: DeclRef,
    use: CapabilityUseId,
    next: Option<DeclRef | RuntimeInterfaceRequirementKey>
}
```

Unqualified `CapabilityUse` means `CapabilityUse<Published>`. Only a construction-stage synthesis
graph may instantiate `<Construction>`; atomic freeze resolves every operational conformance to a
validated published reference before publication.
`rootWitnessResolutions` is the minimal stage-correct set required by `root.specializations`.
Every graph map key equals `ContentId(use.key)`, every `use.key.owner` equals `root`, and ordinals
are assigned by stable origin plus semantic child-role order, never task or hash-map order.
The use origin is projected only as `use.key.origin`; there is no second payload copy.

`CAP-USE-001`: A capability-use graph contains only direct uses in `root`'s body. Every map ID
resolves to its payload and every payload owner equals `root`. `LocalCallable` and `WitnessEntry`
requirements themselves name scheduler dependencies; inference follows those dependencies without
copying/re-keying transitive callee uses. Imported/direct requirements are leaves. A
`CapabilityUsePathStep` resolves `use` in the direct graph of `owner`; `next` is present exactly for
a local-call/witness requirement and equals its named target. Adjacent diagnostic steps agree on
that target, and the last step is a leaf, so paths are validated projections of scheduler traversal
rather than arbitrary graph edges.

`CAP-USE-002`: A selected callable contributes exactly one keyed use for its
`PreInferenceCallableContract.inferredCapabilities`, represented by the local, imported, or witness
constructor appropriate to its stable target. That use is an entry in the selected
`CapabilitySelectionAt<S>.inferredCapabilityUses` map. Concrete-availability sources and their
region proof never enter the use graph. If one operation independently declares equal ordinary and
concrete formulas, the ordinary formula still contributes one use and the concrete formula still
has one availability proof; neither is deduplicated across those different semantic roles.

`DeclRef` is the sole owner of callable specialization frames. A local callable use wraps
that stable target in `ResolvedDeclRefAt<S>` solely to retain the exact definition dependencies of
witness evidence in those frames. A witness use is already specialized by its stage-appropriate
`SubtypeWitnessRef` and `RuntimeInterfaceRequirementKey`; capability edges do not repeat a frame ID that could
diverge from those identities. Property and subscript calls retain their exact accessor role in
that entry key.

Standard operations and types contribute contracts through versioned standard-environment facts.
A local call records callee identity and specialization, not a snapshot of an inferred formula.
The capability fixpoint reads that callee's declared contract and current inference approximation
directly. An imported call contributes the substituted, already published effective contract. A
witness call resolves its keyed satisfaction using the same local/imported distinction. Generic
specialization substitutes contract operands using the callable's `SpecializationFrame`; it cannot
re-run inference with lost constraint evidence.

`CAP-INF-001`: Sequential expressions/statements, operands of one operation, stored property
types, and ordinary runtime control-flow branches combine requirements with `requireAll`, because
all emitted paths must be legal for the selected compilation world. Optimizer dead-code removal
does not change frontend inference.

`CAP-INF-002`: A compile-time branch whose condition is resolved for the current specialization
contributes only the selected branch. A dependent generic condition retains a conditional use in
the generic body and must be specialized before producing a concrete instantiation contract.

`CAP-INF-003`: Capability requirements flow from referenced declarations to the referencing
declaration. They never flow backward into the callee, nominal type, or standard-environment fact.
Provenance is a graph and may contain cycles; no mutable parent pointer is used as the source of
truth.

`CAP-INF-004`: An unreferenced source declaration does not contribute merely because it shares a
scope. Synthesized declarations contribute only when the synthesis rule makes them part of the
declaration's signature, body, witness map, or emitted `IRReady` node.

`CAP-INF-005`: Constructing a typed local call and resolving its overload set requires callable
signatures, the pre-inference ordinary requirement, and optional concrete availability only.
`InferCapabilities(caller)` is the sole owner of the `InferCapabilities(callee)` dependency edge. No
expression-checking or effective-contract query may insert a different-policy node into the
capability-inference SCC, and no concrete-availability proof creates such an edge.

## Target, stage, and compile-time selection

A concrete compilation request supplies a canonical `CompilationWorld`:

```text
CompilationWorld = {
    target: CapabilityAtom,
    stage: Option<CapabilityAtom>,
    supportedAtoms: WorldAtomSet,
    universe: CapabilityUniverseRevision
}
```

`supportedAtoms` is implication-closed and must agree with the target/stage key choices. Entry
point checking evaluates `world entails effective(entryPoint)` and reports a capability failure
before IR legalization. `WorldAtomSet` is intentionally distinct from `CapabilityAtomSet`: a world
retains its complete implication closure, while clause canonicalization removes weaker atoms that
are already implied.

`CAP-TGT-001`: A shader entry-point stage is an explicit capability use. A stage-independent
library function does not acquire a stage atom merely because one caller is an entry point.

Target/stage switches use first-match regions, including an explicit residual region for `default`:

```text
CapabilityBranchSelection = NodeList<{
    region: BooleanCapabilityPredicate,
    bodyRequirement: CapabilitySet,
    origin: Origin
}>
```

The predicate domain may use complement for selection even though exported requirements remain
positive DNF. For each valid world, the first satisfied region determines whether that world also
satisfies the selected body's requirement. The resulting set of valid worlds must be upward-closed
under atom support. Its minimal worlds are then canonicalized into positive DNF.

`CAP-TGT-002`: If selection produces a non-monotone valid-world set, it cannot be represented by a
positive capability contract and is diagnosed. Recovery uses `requireAll` of all reachable branch
requirements, which is conservative. A compiler must not silently approximate with
`allowEither`.

`CAP-TGT-003`: Exhaustiveness, overlap, and residual/default computation are relative to the
capability-universe revision in the query key. Adding a target or stage invalidates those results;
an old serialized module retains its original universe revision until explicitly migrated.

## Interfaces, class bases, extensions, and availability

Ordinary contract compatibility is directional. If an interface entry transmits ordinary
requirement `R_i` and its satisfying implementation requires `I_i`, every caller admitted by the
entry's promise must cover the implementation:

```text
R_i entails I_i
----------------------------- CAP-IFC-001
I_i may satisfy ordinary requirement R_i
```

This implication produces chapter 9's `InferredCapabilityCompatibilityObligation` and is validated
against the implementation's effective ordinary requirement after local inference. It is not a
selection-availability proof and does not inspect the current world assumption.

Concrete availability has a second, region-indexed judgment. Let `R_a` and `I_a` be the requirement
and implementation optional filters in universe `U`, and let `C` be the active requirement-match
region:

```text
C satisfies totalConcreteAvailability(R_a, U)
C satisfies totalConcreteAvailability(I_a, U)
---------------------------------------------------------------- CAP-IFC-004
I_a may satisfy R_a throughout C
```

The conclusion is retained as chapter 9's `ConcreteAvailabilityCompatibilityProof` with both
original options and two exact `CapabilityRegionAvailabilityProof` values. Across a conditional
witness map, the guarded regions must cover the requirement's availability domain, so an
implementation may be narrower globally only when other guarded satisfactions cover the remaining
regions. Neither compatibility field alters signature equality or witness identity, and the ordinary
proof cannot be substituted for either concrete proof even when their formulas happen to be equal.

`CAP-IFC-002`: A conformance's effective availability formula requires the conforming type,
interface, declared conformance condition, and the concrete availability of every synthesized
adapter or default body it needs. Ordinary inferred requirements are not folded into this selection
formula; witness-map entries retain them in their callable contracts so existential/witness dispatch
transmits the selected entry's keyed capability use.

`CAP-IFC-003`: Building a local requirement map compares the two pre-inference ordinary requirements
and records an `InferredCapabilityCompatibilityObligation`; it does not request the implementation's
inferred contract. It separately validates `ConcreteAvailabilityCompatibilityProof` from the two
optional filters. After all involved `InferCapabilities` queries stabilize, conformance validation
discharges the ordinary obligation using `effectiveCapabilities`. Imported satisfactions already
carry a published effective ordinary contract. Concrete availability is never pending on body
inference and never discharges the ordinary obligation.

`CAP-INH-001`: A class's effective contract must entail the effective contract of its representation
base, and an interface's effective contract must entail each refined interface it exposes. A
failure is attached to the typed class-base or refinement edge and does not mutate either contract.
No concrete struct-base edge exists in the proposed language.

`CAP-EXT-001`: Context-free extension matching proves target equality, generic/conformance
conditions, and reachability only. Context-dependent applicability then selects the canonical union
of the extension and target optional concrete-availability source sets in the lookup region. The
facet route retains the resulting applicability-evidence ID, so facets selected in different
boolean regions cannot alias merely because their intrinsic target/reachability evidence is equal;
caller-owned capability-use IDs do not enter that route identity. Committing a member candidate
constructs a separate `ExtensionFacetUseAt<S>` containing the distinct extension and optional target
ordinary inferred-capability uses. Those maps aggregate exactly once into the enclosing body and
each declared ordinary contract is validated after inference. An extension member may have narrower
concrete availability than the target only when the route evidence retains and proves that source;
candidate selection retains a failed concrete proof for diagnostics.

The current checker additionally requires equal abstract target/stage atoms in some class-base and
interface-refinement comparisons. The proposed rules replace that positional/keyhole check with logical
implication. Compatibility tests must identify any intended behavior not expressible by
`CAP-IFC-001` or `CAP-INH-001` before implementation freeze.

## Queries, recursion, and fixpoints

Capability checking is split into policy-homogeneous queries:

```text
DirectCapabilityUses = CapabilityUseGraph<Published>

CapabilityValidation =
    ValidDeclaredCapability(proof: CapabilityImplicationProof)
  | InvalidDeclaredCapability(failure: CapabilityFailure)
  | RecoveredCapabilityValidation(error: ErrorId)

CapabilityAvailability =
    AvailableInWorld(world: WorldAtomSet,
                     requirement: CapabilitySet,
                     supportingClause: CapabilityAtomSet)
  | UnavailableInWorld(failure: CapabilityFailure)
  | RecoveredAvailability(error: ErrorId)

CollectDirectCapabilityUses(body, context) -> DirectCapabilityUses
ComputeConcreteAvailability(declaration, modifiers, environment)
    -> CheckResult<Option<ConcreteAvailability>>
ResolveConcreteAvailability(subject, environment)
    -> QueryStep<Option<ResolvedConcreteAvailability>>
SelectCapabilitiesAt<S>(region, inferredUses, concreteSources)
    -> CheckResult<CapabilitySelectionAt<S>>
InferCapabilities(decl, specialization) -> InferredCapabilityRequirements
ValidateDeclaredCapability(decl, specialization) -> CapabilityValidation
EffectiveCapabilityRequirements(decl, specialization) -> EffectiveCallableContract
CheckWorldAvailability(use, world) -> CapabilityAvailability
```

The concrete-availability queries read headers and versioned registries but never bodies or inferred
contracts. `SelectCapabilitiesAt` is therefore a pre-inference applicability product and cannot add
an edge to the inference SCC. `CollectDirectCapabilityUses` depends on typed/elaborated uses and
callable signatures, but not on the declaration's inferred contract. `InferCapabilities(d)` requests
`InferCapabilities(c)` for
every local callee `c`, whether or not that edge is currently known to be cyclic. Both ends
therefore have the same least-fixpoint policy. It also requests the pre-inference declared contract
of `c`. Imported call uses are leaves containing their provider's already published effective
contract. No `InferCapabilities` query requests `EffectiveCapabilityRequirements`.

For an SCC of closed `InferCapabilities` queries, the scheduler uses the requirement-order least
fixpoint:

```text
x_d^0 = TrueFormula
x_d^(n+1) = joinReq(x_d^n,
                    directRequirements(d),
                    substituted(requireAll(declared(c), approximation(c)))
                        for each local call edge d -> c,
                    substituted(importedEffective(i))
                        for each imported call use i)

approximation(c) = current(InferCapabilities(c))  when c is in the current SCC
                 | published(InferCapabilities(c)) otherwise
```

`current(InferCapabilities(c))` is the SCC approximation supplied by `FixpointContext`;
requesting the ordinary published result from inside the SCC is invalid. `declared(c)` is
available before body inference. It participates in each call edge but is not used as `x_c^0`, so
validation still detects a body that needs more than it declared.

For a generic scheme, the same equations operate pointwise over the finite canonical decision
regions in `CapabilityRequirementExpr`; each leaf uses the closed-formula lattice. A newly discovered
predicate or call edge restarts dependency closure for the SCC epoch.

`CAP-FIX-001`: The transfer function is monotone under `<=req`. The universe is finite, so the
canonical-formula lattice is finite and iteration terminates. Implementations may use a canonical
BDD/shared DAG internally, but publication and equality obey canonical DNF semantics.

`CAP-FIX-002`: The scheduler restarts an SCC epoch when inference discovers a new in-SCC call edge,
and atomically publishes every member only after both dependency closure and formula values are
stable. Outside queries never observe an iteration approximation.

`CAP-FIX-003`: Recursive provenance records SCC edges without recursively nesting provenance
values. A diagnostic trace chooses the shortest stable path from the declaration to a failing
direct use.

`CAP-FIX-004`: A deterministic per-root term-growth and formula-complexity budget detects infinite
acyclic generic instantiation such as `F<N+1>`. Exceeding it returns recovered
`InferredCapabilityRequirements` data containing `ErrorCapabilityRequirement(error)`; it is not
reported as fixpoint convergence, inserted into the formula lattice, or widened unsafely.

Declared-contract validation runs only after inference stabilizes. Therefore an explicit
capability contract constrains/validates a recursive SCC but is not substituted as the SCC's
initial inferred value. `EffectiveCapabilityRequirements` then combines the stable declared/inferred
facts with the pure accessor above and has a one-way dependency on inference; because inference
never requests it, this post-fixpoint query cannot join the capability SCC.

## Diagnostics and recovery

Failures are structured values:

```text
CapabilityFailure = {
    kind: UnavailableUse | ConcreteCandidateUnavailable |
          DeclaredContractTooWeak | IncompatibleRequirements |
          InterfaceInferredContractMismatch |
          InterfaceConcreteAvailabilityMismatch |
          InheritanceContractMismatch | NonMonotoneSelection | InvalidUniverse,
    availableOrDeclared: CapabilitySet,
    requiredOrInferred: CapabilitySet,
    counterexample: Option<CapabilityCounterexample>,
    usePath: NodeList<CapabilityUsePathStep>,
    origin: Origin,
    rule: RuleId
}

CapabilityCounterexample = {
    failingSourceClause: CapabilityAtomSet,
    alternatives: NodeList<{
        requiredClause: CapabilityAtomSet,
        missingAtoms: CapabilityAtomSet
    }>
}
```

`CAP-DIAG-001`: For a failed implication, choose the smallest canonical source clause for which no
target clause is entailed. For each target alternative, report its non-implied atoms after removing
atoms implied by another missing atom. Stable atom order, not hash-table or scheduling order,
selects the primary diagnostic.

`CAP-DIAG-002`: The primary diagnostic names the declaration/use and failed contract relation.
Related locations follow the shortest capability-use path and end at direct operations,
attributes, or external contracts. A recursive edge appears at most once in the rendered trace.

`CAP-DIAG-003`: An inaccessible declaration and an unavailable declaration are distinct overload
failures. If all name candidates are inaccessible, visibility owns the primary diagnostic. If an
accessible candidate fails its optional concrete availability, the
`ConcreteCandidateUnavailable` failure is retained for the best-failed-candidate diagnostic. An
ordinary inferred requirement that is not implied by the current symbolic region is not a candidate
failure and therefore cannot be ranked as one.

`CAP-DIAG-004`: Error recovery never turns a concretely unavailable candidate into an applicable one.
`ErrorCapabilityRequirement` suppresses derivative diagnostics carrying the same `ErrorId`; a
module with it in an exported effective contract is not successfully publishable.

Visibility diagnostics similarly use `VisibilityFailure` values containing the declaration,
access context or exposed field path, actual/required visibility, import path, origin, and rule ID.

```text
VisibilityFailure = {
    declaration: DeclId,
    context: Option<VisibilityContext>,
    exposedPath: Option<SemanticFieldPath>,
    actual: DeclVisibility,
    required: DeclVisibility,
    importPath: Option<ImportPath>,
    origin: Origin,
    rule: RuleId
}
```

## Determinism, serialization, and open-world behavior

`CAP-DET-001`: Capability formulas serialize using stable atom IDs, canonical clause order, and the
universe content hash. Generated enum values, pointer identities, insertion order, and target
driver enumeration order are absent from the wire form.

`CAP-DET-002`: Deserializing under the identical universe revision preserves canonical bytes.
Migrating to a new universe resolves atoms by stable name, re-expands named aliases, revalidates
keyholes, and re-canonicalizes. Migration failure is explicit; unknown atoms are not discarded.

`CAP-DET-003`: The capability universe is closed for one compilation snapshot and open between
revisions. Adding an implication edge, incompatibility edge, alias expansion, target, or stage
changes the universe hash and invalidates every formula operation that depends on it. It does not
retroactively reinterpret cached module artifacts.

`VIS-DET-001`: `DeclVisibility` and exposure results serialize declaration IDs, module identities,
semantic field paths, and module-graph revision. Reordering independent declarations, imports with
equivalent reachability, or parallel tasks cannot change their bytes or diagnostics.

## Pure primitives and unit-test seams

The remaining primitive inputs and results are closed serializable values:

```text
ExportEnvironment = {
    exportingModule: ModuleId,
    reachableModules: ModuleReachabilityId,
    requiredVisibility: DeclVisibility,
    moduleGraph: ContentId<ModuleGraph>,
    schema: SchemaVersion
}

ExposureValidation =
    ExposureValid(footprint: VisibilityFootprint)
  | ExposureInvalid(failures: NonEmpty<VisibilityFailure>)

UniverseValidationFailure =
    DuplicateCapabilityIdentity(ContentId<SchemaValue>)
  | UnknownCapabilityReference(ContentId<SchemaValue>)
  | CyclicCapabilityAlias(cycle: NonEmpty<CapabilityName>)
  | InvalidImplicationEndpoint(atom: CapabilityAtom)
  | InvalidIncompatibilityEndpoint(atom: CapabilityAtom)
  | InvalidKeyhole(keyhole: KeyholeId)
  | UnsatisfiableStandardProfile(name: CapabilityName)
  | DerivedUniverseMismatch(field: FieldName)

UniverseValidation =
    ValidUniverse(revision: CapabilityUniverseRevision)
  | InvalidUniverse(failures: NonEmpty<UniverseValidationFailure>)

NonMonotoneRegion = {
    acceptedWorld: WorldAtomSet,
    rejectedExtension: WorldAtomSet,
    predicate: BooleanCapabilityPredicate
}
```

`acceptedWorld` is a subset of `rejectedExtension`, the predicate accepts the former and rejects
the latter, and both are valid worlds in the same universe. It is therefore a replayable witness
that positive-DNF upward closure failed, not an implementation-specific BDD node.

The following functions are public frontend primitives and accept only immutable values:

```text
meetVisibility(DeclVisibility, DeclVisibility) -> DeclVisibility
decideVisibility(DeclVisibilityFact, VisibilityContext, ModuleGraph) -> VisibilityDecision
computeVisibilityFootprint(SchemaValue, NodeSchemaRegistry) -> VisibilityFootprint
validateExposure(DeclId, DeclSurface, ExportEnvironment) -> ExposureValidation

validateUniverse(CapabilityUniverse) -> UniverseValidation
canonicalize(CapabilitySet, CapabilityUniverse) -> CapabilitySet
entails(CapabilitySet, CapabilitySet, CapabilityUniverse) -> Bool
requireAll(CapabilitySet, CapabilitySet, CapabilityUniverse) -> CapabilitySet
allowEither(CapabilitySet, CapabilitySet, CapabilityUniverse) -> CapabilitySet
explainImplicationFailure(...) -> CapabilityCounterexample
validateDeclaredContract(...) -> CapabilityValidation
canonicalizePredicate(CapabilityPredicateExpr, CapabilityUniverse)
    -> BooleanCapabilityPredicate
projectPositive(BooleanCapabilityPredicate, CapabilityUniverse)
    -> Result<CapabilitySet, NonMonotoneRegion>
specializeCapabilityScheme(CapabilityScheme, SpecializationFrame)
    -> CapabilityRequirement
combineConcreteAvailability(NonEmpty<ResolvedConcreteAvailability>)
    -> CapabilityRequirement
SelectCapabilitiesAt<S>(BooleanCapabilityPredicate,
                        CanonicallyOrderedMap<CapabilityUseId, CapabilityUse<S>>,
                        NodeList<ResolvedConcreteAvailability>)
    -> CheckResult<CapabilitySelectionAt<S>>
effectiveCapabilities(EffectiveCallableContract) -> CapabilitySet
```

None of these functions loads a module, checks a body, reads a global target, or emits a
diagnostic. Query adapters gather those inputs and convert failure values into diagnostics.

Representative isolated tests use these fakes:

```text
FakeDeclVisibilityFacts {
    visibility(PublicAPI) -> Public
    visibility(HiddenType) -> Internal
    privateOwner(secret) -> TypeOwner(S)
}

FakeCapabilityUniverse {
    sm_6_7 implies sm_6_6 implies hlsl
    glsl incompatible hlsl
    rayTracing = (hlsl and sm_6_3) or (spirv and SPV_KHR_ray_tracing)
}

FakeCapabilityUses {
    DirectUses(f) -> { use(g), use(doubleOperation) }
    EffectiveContract(g) -> hlsl and waveOps
}
```

Required direct suites include:

- every visibility default/inheritance rule and each invalid modifier location;
- public/internal/private access across same/different modules, namespaces, nested functions,
  nominal types, generic extensions, and synthesized function extensions;
- recursive footprints for every semantic type/value constructor and each exposure role;
- public-surface exported-import failures, default arguments, aliases, attributes, opaque inline
  bodies, and synthesized declarations;
- universe validation for aliases, implication SCCs, keyholes, incompatibility closure, and stable
  IDs;
- `TrueFormula`/`FalseFormula`, every canonicalization step, implication counterexamples, and all
  lattice/distributive laws;
- Boolean-region complement, overlap splitting, coverage, upward-closure projection, and a
  non-projectable negative region;
- generic capability-scheme substitution, residual `IfConst`, unreachable paths, and deferred
  entailment obligations;
- declared weaker/equal/stronger than inferred contracts;
- ordinary callable requirements that create exactly one caller use without filtering candidates,
  versus absent/present concrete availability with exact subject/source sets and region proofs;
- declaration, registered-standard-operation, and language-rule concrete-availability resolution;
  multiple-source composition, duplicate elimination, explicit `TrueFormula` preservation, and
  mutations of source, combined-requirement, universe, region, and proof endpoints;
- extension intrinsic evidence reused across regions, route evidence that distinguishes concrete
  regions without caller-use identity, and committed extension-facet ordinary uses aggregated once;
- interface ordinary-requirement compatibility and concrete-availability compatibility as distinct
  proof families, including equal formulas that cannot exchange proof roles;
- ordinary runtime branches versus compile-time and target/stage selections;
- interface, inheritance, extension, and capability-specialized overload directions;
- self and mutual recursive call-graph fixpoints, newly discovered edges, and acyclic generic
  growth limits, including an assertion that no effective-contract query enters the SCC;
- one-worker/many-worker, insertion-order, serialization, migration, and universe-revision
  determinism; and
- diagnostics with multiple alternatives and cyclic provenance.

`TST-CAP-001`: Algebra property tests generate small validated universes as well as formulas. A
test over arbitrary atom graphs is invalid because the algebra assumes the universe invariants.

`TST-CAP-002`: Every capability-inference rule test asserts the exact direct-use facts and query
dependencies requested. Scheduler convergence is tested separately with artificial lattices and
then with the capability requirement lattice.

`TST-CAP-003`: Every `CapabilitySelectionAt<S>` producer is schema-tested with zero, one, and
multiple ordinary uses and concrete sources. Tests mutate one field at a time and require rejection
for a wrong use-map key, missing/extra source, stale combined requirement, wrong region/proof
endpoint, cross-universe source, or a `NoConcreteAvailability`/nonempty-source mismatch. Merging two
selections is tested for identical-region associativity and for structured rejection of different
regions or inconsistent equal use IDs.

`TST-VIS-001`: Schema coverage fails when a new semantic operand has no exposure-role annotation.
Visibility tests therefore cover new type/value constructors even before an end-to-end language
feature test happens to instantiate them.

## Compatibility evidence and decisions

The current implementation is primarily in `source/slang/slang-capability.{h,cpp}`,
`source/slang/slang-capabilities.capdef`, capability checking in
`source/slang/slang-check-decl.cpp`, and visibility checking in
`source/slang/slang-check-{expr,modifier,decl}.cpp`. Its `CapabilitySet::join` approximates
conjunction, `unionWith` approximates disjunction, and `nonDestructiveJoin` preserves incompatible
alternatives. The new names above state the logic rather than the storage mutation.

Before accepting this chapter, differential tests must resolve these explicit compatibility
questions in chapter 13:

1. whether enclosing/local capability attributes use strict logical conjunction or preserve
   incompatible local target alternatives;
2. whether current abstract-target/stage equality checks express an intended rule beyond logical
   contract implication;
3. the complete default-visibility table for namespaces, nested declarations, and every
   synthesized declaration family; and
4. which target/capability switch predicates can produce a non-monotone valid-world set in current
   source and how those cases should be diagnosed.

They are review decisions, not implementation freedom. Once accepted, the named rules and their
manifest tests are the language contract.
