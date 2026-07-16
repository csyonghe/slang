# Centralized semantic work scheduler

Semantic checking is defined as a graph of typed queries. Query implementations declare
dependencies; a centralized scheduler owns evaluation, memoization, cycle handling, diagnostics,
parallel execution, cancellation, and incremental invalidation. A query must never recursively
invoke another checker through an ad hoc side channel.

This replaces the current per-declaration `DeclCheckState` ladder and recursive `ensureDecl` model
in `source/slang/slang-ast-support-types.h` and `source/slang/slang-check-decl.cpp`. Those mechanisms
correctly identify useful readiness boundaries, but combine semantic facts, mutation, execution
state, and cycle detection in one byte on each declaration.

## Query model

```text
IncludeRequestKey = {
    includingFile: SourceFileId,
    spelling: Utf8String,
    searchConfiguration: ContentId<SchemaValue>
}

IncludeResolution = Found(SourceFileId) | NotFound

SourceGraph = {
    documents:
        CanonicallyOrderedMap<SourceFileId, SourceFileSnapshotId>,
    includeResolution:
        CanonicallyOrderedMap<IncludeRequestKey, IncludeResolution>,
    externalMacroEnvironment: ContentId<SchemaValue>
}

FrontendOptions = {
    lex: LexOptions,
    preprocessing: PreprocessorDesc,
    syntaxFeatures: SyntaxFeatureSet,
    parsing: ParserOptions,
    semanticOptions: CanonicalArguments
}

QueryKind = {
    stableName: QualifiedName,
    wireTag: UInt32,
    protocolVersion: UInt16
}

QueryKindDescriptor = {
    kind: QueryKind,
    keySchema: ContentId<SchemaValue>,
    resultSchema: ContentId<SchemaValue>
}

QueryKindRegistry = {
    schema: SchemaVersion,
    descriptors: CanonicallyOrderedMap<QueryKind, QueryKindDescriptor>
}

EnvironmentRevision = {
    sourceGraph: ContentId<SourceGraph>,
    frontendOptions: ContentId<FrontendOptions>,
    languageRules: LanguageRuleSetId,
    standardEnvironment: StandardEnvironmentId,
    moduleGraph: ContentId<ModuleGraph>,
    schema: SchemaVersion,
    effectUniverse: EffectUniverseRevision,
    capabilityUniverse: CapabilityUniverseRevision
}

QueryKey = {
    kind: QueryKind,
    subject: StableSemanticId,
    arguments: CanonicalArguments,
    environment: EnvironmentRevision
}

DependencyRole = SignatureOf | LookupIn | TypeOf | ConstraintOf | WitnessFor |
                 CapabilityOf | BodyOf | LoweredFormOf | Other(FieldName)

DependencyKey = {
    query: QueryKey,
    role: DependencyRole
}

DependencyRequest = {
    key: DependencyKey,
    origins: CanonicallyOrderedSet<Origin>
}

DependencySet = CanonicallyOrderedMap<DependencyKey, DependencyRequest>
RuleIdSet = CanonicallyOrderedSet<RuleId>

QueryResult<T> =
    Ready(CheckResult<T>)
  | Waiting(DependencySet)
  | Running(TaskId)
```

`SCH-KEY-000`: `QueryKind` equality is exact equality of stable name, wire tag, and protocol
version. A registry map key equals its descriptor's `kind`; stable names and wire tags are each
unique within one registry, and the key/result schema IDs resolve in that registry's schema
environment. Changing key or result encoding allocates a new protocol version; changing only the
query implementation does not change the kind and is tracked by the cache implementation stamp.
`QueryKey` and `DurableQueryIdentity` store the same registered kind, so an implementation enum,
function address, or registration order can never become query identity.

`ExpressionCheckContext` and `StatementCheckContext` are defined once in chapter 6. They are
immutable, canonically serialized values, and their IDs are mandatory key arguments for expression
and statement queries; a syntax-node ID alone does not determine a checked result. The surrounding
`environment` key field supplies the source revision, language/options revision, target-independent
standard environment, and module graph. Two contexts may be interned together only when every
semantic field is equal.

A `QuerySpec<K, V>` declares:

```text
QuerySpec = {
    keyKind: K,
    valueKind: V,
    execute: PureQueryFunction<K, V>,
    cyclePolicy: CyclePolicy<V>,
    durability: SourceLocal | ModuleInterface | StandardEnvironment | Target,
    validationRules: RuleIdSet
}

QueryStep<T> = Complete(CheckResult<T>) | Blocked(DependencySet)
```

Query functions receive only immutable inputs and a `QueryContext`:

```text
QueryContext = {
    request<K, V>(key: K) -> Need<V>,
    source(id: SourceFileSnapshotId) -> SourceFileSnapshot,
    standardEnvironment(id: StandardEnvironmentId) -> SchemaValue,
    options() -> FrontendOptions,
    cancellation() -> CancellationToken
}

Need<T> = Available(CheckResult<T>) | Pending(QueryKey)

CancellationToken = opaque execution-only shared handle
CancellationObservation = ContinueExecution | CancellationRequested

pollCancellation(CancellationToken) -> CancellationObservation
```

`CancellationToken` belongs to the scheduler invocation, not the language model. It is shareable
among worker tasks but has no structural fields, canonical encoding, equality, hash, or serialized
form. It cannot occur in a `QueryKey`, dependency edge, `CheckResult`, diagnostic, AST/semantic
snapshot, or durable-cache entry, and a query may interact with it only through
`pollCancellation`. Observing `CancellationRequested` abandons the unpublished query attempt; it
does not manufacture an error node or a user diagnostic. An already atomically published result
remains valid because its value is independent of whether a later caller cancels.

If a dependency is pending, the query function returns `Blocked` with all currently known
requirements. It
does not recurse on the C++ stack. The scheduler records graph edges and resumes the task when its
requirements publish results.

A completed dependency always arrives as its total `CheckResult`; recovery is semantic data, not a
third scheduler state. A query explicitly propagates, transforms, or contains that recovery while
merging its structured diagnostics. `DependencyRequest.origins` is duplicate-free and canonically
ordered, so requesting the same semantic edge from multiple syntax sites does not make discovery
order observable.

`SCH-QRY-001`: A semantic fact has exactly one canonical query key and one producing query kind.

`SCH-QRY-002`: Query equality and hashing depend only on stable, serialized input identity.

`SCH-QRY-003`: Query code may request facts but may not inspect or mutate scheduler internals.

`SCH-QRY-004`: An `EnvironmentRevision` is valid only when all repeated configuration references
agree exactly: `frontendOptions.lex.languageRules`,
`frontendOptions.preprocessing.languageRules`, and
`frontendOptions.syntaxFeatures.languageRules` equal `languageRules`; resolving that rule set yields
the same `standardEnvironment`; and the registered standard-environment schema exports the stored
effect- and capability-universe revisions. Contradictory combinations are rejected during key
construction, so they cannot create a second semantic configuration or enter the query cache.

## Core query families

The first implementation must expose at least these independently callable query families:

| Family                                                            | Representative output                                                                |
| ----------------------------------------------------------------- | ------------------------------------------------------------------------------------ |
| `ParseFile`                                                       | `LosslessCST`                                                                        |
| `BuildSurfaceAST`                                                 | `ASTSnapshot<Surface>`                                                               |
| `BuildFragmentScopes`                                             | `(ASTSnapshot<Scoped>, FragmentScopeGraph)`                                          |
| `FreezeDeclIndex`                                                 | `FrozenDeclIndex` (including `FrozenScopeGraph`)                                     |
| `ClassifyModifiers`                                               | `CheckedModifierSet`                                                                 |
| `BindDeclHeader`                                                  | `DeclHeader`                                                                         |
| `LookupName` / `LookupMember`                                     | `LookupResult`                                                                       |
| `DeclareNominalIdentity` / `BuildNominalDefinition`               | `DeclId` / `NodeRef<Typed, Decl>`                                                    |
| `ExpandTypeAlias` / `CanonicalizeStructuralType`                  | `TypeId`                                                                             |
| `BuildCallableSignature`                                          | `CallableSignature`                                                                  |
| `InferGenericArguments`                                           | `GenericSolution`                                                                    |
| `PlanCoercion`                                                    | `ConversionResult`                                                                   |
| `ResolveOverload`                                                 | `OverloadResult`                                                                     |
| `CheckExpression(node, ExpressionCheckContextId)`                 | `TypedExpr`                                                                          |
| `AssignSemanticOperationSite` / `ValidateSemanticOperationSite`   | `SemanticOperationSiteAssignment` / `Unit`                                           |
| `AssignPhysicalProjectionSite` / `ValidatePhysicalProjectionSite` | compatibility aliases of the semantic-operation-site queries                         |
| `ValidateBuiltinPhysicalProjectionAt<S>`                          | `BuiltinPhysicalProjectionValidationResultAt<S>`                                     |
| `ValidateRegisteredPhysicalProjectionAt<S>`                       | `RegisteredPhysicalProjectionValidationResultAt<S>`                                  |
| `BuildPhysicalProjectionApplicationIndex`                         | `PhysicalProjectionApplicationIndex`                                                 |
| `CheckReferenceFormation` / `CheckDereference`                    | `ReferenceFormationResult` / `DereferenceResult`                                     |
| `ResolveReferenceSyntaxPolicy`                                    | `Result<ReferenceSyntaxPolicy, ReferenceSyntaxPolicyFailure>`                        |
| `ValidateReferenceAccessorInvocationAt<S>`                        | `ReferenceAccessorInvocationResultAt<S>`                                             |
| `InstantiateAccessorReferenceResultAt<S>`                         | `Result<AccessorReferenceResultCertificate, AccessorReferenceResultContractFailure>` |
| `AdmitAccessorHandle`                                             | `Result<AccessorHandleAdmissionProof, PointerLikeValidationFailure>`                 |
| `PlanStorageAccessAt<S>`                                          | `StorageAccessResultAt<S>`                                                           |
| `PublishPhysicalProjectionSemanticResults`                        | `PhysicalProjectionSemanticResultSnapshotId`                                         |
| `ResolveOverloadableResultAuthorityAt<S>`                         | `CallableResultAuthorityId`                                                          |
| `BuildTypedCall` / `BuildSelectedSurfaceTypedCallAt<S>`           | `TypedCallAt<S>`                                                                     |
| `CheckStatement(node, StatementCheckContextId)`                   | `NodeRef<Typed, Stmt>`                                                               |
| `BuildInitializationModel` / `ResolveInitialization`              | `InitializationModel` / `InitializationResult`                                       |
| `ComputeFacets`                                                   | `FacetSet`                                                                           |
| `DeclareWitnessTableIdentity`                                     | `WitnessTableId`                                                                     |
| `FindConformance`                                                 | `ConformanceSearchResult`                                                            |
| `BuildRequirementDictionary`                                      | `ProvisionalRequirementDictionary`                                                   |
| `ValidateConformanceEffects`                                      | `EffectValidatedRequirementDictionary`                                               |
| `ValidateConformanceCapabilities`                                 | `CapabilityValidatedRequirementDictionary`                                           |
| `CombineRequirementDictionaryValidation`                          | `FullyValidatedConstructionRequirementDictionary`                                    |
| `BuildWitnessTableDefinition`                                     | `WitnessTableDefinitionPublication`                                                  |
| `InferEffects`                                                    | `InferredEffectContract`                                                             |
| `ValidateDeclaredEffects`                                         | `EffectValidation`                                                                   |
| `InferCapabilities`                                               | `InferredCapabilityRequirements`                                                     |
| `ComputeConcreteAvailability` / `ResolveConcreteAvailability`     | `Option<ConcreteAvailability>` / `Option<ResolvedConcreteAvailability>`              |
| `SelectCapabilitiesAt<S>`                                         | `CapabilitySelectionAt<S>`                                                           |
| `ComputeDeclaredVisibility`                                       | `CheckResult<DeclVisibilityFact>`                                                    |
| `BuildDifferentialInfo` / `BuildCallableDifferentialShape`        | `DifferentialInfoResult` / `CallableDifferentialShapeResult`                         |
| `ResolveDerivativeProvider` / `CheckDifferentiation`              | `DerivativeProviderResult` / `DifferentiationCheckResult`                            |
| `ElaborateDecl`                                                   | `ElaboratedDeclAt<Published>`                                                        |
| `BuildIRReadyDecl`                                                | `IRReadyDecl`                                                                        |
| `DeclareIRSymbol`                                                 | `IRSymbolDecl`                                                                       |
| `LowerIRDefinition`                                               | `IRDefinition`                                                                       |

Small primitives such as argument mapping, candidate comparison, unification, capability
implication, and visibility meet are pure library functions below query granularity. They remain
directly unit-testable without a scheduler.

## Dependency discovery

Queries run in two logical steps even if an implementation fuses them:

1. **discover** reads immutable local syntax and requests all facts needed to make progress;
2. **compute** runs after those facts are available and constructs the immutable output.

Discovery may itself reveal new dependencies after earlier facts arrive. The scheduler records a
monotonic dependency set for a given execution attempt. If a query's dependency set would shrink or
change based on task race order, the query is nondeterministic and invalid.

Dependencies have semantic labels:

```text
DependencyEdge = {
    from: QueryKey,
    to: QueryKey,
    role: DependencyRole,
    origin: Origin
}
```

Each `ContentId` field names a canonically serialized immutable input graph and carries chapter 1's
exact discriminator; loading it resolves and verifies the exact bytes, so a digest collision is
never accepted as equality. The language-rule and standard-environment IDs obey the same rule.
Target-world facts that vary within one target-independent frontend environment are explicit
`CanonicalArguments` (for example `WorldAtomSet`), not ambient process state. An environment value
changes exactly when a query could observe a changed source/options/rule/standard-module/module-
graph/schema/universe input.

Labels produce understandable cycle diagnostics and allow targeted invalidation.

## Cycle policies

Cycles are properties of semantic domains, not one generic error case.

```text
CyclePolicy<T> =
    Reject(makeDiagnostic, makeRecovery)
  | NominalKnot(allocateIdentity, completeDefinition)
  | LeastFixpoint(domain: FiniteJoinSemilattice<T>, transfer)
  | GreatestFixpoint(domain: FiniteMeetSemilattice<T>, transfer)
  | Coinductive(validateGuardedCycle, provisionalValue)
```

Every query kind declares exactly one policy. Falling back to `Reject` without a rule is forbidden.
Query kinds are split until all values produced by one kind have the same policy. A broad kind such
as `CanonicalType` is invalid because nominal identity, alias expansion, and structural
canonicalization have different cycle behavior.

The initial policy assignment is normative:

| Query kind                                                                                                        | Policy                                                                         | Reason/recovery                                                                                                                                         |
| ----------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| parse, bind a finite syntax node, check an expression/statement                                                   | `Reject`                                                                       | the source tree is finite; recover at the offending node                                                                                                |
| `DeclareNominalIdentity`                                                                                          | `NominalKnot`                                                                  | publish identity without requesting its definition                                                                                                      |
| `BuildNominalDefinition`                                                                                          | `Reject` across definition edges                                               | recursive fields refer to nominal identities, not nested definitions                                                                                    |
| `ExpandTypeAlias`, default generic argument, constant evaluation                                                  | `Reject`                                                                       | these denote finite values; publish an error value                                                                                                      |
| class representation-base closure                                                                                 | `Reject`                                                                       | a class has one acyclic base chain; no struct-base relation is admitted                                                                                 |
| interface-refinement closure                                                                                      | `Reject`                                                                       | a refinement cycle has no productive witness lookup; retain an error path for diagnostics                                                               |
| facet-route closure                                                                                               | `Reject` for route cycles; `Blocked` is an ordinary result, not a cycle policy | compute class, interface, witness, and extension routes separately; never publish a shortened closure                                                   |
| function/callable signature                                                                                       | `Reject`                                                                       | recursion passes through declaration or nominal identity, never an incomplete signature                                                                 |
| `BuildInitializationModel`, `ResolveInitialization`                                                               | `Reject`                                                                       | models and selected nested plans are finite; recursive values cross nominal/callable identities rather than embedding an incomplete initialization plan |
| `DeclareWitnessTableIdentity`                                                                                     | `NominalKnot`                                                                  | publish the identity independently of its requirement dictionary                                                                                        |
| conformance selection/witness-table definition                                                                    | `Reject` unless a named productive witness rule applies                        | requirement edges may store witness-table IDs without forcing their definitions                                                                         |
| effect inference                                                                                                  | `LeastFixpoint`                                                                | monotonically union direct and callee effect atoms per finite generic-path partition                                                                    |
| capability inference                                                                                              | `LeastFixpoint`                                                                | monotonically accumulate required alternatives                                                                                                          |
| `BuildDifferentialInfo`, `BuildCallableDifferentialShape`, `TransformDerivativeSignature`, `CheckDifferentiation` | `Reject`                                                                       | canonical types/signatures and finite syntax are finite; recursion crosses nominal identities or witness IDs                                            |
| derivative body activity                                                                                          | `LeastFixpoint`                                                                | finite per-storage activity states monotonically join over the control-flow graph                                                                       |
| `ResolveDerivativeProvider`                                                                                       | `Reject` for proof cycles                                                      | recursive generated calls target separately declared derivative identities; the completed value retains every considered candidate and comparison proof |
| `DeclareAggregateDifferentialIdentity`                                                                            | `NominalKnot`                                                                  | reserve synthesized differential-type and witness-table identities before definitions                                                                   |
| `BuildAggregateDifferential`                                                                                      | `Reject` across definition edges                                               | recursive references use the declared identities, never incomplete plans                                                                                |
| declared/effective effect validation                                                                              | `Reject`                                                                       | consumes stabilized inference; it is outside the inference SCC                                                                                          |
| effective visibility                                                                                              | `GreatestFixpoint` over `Private < Internal < Public`                          | start at `Public` and monotonically meet referenced visibility                                                                                          |
| synthesis planning                                                                                                | `Reject`                                                                       | recursive references target identities allocated by the synthesis group                                                                                 |
| `DeclareIRSymbol`                                                                                                 | `NominalKnot`                                                                  | publish stable symbol declaration independently of its body                                                                                             |
| `LowerIRDefinition`                                                                                               | `Reject`                                                                       | recursive references target already declared IR symbols                                                                                                 |

Adding a query kind requires adding one row, recovery behavior, a cycle witness test, and a
termination argument to the rule manifest.

### Rejected cycles

Type aliases, class-base or base-interface edges, default generic arguments that depend on
themselves, and constant values are finite definitions. A strongly connected component (SCC)
containing a self-dependency
in one of these query families produces one primary cycle diagnostic plus ordered edge notes.

```text
cycle(q)    policy(q) = Reject(diag, recovery)
------------------------------------------------ SCH-CYCLE-001
publish(q, Recovered(recovery(cycle),
                     { errorId(diag(cycle)) },
                     singletonDiagnosticSet(diag(cycle))))
```

The recovery type must break the cycle explicitly, usually with an `ErrorType`, `ErrorValue`, or
empty-base set tagged with the cycle's `ErrorId`.

### Nominal knots

A nominal declaration has identity before its representation is known. `struct Node { Node* next; }`
does not require an infinitely nested type: the field type refers to `DeclId(Node)`. The scheduler
may publish the nominal identity, then complete the separate definition query.

`SCH-CYCLE-010`: Nominal-knot handling is permitted only across an identity query and definition
queries. Structural aliases do not become nominal merely to escape a cycle error.

### Least fixpoints

Capability inference and other may-require analyses are monotone accumulation problems. For an SCC
`S = {q1 ... qn}` with finite-height join semilattice `(L, ≤, ⊔, ⊥)`, initialize every result to
`⊥` and repeatedly apply the transfer functions until no result changes:

```text
x_i^0 = ⊥
x_i^(k+1) = x_i^k ⊔ F_i(x_1^k, ..., x_n^k)
```

`SCH-FIX-001`: A least-fixpoint query must document a finite-height domain or a deterministic
widening operator. The scheduler diagnoses non-convergence rather than iterating forever.

`SCH-FIX-002`: Transfer functions must be monotone. Debug builds and property tests check sampled
`x ≤ y => F(x) ≤ F(y)` cases.

For mutually recursive functions, capability requirements start at `true`/no additional
requirement and accumulate requirements from bodies and callees until stable.

Effect inference uses `EffectSet` directly for a complete specialization. For a generic SCC, a
discovery pass first collects the finite set of canonical `IfConstEffect` predicates reachable from
the SCC bodies and declared/imported callee schemes, computes their finite satisfiable path
partition under the binder constraints, and freezes those path keys. The fixpoint lattice is then a
finite map from path key to `EffectSet`, ordered and joined pointwise; after convergence the map is
reassembled into canonical `EffectScheme`. Discovery that reveals another predicate enlarges the
SCC domain and triggers the same discard/restart rule as a new dependency edge. A transfer may not
invent ever-larger symbolic predicates during iteration.

`SCH-FIX-003`: Effect-scheme path partitioning is deterministic and independent of source/callee
iteration order. Every recursive effect transfer is monotone in the frozen pointwise domain; an
unbounded predicate/key expansion is handled by `SCH-TERM-001/002`, never by inserting an error atom
into the effect lattice.

During iteration a transfer function receives an explicit approximation view:

```text
FixpointContext<L> = {
    current(member: QueryKey) -> L,
    requestExternal(key: QueryKey) -> Need<SchemaValue>,
    reportDependency(key: QueryKey, role: DependencyRole) -> Unit
}
```

Requests to another member of the active component read `current(member)`; they never return
`Pending` and never inspect a half-published cache entry. Requests outside the component use the
ordinary query interface. The transfer result is joined or met with the current approximation by
the scheduler, not destructively installed by query code.

### Greatest fixpoints and coinduction

Greatest fixpoints are reserved for properties meaning “valid unless disproved” and require an
explicit finite meet domain. Coinduction is reserved for guarded recursive semantic objects such as
future recursive function values; it cannot be selected merely because a least fixpoint is
inconvenient.

The initial frontend design does not assign ordinary interface conformance to coinduction. A cycle
of conformance proofs is accepted only if a named rule supplies a productive declared witness; a
chain consisting solely of “I conform because I conform” is rejected.

## SCC evaluation algorithm

The scheduler maintains the dynamic dependency graph and uses an incremental SCC algorithm. When a
new edge closes a cycle:

1. compute the current transitive SCC closure in stable key order;
2. initialize the policy-specific recovery, identity, or approximation values;
3. evaluate through `FixpointContext` where applicable;
4. if discovery adds an edge that enlarges or merges the SCC, discard unpublished approximations,
   recompute the closure, and restart the component in stable key order;
5. reject an SCC containing incompatible policies unless a bridge rule explicitly separates
   provisional identity from definition;
6. run the selected reject/knot/fixpoint/coinductive solver to convergence;
7. publish all SCC results atomically; and
8. resume outgoing dependents in stable `QueryKey` order.

`SCH-CYCLE-020`: An SCC result is atomic. No task outside the SCC observes half of a fixpoint
iteration or a partially built witness map.

`SCH-CYCLE-021`: Cycle diagnostics report the shortest deterministic semantic edge cycle, followed
by any additional SCC members as notes. “Cyclic reference” without the dependency roles is
insufficient.

## Unbounded query-key growth

An infinite computation need not contain a repeated query key. For example, a malformed generic
rule can request `F<N + 1>` from `F<N>` forever, producing an acyclic but unbounded dependency path.
The scheduler therefore tracks per-root semantic expansion traces in addition to graph cycles:

```text
ExpansionTrace = {
    root: QueryKey,
    ancestors: NodeList<QueryKey>,
    termMeasures: NodeList<SemanticTermMeasure>,
    generatedKeyCount: UInt64
}
```

`SCH-TERM-001`: Each query family that can synthesize larger keys declares a structural term
measure and a well-founded decrease rule. Repeated constructor growth with no declared decreasing
component is diagnosed as `NonTerminatingSemanticExpansion`, with the shortest repeating growth
pattern as notes.

`SCH-TERM-002`: A deterministic per-root key-count and term-size ceiling is the final resource
backstop for cases the structural detector cannot prove. It is based only on serialized semantic
size and configured frontend limits, never wall-clock time, task order, or worker count. Hitting the
ceiling publishes the query kind's typed recovery value and one stable resource-limit diagnostic.

Cycle detection, growth detection, and resource limits share diagnostic ancestry but remain
distinct outcomes; an SCC algorithm alone is not claimed to solve unbounded specialization.

## Determinism and parallelism

Ready tasks may execute in parallel. Observable ordering is recovered at publication boundaries:

- immutable maps use canonical key order;
- overload candidates retain language-defined lookup order and stable declaration tie-breakers;
- diagnostics use the order in chapter 1;
- synthesized declaration IDs derive from the causing rule and semantic inputs, not task order; and
- fixpoint worklists pop the smallest stable query key first.

`SCH-DET-001`: Running with one worker and with `N` workers produces byte-identical serialized AST,
semantic facts, diagnostics, and frontend IR.

## Cancellation and failures

Cancellation is not a semantic result and is never cached as one. A cancelled task releases its
published-nothing state; dependents remain pending or are cancelled by their caller. Internal
compiler failures are captured with the query key and dependency stack, but are not converted to a
user language diagnostic.

Recovered user errors are cacheable because they are deterministic for their inputs. A downstream
query receives both the typed recovery value and the originating `ErrorId`, allowing it to suppress
cascades while continuing unrelated work.

## Incremental invalidation

The full `EnvironmentRevision` in an execution `QueryKey` is a correctness namespace: it prevents a
result from being mistaken for one computed in another source/module graph. Cross-revision reuse is
performed through a separate durable identity and red-green validation, not by weakening that key:

```text
DurableSyntaxLineageKey = {
    file: SourceFileId,
    initialAnchor: ContentId<SchemaValue>,
    initialRolePath: NodeList<FieldName>,
    initialOccurrence: UInt32
}

DurableSyntaxLineageId = ContentId<DurableSyntaxLineageKey>

DurableSubjectIdentity =
    SourceFileLineage(SourceFileId)
  | SyntaxLineage(stage: Stage, lineage: DurableSyntaxLineageId,
                  derivationRole: ContentId<SchemaValue>)
  | CrossRevisionSemantic(StableSemanticId)
  | SemanticContent(ContentId<SchemaValue>)

DurableScalarArgument =
    DurableUnitArgument
  | DurableBoolArgument(Bool)
  | DurableUnsignedArgument(BigNat)
  | DurableSignedArgument(BigInt)
  | DurableBytesArgument(ByteString)
  | DurableTextArgument(Utf8String)
  | DurableEnumArgument(type: QualifiedName, variantTag: UInt32)
  | DurableSchemaValueArgument(ContentId<SchemaValue>)

DurableArgument =
    DurableScalar(DurableScalarArgument)
  | DurableIdentityArgument(DurableSubjectIdentity)
  | DurableListArgument(NodeList<DurableArgument>)
  | DurableMapArgument(
        CanonicallyOrderedMap<CanonicalArgumentKey, DurableArgument>)

DurableCanonicalArguments =
    CanonicallyOrderedMap<CanonicalArgumentKey, DurableArgument>

DurableQueryIdentity = {
    kind: QueryKind,
    subject: DurableSubjectIdentity,
    arguments: DurableCanonicalArguments
}

SyntaxLineageAssignment = {
    current: AnyNodeId,
    prior: Option<AnyNodeId>,
    lineage: DurableSyntaxLineageId,
    currentRolePath: NodeList<FieldName>,
    priorRolePath: Option<NodeList<FieldName>>
}

SubjectLineageMap = {
    assignmentsByCurrent: NodeMap<AnyNodeId, SyntaxLineageAssignment>,
    currentByMatchedPrior: NodeMap<AnyNodeId, AnyNodeId>
}

RevisionReuseContext = {
    prior: EnvironmentRevision,
    current: EnvironmentRevision,
    lineage: SubjectLineageMap
}

DirectInputSelector =
    CurrentFileSnapshot(SourceFileId)
  | SourceGraphItem(role: FieldName, key: CanonicalArgument)
  | FrontendOptionField(FieldName)
  | LanguageRuleItem(CanonicalArgument)
  | StandardEnvironmentItem(CanonicalArgument)
  | ModuleGraphItem(role: FieldName, key: CanonicalArgument)
  | EffectUniverseItem(CanonicalArgument)
  | CapabilityUniverseItem(CanonicalArgument)
  | SchemaItem(CanonicalArgument)
  | TargetEnvironmentItem(CanonicalArgument)

InputObservation = Present(ContentId<SchemaValue>) | Absent

InputObservationId = ContentId<InputObservation>

DirectInputStamp = {
    role: CanonicalArgumentKey,
    selector: DirectInputSelector,
    observation: InputObservationId
}

DependencyResultStamp = {
    dependency: DurableQueryIdentity,
    result: ContentId<SchemaValue>
}

CachedQueryEntry = {
    durableIdentity: DurableQueryIdentity,
    executionKey: QueryKey,
    result: ContentId<SchemaValue>,
    directInputs: CanonicallyOrderedSet<DirectInputStamp>,
    dependencyResults: CanonicallyOrderedSet<DependencyResultStamp>,
    implementation: ContentId<SchemaValue>,
    durability: SourceLocal | ModuleInterface | StandardEnvironment | Target
}
```

Every query kind registers total `projectDurableSubject` and `projectDurableArguments` functions, or
is explicitly non-reusable. `CrossRevisionSemantic` accepts only identity alternatives whose exact
encoding excludes `RevisionId`, `SourceFileSnapshotId`, and `NodeId`; revision-local syntax and staged
AST subjects must use `SyntaxLineage`. A syntax-to-AST transform inherits the matched CST lineage and
adds its stage plus exact derivation role. Thus a new snapshot-local `NodeId` can find a prior cache
entry without pretending the two execution subjects are equal.

The incremental parser constructs `SubjectLineageMap` from the explicit source change map. A match
must remain in the same `SourceFileId`, preserve the registered semantic field-role path through
all surviving ancestors, and be one-to-one in both revisions. Repeated equal green subtrees are
disambiguated by the nearest surviving ancestor role and occurrence. If those facts admit more than
one prior node, the current assignment has `prior = None` and receives a new lineage; content hash or source
offset alone never chooses between duplicates. The initial lineage key records the exact green/AST
anchor, role path, and occurrence that created it, so equality remains collision-safe through
`ContentId.exactDiscriminator`.

Every `QueryContext.source`, standard-environment, option, graph lookup, and dependency request
records the precise selector and immutable observation it actually read. A selector is interpreted
relative to `RevisionReuseContext.current`; it never contains the old snapshot ID as the value to
look up. On a new environment revision, the scheduler finds an old entry by `DurableQueryIdentity`,
re-resolves every `DirectInputSelector`, and compares the resulting exact `InputObservationId`.
`Absent` makes a failed keyed lookup observable. If all observations, dependency results, and the
implementation ID match, it aliases the unchanged result under the new execution key without
running the query; otherwise it executes normally and records a new entry. Reading a whole graph
intentionally stamps its root selector, while keyed access stamps only the selected node/edge.

A source edit creates new syntax identities for changed subtrees and reuses unchanged green nodes.
A prior result fails red-green validation only when:

- one of its recorded direct input values changed;
- a dependency's semantic result hash changed;
- its query implementation version changed; or
- an environment durability class it reads changed.

A dependency being recomputed does not by itself invalidate a dependent if the resulting semantic
hash is unchanged.

`SCH-INC-001`: Full environment roots may change every execution key, but cannot by themselves
force semantic recomputation. Reuse requires exact equality of every recorded direct/dependency
result discriminator under the new environment and installs no old diagnostics/origins whose
stamped source value changed. Omitting an observed input is a query-validation failure; ambient
filesystem, process, target, or option reads are forbidden.

`SCH-INC-002`: `ContentId.digest` may accelerate stamp lookup but exact discriminator equality
decides green status. Red-green validation is deterministic and produces the same cache decision
under any worker count.

`SCH-INC-003`: A reusable query's projection is injective over all semantically distinct
cross-revision subjects and arguments admitted by that query kind. The validator constructs two
different execution keys with the same durable identity only when the registered lineage/projection
rule proves that they denote the same logical input role. A missing, ambiguous, or stale lineage
match disables reuse; it never falls back to text, offset, digest-only, or local-node-index equality.
Every assignment map key equals `assignment.current`; `priorRolePath` is present exactly when
`prior` is present; and `currentByMatchedPrior` is the inverse of all present prior links. A matched
assignment retains the prior lineage exactly, while an unmatched assignment interns a new
`DurableSyntaxLineageKey`. These checks make current-node projection total and prior matching
one-to-one.

`SCH-INC-004`: Each direct read has exactly one selector and observation. Re-evaluating all stored
selectors in the current environment must reproduce the complete set of direct reads made by a
green entry; an unregistered ambient read, duplicate `(role, selector)` with conflicting
observations, or selector that resolves outside the current environment is a cache-validation
failure. Tests cover changed and unchanged documents, individual options, absent graph edges,
standard-environment items, and repeated identical syntax subtrees.

## Unit-test interface

A query implementation test supplies an in-memory `QueryContext` whose dependency map is explicit:

```text
FakeContext {
    BuildCallableSignature(f) -> success((int) -> float)
    LookupName(scope, "f") -> success([f])
    PlanCoercion(int, int) -> identity
}
```

The test invokes `ResolveOverload` directly and asserts the exact `OverloadResult`, requested dependency
keys, provenance rules, and diagnostics. Separate scheduler tests use artificial integer lattices
and dependency graphs; they do not need Slang AST nodes.

Required scheduler unit suites include:

- acyclic memoization and fan-in/fan-out;
- duplicate concurrent requests producing one computation;
- rejected self-cycle and multi-node cycle diagnostics;
- nominal identity/definition knots;
- least- and greatest-fixpoint convergence;
- fixpoint transfers reading current in-component approximations;
- SCC enlargement and deterministic restart after a newly discovered dependency;
- non-monotone transfer detection in debug validation;
- incompatible policy SCCs;
- acyclic unbounded key growth and deterministic semantic resource ceilings;
- identical expression nodes under distinct `ExpressionCheckContextId` values;
- identical statement nodes under distinct `StatementCheckContextId` values;
- deterministic initialization-model/strategy enumeration and rejected nested-plan cycles;
- cancellation and restart;
- incremental invalidation by result hash; and
- one-worker versus many-worker determinism.

## Mapping from current declaration states

The current readiness states are useful migration clues, but become query outputs rather than a
total ordering:

| Current `DeclCheckState` | Replacement facts                                                       |
| ------------------------ | ----------------------------------------------------------------------- |
| `ReadyForParserLookup`   | `ScopedDeclStub` available to compatibility parsing                     |
| `ModifiersChecked`       | `CheckedModifierSet`                                                    |
| `ScopesWired`            | `ScopeGraphFragment`                                                    |
| `SignatureChecked`       | bound header plus provisional signature facts                           |
| `ReadyForReference`      | redeclaration group and exported `DeclRef` identity                     |
| `ReadyForLookup`         | class-base, interface-refinement, facet-route closure, and member index |
| `ReadyForConformances`   | witness-table identities and immutable keyed definitions                |
| `TypesFullyResolved`     | canonical associated/member types                                       |
| `AttributesChecked`      | checked attribute values                                                |
| `DefinitionChecked`      | typed/elaborated body                                                   |
| `CapabilityChecked`      | inferred and validated capability formula                               |

There is no rule that every declaration must pass through these facts in table order. Each query
requests only its real prerequisites, and the scheduler makes any cycle visible as a graph with a
declared semantic policy.
