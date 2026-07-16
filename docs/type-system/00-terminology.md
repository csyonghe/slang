# Terminology and implementation correspondence

This chapter is the normative vocabulary authority for the frontend specification. It keeps the
formal model understandable to Slang developers by reusing established codebase terms when those
terms already denote the intended concept. It also records the cases where the replacement model
must introduce a distinction that the current implementation does not represent.

The correspondence is deliberately one-way:

- existing, unambiguous Slang vocabulary is the naming authority for an existing concept; and
- this specification is the semantic authority for the replacement frontend.

Consequently, matching an implementation name does not adopt the implementation's current
behavior, object lifetime, mutability, or accidental representation. A correspondence row is a
traceability aid, not a requirement to preserve incomplete or incorrect behavior.

`TERM-AUTH-001`: A specification construct that denotes an established Slang concept uses the
established codebase name unless this chapter explicitly registers a replacement or split.

`TERM-AUTH-002`: A new term or a refinement of an existing term states both its nearest codebase
correspondence and the semantic difference that requires the new term. A new spelling is not
introduced merely to make the replacement architecture sound different.

`TERM-AUTH-003`: When current implementation behavior conflicts with a normative rule, the
normative rule controls. The implementation anchor controls vocabulary and migration traceability,
not language semantics.

`TERM-AUTH-004`: In this specification, a bare UpperCamelCase identifier denotes the canonical
schema or language term. C++ class names, generated IR class names, source spellings, and textual IR
opcodes are distinguished explicitly when they are not identical.

## Source and syntax vocabulary

| Canonical term       | Meaning in this specification                                                                                                                          | Current implementation anchor                                         |
| -------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------- |
| `SourceFile`         | Owned source contents and their stable source-file identity.                                                                                           | `SourceFile` in `compiler-core/slang-source-loc.h`                    |
| `SourceFileRecord`   | Stable file identity plus original encoded bytes and decoding information.                                                                             | Immutable replacement record around `SourceFile` contents             |
| `SourceFileSnapshot` | One immutable decoded revision of a `SourceFileRecord`.                                                                                                | The immutable-content role of `SourceFile`                            |
| `SourceView`         | A view of source contents with the source-location mapping and inclusion context used to interpret tokens.                                             | `SourceView` in `compiler-core/slang-source-loc.h`                    |
| `TestSourceFixture`  | Test-kernel product containing one mutually consistent `SourceFileRecord`, `SourceFileSnapshot`, and `SourceView`.                                     | New test-only aggregate over the canonical source products            |
| `Token`              | One lexed token, including its `TokenType`, source range, spelling, and lossless trivia associations in the replacement model.                         | `Token` in `compiler-core/slang-token.h`                              |
| `TokenType`          | The token-kind discriminator. `TokenKind` is not a synonym.                                                                                            | `TokenType` and generated token definitions                           |
| `TokenList`          | The immutable source-order sequence of tokens consumed by preprocessing and parsing. The replacement form additionally retains trivia and token gaps.  | `TokenList` in `compiler-core/slang-lexer.h`                          |
| `PhysicalToken`      | A `SourceToken(Token)` or one boundary sentinel in a `PhysicalTokenList`; it is a lossless-list wrapper, not a replacement name for `Token`.           | New closed wrapper around `Token` plus explicit boundary entries      |
| `PhysicalTokenList`  | The lossless replacement form of `TokenList`, including physical slices, trivia, gaps, and its `SourceView`.                                           | `TokenList` plus information currently discarded or stored separately |
| `LosslessCST`        | The immutable concrete-syntax product containing both the physical source tree and the parser-facing grammar tree.                                     | New lossless representation layered over `TokenList`                  |
| `SourceGreenNode`    | An immutable parentless CST node whose children preserve physical source order, directives, disabled regions, tokens, and gaps.                        | New lossless source-tree node                                         |
| `GrammarGreenNode`   | An immutable parentless CST node whose children preserve the grammar recognized by the parser while retaining token references into the physical list. | New parser-facing green node                                          |
| `RedNode`            | A contextual view that adds parent, child-index, and absolute-position information to a source or grammar green node without mutating it.              | New ephemeral/view-layer counterpart to immutable green nodes         |
| `SyntaxNode`         | Base term for a staged AST node `SyntaxNode<S>`. Concrete-syntax nodes remain the distinct green/red CST values above.                                 | `SyntaxNode` in `slang-ast-base.h`                                    |
| `ASTNodeType`        | Discriminator for a `SyntaxNode` kind.                                                                                                                 | `ASTNodeType`                                                         |
| `ASTSnapshot`        | Immutable owner of all stage-indexed `SyntaxNode` values in one frontend representation.                                                               | New replacement for mutable nodes owned by `ASTBuilder` arenas        |
| `Decl`               | A declaration syntax node and its stable declared identity.                                                                                            | `Decl` and its subclasses                                             |
| `Expr`               | An expression syntax node.                                                                                                                             | `Expr` and its subclasses                                             |
| `ThisExpr`           | The expression node for a source `this` reference; receiver type and access facts are staged annotations, not a replacement expression kind.           | `ThisExpr`                                                            |
| `Stmt`               | A statement syntax node.                                                                                                                               | `Stmt` and its subclasses                                             |
| `Modifier`           | A syntax-level declaration, type, statement, or expression modifier. Checked semantic effects are named separately.                                    | `Modifier` and its subclasses                                         |

`TERM-SRC-001`: The lossless token model extends `Token` and `TokenList`; it does not rename them to
`Lexeme`, `TokenKind`, or a token “tape.” `PhysicalToken` is only the closed list-entry wrapper that
adds boundary sentinels, while `SourceToken(Token)` retains the canonical lexical-token value. A
serialization format may use different field labels but must preserve these semantic names in its
schema mapping.

`TERM-SRC-002`: `Decl`, `Expr`, `Stmt`, and `Modifier` are kind families below `SyntaxNode`. The
formal model may refine a family by representation stage, but it does not replace the family names
with generic “declaration node” or “expression node” types.

## Semantic values and types

| Canonical term           | Meaning in this specification                                                                                                                                                                                                           | Current implementation anchor                                                                                                                                                                                                                             |
| ------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `SchemaValue`            | Any value described by the canonical schema and eligible for deterministic content identity, including configuration/query data that is not a type-system value.                                                                        | New serialization meta-domain; broader than `Val`                                                                                                                                                                                                         |
| `Val`                    | Base family of canonical semantic values, including types, declaration references, constants, and witnesses.                                                                                                                            | `Val` in `slang-ast-val.h`                                                                                                                                                                                                                                |
| `Type`                   | A `Val` that classifies source values or participates in type-level computation.                                                                                                                                                        | `Type` in `slang-ast-type.h`                                                                                                                                                                                                                              |
| `DeclRef`                | A declaration identity together with its applied substitutions and required evidence. Source-use provenance is not part of `DeclRef` identity.                                                                                          | `DeclRef` / `DeclRefBase`                                                                                                                                                                                                                                 |
| `DeclRefExpr`            | An expression whose selected declaration is represented by a `DeclRef`. It is an expression node, not the declaration reference value itself.                                                                                           | `DeclRefExpr` in `slang-ast-expr.h`                                                                                                                                                                                                                       |
| `SubstitutionSet`        | Working substitution from generic parameter identity to argument; the replacement representation is immutable and keyed rather than a mutable or linked traversal view.                                                                 | `SubstitutionSet`                                                                                                                                                                                                                                         |
| `FuncType`               | The canonical callable type, including the explicit receiver, parameter passing modes, result, error behavior, callable traits, and calling convention defined by this specification.                                                   | `FuncType`                                                                                                                                                                                                                                                |
| `FuncTypeParamInfo`      | One structural parameter entry in `FuncType`, extended with the fields made explicit by this specification.                                                                                                                             | `FuncType::ParamInfo`                                                                                                                                                                                                                                     |
| `ReceiverSlot`           | The explicit receiver entry of a non-static `FuncType`; it is not parameter zero.                                                                                                                                                       | Principled replacement for receiver information currently recovered from declaration context                                                                                                                                                              |
| `ParamPassingMode`       | The language-level parameter direction and alias contract.                                                                                                                                                                              | `ParamPassingMode`                                                                                                                                                                                                                                        |
| `InMode`                 | Abstract, immutable input that may be copied/moved or read through abstract storage.                                                                                                                                                    | `ParamPassingMode::In` / source `in`                                                                                                                                                                                                                      |
| `OutMode`                | Abstract, mutable output with no pre-read and required initialization/write-back behavior.                                                                                                                                              | `ParamPassingMode::Out` / source `out`                                                                                                                                                                                                                    |
| `InOutMode`              | Abstract, mutable input/output with read/write and write-back behavior.                                                                                                                                                                 | `ParamPassingMode::BorrowInOut` / source `inout`                                                                                                                                                                                                          |
| `RefMode`                | Physical, mutable reference mode; applicability requires physical-location identity and never materializes a fresh temporary.                                                                                                           | `ParamPassingMode::Ref` / source `__ref`                                                                                                                                                                                                                  |
| `ConstRefMode`           | Physical, read-only reference mode; applicability requires physical-location identity, a property/subscript `constref` accessor when applicable, and never materializes a fresh temporary. The underlying storage may still be mutable. | Deliberate semantic split for source `__constref` and current `BorrowInParamType` plumbing; it is not the abstract semantics of `ParamPassingMode::BorrowIn`                                                                                              |
| `OperandDomain`          | Orthogonal parameter-mode axis that distinguishes abstract storage/value preparation from physical-location identity.                                                                                                                   | New explicit replacement axis for concepts currently distributed across parameter wrappers and storage checking                                                                                                                                           |
| `AbstractOperand`        | Operand domain used by `InMode`, `OutMode`, and `InOutMode`; accessor plans and write-back may represent abstract storage.                                                                                                              | Existing abstract-storage behavior of properties/subscripts, made structural                                                                                                                                                                              |
| `PhysicalOperand`        | Operand domain used by `ConstRefMode` and `RefMode`; it carries the physical-location requirement used for applicability and ABI checking.                                                                                              | Existing physical-storage/reference checks, made structural                                                                                                                                                                                               |
| `ThisType`               | The dependent type of `this` in an interface or another explicitly bound receiver context.                                                                                                                                              | `ThisType`                                                                                                                                                                                                                                                |
| `BottomType`             | The uninhabited type spelled `Never` in source.                                                                                                                                                                                         | `BottomType`                                                                                                                                                                                                                                              |
| `VoidType`               | The type of no returned value. This canonical schema term corresponds to `BaseType::Void` and `getVoidType`; it does not assert that the current code has a `VoidType` C++ subclass.                                                    | `BaseType::Void` / `getVoidType`                                                                                                                                                                                                                          |
| `DeclRefType`            | A type formed from a declaration reference, including nominal applications.                                                                                                                                                             | `DeclRefType`                                                                                                                                                                                                                                             |
| `PtrType`                | The ordinary pointer type.                                                                                                                                                                                                              | `PtrType`                                                                                                                                                                                                                                                 |
| `ExplicitRefType`        | The explicitly spelled reference type. Parameter passing modes remain separate from this type constructor.                                                                                                                              | `ExplicitRefType`                                                                                                                                                                                                                                         |
| `ArrayExpressionType`    | The array type constructor used by the AST type domain.                                                                                                                                                                                 | `ArrayExpressionType`                                                                                                                                                                                                                                     |
| `ConcreteTypePack`       | A materialized sequence of types.                                                                                                                                                                                                       | `ConcreteTypePack`                                                                                                                                                                                                                                        |
| `EachType`               | A pack element projection introduced by `each`.                                                                                                                                                                                         | `EachType`                                                                                                                                                                                                                                                |
| `ExpandType`             | A pack expansion introduced by `expand` or equivalent inferred expansion.                                                                                                                                                               | `ExpandType`                                                                                                                                                                                                                                              |
| `ExtractExistentialType` | The fresh opened type extracted from an existential value.                                                                                                                                                                              | `ExtractExistentialType`                                                                                                                                                                                                                                  |
| `AndType`                | A conjunction/intersection of type constraints under its chapter-defined canonicalization rules.                                                                                                                                        | `AndType`                                                                                                                                                                                                                                                 |
| `ModifiedType`           | A semantic type together with semantic type modifiers.                                                                                                                                                                                  | `ModifiedType`                                                                                                                                                                                                                                            |
| `LiteralValue`           | Exact decoded literal payload, before contextual type selection or target-width conversion.                                                                                                                                             | Generalizes the payload fields of `IntegerLiteralExpr`, `FloatingPointLiteralExpr`, `BoolLiteralExpr`, and `StringLiteralExpr`; current `IntegerLiteralValue`/`FloatingPointLiteralValue` names are retained but their host-sized representations are not |

`TERM-TYP-001`: `FuncType` and `ParamPassingMode` are the canonical schema spellings. The replacement
`FuncType` may carry more principled information than the current `FuncType`, including an explicit
receiver; sharing the name does not preserve the old field layout.

`TERM-TYP-002`: A parameter direction is never encoded only as `PtrType`, `ExplicitRefType`, or an
implicit wrapper around a parameter's value type. `ParamPassingMode` and the value type are
independently inspectable.

`TERM-TYP-003`: `SchemaValue` is not an alternate spelling of `Val`. Every `Val` is schema-visible,
but query descriptors, source-management records, and other canonical configuration data may be
`SchemaValue`s without entering Slang's `Val` type-system hierarchy.

## Storage and access

`Storage` is the Slang term for an expression that can be accessed through an l-value-like
operation. The replacement model makes two independent facts explicit:

```text
StorageRef =
    PhysicalStorage(PhysicalStorageRef)
  | AbstractStorage(AbstractStorageRef)

StorageAccessMode = {
    operations: CanonicalFiniteSet<Read | Write>,
    discipline: Ordinary | Atomic
}
```

Physicality describes whether the reference designates stable addressable memory. Access mode
describes permitted reads and writes. Neither fact implies the other.

| Canonical term      | Meaning in this specification                                                                                                           | Current implementation anchor or difference                                                                          |
| ------------------- | --------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------- |
| `StorageRef`        | The checked reference to storage, preserving whether access is physical or abstract and how it is projected.                            | Principled replacement for information currently collapsed into `QualType::isLeftValue` and accessor-specific checks |
| `PhysicalStorage`   | A `StorageRef` alternative that designates a real, stable memory location for the required call lifetime.                               | New explicit refinement of existing storage terminology                                                              |
| `AbstractStorage`   | A `StorageRef` alternative implemented through accessors, write-back, or another operation that does not itself expose physical memory. | `PropertyDecl` and `SubscriptDecl` are existing abstract-storage concepts                                            |
| `StorageAccessMode` | The checked read/write/atomic permissions of a storage reference or storage operation.                                                  | More explicit semantic domain than current `AccessQualifier`                                                         |
| `AccessQualifier`   | The existing type/access qualifier vocabulary. It is used only where a rule intentionally refers to that codebase domain.               | `AccessQualifier` in `slang-type-system-shared.h`                                                                    |
| `PropertyDecl`      | A named abstract-storage declaration.                                                                                                   | `PropertyDecl`                                                                                                       |
| `SubscriptDecl`     | An indexed abstract-storage declaration.                                                                                                | `SubscriptDecl`                                                                                                      |
| `GetterDecl`        | An accessor that reads a value; it does not expose physical storage.                                                                    | `GetterDecl`                                                                                                         |
| `SetterDecl`        | An accessor that writes an abstract storage value; it does not expose physical storage.                                                 | `SetterDecl`                                                                                                         |
| `RefAccessorDecl`   | An accessor that may expose a physical storage reference with the accessor's exact mutability contract.                                 | `RefAccessorDecl`                                                                                                    |

`TERM-STO-001`: The semantic vocabulary `Place` and every derived identifier containing `Place` are
forbidden. The canonical family is `Storage`: `StorageRef`, `PhysicalStorage`,
`AbstractStorage`, `StorageAccessMode`, and storage paths or projections.

`TERM-STO-002`: Physicality and mutability are orthogonal. `__constref` requires readable
`PhysicalStorage` and exposes a read-only view; it does not prove that the underlying storage is
immutable. `__ref` requires writable `PhysicalStorage` and exposes a mutable view. The `in` mode
has an abstract, read-only operand contract, while `out` and `inout` have abstract, writable operand
contracts with their separately defined initialization and read-before-write rules.

`TERM-STO-003`: Neither `__constref` nor `__ref` may be satisfied by materializing a fresh
temporary. A property or subscript is eligible only when the selected `RefAccessorDecl` exposes
physical storage with the required access view; only `__ref` additionally requires a writable,
mutable endpoint. A `GetterDecl` result is a value and cannot be reclassified as physical storage.

`TERM-STO-004`: `StorageAccessMode` is not a rename of `AccessQualifier`. The former records the
operation-level read/write/atomic contract used by checking and lowering; the latter remains the
codebase term for the existing qualifier domain. Every bridge between them is an explicit rule.

`TERM-STO-005`: A `StorageAccessPlan` records how a checked storage operation is performed. It may
select an accessor, physical projection, or write-back protocol, but it cannot change
`AbstractStorage` into `PhysicalStorage` without a qualifying `RefAccessorDecl`.

## Lookup, overload resolution, and coercion

| Canonical term                 | Meaning in this specification                                                                                          | Current implementation anchor or difference                             |
| ------------------------------ | ---------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------- |
| `LookupResult`                 | The complete result of name or member lookup before a use is committed.                                                | `LookupResult`                                                          |
| `LookupResultItem`             | One declaration candidate together with lookup provenance.                                                             | `LookupResultItem`                                                      |
| `LookupResultItem::Breadcrumb` | One step of current lookup provenance. The formal `LookupPath` is its typed immutable replacement.                     | `LookupResultItem::Breadcrumb`                                          |
| `LookupPath`                   | A typed, contiguous sequence of lexical, import, facet, extension, receiver, and witness-lookup edges.                 | New checked form of breadcrumb information                              |
| `BoundDeclUse`                 | A committed declaration use: `DeclRef` identity plus `LookupPath`, access decision, origin, and use-specific evidence. | New immutable record; not a synonym for `DeclRef` or `LookupResultItem` |
| `OverloadCandidate`            | One callable candidate considered by overload resolution.                                                              | `OverloadCandidate`                                                     |
| `OverloadResolveContext`       | The inputs and policy of one overload-resolution operation.                                                            | `OverloadResolveContext`                                                |
| `ConversionCost`               | The ordered, structured quality assigned to an applicable conversion and used in candidate comparison.                 | `ConversionCost`                                                        |
| `CoercionSite`                 | The source construct and policy context in which coercion is requested.                                                | `CoercionSite`                                                          |
| `TypeCoercionWitness`          | Typed evidence that a source type can be coerced to a target type.                                                     | `TypeCoercionWitness`                                                   |
| `ConversionPlan`               | New immutable operational description of the expression transformation selected by coercion checking.                  | Separates applicability evidence and lowering work from a numeric cost  |

`TERM-LKP-001`: `LookupResultItem` is a candidate. `BoundDeclUse` is produced only after a candidate
has been selected and its access and evidence obligations have been checked. A `BoundDeclUse`
retains use provenance without adding that provenance to `DeclRef` identity.

`TERM-LKP-002`: `ConversionCost` ranks an applicable `ConversionPlan`. A cost is not itself a
conversion witness or lowering recipe, and `ConversionRank` is not an alternate name for it.

## Interfaces, subtyping, and witnesses

| Canonical term                                                 | Meaning in this specification                                                                                                                          | Current implementation anchor or difference                                                                                                              |
| -------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Witness`                                                      | Base family of typed proof values used by semantic computation.                                                                                        | `Witness`                                                                                                                                                |
| `SubtypeWitness`                                               | Evidence for a chapter-defined subtype relation, with endpoints carried explicitly.                                                                    | `SubtypeWitness`                                                                                                                                         |
| `SubtypeWitnessTarget`                                         | Shared concrete/generic subtype endpoints used by both `WitnessTableForm` and `SubtypeWitnessForm`.                                                    | Unified replacement for the isomorphic `ConformanceTarget` and `InterfaceSubtypeTarget` draft aliases                                                    |
| `SubtypeWitnessForm`                                           | Canonical concrete/generic/error classifier of a subtype-witness value.                                                                                | New immutable classifier derived from `SubtypeWitness` endpoints and binders                                                                             |
| `SubtypeWitnessValueShape`                                     | Shared IR-ready/IR value shape carrying a `SubtypeWitnessForm`; it does not imply a statically materialized witness table.                             | `IRWitnessTableType` and witness-valued IR operands                                                                                                      |
| `WitnessTable`                                                 | A semantic value proving that a type satisfies an interface and mapping requirement keys to witnesses.                                                 | `WitnessTable`                                                                                                                                           |
| `WitnessTableForm`                                             | Canonical concrete or generic provider-table identity/form, using `SubtypeWitnessTarget` for its endpoints.                                            | Immutable replacement for mutable table/classifier state; distinct from operational `SubtypeWitnessForm`, which also carries error recovery              |
| `RequirementWitness`                                           | The kind-correct value satisfying one interface requirement.                                                                                           | `RequirementWitness`                                                                                                                                     |
| `RequirementDictionary`                                        | The key-to-witness mapping for interface requirements. It is conceptually unordered and keyed by requirement identity.                                 | `RequirementDictionary`                                                                                                                                  |
| `RequirementKey<K>`                                            | Specialization-, declaring-view-, refinement-path-, and kind-aware identity of one declared interface requirement occurrence.                          | Refines the current `RequirementDictionary` use of requirement `Decl*` keys                                                                              |
| `InterfaceRequirementKeyOf<K>` / `SomeInterfaceRequirementKey` | Kind-indexed witness-table entry key and its all-kind existential form.                                                                                | New typed wrapper around current requirement-declaration keys, preserving specialization and path identity                                               |
| `RuntimeInterfaceRequirementKey`                               | Projection of callable, constructor, property-accessor, or subscript-accessor entries that occupy runtime invocation slots.                            | Current runtime witness-table entry roles, made explicit and accessor-indexed                                                                            |
| `SubtypeWitnessLookupKey`                                      | Restricted key for a base-interface entry or conformance-requirement entry whose payload is a `SubtypeWitness`; it is not an all-kind requirement key. | New typed restriction over current keyed witness lookup                                                                                                  |
| `Facet`                                                        | A member-providing view of a type reached through self, a base, or an applicable extension.                                                            | `Facet`                                                                                                                                                  |
| `InheritanceInfo`                                              | Existing aggregate vocabulary for inheritance and facet information. The formal model splits its facts into immutable domains.                         | `InheritanceInfo`                                                                                                                                        |
| `LookupSubtypeWitness`                                         | A new witness operation `LookupSubtypeWitness(witness, key)` that obtains a requirement witness by key from another witness.                           | Operationally corresponds one-to-one with `IRLookupWitnessMethod` / `lookupWitness`                                                                      |
| `PackCountWitness`                                             | Generalized immutable witness family proving equality between actual and expected pack counts.                                                         | Intentionally generalizes `DeclaredVariadicPackCountWitness` and `ConcreteVariadicPackCountWitness` while preserving those declared/concrete proof cases |

`TERM-WIT-001`: Conformance is a relation between a type and an interface. A `WitnessTable` is a
first-class proof value for one conformance. “Conformance” does not name a second proof-object
hierarchy, and a witness table is permitted wherever the relevant concrete subtype/conformance
proof is required.

`TERM-WIT-002`: `WitnessTable` values may be generic. `GenericWitnessTable` denotes a generic
witness-table value, and `SpecializedWitnessTable` denotes application of generic arguments and
keyed constraint witnesses to that value. Specialization does not manufacture an unrelated
nongeneric conformance identity.

`TERM-WIT-003`: `LookupSubtypeWitness(witness, key)` has an operational meaning: look up `key` in
`witness`. A generic `TransitiveSubtypeWitness` must not be used to encode that operation. Lowering
preserves it as `IRLookupWitnessMethod` with operands `[lower(witness), lower(key)]` in that order.

`TERM-WIT-004`: Non-emptiness and pack-count evidence use typed witness constructors. A known
concrete pack produces `ConcreteNonEmptyPackWitness`; an abstract pack constrained to be non-empty
produces `DeclaredNonEmptyPackWitness`. `NonEmptyPackWitness` is only the family name, not an
unexplained placeholder proof. Likewise, `PackCountWitness` has explicit declared and concrete
derivations corresponding to the codebase's `DeclaredVariadicPackCountWitness` and
`ConcreteVariadicPackCountWitness`; it is not an unclassified Boolean proof.

## Visibility and capabilities

| Canonical term      | Meaning in this specification                                                                                                  | Current implementation anchor                                  |
| ------------------- | ------------------------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------- |
| `DeclVisibility`    | Declaration-level visibility and the lattice used to derive effective declaration/type visibility.                             | `DeclVisibility`, `getDeclVisibility`, and `getTypeVisibility` |
| `CapabilitySet`     | Canonical capability alternatives and conjunctions used for target availability and implication.                               | `CapabilitySet` / `CapabilitySetVal`                           |
| `CapabilityAtomSet` | One conjunction component of a `CapabilitySet`; the replacement schema makes its canonical ordering and immutability explicit. | `CapabilityAtomSet`, currently backed by `UIntSet`             |
| `CapabilityAtom`    | One atomic capability fact.                                                                                                    | `CapabilityAtom`                                               |
| `CapabilityName`    | The registered name of a capability.                                                                                           | `CapabilityName`                                               |

`TERM-CAP-001`: `DeclVisibility` and `CapabilitySet` are the canonical terms. Bare `Visibility` and
`CapabilityFormula` do not name parallel domains. Contextual access decisions and capability
implication proofs remain separate from the declaration value and capability set they analyze.

## IR vocabulary and operation names

| Canonical term                           | Meaning in this specification                                                                              | Current implementation anchor or textual opcode                                                                   |
| ---------------------------------------- | ---------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------- |
| `IRInst`                                 | Base IR instruction/value.                                                                                 | `IRInst`                                                                                                          |
| `IROp`                                   | IR opcode discriminator.                                                                                   | `IROp`                                                                                                            |
| `IRParam`                                | IR parameter instruction.                                                                                  | `IRParam`                                                                                                         |
| `IRBuilder`                              | Builder used to construct validated IR instructions.                                                       | `IRBuilder`                                                                                                       |
| `IRCall`                                 | Call instruction whose operand zero is the callee and whose remaining operands are arguments.              | `IRCall`                                                                                                          |
| `IRWitnessTable`                         | IR witness-table value/definition.                                                                         | `IRWitnessTable`                                                                                                  |
| `IRLookupWitnessMethod`                  | Keyed lookup of a requirement witness from a witness table.                                                | Textual opcode `lookupWitness`                                                                                    |
| `IRSpecialize`                           | Application of generic arguments and evidence to a generic IR value.                                       | Textual opcode `specialize`                                                                                       |
| `IRExtractExistentialWitnessTable`       | Extraction of the witness table carried by an existential value.                                           | Textual opcode `extractExistentialWitnessTable`                                                                   |
| `IRForwardDifferentiate`                 | Forward-derivative request with one base-function operand.                                                 | `IRForwardDifferentiate`                                                                                          |
| `IRBackwardDifferentiate`                | Backward-derivative request with apply-function, context-type, and backward-propagate-function operands.   | `IRBackwardDifferentiate`                                                                                         |
| `IRDetachDerivative`                     | Derivative-detachment instruction with one value operand.                                                  | `IRDetachDerivative`                                                                                              |
| `IRUnconditionalBranch`                  | Unconditional branch whose first operand is its target and whose remaining operands are block arguments.   | `IRUnconditionalBranch`                                                                                           |
| `IRConditionalBranch`                    | Conditional branch with condition, true-block, and false-block operands.                                   | `IRConditionalBranch`                                                                                             |
| `IRSwitch`                               | Switch with condition, break/default labels, and case-value/case-label pairs.                              | `IRSwitch`                                                                                                        |
| `IRReturn` / `IRThrow` / `IRUnreachable` | Existing return, throw, and unreachable terminators.                                                       | Same generated class names                                                                                        |
| `IRPoison`                               | Existing typed poison value used only for diagnostic/tooling recovery in this specification.               | `IRPoison`                                                                                                        |
| `IRInstSemanticMetadata`                 | Immutable graph-local sidecar for semantic plans and proofs keyed by `IRInstId`; it is not opcode payload. | Principled replacement for frontend facts currently spread across AST state, decorations, and lowering-local data |

`TERM-IR-001`: A rule that corresponds to an existing IR operation uses the generated IR class name
shown above and the established textual opcode where the table names one.
`LookupWitnessOperation`, `SpecializeWitnessOperation`, and
`ExtractExistentialWitnessOperation` are forbidden invented names.

`TERM-IR-002`: A claimed one-to-one lowering correspondence is testable: the checked constructor's
operands, result type, and proof endpoints must validate against the corresponding `IRInst` without
reconstructing hidden semantic state.

`TERM-IR-003`: A new frontend operation with no existing `IROp` is named as a frontend plan or
checked construct, not as an `IR...` type. It may acquire an `IR...` name only when the IR opcode is
registered.

`TERM-IR-004`: `IROp` means only the generated codebase opcode discriminator. It never denotes a
tagged union carrying ABI, capability, initialization, storage, reference, witness, or derivative
payload. Such facts belong in `IRInstSemanticMetadata`; a standard-environment plan must resolve to
an actual registered `IROp`.

`TERM-IR-005`: Calls use `IRCall`; branches and terminators use the generated class names in the
table; derivative requests use `IRForwardDifferentiate` or `IRBackwardDifferentiate`; recovery uses
`IRPoison`. Names such as `DirectCallOperation`, `WitnessCallOperation`, `BranchOperation`,
`SelectDerivativeOperation`, and `IRErrorOperation` are forbidden invented opcode classes.

## Initialization, lambdas, and differentiability

| Canonical term                                               | Meaning in this specification                                                                                                                                                                    | Current implementation anchor or difference                                                                                                                                                   |
| ------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `InitializerListExpr`                                        | The brace-delimited initializer-list expression node.                                                                                                                                            | `InitializerListExpr`                                                                                                                                                                         |
| `InitializerExpr`                                            | Formal category for an `InvokeExpr`, `ExplicitCastExpr`, `InitializerListExpr`, or `NewExpr` consumed by initialization rules. It is not claimed to be a current C++ base class.                 | New closed grammar/checking category over existing AST node kinds                                                                                                                             |
| `InvokeExpr`                                                 | Existing call-syntax node; when its callee denotes a type, its argument count distinguishes direct, explicit-single, and requested-default initialization forms.                                 | `InvokeExpr`                                                                                                                                                                                  |
| `ExplicitCastExpr`                                           | Existing C-style explicit-cast node consumed by the explicit-single initialization path.                                                                                                         | `ExplicitCastExpr`                                                                                                                                                                            |
| `NewExpr`                                                    | Existing allocating-expression node whose arguments feed allocating initialization.                                                                                                              | `NewExpr`                                                                                                                                                                                     |
| `ConstructorDecl`                                            | Declaration of a constructor selected by initialization.                                                                                                                                         | `ConstructorDecl`                                                                                                                                                                             |
| `LambdaExpr`                                                 | Source AST expression containing the lambda syntax and typed lambda information.                                                                                                                 | `LambdaExpr`                                                                                                                                                                                  |
| `LambdaDecl`                                                 | Synthesized `StructDecl` representing the lambda environment and callable surface; it is not the source expression node.                                                                         | The checker currently creates `LambdaDecl` as a `StructDecl`-derived environment declaration                                                                                                  |
| `LambdaSynthesisResult`                                      | Immutable synthesis product containing `lambdaDecl`, environment type, `CaptureLayout`, initializer, invoke callable, and callable witness.                                                      | Principled staged replacement for facts currently installed by mutating `LambdaDecl` during checking; the enclosing `SynthesisGroup` remains the publication mechanism                        |
| `PartiallyAppliedGenericValue`                               | Immutable checked/value-stage form of a generic with a residual binder after partial application. It is distinct from its expression node.                                                       | `PartiallyAppliedGenericExpr` is the existing AST expression; the replacement value record preserves the established stem while making the stage explicit                                     |
| `DifferentiabilityPromise`                                   | Checked callable promise containing the supported differentiation modes and order policy.                                                                                                        | Header checking translates `ForwardDifferentiableAttribute`, `BackwardDifferentiableAttribute`, and any admitted `TreatAsDifferentiableAttribute` compatibility rule into this explicit value |
| `DifferentialParticipation`                                  | Structural receiver/parameter/result participation in differentiation.                                                                                                                           | `NoDiffModifier` maps to `ExcludedByNoDiff`; absence maps through the declared default rather than remaining a hidden type modifier                                                           |
| `ForwardDifferentiable` / `ForwardDifferentiableAttribute`   | Source vocabulary and declaration attribute promising forward differentiability.                                                                                                                 | `ForwardDifferentiableAttribute`, translated to the forward mode of `DifferentiabilityPromise`                                                                                                |
| `BackwardDifferentiable` / `BackwardDifferentiableAttribute` | Source vocabulary and declaration attribute promising backward differentiability.                                                                                                                | `BackwardDifferentiableAttribute`, translated to the backward mode of `DifferentiabilityPromise`                                                                                              |
| `ForwardDifferentiate`                                       | The operation that requests a forward derivative; its AST and IR forms are `ForwardDifferentiateExpr` and `IRForwardDifferentiate`.                                                              | `ForwardDifferentiateExpr` / `IRForwardDifferentiate`                                                                                                                                         |
| `BackwardDifferentiate`                                      | The operation that requests a backward derivative; its AST and IR forms are `BackwardDifferentiateExpr` and `IRBackwardDifferentiate`.                                                           | `BackwardDifferentiateExpr` / `IRBackwardDifferentiate`                                                                                                                                       |
| `TreatAsDifferentiableExpr`                                  | Existing parsed AST wrapper; its `Flavor::NoDiff` alternative is the current source form for `no_diff(...)`.                                                                                     | `TreatAsDifferentiableExpr`                                                                                                                                                                   |
| `DetachExpr`                                                 | Checked expression synthesized from `TreatAsDifferentiableExpr(Flavor::NoDiff)` or another admitted explicit detachment conversion; it is not claimed to be the current parsed source-node kind. | New checked expression with current source correspondence through `TreatAsDifferentiableExpr::NoDiff`                                                                                         |
| `IDifferentiable`                                            | Standard interface for values with differential information.                                                                                                                                     | `IDifferentiable`                                                                                                                                                                             |
| `IDifferentiablePtrType`                                     | Standard interface for pointer-like differentiable values whose differential contract is pointer-specific.                                                                                       | `IDifferentiablePtrType`                                                                                                                                                                      |

`TERM-DIF-001`: Header checking translates `ForwardDifferentiableAttribute` and
`BackwardDifferentiableAttribute` into the corresponding modes and order policy of one
`DifferentiabilityPromise`. A versioned compatibility rule may translate
`TreatAsDifferentiableAttribute` into an explicit checked promise or contract assumption, but the
attribute is never a hidden instruction to defer validation until IR. `NoDiffModifier` translates
to `DifferentialParticipation.ExcludedByNoDiff`; it is not retained as a semantic type modifier.

`TERM-DIF-002`: Parsing `no_diff(e)` produces
`TreatAsDifferentiableExpr(Flavor::NoDiff)`. Checking that source node produces `DetachExpr`,
elaboration produces `IRReadyDifferentiationPlan.DetachDerivativePlan`, and IR lowering produces
`IRDetachDerivative`. These are successive representations of one operation, not interchangeable
AST/plan/opcode names.

`TERM-INI-001`: C-style initialization, constructor calls, aggregate initialization, and
initializer-list checking use initialization vocabulary. They are not all modeled as an
unqualified call followed by conversion, even when a selected constructor eventually lowers to a
call.

`TERM-DIF-003`: “Differentiable” describes a declaration/type contract; “differentiate” names an
operation. `BackwardDifferentiable` and `BackwardDifferentiate` are therefore not interchangeable.
Derivative detachment uses `DetachExpr` and `IRDetachDerivative` rather than an invented
derivative-detachment operation name.

## Principled terms introduced by this specification

These names describe distinctions or products that are not represented as first-class immutable
domains in the current frontend.

| New canonical term                                                                                | Nearest codebase correspondence                                                                      | Required semantic difference                                                                                                                                              |
| ------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `SourceFileRecord` and `SourceFileSnapshot`                                                       | `SourceFile` plus revision/source-management state                                                   | Separate a stable file identity and original encoded bytes from one immutable decoded revision; each interpretation still has an explicit `SourceView`.                   |
| `PhysicalTokenList` and `LosslessCST`                                                             | `TokenList` plus parser-created syntax                                                               | Preserve every physical token, token gap, trivia item, delimiter, recovery insertion, and exact source range; no semantic interpretation is required to reproduce source. |
| staged immutable snapshots                                                                        | Mutable AST nodes and `DeclCheckState` progression                                                   | Each transformation publishes a new immutable snapshot whose nodes refer to their predecessor origins; no reader observes partial mutation.                               |
| `Origin`                                                                                          | `SourceLoc`, syntax-node links, and synthesis bookkeeping                                            | Tagged provenance that can name source syntax, a prior-stage node, synthesis, recovery, or builtin origin; it is not merely one byte offset.                              |
| `ReferenceInstSemanticPlan` / `PhysicalStorageInstSemanticPlan` / `StorageAccessInstSemanticPlan` | Reference/storage lowering-local state plus registered IR schemas                                    | Stage-free proof plans in `IRInstSemanticMetadata` that select and validate an actual `IROp`; none is an opcode class.                                                    |
| `InitializationInstSemanticPlan`                                                                  | Initialization lowering state                                                                        | Stage-free plan-step/emission identity attached to each actual instruction in an initialization recipe.                                                                   |
| `DerivativeSelectionInstSemanticPlan`                                                             | Autodiff request instructions plus provider/association decorations                                  | Provider, signature, and prerequisite-materialization proof sidecar for an exact `IRForwardDifferentiate` or `IRBackwardDifferentiate`.                                   |
| physical/abstract storage split                                                                   | `QualType::isLeftValue` plus property/subscript accessor checks                                      | Represents addressability independently from mutability and makes `__ref`/`__constref` eligibility explicit.                                                              |
| `StorageAccessPlan`                                                                               | Coercion/accessor/write-back code paths                                                              | Immutable operational plan for reading, writing, borrowing, projecting, or committing storage without inventing physical memory.                                          |
| representation-adjustment proof split                                                             | Inheritance/subtype witnesses used for multiple relations                                            | Separates representation adjustment, interface refinement, concrete conformance, existential opening, and keyed witness lookup into typed proof families.                 |
| `LookupPath` and `BoundDeclUse`                                                                   | `LookupResultItem::Breadcrumb` and selected lookup items                                             | Typed path edges and committed-use provenance survive checking without polluting `DeclRef` identity.                                                                      |
| `SpecializationFrame`                                                                             | `SubstitutionSet`, `GenericAppDeclRef`, and constraint-witness substitutions                         | One immutable, role-keyed applied binder that retains ordinary arguments and required/optional evidence together.                                                         |
| `GenericWitnessTable` and `SpecializedWitnessTable`                                               | Generic witness-table declarations and specialized `DeclRef`/IR values                               | Witness tables are first-class `Val` values before and after specialization; generic application is represented, serializable, and lowerable.                             |
| query scheduler                                                                                   | `ensureDecl`, `DeclCheckState`, and ad hoc request recursion                                         | Central keyed computation with published partial identities, explicit dependencies, cycle policy, deterministic diagnostics, and memoized immutable results.              |
| `IRReadyAST`                                                                                      | The final checked AST consumed by `lowerToIR`                                                        | A stage whose constructs have complete operational plans and map structurally to frontend IR. `CoreAST` is not an alternate name.                                         |
| `DerivativeProvider` and `DerivativeSignatureMap`                                                 | Derivative attributes, registered derivative functions, wrapper-type reconstruction, and autodiff IR | Makes provider identity and the complete primal-to-derivative receiver/parameter/result role mapping explicit and independently testable.                                 |

`TERM-NEW-001`: Each new canonical term above must have a schema definition before its first use in
a normative judgment. The definition must expose the distinction named in the final column; an
opaque ID alone is insufficient.

`TERM-NEW-002`: `IRReadyAST` is the only name for the final frontend representation before IR
generation. The name asserts readiness and a structural lowering contract, not that the AST is a
minimal language “core.”

## Replaced and forbidden aliases

The left column may occur only in this table, the compatibility ledger, quoted historical source,
or a diagnostic-compatibility discussion. It must not define a second semantic construct.

| Replaced or forbidden spelling                                                                     | Canonical spelling                                                                                                     |
| -------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------- |
| `Place` / `PlaceRef`                                                                               | `Storage` / `StorageRef`                                                                                               |
| `PhysicalPlace` / `AbstractPlace`                                                                  | `PhysicalStorage` / `AbstractStorage`                                                                                  |
| `PhysicalPlacePath`                                                                                | `PhysicalStoragePath`                                                                                                  |
| `CoreAST`                                                                                          | `IRReadyAST`                                                                                                           |
| `TokenKind` / token tape                                                                           | `TokenType` / `PhysicalTokenList`                                                                                      |
| `FileId`                                                                                           | `SourceFileId`                                                                                                         |
| bare `SnapshotId`                                                                                  | the specific `ASTSnapshotId<S>`, `SemanticSnapshotId`, or `SourceFileSnapshotId` domain                                |
| `AstNode` / `AstSnapshot` / `AstEdit`                                                              | `SyntaxNode` / `ASTSnapshot` / `ASTEdit`                                                                               |
| a `Cst...` / `Ast...` schema component                                                             | the acronym-correct `CST...` / `AST...` component                                                                      |
| `SemanticValue`                                                                                    | `SchemaValue` (with `Val` as its type-system subset)                                                                   |
| `Declaration` as a schema kind                                                                     | `Decl`                                                                                                                 |
| a `...Declaration...` schema component                                                             | the corresponding `...Decl...` component                                                                               |
| `CanonicalDeclRef`                                                                                 | `DeclRef`                                                                                                              |
| `FunctionType` / `PassingMode`                                                                     | `FuncType` / `ParamPassingMode`                                                                                        |
| `NeverType` / `UnitType`                                                                           | `BottomType` / `VoidType`                                                                                              |
| `NominalType`                                                                                      | `DeclRefType`                                                                                                          |
| `PointerType` / `ReferenceType`                                                                    | `PtrType` / `ExplicitRefType`                                                                                          |
| `ArrayType` / `PackType`                                                                           | `ArrayExpressionType` / `ConcreteTypePack`                                                                             |
| `OpenedExistentialType`                                                                            | `ExtractExistentialType`                                                                                               |
| `SelfType` / `IntersectionType`                                                                    | `ThisType` / `AndType`                                                                                                 |
| bare `Visibility`                                                                                  | `DeclVisibility`                                                                                                       |
| `CapabilityFormula`                                                                                | `CapabilitySet`                                                                                                        |
| `ConversionRank`                                                                                   | `ConversionCost`                                                                                                       |
| `AccessOperand` / `AccessStep`                                                                     | `StorageAccessOperand` / `StorageAccessStep`                                                                           |
| `rankingConversion`                                                                                | `rankingCoercion`                                                                                                      |
| `ConvertedAccess` / `ConsumedWithoutAccessConversion`                                              | `AppliedStorageCoercion` / `ConsumedWithoutStorageCoercion`                                                            |
| `InterfaceSubtypeWitness`                                                                          | `SubtypeWitness`                                                                                                       |
| `InterfaceSubtypeTarget` / `ConformanceTarget`                                                     | `SubtypeWitnessTarget`                                                                                                 |
| `RefinementClauseId`                                                                               | `InterfaceInheritanceClauseId`                                                                                         |
| `WitnessUseStage`                                                                                  | `WitnessTableState`                                                                                                    |
| `InterfaceWitnessClassifier` / `InterfaceWitnessShape`                                             | `SubtypeWitnessForm` / `SubtypeWitnessValueShape`                                                                      |
| `WitnessTableClassifier`                                                                           | `WitnessTableForm`                                                                                                     |
| `WitnessCallRef`                                                                                   | `SubtypeWitnessRef`                                                                                                    |
| `WitnessTableValue`                                                                                | `WitnessTable`                                                                                                         |
| `WitnessTableConstructionScope`                                                                    | `ConformanceConstructionScope`                                                                                         |
| `ConformanceDependency`                                                                            | `WitnessTableDependency`                                                                                               |
| `PackNonEmptyWitness` / `PackNonEmptyDerivation`                                                   | `NonEmptyPackWitness` / `NonEmptyPackWitnessDerivation`                                                                |
| `WitnessEntryKey<K>` / `SomeWitnessEntryKey` / `WitnessRuntimeEntryKey`                            | `InterfaceRequirementKeyOf<K>` / `SomeInterfaceRequirementKey` / `RuntimeInterfaceRequirementKey`                      |
| `RequirementEvidenceMap`                                                                           | `RequirementDictionary`                                                                                                |
| `RequirementSatisfaction`                                                                          | `RequirementWitness`                                                                                                   |
| `TransitiveSubtypeWitness` used for requirement lookup                                             | `LookupSubtypeWitness`                                                                                                 |
| `LookupWitnessOperation`                                                                           | `IRLookupWitnessMethod` / `lookupWitness`                                                                              |
| `SpecializeWitnessOperation`                                                                       | `IRSpecialize` / `specialize`                                                                                          |
| `ExtractExistentialWitnessOperation`                                                               | `IRExtractExistentialWitnessTable` / `extractExistentialWitnessTable`                                                  |
| `DirectCallOperation` / `WitnessCallOperation` / `DynamicCallOperation` / `LambdaCallOperation`    | `IRCall` plus `CallInstSemanticMetadata`; witness and dynamic callable selection remain explicit producer instructions |
| `BranchOperation` / `ConditionalBranchOperation` / `SwitchOperation`                               | `IRUnconditionalBranch` / `IRConditionalBranch` / `IRSwitch`                                                           |
| `ReturnOperation` / `ThrowOperation` / `UnreachableOperation`                                      | `IRReturn` / `IRThrow` / `IRUnreachable`                                                                               |
| `SelectDerivativeOperation`                                                                        | `IRForwardDifferentiate` or `IRBackwardDifferentiate` plus `DerivativeSelectionInstSemanticPlan`                       |
| `IRErrorOperation` / `IRError`                                                                     | `IRPoison` in diagnostic/tooling recovery only                                                                         |
| `IRReferenceOperation` / `IRPhysicalStorageOperation` / `IRStorageAccessOperation`                 | the corresponding `...InstSemanticPlan` sidecar selecting an actual registered `IROp`                                  |
| `IRInitializationDescriptor` / `IRInitializationOperation`                                         | `InitializationInstSemanticPlan` attached to the actual instruction recipe                                             |
| `PartialGeneric`                                                                                   | `PartiallyAppliedGenericValue`                                                                                         |
| `BindHeader` / `BoundHeader`                                                                       | `BindDeclHeader` / `DeclHeader`                                                                                        |
| `CheckedInterfaceDecl`                                                                             | `InterfaceDecl<Typed>`                                                                                                 |
| `LambdaToClosure` / closure schema identifiers                                                     | `LambdaToCallable` / synthesized lambda environment                                                                    |
| `TypeExpr` as a replacement wrapper                                                                | `NodeRef<Typed, Expr>` plus explicit `TypeId` and `KindClassifier(TypeKind)`                                           |
| `StopGradientOnUnsupportedPlace` or another stop-gradient alias                                    | `DetachExpr` / `IRDetachDerivative`, under the chapter-defined diagnostic policy                                       |
| `BackwardUnitResult`                                                                               | `BackwardVoidResult`                                                                                                   |
| `InitializerCallable`                                                                              | `ConstructorCallable`                                                                                                  |
| `RefinementWitnessEntry`                                                                           | `BaseInterfaceEntry`                                                                                                   |
| staged `InitializationCandidateResult<S>`, `InitializationResult<S>`, or `InitializationPlanId<S>` | the corresponding `...At<S>` form; the unparameterized name is the published alias                                     |

`TERM-ALIAS-001`: A forbidden alias in an identifier is an error even when its surrounding schema
would otherwise make the intended canonical term obvious. Serialization aliases are accepted only
by an explicitly versioned compatibility decoder and are never emitted by the canonical encoder.

## Validation expectations

`TERM-VAL-001`: Specification validation scans schema identifiers, headings, table labels, and
normative prose for the forbidden aliases above. Allowlisted occurrences must identify their
compatibility purpose and location.

`TERM-VAL-002`: The future schema compiler must inventory every exported schema constructor. A
constructor whose root is not an established term or a principled new term registered in this
chapter is an error; compounds such as `PhysicalStorageProjectionProof` inherit the registration of
their canonical root and do not each require a redundant glossary row.

`TERM-VAL-002a`: The checked-in `validate-terminology.py` is a bootstrap lexical guard. It rejects
the forbidden aliases explicitly listed in that script across the Markdown chapters. Passing it
does not prove complete constructor inventory, root registration, semantic equivalence, or generated
IR correspondence.

`TERM-VAL-003`: The future schema compiler must validate claimed existing-IR correspondences against
the generated IR instruction registry, including generated class spelling, textual opcode, and
operand schema. Until that check exists, the glossary and bootstrap alias guard document the
requirement but cannot by themselves prove registry completeness.

`TERM-VAL-004`: Unit tests cover every explicit bridge between distinct vocabulary domains,
including `StorageAccessMode` to `AccessQualifier`, `LookupResultItem::Breadcrumb` to
`LookupPath`, `SpecializationFrame` to `IRSpecialize` operands, and checked witness lookup to
`IRLookupWitnessMethod`.

`TERM-VAL-005`: A terminology-only rename cannot silently change semantic identity, serialization,
or proof equality. A semantic split or merge requires its own normative rule, migration entry, and
positive and negative tests.
