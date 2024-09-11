#include "slang-ast-builder.h"
#include "slang-ast-reflect.h"
#include "slang-generated-ast.h"
#include "slang-generated-ast-macro.h"
#include "slang-check-impl.h"

namespace Slang
{

DeclRefBase* DirectDeclRef::_substituteImplOverride(ASTBuilder* astBuilder, SubstitutionSet subst, int* ioDiff)
{
    SLANG_UNUSED(astBuilder);
    SLANG_UNUSED(subst);
    SLANG_UNUSED(ioDiff);
    return this;
}

void DirectDeclRef::_toTextOverride(StringBuilder& out)
{
    if (getDecl()->getName() && getDecl()->getName()->text.getLength() != 0)
    {
        out << getDecl()->getName()->text;
    }
}

Val* DirectDeclRef::_resolveImplOverride()
{
    return this;
}

DeclRefBase* DirectDeclRef::_getBaseOverride()
{
    return nullptr;
}

DeclRefBase* _getDeclRefFromVal(Val* val)
{
    if (auto declRefType = as<DeclRefType>(val))
        return declRefType->getDeclRef();
    else if (auto genParamIntVal = as<GenericParamIntVal>(val))
        return genParamIntVal->getDeclRef();
    else if (auto declaredSubtypeWitness = as<DeclaredSubtypeWitness>(val))
        return declaredSubtypeWitness->getDeclRef();
    else if (auto declRef = as<DeclRefBase>(val))
        return declRef;
    return nullptr;
}

DeclRefBase* _resolveAsDeclRef(DeclRefBase* declRefToResolve)
{
    if (auto rs = _getDeclRefFromVal(declRefToResolve->resolve()))
        return rs;
    return declRefToResolve;
}

DeclRefBase* MemberDeclRef::_substituteImplOverride(ASTBuilder* astBuilder, SubstitutionSet subst, int* ioDiff)
{
    int diff = 0;
    auto substParent = getParentOperand()->substituteImpl(astBuilder, subst, &diff);
    if (diff)
    {
        (*ioDiff)++;
        return astBuilder->getMemberDeclRef(substParent, getDecl());
    }
    return this;
}

void MemberDeclRef::_toTextOverride(StringBuilder& out)
{
    getParentOperand()->toText(out);
    if (out.getLength() && !out.endsWith("."))
        out << ".";
    if (getDecl()->getName() && getDecl()->getName()->text.getLength() != 0)
    {
        out << getDecl()->getName()->text;
    }
}

Val* MemberDeclRef::_resolveImplOverride()
{
    auto resolvedParent = _resolveAsDeclRef(getParentOperand());
    if (resolvedParent != getParentOperand())
    {
        return getCurrentASTBuilder()->getMemberDeclRef(resolvedParent, getDecl());
    }
    return this;
}

DeclRefBase* MemberDeclRef::_getBaseOverride()
{
    return getParentOperand();
}

Decl* LookupDeclRef::getSupDecl()
{
    if (auto supType = as<DeclRefType>(getWitness()->getSup()))
    {
        return supType->getDeclRef().getDecl();
    }
    // If we reach here, something is wrong.
    SLANG_UNEXPECTED("Invalid lookup declref");
}

DeclRefBase* LookupDeclRef::_substituteImplOverride(ASTBuilder* astBuilder, SubstitutionSet subst, int* ioDiff)
{
    int diff = 0;
 
    auto substWitness = as<SubtypeWitness>(getWitness()->substituteImpl(astBuilder, subst, &diff));
    if (diff == 0)
        return this;
    (*ioDiff)++;
    
    auto substSource = as<Type>(getLookupSource()->substituteImpl(astBuilder, subst, &diff));
    SLANG_ASSERT(substSource);

    if (auto resolved = _getDeclRefFromVal(tryResolve(substWitness, substSource)))
        return resolved;

    return astBuilder->getLookupDeclRef(substSource, substWitness, getDecl());
}

void LookupDeclRef::_toTextOverride(StringBuilder& out)
{
    getLookupSource()->toText(out);
    if (out.getLength() && !out.endsWith("."))
        out << ".";
    if (getDecl()->getName() && getDecl()->getName()->text.getLength() != 0)
    {
        out << getDecl()->getName()->text;
    }
}

Val* LookupDeclRef::_resolveImplOverride()
{
    auto astBuilder = getCurrentASTBuilder();
    Val* resolved = this;

    auto newLookupSource = as<Type>(getLookupSource()->resolve());
    SLANG_ASSERT(newLookupSource);

    auto newWitness = as<SubtypeWitness>(getWitness()->resolve());
    SLANG_ASSERT(newWitness);

    if (auto resolvedVal = tryResolve(newWitness, newLookupSource))
        return resolvedVal;
    if (newLookupSource != getLookupSource() || newWitness != getWitness())
        resolved = astBuilder->getLookupDeclRef(newLookupSource, newWitness, getDecl());
    return resolved;
}

DeclRefBase* LookupDeclRef::_getBaseOverride()
{
    auto supType = getWitness()->getSup();
    if (auto declRefType = as<DeclRefType>(supType))
    {
        return declRefType->getDeclRef();
    }
    return nullptr;
}

Val* LookupDeclRef::tryResolve(SubtypeWitness* newWitness, Type* newLookupSource)
{
    auto astBuilder = getCurrentASTBuilder();
    Decl* requirementKey = getDecl();

    // If we are looking up a generic associated type requirement, the requirementKey can be the
    // Decl* to the GenericDecl itself. However, our witness table will always use the inner decl
    // as the key, so we need to extract the inner decl from the generic requirement key.
    //
    bool isGenericRequirement = false;
    if (auto genericDecl = as<GenericDecl>(requirementKey))
    {
        requirementKey = genericDecl->inner;
        isGenericRequirement = true;
    }
    RequirementWitness requirementWitness = tryLookUpRequirementWitness(astBuilder, newWitness, requirementKey);
    switch (requirementWitness.getFlavor())
    {
    default:
        // No usable value was found, so there is nothing we can do.
        break;

    case RequirementWitness::Flavor::val:
    {
        auto satisfyingVal = requirementWitness.getVal()->resolve();

        // If the lookup key is a generic decl, we need to return the resulting generic decl from the
        // DeclRefType stored in the witness table.
        //
        if (isGenericRequirement)
        {
            if (auto declRefVal = as<GenericDeclRefType>(satisfyingVal))
            {
                return declRefVal->getDeclRef();
            }
        }
        return satisfyingVal;
    }
    break;
    }

    // Hard code implementation of T.Differential.Differential == T.Differential rule.
    auto builtinReq = requirementKey->findModifier<BuiltinRequirementModifier>();
    bool isConstraint = false;
    if (!builtinReq)
    {
        if (auto parentAssocType = as<AssocTypeDecl>(requirementKey->parentDecl))
        {
            builtinReq = parentAssocType->findModifier<BuiltinRequirementModifier>();
            isConstraint = true;
        }
        if (!builtinReq)
            return nullptr;
    }
    if (builtinReq->kind != BuiltinRequirementKind::DifferentialType)
        return nullptr;
    // Is the concrete type a Differential associated type?
    auto innerDeclRefType = as<DeclRefType>(newLookupSource);
    if (!innerDeclRefType)
        return nullptr;
    auto innerBuiltinReq = innerDeclRefType->getDeclRef().getDecl()->findModifier<BuiltinRequirementModifier>();
    if (!innerBuiltinReq)
        return nullptr;
    if (innerBuiltinReq->kind != BuiltinRequirementKind::DifferentialType)
        return nullptr;
    if (isConstraint)
        return newWitness;
    if (innerDeclRefType->getDeclRef() != this)
    {
        auto result = innerDeclRefType->getDeclRef().declRefBase->resolve();
        if (result)
            return result;
    }
    return innerDeclRefType;
}

DeclRefBase* GenericAppDeclRef::_substituteImplOverride(ASTBuilder* astBuilder, SubstitutionSet subst, int* ioDiff)
{
    int diff = 0;
    auto substGenericDeclRef = getGenericDeclRef()->substituteImpl(astBuilder, subst, &diff);
    Decl* decl = getDecl();
    if (substGenericDeclRef != getGenericDeclRef())
    {
        diff = true;
        decl = remapInnerDecl(substGenericDeclRef, decl);
    }
    List<Val*> substArgs;
    for (auto arg : getArgs())
    {
        substArgs.add(arg->substituteImpl(astBuilder, subst, &diff));
    }
    if (diff == 0)
        return this;
    (*ioDiff)++;
    return astBuilder->getGenericAppDeclRef(substGenericDeclRef, substArgs.getArrayView(), decl);
}

GenericDecl* GenericAppDeclRef::getGenericDecl() { return as<GenericDecl>(getGenericDeclRef()->getDecl()); }


void GenericAppDeclRef::_toTextOverride(StringBuilder& out)
{
    auto genericDecl = as<GenericDecl>(getGenericDeclRef()->getDecl());
    Index paramCount = 0;
    for (auto member : genericDecl->members)
        if (as<GenericTypeParamDeclBase>(member) || as<GenericValueParamDecl>(member))
            paramCount++;
    getGenericDeclRef()->toText(out);
    out << "<";
    auto args = getArgs();
    Index argCount = args.getCount();
    for (Index aa = 0; aa < Math::Min(paramCount, argCount); ++aa)
    {
        if (aa != 0) out << ", ";
        args[aa]->toText(out);
    }
    out << ">";
}

Decl* GenericAppDeclRef::remapInnerDecl(DeclRefBase* resolvedGenericDeclRef, Decl* oldDecl)
{
    Decl* decl = oldDecl;
    if (resolvedGenericDeclRef->getDecl() != getGenericDeclRef()->getDecl())
    {
        // If the resolved declref points to a different generic decl,
        // we need to update this DeclRef's inner decl to map to the
        // corresponding decl in the new generic decl.
        auto oldGenericDecl = as<GenericDecl>(getGenericDeclRef()->getDecl());
        auto newGenericDecl = as<GenericDecl>(resolvedGenericDeclRef->getDecl());
        bool isInnerDecl = oldGenericDecl->inner == decl;
        if (isInnerDecl)
        {
            decl = newGenericDecl->inner;
        }
        else
        {
            // Find the index of the original inner decl.
            Index childDeclIndex = 0;
            for (auto dd : oldGenericDecl->members)
            {
                switch (dd->astNodeType)
                {
                case ASTNodeType::GenericTypeConstraintDecl:
                case ASTNodeType::GenericTypeParamDecl:
                case ASTNodeType::GenericValueParamDecl:
                case ASTNodeType::GenericTypePackParamDecl:
                    break;
                default:
                    continue;
                }
                if (dd == decl)
                    break;
                childDeclIndex++;
            }
            // Replace decl with the inner decl at the same index within
            // the new generic decl.
            for (auto dd : newGenericDecl->members)
            {
                switch (dd->astNodeType)
                {
                case ASTNodeType::GenericTypeConstraintDecl:
                case ASTNodeType::GenericTypeParamDecl:
                case ASTNodeType::GenericValueParamDecl:
                case ASTNodeType::GenericTypePackParamDecl:
                    break;
                default:
                    continue;
                }
                if (childDeclIndex == 0)
                {
                    decl = dd;
                    break;
                }
                childDeclIndex--;
                if (childDeclIndex < 0)
                {
                    SLANG_UNEXPECTED("inner decl of a generic has no correspondence in the lookup result.");
                }
            }
        }
    }
    return decl;
}

Val* GenericAppDeclRef::_resolveImplOverride()
{
    auto astBuilder = getCurrentASTBuilder();
    Val* resolvedVal = this;
    auto resolvedGenericDeclRef = _resolveAsDeclRef(getGenericDeclRef());
    bool diff = false;
    Decl* decl = getDecl();
    if (resolvedGenericDeclRef != getGenericDeclRef())
    {
        diff = true;
        decl = remapInnerDecl(resolvedGenericDeclRef, decl);
    }
    List<Val*> resolvedArgs;
    for (auto arg : getArgs())
    {
        auto resolvedArg = arg->resolve();
        resolvedArgs.add(resolvedArg);
        if (resolvedArg != arg)
            diff = true;
    }
    if (diff)
        resolvedVal = astBuilder->getGenericAppDeclRef(resolvedGenericDeclRef, resolvedArgs.getArrayView(), decl);
    return resolvedVal;
}

DeclRefBase* GenericAppDeclRef::_getBaseOverride()
{
    return getGenericDeclRef();
}

// Convenience accessors for common properties of declarations

DeclRefBase* DeclRefBase::substituteImpl(ASTBuilder* astBuilder, SubstitutionSet subst, int* ioDiff)
{
    SLANG_AST_NODE_VIRTUAL_CALL(DeclRefBase, substituteImpl, (astBuilder, subst, ioDiff));
}

DeclRefBase* DeclRefBase::getBase() { SLANG_AST_NODE_VIRTUAL_CALL(DeclRefBase, getBase, ()); }
void DeclRefBase::toText(StringBuilder& out) { SLANG_AST_NODE_VIRTUAL_CALL(DeclRefBase, toText, (out)); }

Name* DeclRefBase::getName() const
{
    return getDecl()->nameAndLoc.name;
}

SourceLoc DeclRefBase::getNameLoc() const
{
    return getDecl()->nameAndLoc.loc;
}

SourceLoc DeclRefBase::getLoc() const
{
    return getDecl()->loc;
}

DeclRefBase* DeclRefBase::getParent()
{
    auto astBuilder = getCurrentASTBuilder();
    if (!getDecl()->parentDecl)
        return nullptr;
    auto parentDecl = getDecl()->parentDecl;
    for (auto base = getBase(); base; base = base->getBase())
    {
        if (base->getDecl() == parentDecl)
            return base;
        bool parentIsChildOfBase = false;
        for (auto dd = parentDecl->parentDecl; dd; dd = dd->parentDecl)
        {
            if (dd == base->getDecl())
            {
                parentIsChildOfBase = true;
                break;
            }
        }
        if (parentIsChildOfBase)
            return astBuilder->getMemberDeclRef(base, parentDecl);
    }
    return astBuilder->getDirectDeclRef(parentDecl);
}

SubstitutionSet::operator bool() const
{
    return declRef != nullptr && !as<DirectDeclRef>(declRef);
}

Val::OperandView<Val> tryGetGenericArguments(SubstitutionSet substSet, Decl* genericDecl)
{
    if (!substSet.declRef)
        return Val::OperandView<Val>();

    DeclRefBase* currentDeclRef = substSet.declRef;
    // search for a substitution that might apply to us
    for (auto s = currentDeclRef; s; s = s->getBase())
    {
        auto genericAppDeclRef = as<GenericAppDeclRef>(s);
        if (!genericAppDeclRef)
            continue;

        // the generic decl associated with the substitution list must be
        // the generic decl that declared this parameter
        auto parentGeneric = genericAppDeclRef->getGenericDecl();
        if (parentGeneric != genericDecl)
            continue;

        return genericAppDeclRef->getArgs();
    }
    return Val::OperandView<Val>();
}

Type* SubstitutionSet::applyToType(ASTBuilder* astBuilder, Type* type) const
{
    if (!type)
        return nullptr;
    int diff = 0;
    auto newType = as<Type>(type->substituteImpl(astBuilder, *this, &diff));
    if (diff && newType)
        return newType;
    return type;
}

SubstExpr<Expr> applySubstitutionToExpr(SubstitutionSet substSet, Expr* expr)
{
    return SubstExpr<Expr>(expr, substSet);
}


DeclRefBase* SubstitutionSet::applyToDeclRef(ASTBuilder* astBuilder, DeclRefBase* otherDeclRef) const
{
    int diff = 0;
    return otherDeclRef->substituteImpl(astBuilder, *this, &diff);
}

LookupDeclRef* SubstitutionSet::findLookupDeclRef() const
{
    for (auto s = declRef; s; s = s->getBase())
    {
        if (auto lookupDeclRef = as<LookupDeclRef>(s))
            return lookupDeclRef;
    }
    return nullptr;
}

DeclRefBase* SubstitutionSet::getInnerMostNodeWithSubstInfo() const
{
    for (auto s = declRef; s; s = s->getBase())
    {
        if (as<LookupDeclRef>(s) || as<GenericAppDeclRef>(s))
            return s;
    }
    return nullptr;
}


GenericAppDeclRef* SubstitutionSet::findGenericAppDeclRef(GenericDecl* genericDecl) const
{
    for (auto s = declRef; s; s = s->getBase())
    {
        if (auto genApp = as<GenericAppDeclRef>(s))
        {
            if (genApp->getGenericDecl() == genericDecl)
                return genApp;
        }
    }
    return nullptr;
}

GenericAppDeclRef* SubstitutionSet::findGenericAppDeclRef() const
{
    for (auto s = declRef; s; s = s->getBase())
    {
        if (auto genApp = as<GenericAppDeclRef>(s))
        {
            return genApp;
        }
    }
    return nullptr;
}

DeclRef<Decl> createDefaultSubstitutionsIfNeeded(
    ASTBuilder* astBuilder,
    SemanticsVisitor* semantics,
    DeclRef<Decl>   declRef)
{
    if (declRef.as<GenericTypeParamDeclBase>())
        return declRef;
    if (declRef.as<GenericValueParamDecl>())
        return declRef;
    if (declRef.as<GenericTypeConstraintDecl>())
        return declRef;
    ShortList<GenericDecl*> genericParentDecls;
    auto lastSubstNode = SubstitutionSet(declRef).getInnerMostNodeWithSubstInfo();
    auto lastGenApp = as<GenericAppDeclRef>(lastSubstNode);
    auto lastLookup = as<LookupDeclRef>(lastSubstNode);
    for (auto dd = declRef.getDecl()->parentDecl; dd; dd = dd->parentDecl)
    {
        if (lastGenApp && dd == lastGenApp->getGenericDecl())
            break;
        if (lastLookup && lastLookup->getDecl()->isChildOf(dd))
            break;
        if (auto gen = as<GenericDecl>(dd))
            genericParentDecls.add(gen);
    }
    DeclRef<Decl> parentDeclRef = lastSubstNode;
    for (auto i = genericParentDecls.getCount() - 1; i >= 0; i--)
    {
        auto current = genericParentDecls[i];
        auto args = getDefaultSubstitutionArgs(astBuilder, semantics, current);
        if (parentDeclRef)
        {
            parentDeclRef = astBuilder->getMemberDeclRef(parentDeclRef, current);
        }
        else
        {
            parentDeclRef = astBuilder->getDirectDeclRef(current);
        }
        parentDeclRef = astBuilder->getGenericAppDeclRef(parentDeclRef.as<GenericDecl>(), args.getArrayView());
    }
    if (!parentDeclRef)
        return declRef;
    if (parentDeclRef.getDecl() == declRef.getDecl())
        return parentDeclRef;
    return astBuilder->getMemberDeclRef(parentDeclRef, declRef.getDecl());
}
}
