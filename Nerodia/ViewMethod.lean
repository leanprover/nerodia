/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
-/
module
import Lean.Exception
import Lean.Environment
import Lean.Attributes
import Lean.AddDecl
import Lean.DocString
import Lean.Meta.Basic
import Lean.Compiler.BorrowedAnnotation

/-! # {lit}`@[view_method]` -/

open Lean Meta

namespace Nerodia.Internal

/--
Returns the index of the first parameter of a function
whose type is the constant {lean}`tyName` (modulo annotations).
-/
@[inline] def findSelfBinder? (tyName : Name) (fnTy : Expr) : Option Nat :=
  go 0 fnTy
where go i
  | .forallE _ d b _  =>
    if d.consumeMData.isConstOf tyName then some i else go (i+1) b
  | _ => none

/-- Replaces the type of the {lean}`i`-th binder of a function type with {lean}`ty`. -/
def updateSelfType (fnTy : Expr) (i : Nat) (ty : Expr) : Expr :=
  match fnTy, i with
  | .forallE n _ b bi, 0 => .forallE n ty b bi
  | .forallE n d b bi, i+1 => .forallE n d (updateSelfType b i ty) bi
  | e, _ => e

/-- Strips a borrow (`@&`) annotation, possibly under an {name}`optParam`. -/
def stripBorrow (ty : Expr) : Expr :=
  match ty with
  | .mdata _ e => if isMarkedBorrowed ty then stripBorrow e else ty
  | .app (.app f@(.const ``optParam _) t) v => .app (.app f (stripBorrow t)) v
  | _ => ty

/-- Strips borrow (`@&`) annotations from the binder types of the forall type. -/
def stripBinderBorrows : Expr → Expr
  | .forallE n d b bi => .forallE n (stripBorrow d) (stripBinderBorrows b) bi
  | e => e

/--
Generates the view version of the method {lean}`declName`.

For a definition {lit}`Ty.meth`, produces {lit}`TyView.meth`. Its type has the
{lit}`Ty` parameter's type replaced by {lit}`TyView α` and {lit}`{α} [ToTy α]`
binders prepended. It definition passes {lit}`toTy` to {lit}`Ty.method`.
-/
@[specialize attrName]
def mkViewMethod (attrName declName : Name) : MetaM Unit := do
  let .str tyName methStr := declName
    | throwError "invalid `[{attrName}]` attribute: \
        declaration name '{declName}' is not of the form `Ty.meth`"
  let .str basePrefix typeStr := tyName
    | throwError "invalid `[{attrName}]` attribute: \
        declaration name '{declName}' is not of the form `Ty.meth`"
  let viewName := Name.str basePrefix (typeStr ++ "View")
  let toName := Name.str viewName ("to" ++ typeStr)
  let env ← getEnv
  unless env.contains viewName do
    throwError "invalid `[{attrName}]` attribute: \
      view type '{viewName}' does not exist"
  let some toBaseInfo := env.find? toName
    | throwError "invalid `[{attrName}]` attribute: \
        '{toName}' does not exist"
  let declInfo ← getConstInfo declName
  let some selfIdx := findSelfBinder? tyName declInfo.type
    | throwError "invalid `[{attrName}]` attribute: \
        {.ofConstName declName} has no parameter of type {.ofConstName tyName}"
  -- Give the view standard `u_<n>` universe parameter names
  let numLvls := toBaseInfo.numLevelParams + declInfo.numLevelParams
  let lvlNames := List.range numLvls |>.map fun i => (`u).appendIndexAfter (i+1)
  let lvls := lvlNames.map Level.param
  let tbLvls := lvls.take toBaseInfo.numLevelParams
  let declLvls := lvls.drop toBaseInfo.numLevelParams
  let viewDeclName := Name.str viewName methStr
  forallTelescope (toBaseInfo.instantiateTypeLevelParams tbLvls) fun tbArgs tbRet => do
    let #[a, inst, tbSelf] := tbArgs
      | let className := Name.str basePrefix ("To" ++ typeStr)
        let u := Level.param <| (`u).appendIndexAfter 1
        let expectedSig : Expr :=
          mkForall `α (bi := .implicit) (.sort u.succ)  <|
          mkForall `inst (bi := .instImplicit) (mkApp (mkConst className [u]) (.bvar 0)) <|
          mkForall `self (bi := .default) (mkApp (mkConst viewName [u]) (.bvar 1)) <|
          mkConst tyName
        throwError "invalid `[{attrName}]` attribute: \
          {.ofConstName toName} does not have the expected signature{indentD expectedSig}"
    unless tbRet.consumeMData.isConstOf tyName do
      throwError "invalid `[view_method]` attribute: \
        {.ofConstName toName} does not return {.ofConstName tyName}"
    let type ← mkForallFVars #[a, inst] <|
      updateSelfType (stripBinderBorrows <| declInfo.instantiateTypeLevelParams declLvls)
        selfIdx (← inferType tbSelf)
    let value ← forallTelescope type fun args _ => do
      let fnArgs := args.extract 2 args.size
      let self := mkApp3 (mkConst toName tbLvls) args[0]! args[1]! fnArgs[selfIdx]!
      mkLambdaFVars args <| mkAppN (mkConst declName declLvls) (fnArgs.set! selfIdx self)
    withExporting do
      addAndCompile <| .defnDecl {
        name := viewDeclName
        levelParams := lvlNames
        type, value
        hints := .abbrev
        safety := if declInfo.isUnsafe then .unsafe else .safe
      }
    setInlineAttribute viewDeclName
    addInheritedDocString viewDeclName declName

initialize
  let attrName := `view_method
  registerBuiltinAttribute {
    ref := decl_name%
    name := attrName
    descr := "generate the method on the type's view"
    applicationTime := .afterCompilation
    add := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal attrName kind
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule attrName declName
      MetaM.run' <| mkViewMethod attrName declName
  }
