/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Lean.Exception
import Lean.Environment
import Lean.Compiler.ExportAttr
import Lean.Meta.SynthInstance
import Lean.Meta.DecLevel
import Lean.AddDecl
import Lean.DocString
import Lean.Meta.Eval
import Nerodia.Compiler.ModuleConfig.Extension

/-! # Nerodiac Attributes -/

open Lean Meta

namespace Nerodia

/-! ## Utilities -/

@[inline] def throwInvalidExportName [Monad m] [MonadError m] (n : Name) : m α :=
  throwError s!"invalid export name '{n}'"

@[inline] def getFnSymbol [Monad m] [MonadEnv m] [MonadError m] (declName : Name) : m String := do
  let env ← getEnv
  match getExportNameFor? env declName with
  | some (.str .anonymous s) => return s
  | some _                   => throwInvalidExportName declName
  | none                     => return getSymbolStem env declName

/-! ## Attributes -/

@[inline] def throwAttrWithoutModuleConfig [Monad m] [MonadError m] (attrName : Name) : m α :=
  throwError m!"Cannot add attribute `[{attrName}]`: \
    A Python module must first be configured with `py_module`."

initialize
  let attrName := `py_module_init
  let typeName := `Nerodia.PyModuleInit
  registerBuiltinAttribute {
    ref := decl_name%
    name := attrName
    descr := "mark a definition as the Python module initializer"
    applicationTime := .afterCompilation
    add := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal attrName kind
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule attrName declName
      unless modCfgExt.toEnvExtension.asyncMayModify env declName do
        throwAttrNotInAsyncCtx attrName declName env.asyncPrefix?
      let decl ← getConstInfo declName
      unless decl.type.isConstOf typeName do
        throwAttrDeclNotOfExpectedType attrName declName decl.type (mkConst typeName)
      unless hasModuleConfig env do
        throwAttrWithoutModuleConfig attrName
      let sym ← getFnSymbol declName
      modifyModuleConfig fun cfg => {cfg with inits := cfg.inits.push sym}
  }

syntax (name := py_module_fn) "py_module_fn" (ppSpace str)?
  (ppSpace atomic("(" &"sig") " := " str ")")? : attr

initialize
  let attrName := `py_module_fn
  let typeName := `Nerodia.PyMethO
  registerBuiltinAttribute {
    ref := decl_name%
    name := attrName
    descr := "mark a definition as a Python module function"
    applicationTime := .afterCompilation
    add := fun declName stx kind => do
      let `(attr|py_module_fn $[$name?:str]? $[(sig := $pySig?)]?) := stx
        | throwError "ill-formed [py_module_fn] attribute syntax"
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal attrName kind
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule attrName declName
      unless modCfgExt.toEnvExtension.asyncMayModify env declName do
        throwAttrNotInAsyncCtx attrName declName env.asyncPrefix?
      let decl ← getConstInfo declName
      unless decl.type.isConstOf typeName do
        throwAttrDeclNotOfExpectedType attrName declName decl.type (mkConst typeName)
      unless hasModuleConfig env do
        throwAttrWithoutModuleConfig attrName
      let cSym ← getFnSymbol declName
      let df : MethodDef := {
        cSym
        callConv := .o
        doc? := (← findDocString? env declName).map (·.trimAscii.copy)
        name := name?.elim declName.getString! (·.getString)
        cSig := s!"size_t {cSym}(size_t self, size_t arg)"
        pySig := pySig?.elim "(_, /)" (·.getString)
      }
      modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}
  }

syntax (name := py_module_attr) "py_module_attr" (ppSpace str)?
  (ppSpace atomic("(" &"ty") " := " str ")")? : attr

initialize
  let attrName := `py_module_attr
  registerBuiltinAttribute {
    ref := decl_name%
    name := attrName
    descr := "mark a definition as a Python module attribute"
    applicationTime := .afterCompilation
    add := fun declName stx kind => do
      let `(attr|py_module_attr $[$name?:str]? $[(ty := $ty?)]?) := stx
        | throwError "ill-formed [py_module_attr] attribute syntax"
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal attrName kind
      let env ← getEnv
      -- TODO: `attribute` could be used to include definitions in other modules
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule attrName declName
      unless modCfgExt.toEnvExtension.asyncMayModify env declName do
        throwAttrNotInAsyncCtx attrName declName env.asyncPrefix?
      let decl ← getConstInfo declName
      unless hasModuleConfig env do
        throwAttrWithoutModuleConfig attrName
      let name := name?.elim declName.getString! (·.getString)
      let doc? := (← findDocString? env declName).map (·.trimAscii.copy)
      MetaM.run' do
      let u ← getDecLevel decl.type
      let tyTy := (mkConst ``String)
      let ty ← mkFreshExprMVar (some tyTy)
      let inst ← synthInstance (mkApp2 (mkConst `Nerodia.MkAttr [u]) decl.type ty)
      let ty ← instantiateMVars ty
      let pyTy ← unsafe evalExpr String tyTy ty
      let attrDeclName ← mkAuxDeclName `_pyAttr
      let us := decl.levelParams.map .param
      addAndCompile <| .defnDecl {
        name := attrDeclName
        levelParams := decl.levelParams
        type := mkApp (mkConst `Nerodia.CPyIO [levelZero]) (mkConst `Nerodia.PyObject)
        value := mkApp4 (mkConst `Nerodia.MkAttr.mkAttr [u])
          decl.type ty inst (mkConst declName us)
        hints := .opaque
        safety := .safe
      }
      let df : AttrDef := {
        name, doc?
        cSym := ← getFnSymbol attrDeclName
        ty := ty?.elim pyTy (·.getString)
      }
      modifyModuleConfig fun cfg => {cfg with attrs := cfg.attrs.push df}
  }
