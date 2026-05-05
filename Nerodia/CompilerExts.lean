/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
import Lean
public import Lean.Compiler.ModPkgExt

/-! # Neordiac Configuration -/

open Lean

namespace Nerodia

/-! ## Utilites -/

@[inline] def throwInvalidExportName [Monad m] [MonadError m] (n : Name) : m α :=
  throwError s!"invalid export name '{n}'"

@[inline] def getFnSymbol[Monad m] [MonadEnv m] [MonadError m] (declName : Name) : m String := do
  let env ← getEnv
  match getExportNameFor? env declName with
  | some (.str .anonymous s) => return s
  | some _                   => throwInvalidExportName declName
  | none                     => return getSymbolStem env declName

/-! ## Configuration -/

public structure ModuleConfig where
  init? : Option String := none
  deriving Inhabited

public initialize modConfigExt : ModuleEnvExtension ModuleConfig ←
  registerModuleEnvExtension (pure {})

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
      unless modConfigExt.toEnvExtension.asyncMayModify env declName do
        throwAttrNotInAsyncCtx attrName declName env.asyncPrefix?
      let decl ← getConstInfo declName
      unless decl.type.isConstOf typeName do
        throwAttrDeclNotOfExpectedType attrName declName decl.type (mkConst typeName)
      let sym ← getFnSymbol declName
      modifyEnv fun env => modConfigExt.modifyState env ({· with init? := some sym})
  }
