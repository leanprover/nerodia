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

def mkResult (ty : Expr) (x : Expr) : MetaM (Expr × String) := do
  let u ← getDecLevel ty
  let hintTy := mkConst ``String
  let hintExpr ← mkFreshExprMVar (some hintTy)
  let inst ← synthInstance (mkApp2 (mkConst `Nerodia.MkAttr [u]) ty hintExpr)
  let hintExpr ← instantiateMVars hintExpr
  let hint ← unsafe evalExpr String hintTy hintExpr
  let x := mkApp4 (mkConst `Nerodia.MkAttr.mkAttr [u]) ty hintExpr inst x
  return (x, hint)

def mkArgCore
  (fnName : Name)
  (fn : Expr) (i : Expr) (ty : Expr) (arg : Expr)
: MetaM (Expr × String) := do
  let hintTy := mkConst ``String
  let hintExpr ← mkFreshExprMVar (some hintTy)
  let inst ← synthInstance (mkApp2 (mkConst `Nerodia.OfPyArg) ty hintExpr)
  let hintExpr ← instantiateMVars hintExpr
  let hint ← unsafe evalExpr String hintTy hintExpr
  let x := mkApp6 (mkConst fnName) ty hintExpr inst fn i arg
  return (x, hint)

@[inline] def mkArg (fn : Expr) (i : Nat) (ty : Expr) (arg : Expr) : MetaM (Expr × String) := do
  mkArgCore `Nerodia.OfPyArg.ofPyArg fn (toExpr (i+1)) ty arg

@[inline] def mkCArg (fn : Expr) (i : USize) (ty : Expr) (args : Expr) : MetaM (Expr × String) := do
  mkArgCore `Nerodia.ofPyArgUnsafe fn (toExpr i) ty args

@[inline] def mkPyBind (ty ma lam : Expr) : Expr :=
  mkApp6 (mkConst ``Bind.bind [0, 0])
    (mkConst `Nerodia.PyIO) (mkConst `Nerodia.PyIO.instBind)
    ty (mkConst `Nerodia.PyObject) ma lam

def mkAuxSym
  (name : Name) (levelParams : List Name) (typeName : Name) (value : Expr)
: CoreM String := do
  let auxDeclName ← mkAuxDeclName name
  addAndCompile <| .defnDecl {
    name := auxDeclName
    levelParams
    type := mkConst typeName
    value
    hints := .opaque
    safety := .safe
  }
  getFnSymbol auxDeclName

initialize
  let attrName := `py_module_fn
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
      let some moduleCfg := modCfgExt.getState env
        | throwAttrWithoutModuleConfig attrName
      let decl ← getConstInfo declName
      let name := name?.elim declName.getString! (·.getString)
      let doc? := (← findDocString? env declName).map (·.trimAscii.copy)
      if let .const n .. := decl.type then
        match n with
        | `Nerodia.PyMethNoArgs =>
          let cSym ← getFnSymbol declName
          let df : MethodDef := {
            name, doc?, cSym
            callConv := .noArgs
            cSig := s!"size_t {cSym}(size_t self, size_t arg)"
            pySig := pySig?.elim "()" (·.getString)
          }
          modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}
        | `Nerodia.PyMethFastCall =>
          let cSym ← getFnSymbol declName
          let df : MethodDef := {
            name, doc?, cSym
            callConv := .fastCall
            cSig := s!"size_t {cSym}(size_t self, size_t args, size_t nargs)"
            pySig := pySig?.elim "(*_, /)" (·.getString)
          }
          modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}
        | `Nerodia.PyMethO =>
          let cSym ← getFnSymbol declName
          let df : MethodDef := {
            name, doc?, cSym
            callConv := .o
            cSig := s!"size_t {cSym}(size_t self, size_t arg)"
            pySig := pySig?.elim "(_, /)" (·.getString)
          }
          modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}
        | _ =>
          MetaM.run' do
          let us := decl.levelParams.map .param
          let (val, pyTy) ← mkResult decl.type (mkConst decl.name us)
          let val := mkApp (mkConst `Nerodia.PyMethNoArgs.ofCPyIO) val
          let cSym ← mkAuxSym `_pyFn decl.levelParams `Nerodia.PyMethNoArgs val
          let df : MethodDef := {
            name, doc?, cSym
            callConv := .noArgs
            cSig := s!"size_t {cSym}(size_t self, size_t arg)"
            pySig := pySig?.elim s!"() -> {pyTy}" (·.getString)
          }
          modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}
      else
        MetaM.run' do
        let fn := mkStrLit s!"{moduleCfg.name}.{name}()"
        forallTelescope decl.type fun as rTy => do
          let argIdxs : Array (Fin as.size) ← as.size.foldM (init := #[]) fun i h is => do
            let ldecl ← getFVarLocalDecl as[i]
            return if ldecl.binderInfo.isExplicit then is.push ⟨i, h⟩ else is
          let us := decl.levelParams.map .param
          let rx := mkAppN (mkConst decl.name us) as
          let (rx, pyRet) ← mkResult rTy rx
          if argIdxs.size = 0 then
            let us := decl.levelParams.map .param
            let (val, pyTy) ← mkResult decl.type (mkConst decl.name us)
            let val := mkApp (mkConst `Nerodia.PyMethNoArgs.ofCPyIO) val
            let cSym ← mkAuxSym `_pyFn decl.levelParams `Nerodia.PyMethNoArgs val
            let df : MethodDef := {
              name, doc?, cSym
              callConv := .noArgs
              cSig := s!"size_t {cSym}(size_t self, size_t arg)"
              pySig := pySig?.elim s!"() -> {pyTy}" (·.getString)
            }
            modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}
          else if h : argIdxs.size = 1 then
            withLocalDeclD `arg (mkConst `Nerodia.PyObject) fun arg => do
            let rx := mkApp2 (mkConst `Nerodia.CPyIO.toPyIO) (mkConst `Nerodia.PyObject) rx
            let a := as[argIdxs[0]]
            let ldecl ← getFVarLocalDecl a
            let (ma, pyTy) ← mkArg fn 0 ldecl.type arg
            let lam ← mkLambdaFVars #[a] rx
            let rx := mkPyBind ldecl.type ma lam
            let pyName := ldecl.userName.getString!
            let lam ← mkLambdaFVars #[arg] rx
            let val := mkApp (mkConst `Nerodia.PyMethO.ofPyIO') lam
            let cSym ← mkAuxSym `_pyFn decl.levelParams `Nerodia.PyMethO val
            let df : MethodDef := {
              name, doc?, cSym
              callConv := .o
              cSig := s!"size_t {cSym}(size_t self, size_t arg)"
              pySig := pySig?.elim s!"({pyName}: {pyTy}, /) -> {pyRet}" (·.getString)
            }
            modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}
          else if lt32 : argIdxs.size < UInt32.size then
            withLocalDeclD `cargs (mkConst `Nerodia.CPyArgs) fun args => do
            withLocalDeclD `nargs (mkConst ``USize) fun nargs => do
            let rx := mkApp2 (mkConst `Nerodia.CPyIO.toPyIO) (mkConst `Nerodia.PyObject) rx
            let init := (rx, s!"/) -> {pyRet}")
            let (rx, pySig) ← argIdxs.size.foldRevM (init := init) fun i h (rx, pySig) => do
              let a := as[argIdxs[i]]
              let ldecl ← getFVarLocalDecl a
              let i := USize.ofNat32 i (Nat.lt_trans h lt32)
              let (ma, pyTy) ← mkCArg fn i ldecl.type args
              let lam ← mkLambdaFVars #[a] rx
              let rx := mkPyBind ldecl.type ma lam
              let pyName := ldecl.userName.getString!
              let pySig := s!"{pyName}: {pyTy}, {pySig}"
              return (rx, pySig)
            let nx := toExpr argIdxs.size.toUSize
            let mTy := mkApp (mkConst `Nerodia.PyIO) (mkConst `Nerodia.PyObject)
            let eqN := mkApp2 (mkApp (mkConst ``Eq [1]) (mkConst ``USize)) nargs nx
            let err := mkApp4 (mkConst `Nerodia.raiseArityNotEq [0]) (mkConst `Nerodia.PyObject) fn nx nargs
            let err := mkApp2 (mkConst `Nerodia.CPyIO.toPyIO) (mkConst `Nerodia.PyObject) err
            let deq := mkApp2 (mkConst ``instDecidableEqUSize) nargs nx
            let rx := mkApp5 (mkConst ``ite [1]) mTy eqN deq rx err
            let lam ← mkLambdaFVars #[args, nargs] rx
            let val := mkApp (mkConst `Nerodia.PyMethFastCall.mkInternalUnsafe) lam
            let cSym ← mkAuxSym `_pyFn decl.levelParams `Nerodia.PyMethFastCall val
            let df : MethodDef := {
              name, doc?, cSym
              callConv := .fastCall
              cSig := s!"size_t {cSym}(size_t self, size_t args, size_t nargs)"
              pySig := pySig?.elim s!"({pySig}" (·.getString)
            }
            modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}
          else
            throwError "Cannot generate Python function: \
              {.ofConstName declName} has too many arguments ({argIdxs.size})"
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
      let us := decl.levelParams.map .param
      let (val, pyTy) ← mkResult decl.type (mkConst declName us)
      let cSym ← mkAuxSym `_pyAttr decl.levelParams `Nerodia.PyAttrInit val
      let df : AttrDef := {
        name, doc?, cSym
        ty := ty?.elim pyTy (·.getString)
      }
      modifyModuleConfig fun cfg => {cfg with attrs := cfg.attrs.push df}
  }
