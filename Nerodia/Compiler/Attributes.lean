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
import Lean.Meta.ReduceEval
import Nerodia.Compiler.ModuleConfig.Extension

/-! # Nerodiac Attributes -/

open Lean Meta

namespace Nerodia

/-! ## Utilities -/

@[inline] def throwInvalidExportName [Monad m] [MonadError m] (n : Name) : m α :=
  throwError s!"invalid export name '{n}'"

@[specialize] def getFnSymbol [Monad m] [MonadEnv m] [MonadError m] (declName : Name) : m String := do
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

def mkHint (p : Expr) : MetaM (Option String) := do
  let inst? ← trySynthInstance (mkApp (mkConst `Nerodia.ToTypeExpr) p)
  if let .some inst := inst? then
    let hintExpr := mkApp2 (mkConst `Nerodia.ToTypeExpr.toTypeExpr) p inst
    let hintExpr := mkApp (mkConst `Nerodia.TypeExpr.toString) hintExpr
    return some (← reduceEval hintExpr)
  else
    return none

def mkResult (ty : Expr) (x : Expr) : MetaM (Expr × Option String) := do
  let u ← getDecLevel ty
  let predTy := mkConst `Nerodia.TypePred
  let predExpr ← mkFreshExprMVar (some predTy)
  let predInst ← synthInstance (mkApp2 (mkConst `Nerodia.MkResult [u]) ty predExpr)
  let predExpr ← instantiateMVars predExpr
  let x := mkApp4 (mkConst `Nerodia.Internal.mkResult [u]) ty predExpr predInst x
  let hint? ← mkHint predExpr
  return (x, hint?)

def mkArgCore
  (fnName : Name)
  (fn : Expr) (i : Expr) (ty : Expr) (arg : Expr)
: MetaM (Expr × Option String) := do
  let predTy := mkConst `Nerodia.TypePred
  let predExpr ← mkFreshExprMVar (some predTy)
  let inst ← synthInstance (mkApp2 (mkConst `Nerodia.OfPyArg) ty predExpr)
  let x := mkApp6 (mkConst fnName) ty predExpr inst fn i arg
  let hint? ← mkHint predExpr
  return (x, hint?)

@[inline] def mkArg
  (fn : Expr) (i : Nat) (ty : Expr) (arg : Expr)
: MetaM (Expr × Option String) := do
  mkArgCore `Nerodia.OfPyArg.ofPyArg fn (toExpr (i+1)) ty arg

@[inline] def mkCArg
  (fn : Expr) (i : USize) (ty : Expr) (args : Expr)
: MetaM (Expr × Option String) := do
  mkArgCore `Nerodia.Internal.ofPyArgUnsafe fn (toExpr i) ty args

def mkPyBind (ty ma lam : Expr) : Expr :=
  mkApp6 (mkConst ``Bind.bind [0, 0])
    (mkConst `Nerodia.PyIO) (mkConst `Nerodia.PyIO.instBind)
    ty (mkConst `Nerodia.PyAny) ma lam

def mkAuxSym
  (kind : Name) (isUnsafe : Bool) (levelParams : List Name)
  (typeName : Name) (value : Expr)
: CoreM String := do
  let name ← mkAuxDeclName kind
  addAndCompile <| .defnDecl {
    name, levelParams, value
    type := mkConst typeName
    hints := .opaque
    safety := if isUnsafe then .unsafe else .safe
  }
  getFnSymbol name

@[inline] def mkPyName (name : Name) : String :=
  name.getString! -- TODO: validate / mangle Lean name for Python

@[inline] def addMethodDef [MonadEnv m] (df : MethodDef) : m PUnit :=
  modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}

@[inline_if_reduce]
def CallConv.ofTypeName? (n : Name) : Option CallConv :=
  match n with
  | `Nerodia.PyMethNoArgs => some .noArgs
  | `Nerodia.PyMethFastCall => some .fastCall
  | `Nerodia.PyMethO => some .o
  | _ => none

/--
Constructs an expression which converts the Python arguments in {lean}`cargs`
into Lean objects and passes them to {lean}`body` via a bind chain. Returns the
expression paired with the inferred parameter list of the Python function.

The expression is of the form:

{given -show}`fn : String, n : USize`
{given -show}`ofPyArgUnsafe : String → USize → Expr → Id Expr`
{given -show}`body : Expr → Expr → Id Expr`
```leanTerm
do
  let args₀ ← ofPyArgUnsafe fn 0 cargs
  -- ...
  let argsₙ ← ofPyArgUnsafe fn n cargs
  body args₀ /- ... -/ argsₙ
```
-/
def mkArgChain
  (fn : Expr) (cargs : Expr) (args : Array Expr) (body : Expr)
  (lt32 : args.size < UInt32.size)
: MetaM (Expr × String) := do
  let s := (body, s!"/)")
  let (body, pySig) ← args.size.foldRevM (init := s) fun i h (body, pySig) => do
    let a := args[i]
    let ldecl ← getFVarLocalDecl a
    let i := USize.ofNat32 i (Nat.lt_trans h lt32)
    let (ma, pyTy?) ← mkCArg fn i ldecl.type cargs
    let lam ← mkLambdaFVars #[a] body
    let body := mkPyBind ldecl.type ma lam
    let pyName := mkPyName ldecl.userName
    let pySig :=
      match pyTy? with
      | some pyTy => s!"{pyName}: {pyTy}, {pySig}"
      | none => s!"{pyName}, {pySig}"
    return (body, pySig)
  return (body, s!"({pySig}")

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
      -- TODO: Validate the name is a legal Python identifier
      let name := name?.elim declName.getString! (·.getString)
      let doc? := (← findDocString? env declName).map (·.trimAscii.copy)
      let pySigD df := pySig?.elim df (·.getString)
      let declConst := mkConst decl.name (decl.levelParams.map .param)
      let mkAuxSym := mkAuxSym `_pyFn  decl.isUnsafe decl.levelParams
      if let .const n .. := decl.type then
        if let some callConv := CallConv.ofTypeName? n then
          addMethodDef {
            name, doc?, callConv
            cSym := ← getFnSymbol declName
            pySig := pySigD callConv.pySig
          }
        else MetaM.run' do
          let (val, pyRet?) ← mkResult decl.type declConst
          let val := mkApp (mkConst `Nerodia.PyMethNoArgs.ofCPyIO) val
          let cSym ← mkAuxSym `Nerodia.PyMethNoArgs val
          let pySig := pySigD (pyRet?.elim "()" (s!"() -> {·}"))
          addMethodDef {name, doc?, cSym, pySig, callConv := .noArgs}
      else
        MetaM.run' do
        let fn := mkStrLit s!"{moduleCfg.name}.{name}()"
        forallTelescope decl.type fun as rTy => do
          let allExplicit ← as.allM fun a => do
            return (← getFVarLocalDecl a).binderInfo.isExplicit
          unless allExplicit do
            throwError "All parameters of a `@[py_module_fn]` definition must be explicit."
          let (rx, pyRet?) ← mkResult rTy (mkAppN declConst as)
          let pySigD params := pySigD <|
            pyRet?.elim params (s!"{params} -> {·}")
          if as.size = 0 then
            let val := mkApp (mkConst `Nerodia.PyMethNoArgs.ofCPyIO) rx
            let cSym ← mkAuxSym `Nerodia.PyMethNoArgs val
            let pySig := pySigD "()"
            addMethodDef {name, doc?, cSym, pySig, callConv := .noArgs}
          else if h : as.size = 1 then
            withLocalDeclD `arg (mkConst `Nerodia.PyAny) fun arg => do
            let a := as[0]
            let ldecl ← getFVarLocalDecl a
            let (ma, pyTy?) ← mkArg fn 0 ldecl.type arg
            let pyName := mkPyName ldecl.userName
            let pySig := pySigD <|
              match pyTy? with
              | some pyTy => s!"({pyName}: {pyTy}, /)"
              | none => s!"({pyName}, /)"
            -- TODO: Use something more efficient than `CPyIO.toPyIO` here?
            let rx := mkApp2 (mkConst `Nerodia.CPyIO.toPyIO) (mkConst `Nerodia.PyAny) rx
            let lam ← mkLambdaFVars #[a] rx
            let rx := mkPyBind ldecl.type ma lam
            let lam ← mkLambdaFVars #[arg] rx
            let val := mkApp (mkConst `Nerodia.PyMethO.ofPyIO') lam
            let cSym ← mkAuxSym `Nerodia.PyMethO val
            addMethodDef {name, doc?, cSym, pySig, callConv := .o}
          else if lt32 : as.size < UInt32.size then
            withLocalDeclD `cargs (mkConst `Nerodia.CPyArgs) fun cargs => do
            -- TODO: Use something more efficient than `CPyIO.toPyIO` here?
            let rx := mkApp2 (mkConst `Nerodia.CPyIO.toPyIO) (mkConst `Nerodia.PyAny) rx
            let (rx, pyParams) ← mkArgChain fn cargs as rx lt32
            let rx := mkApp2 (mkConst `Nerodia.PyIO.toCPyIO) (mkConst `Nerodia.TypePred.any) rx
            let pySig := pySigD pyParams
            let lam ← mkLambdaFVars #[cargs] rx
            let val := mkApp3 (mkConst `Nerodia.Internal.mkPyMethFastCallUnsafe)
              fn (toExpr as.usize) lam
            let cSym ← mkAuxSym `Nerodia.PyMethFastCall val
            addMethodDef {name, doc?, cSym, pySig, callConv := .fastCall}
          else
            throwError "Cannot generate Python function: \
              {.ofConstName declName} has too many arguments ({as.size})"
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
      -- TODO: Validate the name is a legal Python identifier
      let name := name?.elim declName.getString! (·.getString)
      let doc? := (← findDocString? env declName).map (·.trimAscii.copy)
      MetaM.run' do
      let us := decl.levelParams.map .param
      let (val, pyTy?) ← mkResult decl.type (mkConst declName us)
      let val := mkApp (mkConst `Nerodia.PyAttrInit.ofCPyIO) val
      let cSym ← mkAuxSym `_pyAttr decl.isUnsafe decl.levelParams `Nerodia.PyAttrInit val
      let df : AttrDef := {
        name, doc?, cSym
        ty? := ty?.elim pyTy? (some ·.getString)
      }
      modifyModuleConfig fun cfg => {cfg with attrs := cfg.attrs.push df}
  }
