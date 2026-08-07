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
import Lean.PrivateName
import Lean.Meta.ReduceEval
import Nerodia.Compiler.Meta.PyName
import Nerodia.Compiler.Meta.Extension

/-! # Nerodiac Attributes -/

open Lean Meta

namespace Nerodia.Compiler

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
    return some (← withTransparency .all <| reduceEval hintExpr)
  else
    return none

def mkPyResultCore
  (className mkName : Name) (ty : Expr) (x : Expr)
: MetaM (Expr × Option String) := do
  let u ← getDecLevel ty
  let predTy := mkConst `Nerodia.Typing
  let predExpr ← mkFreshExprMVar (some predTy)
  let predInst ← synthInstance (mkApp2 (mkConst className [u]) ty predExpr)
  let predExpr ← instantiateMVars predExpr
  let x := mkApp4 (mkConst mkName [u]) ty predExpr predInst x
  let hint? ← mkHint predExpr
  return (x, hint?)

@[inline] def mkPyResult (ty : Expr) (x : Expr) : MetaM (Expr × Option String) :=
  mkPyResultCore `Nerodia.MkPyResult `Nerodia.Internal.mkPyResult ty x

@[inline] def mkCPyResult (ty : Expr) (x : Expr) : MetaM (Expr × Option String) :=
  mkPyResultCore `Nerodia.MkCPyResult `Nerodia.Internal.mkCPyResult ty x

def mkArgCore
  (fnName : Name)
  (fn : Expr) (i : Expr) (ty : Expr) (arg : Expr)
: MetaM (Expr × Option String) := do
  let predTy := mkConst `Nerodia.Typing
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

@[inline] def mkPyBind (ty ma lam : Expr) : Expr :=
  mkApp3 (mkConst `Nerodia.Internal.pyBind) ty ma lam

def mkAuxSym
  (kind : Name) (isUnsafe : Bool) (levelParams : List Name)
  (typeName : Name) (value : Expr)
: CoreM String := do
  let name ← mkAuxDeclName kind
  withoutExporting <| addAndCompile <| .defnDecl {
    name, levelParams, value
    type := mkConst typeName
    hints := .opaque
    safety := if isUnsafe then .unsafe else .safe
  }
  getFnSymbol name

@[inline] def mkPyDoc? (env : Environment) (declName : Name) : IO (Option String) := do
  return (← findDocString? env declName).map (·.trimAscii.copy)

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

The expression is essentially of the form:

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
    let pyName ← mkPyArgName ldecl.userName (i.toNat+1)
    let pySig :=
      match pyTy? with
      | some pyTy => s!"{pyName}: {pyTy}, {pySig}"
      | none => s!"{pyName}, {pySig}"
    return (body, pySig)
  return (body, s!"({pySig}")

def mkMethodDef
  (decl : ConstantInfo)
  (modName name : String) (doc? : Option String) (pySig? : Option StrLit)
: MetaM MethodDef := do
  let declName := decl.name
  let pySigD df := pySig?.elim df (·.getString)
  let declConst := mkConst decl.name (decl.levelParams.map .param)
  let mkAuxSym := mkAuxSym `_pyFn  decl.isUnsafe decl.levelParams
  if let .const n .. := decl.type then
    if let some callConv := CallConv.ofTypeName? n then
      return {
        name, doc?, callConv
        cSym := ← getFnSymbol declName
        pySig := pySigD callConv.pySig
      }
    else
      let (val, pyRet?) ← mkCPyResult decl.type declConst
      let val := mkApp (mkConst `Nerodia.Internal.mkPyMethNoArgs) val
      let cSym ← mkAuxSym `Nerodia.PyMethNoArgs val
      let pySig := pySigD (pyRet?.elim "()" (s!"() -> {·}"))
      return {name, doc?, cSym, pySig, callConv := .noArgs}
  else
    let fn := mkStrLit s!"{modName}.{name}()"
    forallTelescope decl.type fun as rTy => do
      let allExplicit ← as.allM fun a => do
        return (← getFVarLocalDecl a).binderInfo.isExplicit
      unless allExplicit do
        throwError "All parameters of a `@[py_module_fn]` definition must be explicit."
      if as.size = 0 then
        let (rx, pyRet?) ← mkCPyResult rTy (mkAppN declConst as)
        let val := mkApp (mkConst `Nerodia.Internal.mkPyMethNoArgs) rx
        let cSym ← mkAuxSym `Nerodia.PyMethNoArgs val
        let pySig := pySigD (pyRet?.elim "()" (s!"() -> {·}"))
        return {name, doc?, cSym, pySig, callConv := .noArgs}
      else
        let (rx, pyRet?) ← mkPyResult rTy (mkAppN declConst as)
        let pySigD params := pySigD <|
          pyRet?.elim params (s!"{params} -> {·}")
        if h : as.size = 1 then
          withLocalDeclD `arg (mkConst `Nerodia.PyObject) fun arg => do
          let a := as[0]
          let ldecl ← getFVarLocalDecl a
          let (ma, pyTy?) ← mkArg fn 0 ldecl.type arg
          let pyName ← mkPyArgName ldecl.userName 0
          let pySig := pySigD <|
            match pyTy? with
            | some pyTy => s!"({pyName}: {pyTy}, /)"
            | none => s!"({pyName}, /)"
          let lam ← mkLambdaFVars #[a] rx
          let rx := mkPyBind ldecl.type ma lam
          let lam ← mkLambdaFVars #[arg] rx
          let val := mkApp (mkConst `Nerodia.Internal.mkPyMethO) lam
          let cSym ← mkAuxSym `Nerodia.PyMethO val
          return {name, doc?, cSym, pySig, callConv := .o}
        else if lt32 : as.size < UInt32.size then
          withLocalDeclD `cargs (mkConst `Nerodia.Internal.CPyArgs) fun cargs => do
          let (rx, pyParams) ← mkArgChain fn cargs as rx lt32
          let pySig := pySigD pyParams
          let lam ← mkLambdaFVars #[cargs] rx
          let mk := mkConst `Nerodia.Internal.mkPyMethFastCallUnsafe
          let val := mkApp3 mk fn (toExpr as.usize) lam
          let cSym ← mkAuxSym `Nerodia.PyMethFastCall val
          return {name, doc?, cSym, pySig, callConv := .fastCall}
        else
          throwError "Cannot generate Python function: \
            {.ofConstName declName} has too many arguments ({as.size})"

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
      let name ← mkPyDeclName declName name?
      let doc? ← mkPyDoc? env declName
      let df ← MetaM.run' <| mkMethodDef decl moduleCfg.name name doc? pySig?
      modifyModuleConfig fun cfg => {cfg with methods := cfg.methods.push df}
  }

syntax (name := py_module_attr) "py_module_attr" (ppSpace str)?
  (ppSpace atomic("(" &"ty") " := " str ")")? : attr

def mkAttrDef
  (decl : ConstantInfo)
  (name : String) (doc? : Option String) (ty? : Option StrLit)
: MetaM AttrDef := do
  let declName := decl.name
  let us := decl.levelParams.map .param
  let (val, pyTy?) ← mkCPyResult decl.type (mkConst declName us)
  let val := mkApp (mkConst `Nerodia.Internal.mkPyAttrInit) val
  let cSym ← mkAuxSym `_pyAttr decl.isUnsafe decl.levelParams `Nerodia.PyAttrInit val
  return {
    name, doc?, cSym
    ty? := ty?.elim pyTy? (some ·.getString)
  }

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
      let name ← mkPyDeclName declName name?
      let doc? ← mkPyDoc? env declName
      let df ← MetaM.run' <| mkAttrDef decl name doc? ty?
      modifyModuleConfig fun cfg => {cfg with attrs := cfg.attrs.push df}
  }
