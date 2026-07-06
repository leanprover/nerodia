/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Nerodiac Module Configuration -/

open Lean

namespace Nerodia

public structure AttrDef where
  name : String
  doc? : Option String
  cSym : String
  ty : String

public structure MethodFlags where
  private ofString ::
    protected toString : String

public instance : ToString MethodFlags := ⟨MethodFlags.toString⟩

/-- Implementation detail of {lit}`CallConv`. -/
inductive CallConv.Raw
| varArgsNoKeywords
| varArgsWithKeywords
| fastCallNoKeywords
| fastCallWithKeywords
| method
| noArgs
| o
deriving Nonempty, DecidableEq

/-- The FFI calling convention of a Python function. -/
public structure CallConv where
  private mk ::
    -- Recursor is not public API.
    -- More conventions may be added as Python evolves.
    private raw : CallConv.Raw
    deriving Nonempty, DecidableEq

namespace CallConv

@[inline] public def varArgs (keywords := false) : CallConv :=
  if keywords then ⟨.varArgsWithKeywords⟩ else ⟨.varArgsNoKeywords⟩

@[inline] public def fastCall (keywords := false) : CallConv :=
  if keywords then ⟨.fastCallWithKeywords⟩ else ⟨.fastCallNoKeywords⟩

@[inline] public def noArgs : CallConv :=
  ⟨.noArgs⟩

@[inline] public def method : CallConv :=
  ⟨.method⟩

@[inline] public def o : CallConv :=
  ⟨.o⟩

theorem raw_ctorIdx_lt : (raw self).ctorIdx < 7 := by
  cases self.raw <;> decide

@[inline] public def flags (self : CallConv) : MethodFlags :=
  ⟨strs[inline self.raw.ctorIdx]'raw_ctorIdx_lt⟩
where
  strs : Vector String 7 := .mk #[
    "METH_VARARGS", -- varArgsNoKeywords
    "METH_VARARGS | METH_KEYWORDS", -- varArgsWithKeywords
    "METH_FASTCALL", -- fastCallNoKeywords
    "METH_FASTCALL | METH_KEYWORDS", -- fastCallWithKeywords
    "METH_METHOD | METH_FASTCALL | METH_KEYWORDS", -- method
    "METH_NOARGS", -- noArgs
    "METH_O" -- o
  ] rfl

@[inline] public protected def toString (self : CallConv) : String :=
  self.flags.toString

public instance : ToString CallConv := ⟨CallConv.toString⟩

/--
Returns the C parentheical parameter list for this calling convention.

**Example:** {assert}`cParams .o = "(size_t self, size_t arg)"`
-/
@[inline] public def cParams (self : CallConv) : String :=
  strs[self.raw.ctorIdx]'raw_ctorIdx_lt
where
  strs : Vector String 7 := .mk #[
    "(size_t self, size_t args)", -- varArgsNoKeywords
    "(size_t self, size_t args, size_t kwargs)", -- varArgsWithKeywords
    "(size_t self, size_t args, size_t nargs)", -- fastCallNoKeywords
    "(size_t self, size_t arg, size_t narg, size_t kwnames)", -- fastCallWithKeywords
    "(size_t self, size_t defining_class, size_t arg, size_t narg, size_t kwnames)", -- method
    "(size_t self, size_t arg)", -- noArgs
    "(size_t self, size_t arg)", -- o
  ] rfl

/--
Returns the default, untyped Python signature for a Python
module function using this calling convention.
-/
@[inline] public def pySig (self : CallConv) : String :=
  strs[self.raw.ctorIdx]'raw_ctorIdx_lt
where
  @[inline] strs : Vector String 7 := .mk #[
    "(*args)", -- varArgsNoKeywords
    "(*args, **kwds)", -- varArgsWithKeywords
    "(*args)", -- fastCallNoKeywords
    "(*args, **kwds)", -- fastCallWithKeywords
    "(*args, **kwds)", -- method
    "()", -- noArgs
    "(_, /)", -- o
  ] rfl

end CallConv

public structure MethodDef where
  name : String
  doc? : Option String
  callConv : CallConv
  coexist : Bool := false
  cSym : String
  pySig : String := callConv.pySig

public def MethodDef.flags (self : MethodDef) : MethodFlags :=
  let flags := self.callConv.flags.toString
  if self.coexist then
    ⟨s!"{flags} | METH_COEXIST"⟩
  else
    ⟨flags⟩

public structure ModuleConfig where
  name : String
  doc? : Option String := none
  inits : Array String := #[]
  attrs : Array AttrDef := #[]
  methods : Array MethodDef := #[]
  deriving Inhabited

public structure ModuleDef extends config : ModuleConfig where
  leanInit : String
  leanModule : Lean.Name
