/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Nerodiac Module Configuration -/

open Lean

namespace Nerodia.Compiler

public structure AttrDef where
  name : String
  doc? : Option String
  cSym : String
  ty? : Option String
  deriving Inhabited

public structure MethodFlags where
  private ofString ::
    protected toString : String
    deriving Inhabited

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
deriving Inhabited, DecidableEq

/-- The FFI calling convention of a Python function. -/
public structure CallConv where
  private mk ::
    -- Recursor is not public API.
    -- More conventions may be added as Python evolves.
    private raw : CallConv.Raw
    deriving Inhabited, DecidableEq

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

@[inline_if_reduce]
public def flags (self : CallConv) : MethodFlags :=
  match self.raw with
  | .varArgsNoKeywords => ⟨"METH_VARARGS"⟩
  | .varArgsWithKeywords => ⟨"METH_VARARGS | METH_KEYWORDS"⟩
  | .fastCallNoKeywords => ⟨"METH_FASTCALL"⟩
  | .fastCallWithKeywords => ⟨"METH_FASTCALL | METH_KEYWORDS"⟩
  | .method => ⟨"METH_METHOD | METH_FASTCALL | METH_KEYWORDS"⟩
  | .noArgs => ⟨"METH_NOARGS"⟩
  | .o => ⟨"METH_O"⟩

@[inline] public protected def toString (self : CallConv) : String :=
  self.flags.toString

public instance : ToString CallConv := ⟨CallConv.toString⟩

/--
Given Lean function with the C symbol name {lean}`sym`,
returns the C function signature for this calling convention.
-/
@[inline_if_reduce]
public def cSig (self : CallConv) (sym : String) : String :=
  match self.raw with
  | .varArgsNoKeywords => s!"size_t {sym}(size_t self, size_t args)"
  | .varArgsWithKeywords => s!"size_t {sym}(size_t self, size_t args, size_t kwargs)"
  | .fastCallNoKeywords => s!"size_t {sym}(size_t self, size_t args, size_t nargs)"
  | .fastCallWithKeywords => s!"size_t {sym}(size_t self, size_t arg, size_t narg, size_t kwnames)"
  | .method => s!"size_t {sym}(size_t self, size_t defining_class, size_t arg, size_t narg, size_t kwnames)"
  | .noArgs => s!"size_t {sym}(size_t self, size_t arg)"
  | .o => s!"size_t {sym}(size_t self, size_t arg)"

/--
Returns the default, untyped Python signature for a Python
module function using this calling convention.
-/
@[inline_if_reduce]
public def pySig (self : CallConv) : String :=
  match self.raw with
  | .varArgsNoKeywords => s!"(*args)"
  | .varArgsWithKeywords => s!"(*args, **kwds)"
  | .fastCallNoKeywords => s!"(*args)"
  | .fastCallWithKeywords => s!"(*args, **kwds)"
  | .method => s!"(*args, **kwds)"
  | .noArgs => "()"
  | .o => "(_, /)"

end CallConv

public structure MethodDef where
  name : String
  doc? : Option String
  callConv : CallConv
  coexist : Bool := false
  cSym : String
  pySig : String := callConv.pySig
  deriving Inhabited

/--  The C function signature of the method's Lean definition. -/
@[inline] public def MethodDef.cSig (self : MethodDef) : String :=
  self.callConv.cSig self.cSym

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
