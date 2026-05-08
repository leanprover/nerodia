/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

/-! # Neordiac Module Configuration -/

open Lean

namespace Nerodia

public structure AttrDef where
  name : String
  doc? : Option String
  cSym : String
  ty : String

/-- The FFI calling convention of a Python function. -/
public structure CallConv where
  private ofString ::
    protected toString : String

public instance : ToString CallConv := ⟨CallConv.toString⟩

public def CallConv.o : CallConv := ⟨"METH_O"⟩

public structure MethodDef where
  name : String
  doc? : Option String
  callConv : CallConv
  cSym : String
  cSig : String
  pySig : String

public structure MethodFlags where
  private ofString ::
    protected toString : String

public instance : ToString MethodFlags := ⟨MethodFlags.toString⟩

@[inline] public def MethodDef.flags (meth : MethodDef) : MethodFlags :=
  ⟨meth.callConv.toString⟩

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
