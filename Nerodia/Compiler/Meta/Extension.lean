/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module
public import Lean.Compiler.ModPkgExt
public import Nerodia.Compiler.Data.ModuleConfig.Basic

/-! # Nerodiac Configuration Extension -/

open Lean

namespace Nerodia.Compiler

public abbrev ModuleConfigExtension := ModuleEnvExtension (Option ModuleConfig)

public initialize modCfgExt : ModuleConfigExtension ←
  registerModuleEnvExtension (pure none)

@[inline] public def hasModuleConfig (env : Environment) : Bool :=
  modCfgExt.getState env |>.isSome

@[inline] public def modifyModuleConfig [MonadEnv m] (f : ModuleConfig → ModuleConfig) : m PUnit :=
  modifyEnv fun env => modCfgExt.modifyState env (·.map f)
