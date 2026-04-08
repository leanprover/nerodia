import Lake
open System Lake DSL
open Lean (Json ToJson FromJson toJson fromJson?)

package nerodia where
  leanOptions := #[⟨`doc.verso, true⟩]
  buildType := .debug

/-! ## Python -/

structure PyConfig where
  version : String
  hexVersion : Nat
  includeDirs : Array FilePath
  libDir : FilePath
  lib3 : String × FilePath
  lib3x : String × FilePath
  deriving ToJson, FromJson

instance : QueryText PyConfig := ⟨(toJson · |>.compress)⟩

input_file pyconfigSrc where
  text := true
  path := "pyconfig.py"

def minHexVersion : Nat := 0x030D00A0 -- 3.13 (a0)

target pyconfig : PyConfig := do
  (← pyconfigSrc.fetch).mapM fun srcFile => do
    let python3 := (← IO.getEnv "PYTHON3").getD "python3"
    let out ← captureProc {cmd := python3, args := #[srcFile.toString]}
    match Json.parse out >>= fromJson? with
    | .ok py =>
      unless py.hexVersion ≥ minHexVersion do
        error s!"Nerodia requires Python 3.13+, got {py.version}"
      setTrace <| .ofHash
        (pureHash py.lib3.1) s!"pyconfig: {py.lib3.1}"
      return py
    | .error e =>
      error s!"configuration script produced unexpect output; {e}:\n{out}"

target libpython3 : Dynlib := do
  return (← pyconfig.fetch).map (sync := true) fun py =>
    {name := py.lib3.1, path := py.lib3.2}

target libpython3x : Dynlib := do
  return (← pyconfig.fetch).map (sync := true) fun py =>
    {name := py.lib3x.1, path := py.lib3x.2}

/-! ## Nerodia FFI -/

input_file nerodia.c where
  text := true
  path := "ffi" / "nerodia.c"

target nerodia.o pkg : FilePath := do
  let cJob ← nerodia.c.fetch
  (← pyconfig.fetch).bindM fun py => do
    newTrace
    let oFile := pkg.irDir / "c" / "nerodia.o"
    let weakArgs := py.includeDirs.map (s!"-I{·}")
      |>.push s!"-I{← getLeanIncludeDir}"
    let traceArgs := pkg.buildType.leancArgs ++ #[
      s!"-DPy_LIMITED_API={minHexVersion}",
      "-fPIC", "-std=c17", "-Wall"
    ]
    let cc := (← IO.getEnv "CC").getD "cc"
    buildO oFile cJob weakArgs traceArgs cc getLeanTrace

/-! ## Nerodia Lean -/

@[default_target]
lean_lib Nerodia where
  defaultFacets := #[LeanLib.staticFacet, LeanLib.sharedFacet]
  moreLinkObjs := #[nerodia.o]
  moreLinkLibs := #[libpython3]

lean_lib NerodiaTests where
  srcDir := "tests"
  globs := #[`NerodiaTests.+]
  precompileModules := true
  dynlibs :=
    -- On non-Windows, libpython3 = libpython3x
    if System.Platform.isWindows then #[libpython3x]
    else #[]

lean_exe testExe where
  srcDir := "tests"
  -- The Lean toolchain's sysroot may have an older glibc than the
  -- Python library, causing lld to reject unresolved versioned symbols.
  weakLinkArgs :=
    if System.Platform.isWindows || System.Platform.isOSX then #[]
    else #["-Wl,--allow-shlib-undefined"]

@[test_driver]
script test do
  runBuild do
    let pyJob ← pyconfig.fetch
    let libJob ← Nerodia.fetch
    discard <| NerodiaTests.fetch
    let exeJob ← testExe.fetch
    discard <| withRegisterJob "testExe test" do
      pyJob.bindM fun py =>
      exeJob.mapM fun exeFile => do
        let env ← id do
          -- ensures the executable can find Python's shared libraries
          let path ← getAugmentedSharedLibPath
          let path : SearchPath := py.libDir :: path
          return #[(sharedLibPathEnvVar, some path.toString)]
        let out ← captureProc {cmd := exeFile.toString, env}
        unless out == py.version do
          error s!"incorrect output: expected\
            \n  {py.version}\
            \ngot\
            \n  {out}"
    withRegisterJob "testModule test" <| libJob.mapM fun _ => do proc {
      cmd := "uv",
      args := #["-q", "run","--reinstall", "test.py"]
      cwd := FilePath.mk "tests" / "testModule"
      -- ensures Python can find Lean's shared libraries
      env := ← getAugmentedEnv
    }
  return 0
