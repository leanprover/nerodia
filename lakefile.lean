import Lake
open System Lake DSL
open Lean (Json ToJson FromJson toJson fromJson?)

package nerodia where
  leanOptions := #[⟨`doc.verso, true⟩]
  buildType := .debug

/-! ## Python -/

structure PyConfig where
  exe : FilePath
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
  let pkgDir := __dir__
  let testModuleDir := pkgDir / "tests" / "testModule"
  runBuild do
    let pyJob ← pyconfig.fetch
    let libJob ← Nerodia.fetch
    discard <| NerodiaTests.fetch
    let exeJob ← testExe.fetch
    discard <| withRegisterJob "testExe test" do
      pyJob.bindM (sync := true) fun py =>
      exeJob.mapM fun exeFile => do
        let out ← captureProc {cmd := exeFile.toString, env := ← getPyEnv py}
        validateOutput py.version out
    let installJob ← withRegisterJob "testModule install" <| libJob.mapM fun _ => do proc {
      cmd := "uv",
      args := #["-q", "sync", "--reinstall"]
      cwd := testModuleDir
      -- ensures Python can find Lean's shared libraries
      env := ← getAugmentedEnv
    }
    discard <| withRegisterJob "testModule test" <| installJob.mapM fun _ => do proc {
      cmd := "uv",
      args := #["-q", "run", "--no-sync", "test.py"]
      cwd := testModuleDir
      -- ensures Python can find Lean's shared libraries
      env := ← getAugmentedEnv
    }
    withRegisterJob "testModule lpl" <| installJob.mapM fun _ => do
      let out ← captureProc {
        cmd := "uv",
        args := #["run", "--no-sync", (← getLake).toString, "query", "--json", "lpl", "pyconfig"]
        cwd := testModuleDir
        env := ← getAugmentedEnv
      }
      let [lpl, pyconfig] := out.lines.toStringList
        | error s!"unexpected lake output: {out}"
      let lpl ← match Json.parse lpl >>= fromJson? with
        | .ok a => pure a
        | .error e => error s!"invalid executable path; {e}:\n{out}"
      let pyconfig ← match Json.parse pyconfig >>= fromJson? with
        | .ok a => pure a
        | .error e => error s!"invalid python configuration; {e}:\n{out}"
      let out ← captureProc {
        cmd := lpl,
        cwd := testModuleDir
        env := ← getPyEnv pyconfig
      }
      validateOutput "Hello!" out
  return 0
where
  @[inline] validateOutput (expected actual : String) := do
    unless actual == expected do
      error s!"incorrect output: expected\
        \n  {expected}\
        \ngot\
        \n  {actual}"
  getPyEnv py := do
    -- ensures the executable can find Python's shared libraries
    let libPath ← getAugmentedSharedLibPath
    let libPath : SearchPath := py.libDir :: libPath
    return #[
      (sharedLibPathEnvVar, some libPath.toString),
      -- activate the venv for embedded Python if necessary
      ("__PYVENV_LAUNCHER__", some py.exe.toString),
    ]
