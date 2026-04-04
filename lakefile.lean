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
  libName : String
  libPath : FilePath
  includeDir : FilePath
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
        (pureHash py.libName) s!"pyconfig: {py.libName}"
      return py
    | .error e =>
      error s!"configuration script produced unexpect output; {e}:\n{out}"

target libpython3 : Dynlib := do
  return (← pyconfig.fetch).map (sync := true) fun py =>
    {name := py.libName, path := py.libPath}

/-! ## Nerodia FFI -/

input_file nerodia.c where
  text := true
  path := "ffi" / "nerodia.c"

target nerodia.o pkg : FilePath := do
  let cJob ← nerodia.c.fetch
  (← pyconfig.fetch).bindM fun py => do
    newTrace
    let oFile := pkg.irDir / "c" / "nerodia.o"
    let weakArgs := #[
      s!"-I{py.includeDir}",
      s!"-I{← getLeanIncludeDir}"
    ]
    let traceArgs := pkg.buildType.leancArgs ++ #[
      s!"-DPy_LIMITED_API={minHexVersion}",
      "-fPIC", "-std=c17", "-Wall"
    ]
    let cc := (← IO.getEnv "CC").getD "cc"
    buildO oFile cJob weakArgs traceArgs cc getLeanTrace

target libnerodiaffi pkg : FilePath := do
  let libName := pkg.staticLibDir / nameToStaticLib "nerodiaffi"
  let oJob ← nerodia.o.fetch
  buildStaticLib libName #[oJob]

/-! ## Nerodia Lean -/

@[default_target]
lean_lib Nerodia where
  defaultFacets := #[LeanLib.sharedFacet]
  moreLinkObjs := #[libnerodiaffi]
  moreLinkLibs := #[libpython3]

lean_lib NerodiaTests where
  srcDir := "tests"
  globs := #[`NerodiaTests.+]
  precompileModules := true

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
    let libJob ← NerodiaTests.fetch
    let exeJob ← testExe.fetch
    withRegisterJob "testExe test" do
      libJob.bindM fun _ =>
      pyJob.bindM fun py =>
      exeJob.mapM fun exeFile => do
        let out ← captureProc {cmd := exeFile.toString}
        unless out == py.version do
          error s!"incorrect output: expected\
            \n  {py.version}\
            \ngot\
            \n  {out}"
  return 0
