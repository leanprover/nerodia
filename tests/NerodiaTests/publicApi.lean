/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Claude Code
-/
module
public import Nerodia
meta import Lean

/-! # Public API

Verifies the list of {lit}`public` definitions exposed by {module}`Nerodia`
within the {lit}`Nerodia` namespace (excluding {lit}`Nerodia.Internal`).
-/

open Lean

/--
info:
# Constants (340)
Nerodia.Addr
Nerodia.Addr.not_isNull
Nerodia.Addr.ofNullableAddr
Nerodia.Addr.toNullableAddr (proj)
Nerodia.Addr.toNullableAddr_inj
Nerodia.BaseIO.toPyBaseIO
Nerodia.BaseIO.toPyIO
Nerodia.CPyBaseIO (irreducible)
Nerodia.CPyBaseIO.ofBind
Nerodia.CPyBaseIO.pure
Nerodia.CPyBaseIO.toCPyIO
Nerodia.CPyBaseIO.toM
Nerodia.CPyBaseIO.toPyBaseIO
Nerodia.CPyIO (irreducible)
Nerodia.CPyIO.ofBind
Nerodia.CPyIO.promote
Nerodia.CPyIO.pure
Nerodia.CPyIO.raise
Nerodia.CPyIO.raw
Nerodia.CPyIO.toAlternative
Nerodia.CPyIO.toEIO
Nerodia.CPyIO.toExceptT
Nerodia.CPyIO.toIO
Nerodia.CPyIO.toM
Nerodia.CPyIO.toM?
Nerodia.CPyIO.toOptionT
Nerodia.CPyIO.toPyIO
Nerodia.CPyIO.toPyResultIO
Nerodia.CPyIO.tryCatchM
Nerodia.CPyUnitIO (irreducible)
Nerodia.CPyUnitIO.ok
Nerodia.CPyUnitIO.toAlternative
Nerodia.CPyUnitIO.toEIO
Nerodia.CPyUnitIO.toExceptT
Nerodia.CPyUnitIO.toM
Nerodia.CPyUnitIO.toPyIO
Nerodia.CodecEncoding
Nerodia.CodecEncoding.ascii
Nerodia.CodecEncoding.latin1
Nerodia.CodecEncoding.ofString
Nerodia.CodecEncoding.toString (proj)
Nerodia.CodecEncoding.utf16
Nerodia.CodecEncoding.utf16BE
Nerodia.CodecEncoding.utf16LE
Nerodia.CodecEncoding.utf32
Nerodia.CodecEncoding.utf32BE
Nerodia.CodecEncoding.utf32LE
Nerodia.CodecEncoding.utf8
Nerodia.CodecErrors
Nerodia.CodecErrors.backslashReplace
Nerodia.CodecErrors.ignore
Nerodia.CodecErrors.nameReplace
Nerodia.CodecErrors.ofString
Nerodia.CodecErrors.replace
Nerodia.CodecErrors.strict
Nerodia.CodecErrors.surrogateEscape
Nerodia.CodecErrors.surrogatePass
Nerodia.CodecErrors.toString (proj)
Nerodia.CodecErrors.xmlCharRefReplace
Nerodia.DecidablePy (type abbrev)
Nerodia.IsPy
Nerodia.IsSubtypeOf
Nerodia.IsSubtypeOf.infer_subtype
Nerodia.IsSubtypeOf.mk
Nerodia.MkCPyResult
Nerodia.MkCPyResult.mk
Nerodia.MkCPyResult.mkCPyResult (proj)
Nerodia.MkPyResult
Nerodia.MkPyResult.mk
Nerodia.MkPyResult.mkPyResult (proj)
Nerodia.MonadPy
Nerodia.MonadPy.getPyThreadCtxUnsafe (proj)
Nerodia.MonadPy.mk
Nerodia.MonadPyEnv
Nerodia.MonadPyEnv.getPyEnvironment (proj)
Nerodia.MonadPyEnv.mk
Nerodia.MonadRaise
Nerodia.MonadRaise.mk
Nerodia.MonadRaise.raise (proj)
Nerodia.NonemptyPy (type abbrev)
Nerodia.NonemptyPy.intro
Nerodia.Null
Nerodia.Null.addr (proj)
Nerodia.Null.addr_eq_null
Nerodia.Null.addr_inj
Nerodia.Null.eq_null
Nerodia.Null.isNull_addr
Nerodia.Null.mk
Nerodia.Null.null
Nerodia.NullableAddr
Nerodia.NullableAddr.IsNull
Nerodia.NullableAddr.IsNull.eq_null
Nerodia.NullableAddr.isNull_null
Nerodia.NullableAddr.null
Nerodia.NullableAddr.toNat
Nerodia.NullableAddr.toUSize (proj)
Nerodia.OfPyArg
Nerodia.OfPyArg.mk
Nerodia.OfPyArg.ofPyArg (proj)
Nerodia.Py
Nerodia.Py.Raw
Nerodia.Py.Raw.addr
Nerodia.Py.Raw.cast
Nerodia.Py.Raw.cast_mem_typeHint
Nerodia.Py.Raw.decEq
Nerodia.Py.cast
Nerodia.Py.mk
Nerodia.Py.promote
Nerodia.Py.raw (proj)
Nerodia.Py.raw_mem
Nerodia.Py.raw_promote
Nerodia.PyAny (type abbrev)
Nerodia.PyAttrInit (irreducible)
Nerodia.PyAttrInit.ofCPyIO
Nerodia.PyBaseException (type abbrev)
Nerodia.PyBaseException.mk
Nerodia.PyBaseException.sprint
Nerodia.PyBaseExceptionView (type abbrev)
Nerodia.PyBaseExceptionView.sprint
Nerodia.PyBaseExceptionView.sprint_spec
Nerodia.PyBaseExceptionView.toPyBaseException
Nerodia.PyBaseExceptionView.toPyBaseException_eq_toPy
Nerodia.PyBaseIO (irreducible)
Nerodia.PyBaseIO.bindCPyBaseIO
Nerodia.PyBaseIO.bindCPyIO
Nerodia.PyBaseIO.bindPyResultIO
Nerodia.PyBaseIO.run
Nerodia.PyBaseIO.toBaseIO
Nerodia.PyBaseIO.toCPyBaseIO
Nerodia.PyBaseIO.toM
Nerodia.PyBaseIO.toPyIO
Nerodia.PyBuffer (type abbrev)
Nerodia.PyBuffer.decode
Nerodia.PyBuffer.decodeUTF8
Nerodia.PyBuffer.decodeUTF8_eq_decode
Nerodia.PyBufferView (type abbrev)
Nerodia.PyBufferView.decode
Nerodia.PyBufferView.decodeUTF8
Nerodia.PyBufferView.decodeUTF8_spec
Nerodia.PyBufferView.decode_spec
Nerodia.PyBufferView.toPyBuffer
Nerodia.PyBufferView.toPyBuffer_eq_toPy
Nerodia.PyBytes (type abbrev)
Nerodia.PyBytes.mk
Nerodia.PyBytes.size
Nerodia.PyBytes.sizeImpl
Nerodia.PyBytes.size_eq
Nerodia.PyBytes.toByteArray
Nerodia.PyBytes.usize
Nerodia.PyBytes.usize_eq
Nerodia.PyCResultIO (irreducible)
Nerodia.PyCResultIO.pure
Nerodia.PyCResultIO.raw
Nerodia.PyCResultIO.toCPyIO
Nerodia.PyEOFError (type abbrev)
Nerodia.PyEnvironment
Nerodia.PyEnvironment.getOrInit
Nerodia.PyEnvironment.none
Nerodia.PyException (type abbrev)
Nerodia.PyIO (irreducible)
Nerodia.PyIO.bindCPyIO
Nerodia.PyIO.bindPyResultIO
Nerodia.PyIO.orElseM
Nerodia.PyIO.raise
Nerodia.PyIO.toCPyIO
Nerodia.PyIO.toCPyUnitIO
Nerodia.PyIO.toEIO
Nerodia.PyIO.toIO
Nerodia.PyIO.tryCatchM
Nerodia.PyIO.tryFinallyM'
Nerodia.PyInt (type abbrev)
Nerodia.PyInt.mk
Nerodia.PyInt.size_toByteArrayBE_pos
Nerodia.PyInt.size_toByteArrayLE_pos
Nerodia.PyInt.toByteArrayBE
Nerodia.PyInt.toByteArrayLE
Nerodia.PyInt.toInt
Nerodia.PyInt.toString
Nerodia.PyMethFastCall (irreducible)
Nerodia.PyMethFastCall.ofPyIO
Nerodia.PyMethNoArgs (irreducible)
Nerodia.PyMethNoArgs.ofPyIO
Nerodia.PyMethO (irreducible)
Nerodia.PyMethO.ofPyIO
Nerodia.PyModule (type abbrev)
Nerodia.PyModule.addByString
Nerodia.PyModule.mk
Nerodia.PyModuleInit (irreducible)
Nerodia.PyModuleInit.ofPyIO
Nerodia.PyNone (type abbrev)
Nerodia.PyNone.isNone_eq_true
Nerodia.PyObject (type abbrev)
Nerodia.PyObject.getAttrByString
Nerodia.PyObject.getType
Nerodia.PyObject.isBaseExceptionInstance
Nerodia.PyObject.isBaseExceptionInstance_iff_mem
Nerodia.PyObject.isBytesInstance
Nerodia.PyObject.isBytesInstance_iff_mem
Nerodia.PyObject.isIntInstance
Nerodia.PyObject.isIntInstance_iff_mem
Nerodia.PyObject.isModuleInstance
Nerodia.PyObject.isModuleInstance_iff_mem
Nerodia.PyObject.isNone
Nerodia.PyObject.isNone_iff_mem
Nerodia.PyObject.isStrInstance
Nerodia.PyObject.isStrInstance_iff_mem
Nerodia.PyObject.isTypeInstance
Nerodia.PyObject.mk
Nerodia.PyObject.raw_mk
Nerodia.PyObject.repr
Nerodia.PyObject.str
Nerodia.PyObjectView (type abbrev)
Nerodia.PyObjectView.getAttrByString
Nerodia.PyObjectView.getAttrByString_spec
Nerodia.PyObjectView.getType
Nerodia.PyObjectView.getType_spec
Nerodia.PyObjectView.isBaseExceptionInstance
Nerodia.PyObjectView.isBaseExceptionInstance_spec
Nerodia.PyObjectView.isBytesInstance
Nerodia.PyObjectView.isBytesInstance_spec
Nerodia.PyObjectView.isIntInstance
Nerodia.PyObjectView.isIntInstance_spec
Nerodia.PyObjectView.isModuleInstance
Nerodia.PyObjectView.isModuleInstance_spec
Nerodia.PyObjectView.isNone
Nerodia.PyObjectView.isNone_spec
Nerodia.PyObjectView.isStrInstance
Nerodia.PyObjectView.isStrInstance_spec
Nerodia.PyObjectView.isTypeInstance
Nerodia.PyObjectView.isTypeInstance_spec
Nerodia.PyObjectView.repr
Nerodia.PyObjectView.repr_spec
Nerodia.PyObjectView.str
Nerodia.PyObjectView.str_spec
Nerodia.PyObjectView.toPyObject
Nerodia.PyObjectView.toPyObject_eq_toPy
Nerodia.PyStr (type abbrev)
Nerodia.PyStr.encode
Nerodia.PyStr.encodeUTF8
Nerodia.PyStr.mk
Nerodia.PyStr.toString
Nerodia.PySystemError (type abbrev)
Nerodia.PyThreadCtxT (irreducible)
Nerodia.PyThreadCtxT.run
Nerodia.PyThreadCtxT.run'
Nerodia.PyThreadCtxT.toM
Nerodia.PyType (type abbrev)
Nerodia.PyType.getQualName
Nerodia.PyType.mk
Nerodia.PyTypeError (type abbrev)
Nerodia.ToPy
Nerodia.ToPy.mk
Nerodia.ToPy.toPy (proj)
Nerodia.ToPyBaseException (type abbrev)
Nerodia.ToPyBuffer (type abbrev)
Nerodia.ToPyObject (type abbrev)
Nerodia.ToPyObject.toPy_eq_mk
Nerodia.ToTypeExpr
Nerodia.ToTypeExpr.mk
Nerodia.ToTypeExpr.toTypeExpr (proj)
Nerodia.TypeConst
Nerodia.TypeConst.ofString
Nerodia.TypeConst.toString (proj)
Nerodia.TypeExpr
Nerodia.TypeExpr.none (irreducible)
Nerodia.TypeExpr.ofString
Nerodia.TypeExpr.ofTypeConst (irreducible)
Nerodia.TypeExpr.toString (proj)
Nerodia.TypePred (irreducible)
Nerodia.TypePred.Mem
Nerodia.TypePred.Mem.left
Nerodia.TypePred.Mem.object
Nerodia.TypePred.Mem.right
Nerodia.TypePred.Mem.union_left
Nerodia.TypePred.Mem.union_right
Nerodia.TypePred.Subset
Nerodia.TypePred.Subset.inter_left
Nerodia.TypePred.Subset.inter_right
Nerodia.TypePred.Subset.mem_of_mem
Nerodia.TypePred.Subset.object
Nerodia.TypePred.Subset.refl
Nerodia.TypePred.Subset.rfl
Nerodia.TypePred.any
Nerodia.TypePred.any_eq_object
Nerodia.TypePred.baseException
Nerodia.TypePred.bytes
Nerodia.TypePred.ext
Nerodia.TypePred.ext_iff
Nerodia.TypePred.int
Nerodia.TypePred.inter
Nerodia.TypePred.inter_never
Nerodia.TypePred.inter_object
Nerodia.TypePred.mem_inter_iff_and
Nerodia.TypePred.mem_ofFn_iff
Nerodia.TypePred.mem_union_iff_or
Nerodia.TypePred.moduleType
Nerodia.TypePred.never
Nerodia.TypePred.never_inter
Nerodia.TypePred.never_subset
Nerodia.TypePred.never_union
Nerodia.TypePred.none
Nerodia.TypePred.not_mem_never
Nerodia.TypePred.object
Nerodia.TypePred.object_inter
Nerodia.TypePred.object_union
Nerodia.TypePred.ofFn
Nerodia.TypePred.str
Nerodia.TypePred.subset_iff_forall
Nerodia.TypePred.type
Nerodia.TypePred.union
Nerodia.TypePred.union_never
Nerodia.TypePred.union_object
Nerodia.baseException (irreducible)
Nerodia.buffer (irreducible)
Nerodia.bytes (irreducible)
Nerodia.decode
Nerodia.eofError (irreducible)
Nerodia.exceptHint
Nerodia.exception (irreducible)
Nerodia.getPyNone
Nerodia.import
Nerodia.int (irreducible)
Nerodia.mkPyBytes
Nerodia.mkPyEOFError
Nerodia.mkPyInt
Nerodia.mkPyStr
Nerodia.moduleType (irreducible)
Nerodia.noneType (irreducible)
Nerodia.object (irreducible)
Nerodia.raise
Nerodia.raisePyEOFError
Nerodia.raisePyTypeError
Nerodia.str (irreducible)
Nerodia.systemError (irreducible)
Nerodia.toPy_eq_promote
Nerodia.toPy_eq_self
Nerodia.toPy_eq_toPy_raw
Nerodia.type (irreducible)
Nerodia.typeError (irreducible)
Nerodia.typeHint

# Instances (150)
Nerodia.Addr.instCoeNullableAddr
Nerodia.Addr.instNonempty
Nerodia.CPyBaseIO.instMonadLiftCPyIO
Nerodia.CPyBaseIO.instMonadLiftPyBaseIO
Nerodia.CPyBaseIO.instNonemptyOfIsPy
Nerodia.CPyIO.instMonadEvalIO
Nerodia.CPyIO.instMonadLiftPyIO
Nerodia.CPyIO.instMonadRaise
Nerodia.CPyIO.instNonempty
Nerodia.CPyUnitIO.instCoePyIOUnit
Nerodia.CPyUnitIO.instNonempty
Nerodia.CodecEncoding.instToString
Nerodia.CodecErrors.instToString
Nerodia.Null.instCoeNullableAddr
Nerodia.Null.instInhabited
Nerodia.Null.instSubsingleton
Nerodia.NullableAddr.instDecidablePredIsNull
Nerodia.NullableAddr.instInhabited
Nerodia.Py.Raw.instDecidableEq
Nerodia.Py.instNonemptyRaw
Nerodia.PyBaseExceptionView.instCoeOutPyBaseExceptionOfToPyBaseException
Nerodia.PyBaseIO.instMonadEvalBaseIO
Nerodia.PyBufferView.instCoeOutPyBufferOfToPyBuffer
Nerodia.PyIO.instMonadEvalIO
Nerodia.PyIO.instMonadExceptOfPyBaseException
Nerodia.PyIO.instMonadFinally
Nerodia.PyIO.instMonadRaise
Nerodia.PyIO.instOrElse
Nerodia.PyInt.instToString
Nerodia.PyObjectView.instCoeOutPyObjectOfToPyObject
Nerodia.PyStr.instToString
Nerodia.PyThreadCtxT.instLawfulMonad
Nerodia.PyThreadCtxT.instLawfulMonadAttachOfLawfulMonad
Nerodia.PyThreadCtxT.instMonad
Nerodia.PyThreadCtxT.instMonadAttachOfMonad
Nerodia.PyThreadCtxT.instMonadControl
Nerodia.PyThreadCtxT.instMonadExceptOf
Nerodia.PyThreadCtxT.instMonadFunctor
Nerodia.PyThreadCtxT.instMonadLift
Nerodia.PyThreadCtxT.instMonadPyOfMonad
Nerodia.ToPyObject.instRaw
Nerodia.TypeExpr.instCoeTypeConst
Nerodia.TypeExpr.instToString
Nerodia.TypePred.instHasSubset
Nerodia.TypePred.instInter
Nerodia.TypePred.instMembershipRaw
Nerodia.TypePred.instUnion
Nerodia.instCoeDepOptionNoneTypeExpr
Nerodia.instCoeDepOptionNoneTypePred
Nerodia.instCoeDepTypeConstBaseExceptionTypePred
Nerodia.instCoeDepTypeConstBufferTypePred
Nerodia.instCoeDepTypeConstBytesTypePred
Nerodia.instCoeDepTypeConstEofErrorTypePred
Nerodia.instCoeDepTypeConstExceptionTypePred
Nerodia.instCoeDepTypeConstIntTypePred
Nerodia.instCoeDepTypeConstModuleTypeTypePred
Nerodia.instCoeDepTypeConstObjectTypePred
Nerodia.instCoeDepTypeConstStrTypePred
Nerodia.instCoeDepTypeConstSystemErrorTypePred
Nerodia.instCoeDepTypeConstTypeErrorTypePred
Nerodia.instCoeDepTypeConstTypeTypePred
Nerodia.instDecidableEqAddr
Nerodia.instDecidableEqAddr.decEq
Nerodia.instDecidableEqNullableAddr
Nerodia.instDecidableEqNullableAddr.decEq
Nerodia.instDecidableEqTypeConst
Nerodia.instDecidableEqTypeConst.decEq
Nerodia.instDecidableEqTypeExpr
Nerodia.instDecidableEqTypeExpr.decEq
Nerodia.instDecidablePyAny
Nerodia.instDecidablePyBaseException
Nerodia.instDecidablePyBytes
Nerodia.instDecidablePyInt
Nerodia.instDecidablePyModuleType
Nerodia.instDecidablePyNone
Nerodia.instDecidablePyObject
Nerodia.instDecidablePyStr
Nerodia.instInhabitedPyModuleInit
Nerodia.instIsPyPy
Nerodia.instIsPyRaw
Nerodia.instIsSubtypeOf
Nerodia.instIsSubtypeOfBaseExceptionExceptHint
Nerodia.instIsSubtypeOfInterTypePred
Nerodia.instIsSubtypeOfInterTypePred_1
Nerodia.instIsSubtypeOfTypeHintOfTypeConstExceptHint
Nerodia.instMkCPyResultBaseIO
Nerodia.instMkCPyResultIntInt
Nerodia.instMkCPyResultOfMkPyResult
Nerodia.instMkCPyResultPUnitNone
Nerodia.instMkCPyResultPy
Nerodia.instMkCPyResultPyBaseIO
Nerodia.instMkCPyResultPyIO
Nerodia.instMkCPyResultStringStr
Nerodia.instMkPyResultBaseIO
Nerodia.instMkPyResultOfMkCPyResult
Nerodia.instMkPyResultPy
Nerodia.instMkPyResultPyBaseIO
Nerodia.instMkPyResultPyIO
Nerodia.instMonadLiftBaseIOPyBaseIO
Nerodia.instMonadLiftBaseIOPyIO
Nerodia.instMonadLiftPyBaseIOPyIO
Nerodia.instMonadPyBaseIO
Nerodia.instMonadPyEnvOfFunctorOfMonadPy
Nerodia.instMonadPyEnvOfMonadLift
Nerodia.instMonadPyIO
Nerodia.instMonadPyOfMonadLift
Nerodia.instMonadPyPyBaseIO
Nerodia.instMonadPyPyIO
Nerodia.instNonemptyPyAttrInit
Nerodia.instNonemptyPyBaseException
Nerodia.instNonemptyPyBytes
Nerodia.instNonemptyPyEnvironment
Nerodia.instNonemptyPyExceptHint
Nerodia.instNonemptyPyInt
Nerodia.instNonemptyPyInterTypePredBaseExceptionTypeHint
Nerodia.instNonemptyPyModuleType
Nerodia.instNonemptyPyNone
Nerodia.instNonemptyPyObject
Nerodia.instNonemptyPyStr
Nerodia.instNonemptyPyType
Nerodia.instNonemptyPyTypeHint
Nerodia.instNonemptyPyUnionTypePred
Nerodia.instNonemptyPyUnionTypePred_1
Nerodia.instNonemptyTypeConst
Nerodia.instNonemptyTypeExpr
Nerodia.instOfPyArgIntInt
Nerodia.instOfPyArgPyAnyAny
Nerodia.instOfPyArgPyObjectObject
Nerodia.instOfPyArgPyOfDecidablePyOfToTypeExpr
Nerodia.instOfPyArgStringStr
Nerodia.instToPyPy
Nerodia.instToPyPyOfIsSubtypeOf
Nerodia.instToPyPyOfRaw
Nerodia.instToPyTypeHintPy
Nerodia.instToStringTypeConst
Nerodia.instToTypeExprBaseException
Nerodia.instToTypeExprBytes
Nerodia.instToTypeExprExceptHintEofError
Nerodia.instToTypeExprExceptHintException
Nerodia.instToTypeExprExceptHintSystemError
Nerodia.instToTypeExprExceptHintTypeError
Nerodia.instToTypeExprInt
Nerodia.instToTypeExprInterTypePredBaseExceptionTypeHint
Nerodia.instToTypeExprModuleType
Nerodia.instToTypeExprNone
Nerodia.instToTypeExprObject
Nerodia.instToTypeExprStr
Nerodia.instToTypeExprType
Nerodia.instToTypeExprTypeHint
Nerodia.instToTypeExprTypeHintOfTypeConstBuffer
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  -- Since this module publicly imports `Nerodia`, its exporting environment
  -- sees exactly the `public` definitions importers of `Nerodia` would.
  let expEnv := env.setExporting true
  -- Instances and their generated definitions (e.g., `decEq`) are grouped
  -- separately from other definitions
  let isInstRelated (n : Name) : Bool := Id.run do
    let mut n := n
    while n != .anonymous do
      if Meta.isInstanceCore env n then return true
      n := n.getPrefix
    return false
  let mut defs := #[]
  let mut insts := #[]
  for (name, info) in env.constants.toList do
    unless (`Nerodia).isPrefixOf name do continue
    if (`Nerodia.Internal).isPrefixOf name then continue
    if (`Nerodia.Compiler).isPrefixOf name then continue
    -- Skip auto-generated auxiliaries (e.g., `casesOn`, `noConfusion`)
    if info matches .recInfo _ then continue
    if name.isInternalDetail || isAuxRecursor env name || isNoConfusion env name then
      continue
    if let .str _ s := name then
      if #["noConfusionType", "ctorIdx", "inj", "injEq",
          "sizeOf_spec", "congr_simp"].contains s then
        continue
    unless expEnv.contains name do continue
    if isInstRelated name then
      insts := insts.push name
    else
      defs := defs.push name
  IO.print s!"\n# Constants ({defs.size})\n"
  let rec isType
    | .sort _ => true
    | .forallE (body := b) .. => isType b
    | _ => false
  for name in defs.qsort (·.toString < ·.toString) do
    if env.hasExposedBody name then
      if getReducibilityStatusCore env name matches .irreducible then
        IO.println s!"{name} (irreducible)"
      else if env.isProjectionFn name then
        IO.println s!"{name} (proj)"
      else if env.find? name |>.any fun | .defnInfo v => isType v.type | _ => false then
        IO.println s!"{name} (type abbrev)"
      else
        IO.println s!"{name} (exposed)"
    else
      IO.println name
  IO.print s!"\n# Instances ({insts.size})\n"
  for name in insts.qsort (·.toString < ·.toString) do
    IO.println name
