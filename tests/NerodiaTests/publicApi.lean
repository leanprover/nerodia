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
# Constants (361)
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
Nerodia.Constant
Nerodia.DecidablePy (type abbrev)
Nerodia.IO.toPyIO
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
Nerodia.Py.Raw.raw_toPyObject
Nerodia.Py.Raw.toPyObject
Nerodia.Py.Raw.toPy_eq_toPyObject
Nerodia.Py.attachType
Nerodia.Py.mk
Nerodia.Py.promote
Nerodia.Py.raw (proj)
Nerodia.Py.raw_attachType
Nerodia.Py.raw_hasType
Nerodia.Py.raw_promote
Nerodia.PyAny (type abbrev)
Nerodia.PyAttrInit (irreducible)
Nerodia.PyAttrInit.ofCPyIO
Nerodia.PyBaseException (type abbrev)
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
Nerodia.PyBuffer.getByteArray
Nerodia.PyBufferView (type abbrev)
Nerodia.PyBufferView.decode
Nerodia.PyBufferView.decodeUTF8
Nerodia.PyBufferView.decodeUTF8_spec
Nerodia.PyBufferView.decode_spec
Nerodia.PyBufferView.getByteArray
Nerodia.PyBufferView.getByteArray_spec
Nerodia.PyBufferView.toPyBuffer
Nerodia.PyBufferView.toPyBuffer_eq_toPy
Nerodia.PyBytes (type abbrev)
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
Nerodia.PyModuleInit (irreducible)
Nerodia.PyModuleInit.ofPyIO
Nerodia.PyNever (type abbrev)
Nerodia.PyNever.elim
Nerodia.PyNone (type abbrev)
Nerodia.PyNone.isNone_eq_true
Nerodia.PyOSError (type abbrev)
Nerodia.PyObject (type abbrev)
Nerodia.PyObject.bytes
Nerodia.PyObject.getAttrByString
Nerodia.PyObject.getPyBuffer?
Nerodia.PyObject.getType
Nerodia.PyObject.index
Nerodia.PyObject.int
Nerodia.PyObject.isNone
Nerodia.PyObject.isNone_iff_hasType
Nerodia.PyObject.repr
Nerodia.PyObject.str
Nerodia.PyObjectView (type abbrev)
Nerodia.PyObjectView.bytes
Nerodia.PyObjectView.bytes_spec
Nerodia.PyObjectView.getAttrByString
Nerodia.PyObjectView.getAttrByString_spec
Nerodia.PyObjectView.getPyBuffer?
Nerodia.PyObjectView.getPyBuffer?_spec
Nerodia.PyObjectView.getType
Nerodia.PyObjectView.getType_spec
Nerodia.PyObjectView.index
Nerodia.PyObjectView.index_spec
Nerodia.PyObjectView.int
Nerodia.PyObjectView.int_spec
Nerodia.PyObjectView.isNone
Nerodia.PyObjectView.isNone_spec
Nerodia.PyObjectView.repr
Nerodia.PyObjectView.repr_spec
Nerodia.PyObjectView.str
Nerodia.PyObjectView.str_spec
Nerodia.PyObjectView.toPyObject
Nerodia.PyObjectView.toPyObject_eq_toPy
Nerodia.PyRuntimeError (type abbrev)
Nerodia.PyStr (type abbrev)
Nerodia.PyStr.encode
Nerodia.PyStr.encodeUTF8
Nerodia.PyStr.toString
Nerodia.PySystemError (type abbrev)
Nerodia.PyThreadCtxT (irreducible)
Nerodia.PyThreadCtxT.run
Nerodia.PyThreadCtxT.run'
Nerodia.PyThreadCtxT.toM
Nerodia.PyType (type abbrev)
Nerodia.PyType.getQualName
Nerodia.PyTypeError (type abbrev)
Nerodia.PyValueError (type abbrev)
Nerodia.ToPy
Nerodia.ToPy.mk
Nerodia.ToPy.toPy (proj)
Nerodia.ToPyBaseException (type abbrev)
Nerodia.ToPyBuffer (type abbrev)
Nerodia.ToPyObject (type abbrev)
Nerodia.ToTypeExpr
Nerodia.ToTypeExpr.mk
Nerodia.ToTypeExpr.toTypeExpr (proj)
Nerodia.TypeExpr
Nerodia.TypeExpr.baseException (irreducible)
Nerodia.TypeExpr.buffer (irreducible)
Nerodia.TypeExpr.bytes (irreducible)
Nerodia.TypeExpr.eofError (irreducible)
Nerodia.TypeExpr.exception (irreducible)
Nerodia.TypeExpr.int (irreducible)
Nerodia.TypeExpr.moduleType (irreducible)
Nerodia.TypeExpr.never (irreducible)
Nerodia.TypeExpr.none (irreducible)
Nerodia.TypeExpr.object (irreducible)
Nerodia.TypeExpr.ofString
Nerodia.TypeExpr.osError (irreducible)
Nerodia.TypeExpr.runtimeError (irreducible)
Nerodia.TypeExpr.str (irreducible)
Nerodia.TypeExpr.systemError (irreducible)
Nerodia.TypeExpr.toString (proj)
Nerodia.TypeExpr.type (irreducible)
Nerodia.TypeExpr.typeError (irreducible)
Nerodia.TypeExpr.valueError (irreducible)
Nerodia.Typing (irreducible)
Nerodia.Typing.HasType
Nerodia.Typing.HasType.left
Nerodia.Typing.HasType.object
Nerodia.Typing.HasType.right
Nerodia.Typing.HasType.union_left
Nerodia.Typing.HasType.union_right
Nerodia.Typing.Subset
Nerodia.Typing.Subset.hasType_of_hasType
Nerodia.Typing.Subset.inter_left
Nerodia.Typing.Subset.inter_right
Nerodia.Typing.Subset.object
Nerodia.Typing.Subset.refl
Nerodia.Typing.Subset.rfl
Nerodia.Typing.any
Nerodia.Typing.any_eq_object
Nerodia.Typing.baseException
Nerodia.Typing.buffer
Nerodia.Typing.bytes
Nerodia.Typing.eofError
Nerodia.Typing.exception
Nerodia.Typing.ext
Nerodia.Typing.ext_iff
Nerodia.Typing.hasType_inter_iff_and
Nerodia.Typing.hasType_ofFn_iff
Nerodia.Typing.hasType_union_iff_or
Nerodia.Typing.int
Nerodia.Typing.inter
Nerodia.Typing.inter_never
Nerodia.Typing.inter_object
Nerodia.Typing.moduleType
Nerodia.Typing.never
Nerodia.Typing.never_inter
Nerodia.Typing.never_subset
Nerodia.Typing.never_union
Nerodia.Typing.none
Nerodia.Typing.not_hasType_never
Nerodia.Typing.object
Nerodia.Typing.object_inter
Nerodia.Typing.object_union
Nerodia.Typing.ofFn
Nerodia.Typing.osError
Nerodia.Typing.runtimeError
Nerodia.Typing.str
Nerodia.Typing.subset_iff_forall
Nerodia.Typing.systemError
Nerodia.Typing.type
Nerodia.Typing.typeError
Nerodia.Typing.union
Nerodia.Typing.union_never
Nerodia.Typing.union_object
Nerodia.Typing.valueError
Nerodia.ViewPy
Nerodia.ViewPy.isPyT
Nerodia.ViewPy.mk
Nerodia.any
Nerodia.baseException
Nerodia.buffer
Nerodia.bytes
Nerodia.decode
Nerodia.eofError
Nerodia.exception
Nerodia.getPyNone
Nerodia.import
Nerodia.int
Nerodia.mkPyBytes
Nerodia.mkPyInt
Nerodia.mkPyNat
Nerodia.mkPyStr
Nerodia.moduleType
Nerodia.never
Nerodia.object
Nerodia.osError
Nerodia.raise
Nerodia.raiseIOError
Nerodia.raisePyEOFError
Nerodia.raisePyOSError
Nerodia.raisePyRuntimeError
Nerodia.raisePyTypeError
Nerodia.raisePyValueError
Nerodia.runtimeError
Nerodia.str
Nerodia.systemError
Nerodia.toPy_eq_promote
Nerodia.toPy_eq_self
Nerodia.toPy_eq_toPy_raw
Nerodia.type
Nerodia.typeError
Nerodia.valueError
Nerodia.«term_⦂_»

# Instances (214)
Nerodia.Addr.instCoeNullableAddr
Nerodia.Addr.instNonempty
Nerodia.CPyBaseIO.instMonadLiftCPyIO
Nerodia.CPyBaseIO.instMonadLiftPyBaseIO
Nerodia.CPyBaseIO.instNonemptyOfIsPy
Nerodia.CPyIO.instMonadEvalIO
Nerodia.CPyIO.instMonadLiftPyIO
Nerodia.CPyIO.instMonadRaise
Nerodia.CPyIO.instNonempty
Nerodia.CPyUnitIO.instNonempty
Nerodia.CodecEncoding.instToString
Nerodia.CodecErrors.instToString
Nerodia.Null.instCoeNullableAddr
Nerodia.Null.instInhabited
Nerodia.Null.instSubsingleton
Nerodia.NullableAddr.instDecidablePredIsNull
Nerodia.NullableAddr.instInhabited
Nerodia.Py.Raw.instToPyObject
Nerodia.Py.instCoeOutRaw
Nerodia.Py.instNonemptyRaw
Nerodia.PyBaseExceptionView.instCoeOutPyBaseExceptionOfToPyBaseException
Nerodia.PyBaseIO.instMonadEvalBaseIO
Nerodia.PyBufferView.instCoeOutPyBufferOfToPyBuffer
Nerodia.PyIO.instInhabited
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
Nerodia.Typing.instHasSubset
Nerodia.Typing.instInter
Nerodia.Typing.instIsSubtypeOfBaseExceptionEofError
Nerodia.Typing.instIsSubtypeOfBaseExceptionException
Nerodia.Typing.instIsSubtypeOfBaseExceptionOsError
Nerodia.Typing.instIsSubtypeOfBaseExceptionRuntimeError
Nerodia.Typing.instIsSubtypeOfBaseExceptionSystemError
Nerodia.Typing.instIsSubtypeOfBaseExceptionTypeError
Nerodia.Typing.instIsSubtypeOfBaseExceptionValueError
Nerodia.Typing.instNonemptyPyBaseException
Nerodia.Typing.instNonemptyPyBuffer
Nerodia.Typing.instNonemptyPyBytes
Nerodia.Typing.instNonemptyPyEofError
Nerodia.Typing.instNonemptyPyException
Nerodia.Typing.instNonemptyPyInt
Nerodia.Typing.instNonemptyPyModuleType
Nerodia.Typing.instNonemptyPyOsError
Nerodia.Typing.instNonemptyPyRuntimeError
Nerodia.Typing.instNonemptyPyStr
Nerodia.Typing.instNonemptyPySystemError
Nerodia.Typing.instNonemptyPyType
Nerodia.Typing.instNonemptyPyTypeError
Nerodia.Typing.instNonemptyPyValueError
Nerodia.Typing.instUnion
Nerodia.instCoeCPyUnitIOPyIOUnit
Nerodia.instCoeDepConstantAnyTyping
Nerodia.instCoeDepConstantBaseExceptionTyping
Nerodia.instCoeDepConstantBufferTypeExpr
Nerodia.instCoeDepConstantBufferTyping
Nerodia.instCoeDepConstantBytesTypeExpr
Nerodia.instCoeDepConstantBytesTyping
Nerodia.instCoeDepConstantEofErrorTypeExpr
Nerodia.instCoeDepConstantEofErrorTyping
Nerodia.instCoeDepConstantExceptionTypeExpr
Nerodia.instCoeDepConstantExceptionTyping
Nerodia.instCoeDepConstantIntTypeExpr
Nerodia.instCoeDepConstantIntTyping
Nerodia.instCoeDepConstantModuleTypeTypeExpr
Nerodia.instCoeDepConstantModuleTypeTyping
Nerodia.instCoeDepConstantNeverTypeExpr
Nerodia.instCoeDepConstantNeverTyping
Nerodia.instCoeDepConstantObjectTypeExpr
Nerodia.instCoeDepConstantObjectTyping
Nerodia.instCoeDepConstantOsErrorTypeExpr
Nerodia.instCoeDepConstantOsErrorTyping
Nerodia.instCoeDepConstantRuntimeErrorTypeExpr
Nerodia.instCoeDepConstantRuntimeErrorTyping
Nerodia.instCoeDepConstantStrTypeExpr
Nerodia.instCoeDepConstantStrTyping
Nerodia.instCoeDepConstantSystemErrorTypeExpr
Nerodia.instCoeDepConstantSystemErrorTyping
Nerodia.instCoeDepConstantTypeErrorTypeExpr
Nerodia.instCoeDepConstantTypeErrorTyping
Nerodia.instCoeDepConstantTypeTypeExpr
Nerodia.instCoeDepConstantTypeTyping
Nerodia.instCoeDepConstantValueErrorTypeExpr
Nerodia.instCoeDepConstantValueErrorTyping
Nerodia.instCoeDepOptionNoneTypeExpr
Nerodia.instCoeDepOptionNoneTyping
Nerodia.instDecidableEqAddr
Nerodia.instDecidableEqAddr.decEq
Nerodia.instDecidableEqNullableAddr
Nerodia.instDecidableEqNullableAddr.decEq
Nerodia.instDecidableEqTypeExpr
Nerodia.instDecidableEqTypeExpr.decEq
Nerodia.instDecidablePyAny
Nerodia.instDecidablePyBaseException
Nerodia.instDecidablePyBytes
Nerodia.instDecidablePyInt
Nerodia.instDecidablePyInterTyping
Nerodia.instDecidablePyModuleType
Nerodia.instDecidablePyNever
Nerodia.instDecidablePyNone
Nerodia.instDecidablePyObject
Nerodia.instDecidablePyStr
Nerodia.instDecidablePyType
Nerodia.instDecidablePyUnionTyping
Nerodia.instInhabitedConstant
Nerodia.instInhabitedConstant.default
Nerodia.instInhabitedPyModuleInit
Nerodia.instIsPyPy
Nerodia.instIsPyRaw
Nerodia.instIsSubtypeOf
Nerodia.instIsSubtypeOfInterTyping
Nerodia.instIsSubtypeOfInterTyping_1
Nerodia.instMkCPyResultBaseIO
Nerodia.instMkCPyResultEmptyNever
Nerodia.instMkCPyResultFinInt
Nerodia.instMkCPyResultIO
Nerodia.instMkCPyResultIntInt
Nerodia.instMkCPyResultNatInt
Nerodia.instMkCPyResultOfMkPyResult
Nerodia.instMkCPyResultPEmptyNever
Nerodia.instMkCPyResultPUnitNone
Nerodia.instMkCPyResultPy
Nerodia.instMkCPyResultPyBaseIO
Nerodia.instMkCPyResultPyIO
Nerodia.instMkCPyResultStringStr
Nerodia.instMkPyResultBaseIO
Nerodia.instMkPyResultIO
Nerodia.instMkPyResultOfMkCPyResult
Nerodia.instMkPyResultPy
Nerodia.instMkPyResultPyBaseIO
Nerodia.instMkPyResultPyIO
Nerodia.instMonadLiftBaseIOPyBaseIO
Nerodia.instMonadLiftBaseIOPyIO
Nerodia.instMonadLiftIOPyIO
Nerodia.instMonadLiftPyBaseIOPyIO
Nerodia.instMonadPyBaseIO
Nerodia.instMonadPyEnvOfFunctorOfMonadPy
Nerodia.instMonadPyEnvOfMonadLift
Nerodia.instMonadPyIO
Nerodia.instMonadPyOfMonadLift
Nerodia.instMonadPyPyBaseIO
Nerodia.instMonadPyPyIO
Nerodia.instNonemptyPyAny
Nerodia.instNonemptyPyAttrInit
Nerodia.instNonemptyPyEnvironment
Nerodia.instNonemptyPyIO
Nerodia.instNonemptyPyNone
Nerodia.instNonemptyPyObject
Nerodia.instNonemptyPyUnionTyping
Nerodia.instNonemptyPyUnionTyping_1
Nerodia.instNonemptyTypeExpr
Nerodia.instOfPyArgByteArrayBuffer
Nerodia.instOfPyArgFinInt
Nerodia.instOfPyArgIntInt
Nerodia.instOfPyArgNatInt
Nerodia.instOfPyArgPyAnyAny
Nerodia.instOfPyArgPyBufferBuffer
Nerodia.instOfPyArgPyObjectObject
Nerodia.instOfPyArgPyOfDecidablePyOfToTypeExpr
Nerodia.instOfPyArgStringStr
Nerodia.instToPyBufferPyBytes
Nerodia.instToPyPy
Nerodia.instToPyPyOfIsSubtypeOf
Nerodia.instToPyPyOfRaw
Nerodia.instToStringTypeExpr
Nerodia.instToTypeExprBaseException
Nerodia.instToTypeExprBuffer
Nerodia.instToTypeExprBytes
Nerodia.instToTypeExprEofError
Nerodia.instToTypeExprException
Nerodia.instToTypeExprInt
Nerodia.instToTypeExprModuleType
Nerodia.instToTypeExprNever
Nerodia.instToTypeExprNone
Nerodia.instToTypeExprObject
Nerodia.instToTypeExprOsError
Nerodia.instToTypeExprRuntimeError
Nerodia.instToTypeExprStr
Nerodia.instToTypeExprSystemError
Nerodia.instToTypeExprType
Nerodia.instToTypeExprTypeError
Nerodia.instToTypeExprValueError
Nerodia.instViewPyAnyPyAny
Nerodia.instViewPyBaseExceptionPyBaseException
Nerodia.instViewPyBufferPyBuffer
Nerodia.instViewPyBytesPyBytes
Nerodia.instViewPyEofErrorPyEOFError
Nerodia.instViewPyExceptionPyException
Nerodia.instViewPyIntPyInt
Nerodia.instViewPyModuleTypePyModule
Nerodia.instViewPyNeverPyNever
Nerodia.instViewPyObjectPyObject
Nerodia.instViewPyOsErrorPyOSError
Nerodia.instViewPyPy
Nerodia.instViewPyRuntimeErrorPyRuntimeError
Nerodia.instViewPyStrPyStr
Nerodia.instViewPySystemErrorPySystemError
Nerodia.instViewPyTypeErrorPyTypeError
Nerodia.instViewPyTypePyType
Nerodia.instViewPyValueErrorPyValueError
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
