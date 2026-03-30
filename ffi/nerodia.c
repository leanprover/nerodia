/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
*/
#include <Python.h>
#include <lean/lean.h>

static void nop_foreach(void* p, b_lean_obj_arg f) {
  return;
}

static void py_finalize(void* p) {
  Py_Finalize();
}

static lean_object * g_py_context = NULL;
static lean_external_class * g_py_context_external_class = NULL;

LEAN_EXPORT lean_obj_res nerodia_py_context_get() {
  if (g_py_context) {
    lean_inc_ref(g_py_context);
  } else {
    if (!g_py_context_external_class) {
      g_py_context_external_class = lean_register_external_class(py_finalize, nop_foreach);
    }
    // TODO: Determine what to do if Python is already initialized.
    Py_Initialize();
    g_py_context = lean_alloc_external(g_py_context_external_class, NULL);
  }
  return g_py_context;
}

static void py_object_finalize(void* p) {
  Py_DECREF(p);
  lean_dec_ref(g_py_context);
}

static lean_external_class * g_py_object_external_class = NULL;

lean_obj_res nerodia_mk_object(PyObject* o, lean_obj_arg ctx) {
  if (g_py_object_external_class == NULL) {
    g_py_object_external_class = lean_register_external_class(py_object_finalize, nop_foreach);
  }
  return lean_alloc_external(g_py_object_external_class, o);
}

PyObject* nerodia_get_object(b_lean_obj_arg o) {
  assert(lean_get_external_class(o) == g_py_object_external_class);
  return lean_get_external_data(o);
}

LEAN_EXPORT lean_obj_res nerodia_mk_string(b_lean_obj_arg s, lean_obj_arg ctx) {
  // Lean strings include a null-terminator.
  // `FromStringAndSize` does not expect one, so use `size-1`.
  PyObject * o = PyUnicode_FromStringAndSize(lean_string_cstr(s), lean_string_size(s)-1);
  return nerodia_mk_object(o, ctx);
}


LEAN_EXPORT lean_obj_res nerodia_repr(b_lean_obj_arg o) {
  // Lean strings include a null-terminator.
  // `FromStringAndSize` does not expect one, so use `size-1`.
  PyObject * s = PyObject_Repr(nerodia_get_object(o));
  if (s) {
    Py_ssize_t size;
    const char * bs = PyUnicode_AsUTF8AndSize(s, &size);
    if (bs) {
      return lean_mk_string_from_bytes_unchecked(bs, size);
    } else {
      // TODO: Handle errors
      return lean_mk_string("<decode error>");
    }
  } else {
    // TODO: Handle errors
    return lean_mk_string("<repr error>");
  }
}

