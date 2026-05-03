/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
*/
#include <Python.h>
#include <lean/lean.h>

// Nerodia primtiives
void nerodia_initialize_lean(void);
lean_obj_res nerodia_py_context_mk_object(b_lean_obj_arg ctx, size_t ptr);
lean_obj_res nerodia_py_context_init(void);

// Module functions
lean_object* initialize_test_Test(uint8_t builtin);
size_t test_greeting_for(size_t self, size_t arg);
int32_t test_init_module(size_t mod);

static int module_exec(PyObject *m) {
  nerodia_initialize_lean();
  lean_object* res = initialize_test_Test(true);
  if (lean_io_result_is_error(res)) {
    lean_dec_ref(res);
    // TODO: Error class for Lean errors
    PyErr_SetString(PyExc_ImportError,
      "Failed to initialize Lean module 'Test'");
    return -1;
  }
  lean_dec_ref(res);
  return test_init_module((size_t)m);
}

static PyMethodDef module_methods[] = {
  {"greeting_for", (PyCFunction)test_greeting_for, METH_O, "Return a greeting."},
  {NULL, NULL, 0, NULL}
};

static PyModuleDef_Slot module_slots[] = {
  {Py_mod_exec, module_exec},
  {0, NULL}
};

static struct PyModuleDef module = {
  .m_base = PyModuleDef_HEAD_INIT,
  .m_name = "testmodule._native",
  .m_size = 0,
  .m_methods = module_methods,
  .m_slots = module_slots,
};

PyMODINIT_FUNC PyInit__native(void) {
  return PyModuleDef_Init(&module);
}
