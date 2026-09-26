# Nerodia Reference Manual

A reference manual for Nerodia, written in Verso.

To build it, ensure Python's shared libraries are in the shared library path and run:

```
$ lake exe docs
```

The generated site will be in `_out/doc/latest/`. Serve it with:

```
$ lake exe verso-serve _out/doc/latest
```

or, to demo the full website:

```
$ npx netlify-cli dev
```

## Development

All modules referencing docstrings should `open Nerodia` so that types in the rendered signatures are not qualified by `Nerodia`. Modules using the module system must `import all` the module containing the signature's docstring in order for it to appear in hovers.
