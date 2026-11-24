# AxQM documentation

This branch builds the API documentation of AxQM, the library on `main`, and publishes it to
GitHub Pages at <https://axiomatic-ai.github.io/AxQMLib/>. It holds no part of the library.

The documentation is of the commit of the library pinned in `lakefile.toml`, and covers `AxQM`,
`ToMathlib` and everything they import, Mathlib and Lean core included. Its home page is the
library's `README.md`, and a second page is the index of the book's numbered items,
`AxQM/NC/README.md`, with each item linked to its module; `pages.py` adds both.

## Documenting a later commit

1. Set `rev` of `axqm` in `lakefile.toml` to the commit. If that commit changes the library's
   `lean-toolchain`, copy it here and set `rev` of `doc-gen4` to the tag of the new toolchain.
2. Run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update axqm` (and `doc-gen4`, if its `rev` changed).
3. Commit and push. `.github/workflows/docs.yml` builds the documentation and publishes it.

## Building locally

```
lake exe cache get
lake build @axqm:docs
python3 pages.py .lake/build/doc https://github.com/Axiomatic-AI/AxQMLib/blob/<commit>
python3 -m http.server -d .lake/build/doc
```

The first build also documents Lean core and Mathlib, which takes a while.
