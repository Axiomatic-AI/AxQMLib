/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LinearDependenceExample

/-!
# Nielsen & Chuang, Exercise 2.1 (Linear dependence: example)

Show that (1,-1),(1,2),(2,1) are linearly dependent.

The formalisation is in `AxQM/Concrete/LinearDependenceExample.lean`:

* `AxQM.Concrete.dependentTripleC2` — the three vectors of `ℂ²`
  (`EuclideanSpace ℂ (Fin 2)`), as a family indexed by `Fin 3`.
* `AxQM.Concrete.dependentTripleC2_combination_eq_zero` — the explicit
  nontrivial relation `(-1)·(1, -1) + (-1)·(1, 2) + 1·(2, 1) = 0` (N&C (2.9)).
* `AxQM.Concrete.not_linearIndependent_dependentTripleC2` — the vectors
  are linearly dependent (not linearly independent), the exercise's claim.
-/
