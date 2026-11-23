/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MatrixRepresentationExample

/-!
# Nielsen & Chuang, Exercise 2.2 (Matrix representations: example)

Give a matrix representation for a swap-like operator A; find bases giving a different
representation.

The formalisation is in
`AxQM/Concrete/MatrixRepresentationExample.lean`, with `V` modelled by
`EuclideanSpace ℂ (Fin 2)` and `|0⟩, |1⟩` its standard basis:

* `AxQM.Concrete.swapOperator` — the operator `A` (`A|0⟩ = |1⟩`,
  `A|1⟩ = |0⟩`), defined by its action on the standard basis via
  `Module.Basis.constr`; `swapOperator_apply_zero` / `swapOperator_apply_one`
  record that action.
* `AxQM.Concrete.toMatrix_swapOperator_std` — **Part 1**: with respect
  to the standard basis `|0⟩, |1⟩` for both input and output, `A` has the matrix
  representation `!![0, 1; 1, 0]`.
* `AxQM.Concrete.hadamardBasis` — a *different* basis
  `{|0⟩ + |1⟩, |0⟩ - |1⟩}` (the unnormalised `|±⟩` basis; the vectors are the
  eigenvectors of `A`).
* `AxQM.Concrete.toMatrix_swapOperator_hadamard` — **Part 2**: with
  respect to `hadamardBasis` for both input and output, the *same* `A` has the
  diagonal matrix representation `!![1, 0; 0, -1]`.
* `AxQM.Concrete.toMatrix_swapOperator_std_ne_hadamard` — the two matrix
  representations differ, so these bases genuinely give a different matrix
  representation of `A`, as the exercise asks.
-/
