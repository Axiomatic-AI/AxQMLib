/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliKronecker

/-!
# Nielsen & Chuang, Exercise 2.27

Matrix reps of tensor products X⊗Z, I⊗X, X⊗I; is tensor product commutative?

These are explicit computations of `4 × 4` complex matrices — the Kronecker products of the
`2 × 2` Pauli matrices — together with the observation that two of them differ.

The formalisation is in `AxQM/Concrete/PauliKronecker.lean`:

* `AxQM.Concrete.flattenFin4` — the re-indexing of a two-factor tensor product
  `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` to its flat `4 × 4` matrix, ordering the
  product index by `finProdFinEquiv` (`(i, j) ↦ 2 * i + j`), i.e. the computational-basis
  order `|00⟩, |01⟩, |10⟩, |11⟩` used throughout Chapter 2.
* `AxQM.Concrete.flattenFin4_pauliX_kronecker_pauliZ` — part (a): the matrix of
  `X ⊗ Z`.
* `AxQM.Concrete.flattenFin4_pauliI_kronecker_pauliX` — part (b): the matrix of
  `I ⊗ X`.
* `AxQM.Concrete.flattenFin4_pauliX_kronecker_pauliI` — part (c): the matrix of
  `X ⊗ I`.
* `AxQM.Concrete.pauliI_kronecker_pauliX_ne_pauliX_kronecker_pauliI` — the answer to
  the final question: the tensor product is **not** commutative, witnessed by
  `I ⊗ X ≠ X ⊗ I` (parts (b) and (c) are different matrices).
-/
