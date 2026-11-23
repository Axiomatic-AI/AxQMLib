/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Matrix.Mul
import AxQM.Concrete.Pauli

/-!
# Concrete: the Pauli matrices in the outer-product notation (Nielsen & Chuang, Exercise 2.9)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.9
("Pauli operators and the outer product", p. 68) asks to express each of the Pauli
operators — considered as operators with respect to the orthonormal computational
basis `|0⟩, |1⟩` of a two-dimensional Hilbert space — in the outer-product notation.

This is pure linear algebra over `ℂ²`. The Pauli matrices
themselves are the `Matrix (Fin 2) (Fin 2) ℂ` objects `pauliX`, `pauliY`, `pauliZ`
from `AxQM.Concrete.Pauli`; here we add the fourth, `pauliI` (`σ₀ = I`, per
Figure 2.2), and the outer-product vocabulary needed to state the exercise.

## Contents

* `ket i` — the computational-basis column vector `|i⟩` of `ℂ²`, i.e. `Pi.single i 1`
  (`|0⟩ = (1, 0)`, `|1⟩ = (0, 1)`).
* `ketBra i j` — the outer product `|i⟩⟨j|` as a `2 × 2` matrix. Following N&C
  eq. (2.20) the bra `⟨j|` is the conjugate transpose of `|j⟩`, so `ketBra i j` is
  `vecMulVec |i⟩ (star |j⟩)`; its `(a, b)` entry is `⟨a|i⟩ · conj⟨b|j⟩ = δ_{ai} δ_{jb}`.
* `ketBra_apply` / `ketBra_eq_single` — the entrywise value and the identification
  `|i⟩⟨j| = single i j 1` with the matrix unit (this is the completeness-relation
  fact that outer products of an orthonormal basis are the standard basis matrices).
* `pauliI_eq_ketBra`, `pauliX_eq_ketBra`, `pauliY_eq_ketBra`, `pauliZ_eq_ketBra` —
  the four decompositions the exercise asks for:
  `I = |0⟩⟨0| + |1⟩⟨1|`, `X = |0⟩⟨1| + |1⟩⟨0|`,
  `Y = -i|0⟩⟨1| + i|1⟩⟨0|`, `Z = |0⟩⟨0| - |1⟩⟨1|`.

## Design notes

* The Pauli matrices are already modelled as raw `2 × 2` matrices in
  `Concrete.Pauli`, and Mathlib's outer product `Matrix.vecMulVec` takes plain
  `Fin 2 → ℂ` column vectors, so the whole exercise stays at the matrix level: no
  `EuclideanSpace`/`LinearMap` machinery is needed to say "express the matrix as a
  sum of outer products". The `star` in `ketBra` makes the bra a genuine conjugate
  dual (faithful to N&C's `|i⟩⟨j|`); on the real basis vectors it is inert, which is
  why the decompositions reduce to entrywise `2 × 2` computations.
* Each decomposition is its own named theorem (not one monolithic conjunction), and
  the coefficients are read directly off the matrix: the coefficient of `|a⟩⟨b|` is
  the `(a, b)` entry of the Pauli matrix.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The Pauli `I` matrix (`σ₀` in Nielsen & Chuang's Figure 2.2): the `2 × 2` identity
`!![1, 0; 0, 1]`. -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- The computational-basis ket `|i⟩` of `ℂ²`, as a column vector `Fin 2 → ℂ`:
`|0⟩ = (1, 0)` and `|1⟩ = (0, 1)`. Concretely the standard basis vector `Pi.single i 1`. -/
def ket (i : Fin 2) : Fin 2 → ℂ := Pi.single i 1

/-- The outer product `|i⟩⟨j|` of two computational-basis vectors, as a `2 × 2` matrix.
Following Nielsen & Chuang eq. (2.20) the bra `⟨j|` is the conjugate transpose of `|j⟩`,
so `ketBra i j = vecMulVec |i⟩ (star |j⟩)` has `(a, b)` entry `|i⟩ₐ · conj(|j⟩_b)`. -/
def ketBra (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := vecMulVec (ket i) (star (ket j))

/-- The `(a, b)` entry of `|i⟩⟨j|` is `1` when `a = i` and `b = j`, and `0` otherwise. -/
theorem ketBra_apply (i j a b : Fin 2) :
    ketBra i j a b = if a = i ∧ b = j then 1 else 0 := by
  simp only [ketBra, ket, vecMulVec_apply, Pi.single_apply]
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb]

/-- The outer product `|i⟩⟨j|` of two computational-basis vectors is the matrix unit
`single i j 1` (a single `1` in row `i`, column `j`): outer products of an orthonormal
basis are the standard basis matrices. -/
theorem ketBra_eq_single (i j : Fin 2) : ketBra i j = Matrix.single i j 1 := by
  ext a b
  rw [ketBra_apply, Matrix.single_apply]
  simp [eq_comm]

/-- **Nielsen & Chuang, Exercise 2.9** for `σ₀`: `I = |0⟩⟨0| + |1⟩⟨1|` (the
completeness relation for the computational basis). -/
theorem pauliI_eq_ketBra : pauliI = ketBra 0 0 + ketBra 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pauliI, ketBra_apply]

/-- **Nielsen & Chuang, Exercise 2.9** for `σ₁ = X`: `X = |0⟩⟨1| + |1⟩⟨0|`. -/
theorem pauliX_eq_ketBra : pauliX = ketBra 0 1 + ketBra 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pauliX, ketBra_apply]

/-- **Nielsen & Chuang, Exercise 2.9** for `σ₂ = Y`: `Y = -i|0⟩⟨1| + i|1⟩⟨0|`. -/
theorem pauliY_eq_ketBra : pauliY = (-I) • ketBra 0 1 + I • ketBra 1 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pauliY, ketBra_apply]

/-- **Nielsen & Chuang, Exercise 2.9** for `σ₃ = Z`: `Z = |0⟩⟨0| - |1⟩⟨1|`. -/
theorem pauliZ_eq_ketBra : pauliZ = ketBra 0 0 - ketBra 1 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pauliZ, ketBra_apply]

end AxQM.Concrete
