/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# An orthogonal pair in `ℂ²` and its normalized forms (Nielsen & Chuang, Exercise 2.7)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 2.7
(p. 66) asks to verify that the vectors `|w⟩ ≡ (1, 1)` and `|v⟩ ≡ (1, -1)` of
`ℂ²` are *orthogonal*, and to find their *normalized forms*.

Both parts are pure linear algebra over `ℂ`. `ℂ²` is modelled by
`EuclideanSpace ℂ (Fin 2)`, the library's model of a
two-dimensional complex Hilbert space, with N&C's inner product `(2.14)`
(`(y, z) = ∑ᵢ yᵢ* zᵢ`, conjugate-linear in the first argument) supplied by its
canonical `InnerProductSpace ℂ` instance, and the norm `‖·‖` of `(2.16)`
(`‖v⟩‖ = √⟨v|v⟩`) by the induced norm.

* `vecOneOneC2`, `vecOneNegOneC2` — the two vectors `(1, 1)` and `(1, -1)`.
* `inner_vecOneOneC2_vecOneNegOneC2_eq_zero` — **part 1**: their inner product
  is `0`, i.e. they are orthogonal (N&C: orthogonal ⇔ inner product zero).
* `norm_vecOneOneC2`, `norm_vecOneNegOneC2` — each has norm `√2`, the divisor
  used to normalize.
* `unitVecOneOneC2`, `unitVecOneNegOneC2` — **part 2**: the explicit normalized
  forms `(1/√2, 1/√2)` and `(1/√2, -1/√2)`.
* `unitVecOneOneC2_eq_norm_inv_smul`, `unitVecOneNegOneC2_eq_norm_inv_smul` —
  these explicit vectors *are* the normalized forms `‖·‖⁻¹ • ·` of N&C
  (dividing each vector by its norm).
* `norm_unitVecOneOneC2`, `norm_unitVecOneNegOneC2` — and they are indeed unit
  vectors (norm `1`), confirming the normalization.
-/

namespace AxQM.Concrete

open scoped ComplexConjugate

/-- The vector `|w⟩ ≡ (1, 1)` of `ℂ²` from Nielsen & Chuang, Exercise 2.7.
`ℂ²` is modelled by `EuclideanSpace ℂ (Fin 2)`. -/
def vecOneOneC2 : EuclideanSpace ℂ (Fin 2) := !₂[1, 1]

/-- The vector `|v⟩ ≡ (1, -1)` of `ℂ²` from Nielsen & Chuang, Exercise 2.7.
`ℂ²` is modelled by `EuclideanSpace ℂ (Fin 2)`. -/
def vecOneNegOneC2 : EuclideanSpace ℂ (Fin 2) := !₂[1, -1]

/-- **Nielsen & Chuang, Exercise 2.7 (orthogonality).** The vectors `(1, 1)`
and `(1, -1)` of `ℂ²` are orthogonal: their inner product (N&C `(2.14)`,
`(y, z) = ∑ᵢ yᵢ* zᵢ`) is `0`. Concretely `1* · 1 + 1* · (-1) = 0`. -/
theorem inner_vecOneOneC2_vecOneNegOneC2_eq_zero :
    inner ℂ vecOneOneC2 vecOneNegOneC2 = 0 := by
  simp [vecOneOneC2, vecOneNegOneC2, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_two]

/-- The vector `(1, 1)` has norm `√2` (N&C `(2.16)`, `‖v⟩‖ = √⟨v|v⟩`):
`√(|1|² + |1|²) = √2`. This is the divisor used to normalize it. -/
theorem norm_vecOneOneC2 : ‖vecOneOneC2‖ = Real.sqrt 2 := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  norm_num [vecOneOneC2, Fin.sum_univ_two]

/-- The vector `(1, -1)` has norm `√2` (N&C `(2.16)`, `‖v⟩‖ = √⟨v|v⟩`):
`√(|1|² + |-1|²) = √2`. This is the divisor used to normalize it. -/
theorem norm_vecOneNegOneC2 : ‖vecOneNegOneC2‖ = Real.sqrt 2 := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  norm_num [vecOneNegOneC2, Fin.sum_univ_two]

/-- The normalized form of `(1, 1)`, namely `(1/√2, 1/√2)`; see
`unitVecOneOneC2_eq_norm_inv_smul`. -/
noncomputable def unitVecOneOneC2 : EuclideanSpace ℂ (Fin 2) :=
  !₂[(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹]

/-- The normalized form of `(1, -1)`, namely `(1/√2, -1/√2)`; see
`unitVecOneNegOneC2_eq_norm_inv_smul`. -/
noncomputable def unitVecOneNegOneC2 : EuclideanSpace ℂ (Fin 2) :=
  !₂[(Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹]

/-- **Nielsen & Chuang, Exercise 2.7 (normalized form of `(1, 1)`).** The
explicit vector `(1/√2, 1/√2)` is the normalized form of `(1, 1)`: dividing
`(1, 1)` by its norm `√2` (N&C: `|v⟩/‖v⟩‖`). -/
theorem unitVecOneOneC2_eq_norm_inv_smul :
    unitVecOneOneC2 = (‖vecOneOneC2‖ : ℂ)⁻¹ • vecOneOneC2 := by
  rw [norm_vecOneOneC2]
  ext i
  fin_cases i <;> simp [unitVecOneOneC2, vecOneOneC2]

/-- **Nielsen & Chuang, Exercise 2.7 (normalized form of `(1, -1)`).** The
explicit vector `(1/√2, -1/√2)` is the normalized form of `(1, -1)`: dividing
`(1, -1)` by its norm `√2` (N&C: `|v⟩/‖v⟩‖`). -/
theorem unitVecOneNegOneC2_eq_norm_inv_smul :
    unitVecOneNegOneC2 = (‖vecOneNegOneC2‖ : ℂ)⁻¹ • vecOneNegOneC2 := by
  rw [norm_vecOneNegOneC2]
  ext i
  fin_cases i <;> simp [unitVecOneNegOneC2, vecOneNegOneC2]

/-- The normalized form `(1/√2, 1/√2)` of `(1, 1)` is a unit vector: it has
norm `1`, confirming the normalization. -/
theorem norm_unitVecOneOneC2 : ‖unitVecOneOneC2‖ = 1 := by
  have h : vecOneOneC2 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_vecOneOneC2]
    exact (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [unitVecOneOneC2_eq_norm_inv_smul]
  exact norm_smul_inv_norm h

/-- The normalized form `(1/√2, -1/√2)` of `(1, -1)` is a unit vector: it has
norm `1`, confirming the normalization. -/
theorem norm_unitVecOneNegOneC2 : ‖unitVecOneNegOneC2‖ = 1 := by
  have h : vecOneNegOneC2 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_vecOneNegOneC2]
    exact (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [unitVecOneNegOneC2_eq_norm_inv_smul]
  exact norm_smul_inv_norm h

end AxQM.Concrete
