/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Concrete: every proper rotation of `ℝ³` fixes an axis (Euler's rotation theorem)

This file supplies the pure linear-algebra content behind the *axis* step of the qubit converse of
**Nielsen & Chuang, Problem 8.3** (p. 396): every `O ∈ SO(3)` has a unit vector it fixes.

> **Euler's rotation theorem.** For every `O ∈ SO(3)` there is a *unit* vector `n : Fin 3 → ℝ`
> (`n₀² + n₁² + n₂² = 1`) with `O n = n`.

## Context in N&C

Problem 8.3's qubit direction realises a unital single-qubit channel's Bloch matrix `M` as
`M = O₁ · diagonal d · O₂` (`Concrete.exists_specialOrthogonalGroup_diagonal_factor`) and must then
realise the proper rotations `O₁, O₂ ∈ SO(3)` as *unitary conjugations* on the Bloch sphere (the
`SU(2) → SO(3)` cover, whose forward direction is `Concrete.blochRotationOfUnitary`). The
surjectivity of that cover reduces to the classical **axis–angle decomposition** `O = rot3D n̂ θ`:
every proper
rotation is a rotation by some angle `θ` about some *axis* `n̂`, and `n̂` is exactly the unit
eigenvector of eigenvalue `1` provided here. Realising `rot3D n̂ θ` by the qubit rotation gate
`rotAxis n̂ θ` (`Concrete.blochMatrix_conj_rotAxis`) then closes the converse.

This file is the first ingredient: the *existence of the axis*.

## The proof (the classical determinant argument)

The eigenvalue `1` exists because `det(O − 1) = 0`. Transposing and using `Oᵀ O = 1`, `det O = 1`,

> `det(O − 1) = det((O − 1)ᵀ) = det(Oᵀ − 1) = det(Oᵀ (1 − O)) = det Oᵀ · det(1 − O)`
> `           = det(1 − O)`,

while `1 − O = (−1) • (O − 1)` gives `det(1 − O) = (−1)³ det(O − 1) = −det(O − 1)` in odd dimension
`3`. Hence `det(O − 1) = −det(O − 1)`, so `det(O − 1) = 0`. A singular matrix has a nonzero kernel
vector (`Matrix.exists_mulVec_eq_zero_iff`): some `v ≠ 0` with `(O − 1) v = 0`, i.e. `O v = v`.
Normalising `v` to `n = ‖v‖⁻¹ v` keeps `O n = n` (linearity) and makes it a unit vector.

Compare the `SO(3)` files `AxQM/Concrete/BlochSVD.lean` and
`AxQM/Concrete/BlochAffineDecomposition.lean`.
-/

namespace AxQM.Concrete

open Matrix

/-- **Euler's rotation theorem (existence of the axis).** Every proper rotation `O ∈ SO(3)` fixes a
unit vector: there is `n : Fin 3 → ℝ` with `n₀² + n₁² + n₂² = 1` and `O n = n`.

`n` is a unit eigenvector of eigenvalue `1`, whose existence follows from `det(O − 1) = 0` (the
classical determinant argument, using `Oᵀ O = 1`, `det O = 1`, and oddness of the dimension). It is
the rotation axis of the axis–angle decomposition `O = rot3D n̂ θ` underlying the `SU(2) → SO(3)`
surjectivity of the qubit converse of Nielsen & Chuang, Problem 8.3. -/
theorem exists_unit_mulVec_self_of_mem_specialOrthogonalGroup
    {O : Matrix (Fin 3) (Fin 3) ℝ} (hO : O ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ n : Fin 3 → ℝ, n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 ∧ O.mulVec n = n := by
  obtain ⟨hOgroup, hdetO⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hO
  have hOO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hOgroup
  -- `det (O - 1) = det (1 - O)` by transposing and factoring `Oᵀ - 1 = Oᵀ (1 - O)`.
  have hfac : Oᵀ - 1 = Oᵀ * (1 - O) := by rw [Matrix.mul_sub, Matrix.mul_one, hOO]
  have key : (O - 1).det = (1 - O).det := by
    rw [← Matrix.det_transpose (O - 1), Matrix.transpose_sub, Matrix.transpose_one, hfac,
      Matrix.det_mul, Matrix.det_transpose, hdetO, one_mul]
  -- but `1 - O = (-1) • (O - 1)`, so in dimension 3 `det (1 - O) = -det (O - 1)`.
  have hdet : (O - 1).det = 0 := by
    have h2 : (1 - O) = (-1 : ℝ) • (O - 1) := by rw [neg_one_smul]; abel
    rw [h2, Matrix.det_smul, Fintype.card_fin] at key
    have h3 : ((-1 : ℝ)) ^ 3 = -1 := by norm_num
    rw [h3] at key
    linarith [key]
  -- A singular matrix has a nonzero kernel vector `v`; then `O v = v`.
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hOv : O.mulVec v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hv
    exact sub_eq_zero.mp hv
  -- `v ≠ 0` so its squared length is positive; normalise `v` to a unit vector.
  have hs_pos : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    simp only [Pi.zero_apply] at hi
    fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hi <;>
      positivity
  refine ⟨(Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2))⁻¹ • v, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt hs_pos.le, ← mul_add,
      inv_mul_cancel₀ hs_pos.ne']
  · rw [Matrix.mulVec_smul, hOv]

end AxQM.Concrete
