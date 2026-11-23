/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation

/-!
# Concrete: conjugating the single-qubit rotations by Pauli-`X` (Nielsen & Chuang, Exercise 4.7)

Nielsen & Chuang, Exercise 4.7 asks to show `X Y X = -Y` and to use it to prove
`X R_y(θ) X = R_y(-θ)`. Both are `2 × 2` complex-matrix identities, stated for the concrete
Pauli matrices `pauliX`/`pauliY`/`pauliZ` and the rotation operators `rotY`/`rotZ`.

## What is formalized

* `pauliX_mul_pauliY_mul_pauliX` — `X Y X = -Y` (Exercise 4.7, first part).
* `pauliX_mul_pauliZ_mul_pauliX` — `X Z X = -Z` (the same computation for `Z`).
* `pauliX_mul_rotY_mul_pauliX` — `X R_y(θ) X = R_y(-θ)` (Exercise 4.7, second part).
* `pauliX_mul_rotZ_mul_pauliX` — `X R_z(θ) X = R_z(-θ)` (the `R_z` analogue).

The two `X σ X = -σ` facts hold because conjugation by `X` fixes `X` but negates the two Pauli
matrices that anticommute with it. Since `R_a(θ) = cos(θ/2) I − i sin(θ/2) a` for `a ∈ {Y, Z}`
(the closed form of eq. 4.5/4.6) and `X I X = I`, conjugation by `X` therefore flips the sign of
the `sin` term, i.e. sends `θ ↦ −θ`:
`X R_a(θ) X = cos(θ/2) I − i sin(θ/2) (X a X) = cos(θ/2) I + i sin(θ/2) a = R_a(−θ)`.

## Use in later results

These conjugation identities are the shared foundation for the `X`-based reshufflings in
Chapter 4's single-qubit decompositions. In particular the ABC decomposition (N&C Corollary 4.2)
uses exactly `X R_y(θ) X = R_y(-θ)` and `X R_z(θ) X = R_z(-θ)` to move the two `X` gates through
the middle rotation `B`.

## Design notes

* The two rotation identities are proved directly from the explicit closed-form matrices
  `rotY_eq`/`rotZ_eq` (eq. 4.5/4.6) by the entrywise `2 × 2` computation, with the sign flip
  supplied by `Real.cos_neg`/`Real.sin_neg`. This is the same reduce-to-a-closed-form-and-compute
  idiom used throughout `Concrete/Pauli.lean` and `Concrete/Rotation.lean`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **Nielsen & Chuang, Exercise 4.7 (first part)**: conjugating `Y` by `X` negates it,
`X Y X = -Y`. -/
theorem pauliX_mul_pauliY_mul_pauliX : pauliX * pauliY * pauliX = -pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-- Conjugating `Z` by `X` negates it, `X Z X = -Z` (the analogue of the first part of
Exercise 4.7 for `Z`; used in the ABC decomposition, Corollary 4.2). -/
theorem pauliX_mul_pauliZ_mul_pauliX : pauliX * pauliZ * pauliX = -pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-- **Nielsen & Chuang, Exercise 4.7 (second part)**: `X R_y(θ) X = R_y(-θ)`. Conjugation by `X`
negates the `Y` component of the rotation, sending `θ ↦ -θ`. -/
theorem pauliX_mul_rotY_mul_pauliX (θ : ℝ) : pauliX * rotY θ * pauliX = rotY (-θ) := by
  rw [rotY_eq, rotY_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, neg_div]

/-- `X R_z(θ) X = R_z(-θ)` (the `R_z` analogue of Exercise 4.7). Conjugation by `X` swaps the two
diagonal phases `exp(∓iθ/2)`, which is exactly `R_z(-θ)`. Used in the ABC decomposition
(Corollary 4.2). -/
theorem pauliX_mul_rotZ_mul_pauliX (θ : ℝ) : pauliX * rotZ θ * pauliX = rotZ (-θ) := by
  rw [rotZ_eq, rotZ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_neg, neg_div]

end AxQM.Concrete
