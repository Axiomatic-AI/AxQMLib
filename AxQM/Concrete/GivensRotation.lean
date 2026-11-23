/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import ToMathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Basic.Complex.Basic
import ToMathlib.Data.Real.Sqrt
import ToMathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul

/-!
# Concrete: the 2×2 Givens rotation clearing a column entry (N&C eq. 4.45)

The two-level decomposition of an arbitrary `d × d` unitary (Nielsen & Chuang §4.5.1, p. 189) is
built from a sequence of *two-level* unitaries `U₁, U₂, …` chosen so that `Uₖ ⋯ U₁ U` has its first
column equal to `e₀`. Each `Uₖ` is obtained by embedding, into a chosen `{p, q}` coordinate pair, a
single `2 × 2` unitary — the **Givens rotation** of N&C eq. (4.45) — that zeros the second entry of
the length-two column `(a, b)` it acts on. This file provides that atomic `2 × 2` building block,
independently of the `d × d` embedding and the column-clearing induction.

## The construction

For a column `(a, b) : ℂ²` write `r = givensNorm a b = √(|a|² + |b|²)` for its Euclidean length.
Following N&C eq. (4.45), when `(a, b) ≠ 0` set

```
  givensRotation a b = r⁻¹ • !![conj a, conj b; b, -a],
```

and `givensRotation a b = 1` when `a = b = 0` (the degenerate case, where there is nothing to
clear; N&C's own `U₁ = I` branch of eq. (4.44)). Two facts make it the required clearing step:

* `givensRotation_mem_unitaryGroup` — it is unitary. In the non-degenerate branch
  `Gᴴ G = r⁻² • (Mᴴ M) = r⁻² • (r² • 1) = 1`, since `Mᴴ M = (|a|² + |b|²) • 1 = r² • 1`.
* `givensRotation_mulVec` — it clears the column: `G *ᵥ ![a, b] = ![r, 0]`. The first entry is
  `r⁻¹ · (conj a · a + conj b · b) = r⁻¹ · (|a|² + |b|²) = r⁻¹ · r² = r`; the second is
  `r⁻¹ · (b · a − a · b) = 0`. This holds in *all* cases, including `a = b = 0` (both sides are
  `![0, 0]`, as `r = 0` there).

## Use

This is a shared building block for the §4.5.1 development (used by Exercise 4.43's `n`-qubit lift
and reusable by Exercises 4.37 and 4.38). The statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

/-- The Euclidean length `√(|a|² + |b|²)` of the column `(a, b) : ℂ²`; the normalising scalar of the
Givens rotation `givensRotation a b`. -/
noncomputable def givensNorm (a b : ℂ) : ℝ :=
  Real.sqrt (Complex.normSq a + Complex.normSq b)

/-- `givensNorm` is nonnegative (a square root). -/
theorem givensNorm_nonneg (a b : ℂ) : 0 ≤ givensNorm a b := Real.sqrt_nonneg _

/-- The square of `givensNorm` recovers the sum of squared moduli: `r² = |a|² + |b|²`. -/
theorem givensNorm_sq (a b : ℂ) :
    givensNorm a b ^ 2 = Complex.normSq a + Complex.normSq b :=
  Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b))

/-- `givensNorm` vanishes only in the degenerate case: if `(a, b) ≠ 0` then `r ≠ 0`. -/
theorem givensNorm_ne_zero {a b : ℂ} (h : ¬(a = 0 ∧ b = 0)) : givensNorm a b ≠ 0 := by
  rw [givensNorm, Real.sqrt_ne_zero']
  rcases not_and_or.mp h with ha | hb
  · have h1 := Complex.normSq_pos.mpr ha
    have h2 := Complex.normSq_nonneg b
    linarith
  · have h1 := Complex.normSq_pos.mpr hb
    have h2 := Complex.normSq_nonneg a
    linarith

/-- The complex-cast form of `givensNorm_sq`: `(r : ℂ)² = |a|² + |b|²`. -/
theorem givensNorm_sq_complex (a b : ℂ) :
    (givensNorm a b : ℂ) ^ 2 = (Complex.normSq a : ℂ) + (Complex.normSq b : ℂ) := by
  rw [← Complex.ofReal_pow, givensNorm_sq]; push_cast; ring

/-- **The Givens rotation of Nielsen & Chuang eq. (4.45).** The `2 × 2` unitary that clears the
second entry of the column `(a, b)`: for `(a, b) ≠ 0` it is `r⁻¹ • !![conj a, conj b; b, -a]` (with
`r = givensNorm a b`), and the identity in the degenerate case `a = b = 0`. -/
noncomputable def givensRotation (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a = 0 ∧ b = 0 then 1
  else (givensNorm a b : ℂ)⁻¹ • !![starRingEnd ℂ a, starRingEnd ℂ b; b, -a]

/-- The core `2 × 2` product identity behind unitarity: `Mᴴ M = (|a|² + |b|²) • 1`, where
`M = !![conj a, conj b; b, -a]` is the unnormalised Givens block. -/
theorem givensBlock_conjTranspose_mul_self (a b : ℂ) :
    (!![starRingEnd ℂ a, starRingEnd ℂ b; b, -a] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
        !![starRingEnd ℂ a, starRingEnd ℂ b; b, -a]
      = ((Complex.normSq a : ℂ) + Complex.normSq b) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.smul_apply,
      ← Complex.normSq_eq_conj_mul_self] <;> ring

/-- **The Givens rotation is unitary.** In the non-degenerate branch,
`Gᴴ G = r⁻² • (Mᴴ M) = r⁻² • (r² • 1) = 1`. -/
theorem givensRotation_mem_unitaryGroup (a b : ℂ) :
    givensRotation a b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  by_cases h : a = 0 ∧ b = 0
  · rw [givensRotation, ite_eq_left h]; simp
  · have hr : (givensNorm a b : ℂ) ≠ 0 := by exact_mod_cast givensNorm_ne_zero h
    have key : (givensNorm a b : ℂ)⁻¹ * (givensNorm a b : ℂ)⁻¹ *
        ((Complex.normSq a : ℂ) + Complex.normSq b) = 1 := by
      rw [← givensNorm_sq_complex]; field_simp
    have hstar : star ((givensNorm a b : ℂ)⁻¹) = (givensNorm a b : ℂ)⁻¹ := by simp
    rw [givensRotation, ite_eq_right h, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, givensBlock_conjTranspose_mul_self, smul_smul, smul_smul,
      hstar, key, one_smul]

/-- **The Givens rotation clears the column.** `givensRotation a b *ᵥ ![a, b] = ![r, 0]` with
`r = givensNorm a b`: the second component is zeroed and the first becomes the column's length. This
holds in all cases (in the degenerate `a = b = 0` case both sides are `![0, 0]`). -/
theorem givensRotation_mulVec (a b : ℂ) :
    givensRotation a b *ᵥ ![a, b] = ![(givensNorm a b : ℂ), 0] := by
  by_cases h : a = 0 ∧ b = 0
  · obtain ⟨ha, hb⟩ := h
    subst ha; subst hb
    funext i; fin_cases i <;> simp [givensRotation, givensNorm]
  · have hr : (givensNorm a b : ℂ) ≠ 0 := by exact_mod_cast givensNorm_ne_zero h
    have hMv : (!![starRingEnd ℂ a, starRingEnd ℂ b; b, -a] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![a, b]
        = ![(Complex.normSq a : ℂ) + Complex.normSq b, 0] := by
      funext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ← Complex.normSq_eq_conj_mul_self]
      ring
    rw [givensRotation, ite_eq_right h, Matrix.smul_mulVec, hMv, ← givensNorm_sq_complex]
    funext i
    fin_cases i <;> simp [pow_two, inv_mul_cancel_left₀ hr]

/-- **The Givens clearing identity as a scalar equation.** Applying `givensRotation a b` to the
column `(a, b)` zeroes the second component: `givensRotation a b 1 0 * a + givensRotation a b 1 1 *
b = 0`. Extracted from `givensRotation_mulVec` (its second output component), this is the arithmetic
behind zeroing one entry in the column-clearing step of §4.5.1. -/
theorem givensRotation_row_one_dotProduct (a b : ℂ) :
    givensRotation a b 1 0 * a + givensRotation a b 1 1 * b = 0 := by
  have h := congrFun (givensRotation_mulVec a b) 1
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

end AxQM.Concrete
