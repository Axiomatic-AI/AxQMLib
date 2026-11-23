/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFC

/-!
# Diagonal Cauchy–Schwarz bounds for the operator square root

For a positive operator `A ≥ 0` on a complex Hilbert space and a vector `x`, this file records the
**diagonal Cauchy–Schwarz bounds** for the operator square root `√A = cfc Real.sqrt A`:

* `0 ≤ ⟪x, √A x⟫`   (the diagonal overlap is nonnegative), and
* `⟪x, √A x⟫²  ≤  ‖x‖² · ⟪x, A x⟫`   (its square is controlled by the diagonal of `A`),

together with the consequence that on a unit vector where `A` is a contraction the overlap lies in
`[0, 1]`.  (All inner products are real, `√A` being positive; the statements use `RCLike.re`.)

## Motivation

This is the "diagonal overlap" step of **Nielsen & Chuang's Box 12.5**, the achievability half of
the **Holevo–Schumacher–Westmoreland theorem** (`χ(E) = C⁽¹⁾(E)`, N&C Theorem 12.8).  There the
decoding overlap coefficients `α_{c,c'} = ⟨Ẽ_c | S⁻¹ᐟ² | Ẽ_{c'}⟩` of the pretty-good (square-root)
measurement are the entries of `α = V⋆ · S⁻¹ᐟ² · V = √Γ`, the operator square root of the Gram
operator
`Γ = V⋆ V` of the (typical-subspace–compressed) codeword vectors `Ẽ_c = V e_c`
(`ContinuousLinearMap.adjoint_comp_genInvSqrt_comp_self`).  The diagonal entry
`α_{c,c} = ⟪e_c, √Γ e_c⟫` therefore obeys, by the bounds below applied to `A = Γ` and `x = e_c`,

`α_{c,c}²  ≤  ⟪e_c, Γ e_c⟫  =  ‖Ẽ_c‖²  =  γ_{c,c}  ≤  1`   (`Ẽ_c` a compression of a unit vector),

so `0 ≤ α_{c,c} ≤ 1` — precisely the input to N&C's eq. (12.87)→(12.88) step, where
`1 - x² = (1+x)(1-x) ≤ 2(1-x)` for `0 ≤ x ≤ 1` turns the diagonal deficiency `1 - α²_{c,c}` into
`2(1 - α_{c,c})`, which the square-root operator inequality
(`ContinuousLinearMap.two_smul_one_sub_cfc_sqrt_le`) then controls.

## What this file provides

* `ContinuousLinearMap.re_inner_cfc_real_sqrt_nonneg` — `0 ≤ re ⟪x, √A x⟫`.
* `ContinuousLinearMap.re_inner_cfc_real_sqrt_sq_le` — `(re ⟪x, √A x⟫)² ≤ ‖x‖² · re ⟪x, A x⟫`
  for `0 ≤ A`.
* `ContinuousLinearMap.re_inner_cfc_real_sqrt_le_one` — for `0 ≤ A`, on a unit `x` with
  `re ⟪x, A x⟫ ≤ 1`, `re ⟪x, √A x⟫ ≤ 1`.

## Proof

Write `B = √A`.  It is positive (`cfc_nonneg`, `Real.sqrt ≥ 0`), giving `0 ≤ re ⟪x, B x⟫` — this
half needs no positivity of `A`.  For a positive `A`, `B` is moreover self-adjoint
(`IsSelfAdjoint.cfc`) with `B * B = A` (`cfc_mul` folded to the identity via `√x · √x = x` on the
nonnegative spectrum), so `‖B x‖² = re ⟪B x, B x⟫ = re ⟪x, (B†B) x⟫ = re ⟪x, A x⟫`, and
Cauchy–Schwarz `re ⟪x, B x⟫ ≤ ‖⟪x, B x⟫‖ ≤ ‖x‖ · ‖B x‖` squares (both sides nonnegative) to
`(re ⟪x, B x⟫)² ≤ ‖x‖² · ‖B x‖² = ‖x‖² · re ⟪x, A x⟫`.  The `[0, 1]` bound is then immediate.
-/

@[expose] public section

open ContinuousFunctionalCalculus

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The diagonal overlap of the operator square root is nonnegative.**  For any operator
`A : E →L[ℂ] E` and any vector `x`,

`0 ≤ re ⟪x, √A x⟫`,

where `√A = cfc Real.sqrt A`.  Immediate from positivity of `√A` (`cfc_nonneg`, as `Real.sqrt ≥ 0`);
no positivity of `A` is needed for this half.  It is the `α_{c,c} ≥ 0` half of the diagonal
decoding-overlap bound of Nielsen & Chuang's Box 12.5. -/
theorem re_inner_cfc_real_sqrt_nonneg (A : E →L[ℂ] E) (x : E) :
    0 ≤ RCLike.re (inner ℂ x (cfc Real.sqrt A x)) :=
  (nonneg_iff_isPositive.mp (cfc_nonneg fun y _ => Real.sqrt_nonneg y)).re_inner_nonneg_right x

/-- **The diagonal Cauchy–Schwarz bound for the operator square root.**  For a positive operator
`A ≥ 0` and any vector `x`,

`(re ⟪x, √A x⟫)²  ≤  ‖x‖² · re ⟪x, A x⟫`,

where `√A = cfc Real.sqrt A`.  Writing `B = √A` (self-adjoint, `B * B = A`), the norm identity
`‖B x‖² = re ⟪x, A x⟫` and Cauchy–Schwarz `re ⟪x, B x⟫ ≤ ‖x‖ · ‖B x‖` square to the claim.  Applied
to the Gram operator `A = Γ = V⋆ V` and a unit basis vector `x = e_c`, this is N&C's Box 12.5 bound
`α²_{c,c} ≤ γ_{c,c}` on the pretty-good measurement's diagonal decoding overlap. -/
theorem re_inner_cfc_real_sqrt_sq_le {A : E →L[ℂ] E} (hA : 0 ≤ A) (x : E) :
    RCLike.re (inner ℂ x (cfc Real.sqrt A x)) ^ 2 ≤ ‖x‖ ^ 2 * RCLike.re (inner ℂ x (A x)) := by
  set B := cfc Real.sqrt A with hB
  -- `B` is self-adjoint with `B * B = A` (`√A` a real functional-calculus image).
  have hsaB : IsSelfAdjoint B := IsSelfAdjoint.cfc
  have hsa : adjoint B = B := by rw [← star_eq_adjoint]; exact hsaB.star_eq
  have hself : B * B = A := by
    rw [hB, ← cfc_mul Real.sqrt Real.sqrt A Real.continuous_sqrt.continuousOn
        Real.continuous_sqrt.continuousOn]
    conv_rhs => rw [← cfc_id' ℝ A]
    exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hA hx)
  -- `‖B x‖² = re ⟪x, A x⟫`.
  have hnormBx : ‖B x‖ ^ 2 = RCLike.re (inner ℂ x (A x)) := by
    have e1 : (inner ℂ (B x) (B x) : ℂ) = inner ℂ x (A x) := by
      rw [← adjoint_inner_right B x (B x), hsa, ← mul_apply_eq_comp, hself]
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), e1]
  -- Cauchy–Schwarz: `re ⟪x, B x⟫ ≤ ‖x‖ · ‖B x‖`.
  have hcs : RCLike.re (inner ℂ x (B x)) ≤ ‖x‖ * ‖B x‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm (𝕜 := ℂ) x (B x))
  have hnn : 0 ≤ RCLike.re (inner ℂ x (B x)) := re_inner_cfc_real_sqrt_nonneg A x
  calc RCLike.re (inner ℂ x (B x)) ^ 2
      ≤ (‖x‖ * ‖B x‖) ^ 2 := pow_le_pow_left₀ hnn hcs 2
    _ = ‖x‖ ^ 2 * RCLike.re (inner ℂ x (A x)) := by rw [mul_pow, hnormBx]

/-- **The diagonal overlap of the operator square root is at most `1`** on a unit vector where `A`
is a contraction.  For a positive operator `A ≥ 0`, a unit vector `x` (`‖x‖ = 1`), and
`re ⟪x, A x⟫ ≤ 1`,

`re ⟪x, √A x⟫ ≤ 1`.

From the Cauchy–Schwarz bound `(re ⟪x, √A x⟫)² ≤ ‖x‖² · re ⟪x, A x⟫ = re ⟪x, A x⟫ ≤ 1` and
nonnegativity of `re ⟪x, √A x⟫`.  With `A = Γ` and `x = e_c` this is `α_{c,c} ≤ 1`
(`γ_{c,c} = ‖Ẽ_c‖² ≤ 1`), the remaining half of N&C's diagonal decoding-overlap bound
(Box 12.5, eq. (12.87)→(12.88)). -/
theorem re_inner_cfc_real_sqrt_le_one {A : E →L[ℂ] E} (hA : 0 ≤ A) {x : E} (hx : ‖x‖ = 1)
    (hAx : RCLike.re (inner ℂ x (A x)) ≤ 1) :
    RCLike.re (inner ℂ x (cfc Real.sqrt A x)) ≤ 1 := by
  have hsq := re_inner_cfc_real_sqrt_sq_le hA x
  rw [hx, one_pow, one_mul] at hsq
  have hnn := re_inner_cfc_real_sqrt_nonneg A x
  nlinarith [hsq, hnn, hAx]

end ContinuousLinearMap
