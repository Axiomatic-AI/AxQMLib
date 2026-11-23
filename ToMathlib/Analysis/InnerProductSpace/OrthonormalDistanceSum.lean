/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Algebra.Order.Chebyshev
public import ToMathlib.Data.Real.Sqrt

/-! # Sum of squared distances from a vector to an orthonormal family

For a normalized vector `ψ` and a finite orthonormal family `v : ι → E`, the total squared
distance from `ψ` to the members of the family is bounded below:
`∑ x, ‖ψ - v x‖² ≥ 2N - 2√N`, where `N = Fintype.card ι` is the number of vectors.

The two ingredients are **Bessel's inequality** (`Orthonormal.sum_inner_products_le`,
`∑ x, ‖⟪v x, ψ⟫‖² ≤ ‖ψ‖²`) and the **Cauchy–Schwarz inequality for finite sums**
(`sq_sum_le_card_mul_sum_sq`, `(∑ x, f x)² ≤ N · ∑ x, f x²`). Together they give the reusable
bound `∑ x, re ⟪ψ, v x⟫ ≤ √N · ‖ψ‖`; expanding `‖ψ - v x‖² = 2 - 2·re ⟪ψ, v x⟫` (via
`norm_sub_pow_two`, using `‖ψ‖ = ‖v x‖ = 1`) then yields the distance bound.

## Main results

* `Orthonormal.sum_re_inner_le_sqrt_card_mul_norm`: `∑ x, re ⟪ψ, v x⟫ ≤ √N · ‖ψ‖` for any `ψ`.
* `Orthonormal.two_mul_card_sub_two_mul_sqrt_card_le_sum_norm_sub_sq`: for a normalized `ψ`,
  `2N - 2√N ≤ ∑ x, ‖ψ - v x‖²`.

The second statement is Exercise 6.15 of Nielsen & Chuang, *Quantum Computation and Quantum
Information* (eq. 6.53), used in the proof that the quantum search algorithm is optimal. It is
stated for an arbitrary finite orthonormal family (not necessarily a basis), which is the natural
generality: Bessel's inequality does not require the family to span the space.
-/

@[expose] public section

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] {v : ι → E}

/-- **Cauchy–Schwarz combined with Bessel's inequality**: for a finite orthonormal family
`v : ι → E` and any vector `ψ`, the sum of the real parts of the inner products `⟪ψ, v x⟫` is at
most `√N · ‖ψ‖`, where `N = Fintype.card ι`.

The chain is `∑ x, re ⟪ψ, v x⟫ ≤ ∑ x, ‖⟪v x, ψ⟫‖` (real part is at most the norm), then Cauchy–
Schwarz `(∑ x, ‖⟪v x, ψ⟫‖)² ≤ N · ∑ x, ‖⟪v x, ψ⟫‖²`, then Bessel's inequality
`∑ x, ‖⟪v x, ψ⟫‖² ≤ ‖ψ‖²`, and finally taking square roots. -/
theorem Orthonormal.sum_re_inner_le_sqrt_card_mul_norm
    (hv : Orthonormal 𝕜 v) (ψ : E) :
    ∑ x, RCLike.re (inner 𝕜 ψ (v x)) ≤ Real.sqrt (Fintype.card ι) * ‖ψ‖ := by
  have h1 : ∑ x, RCLike.re (inner 𝕜 ψ (v x)) ≤ ∑ x, ‖inner 𝕜 (v x) ψ‖ := by
    apply Finset.sum_le_sum
    intro x _
    calc RCLike.re (inner 𝕜 ψ (v x)) ≤ ‖inner 𝕜 ψ (v x)‖ := RCLike.re_le_norm _
      _ = ‖inner 𝕜 (v x) ψ‖ := norm_inner_symm _ _
  have hbessel : ∑ x, ‖inner 𝕜 (v x) ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := hv.sum_inner_products_le ψ
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have h2 : (∑ x, ‖inner 𝕜 (v x) ψ‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ‖ψ‖ ^ 2 := by
    calc (∑ x, ‖inner 𝕜 (v x) ψ‖) ^ 2
        ≤ (Finset.univ.card : ℝ) * ∑ x, ‖inner 𝕜 (v x) ψ‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = (Fintype.card ι : ℝ) * ∑ x, ‖inner 𝕜 (v x) ψ‖ ^ 2 := by rw [Finset.card_univ]
      _ ≤ (Fintype.card ι : ℝ) * ‖ψ‖ ^ 2 := mul_le_mul_of_nonneg_left hbessel hcard
  calc ∑ x, RCLike.re (inner 𝕜 ψ (v x))
      ≤ ∑ x, ‖inner 𝕜 (v x) ψ‖ := h1
    _ ≤ |∑ x, ‖inner 𝕜 (v x) ψ‖| := le_abs_self _
    _ = Real.sqrt ((∑ x, ‖inner 𝕜 (v x) ψ‖) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ‖ψ‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (Fintype.card ι) * ‖ψ‖ := by
        rw [Real.sqrt_mul hcard, Real.sqrt_sq (norm_nonneg ψ)]

/-- **Nielsen & Chuang, Exercise 6.15** (eq. 6.53): for a normalized state vector `ψ`
(`‖ψ‖ = 1`) and a set of `N` orthonormal vectors `v x`,
`∑ x, ‖ψ - v x‖² ≥ 2N - 2√N`, where `N = Fintype.card ι`.

Expanding `‖ψ - v x‖² = 2 - 2·re ⟪ψ, v x⟫` (both `ψ` and each `v x` are unit vectors) turns the
sum into `2N - 2·∑ x, re ⟪ψ, v x⟫`, and `Orthonormal.sum_re_inner_le_sqrt_card_mul_norm` bounds
`∑ x, re ⟪ψ, v x⟫ ≤ √N`. Used in Section 6.6 to prove the `Ω(√N)` lower bound on the number of
oracle queries for quantum search. -/
theorem Orthonormal.two_mul_card_sub_two_mul_sqrt_card_le_sum_norm_sub_sq
    (hv : Orthonormal 𝕜 v) {ψ : E} (hψ : ‖ψ‖ = 1) :
    2 * (Fintype.card ι : ℝ) - 2 * Real.sqrt (Fintype.card ι) ≤ ∑ x, ‖ψ - v x‖ ^ 2 := by
  have key : ∑ x, ‖ψ - v x‖ ^ 2
      = 2 * (Fintype.card ι : ℝ) - 2 * ∑ x, RCLike.re (inner 𝕜 ψ (v x)) := by
    have hterm : ∀ x, ‖ψ - v x‖ ^ 2 = 2 - 2 * RCLike.re (inner 𝕜 ψ (v x)) := fun x => by
      rw [norm_sub_pow_two (𝕜 := 𝕜), hψ, hv.norm_eq_one x]; ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum,
      nsmul_eq_mul]
    ring
  have hbound : ∑ x, RCLike.re (inner 𝕜 ψ (v x)) ≤ Real.sqrt (Fintype.card ι) := by
    have h := hv.sum_re_inner_le_sqrt_card_mul_norm ψ
    rwa [hψ, mul_one] at h
  rw [key]
  linarith [hbound]
