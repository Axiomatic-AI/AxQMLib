/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.BinaryEntropyBit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Convex.Deriv

/-!
# A quadratic upper bound on the binary entropy function

The binary entropy function is concave and attains its maximum, `log 2` (nats) or `1` (bits),
at `p = 1 / 2`. This file records the sharper *quadratic* upper bound

`binEntropy p ≤ log 2 * (1 - 2 * (p - 1 / 2) ^ 2)`   (nats)

equivalently, in bits,

`binEntropyBit p ≤ 1 - 2 * (p - 1 / 2) ^ 2`,

for `p ∈ [0, 1]`. The parabola on the right osculates the entropy at `p = 1 / 2` (both equal `1`
in bits there) and controls how fast the entropy drops away from its maximum. It is the bound
`H(x) < 1 - 2 (x - 1/2)²` used in step (3) of Nielsen & Chuang, Exercise 12.27 (random sampling
tests), where the quadratic gap is what turns an entropy estimate into an `exp[-Θ(ε² n)]` tail
bound.

## Main results

* `Real.binEntropy_le_log_two_mul_one_sub_two_mul_sq`: `binEntropy p ≤ log 2 * (1 - 2 (p - 1/2)²)`
  on `[0, 1]`.
* `Real.binEntropyBit_le_one_sub_two_mul_sq`: `binEntropyBit p ≤ 1 - 2 (p - 1/2)²` on `[0, 1]`.

## Proof

Both sides agree at `p = 1 / 2`, so it suffices to show the *gap*
`g p := log 2 * (1 - 2 (p - 1/2)²) - binEntropy p` is nonnegative on `[0, 1]`. The gap is convex:
its second derivative is `1 / (p (1 - p)) - 4 log 2 ≥ 4 - 4 log 2 > 0`, since `p (1 - p) ≤ 1 / 4`
and `log 2 ≤ 1`. A convex function whose derivative vanishes at an interior point attains its
minimum there, and `g (1 / 2) = 0`, giving `g ≥ 0`.
-/

open Set

namespace Real

public section

/-- **Quadratic upper bound on the binary entropy** (in nats): for `p ∈ [0, 1]`,
`binEntropy p ≤ log 2 * (1 - 2 * (p - 1 / 2) ^ 2)`. The parabola on the right touches the entropy
at its maximum `p = 1 / 2` and bounds how quickly the entropy decreases away from it; this is the
quadratic entropy bound `H(x) < 1 - 2 (x - 1/2)²` of Nielsen & Chuang, Exercise 12.27 step (3). -/
theorem binEntropy_le_log_two_mul_one_sub_two_mul_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    binEntropy x ≤ log 2 * (1 - 2 * (x - 2⁻¹) ^ 2) := by
  set g : ℝ → ℝ := fun x => log 2 * (1 - 2 * (x - 2⁻¹) ^ 2) - binEntropy x with hg
  -- The first derivative of `g` on the open interval `(0, 1)`.
  have hg1 : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt g (-4 * log 2 * (y - 2⁻¹) - log (1 - y) + log y) y := by
    intro y hy
    have hy0 : y ≠ 0 := (hy.1).ne'
    have hy1 : y ≠ 1 := (hy.2).ne
    have hbin : HasDerivAt binEntropy (log (1 - y) - log y) y := hasDerivAt_binEntropy hy0 hy1
    have hsq : HasDerivAt (fun z : ℝ => (z - 2⁻¹) ^ 2) (2 * (y - 2⁻¹)) y := by
      simpa using ((hasDerivAt_id y).sub_const 2⁻¹).fun_pow 2
    have hpoly : HasDerivAt (fun z : ℝ => log 2 * (1 - 2 * (z - 2⁻¹) ^ 2))
        (-4 * log 2 * (y - 2⁻¹)) y := by
      have h := ((hsq.const_mul (2 : ℝ)).const_sub (1 : ℝ)).const_mul (log 2)
      convert h using 1
      ring
    rw [hg]
    convert hpoly.sub hbin using 1
    ring
  -- The second derivative of `g` on `(0, 1)`.
  have hg2 : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun z : ℝ => -4 * log 2 * (z - 2⁻¹) - log (1 - z) + log z)
        (1 / (y * (1 - y)) - 4 * log 2) y := by
    intro y hy
    have hy0 : y ≠ 0 := (hy.1).ne'
    have hy1' : (1 : ℝ) - y ≠ 0 := by have := hy.2; intro h; simp_all; linarith
    have hlin : HasDerivAt (fun z : ℝ => -4 * log 2 * (z - 2⁻¹)) (-4 * log 2) y := by
      simpa using ((hasDerivAt_id y).sub_const 2⁻¹).const_mul (-4 * log 2)
    have hlog1 : HasDerivAt (fun z : ℝ => log (1 - z)) (-1 / (1 - y)) y := by
      simpa using ((hasDerivAt_id y).const_sub 1).log hy1'
    have hlog2 : HasDerivAt (fun z : ℝ => log z) y⁻¹ y := hasDerivAt_log hy0
    have hcomb := (hlin.sub hlog1).add hlog2
    convert hcomb using 1
    field_simp
    ring
  -- `g` is continuous on `[0, 1]`, differentiable and convex on the interior.
  have hcont : Continuous g := by
    rw [hg]
    exact (by fun_prop : Continuous fun x : ℝ => log 2 * (1 - 2 * (x - 2⁻¹) ^ 2)).sub
      binEntropy_continuous
  have hdiff : DifferentiableOn ℝ g (interior (Icc 0 1)) := by
    rw [interior_Icc]
    exact fun y hy => (hg1 y hy).differentiableAt.differentiableWithinAt
  have hderiv_eq : EqOn (deriv g)
      (fun z : ℝ => -4 * log 2 * (z - 2⁻¹) - log (1 - z) + log z) (Ioo 0 1) :=
    fun y hy => (hg1 y hy).deriv
  have hdiff2 : DifferentiableOn ℝ (deriv g) (interior (Icc 0 1)) := by
    rw [interior_Icc]
    have hg2diff : DifferentiableOn ℝ
        (fun z : ℝ => -4 * log 2 * (z - 2⁻¹) - log (1 - z) + log z) (Ioo 0 1) :=
      fun y hy => (hg2 y hy).differentiableAt.differentiableWithinAt
    exact hg2diff.congr hderiv_eq
  have hderiv2nn : ∀ y ∈ interior (Icc (0 : ℝ) 1), 0 ≤ deriv^[2] g y := by
    intro y hy
    rw [interior_Icc] at hy
    have hpos : 0 < y * (1 - y) := mul_pos hy.1 (by linarith [hy.2])
    have hval : deriv^[2] g y = 1 / (y * (1 - y)) - 4 * log 2 := by
      have hee : deriv g =ᶠ[nhds y]
          (fun z : ℝ => -4 * log 2 * (z - 2⁻¹) - log (1 - z) + log z) :=
        hderiv_eq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy)
      have : deriv^[2] g y = deriv (deriv g) y := rfl
      rw [this, hee.deriv_eq, (hg2 y hy).deriv]
    rw [hval]
    have h4 : (4 : ℝ) ≤ 1 / (y * (1 - y)) := by
      rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg (y - 2⁻¹)]
    have hlog2le : log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    nlinarith [h4, hlog2le]
  have hconv : ConvexOn ℝ (Icc 0 1) g :=
    convexOn_of_deriv2_nonneg (convex_Icc 0 1) hcont.continuousOn hdiff hdiff2 hderiv2nn
  -- `g` attains its minimum at `1 / 2`, where its derivative vanishes, and `g (1 / 2) = 0`.
  have hhalf : (2⁻¹ : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hderiv_half : HasDerivAt g 0 2⁻¹ := by
    have h := hg1 2⁻¹ hhalf
    convert h using 1
    have h1 : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
    rw [h1]; ring
  have hmem : (2⁻¹ : ℝ) ∈ interior (Icc (0 : ℝ) 1) := by rw [interior_Icc]; exact hhalf
  have hmin : IsMinOn g (Icc 0 1) 2⁻¹ :=
    hconv.isMinOn_of_rightDeriv_eq_zero hmem
      (HasDerivWithinAt.derivWithin hderiv_half.hasDerivWithinAt (uniqueDiffWithinAt_Ioi _))
  have hg_half : g 2⁻¹ = 0 := by
    simp only [hg, binEntropy_two_inv]; ring
  have key := (isMinOn_iff.1 hmin) x ⟨hx0, hx1⟩
  rw [hg_half, hg] at key
  simp only at key
  linarith

/-- **Quadratic upper bound on the binary entropy** (in bits): for `p ∈ [0, 1]`,
`binEntropyBit p ≤ 1 - 2 * (p - 1 / 2) ^ 2`. The bits form of
`Real.binEntropy_le_log_two_mul_one_sub_two_mul_sq`: since a fair coin carries one bit, the
osculating parabola is `1 - 2 (p - 1/2)²`. This is the quadratic entropy bound of Nielsen &
Chuang, Exercise 12.27 step (3), in the base-`2` normalisation N&C uses. -/
theorem binEntropyBit_le_one_sub_two_mul_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    binEntropyBit x ≤ 1 - 2 * (x - 2⁻¹) ^ 2 := by
  rw [binEntropyBit_eq_binEntropy_div_log_two, div_le_iff₀ (log_pos (by norm_num)), mul_comm]
  exact binEntropy_le_log_two_mul_one_sub_two_mul_sq hx0 hx1

end

end Real
