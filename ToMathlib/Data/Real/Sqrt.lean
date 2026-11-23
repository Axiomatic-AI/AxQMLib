/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Square root of a real number: conjugate-multiplication identities

Extends `Mathlib.Data.Real.Sqrt` with conjugate-multiplication factorizations and squared
binomial expansions for `Real.sqrt`, used for triangle-inequality and L¹-distance arguments.
-/

@[expose] public section

namespace Real

/-- **Conjugate-multiplication factorization** for non-negative reals:
`a - b = (√a - √b) * (√a + √b)`. -/
theorem sub_eq_sqrt_sub_mul_sqrt_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x - y = (√x - √y) * (√x + √y) := by
  have := sq_sqrt hx
  have := sq_sqrt hy
  nlinarith

/-- **Abs form of the conjugate-multiplication factorization** for non-negative reals:
`|a - b| = |√a - √b| * (√a + √b)`. The application-facing API for triangle-inequality and
L¹-distance arguments; the signed form (`sub_eq_sqrt_sub_mul_sqrt_add`) is the algebraic
backbone. -/
theorem abs_sub_eq_abs_sqrt_sub_mul_sqrt_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x - y| = |√x - √y| * (√x + √y) := by
  rw [sub_eq_sqrt_sub_mul_sqrt_add hx hy, abs_mul,
    abs_of_nonneg (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]

/-- **Squared binomial expansion** for non-negative reals:
`(√a - √b)² = a + b - 2 √(a · b)`. -/
theorem sqrt_sub_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (√x - √y) ^ 2 = x + y - 2 * √(x * y) := by
  rw [sub_sq, sq_sqrt hx, sq_sqrt hy, sqrt_mul hx]
  ring

/-- **Squared binomial expansion** for non-negative reals:
`(√a + √b)² = a + b + 2 √(a · b)`. -/
theorem sqrt_add_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (√x + √y) ^ 2 = x + y + 2 * √(x * y) := by
  rw [add_sq, sq_sqrt hx, sq_sqrt hy, sqrt_mul hx]
  ring

/-- For non-negative `a`, `b`: `(√a - √b)² ≤ |a - b|`. AM-GM-style bound on the squared
distance of square roots in terms of the distance of the originals. -/
theorem sqrt_sub_sq_le_abs_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (√x - √y) ^ 2 ≤ |x - y| := by
  have ha_sq : √x ^ 2 = x := sq_sqrt hx
  have hb_sq : √y ^ 2 = y := sq_sqrt hy
  have hsa : 0 ≤ √x := sqrt_nonneg _
  have hsb : 0 ≤ √y := sqrt_nonneg _
  rcases le_total y x with hab | hab
  · rw [abs_of_nonneg (by linarith)]
    have hsqab : √y ≤ √x := sqrt_le_sqrt hab
    nlinarith [ha_sq, hb_sq, hsa, hsb, hsqab]
  · rw [abs_of_nonpos (by linarith)]
    have hsqab : √x ≤ √y := sqrt_le_sqrt hab
    nlinarith [ha_sq, hb_sq, hsa, hsb, hsqab]

end Real
