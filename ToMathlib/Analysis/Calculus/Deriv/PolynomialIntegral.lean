/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Rodrigues-type integration by parts for polynomials

Two reusable facts behind Rodrigues-formula arguments (e.g. associated Legendre functions, the
electric-dipole selection rules):

* `Polynomial.eval_iterate_derivative_eq_zero_of_dvd`: the low-order iterated derivatives of a
  polynomial divisible by `(X - C a) ^ r` vanish at `a`.
* `Polynomial.integral_iterate_derivative_mul`: on a real interval `[a, b]`, all `n` derivatives of
  `derivative^[n] u` may be moved onto a cofactor `S` at the cost of the sign `(-1) ^ n`, provided
  every boundary product `(derivative^[i] u) · (derivative^[j] S)` with `i + j + 1 = n` vanishes at
  both endpoints.
-/

public section

open scoped Polynomial

namespace Polynomial

/-- Low-order iterated derivatives of a polynomial divisible by `(X - C a) ^ r` vanish at `a`:
if `(X - C a) ^ r ∣ p` then `(derivative^[j] p).eval a = 0` for every `j < r`. -/
theorem eval_iterate_derivative_eq_zero_of_dvd {R : Type*} [CommRing R]
    {p : R[X]} {a : R} {r j : ℕ} (hdvd : (X - C a) ^ r ∣ p) (hj : j < r) :
    (derivative^[j] p).eval a = 0 := by
  rcases eq_or_ne p 0 with hp | hp
  · simp [hp]
  · have hle : r ≤ rootMultiplicity a p := (le_rootMultiplicity_iff hp).2 hdvd
    exact isRoot_iterate_derivative_of_lt_rootMultiplicity (lt_of_lt_of_le hj hle)

/-- **Rodrigues integration by parts on a real interval.** If every boundary product
`(derivative^[i] u)(x) · (derivative^[j] S)(x)` with `i + j + 1 = n` vanishes at `x = a` and
`x = b`, then all `n` derivatives can be moved off `derivative^[n] u` onto `S` at the cost of the
sign `(-1) ^ n`, with no surviving boundary terms. -/
theorem integral_iterate_derivative_mul {a b : ℝ} (n : ℕ) (u S : ℝ[X])
    (hb : ∀ i j, i + j + 1 = n →
      (derivative^[i] u).eval b * (derivative^[j] S).eval b = 0)
    (ha : ∀ i j, i + j + 1 = n →
      (derivative^[i] u).eval a * (derivative^[j] S).eval a = 0) :
    (∫ x in a..b, (derivative^[n] u).eval x * S.eval x)
      = (-1) ^ n * ∫ x in a..b, u.eval x * (derivative^[n] S).eval x := by
  induction n generalizing S with
  | zero => simp
  | succ n ih =>
    have hstep : (∫ x in a..b, (derivative^[n + 1] u).eval x * S.eval x)
        = -∫ x in a..b, (derivative^[n] u).eval x * (derivative S).eval x := by
      have hV : ∀ x ∈ Set.uIcc a b,
          HasDerivAt (fun y => eval y (derivative^[n] u)) (eval x (derivative^[n + 1] u)) x := by
        intro x _
        have h := (derivative^[n] u).hasDerivAt x
        rwa [← Function.iterate_succ_apply' derivative n u] at h
      have hU : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => eval y S) (eval x (derivative S)) x :=
        fun x _ => S.hasDerivAt x
      have hUi : IntervalIntegrable (fun x => eval x (derivative S)) MeasureTheory.volume a b :=
        ((derivative S).continuous).intervalIntegrable _ _
      have hVi : IntervalIntegrable (fun x => eval x (derivative^[n + 1] u))
          MeasureTheory.volume a b := ((derivative^[n + 1] u).continuous).intervalIntegrable _ _
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU hV hUi hVi
      have hbb : eval b S * eval b (derivative^[n] u) = 0 := by
        have := hb n 0 (by omega); simpa [mul_comm] using this
      have haa : eval a S * eval a (derivative^[n] u) = 0 := by
        have := ha n 0 (by omega); simpa [mul_comm] using this
      rw [hbb, haa, sub_zero, zero_sub] at hibp
      rw [show (∫ x in a..b, (derivative^[n + 1] u).eval x * S.eval x)
            = ∫ x in a..b, S.eval x * (derivative^[n + 1] u).eval x from by
          apply intervalIntegral.integral_congr; intro x _; ring]
      rw [hibp,
        show (∫ x in a..b, (derivative S).eval x * (derivative^[n] u).eval x)
            = ∫ x in a..b, (derivative^[n] u).eval x * (derivative S).eval x from by
          apply intervalIntegral.integral_congr; intro x _; ring]
    rw [hstep, ih (derivative S) ?_ ?_]
    · rw [← Function.iterate_succ_apply derivative n S]; ring
    · intro i j hij
      have := hb i (j + 1) (by omega)
      rwa [Function.iterate_succ_apply derivative j S] at this
    · intro i j hij
      have := ha i (j + 1) (by omega)
      rwa [Function.iterate_succ_apply derivative j S] at this

end Polynomial
