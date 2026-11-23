/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
public import Mathlib.Data.Rat.Lemmas

/-!
# Legendre's Theorem on rational approximation: the `s/r` form and its sharpness

This file is the general-mathematics home of *Nielsen & Chuang, Quantum Computation and Quantum
Information*, **Theorem 5.1** (used in the continued-fractions step of order finding, §5.3.1):

a rational `s/r` with `|s/r - φ| ≤ 1/(2r²)` is a convergent of the continued fraction of `φ`.

The mathematical content is *Legendre's Theorem* of Diophantine approximation. Mathlib already has
it in the reduced-rational form `Real.exists_convs_eq_rat` (`|ξ - q| < 1 / (2 * q.den ^ 2)` implies
`q` is a convergent). This file records two things Theorem 5.1 additionally needs.

## The `s/r` form (the theorem as stated)

`Real.exists_convs_eq_of_abs_sub_lt` restates Legendre's Theorem in N&C's own `s/r` phrasing: for an
integer numerator `k` and a positive integer denominator `r` (**not** required to be in lowest
terms), an estimate `φ` within `1 / (2 r²)` of `k / r` has `k / r` as a convergent of `φ`. The
reduced denominator of `k / r` divides `r`, hence is `≤ r`, so the `1 / (2 r²)` accuracy is at least
the `1 / (2 · den²)` accuracy Legendre's Theorem requires. This is the form the order-finding and
discrete-logarithm post-processing actually consume.

## Sharpness: the strict `<` cannot be relaxed to `≤`

N&C states the hypothesis with a **non-strict** `≤` (Eq. 5.48), whereas the standard — and
provable — theorem needs the **strict** `<`. The non-strict version is genuinely *false* at the
boundary. The witness is `φ = 1/2` and `s/r = 1`. There `|1/2 - 1| = 1/2 = 1 / (2 · 1²)`, so the
non-strict
hypothesis holds *with equality*, yet the convergents of `1/2` are exactly `{0, 1/2}` (its continued
fraction is `[0; 2]`), so none of them equals `1`. Per obligation 1 (read the source critically; no
silent repair) the literal `≤`-statement is refuted here rather than quietly replaced by the strict
one.

## Main statements

* `Real.exists_convs_eq_of_abs_sub_lt` — **Theorem 5.1 (corrected, strict).** `|φ - k/r| < 1/(2r²)`
  implies `k/r` is a convergent of `φ`, in N&C's `s/r` phrasing with `k : ℤ`, `r : ℕ`, `0 < r`.
* `Real.convergent_one_half_succ` — the positive-index convergents of `1/2` all equal `1/2`.
* `Real.convergent_one_half_ne_one` — no convergent of `1/2` (as `Real.convergent`) equals `1`.
* `Real.convs_one_half_ne_one` — no convergent of `1/2` (as `GenContFract.convs`) equals `1`.
* `Real.not_forall_exists_convs_eq_of_abs_sub_le` — **the `≤`-version of Theorem 5.1 is false**: it
  is *not* the case that `|ξ - q| ≤ 1 / (2 * q.den ^ 2)` forces `q` to be a convergent of `ξ`.

## Scope

The "computable in `O(L³)` operations" clause of Theorem 5.1 is a complexity claim about the
continued-fractions algorithm; the library has no cost model in which to state it, so it is
deliberately out of scope, as for the sibling development in
`ToMathlib.NumberTheory.DiophantineApproximation.DiscreteLogRecovery`.
-/

open GenContFract

public section

namespace Real

/-- **Nielsen & Chuang, Theorem 5.1 (corrected, strict form).** Legendre's Theorem in N&C's `s/r`
phrasing: if a real estimate `φ` approximates the fraction `k / r` to within `1 / (2 r²)`, then
`k / r` occurs as a convergent of the continued fraction of `φ`, so the continued-fractions
algorithm recovers it exactly. Here `k : ℤ`, `r : ℕ`, `0 < r`, and `k / r` need **not** be in lowest
terms.

This specializes the reduced-rational Legendre theorem `Real.exists_convs_eq_rat`: the reduced
denominator of `k / r` divides `r`, hence is `≤ r`, so the `1 / (2 r²)` accuracy of the estimate
implies the `1 / (2 · den²)` accuracy Legendre's Theorem requires.

The hypothesis uses the **strict** `<`; see `Real.not_forall_exists_convs_eq_of_abs_sub_le` for why
the literal non-strict `≤` of N&C (5.48) is false. -/
theorem exists_convs_eq_of_abs_sub_lt {r : ℕ} (hr : 0 < r) (k : ℤ) {φ : ℝ}
    (hφ : |φ - (k : ℝ) / r| < 1 / (2 * (r : ℝ) ^ 2)) :
    ∃ n, (GenContFract.of φ).convs n = ((k : ℚ) / r : ℝ) := by
  set q : ℚ := (k : ℚ) / r with hq
  have hqeq : q = Rat.divInt k (r : ℤ) := by rw [hq, Rat.divInt_eq_div]; push_cast; ring
  have hden : (q.den : ℤ) ∣ (r : ℤ) := by rw [hqeq]; exact Rat.den_dvd k r
  have hdenle : q.den ≤ r := Nat.le_of_dvd hr (by exact_mod_cast hden)
  have hcast : (↑q : ℝ) = (k : ℝ) / r := by rw [hq]; push_cast; ring
  have key : ∃ n, (GenContFract.of φ).convs n = (↑q : ℝ) := by
    apply Real.exists_convs_eq_rat
    rw [hcast]
    refine lt_of_lt_of_le hφ ?_
    have hpos : (0 : ℝ) < 2 * (q.den : ℝ) ^ 2 := by have := q.pos; positivity
    have hle : 2 * (q.den : ℝ) ^ 2 ≤ 2 * (r : ℝ) ^ 2 := by
      have hle' : (q.den : ℝ) ≤ r := by exact_mod_cast hdenle
      nlinarith [hle', (Nat.cast_nonneg q.den : (0 : ℝ) ≤ (q.den : ℝ))]
    exact one_div_le_one_div_of_le hpos hle
  rw [hcast] at key
  exact key

/-- Every positive-index convergent of `1/2` equals `1/2`: the continued fraction of `1/2` is
`[0; 2]`, so `convergent (1/2) (n+1) = ⌊1/2⌋ + (convergent 2 n)⁻¹ = 0 + 2⁻¹ = 1/2`. -/
theorem convergent_one_half_succ (n : ℕ) : Real.convergent (1 / 2 : ℝ) (n + 1) = 1 / 2 := by
  have hfloor : ⌊(1 / 2 : ℝ)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]; constructor <;> norm_num
  have h2 : (Int.fract (1 / 2 : ℝ))⁻¹ = ((2 : ℤ) : ℝ) := by
    rw [Int.fract, hfloor]; norm_num
  rw [Real.convergent_succ, hfloor, h2, Real.convergent_of_int]
  push_cast
  norm_num

/-- No convergent of `1/2` equals `1`: the zeroth is `⌊1/2⌋ = 0` and every later one is `1/2`. -/
theorem convergent_one_half_ne_one (n : ℕ) : Real.convergent (1 / 2 : ℝ) n ≠ 1 := by
  cases n with
  | zero => rw [Real.convergent_zero]; norm_num
  | succ m => rw [convergent_one_half_succ]; norm_num

/-- No convergent of the continued fraction expansion of `1/2` equals `1`. This transports
`Real.convergent_one_half_ne_one` to the `GenContFract.convs` formulation via
`Real.convs_eq_convergent`. -/
theorem convs_one_half_ne_one (n : ℕ) :
    (GenContFract.of (1 / 2 : ℝ)).convs n ≠ ((1 : ℚ) : ℝ) := by
  rw [convs_eq_convergent]
  exact_mod_cast convergent_one_half_ne_one n

/-- **Sharpness of Legendre's Theorem.** The strict inequality in `Real.exists_convs_eq_rat`
cannot be relaxed to `≤`: it is *not* true that every rational `q` with
`|ξ - q| ≤ 1 / (2 * q.den ^ 2)` is a convergent of `ξ`.

This is *Nielsen & Chuang* Theorem 5.1 read literally, with its non-strict hypothesis `≤`. The
witness `ξ = 1/2`, `q = 1` attains the bound with equality (`|1/2 - 1| = 1/2 = 1 / (2 * 1 ^ 2)`)
yet `1` is not a convergent of `1/2` (whose convergents are `{0, 1/2}`). The faithful, correct
statement is the strict form `Real.exists_convs_eq_rat`. -/
theorem not_forall_exists_convs_eq_of_abs_sub_le :
    ¬ ∀ (ξ : ℝ) (q : ℚ), |ξ - (q : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2) →
      ∃ n, (GenContFract.of ξ).convs n = (q : ℝ) := by
  intro H
  obtain ⟨n, hn⟩ := H (1 / 2 : ℝ) 1 (by norm_num)
  exact convs_one_half_ne_one n hn

end Real
