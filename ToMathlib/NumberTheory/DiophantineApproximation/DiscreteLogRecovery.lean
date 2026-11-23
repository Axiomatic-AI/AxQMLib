/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.NumberTheory.DiophantineApproximation.LegendreSharp
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.Rat.Lemmas

/-!
# The generalized continued-fractions algorithm for the discrete logarithm

This file formalises the classical post-processing step of the quantum discrete-logarithm algorithm
(*Nielsen & Chuang, Quantum Computation and Quantum Information*, §5.4.2, p. 239, Exercise 5.24).

## Setup

In the discrete-logarithm algorithm one wants the least positive `s` with `aˢ = b` for elements of
order `r` (known from order finding). The quantum part outputs, from a single query,
estimates of the two phases `s·ℓ₂ / r` and `ℓ₂ / r` for some `ℓ₂` (from the first two registers,
step 5). A phase register holds a *fractional* value, so the estimates approximate the fractional
residues `((s·ℓ₂) mod r)/r` and `(ℓ₂ mod r)/r`. Step 6 recovers `s` from these two estimates
and the known `r`; the textbook leaves the construction as this exercise.

The construction generalizes the single continued-fractions step of order finding (§5.3.1,
Theorem 5.1 / Legendre's theorem) to *two* estimates:

1. Run the continued-fractions algorithm on each estimate. By Legendre's theorem in its `s/r` form
   (`Real.exists_convs_eq_of_abs_sub_lt`, N&C Theorem 5.1), an estimate `φ` within `1/(2r²)` of the
   exact fraction `k/r` has `k/r` occurring as a convergent — the algorithm recovers the exact
   rational.
2. Knowing `r`, read the integer numerator `k` off the recovered fraction `k/r`
   (`recoverNumerator`, `recoverNumerator_eq`): here `k = (s·ℓ₂) mod r` and `k = ℓ₂ mod r`
   respectively.
3. Combine the two residues by modular division: `s ≡ (s·ℓ₂) · ℓ₂⁻¹ (mod r)`
   (`discreteLogRecover`, `discreteLogRecover_eq`), which determines `s` uniquely in `[0, r)`
   (`discreteLogRecover_val`).

Step 3 requires `ℓ₂` to be invertible modulo `r`, i.e. `IsCoprime ℓ₂ r`. This is intrinsic to the
problem: if `gcd(ℓ₂, r) > 1` the two residues `(s·ℓ₂) mod r` and `ℓ₂ mod r` only determine `s`
modulo `r / gcd(ℓ₂, r)`, so `s` is genuinely *not* recoverable from them alone (this is why the
quantum algorithm succeeds only with probability `O(1)`, over the random `ℓ₂`). The hypothesis is a
faithful requirement of the construction, not a convenience weakening.

## Main declarations

* `recoverNumerator` / `recoverNumerator_eq` — read the numerator `k` of `k/r`, given `r`.
* `discreteLogRecover` / `discreteLogRecover_eq` — recover `s` in `ZMod r` from the two exact
  fractions by modular division.
* `discreteLogRecover_val` — the recovered value in `[0, r)` is exactly `s` when `0 ≤ s < r`.
* `discreteLog_of_estimates` — the end-to-end correctness of the algorithm: from the two estimates,
  continued fractions recovers both fractions and the modular combination returns `s`.

## Scope

The `O(⌈log r⌉²)` operation-count clause of the exercise is a complexity claim; the library has no
cost model in which to state it, so — as for Theorem 5.1 — it is deliberately out of scope. What is
captured is the mathematical correctness of the recovery procedure.
-/

open GenContFract

public section

namespace DiscreteLogRecovery

/-- Recover the integer numerator `k` of a fraction `q = k / r` from `q` and a known
denominator multiple `r`. Since `q * r = k`, the numerator is `(q * r).num`. -/
def recoverNumerator (q : ℚ) (r : ℕ) : ℤ := (q * r).num

/-- `recoverNumerator` reads back the numerator of `k / r` exactly (for `r ≠ 0`): the fraction
`k / r` need not be in lowest terms, but multiplying by the known `r` cancels the denominator. -/
theorem recoverNumerator_eq (k : ℤ) {r : ℕ} (hr : r ≠ 0) :
    recoverNumerator ((k : ℚ) / r) r = k := by
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr
  unfold recoverNumerator
  rw [div_mul_cancel₀ (k : ℚ) hr', Rat.num_intCast]

/-- The generalized continued-fractions recovery of the discrete logarithm. Given two convergents
`q₁ ≈ (s·ℓ₂) / r` and `q₂ ≈ ℓ₂ / r` from continued fractions, and the known order `r`, return
`s` as an element of `ZMod r` by reading off the numerators and dividing modulo `r`. -/
def discreteLogRecover (q₁ q₂ : ℚ) (r : ℕ) : ZMod r :=
  (recoverNumerator q₁ r : ZMod r) * (recoverNumerator q₂ r : ZMod r)⁻¹

/-- Correctness of the modular-division step: from the exact fractions `((s·ℓ) mod r) / r` and
`(ℓ mod r) / r`, `discreteLogRecover` returns `s` in `ZMod r`, provided `ℓ` is coprime to `r` (so
`ℓ` is invertible modulo `r`). -/
theorem discreteLogRecover_eq {r : ℕ} (hr : r ≠ 0) (s ℓ : ℤ) (hcop : IsCoprime ℓ (r : ℤ)) :
    discreteLogRecover (((s * ℓ) % r : ℤ) / r) ((ℓ % r : ℤ) / r) r = (s : ZMod r) := by
  unfold discreteLogRecover
  rw [recoverNumerator_eq _ hr, recoverNumerator_eq _ hr, ZMod.intCast_mod, ZMod.intCast_mod,
    Int.cast_mul, mul_assoc, mul_comm ((ℓ : ℤ) : ZMod r) (((ℓ : ℤ) : ZMod r)⁻¹),
    ZMod.intCast_inv_mul_eq_one hcop, mul_one]

/-- The recovered value determines `s` as a concrete integer in `[0, r)`: when `0 ≤ s < r`, the
`ZMod r` output of `discreteLogRecover` has canonical representative equal to `s`. -/
theorem discreteLogRecover_val {r : ℕ} (s ℓ : ℤ) (hs0 : 0 ≤ s) (hsr : s < r)
    (hcop : IsCoprime ℓ (r : ℤ)) :
    ((discreteLogRecover (((s * ℓ) % r : ℤ) / r) ((ℓ % r : ℤ) / r) r).val : ℤ) = s := by
  have hrpos : 0 < r := by exact_mod_cast lt_of_le_of_lt hs0 hsr
  have : NeZero r := ⟨hrpos.ne'⟩
  rw [discreteLogRecover_eq hrpos.ne' s ℓ hcop, ZMod.val_intCast]
  exact Int.emod_eq_of_lt hs0 hsr

/-- End-to-end correctness of the generalized continued-fractions algorithm (steps 4–6 of N&C's
discrete-logarithm algorithm). Given estimates `φ₁ ≈ (s·ℓ₂) / r` and `φ₂ ≈ ℓ₂ / r` each accurate to
`1 / (2 r²)`, with `ℓ₂` coprime to `r` and `0 ≤ s < r`: continued fractions recovers
both exact fractions as convergents, and the combination `discreteLogRecover` returns `s`. -/
theorem discreteLog_of_estimates {r : ℕ} (s ℓ : ℤ) (hs0 : 0 ≤ s) (hsr : s < r)
    (hcop : IsCoprime ℓ (r : ℤ)) {φ₁ φ₂ : ℝ}
    (h₁ : |φ₁ - ((s * ℓ) % r : ℤ) / (r : ℝ)| < 1 / (2 * (r : ℝ) ^ 2))
    (h₂ : |φ₂ - (ℓ % r : ℤ) / (r : ℝ)| < 1 / (2 * (r : ℝ) ^ 2)) :
    ∃ n₁ n₂ : ℕ,
      (GenContFract.of φ₁).convs n₁ = (((s * ℓ) % r : ℤ) / r : ℝ) ∧
      (GenContFract.of φ₂).convs n₂ = ((ℓ % r : ℤ) / r : ℝ) ∧
      ((discreteLogRecover (((s * ℓ) % r : ℤ) / r) ((ℓ % r : ℤ) / r) r).val : ℤ) = s := by
  have hrpos : 0 < r := by exact_mod_cast lt_of_le_of_lt hs0 hsr
  obtain ⟨n₁, hn₁⟩ := Real.exists_convs_eq_of_abs_sub_lt hrpos ((s * ℓ) % r) h₁
  obtain ⟨n₂, hn₂⟩ := Real.exists_convs_eq_of_abs_sub_lt hrpos (ℓ % r) h₂
  exact ⟨n₁, n₂, hn₁, hn₂, discreteLogRecover_val s ℓ hs0 hsr hcop⟩

end DiscreteLogRecovery
