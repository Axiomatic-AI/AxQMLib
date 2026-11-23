/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.BinaryEntropyBit
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Sum

/-!
# An entropy bound on partial sums of binomial coefficients

The number of binary strings of length `n` at Hamming distance at most `r` from a fixed point —
the volume of a Hamming ball of radius `r` — is `∑_{i ≤ r} C(n, i)`. This file proves the classical
bound expressing that volume in terms of the base-`2` binary entropy `Real.binEntropyBit`:

`∑_{i ≤ r} C(n, i) ≤ 2 ^ (n · H₂(r / n))`   whenever   `2 r ≤ n`,

where `H₂ = Real.binEntropyBit`. This is the analytic ingredient behind the sphere-packing and
Gilbert–Varshamov bounds of coding theory (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, §10.4.1 eq. (10.63) and Problem 10.2).

## Main results

* `sum_range_choose_mul_pow_mul_pow_le_one`: for `0 ≤ p ≤ 1/2` and `r ≤ n`,
  `(∑_{i ≤ r} C(n, i)) · p ^ r · (1 - p) ^ (n - r) ≤ 1`. The raw sphere-packing inequality,
  obtained by weighting each ball term by the Bernoulli`(p)` probability and comparing with the
  binomial theorem `∑_{i ≤ n} C(n, i) p ^ i (1 - p) ^ (n - i) = 1`.
* `sum_range_choose_le_rpow_mul_binEntropyBit`: for `2 r ≤ n`,
  `∑_{i ≤ r} C(n, i) ≤ 2 ^ (n · Real.binEntropyBit (r / n))`. The entropy form, obtained from the
  raw inequality by specialising `p = r / n` and rewriting `p ^ (-r) (1 - p) ^ (-(n - r))` as
  `2 ^ (n · H₂(r / n))` via the change-of-base identity `2 ^ (a · logb 2 x) = x ^ a`.

## Implementation notes

The hypothesis `p ≤ 1/2` (equivalently `2 r ≤ n`) is exactly what makes the ball terms dominated:
for `i ≤ r` one has `p ^ r (1 - p) ^ (n - r) ≤ p ^ i (1 - p) ^ (n - i)`, because the common ratio
`p / (1 - p) ≤ 1`.
-/

open Finset

public section

/-- **Sphere-packing inequality** (raw form). For `0 ≤ p ≤ 1/2` and `r ≤ n`, the Hamming-ball
volume `∑_{i ≤ r} C(n, i)`, weighted by `p ^ r (1 - p) ^ (n - r)`, is at most `1`. Each term is
dominated by the corresponding Bernoulli`(p)` weight `C(n, i) p ^ i (1 - p) ^ (n - i)`, and these
sum to `(p + (1 - p)) ^ n = 1` by the binomial theorem. -/
theorem sum_range_choose_mul_pow_mul_pow_le_one {p : ℝ} (hp₀ : 0 ≤ p) (hp : p ≤ 1 / 2)
    {r n : ℕ} (hrn : r ≤ n) :
    (∑ i ∈ range (r + 1), (n.choose i : ℝ)) * p ^ r * (1 - p) ^ (n - r) ≤ 1 := by
  have h1p : (0 : ℝ) ≤ 1 - p := by linarith
  have hple : p ≤ 1 - p := by linarith
  have hsub2 : range (r + 1) ⊆ range (n + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  calc (∑ i ∈ range (r + 1), (n.choose i : ℝ)) * p ^ r * (1 - p) ^ (n - r)
      = ∑ i ∈ range (r + 1), (n.choose i : ℝ) * p ^ r * (1 - p) ^ (n - r) := by
        rw [sum_mul, sum_mul]
    _ ≤ ∑ i ∈ range (r + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) :=
        Finset.sum_le_sum fun i hi => by
          have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hpr : p ^ r = p ^ i * p ^ (r - i) := by
            rw [← pow_add, Nat.add_sub_cancel' hir]
          have hsub : n - i = (n - r) + (r - i) := by omega
          have h1pn : (1 - p) ^ (n - i) = (1 - p) ^ (n - r) * (1 - p) ^ (r - i) := by
            rw [hsub, pow_add]
          have hkey : p ^ (r - i) ≤ (1 - p) ^ (r - i) := pow_le_pow_left₀ hp₀ hple (r - i)
          have hM : (0 : ℝ) ≤ (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - r) :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀ i)) (pow_nonneg h1p (n - r))
          calc (n.choose i : ℝ) * p ^ r * (1 - p) ^ (n - r)
              = ((n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - r)) * p ^ (r - i) := by rw [hpr]; ring
            _ ≤ ((n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - r)) * (1 - p) ^ (r - i) :=
                mul_le_mul_of_nonneg_left hkey hM
            _ = (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) := by rw [h1pn]; ring
    _ ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun i _ _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀ i)) (pow_nonneg h1p (n - i))
    _ = 1 := by
        have h := add_pow p (1 - p) n
        rw [(by ring : p + (1 - p) = 1), one_pow] at h
        calc ∑ i ∈ range (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)
            = ∑ m ∈ range (n + 1), p ^ m * (1 - p) ^ (n - m) * (n.choose m : ℝ) :=
              Finset.sum_congr rfl fun i _ => by ring
          _ = 1 := h.symm

/-- **Entropy bound on the Hamming-ball volume.** For `2 r ≤ n`, the volume of the Hamming ball of
radius `r` in `{0,1}^n` is bounded by `2 ^ (n · H₂(r / n))`, where `H₂ = Real.binEntropyBit` is the
base-`2` binary entropy: `∑_{i ≤ r} C(n, i) ≤ 2 ^ (n · Real.binEntropyBit (r / n))`. This is the
form of the volume bound used in the (classical and quantum) Gilbert–Varshamov bounds. -/
theorem sum_range_choose_le_rpow_mul_binEntropyBit {r n : ℕ} (hrn : 2 * r ≤ n) :
    (∑ i ∈ range (r + 1), (n.choose i : ℝ))
      ≤ (2 : ℝ) ^ ((n : ℝ) * Real.binEntropyBit (r / n)) := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  · subst hr0
    simp [Real.binEntropyBit_zero]
  · have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    set p : ℝ := (r : ℝ) / n with hp_def
    have hp0 : 0 < p := div_pos hrR hnR
    have hp₀ : 0 ≤ p := hp0.le
    have hphalf : p ≤ 1 / 2 := by
      have h2 : (2 : ℝ) * r ≤ n := by exact_mod_cast hrn
      rw [hp_def, div_le_iff₀ hnR]; linarith
    have h1p : 0 < 1 - p := by linarith
    have hrn' : r ≤ n := by omega
    -- The raw sphere-packing inequality, and positivity of the weight `p ^ r (1 - p) ^ (n - r)`.
    have hraw := sum_range_choose_mul_pow_mul_pow_le_one hp₀ hphalf hrn'
    have hABpos : (0 : ℝ) < p ^ r * (1 - p) ^ (n - r) := mul_pos (pow_pos hp0 r) (pow_pos h1p _)
    have hraw' : (∑ i ∈ range (r + 1), (n.choose i : ℝ)) * (p ^ r * (1 - p) ^ (n - r)) ≤ 1 := by
      rw [← mul_assoc]; exact hraw
    -- Coefficient identities `n · p = r` and `n · (1 - p) = n - r`.
    have hnp : (n : ℝ) * p = r := by rw [hp_def]; field_simp
    have hn1p : (n : ℝ) * (1 - p) = (n : ℝ) - r := by rw [mul_sub, mul_one, hnp]
    have hcastsub : ((n - r : ℕ) : ℝ) = (n : ℝ) - r := Nat.cast_sub hrn'
    have hAeq : p ^ r = p ^ (r : ℝ) := (Real.rpow_natCast p r).symm
    have hBeq : (1 - p) ^ (n - r) = (1 - p) ^ ((n : ℝ) - r) := by
      rw [← Real.rpow_natCast (1 - p) (n - r), hcastsub]
    -- Rewrite the entropy exponential as the reciprocal of the weight.
    have hRHS : (2 : ℝ) ^ ((n : ℝ) * Real.binEntropyBit p) = (p ^ r * (1 - p) ^ (n - r))⁻¹ := by
      -- The `logb`-form of `binEntropyBit` (its definitional body is not exposed).
      have hbeb := Real.binEntropyBit_eq_neg_mul_logb p
      have hexp : (n : ℝ) * Real.binEntropyBit p
          = Real.logb 2 p * (-(r : ℝ)) + Real.logb 2 (1 - p) * (-((n : ℝ) - r)) := by
        rw [hbeb]
        have e1 : (n : ℝ) * (p * Real.logb 2 p) = (r : ℝ) * Real.logb 2 p := by
          rw [← mul_assoc, hnp]
        have e2 : (n : ℝ) * ((1 - p) * Real.logb 2 (1 - p))
            = ((n : ℝ) - r) * Real.logb 2 (1 - p) := by rw [← mul_assoc, hn1p]
        rw [mul_sub, mul_neg, e1, e2]; ring
      rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) hp0,
        Real.rpow_logb (by norm_num) (by norm_num) h1p,
        Real.rpow_neg hp₀, Real.rpow_neg h1p.le, ← hAeq, ← hBeq, ← mul_inv]
    -- Conclude `S ≤ 1 / (p ^ r (1 - p) ^ (n - r))` from `S · (…) ≤ 1`.
    rw [hRHS, ← one_div]
    exact (le_div_iff₀ hABpos).mpr hraw'

end
