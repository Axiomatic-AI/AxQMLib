/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.BinaryEntropyBit
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The spike-distribution entropy behind "high fidelity implies low entropy"

Nielsen & Chuang's Lemma 12.19 (*Quantum Computation and Quantum Information*, §12.6.5, p. 594)
states that if a density matrix `ρ` on `2n` qubits has squared fidelity greater than `1 - 2^(-s)`
with a target pure state, then its von Neumann entropy is small:
`S(ρ) < (2n + s + 1 / ln 2) · 2^(-s) + O(2^(-2s))`.  Their proof bounds `S(ρ)` by the entropy of
the worst-case diagonal density matrix `ρ_max`, whose eigenvalue distribution is a **spike**: a
single mass `1 - 2^(-s)` with the residual weight `2^(-s)` spread uniformly over the remaining
`2^(2n) - 1` eigenvalues.  Equation (12.199) writes that entropy (in bits) as

`S(ρ_max) = -(1 - 2^(-s)) · logb 2 (1 - 2^(-s)) - 2^(-s) · logb 2 (2^(-s) / (2^(2n) - 1))`.

This file records that quantity as `Real.spikeEntropyBit` and carries out **Exercise 12.30** —
simplifying (12.199) to the leading-order expression appearing in the Lemma.

## Main declarations

* `Real.spikeEntropyBit s n`: the base-`2` Shannon entropy of the spike distribution, i.e. the
  right-hand side of N&C eq. (12.199).

## Main results

* `Real.spikeEntropyBit_eq_binEntropyBit_add`: the first algebraic step of the simplification,
  splitting `2^(-s) · logb 2 (2^(-s) / (2^(2n) - 1))` so that
  `spikeEntropyBit s n = binEntropyBit (2^(-s)) + 2^(-s) · logb 2 (2^(2n) - 1)`.
* `Real.spikeEntropyBit_lt`: the clean strict bound matching Lemma 12.19's expression,
  `spikeEntropyBit s n < (2n + s + 1 / ln 2) · 2^(-s)` for `0 < s` and `1 ≤ n`.  The overestimate
  `logb 2 (2^(2n) - 1) < 2n` together with the tangent bound `-(1-x) log (1-x) < x` make the
  `O(2^(-2s))` remainder of the textbook statement unnecessary: the inequality holds outright.
* `Real.abs_spikeEntropyBit_sub_le`: the honest asymptotic expansion with an explicit
  `O(2^(-2s))` remainder,
  `|spikeEntropyBit s n - (logb 2 (2^(2n) - 1) + s + 1 / ln 2) · 2^(-s)| ≤ (2^(-s))^2 / ln 2`.
  Here the leading coefficient is the *exact* `logb 2 (2^(2n) - 1)`, not `2n`: replacing it by `2n`
  would introduce an `O(2^(-s))` error, so `2n` is genuinely an upper bound (as used in
  `spikeEntropyBit_lt`) rather than the leading term of a `2^(-2s)`-accurate expansion.

## Implementation notes

`2^(-s)` is `(2 : ℝ) ^ (-s)` via `Real.rpow`, while `2^(2n)` is `(2 : ℝ) ^ (2 * n)` via the
monoid power.  The proofs pass through the natural logarithm: `spikeEntropyBit` is `ln 2` times a
combination of `Real.log` terms (`spikeEntropyBit_mul_log_two`), and the analytic core is the pair
of tangent-line bounds `x - x^2 ≤ -(1-x) log (1-x) < x` for `x ∈ (0,1)`.
-/

open Real

@[expose] public section

namespace Real

variable (s : ℝ) (n : ℕ)

/-- The base-`2` Shannon entropy of the **spike distribution** from the proof of Nielsen & Chuang's
Lemma 12.19: a peak of probability `1 - 2^(-s)` on one outcome, with the residual mass `2^(-s)`
spread uniformly over the other `2^(2n) - 1` outcomes.  This is the right-hand side of N&C eq.
(12.199). -/
noncomputable def spikeEntropyBit : ℝ :=
  -(1 - (2 : ℝ) ^ (-s)) * Real.logb 2 (1 - (2 : ℝ) ^ (-s))
    - (2 : ℝ) ^ (-s) * Real.logb 2 ((2 : ℝ) ^ (-s) / ((2 : ℝ) ^ (2 * n) - 1))

/-- Tangent-line bounds for `-(1-x) log (1-x)` near `x = 0`, the analytic core of the spike-entropy
estimate: for `x ∈ (0,1)`, `x - x^2 ≤ -(1-x) log (1-x) < x`.  The upper bound comes from
`t log t > t - 1` (with `t = 1-x ≠ 1`), the lower bound from `log (1-x) ≤ -x`. -/
private lemma neg_one_sub_mul_log_bounds {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x - x ^ 2 ≤ -(1 - x) * Real.log (1 - x) ∧ -(1 - x) * Real.log (1 - x) < x := by
  have h1mx : (0 : ℝ) < 1 - x := by linarith
  refine ⟨?_, ?_⟩
  · have hle : Real.log (1 - x) ≤ -x := by
      have := Real.log_le_sub_one_of_pos h1mx; linarith
    nlinarith [hle, h1mx]
  · have hne : (1 - x)⁻¹ ≠ 1 := by rw [ne_eq, inv_eq_one]; intro h; linarith
    have hl := Real.log_lt_sub_one_of_pos (inv_pos.mpr h1mx) hne
    rw [Real.log_inv] at hl
    have hmul := mul_lt_mul_of_pos_left hl h1mx
    rw [mul_sub, mul_inv_cancel₀ h1mx.ne', mul_one] at hmul
    nlinarith [hmul]

/-- The first step of the simplification of N&C eq. (12.199): expanding
`logb 2 (2^(-s) / (2^(2n) - 1))` exhibits the spike entropy as Mathlib's binary entropy in bits at
`2^(-s)` plus a tail term, `spikeEntropyBit s n = binEntropyBit (2^(-s)) + 2^(-s) · logb 2
(2^(2n) - 1)`.  Requires `1 ≤ n` so that `2^(2n) - 1 ≠ 0`. -/
theorem spikeEntropyBit_eq_binEntropyBit_add (hn : 1 ≤ n) :
    spikeEntropyBit s n
      = Real.binEntropyBit ((2 : ℝ) ^ (-s))
        + (2 : ℝ) ^ (-s) * Real.logb 2 ((2 : ℝ) ^ (2 * n) - 1) := by
  have hx0 : (0 : ℝ) < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
  have hM0 : (0 : ℝ) < (2 : ℝ) ^ (2 * n) - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ (2 * n) := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  simp only [spikeEntropyBit]
  rw [Real.binEntropyBit_eq_neg_mul_logb, Real.logb_div hx0.ne' hM0.ne']
  ring

/-- The spike entropy scaled by `ln 2`, written entirely with natural logarithms — the identity
underlying the estimates below.  Concretely, `spikeEntropyBit s n · ln 2` equals
`-(1 - 2^(-s)) log(1 - 2^(-s)) + s · ln 2 · 2^(-s) + 2^(-s) log(2^(2n) - 1)`,
using `log (2^(-s)) = -s · ln 2`. -/
theorem spikeEntropyBit_mul_log_two (hn : 1 ≤ n) :
    spikeEntropyBit s n * Real.log 2
      = -(1 - (2 : ℝ) ^ (-s)) * Real.log (1 - (2 : ℝ) ^ (-s))
        + s * Real.log 2 * (2 : ℝ) ^ (-s)
        + (2 : ℝ) ^ (-s) * Real.log ((2 : ℝ) ^ (2 * n) - 1) := by
  have hx0 : (0 : ℝ) < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
  have hM0 : (0 : ℝ) < (2 : ℝ) ^ (2 * n) - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ (2 * n) := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp only [spikeEntropyBit, Real.logb]
  rw [Real.log_div hx0.ne' hM0.ne', Real.log_rpow (show (0 : ℝ) < 2 by norm_num)]
  field_simp
  ring

/-- **Exercise 12.30 (the bound of Lemma 12.19).**  Simplifying N&C eq. (12.199) yields the strict
inequality `spikeEntropyBit s n < (2n + s + 1 / ln 2) · 2^(-s)` for `0 < s` and `1 ≤ n` — exactly
the expression stated in Lemma 12.19.  Both simplifying steps go strictly in the direction of the
bound (`logb 2 (2^(2n) - 1) < 2n`, and `-(1-x) log (1-x) < x`), so the textbook's `O(2^(-2s))`
slack is not needed here; see `abs_spikeEntropyBit_sub_le` for the corresponding two-sided
asymptotic. -/
theorem spikeEntropyBit_lt (hs : 0 < s) (hn : 1 ≤ n) :
    spikeEntropyBit s n < (2 * n + s + 1 / Real.log 2) * (2 : ℝ) ^ (-s) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : (0 : ℝ) < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
  have hx1 : (2 : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hM0 : (0 : ℝ) < (2 : ℝ) ^ (2 * n) - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ (2 * n) := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hMlt : Real.log ((2 : ℝ) ^ (2 * n) - 1) < 2 * n * Real.log 2 := by
    have h1 : Real.log ((2 : ℝ) ^ (2 * n) - 1) < Real.log ((2 : ℝ) ^ (2 * n)) :=
      Real.log_lt_log hM0 (by linarith)
    rw [Real.log_pow] at h1; push_cast at h1; linarith
  have hb2 : -(1 - (2 : ℝ) ^ (-s)) * Real.log (1 - (2 : ℝ) ^ (-s)) < (2 : ℝ) ^ (-s) :=
    (neg_one_sub_mul_log_bounds hx0 hx1).2
  have key : spikeEntropyBit s n * Real.log 2
      < (2 * n + s + 1 / Real.log 2) * (2 : ℝ) ^ (-s) * Real.log 2 := by
    rw [spikeEntropyBit_mul_log_two s n hn]
    have hRHS : (2 * n + s + 1 / Real.log 2) * (2 : ℝ) ^ (-s) * Real.log 2
        = 2 * n * (2 : ℝ) ^ (-s) * Real.log 2 + s * Real.log 2 * (2 : ℝ) ^ (-s)
          + (2 : ℝ) ^ (-s) := by
      field_simp
    rw [hRHS]
    nlinarith [hb2, mul_lt_mul_of_pos_left hMlt hx0, hx0]
  exact lt_of_mul_lt_mul_right key hlog2.le

/-- **Exercise 12.30 (the asymptotic expansion).**  The honest leading-order form of N&C eq.
(12.199): the spike entropy differs from `(logb 2 (2^(2n) - 1) + s + 1 / ln 2) · 2^(-s)` by an
explicit `O(2^(-2s))` term, `|spikeEntropyBit s n - (logb 2 (2^(2n) - 1) + s + 1 / ln 2) · 2^(-s)|
≤ (2^(-s))^2 / ln 2`.  The leading coefficient is the exact `logb 2 (2^(2n) - 1)`; replacing it by
`2n` (as in the Lemma's stated expression) is an *upper* estimate that costs an `O(2^(-s))` error,
which is why `spikeEntropyBit_lt` phrases `2n` as a bound rather than an asymptotic term. -/
theorem abs_spikeEntropyBit_sub_le (hs : 0 < s) (hn : 1 ≤ n) :
    |spikeEntropyBit s n
        - (Real.logb 2 ((2 : ℝ) ^ (2 * n) - 1) + s + 1 / Real.log 2) * (2 : ℝ) ^ (-s)|
      ≤ ((2 : ℝ) ^ (-s)) ^ 2 / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : (0 : ℝ) < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
  have hx1 : (2 : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbds := neg_one_sub_mul_log_bounds hx0 hx1
  have hnum : |-(1 - (2 : ℝ) ^ (-s)) * Real.log (1 - (2 : ℝ) ^ (-s)) - (2 : ℝ) ^ (-s)|
      ≤ ((2 : ℝ) ^ (-s)) ^ 2 := by
    rw [abs_le]
    exact ⟨by nlinarith [hbds.1], by nlinarith [hbds.2, sq_nonneg ((2 : ℝ) ^ (-s))]⟩
  have hrel : spikeEntropyBit s n
        - (Real.logb 2 ((2 : ℝ) ^ (2 * n) - 1) + s + 1 / Real.log 2) * (2 : ℝ) ^ (-s)
      = (-(1 - (2 : ℝ) ^ (-s)) * Real.log (1 - (2 : ℝ) ^ (-s)) - (2 : ℝ) ^ (-s)) / Real.log 2 := by
    rw [eq_div_iff hlog2.ne', sub_mul, spikeEntropyBit_mul_log_two s n hn]
    simp only [Real.logb]
    field_simp
    ring
  rw [hrel, abs_div, abs_of_pos hlog2, div_le_div_iff_of_pos_right hlog2]
  exact hnum

end Real
