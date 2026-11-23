/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exponential decay of `Real.exp (n · c)` for negative `c`

A small `SpecificLimits` companion.  For a fixed negative rate `c < 0`, the sequence
`Real.exp (n · c)` — geometric in `n` with ratio `Real.exp c ∈ [0, 1)` — tends to `0` as
`n → ∞` over `ℕ`.

This is the elementary exponential-decay estimate that a coding argument reuses whenever a rate
below a threshold makes an exponential term vanish (e.g. the confusion / typical-defect terms of the
Holevo–Schumacher–Westmoreland theorem, Nielsen & Chuang, Theorem 12.8, Box 12.5, whose per-block
error bounds carry factors `exp (−n · β)` with `β > 0`).

## Main results

- `Real.tendsto_exp_nat_mul_atTop_nhds_zero`: `Real.exp (n · c) → 0` for `c < 0`.
-/

@[expose] public section

open Filter Topology

namespace Real

/-- **Exponential decay** `Real.exp (n · c) → 0` as `n → ∞` over `ℕ`, for any negative rate `c < 0`.
Since `Real.exp (n · c) = (Real.exp c) ^ n` (`Real.exp_natCast_mul`) with base
`Real.exp c ∈ [0, 1)` (positive, and `< 1` iff `c < 0` via `Real.exp_lt_one_iff`), this is the
geometric limit `tendsto_pow_atTop_nhds_zero_of_lt_one`. -/
theorem tendsto_exp_nat_mul_atTop_nhds_zero {c : ℝ} (hc : c < 0) :
    Tendsto (fun n : ℕ => Real.exp (n * c)) atTop (𝓝 0) := by
  simp only [Real.exp_natCast_mul]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr hc)

end Real
