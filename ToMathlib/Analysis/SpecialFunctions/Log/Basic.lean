/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Gibbs-style pointwise log bounds

Pointwise bounds and identities on `Real.log` underlying the classical Gibbs/Klein inequality
(entropy ≤ cross-entropy).
-/

@[expose] public section

noncomputable section

namespace Real

/-- **Gibbs-style pointwise bound**: `p * log (q / p) ≤ q - p` for `0 ≤ p`, `0 < q`. Underlying
real-analysis fact for classical Klein/Gibbs inequality (entropy ≤ cross-entropy) via
summation. Proof: `log_le_sub_one_of_pos` on `q / p`, multiplied by `p`; the `p = 0` case
collapses to `0 ≤ q`. -/
lemma mul_log_div_le_sub_of_nonneg {p q : ℝ} (hp_nn : 0 ≤ p) (hq_pos : 0 < q) :
    p * log (q / p) ≤ q - p := by
  obtain rfl | hp_pos := hp_nn.eq_or_lt
  · simpa using hq_pos.le
  · calc p * log (q / p)
        ≤ p * (q / p - 1) :=
          mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hq_pos hp_pos)) hp_pos.le
      _ = q - p := by field_simp

/-- **Log-quotient identity for nonneg numerator**: `p * log (q / p) = p * log q - p * log p`
for `0 ≤ p`, `0 < q`. The `p = 0` case uses junk-zero (`Real.log 0 = 0`, `0 * _ = 0`); the
`p > 0` case is `Real.log_div`. Bridges KL-divergence form to entropy/cross-entropy form. -/
lemma mul_log_div {p q : ℝ} (hp_nn : 0 ≤ p) (hq_pos : 0 < q) :
    p * log (q / p) = p * log q - p * log p := by
  obtain rfl | hp_pos := hp_nn.eq_or_lt
  · simp
  · rw [log_div hq_pos.ne' hp_pos.ne', mul_sub]

/-- **Strict Gibbs-style pointwise bound**: `p * log (q / p) < q - p` for `0 ≤ p`, `0 < q`
whenever `p ≠ q`. The strict/equality companion to `Real.mul_log_div_le_sub_of_nonneg`: the
tangent bound `log x ≤ x - 1` is strict off `x = 1` (`Real.log_lt_sub_one_of_pos`), so the
pointwise Gibbs bound is strict unless `p = q` (with the `p = 0` case reducing to `0 < q`). This
is the per-term input to the equality condition of the classical Gibbs/Klein inequality
(`Real.relativeEntropy_eq_zero_iff`, Nielsen–Chuang Theorem 11.1). -/
lemma mul_log_div_lt_sub_of_ne {p q : ℝ} (hp_nn : 0 ≤ p) (hq_pos : 0 < q) (hpq : p ≠ q) :
    p * log (q / p) < q - p := by
  obtain rfl | hp_pos := hp_nn.eq_or_lt
  · simpa using hq_pos
  · have hne : q / p ≠ 1 := by
      intro hh
      rw [div_eq_one_iff_eq hp_pos.ne'] at hh
      exact hpq hh.symm
    calc p * log (q / p)
        < p * (q / p - 1) :=
          mul_lt_mul_of_pos_left (log_lt_sub_one_of_pos (div_pos hq_pos hp_pos) hne) hp_pos
      _ = q - p := by field_simp

end Real
