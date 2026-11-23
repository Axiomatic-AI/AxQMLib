/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# AxQM.Concrete — Shannon entropy of a fair coin and a fair die

The concrete distributions and entropy computations of Nielsen & Chuang Exercise 11.1
("Simple calculations of entropy", p. 501):

Shannon entropy of a fair coin and a fair die, and the effect of making them unfair.

These are pure classical information-theoretic facts about `Real.entropy` (the Shannon entropy of a
finite distribution). The statement of Exercise 11.1 is in `AxQM/NC/Ch11/Exercise11_1.lean`.

## Contents

* `fairCoin` / `fairDie` — the uniform distributions on `Fin 2` / `Fin 6`, together with the basic
  probability facts (nonnegativity and normalisation to `1`).
* `entropy_fairCoin` / `entropy_fairDie` — **the two calculations**, in *nats* (Mathlib's
  `Real.entropy` uses the natural logarithm): `H(fair coin) = log 2` and `H(fair die) = log 6`.
* `entropy_fairCoin_div_log_two` / `entropy_fairDie_div_log_two` — the same values in *bits*
  (dividing by `log 2`, the convention N&C uses): `1` bit for the coin and `log₂ 6 ≈ 2.585` bits
  for the die.
* `entropy_lt_entropy_fairCoin_of_ne_uniform` / `entropy_lt_entropy_fairDie_of_ne_uniform` — the
  **unfair** case: **an unfair coin/die has strictly less entropy than the fair one**, which is how
  the entropy "behaves" when the coin or die is biased. Each is a direct specialisation of the
  general strict **maximum-entropy** fact `Real.entropy_lt_log_card_of_ne_uniform` (any non-uniform
  distribution on a nonempty finite type has entropy strictly below `log (card)`), which — being
  general mathematics — lives in `ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean`
  beside its parents `Real.entropy_le_log_card` and `Real.entropy_eq_log_card_iff`, not here.

## Bits versus nats

Mathlib's `Real.entropy p = ∑ i, (p i).negMulLog = -∑ i, p i · log (p i)` is measured in *nats*
(natural log). N&C measures entropy in *bits* (base-2 log), so the bit value of a distribution `p`
is `Real.entropy p / Real.log 2`. Under this conversion the uniform distribution on `n` outcomes has
bit-entropy `log n / log 2 = Real.logb 2 n`: `Real.logb 2 2 = 1` bit for the fair coin and
`Real.logb 2 6` bits for the fair die, exactly N&C's answers. We record both the nat form (the
Mathlib-native equality) and the bit form (faithful to the textbook's stated numbers).
-/

open scoped BigOperators

namespace AxQM.Concrete

noncomputable section

-- The uniform distributions are written with `Function.const` rather than `fun _ => c`: both denote
-- the same constant function, but `Function.const` keeps the index argument syntactically present.

/-- The **fair-coin** distribution: the uniform probability distribution on the two outcomes
`Fin 2`, each with probability `1/2`. -/
def fairCoin : Fin 2 → ℝ := Function.const _ (2 : ℝ)⁻¹

/-- The **fair-die** distribution: the uniform probability distribution on the six outcomes
`Fin 6`, each with probability `1/6`. -/
def fairDie : Fin 6 → ℝ := Function.const _ (6 : ℝ)⁻¹

/-- Each fair-coin probability is nonnegative. -/
theorem fairCoin_nonneg (i : Fin 2) : 0 ≤ fairCoin i := by
  simp only [fairCoin, Function.const_apply]; positivity

/-- Each fair-die probability is nonnegative. -/
theorem fairDie_nonneg (i : Fin 6) : 0 ≤ fairDie i := by
  simp only [fairDie, Function.const_apply]; positivity

/-- The fair-coin probabilities sum to `1`. -/
theorem fairCoin_sum : ∑ i, fairCoin i = 1 := by
  simp [fairCoin]

/-- The fair-die probabilities sum to `1`. -/
theorem fairDie_sum : ∑ i, fairDie i = 1 := by
  simp [fairDie]

/-- **Entropy of a fair coin (nats).** The Shannon entropy of the fair-coin distribution is
`log 2`. Equivalently (see `entropy_fairCoin_div_log_two`) it is `1` bit — N&C's answer. -/
theorem entropy_fairCoin : Real.entropy fairCoin = Real.log 2 := by
  have h := Real.entropy_uniform (ι := Fin 2)
  simpa [fairCoin, Fintype.card_fin, Function.const_def] using h

/-- **Entropy of a fair die (nats).** The Shannon entropy of the fair-die distribution is `log 6`.
Equivalently (see `entropy_fairDie_div_log_two`) it is `log₂ 6 ≈ 2.585` bits — N&C's answer. -/
theorem entropy_fairDie : Real.entropy fairDie = Real.log 6 := by
  have h := Real.entropy_uniform (ι := Fin 6)
  simpa [fairDie, Fintype.card_fin, Function.const_def] using h

/-- **Entropy of a fair coin (bits).** In the base-2 convention N&C uses (bit-entropy is
`Real.entropy p / Real.log 2`), a fair coin carries exactly `1` bit of entropy. -/
theorem entropy_fairCoin_div_log_two : Real.entropy fairCoin / Real.log 2 = 1 := by
  rw [entropy_fairCoin]
  exact div_self (Real.log_pos (by norm_num)).ne'

/-- **Entropy of a fair die (bits).** In the base-2 convention N&C uses, a fair die carries
`Real.logb 2 6 = log₂ 6 ≈ 2.585` bits of entropy. -/
theorem entropy_fairDie_div_log_two : Real.entropy fairDie / Real.log 2 = Real.logb 2 6 := by
  rw [entropy_fairDie, Real.logb]

/-- **An unfair coin carries strictly less entropy than a fair one.** Any distribution on the two
outcomes `Fin 2` other than `fairCoin` has Shannon entropy strictly below that of the fair coin
(`log 2`, i.e. `1` bit). This is the coin case of N&C's "unfair" discussion; it consumes the general
strict maximum-entropy fact `Real.entropy_lt_log_card_of_ne_uniform`. -/
theorem entropy_lt_entropy_fairCoin_of_ne_uniform {p : Fin 2 → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hne : p ≠ fairCoin) :
    Real.entropy p < Real.entropy fairCoin := by
  rw [entropy_fairCoin]
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  rw [← hcard]
  refine Real.entropy_lt_log_card_of_ne_uniform h0 hsum fun hall => hne ?_
  funext i; rw [hall i]; simp [fairCoin]

/-- **An unfair die carries strictly less entropy than a fair one.** Any distribution on the six
outcomes `Fin 6` other than `fairDie` has Shannon entropy strictly below that of the fair die
(`log 6`, i.e. `log₂ 6` bits). This is the die case of N&C's "unfair" discussion; it consumes the
general strict maximum-entropy fact `Real.entropy_lt_log_card_of_ne_uniform`. -/
theorem entropy_lt_entropy_fairDie_of_ne_uniform {p : Fin 6 → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hne : p ≠ fairDie) :
    Real.entropy p < Real.entropy fairDie := by
  rw [entropy_fairDie]
  have hcard : (Fintype.card (Fin 6) : ℝ) = 6 := by simp
  rw [← hcard]
  refine Real.entropy_lt_log_card_of_ne_uniform h0 hsum fun hall => hne ?_
  funext i; rw [hall i]; simp [fairDie]

end

end AxQM.Concrete
