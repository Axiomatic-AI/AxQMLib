/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.FairCoinDieEntropy

/-!
# N&C Exercise 11.1 — simple calculations of Shannon entropy (fair coin, fair die, unfair cases)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.1, p. 501.

Compute Shannon entropy for a fair coin, a fair die, and discuss unfair cases.

Here `H(X) = -∑ₓ p(x) log₂ p(x)` is the Shannon entropy (N&C measures it in *bits*, i.e. base-2
log). A fair coin is the uniform distribution on two outcomes, a fair die the uniform distribution
on six; the exercise asks for their entropies and how a bias would change them.

## What is proved

Each of the three parts is a precise, provable proposition:

* the entropy of a fair coin is a definite number (`1` bit);
* the entropy of a fair die is a definite number (`log₂ 6` bits);
* "how the entropy behaves if the coin/die is unfair" has a precise answer — it strictly
  *decreases*, because the uniform (fair) distribution is the unique entropy maximiser.

The content is *classical* information theory: it quantifies over real-valued distributions and
`Real.entropy`.

## Where the formalisation lives

The concrete instances are in `AxQM/Concrete/FairCoinDieEntropy.lean`, namespace
`AxQM.Concrete`:

* `fairCoin` / `fairDie` — the uniform distributions on `Fin 2` / `Fin 6` (with `fairCoin_nonneg`,
  `fairCoin_sum`, `fairDie_nonneg`, `fairDie_sum` recording that they are probability
  distributions).
* `entropy_fairCoin : Real.entropy fairCoin = Real.log 2` — **the fair-coin calculation** in nats;
  and `entropy_fairCoin_div_log_two : Real.entropy fairCoin / Real.log 2 = 1` — the same value in
  bits, i.e. N&C's answer of `1` bit.
* `entropy_fairDie : Real.entropy fairDie = Real.log 6` — **the fair-die calculation** in nats; and
  `entropy_fairDie_div_log_two : Real.entropy fairDie / Real.log 2 = Real.logb 2 6` — the same value
  in bits, i.e. N&C's answer of `log₂ 6 ≈ 2.585` bits.
* `entropy_lt_entropy_fairCoin_of_ne_uniform` / `entropy_lt_entropy_fairDie_of_ne_uniform` — **the
  "unfair" answer, specialised**: an unfair coin/die has strictly less entropy than the fair one.

The **general** strict maximum-entropy fact these specialise — on a nonempty finite type any
distribution other than the uniform one has entropy strictly below `log (card)`, the value the
uniform distribution attains — is in `ToMathlib/`
beside its parents `Real.entropy_le_log_card` / `Real.entropy_eq_log_card_iff`:

* `Real.entropy_lt_log_card_of_ne_uniform` — **the "unfair" answer, general form**: the
  maximum-entropy principle in strict form (in
  `ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean`).

## Faithfulness note

Mathlib's `Real.entropy` is measured in nats (natural log), whereas N&C uses bits (base-2 log), so
the two `_div_log_two` theorems convert to bits by dividing by `log 2`; both the nat form (the
Mathlib-native equality) and the bit form (matching the textbook's stated numbers) are recorded, so
the calculations are reported in exactly N&C's units without weakening. The unfair case is stated at
full strength — a *strict* decrease for *every* non-uniform distribution — rather than as a mere
inequality or an illustrative example, which is the exercise's actual claim (that fairness uniquely
maximises the entropy).
-/
