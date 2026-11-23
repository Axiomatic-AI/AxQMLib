/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.BinaryEntropyQuadraticBound
import ToMathlib.Combinatorics.Enumerative.PowersetCardInter
import ToMathlib.InformationTheory.RandomSamplingErrorBound

/-!
# Nielsen & Chuang, Exercise 12.27 (random sampling tests)

*(N&C p. 589.)*

Random sampling tests: bound error prob on untested bits < exp(-O(eps^2 n)).

The claim is a hypergeometric large-deviation
inequality: for a *fixed* error set `E` of `M = μ n` bits among `2 n`, a uniformly random `n`-subset
`C` (the check bits) meets `E` in `|C ∩ E|` places, and the probability that this is small decays
exponentially. It is a statement about combinatorics and analysis, the mathematical content Alice
and Bob invoke, not about states or measurements.

## The formalisation

The formalisation is in `ToMathlib/`. The probability is modelled without measure theory, as the
`Finset`-counting ratio `p = #{C ∈ S.powersetCard n | (C ∩ E).card < s} / (2 n).choose n` (uniform
over `n`-subsets of the `2 n` bits). N&C's `δ = (μ - ε) / 2` normalisation appears as the deficit
hypothesis `ε n ≤ M - 2 (s - 1)` (which the physical parametrisation `M = μ n`, `s = δ n` satisfies,
with room `+2` to spare); the headline `exp[-O(ε² n)]` is rendered as the explicit, non-asymptotic
`(2 n + 1) · 2 ^ (-ε² n / 4)` (a strictly stronger, unweakened statement — the polynomial prefactor
is absorbed into the `O(·)` for large `n`).

**Step (3) — the quadratic entropy bound** (`Mathlib/Analysis/SpecialFunctions/`
`BinaryEntropyQuadraticBound.lean`), the osculating parabola at the entropy maximum:

* `Real.binEntropy_le_log_two_mul_one_sub_two_mul_sq` — `binEntropy x ≤ log 2 · (1 - 2 (x - ½)²)`.
* `Real.binEntropyBit_le_one_sub_two_mul_sq` — the bits form `H₂ x ≤ 1 - 2 (x - ½)²` on `[0, 1]`.

**Step (1) — the combinatorial core**
(`ToMathlib/Combinatorics/Enumerative/PowersetCardInter.lean`),
the hypergeometric left-tail count:

* `Finset.card_powerset_filter_card_lt` — `#{A ⊆ E | A.card < s} = ∑_{j < s} (E.card).choose j`.
* `Finset.card_powersetCard_filter_inter_lt_le` — `#{C ∈ S.powersetCard n | (C ∩ E).card < s} ≤`
  `(∑_{j < s} (E.card).choose j) · 2 ^ (S \ E).card`, via the injection `C ↦ (C ∩ E, C \ E)`.

**Steps (2)–(3) — the analytic assembly**
(`ToMathlib/InformationTheory/RandomSamplingErrorBound.lean`):

* `Finset.card_powersetCard_filter_inter_lt_div_choose_le` — the *entropy form*
  `p ≤ (2 n + 1) · 2 ^ (-M (1 - H₂ ((s - 1) / M)))` (eqs 12.186–12.187), assembling the count
  inequality above, the Hamming-ball entropy bound `sum_range_choose_le_rpow_mul_binEntropyBit`,
  and the central-binomial lower bound `Nat.four_pow_le_two_mul_add_one_mul_central_binom`.
* `Finset.card_powersetCard_filter_inter_lt_div_choose_le_two_pow` — the *Gaussian tail form*
  `p ≤ (2 n + 1) · 2 ^ (-ε² n / 4)`, step (3), applying the quadratic entropy bound.
* `Finset.card_powersetCard_filter_inter_lt_and_lt_div_choose_le_two_pow` — the same bound for the
  *full* exercise event `{(C ∩ E).card < s ∧ t < (E \ C).card}` (few errors on the checks **and**
  many on the untested rest), matching N&C's exact wording; the second conjunct is discarded, as in
  N&C's own step-(1) reduction.

Part (4) is a discussion prompt (compare with Chernoff / find another derivation) with no formal
statement; the counting route taken here is one such alternative to the max-term argument of
eq. 12.186. Together these `def`s and theorems are the formalisation of Exercise 12.27, a faithful,
unweakened rendering over an arbitrary finite bit set, error set, and threshold.
-/
