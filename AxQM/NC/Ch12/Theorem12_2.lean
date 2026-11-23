/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.TypicalSequence

/-!
# Nielsen & Chuang, Theorem 12.2 (the theorem of typical sequences)

*(N&C p. 539.)*

Theorem of typical sequences: typicality prob, |T(n,eps)| bounds, small-set bound.

Theorem 12.2 is the classical asymptotic equipartition property: a purely probabilistic
statement about the `n`-fold i.i.d. product distribution `s ↦ ∏ᵢ p(sᵢ)` on a finite alphabet. It
is the classical (Shannon) prerequisite for the *quantum* data-compression results later in N&C
Chapter 12.

## The formalisation

Everything is finite-sum / elementary (no measure theory), matching the finite-distribution
convention of `ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean` (a distribution is a bare
`p : α → ℝ` with hypotheses `0 ≤ p` and `∑ p = 1`). N&C's base-`2` bounds `2^{n(H ± ε)}` are the
nats-convention exponentials `exp (n (H ± ε))` (with `H = Real.entropy p` in nats) — the same
statements rescaled by `log 2`.

The **concentration engine** (`ToMathlib/InformationTheory/IIDConcentration.lean`), an elementary
finite Chebyshev weak law of large numbers for the i.i.d. product distribution:

* `Real.iid_total_mass` — the total mass `∑ₛ ∏ᵢ p(sᵢ) = (∑ₓ p x)ⁿ`.
* `Real.iid_centered_sq` — the second-moment identity (variance of a sum of `n` i.i.d. terms is `n`
  times the per-sample variance).
* `Real.iid_average_deviation_le` — the Chebyshev bound: the empirical mean of an observable
  deviates from its mean by more than `ε` with probability at most `Var / (n ε²)`.

The **theorem of typical sequences** itself (`ToMathlib/InformationTheory/TypicalSequence.lean`):

* `Real.typicalSeq` — the `ε`-typical set `T(n, ε)` (Eq. 12.26), via the multiplicative definition;
  `Real.mem_typicalSeq_iff_abs_le` bridges it to the additive surprisal form (12.27) on the support.
* `Real.sum_typicalSeq_ge` / `Real.exists_le_sum_typicalSeq` — **part (1):** the typicality
  probability is at least `1 − V/(n ε²)`, hence `≥ 1 − δ` for large `n`.
* `Real.card_typicalSeq_le`, `Real.card_typicalSeq_ge_of_le_sum`,
  `Real.exists_card_typicalSeq_bounds` — **part (2):** the cardinality bounds (Eq. 12.28).
* `Real.exists_sum_prod_le_of_card_le_exp` — **part (3):** the small-set bound (Eq. 12.29) — for a
  rate `R < H` and any `δ > 0`, for all sufficiently large `n` every collection `S` of length-`n`
  sequences with `|S| ≤ exp (n R)` carries total probability at most `δ`.

Together these `def` (`typicalSeq`) and theorems (the three-part statement plus its concentration
engine) are the formalisation of Theorem 12.2 — a faithful, unweakened rendering: the statements
quantify over an arbitrary finite alphabet, an arbitrary probability mass function, and (in part 3)
*every* collection of the stated size, exactly as N&C states them.
-/
