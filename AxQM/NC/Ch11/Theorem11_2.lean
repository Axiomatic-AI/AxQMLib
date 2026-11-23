/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Nielsen & Chuang, Theorem 11.2 (Maximum of the Shannon entropy)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.2, p. 505.

For X with d outcomes H(X)<=log d, equality iff uniform.

Here `H(X) = −∑ₓ p(x) log p(x)` is the Shannon entropy of the distribution of `X`. Modelling `X`
as a probability distribution `p : ι → ℝ` on a finite type `ι` (`p i ≥ 0`, `∑ i, p i = 1`), the
number of outcomes is `d = Fintype.card ι`, and "uniformly distributed" is `p i = (card ι)⁻¹`
for all `i`.

The statement is a real-analysis fact about the Shannon entropy of a finite probability
distribution.

**Base convention.** `ToMathlib/` measures entropy in *nats* (natural log), matching
`Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`, so `H` and `log` here are both natural
log. The inequality `H(X) ≤ log d` and the equality-iff-uniform characterization are invariant
under the choice of logarithm base (both sides scale by the same factor), so this is a faithful
reformulation of N&C's base-2 statement.

The formalisation is in `ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean`:

* `Real.entropy` — the Shannon entropy `∑ i, Real.negMulLog (p i)` of `p : ι → ℝ` (in nats).
* `Real.entropy_le_log_card` — the **inequality** `H(X) ≤ log d`: for a probability distribution
  on a nonempty finite type, `entropy p ≤ Real.log (Fintype.card ι)` (Jensen's bound).
* `Real.entropy_eq_log_card_iff` — **Theorem 11.2's equality condition**: `entropy p` attains the
  bound `log (card ι)` **iff** `p` is uniform, `∀ i, p i = (Fintype.card ι : ℝ)⁻¹`. Proved via the
  equality case of strict Jensen (`StrictConcaveOn.map_sum_eq_iff` for `strictConcaveOn_negMulLog`)
  with uniform weights. Together with `entropy_le_log_card` this is the full theorem.
* `Real.entropy_uniform` — the uniform distribution attains the maximum:
  `entropy (fun _ ↦ (Fintype.card ι)⁻¹) = log (Fintype.card ι)`, so the equality case is realized
  (the `←` direction of the `iff` is non-vacuous).
-/
