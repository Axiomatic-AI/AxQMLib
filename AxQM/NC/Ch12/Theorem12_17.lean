/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.ConditionalCollisionEntropy

/-!
# Nielsen & Chuang, Theorem 12.17 (privacy amplification tail bound)

*(N&C p. 585.)*

With prob 1-2^{-s}, Hc(X|U=u) >= Hc(X) - 2log|U| - 2s.

Here `Hc(X) = −log₂ ∑ₓ p(x)²` is the **collision entropy** (Rényi entropy of order 2, N&C
eq. 12.171) and `Hc(X | U = u) = −log₂ ∑ₓ p(x | u)²` is its conditional version for the *specific*
observed value `U = u` (not an average over `u`). This is the "stronger bound" N&C invoke to control
the collision entropy lost to a reconciliation message `U = u`: it says the leaked information only
rarely — probability `< 2⁻ˢ` — costs more than `2 log |𝒰| + 2s` bits of collision entropy.

Theorem 12.17 is a statement in classical probability / information theory: a tail bound on
the conditional collision entropy of a pair of random variables over finite alphabets. Compare the
neighbouring collision-entropy result Theorem 12.16 (`Theorem12_16`).

## The formalisation

The formalisation is in `ToMathlib/InformationTheory/ConditionalCollisionEntropy.lean`, using the
collision-entropy API of
`ToMathlib/InformationTheory/CollisionEntropy.lean` (Theorem 12.16, providing `Real.collisionProb`
and `Real.collisionEntropy`) and the joint-distribution marginals of
`ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean` (`Real.marginalFst = p_X`,
`Real.marginalSnd = p_U`). Following that convention, `X` is the first coordinate `ι` and `U` the
second coordinate `κ` of a joint law `p : ι × κ → ℝ`.

* `Real.condDistribGivenSnd p u` — the conditional distribution `x ↦ p(x, u) / p_U(u)` of `X` given
  `U = u` (the zero function where `p_U(u) = 0`); `Real.sum_condDistribGivenSnd` shows it is a
  genuine probability distribution wherever `p_U(u) ≠ 0`.
* `Real.condCollisionProb p u` — the conditional collision probability `Pc(X | U = u) = ∑ₓ p(x|u)²`.
* `Real.condCollisionEntropy p u` — **`Hc(X | U = u) = −log₂ ∑ₓ p(x|u)²`**, the conditional
  collision entropy; `Real.condCollisionEntropy_eq` records `Hc(X | U = u) = −log₂ Pc(X | U = u)`.
* `Real.prob_condCollisionEntropy_ge` — **Theorem 12.17 itself**: for `p ≥ 0`, `∑ p = 1` and any
  `s`,
  `1 − 2⁻ˢ ≤ ∑ u ∈ Finset.univ.filter (fun u ↦ Hc(X) − 2·log₂|U| − 2s ≤ Hc(X | U = u)),
  Real.marginalSnd p u`,
  with `Hc(X) = Real.collisionEntropy (Real.marginalFst p)` and `|U| = Fintype.card κ`. The
  right-hand side is the total `p_U`-probability of the set of values `u` at which the collision
  entropy bound holds; the inequality is exactly N&C's "with probability at least `1 − 2⁻ˢ`, `U`
  takes a value `u` for which `Hc(X | U = u) ≥ Hc(X) − 2 log|𝒰| − 2s`".

Two supporting lemmas capture the crux of the proof:

* `Real.marginalSnd_sq_mul_condCollisionProb` — the weighting identity
  `p_U(u)² · Pc(X | U = u) = ∑ₓ p(x, u)²` (valid even where `p_U(u) = 0`).
* `Real.sum_marginalSnd_sq_mul_condCollisionProb_le` — the marginal-domination bound
  `∑ᵤ p_U(u)² · Pc(X | U = u) ≤ Pc(X)`, i.e. the joint collision probability is at most the
  marginal collision probability (from `Finset.sum_sq_le_sq_sum_of_nonneg`, since
  `∑ᵤ p(x, u)² ≤ (∑ᵤ p(x, u))² = p_X(x)²`).

The tail bound then follows by a Cauchy–Schwarz / Markov argument
(`sq_sum_le_card_mul_sum_sq`): the "bad" set `{u : Hc(X | U = u) < Hc(X) − 2 log|U| − 2s}` has
`p_U`-mass `S` with `θ · ∑_bad p_U(u)² ≤ Pc(X)` for the threshold `θ = Pc(X)·|U|²·2^{2s}` (the
`u`-value at which the entropy bound turns into `θ ≤ Pc(X | U = u)`), and
`S² ≤ |bad|·∑_bad p_U(u)² ≤ |U|·Pc(X)/θ = (|U|·2^{2s})⁻¹ ≤ 2^{−2s}`, whence `S ≤ 2⁻ˢ`. Collision
entropy is converted to collision probability throughout via strict monotonicity of `log₂`
(`Real.strictMonoOn_logb`).

## Faithfulness

N&C states Theorem 12.17 for random variables on finite alphabets `𝒳`, `𝒰` with a joint
distribution and a parameter `s > 0`. The Mathlib development is stated for arbitrary finite types
`ι`, `κ` and any joint law `p : ι × κ → ℝ` with `p ≥ 0` and `∑ p = 1`, and the conclusion is
verbatim N&C's `Hc(X | U = u) ≥ Hc(X) − 2·log₂|U| − 2s` holding on a set of `p_U`-probability at
least `1 − 2⁻ˢ`. Two points of honesty:

* **Positivity of `s`.** N&C require `s > 0` (the regime where `1 − 2⁻ˢ ∈ (0, 1)` is a genuine
  high-probability guarantee). The formal statement drops this hypothesis: the inequality holds for
  *every* real `s`, vacuously when `s ≤ 0` (then `1 − 2⁻ˢ ≤ 0 ≤ ∑ p_U`). This is a strengthening,
  not a weakening — instantiating at any `s > 0` recovers N&C's claim exactly.
* **The `|U|` exponent.** N&C state the loss term as `2 log|𝒰|`; the Cauchy–Schwarz argument in
  fact delivers the sharper `log|𝒰|`, so the stated `2 log|𝒰|` bound (which is what is formalised,
  for fidelity to the textbook) holds with slack `2⁻ˢ/√|U|` to spare.

N&C do not prove Theorem 12.17 ("a detailed proof … is beyond the scope of this book"); the formal
proof is complete.
-/
