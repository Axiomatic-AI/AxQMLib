/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.InformationFunction

/-!
# N&C Exercise 11.2 — intuitive justification for the definition of entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.2, p. 501.

The exercise asks: given an *information function* `I` on events, with

1. `I` a function only of the event's probability `p` (so `I = I p`, `p ∈ [0, 1]`);
2. `I` a smooth function of probability;
3. `I (p q) = I p + I q` for `p, q > 0` (information of independent events adds),

show that `I p = k * log p` for some constant `k`. It follows that the average information gain
over a set of mutually exclusive events with probabilities `p₁, …, pₙ` is `k ∑ᵢ pᵢ log pᵢ`, which
is the Shannon entropy up to the constant factor.

## Where the formalisation lives

The exercise is a statement about a real-valued function `I : ℝ → ℝ` and `Real.log` /
`Real.entropy`. The declarations are both in
`ToMathlib/Analysis/SpecialFunctions/InformationFunction.lean`:

* `Real.exists_const_mul_log_of_map_mul_eq_add` — the main claim: a function differentiable on the
  positive reals with `I (p q) = I p + I q` (`p, q > 0`) satisfies `I p = k * Real.log p` for some
  constant `k` (`= deriv I 1`). This is Cauchy's logarithmic functional equation. Smoothness
  (axiom 2) is weakened to differentiability, giving a strictly more general result; the functional
  equation and conclusion are taken on all of `(0, ∞)`, exactly as axiom (3) is stated, with the
  probability range `(0, 1]` a special case.
* `Real.sum_mul_eq_neg_mul_entropy_of_eq_const_mul_log` — the consequence: for such an `I`, the
  average information gain `∑ i, p i * I (p i)` over a distribution `p` equals
  `-k * Real.entropy p`, identifying it with the Shannon entropy up to the constant factor.

## Faithfulness note

Axiom (2) demands a *smooth* `I`; the formalisation assumes only differentiability at each positive
point, which is a weaker hypothesis and hence a stronger theorem (it subsumes the smooth case). No
generality of the textbook claim is lost.
-/
