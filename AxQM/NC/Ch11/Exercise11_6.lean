/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# N&C Exercise 11.6 — proof of classical strong subadditivity (equality iff Markov chain)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.6, p. 507.

Prove classical strong subadditivity, equality iff Markov chain Z->Y->X.

Here `H(·)` is the Shannon entropy, `p` is the joint distribution of the triple `(X, Y, Z)`, and
`H(X, Y)`, `H(Y, Z)`, `H(Y)` are its two- and one-variable margins. The exercise supplies the proof
of part 6 of N&C Theorem 11.3, promised there ("You will be asked to supply this proof as Exercise
11.6").

## Where the formalisation lives

The exercise quantifies over a joint distribution `p : ι × κ × μ → ℝ` on a product of finite types
and the real-valued `Real.entropy`. Compare Exercise 11.5 (`AxQM/NC/Ch11/Exercise11_5.lean`).

The declarations (all in `ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`, alongside the
classical half of N&C Theorem 11.3, whose part 6 this exercise completes):

* `Real.entropy_triple_add_marginal_le` — **the inequality**:
  `H(X, Y, Z) + H(Y) ≤ H(X, Y) + H(Y, Z)`. Following N&C's subadditivity argument, it is
  non-negativity of the relative entropy `D(p ‖ condIndepProd p)` of `p` against its `Z → Y → X`
  reconstruction `condIndepProd p (x, y, z) = p(x, y) · p(y, z) / p(y)`, through the identity
  `Real.relativeEntropy_condIndepProd`.
* `Real.IsMarkovChain` — **the Markov chain condition** `Z → Y → X`: the division-free
  factorization `p(x, y, z) · p_Y(y) = p_{XY}(x, y) · p_{YZ}(y, z)` for all `x, y, z`, i.e. the
  conditional independence of `X` and `Z` given `Y`. On the support of `p_Y` this rearranges to
  `p(x | y, z) = p(x | y)`, N&C's definition (11.36) of the chain; the product form is symmetric in
  `X`, `Z` (so it is manifestly also the chain `X → Y → Z`, cf. Exercise 11.10) and handles the
  `p_Y(y) = 0` fibres uniformly.
* `Real.entropy_triple_add_marginal_eq_iff` — **the equality condition** the exercise asks for:
  `H(X, Y, Z) + H(Y) = H(X, Y) + H(Y, Z) ↔ Real.IsMarkovChain p`. This is the equality case of
  relative-entropy non-negativity: `Real.relativeEntropy_eq_zero_iff` gives
  `D(p ‖ condIndepProd p) = 0 ↔ p = condIndepProd p`, and `Real.isMarkovChain_iff_eq_condIndepProd`
  identifies the Markov chain condition with that fixed point `p = condIndepProd p`.

## Faithfulness note

The library measures entropy in *nats* (natural logarithm), whereas N&C use base-`2` logarithms
(*bits*). Both sides of the inequality and of the equality identity scale by the same positive
factor `Real.log 2` under a change of base, so both — and the Markov equality characterization —
are invariant under the choice of logarithm base; this is a faithful reformulation, not a
weakening. `Real.IsMarkovChain` is the standard finite-support rendering of the conditional
independence `X ⊥ Z ∣ Y` that "`Z → Y → X` is a Markov chain" denotes.
-/
