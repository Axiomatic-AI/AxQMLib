/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# N&C Exercise 11.10 — a Markov chain read backwards is still a Markov chain

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.10, p. 510.

Show that if X->Y->Z is a Markov chain then so is Z->Y->X.

Here `p : ι × κ × μ → ℝ` is the joint distribution of the triple `(X, Y, Z)` on a product of finite
types, and "`X → Y → Z` is a Markov chain" means `X` and `Z` are conditionally independent given
`Y`. The reversed chain `Z → Y → X` is the Markov-chain condition for the joint distribution of the
reversed triple `(Z, Y, X)`.

## Where the formalisation lives

Compare Exercises 11.5 (`AxQM/NC/Ch11/Exercise11_5.lean`) and 11.6
(`AxQM/NC/Ch11/Exercise11_6.lean`).

The declarations are all in `ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`, alongside
`Real.IsMarkovChain`:

* `Real.reverseTriple` — the joint distribution of the reversed triple `(Z, Y, X)` obtained from
  that of `(X, Y, Z)` by swapping the outer coordinates: `reverseTriple p (z, y, x) = p (x, y, z)`.
  It is an involution (`Real.reverseTriple_reverseTriple`).
* `Real.isMarkovChain_reverseTriple` — **the exercise**:
  `Real.IsMarkovChain p → Real.IsMarkovChain (Real.reverseTriple p)`, i.e. if `X → Y → Z` is a
  Markov chain then so is `Z → Y → X`.
* `Real.isMarkovChain_reverseTriple_iff` — the two-way form
  `Real.IsMarkovChain (Real.reverseTriple p) ↔ Real.IsMarkovChain p`, exhibiting the symmetry of the
  chain condition under reversal (the exercise's implication holds in both directions because
  `reverseTriple` is an involution).

The supporting marginal-transformation lemmas `Real.marginalMid_reverseTriple`,
`Real.marginalFstMid_reverseTriple`, and `Real.marginalSnd_reverseTriple` record how the one- and
two-variable marginals move under reversal: the middle `Y`-marginal is invariant, while the
`(X, Y)`- and `(Y, Z)`-marginals are exchanged.

## Faithfulness note

`Real.IsMarkovChain p := ∀ x y z, p(x, y, z) · p_Y(y) = p_{XY}(x, y) · p_{YZ}(y, z)` is the standard
division-free rendering of the conditional independence `X ⊥ Z ∣ Y` that "`X → Y → Z` is a Markov
chain" denotes (on the `p_Y(y) > 0` fibres it is N&C's `p(x, z ∣ y) = p(x ∣ y) p(z ∣ y)`; on the
`p_Y(y) = 0` fibres both sides vanish). Modelling the reversed chain `Z → Y → X` as
`Real.IsMarkovChain (Real.reverseTriple p)` — the *same* condition on the joint of the reordered
triple, rather than a second condition hard-wired into one distribution — is the faithful reading of
the exercise: the theorem then has genuine content (order-reversal invariance), which the exercise
asks us to prove. No hypotheses beyond `IsMarkovChain p` are used, so the statement is not weakened.
-/
