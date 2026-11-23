/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.DataProcessingInequality

/-!
# Nielsen & Chuang, Theorem 11.5 (The data processing inequality)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.5, p. 509.

Data processing inequality: for Markov chain X->Y->Z, H(X)>=H(X:Y)>=H(X:Z).

Here `H(X : Y) = H(X) + H(Y) − H(X, Y)` is the mutual information (eq. (11.20)) and a Markov chain
is a sequence of random variables with `p(z | x, y) = p(z | y)` (eq. (11.36)): `Z` is conditionally
independent of `X` given `Y`.

The statement is a real-analysis fact about the Shannon entropies of finite-alphabet random
variables. It uses the joint- and conditional-entropy results of N&C Theorem 11.3.

**Model and base convention.** A tripartite distribution of `(X, Y, Z)` is `p : ι × κ × μ → ℝ` (a
probability mass function when `p ≥ 0` and `∑ p = 1`), read as `ι × (κ × μ)`, so the two-variable
marginals/entropies of `ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean` apply directly.
Entropy
is measured in *nats* (natural log), matching `Real.entropy`; the inequalities are base-invariant
(both sides scale by the same factor under a change of logarithm base), so this is a faithful
reformulation of N&C's base-2 statement.

The formalisation is in `ToMathlib/Analysis/SpecialFunctions/DataProcessingInequality.lean`:

* `Real.IsMarkovChain` — `X → Y → Z` is a Markov chain, `p(x, y, z) · p_Y(y) = p_{XY}(x, y) ·
  p_{YZ}(y, z)` (the division-free form of `p(z | x, y) = p(z | y)`). The condition is symmetric in
  `X` and `Z`, so it also expresses `Z → Y → X` (N&C Exercise 11.10).
* `Real.marginalFstLast` — the `(X, Z)`-marginal `p_{XZ}(x, z) = ∑_y p(x, y, z)` needed to phrase
  `H(X : Z) = Real.mutualInfo (Real.marginalFstLast p)`; likewise `H(X : Y) = Real.mutualInfo
  (Real.marginalFstMid p)` and `H(X) = Real.entropy (Real.marginalFst p)`.
* `Real.mutualInfo_marginalFstMid_le_marginalFst` — **the first inequality** `H(X : Y) ≤ H(X)`
  (which holds for any distribution, no Markov hypothesis needed), and
  `Real.mutualInfo_marginalFstMid_eq_marginalFst_iff` — **its saturation condition**: `H(X) = H(X :
  Y)` iff `X` is a deterministic function of `Y`, i.e. `X` is reconstructible from `Y`.
* `Real.mutualInfo_marginalFstLast_le_marginalFstMid` — **the data processing inequality proper**,
  `H(X : Z) ≤ H(X : Y)` for a Markov chain. Following N&C, `H(X : W) = H(X) − H(X | W)` reduces it
  to `H(X | Y) ≤ H(X | Z)`; the Markov property gives `H(X | Y) = H(X | Y, Z)`
  (`Real.condEntropy_marginalFstMid_eq_of_isMarkovChain`, as `p` equals its conditional-independence
  reconstruction `Real.condIndepProd p`, so strong subadditivity is saturated), and
  conditioning-reduces-entropy (`Real.entropy_conditioning_le`, N&C Theorem 11.3 part 7, applied
  with `Y` and `Z` swapped) gives `H(X | Y, Z) ≤ H(X | Z)`.
-/
