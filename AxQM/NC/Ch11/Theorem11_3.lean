/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# Nielsen & Chuang, Theorem 11.3 (Basic properties of Shannon entropy)

*(N&C p. 506.)*

Basic properties of Shannon entropy: symmetry, conditioning, subadditivity, strong subadditivity,
etc.

Here `H(X, Y) = −∑_{x,y} p(x, y) log p(x, y)` is the joint entropy (eq. (11.18)),
`H(X | Y) = H(X, Y) − H(Y)` the conditional entropy (eq. (11.19)), and
`H(X : Y) = H(X) + H(Y) − H(X, Y)` the mutual information (eq. (11.20)).

## Where this is formalised

Theorem 11.3 is a collection of statements of pure **finite-probability real analysis**: each
quantifies over a distribution `p : ι × κ → ℝ` (or `p : ι × κ × μ → ℝ`) on a finite type and the
real-valued Shannon quantities built on `Real.entropy`. They are in `ToMathlib/`, alongside the
Shannon-entropy development they belong to.

The base-2 logarithm of N&C is replaced by the natural logarithm (nats), matching the `Real.entropy`
convention of `ToMathlib/`. Every inequality and equality condition below is base-independent (both
sides scale by the same factor under a change of logarithm base), so this is a faithful
reformulation, not a weakening. The joint distribution `p` is a probability mass function under
`hp : ∀ q, 0 ≤ p q` and `hsum : ∑ q, p q = 1`; the sub-additivity results are instances of
non-negativity of the classical relative entropy `Real.relativeEntropy` (N&C Theorem 11.1) through
the mutual-information identity, so `supp p ⊆ supp (reconstruction)` holds automatically and no
strict positivity is assumed.

## The formalisation (in `ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`)

The shared substrate: the marginals `Real.marginalFst`, `Real.marginalSnd`; the conditional entropy
`Real.condEntropy p = H(X, Y) − H(Y)`; the mutual information
`Real.mutualInfo p = H(X) + H(Y) − H(X, Y)`; the product-of-marginals `Real.indepProd`; and, for the
tripartite parts, the `(X, Y)`-marginal `Real.marginalFstMid`, the middle marginal
`Real.marginalMid`, and the conditional-independence reconstruction
`Real.condIndepProd p (x, y, z) = p_{XY}(x, y)·p_{YZ}(y, z) / p_Y(y)`. The key bridge is
`Real.mutualInfo_eq_relativeEntropy` — `H(X : Y) = D(p ‖ p_X ⊗ p_Y)` — through which every
subadditivity statement is an instance of relative-entropy non-negativity (reusing N&C Theorem 11.1,
`Real.relativeEntropy_nonneg_of_support_subset` / `Real.relativeEntropy_eq_zero_iff`).

* **Part 1 (symmetry).** `Real.entropy_swap` (`H(X, Y) = H(Y, X)`) and `Real.mutualInfo_swap`
  (`H(X : Y) = H(Y : X)`).
* **Part 2** (`H(Y | X) ≥ 0`, whence `H(X : Y) ≤ H(Y)`). `Real.condEntropy_nonneg` (also N&C
  Exercise 11.7), `Real.mutualInfo_le_marginalSnd`; the equality condition
  `Real.mutualInfo_eq_marginalSnd_iff_sndDeterminedByFst` — saturated iff `Y` is a deterministic
  function of `X` (`Real.SndDeterminedByFst`).
* **Part 3** (`H(X) ≤ H(X, Y)`). `Real.entropy_marginalFst_le`, `Real.entropy_marginalSnd_le`; the
  equality condition `Real.entropy_marginalFst_eq_iff_sndDeterminedByFst` (again iff `Y = f(X)`).
* **Part 4 (subadditivity).** `Real.entropy_le_add_marginal` (`H(X, Y) ≤ H(X) + H(Y)`); the equality
  condition `Real.entropy_add_marginal_eq_iff` — saturated iff `X` and `Y` are independent
  (`p = p_X ⊗ p_Y`).
* **Part 5.** `Real.condEntropy_le_marginalFst` (`H(X | Y) ≤ H(X)`), `Real.mutualInfo_nonneg`
  (`H(X : Y) ≥ 0`); the equality condition `Real.mutualInfo_eq_zero_iff` — again iff independence.
* **Part 6 (strong subadditivity).** `Real.entropy_triple_add_marginal_le`
  (`H(X, Y, Z) + H(Y) ≤ H(X, Y) + H(Y, Z)`, also N&C Exercise 11.6); the equality condition
  `Real.entropy_triple_add_marginal_eq_iff` — saturated iff `Z → Y → X` forms a Markov chain
  (`Real.IsMarkovChain`, i.e. `X ⊥ Z | Y`), via `Real.isMarkovChain_iff_eq_condIndepProd`
  (`IsMarkovChain p ↔ p = Real.condIndepProd p`) and the equality half of relative-entropy
  non-negativity through `Real.relativeEntropy_condIndepProd`.
* **Part 7 (conditioning reduces entropy).** `Real.entropy_conditioning_le`
  (`H(X | Y, Z) ≤ H(X | Y)`), the rearrangement of strong subadditivity.

N&C's parts 4 and 6 close with "equality iff …" clauses; those are the
`_eq_iff` theorems above, so the collection is the full statement of Theorem 11.3 — inequalities and
their saturation conditions — not merely its inequalities.
-/
