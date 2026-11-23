/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# N&C Exercise 11.5 — subadditivity of the Shannon entropy via a relative-entropy identity

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.5, p. 505.

Subadditivity of Shannon entropy via relative entropy identity; H(X,Y)<=H(X)+H(Y).

Here `p(x, y)` is the joint distribution of the pair `(X, Y)`, `p(x) = ∑_y p(x, y)` and
`p(y) = ∑_x p(x, y)` are its marginals, `H(·)` is the Shannon entropy, and
`H(· ‖ ·)` is the classical relative entropy (Kullback–Leibler divergence). The left-hand side of
the identity is the mutual information `H(X : Y)`; the exercise's point is that subadditivity is
just non-negativity of this particular relative entropy, read through the identity.

## Where the formalisation lives

The exercise quantifies over a joint distribution `p : ι × κ → ℝ` on a product of finite types and
the real-valued quantities `Real.entropy` / `Real.relativeEntropy`.

The declarations (all in `ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`, alongside the
classical half of N&C Theorem 11.3, which subsumes subadditivity as its part 4):

* `Real.relativeEntropy_indepProd_eq` — **the identity** the exercise asks to show:
  `D(p ‖ p_X ⊗ p_Y) = H(X) + H(Y) − H(X, Y)`, i.e.
  `H(p(x, y) ‖ p(x) p(y)) = H(p(x)) + H(p(y)) − H(p(x, y))`. Here `p_X ⊗ p_Y = Real.indepProd p`
  is the product of the marginals `Real.marginalFst p` and `Real.marginalSnd p`. Holds for any
  nonnegative `p` (no normalization needed for the identity itself).
* `Real.mutualInfo_eq_relativeEntropy` — the same identity with its right-hand side packaged as the
  mutual information `Real.mutualInfo p = H(X : Y)`; `relativeEntropy_indepProd_eq` is this composed
  with the definitional `Real.mutualInfo_eq`.
* `Real.entropy_le_add_marginal` — **subadditivity** (the first "deduce"): `H(X, Y) ≤ H(X) + H(Y)`,
  obtained from the identity and non-negativity of the relative entropy
  (`Real.relativeEntropy_nonneg_of_support_subset`), since the support of `p` lies in that of
  `p_X ⊗ p_Y` and the two have equal total mass `1`.
* `Real.entropy_add_marginal_eq_iff` — **the equality condition** (the second "deduce"):
  `H(X) + H(Y) = H(X, Y) ↔ p = Real.indepProd p`, i.e. equality holds iff `X` and `Y` are
  independent. This routes through `Real.mutualInfo_eq_zero_iff` and the equality case of Gibbs'
  inequality (`Real.relativeEntropy_eq_zero_iff`).

## Faithfulness note

The library measures entropy in *nats* (natural logarithm), whereas N&C use base-`2` logarithms
(*bits*). Both sides of every statement above scale by the same positive factor `Real.log 2` under
a change of base, so the identity, the inequality, and the equality characterization are all
invariant under the choice of logarithm base; this is a faithful reformulation, not a weakening.
The real-valued `Real.relativeEntropy` uses Mathlib's junk value `Real.log 0 = 0`, which agrees
with N&C's `H(· ‖ ·)` exactly on the absolute-continuity domain `supp p ⊆ supp (p_X ⊗ p_Y)` — and
that support condition holds automatically here (`Real.p_eq_zero_of_indepProd_eq_zero`), so the
comparison is on the domain where the two quantities coincide.
-/
