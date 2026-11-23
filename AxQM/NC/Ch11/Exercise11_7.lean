/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# N&C Exercise 11.7 — conditional entropy as a relative entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.7, p. 507.

Express the conditional entropy `H(Y|X)` as a relative entropy, deduce `H(Y|X) ≥ 0`, and find the
equality conditions.

Here `p(x, y)` is the joint distribution of the pair `(X, Y)`, `p(x) = ∑_y p(x, y)` is the marginal
of the conditioning variable `X`, `H(·)` is the Shannon entropy and `H(· ‖ ·)` is the classical
relative entropy (Kullback–Leibler divergence). Unlike Exercise 11.5, where the reference is the
genuine probability distribution `p(x) p(y)`, the natural reference realizing `H(Y | X)` as a
relative entropy is `q(x, y) = p(x, y)² / p(x) = p(x) · p(y | x)²`, a **sub-normalized**
distribution (`∑ q ≤ 1`, with equality exactly when `Y` is a deterministic function of `X`). The
exercise's deduction `H(Y | X) ≥ 0` is then non-negativity of the relative entropy against a
sub-probability reference, and equality holds iff `Y = f(X)`.

## Where the formalisation lives

The exercise quantifies over a joint distribution `p : ι × κ → ℝ` on a product of finite types and
the real-valued quantities `Real.entropy` / `Real.relativeEntropy`.

Reading `p : ι × κ → ℝ` as the joint distribution of `(X, Y)` with `X` the *conditioning* (first)
variable, the conditional entropy is `H(Y | X) = H(X, Y) − H(X) = Real.entropy p −
Real.entropy (Real.marginalFst p)`. The declarations (in
`ToMathlib/Analysis/SpecialFunctions/JointEntropy.lean`, alongside the classical half of
N&C Theorem 11.3, plus one reusable lemma in
`ToMathlib/Analysis/SpecialFunctions/ShannonEntropy.lean`):

* `Real.condEntropyRef` — **the reference distribution** the exercise asks to identify:
  `condEntropyRef p (x, y) = p(x, y)² / p_X(x)` (equal to `p_X(x) · p(y | x)²` on the support of
  `p`). `Real.condEntropyRef_nonneg` and `Real.p_eq_zero_of_condEntropyRef_eq_zero` record that it
  is nonnegative and its support contains that of `p`; `Real.sum_condEntropyRef_le` that it is
  sub-normalized, `∑ condEntropyRef p ≤ ∑ p`.
* `Real.entropy_sub_entropy_marginalFst_eq_relativeEntropy` — **the expression**:
  `H(Y | X) = D(p ‖ condEntropyRef p)`. On the support of `p` the reference log splits as
  `log q = 2 log p − log p_X`, collapsing `D(p ‖ q)` to `∑ p(x, y)(log p_X(x) − log p(x, y))` (the
  workhorse identity `Real.entropy_sub_entropy_marginalFst_eq_sum`).
* `Real.relativeEntropy_condEntropyRef_nonneg` — **the deduction** `H(Y | X) ≥ 0`: non-negativity of
  the relative entropy against the sub-normalized reference, via the sub-normalized Gibbs inequality
  `Real.relativeEntropy_nonneg_of_sum_le` (the `∑ q ≤ ∑ p` generalization of
  `Real.relativeEntropy_nonneg_of_support_subset`). This reaches, by the relative-entropy route the
  exercise prescribes, the same inequality as the direct part-2/3 result
  `Real.entropy_marginalFst_le`.
* `Real.relativeEntropy_condEntropyRef_eq_zero_iff` — **the equality condition**: `H(Y | X) = 0` if
  and only if `Y` is a deterministic function of `X` (`Real.SndDeterminedByFst`), read off the
  expression through the part-2/3 characterization
  `Real.entropy_marginalFst_eq_iff_sndDeterminedByFst`.

## Faithfulness note

The library measures entropy in *nats* (natural logarithm), whereas N&C use base-`2` logarithms
(*bits*). Both sides of every statement above scale by the same positive factor `Real.log 2` under
a change of base, so the identity, the inequality, and the equality characterization are all
invariant under the choice of logarithm base; this is a faithful reformulation, not a weakening.
The real-valued `Real.relativeEntropy` uses Mathlib's junk value `Real.log 0 = 0`, which agrees
with N&C's `H(· ‖ ·)` exactly on the absolute-continuity domain `supp p ⊆ supp (condEntropyRef p)`
— and that support condition holds automatically here
(`Real.p_eq_zero_of_condEntropyRef_eq_zero`), so the comparison is on the domain where the two
quantities coincide.

The reference `condEntropyRef p` is a *sub*-probability distribution (`∑ ≤ 1`), not a probability
distribution in the strict sense of N&C's phrasing. This is intrinsic to the *canonical* reference:
matching `D(p ‖ q)` to `H(Y | X)` termwise against the joint `p` — asking `q` to realize
`Real.entropy_sub_entropy_marginalFst_eq_sum` cell by cell — forces `log q = 2 log p − log p_X`,
hence `q(x, y) = p(x, y)² / p_X(x)`; this forced `q` is normalized iff `Y` is a deterministic
function of `X`, and is otherwise strictly sub-normalized. This is *not* an impossibility claim
about all normalized references: `D(p ‖ ·)` ranges over `[0, ∞)` as a normalized reference varies,
so whenever `H(Y | X) > 0` some normalized `q` also attains the value `H(Y | X)` — there is simply
no *structural* normalized reference that realizes `H(Y | X)` cellwise from the joint.
Non-negativity of the relative entropy holds for a sub-probability reference nonetheless
(`Real.relativeEntropy_nonneg_of_sum_le`), so the exercise's deduction goes through verbatim.
-/
