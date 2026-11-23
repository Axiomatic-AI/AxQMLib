/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Convex.Majorization

/-!
# Nielsen & Chuang, Exercise 12.17 (tail-sum characterisation of majorization)

*(N&C p. 574.)*

Show x prec y iff sum max(x_j-t,0) <= sum max(y_j-t,0) for all t and equal sums.

This is a purely convex-analytic statement about real vectors: majorization `x ≺ y` — the sum of
the `k` largest entries of `x` is at most that of `y` for every `k`, with equal total sums — is
characterised by the pointwise ordering of the *tail* (or *cut*) functions
`t ↦ ∑ⱼ max(xⱼ - t, 0)` together with equality of the total sums. Compare the neighbouring
classical results on this page, Proposition 12.11 (`Proposition12_11`) and Exercise 12.18
(`Exercise12_18`).

## The formalisation

The formalisation is in `ToMathlib/Analysis/Convex/Majorization.lean`,
extending the shared `Majorize` / `largestKSum` definitions of Proposition 12.11 (used also by
Exercises 12.18 and 12.19). N&C's statement is captured exactly. The declarations are:

* `tailSum x t = ∑ i, max (x i - t) 0` — **the tail/cut function** of `x : ι → ℝ` at threshold `t`
  (over a finite index type `ι`), N&C's `∑ⱼ max(xⱼ - t, 0)`.
* `tailSum_eq_sum_filter` — `tailSum x t = ∑ i ∈ {i | t < x i}, (x i - t)`: only the entries
  strictly above the threshold contribute, the rest having zero positive part (forward direction).
* `majorize_iff_forall_tailSum` — **Exercise 12.17 itself**:
  `Majorize x y ↔ (∀ t, tailSum x t ≤ tailSum y t) ∧ ∑ i, x i = ∑ i, y i`. The right-hand side is
  precisely N&C's condition: the tail functions are pointwise ordered for every real threshold `t`,
  and the total sums agree. (Both conjuncts are genuinely needed: the tail hypothesis alone forces
  only `∑ x ≤ ∑ y` — take `t` below every entry — so equality of the sums is a separate condition,
  exactly as N&C states.)

The proof is the Legendre-type conjugacy between `tailSum` and `largestKSum` (`largestKSum x k` =
sum of the `k` largest entries of `x`, the shared `Majorize` witness). The supporting lemmas, all in
the same file:

* `largestKSum_le_tailSum_add` — `largestKSum x k ≤ tailSum x t + k · t` for `k ≤ card`, the easy
  half (every `k`-subset sum is bounded by the positive-part sum plus `k · t`).
* `exists_tailSum_add_eq_largestKSum` — tightness: for `1 ≤ k ≤ card` the bound is *attained* at the
  threshold `t = ` the `k`-th largest entry, obtained from a maximising `k`-subset by an exchange
  argument (`insert`/`erase`). Combined with the easy half this gives `largestKSum x k ≤ largestKSum
  y k` from the tail hypothesis, and hence (with `majorize_iff_forall_largestKSum`) majorization.
* `largestKSum_zero`, `largestKSum_eq_zero`, `largestKSum_attained` — the `largestKSum` edge-case
  lemmas used in the reverse direction: `k = 0` (empty subset, both sides `0`), `k > card` (no
  `k`-subset, both sides `0`), and attainment of the supremum by an actual `k`-subset (feeding the
  exchange argument above).

## Faithfulness

N&C states Exercise 12.17 for real `d`-dimensional vectors, with `≺` the majorization order (sum of
the `k` largest entries dominated, equal totals — its `largestKSum`/`Majorize` encoding is the same
one used for Prop 12.11 and reused across the chapter). The Mathlib development is stated over
an arbitrary finite index type `ι` with `ℝ`-valued vectors `ι → ℝ`; `ι := Fin d` recovers N&C's case
verbatim, so this is a faithful formalisation (indeed slightly more general — no ordering of the
index is assumed, the majorization order being defined sort-free). The biconditional is stated in
full, neither conjunct weakened. The proof uses only `propext`, `Classical.choice` and `Quot.sound`
(`#print axioms majorize_iff_forall_tailSum`).
-/
