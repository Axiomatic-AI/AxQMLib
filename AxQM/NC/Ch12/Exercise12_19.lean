/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Convex.Majorization

/-!
# Nielsen & Chuang, Exercise 12.19 (the inductive step of Proposition 12.11)

*(N&C p. 574.)*

Verify x' prec y' in the inductive step of Proposition 12.11.

The exercise refers to the induction in N&C's proof of Proposition 12.11 (the representation
theorem `x ≺ y ↔ x = ∑ⱼ pⱼ Pⱼ y`). In the step one has decreasing `(d+1)`-dimensional vectors
`x`, `y` with `x ≺ y` (so `x₁ ≤ y₁`); one picks an index `j` with `yⱼ ≤ x₁ ≤ y_{j-1}` and a
`t ∈ [0,1]` with `x₁ = t y₁ + (1-t) yⱼ`, and forms `D ≡ tI + (1-t)T` (`T` the transposition of the
`1`st and `j`th coordinates), a convex combination of permutation matrices. Then `Dy` has first
entry `x₁`, and setting `x' ≡ (x₂, …, x_{d+1})` and
`y' ≡ (y₂, …, y_{j-1}, (1-t)y₁ + t yⱼ, y_{j+1}, …, y_{d+1})` — i.e. `Dy` with its first entry
dropped — the exercise asks to verify `x' ≺ y'`, which feeds the inductive hypothesis (`x'`
majorized in dimension `d`).

This is a purely convex-analytic statement about real vectors — a majorization descends to the
tails after a T-transform. Compare the neighbouring classical majorization results on this page,
Exercise 12.17 (`Exercise12_17`), Exercise 12.18 (`Exercise12_18`) and Proposition 12.11
(`Proposition12_11`).

## The formalisation

The formalisation is in `ToMathlib/Analysis/Convex/Majorization.lean`,
alongside the `Majorize` / `largestKSum` API of Proposition 12.11. N&C's claim is captured exactly
(0-based indices, so N&C's `x₁` is `x 0`, N&C's `j` is the pivot `p ≠ 0`, and `Fin.tail` drops the
leading coordinate):

* `majorize_tail_update_of_antitone` — **Exercise 12.19 itself**: for decreasing
  `x y : Fin (n + 1) → ℝ` with `Majorize x y`, a pivot `p ≠ 0` and a weight `t : ℝ` satisfying
  `x 0 ≤ y (p - 1)` and `x 0 = t * y 0 + (1 - t) * y p`,
  `Majorize (Fin.tail x) (Fin.tail (Function.update y p ((1 - t) * y 0 + t * y p)))`.
  (N&C additionally assume `0 ≤ t ≤ 1` and `y p ≤ x 0`; these are unused for `x' ≺ y'` and are
  dropped for a minimal statement — see the Faithfulness section below.)
  Here `Fin.tail x = (x 1, …, x n)` is N&C's `x'`, and
  `Fin.tail (Function.update y p ((1 - t) * y 0 + t * y p))` is N&C's `y'` — the vector `Dy` with
  the `p`-th entry replaced by the complementary convex combination `(1-t) y 0 + t y p` and the
  leading entry (which is `x 0`) discarded.

The proof works with the sort-free `largestKSum` (the sum of the `k` largest entries): since `x'`
is decreasing, `largestKSum x' k` is its leading `k`-block, which the successor bijection
identifies with `∑` of `x` over indices `1, …, k`; comparing this with the same block of `y'`
splits into two cases on the pivot `p`. When `p ≤ k` the block sums differ from the leading
`(k+1)`-blocks of `x`, `y` only by the shared value `x 0`, so the bound is `Majorize x y` at level
`k + 1`; when `p > k` the update does not touch the block and the bound is termwise,
`x i ≤ x 0 ≤ y (p - 1) ≤ y i`. Equality of total sums follows from `∑ x = ∑ y` and the T-transform
identity `w + x 0 = y 0 + y p`. This is the sort-free analogue of N&C's partial-sum verification.

**Relation to Proposition 12.11.** `ToMathlib/` proves Proposition 12.11 itself
(`majorize_iff_exists_sum_perm`) by the equivalent separating-hyperplane route
(`Majorize.exists_doublyStochastic_mulVec`), which avoids the dimension induction and hence does
not invoke this lemma. Exercise 12.19 is formalised as the standalone majorization fact
it is — the verification N&C asks the reader to carry out inside the T-transform induction.

## Faithfulness

N&C states the step for real `(d+1)`-dimensional vectors. The Mathlib development is stated over
`Fin (n + 1) → ℝ` (with `n := d`, `ι := Fin (d+1)` recovering N&C's case verbatim). N&C's `x = x↓`,
`y = y↓` (components in decreasing order) become `Antitone x`, `Antitone y`; the pivot `j` becomes
`p ≠ 0`; and N&C's weight equation `x₁ = t y₁ + (1-t) yⱼ` and upper pivot bound `x₁ ≤ y_{j-1}` are
transcribed as `x 0 = t * y 0 + (1 - t) * y p` and `x 0 ≤ y (p - 1)`. The conclusion `x' ≺ y'` is
exactly `Majorize (Fin.tail x) (Fin.tail (Function.update y p …))`, so this is a faithful
formalisation. N&C's step additionally assumes `0 ≤ t ≤ 1` and the lower pivot bound `yⱼ ≤ x₁`
(i.e. `y p ≤ x 0`) — guaranteeing the replacement is a genuine convex combination — but `x' ≺ y'`
needs only `x 0 ≤ y (p - 1)`, so those two bounds are dropped for a minimal statement and the lemma
covers N&C's case a fortiori (its hypotheses are a subset of N&C's).
-/
