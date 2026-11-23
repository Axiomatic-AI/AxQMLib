/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Convex.Majorization

/-!
# Nielsen & Chuang, Exercise 12.18 (the set majorized by a fixed vector is convex)

*(N&C p. 574.)*

Show the set of x with x prec y is convex.

Here `x ≺ y` is majorization: the sum of the `k` largest entries of `x` is at most that of `y` for
every `k`, with equal total sums. The exercise asks for convexity of `{x | x ≺ y}` for a fixed
vector `y`.

This is a purely convex-analytic statement about real vectors — a fixed sublevel/half-space
intersection is convex. Compare the neighbouring classical majorization results on this page,
Exercise 12.17 (`Exercise12_17`) and Proposition 12.11 (`Proposition12_11`).

## The formalisation

The formalisation is in `ToMathlib/Analysis/Convex/Majorization.lean`,
alongside the `Majorize` / `largestKSum` API of Proposition 12.11 and the tail-sum characterisation
of Exercise 12.17. N&C's statement is captured exactly:

* `convex_setOf_majorize` — **Exercise 12.18 itself**: `Convex ℝ {x | Majorize x y}` for any fixed
  `y : ι → ℝ` on a finite index type `ι`. `Majorize x y` is N&C's `x ≺ y`
  (`majorize_iff_forall_largestKSum` confirms it is exactly the textbook "sum of the `k` largest
  entries" condition), and `{x | Majorize x y}` is the set the exercise asks about.

The proof reads convexity off the definition directly. `{x | Majorize x y}` is cut out by
* the affine equation `∑ i, x i = ∑ i, y i` (a hyperplane, hence convex), and
* the half-space conditions `∑ i ∈ s, x i ≤ largestKSum y s.card`, one for each finite subset `s`
  (each `∑ i ∈ s, · ` is linear and the bound is a constant, so each is a half-space),

and an intersection of hyperplanes and half-spaces is convex: for `x₁, x₂` in the set and weights
`a, b ≥ 0` with `a + b = 1`, both defining relations pass through the convex combination
`a • x₁ + b • x₂` by linearity of the subset sums (`add_le_add` / `mul_le_mul_of_nonneg_left` on the
half-spaces, and additivity of the total sum on the hyperplane).

**On N&C's hint.** N&C suggests deriving convexity from the previous exercise — the tail-function
characterisation `x ≺ y ↔ (∀ t, tailSum x t ≤ tailSum y t) ∧ ∑ x = ∑ y`
(`majorize_iff_forall_tailSum`, Exercise 12.17) — since each `x ↦ tailSum x t = ∑ⱼ max (xⱼ - t) 0`
is convex in `x` (a sum of maxima of affine functions), so `{x | tailSum x t ≤ tailSum y t}` is a
sublevel set of a convex function and hence convex. The proof here instead uses the
equivalent half-space form directly (`largestKSum y s.card` is a fixed constant once `y` is fixed),
which needs no tail-function machinery and yields the identical set `{x | x ≺ y}`; the *claim*
proven is exactly the exercise's, so this is a faithful — indeed more elementary — formalisation.

## Faithfulness

N&C states Exercise 12.18 for real `d`-dimensional vectors. The Mathlib development is stated over
an arbitrary finite index type `ι` with `ℝ`-valued vectors `ι → ℝ`; `ι := Fin d` recovers N&C's case
verbatim, so this is a faithful formalisation (indeed slightly more general — the majorization order
is defined sort-free, no ordering of the index being assumed). The convexity is a full result in
`ToMathlib/` (the surrounding development uses only `propext`, `Classical.choice`, `Quot.sound`,
per `#print axioms`). -/
