/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Convex.Prod

/-!
# N&C Exercise 11.23 — joint concavity implies concavity in each input

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.23, p. 519.

Show joint concavity implies concavity in each input; find a per-input-concave non-jointly-concave
function.

Here (eq. 11.96) `f` is *jointly concave* when
`f (λ A₁ + (1−λ) A₂, λ B₁ + (1−λ) B₂) ≥ λ f (A₁, B₁) + (1−λ) f (A₂, B₂)` for all `0 ≤ λ ≤ 1`,
i.e. `f` is concave on the product of the two argument domains. The exercise is the elementary
convexity lemma underpinning the definition N&C use to state Lieb's theorem (Theorem 11.11).

## Where the formalisation lives

The exercise is a statement about `ConcaveOn ℝ` (indeed `ConcaveOn 𝕜` for a general ordered
scalar) of a function on a product of convex sets. Compare the sibling Exercise 11.9.

The declarations are all in `ToMathlib/Analysis/Convex/Prod.lean`:

* `ConcaveOn.slice_left` — **the first part of the exercise**: if `f : E × F → β` is concave on a
  product set `s ×ˢ t`, then for each fixed `b ∈ t` the slice `a ↦ f (a, b)` is concave on `s`.
  This is exactly "`f (A, B)` is concave in `A`, with `B` held fixed".
* `ConcaveOn.slice_right` — the symmetric statement fixing the first argument, so joint concavity
  gives concavity in *each* input, completing the phrase used in the second part.
* `mulPair` — the product function `(x, y) ↦ x * y` on `ℝ × ℝ`, the answer to "find a function of
  two variables …".
* `mulPair_concaveOn_left`, `mulPair_concaveOn_right` — `mulPair` is concave (indeed affine) in
  each argument separately.
* `mulPair_not_concaveOn` — `mulPair` is **not** jointly concave, exhibiting a separately-concave
  but not-jointly-concave function.

## Faithfulness

N&C phrase Part 1 for a "real-valued function of two matrices" on the positive matrices (the
domain of Lieb's theorem). The formalisation is *more general*, not weaker: `slice_left` /
`slice_right` are stated for `ConcaveOn 𝕜 (s ×ˢ t) f` over arbitrary modules `E`, `F` and an
arbitrary convex product domain `s ×ˢ t` (an ordered scalar `𝕜`), of which real-valued functions
of Hermitian matrices on the positive cone are a special case. Restricting to a subset `s ×ˢ t`
(rather than the whole space) is essential precisely so the lemma covers the positive-matrix
domain N&C work with. Part 1 asks only for concavity in `A`; `slice_right` additionally records
the symmetric direction, matching "concave in each of its inputs".

For Part 2, `mulPair (x, y) = x y` is affine — hence both convex and concave — in each argument,
yet its restriction to the segment from `(1, 1)` to `(-1, -1)` is strictly convex through the
origin, so joint concavity fails at the midpoint (`1 ≤ 0` would be required).
-/
