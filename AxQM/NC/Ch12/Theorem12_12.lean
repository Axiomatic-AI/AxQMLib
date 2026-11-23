/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Nielsen & Chuang, Theorem 12.12 (Birkhoff's theorem)

*(N&C p. 574.)*

Birkhoff's theorem: doubly stochastic iff convex combination of permutation matrices.

Theorem 12.12 is a purely combinatorial / convex-analytic statement about real matrices: it
identifies the *doubly stochastic* matrices —
those with non-negative entries whose rows and columns each sum to one — with the convex hull of the
permutation matrices (equivalently, the extreme points of the doubly stochastic polytope are exactly
the permutation matrices). Compare the neighbouring classical results on this page,
Proposition 12.11 (`Proposition12_11`) and Theorem 12.13 (`Theorem12_13`).

## The formalisation

Birkhoff's theorem is already developed in
`Mathlib/Analysis/Convex/Birkhoff.lean` (built on the doubly-stochastic-matrix API of
`Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean`). N&C's statement is captured exactly:

* `doublyStochastic R n` (a `Submonoid (Matrix n n R)`) — the set of doubly stochastic matrices.
  `mem_doublyStochastic_iff_sum` unfolds membership to precisely N&C's definition: non-negative
  entries `∀ i j, 0 ≤ M i j`, unit row sums `∀ i, ∑ j, M i j = 1`, and unit column sums
  `∀ j, ∑ i, M i j = 1`.
* `Equiv.Perm.permMatrix R σ` — the permutation matrix `Pⱼ` of a permutation `σ`; a convex
  combination of permutation matrices is a point of the convex hull
  `convexHull R {x | ∃ σ, Equiv.Perm.permMatrix R σ = x}`.
* `doublyStochastic_eq_convexHull_permMatrix` — **Birkhoff's theorem itself** (the "if and only if"
  as a set equality): `↑(doublyStochastic R n) = convexHull R {x | ∃ σ, permMatrix R σ = x}`.
  Set equality is the two-way iff of N&C's statement: a matrix is doubly stochastic exactly when it
  is a convex combination of permutation matrices.
* `exists_eq_sum_perm_of_mem_doublyStochastic` — the constructive forward direction giving N&C's
  explicit form `D = ∑ⱼ pⱼ Pⱼ` with the weights exposed: for `M ∈ doublyStochastic R n` there is a
  weight function `w` on `Equiv.Perm n` with `∀ σ, 0 ≤ w σ`, `∑ σ, w σ = 1`, and
  `∑ σ, w σ • Equiv.Perm.permMatrix R σ = M` (a genuine probability distribution `pⱼ` over
  permutation matrices).
* The converse direction (a convex combination of permutation matrices is doubly stochastic) is
  bundled in the set equality above, and is also available directly from
  `permMatrix_mem_doublyStochastic` (each `Pⱼ` is doubly stochastic) together with
  `convex_doublyStochastic` (the doubly stochastic set is convex).
* `extremePoints_doublyStochastic` — the companion vertex characterisation: the extreme points of
  the doubly stochastic set are exactly the permutation matrices.

## Faithfulness

N&C states Theorem 12.12 for real `d × d` matrices. The Mathlib development is stated over an
arbitrary linearly ordered field (`Field R`, `LinearOrder R`, `IsStrictOrderedRing R`) indexed by a
finite type `n`; `R := ℝ`, `n := Fin d` recovers N&C's real case verbatim, so this is a faithful
formalisation (indeed strictly more general). The result is a full proof
— N&C itself states the theorem without proof — so nothing here is weakened.
-/
