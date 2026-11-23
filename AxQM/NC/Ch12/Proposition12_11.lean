/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Convex.Majorization

/-!
# Nielsen & Chuang, Proposition 12.11 (majorization representation theorem)

*(N&C p. 574.)*

x prec y iff x = sum p_j P_j y for probabilities p_j and permutation matrices P_j.

Proposition 12.11 is a purely convex-analytic statement about real vectors: majorization
`x ≺ y` — the sum of the `k` largest entries of `x` is at most that of `y` for every `k`, with
equal total sums — holds exactly when `x` is a convex combination of permutations of `y`. Compare
the neighbouring classical results on this page, Exercise 12.18 (`Exercise12_18`) and Birkhoff's
Theorem 12.12 (`Theorem12_12`).

## The formalisation

The formalisation is in `ToMathlib/Analysis/Convex/Majorization.lean` (using the
doubly-stochastic-matrix and Birkhoff API of `Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean`
and `Mathlib/Analysis/Convex/Birkhoff.lean`). N&C's statement is captured exactly:

* `Majorize x y` — majorization of `x y : ι → ℝ` over a finite index type `ι`, defined sort-free via
  `largestKSum x k = ⨆ s, ∑ i ∈ s, x i` (the largest sum of `k` entries) as
  `(∑ i, x i = ∑ i, y i) ∧ ∀ s, ∑ i ∈ s, x i ≤ largestKSum y s.card`.
  `majorize_iff_forall_largestKSum` shows this is exactly N&C's textbook condition
  (`∀ k, largestKSum x k ≤ largestKSum y k` together with equal total sums).
* `majorize_iff_exists_sum_perm` — **Proposition 12.11 itself**:
  `Majorize x y ↔ ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
  x = ∑ σ, w σ • (σ.permMatrix ℝ *ᵥ y)`. The right-hand side is precisely N&C's
  `x = ∑ⱼ pⱼ Pⱼ y`: `w` is the probability distribution `pⱼ` over permutations, and
  `σ.permMatrix ℝ *ᵥ y` applies the permutation matrix `Pⱼ` to `y`.
* `majorize_iff_exists_doublyStochastic` — the equivalent doubly-stochastic form used in N&C's proof
  and on p. 575: `Majorize x y ↔ ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ y = x`. This is the
  Hardy–Littlewood–Pólya theorem; combined with Birkhoff's theorem (Theorem 12.12) it is equivalent
  to the sum-of-permutations form above.

Supporting results in the same file, several of them the exercises N&C cites in the proof:

* `convex_setOf_majorize` — the set `{x | x ≺ y}` is convex (**Exercise 12.18**), used for the easy
  direction.
* `Majorize.of_mem_doublyStochastic` — the easy direction `D *ᵥ y ≺ y` for doubly stochastic `D`.
* `Majorize.exists_perm_sum_mul_le` — the analytic Hardy–Littlewood–Pólya obstruction
  (`∀ c, ∃ σ, ∑ i, c i * x i ≤ ∑ i, c i * y (σ i)`), proved via the rearrangement inequality and
  summation by parts on the `largestKSum` sequence.
* `Majorize.exists_doublyStochastic_mulVec` — the hard direction, proved geometrically by separating
  `x` from the compact convex set `{D *ᵥ y | D doubly stochastic}` with a hyperplane
  (`geometric_hahn_banach_closed_point`) and contradicting the obstruction above.

## Faithfulness

N&C states Proposition 12.11 for real `d`-dimensional vectors. The Mathlib development is stated
over an arbitrary finite index type `ι` with `ℝ`-valued vectors `ι → ℝ`; `ι := Fin d` recovers N&C's
case
verbatim, so this is a faithful formalisation (indeed slightly more general — no ordering of the
index is assumed, the majorization order being defined sort-free). Rather than N&C's `T`-transform
dimension induction (which requires a type-changing coordinate drop and the Exercise 12.19 subset
argument), the hard direction is proved by the equivalent separating-hyperplane route on the same
statement, so nothing is weakened: the result is a full proof.
-/
