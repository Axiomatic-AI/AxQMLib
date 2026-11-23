/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Normed.Algebra.ExponentialSmulSum

/-!
# Nielsen & Chuang, Exercise 4.47 (`Exercise4_47`)

For H=sum H_k with [H_j,H_k]=0, prove e^{-iHt}=prod e^{-iH_k t}.

The statement is a pure operator-algebra identity — the exponential of a sum of pairwise-commuting
elements factors as the product of the individual exponentials — with no physical content.

## The formalisation

Mathlib already proves the scalar-free identity as
`NormedSpace.exp_sum_of_commute` (`Mathlib/Analysis/Normed/Algebra/Exponential.lean`):
in a Banach algebra, a pairwise-commuting family `f` satisfies
`exp (∑ i, f i) = ∏ i, exp (f i)`, the product being a `Finset.noncommProd`.

The exercise dresses this with the physical scalar `-i t`. The file
`ToMathlib/Analysis/Normed/Algebra/ExponentialSmulSum.lean` records the scalar-scaled forms:

* `NormedSpace.exp_smul_sum_of_commute` — for a scalar `c : M` acting on the algebra by a
  distributive, multiplication-compatible action (`DistribSMul`/`SMulCommClass`/`IsScalarTower`,
  so the scalar type is left generic) and pairwise-commuting `f`,
  `exp (c • ∑ i, f i) = ∏ i, exp (c • f i)`. The scalar factors out of the sum
  (`Finset.smul_sum`) and preserves commutativity (`Commute.smul_left`/`smul_right`), so this is
  `exp_sum_of_commute` applied to `fun i => c • f i`.
* `NormedSpace.exp_neg_I_mul_smul_sum_of_commute` — the exercise's exact form, the `M = ℂ`,
  `c = -(i t)` instance:
  `exp (-(i t) • ∑ₖ Hₖ) = ∏ₖ exp (-(i t) • Hₖ)`.

## Correspondence with N&C

Under the dictionary

* `𝔸` ↦ the algebra of operators, e.g. `Matrix n n ℂ` or the bounded operators `H →L[ℂ] H` on a
  complex Hilbert space (both are complex Banach algebras carrying the required `NormedAlgebra ℂ`
  and `NormedAlgebra ℚ` instances);
* the `L` summands `H₁, …, H_L` ↦ the family `H : ι → 𝔸` over a finite index `s : Finset ι`
  (take `ι = Fin L` or `s = Finset.Icc 1 L`);
* `[Hⱼ, Hₖ] = 0` ↦ the pairwise-commutativity hypothesis `(s : Set ι).Pairwise (Commute on H)`;
* `H = ∑ₖ Hₖ` ↦ `∑ k ∈ s, H k`, and `e^{-iHt}` ↦ `exp (-(i t) • ∑ k ∈ s, H k)`,

`NormedSpace.exp_neg_I_mul_smul_sum_of_commute` reads exactly as the exercise's claim
`e^{-iHt} = e^{-iH₁t} ⋯ e^{-iH_L t}`. The ordered product `e^{-iH₁t} ⋯ e^{-iH_L t}` is rendered as a
`Finset.noncommProd`: because the factors commute (the exponentials of commuting operators commute)
the product is order-independent, which is precisely why the exercise's left-to-right ordering is
immaterial. The Mathlib statement is over an arbitrary complex Banach algebra and an arbitrary
finite index set, so it is a faithful generalisation of N&C's finite-dimensional, `k = 1 … L` case,
not a weakening.
-/
