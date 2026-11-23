/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.CollisionEntropy
public import ToMathlib.Analysis.SpecialFunctions.EntropySubadditive

/-!
# Collision probability of a push-forward law

This file bridges the collision probability `Real.collisionProb`
(`ToMathlib/InformationTheory/CollisionEntropy.lean`) and the push-forward law `Real.law`
(`ToMathlib/Analysis/SpecialFunctions/ConditionalEntropyChain.lean`).

## Main results

* `Real.collisionProb_law_eq_sum_pairs`: the collision probability of the push-forward
  `Real.law p f` of a weight `p : α → ℝ` under an arbitrary map `f : α → β` expands over ordered
  input pairs as `Pc(law p f) = ∑_x ∑_{x'} [f x' = f x] · p x · p x'`.

This is the "law of the unconscious statistician" (`Real.sum_law_mul`) applied to the collision
probability: it rewrites `∑_y (∑_{x : f x = y} p x)²`, the probability that two independent
`p`-draws land in the same `f`-fibre, as the sum of `p x · p x'` over the colliding pairs. It is
applied in `ToMathlib/InformationTheory/UniversalHashing.lean` (with `f := h g`) to average the
probability of a hashed output over a random hash function.
-/

@[expose] public section

namespace Real

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- **Ordered-pair expansion of the collision probability of a push-forward law.** For a weight
`p : α → ℝ` and any map `f : α → β`, the collision probability of the push-forward `Real.law p f`
equals the sum over ordered input pairs `(x, x')` of `p x · p x'` restricted to the pairs colliding
under `f`: `Pc(law p f) = ∑_x ∑_{x'} [f x' = f x] · p x · p x'`. Proved by the law-of-the-
unconscious-statistician identity `Real.sum_law_mul` and unfolding `Real.law` on the diagonal
argument `f x`. -/
theorem collisionProb_law_eq_sum_pairs (f : α → β) (p : α → ℝ) :
    collisionProb (law p f) = ∑ x, ∑ x', if f x' = f x then p x * p x' else 0 := by
  rw [collisionProb_eq]
  simp_rw [pow_two]
  rw [sum_law_mul p f (law p f)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hlaw : law p f (f x) = ∑ x', if f x' = f x then p x' else 0 := rfl
  rw [hlaw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [mul_ite, mul_zero]

end Real
