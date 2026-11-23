/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.CollisionEntropyLaw

/-!
# Universal hash families and the leftover-hash collision bound

For a finite family of hash functions `h : γ → α → β` (each `h g : α → β`, with `g` ranging over a
finite index type `γ`) and an input probability distribution `p : α → ℝ`, this file introduces the
combinatorial core behind Nielsen & Chuang's privacy-amplification theorem (§12.6, Theorem 12.16).

* `Real.IsUniversalFamily h`: the family is **(2-)universal** — for any two distinct inputs
  `x ≠ x'`, the fraction of members `g` that *collide* them (`h g x = h g x'`) is at most `1 / |β|`.
  This is N&C's condition "when `g` is chosen uniformly at random, `Pr[g(a₁) = g(a₂)] ≤ 1/|B|`".
* `Real.avgCollisionProb h p`: the **average collision probability** of the output `g(X)`, averaged
  over a uniform random member `g`. Writing `g(X)` for the push-forward `Real.law p (h g)` of the
  input, this is `E_G[Pc(g(X))] = (∑_g Pc(law p (h g))) / |γ|`, with `Pc = Real.collisionProb`.

## Main results

* `Real.avgCollisionProb_le`: the **leftover-hash bound** — for a universal family and any input
  distribution `p`, `avgCollisionProb h p ≤ (Fintype.card β)⁻¹ + collisionProb p`, i.e.
  `E_G[Pc(g(X))] ≤ 1/|B| + Pc(X)`.

The proof is the standard "diagonal + off-diagonal" split. Expanding the collision probability of
each push-forward over ordered input pairs (`Real.collisionProb_law_eq_sum_pairs`),
`Pc(law p (h g)) = ∑_{x, x'} [h g x = h g x'] · p x · p x'`, and averaging over `g` turns the
indicator into the collision frequency `#{g : h g x = h g x'} / |γ|`. On the diagonal `x = x'` this
frequency is `1` and contributes `∑_x p x² = Pc(X)`; off the diagonal universality bounds it by
`1/|β|`, and `∑_{x, x'} p x · p x' = 1`, contributing at most `1/|β|`.

This bound is the engine of N&C Theorem 12.16: applied to the base-`2` collision entropy
`Hc = -log₂ Pc` it yields the (corrected, honest) lower bound on the conditional collision entropy
of the hashed key. Base `2` (bits) is used throughout, matching `Real.collisionEntropy`, since N&C
Theorem 12.16 compares `Hc` to the number of output bits `m = log₂ |β|`.
-/

@[expose] public section

namespace Real

variable {α β γ : Type*}

/-- A finite family of hash functions `h : γ → α → β` is **(2-)universal** (Nielsen & Chuang §12.6)
if for every pair of distinct inputs `x ≠ x'`, the fraction of family members `g` that collide them
(`h g x = h g x'`) is at most `1 / |β|`: with `g` drawn uniformly from the family,
`Pr[h g x = h g x'] ≤ (Fintype.card β)⁻¹`. -/
def IsUniversalFamily [Fintype γ] [Fintype β] [DecidableEq β] (h : γ → α → β) : Prop :=
  ∀ x x' : α, x ≠ x' →
    ((Finset.univ.filter fun g => h g x = h g x').card : ℝ) / Fintype.card γ
      ≤ (Fintype.card β : ℝ)⁻¹

/-- The **average collision probability** of the output `g(X)` of a hash family `h : γ → α → β` on
an input distribution `p : α → ℝ`, averaged over a uniform random member `g`:
`avgCollisionProb h p = (∑_g Real.collisionProb (Real.law p (h g))) / Fintype.card γ`, where
`Real.law p (h g)` is the push-forward distribution of the output `h g`. -/
noncomputable def avgCollisionProb [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (h : γ → α → β) (p : α → ℝ) : ℝ :=
  (∑ g, collisionProb (law p (h g))) / Fintype.card γ

theorem avgCollisionProb_eq [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (h : γ → α → β) (p : α → ℝ) :
    avgCollisionProb h p = (∑ g, collisionProb (law p (h g))) / Fintype.card γ := rfl

/-- **The leftover-hash collision bound** (Nielsen & Chuang §12.6, the combinatorial core of
Theorem 12.16). For a (2-)universal family `h : γ → α → β` and any input probability distribution
`p : α → ℝ`, the average collision probability of the hashed output is at most `1/|β|` above the
input collision probability: `avgCollisionProb h p ≤ (Fintype.card β)⁻¹ + collisionProb p`, i.e.
`E_G[Pc(g(X))] ≤ 1/|B| + Pc(X)`. -/
theorem avgCollisionProb_le [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [Nonempty γ]
    {h : γ → α → β} (hu : IsUniversalFamily h) {p : α → ℝ} (h0 : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) :
    avgCollisionProb h p ≤ (Fintype.card β : ℝ)⁻¹ + collisionProb p := by
  classical
  have hγ : (0 : ℝ) < Fintype.card γ := by exact_mod_cast Fintype.card_pos
  rw [avgCollisionProb_eq, div_le_iff₀ hγ]
  -- Expand each hashed collision probability over ordered pairs and swap the `g`-sum inward.
  have reorder : (∑ g, collisionProb (law p (h g)))
      = ∑ x, ∑ x', ∑ g, if h g x' = h g x then p x * p x' else 0 := by
    simp_rw [collisionProb_law_eq_sum_pairs]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [reorder]
  -- The exact value of the two evaluated pair-sums.
  have key : (∑ x, ∑ x', ((if x' = x then p x * p x' else 0)
        + (Fintype.card β : ℝ)⁻¹ * (p x * p x')))
      = (Fintype.card β : ℝ)⁻¹ + collisionProb p := by
    have hdiag : (∑ x, ∑ x', if x' = x then p x * p x' else 0) = collisionProb p := by
      rw [collisionProb_eq]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_ite_eq' Finset.univ x fun x' => p x * p x', ite_eq_left (Finset.mem_univ x),
        ← pow_two]
    have hpp : (∑ x, ∑ x', p x * p x') = 1 := by rw [← Finset.sum_mul_sum, hsum, mul_one]
    have hoff : (∑ x, ∑ x', (Fintype.card β : ℝ)⁻¹ * (p x * p x')) = (Fintype.card β : ℝ)⁻¹ := by
      rw [show (∑ x, ∑ x', (Fintype.card β : ℝ)⁻¹ * (p x * p x'))
            = (Fintype.card β : ℝ)⁻¹ * ∑ x, ∑ x', p x * p x' by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm]
      rw [hpp, mul_one]
    simp_rw [Finset.sum_add_distrib]
    rw [hdiag, hoff, add_comm]
  calc ∑ x, ∑ x', ∑ g, (if h g x' = h g x then p x * p x' else 0)
      ≤ ∑ x, ∑ x', (Fintype.card γ : ℝ)
          * ((if x' = x then p x * p x' else 0) + (Fintype.card β : ℝ)⁻¹ * (p x * p x')) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => ?_
        have hgsum : (∑ g, if h g x' = h g x then p x * p x' else 0)
            = ((Finset.univ.filter fun g => h g x' = h g x).card : ℝ) * (p x * p x') := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [hgsum]
        by_cases hxx : x' = x
        · subst x'
          have hfull : (Finset.univ.filter fun g => h g x = h g x) = Finset.univ :=
            Finset.filter_true_of_mem fun g _ => rfl
          rw [hfull, Finset.card_univ, ite_eq_left rfl]
          have hnn : (0 : ℝ) ≤ (Fintype.card β : ℝ)⁻¹ * (p x * p x) :=
            mul_nonneg (by positivity) (mul_nonneg (h0 x) (h0 x))
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnn) hγ.le
        · rw [ite_eq_right hxx]
          have hle : ((Finset.univ.filter fun g => h g x' = h g x).card : ℝ)
              ≤ (Fintype.card β : ℝ)⁻¹ * Fintype.card γ := by
            have := hu x' x hxx
            rwa [div_le_iff₀ hγ] at this
          calc ((Finset.univ.filter fun g => h g x' = h g x).card : ℝ) * (p x * p x')
              ≤ ((Fintype.card β : ℝ)⁻¹ * Fintype.card γ) * (p x * p x') :=
                mul_le_mul_of_nonneg_right hle (mul_nonneg (h0 x) (h0 x'))
            _ = (Fintype.card γ : ℝ) * (0 + (Fintype.card β : ℝ)⁻¹ * (p x * p x')) := by ring
    _ = ((Fintype.card β : ℝ)⁻¹ + collisionProb p) * (Fintype.card γ : ℝ) := by
        rw [show (∑ x, ∑ x', (Fintype.card γ : ℝ)
              * ((if x' = x then p x * p x' else 0) + (Fintype.card β : ℝ)⁻¹ * (p x * p x')))
            = (Fintype.card γ : ℝ) * ∑ x, ∑ x', ((if x' = x then p x * p x' else 0)
              + (Fintype.card β : ℝ)⁻¹ * (p x * p x')) by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm]
        rw [key]; ring

end Real
