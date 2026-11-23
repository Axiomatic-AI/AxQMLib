/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.UniversalHashing
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Conditional collision and Shannon entropy of a universal-hash output

Continuing `ToMathlib/InformationTheory/UniversalHashing.lean`, this file assembles the two ordering
inequalities of Nielsen & Chuang's privacy-amplification theorem (§12.6, Theorem 12.16) for the
output `G(X)` of a universal hash family `h` applied to an input `X`, with the hash `G` chosen
uniformly at random from the finite family.

Writing `g(X)` for the push-forward `Real.law p (h g)` of the input distribution `p : α → ℝ`, the
two `G`-conditional entropies (with `G` uniform on the finite index type `γ`) are:

* `Real.avgCollisionEntropy h p := -Real.logb 2 (Real.avgCollisionProb h p)` — the conditional
  collision entropy `Hc(G(X) | G)` in the privacy-amplification convention: `-log₂` of the
  **average** collision probability `E_G[Pc(g(X))]` (the convention of
  Bennett–Brassard–Crépeau–Maurer for which the theorem holds). This is `-log₂` of an average,
  **not** the average of the per-`g` collision entropies.
* `Real.avgShannonEntropy h p := (∑_g H(g(X))) / (|γ| · log 2)` — the conditional Shannon entropy
  `H(G(X) | G)` in bits, the genuine average over `g` of the per-`g` Shannon entropies.

## Main results

* `Real.avgCollisionProb_pos`: the average collision probability is strictly positive (each
  push-forward `g(X)` is a probability distribution, so `Pc(g(X)) > 0`), so its `log₂` is defined.
* `Real.avgCollisionEntropy_ge` — **the corrected (honest) lower bound**, the second inequality of
  Theorem 12.16 with Nielsen & Chuang's constant repaired: for a universal family and any input `p`,
  `Hc(G(X)|G) ≥ log₂|β| - log₂(1 + |β|·Pc(X))`, where `Pc(X) = Real.collisionProb p`. Writing
  `m = log₂|β|` and `2^{m-Hc(X)} = |β|·Pc(X)`, this is `m - log₂(1 + 2^{m-Hc(X)})`. Nielsen & Chuang
  state instead the strictly larger `m - 2^{m-Hc(X)}`, which is **false** (they drop the `1/ln 2`
  factor in `log₂(1 + z) ≤ z / ln 2`, and `log₂(1 + z) > z` for `0 < z < 1`); the counterexample
  refuting the literal constant is developed separately.
* `Real.avgCollisionEntropy_le_avgShannonEntropy` — **the first inequality** of the chain,
  `H(G(X)|G) ≥ Hc(G(X)|G)`.
  Per `g`, `-log Pc(g(X)) ≤ H(g(X))` (`Real.log_collisionProb_inv_le_entropy`, the nat-log form of
  `Hc(g(X)) ≤ H(g(X))`); averaging over `g` and applying Jensen's inequality to the concave
  `Real.log` (so `-log₂` of the average collision probability is at most the average of the per-`g`
  collision entropies) chains these into the conditional statement.

The honest bound `avgCollisionEntropy_ge` is the engine of the assembled faithful statement of
Theorem 12.16.
-/

@[expose] public section

namespace Real

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]

omit [Fintype γ] in
/-- The push-forward `law p (h g)` of a probability distribution `p` is again a probability
distribution: `∑_y law p (h g) y = 1`. -/
private theorem sum_law_hash {h : γ → α → β} {p : α → ℝ} (hsum : ∑ x, p x = 1) (g : γ) :
    ∑ y, law p (h g) y = 1 := by rw [sum_law]; exact hsum

omit [Fintype γ] in
/-- Each hashed collision probability `Pc(g(X)) = collisionProb (law p (h g))` is strictly positive,
since `law p (h g)` is a probability distribution. -/
theorem collisionProb_law_pos {h : γ → α → β} {p : α → ℝ} (hsum : ∑ x, p x = 1) (g : γ) :
    0 < collisionProb (law p (h g)) :=
  collisionProb_pos (sum_law_hash hsum g)

/-- The **average collision probability is strictly positive** (for a nonempty family and a genuine
input distribution): a positive average of the strictly positive per-`g` collision probabilities. It
guarantees `Real.logb 2 (avgCollisionProb h p)` is a genuine logarithm of a positive number. -/
theorem avgCollisionProb_pos [Nonempty γ] {h : γ → α → β} {p : α → ℝ} (hsum : ∑ x, p x = 1) :
    0 < avgCollisionProb h p := by
  rw [avgCollisionProb_eq]
  refine div_pos (Finset.sum_pos (fun g _ => collisionProb_law_pos hsum g) Finset.univ_nonempty) ?_
  exact_mod_cast Fintype.card_pos

/-- The **conditional collision entropy** `Hc(G(X) | G)` of the output of a hash family `h` on an
input distribution `p`, with the hash `G` chosen uniformly: `-log₂` of the average collision
probability (privacy-amplification convention). Note this is `-log₂` of an average, not the average
of the per-`g` collision entropies. -/
noncomputable def avgCollisionEntropy (h : γ → α → β) (p : α → ℝ) : ℝ :=
  -Real.logb 2 (avgCollisionProb h p)

/-- Unfolding lemma for `avgCollisionEntropy`: `Hc(G(X)|G) = -log₂ (avgCollisionProb h p)`. -/
theorem avgCollisionEntropy_eq (h : γ → α → β) (p : α → ℝ) :
    avgCollisionEntropy h p = -Real.logb 2 (avgCollisionProb h p) := rfl

/-- The **conditional Shannon entropy** `H(G(X) | G)` of the output of a hash family `h` on an input
distribution `p`, in bits, with the hash `G` chosen uniformly: the average over `g` of the per-`g`
Shannon entropies `H(g(X)) = entropy (law p (h g))`, converted to bits by dividing by `log 2`.

This coincides with the general conditional Shannon entropy `Real.condEntropyMap`
(`H(f | g) = H(f, g) − H(g)`) instantiated over `Ω = γ × α` with the uniform-`G` joint weight
`(g, x) ↦ |γ|⁻¹ · p x`, output `(g, x) ↦ h g x`, and side variable `Prod.fst` — up to the bits/nats
`1 / log 2` factor (`condEntropyMap` is in nats), since conditional entropy is the average of the
per-block entropies. The direct bits-average is used here to keep bits throughout (matching
`avgCollisionEntropy` and `m = log₂|β|`) and to avoid the `[DecidableEq γ]` instance that
`Real.condEntropyMap` would force. -/
noncomputable def avgShannonEntropy (h : γ → α → β) (p : α → ℝ) : ℝ :=
  (∑ g, entropy (law p (h g))) / (Fintype.card γ * Real.log 2)

/-- Unfolding lemma for `avgShannonEntropy`:
`H(G(X)|G) = (∑_g entropy (law p (h g))) / (|γ| · log 2)`. -/
theorem avgShannonEntropy_eq (h : γ → α → β) (p : α → ℝ) :
    avgShannonEntropy h p = (∑ g, entropy (law p (h g))) / (Fintype.card γ * Real.log 2) := rfl

/-- **The corrected (honest) lower bound on the conditional collision entropy** (Nielsen & Chuang
§12.6, Theorem 12.16, second inequality — with the literal constant repaired). For a (2-)universal
family `h : γ → α → β` and any input probability distribution `p`,
`Hc(G(X)|G) ≥ log₂|β| - log₂(1 + |β|·Pc(X))`, where `Pc(X) = collisionProb p`.

Writing `m = log₂|β|` (the number of output bits) and `2^{m-Hc(X)} = |β|·Pc(X)`, the right-hand side
is `m - log₂(1 + 2^{m-Hc(X)})`. This is strictly weaker than Nielsen & Chuang's stated
`m - 2^{m-Hc(X)}`, which is **false**: `log₂(1 + z) > z` for `0 < z < 1`, so the textbook's linear
constant over-states the true bound (the discrepancy is exactly the `1/ln 2` factor dropped from
`log₂(1 + z) ≤ z / ln 2`). The refutation of the literal constant is developed separately.

Proof: the leftover-hash bound `avgCollisionProb h p ≤ |β|⁻¹ + Pc(X)` (`avgCollisionProb_le`),
monotonicity of `log₂`, and the factorisation `|β|⁻¹ + Pc = |β|⁻¹·(1 + |β|·Pc)`. -/
theorem avgCollisionEntropy_ge [Nonempty β] [Nonempty γ] {h : γ → α → β} (hu : IsUniversalFamily h)
    {p : α → ℝ} (h0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    Real.logb 2 (Fintype.card β) - Real.logb 2 (1 + Fintype.card β * collisionProb p)
      ≤ avgCollisionEntropy h p := by
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hβne : (Fintype.card β : ℝ) ≠ 0 := ne_of_gt hβ
  have hApos : 0 < avgCollisionProb h p := avgCollisionProb_pos hsum
  have hPc : 0 ≤ collisionProb p := collisionProb_nonneg p
  have hfac : 0 < 1 + Fintype.card β * collisionProb p := by positivity
  -- The leftover-hash bound and monotonicity of `log₂`.
  have hlog : Real.logb 2 (avgCollisionProb h p)
      ≤ Real.logb 2 ((Fintype.card β : ℝ)⁻¹ + collisionProb p) :=
    Real.logb_le_logb_of_le (by norm_num) hApos (avgCollisionProb_le hu h0 hsum)
  -- Factor the bound: `|β|⁻¹ + Pc = |β|⁻¹·(1 + |β|·Pc)`, and split the `log₂`.
  have hBfac : (Fintype.card β : ℝ)⁻¹ + collisionProb p
      = (Fintype.card β : ℝ)⁻¹ * (1 + Fintype.card β * collisionProb p) := by
    rw [mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ hβne, one_mul]
  have hlogB : Real.logb 2 ((Fintype.card β : ℝ)⁻¹ + collisionProb p)
      = -Real.logb 2 (Fintype.card β) + Real.logb 2 (1 + Fintype.card β * collisionProb p) := by
    rw [hBfac, Real.logb_mul (inv_ne_zero hβne) (ne_of_gt hfac), Real.logb_inv]
  rw [avgCollisionEntropy_eq]
  rw [hlogB] at hlog
  linarith

/-- **The first inequality** of Nielsen & Chuang Theorem 12.16: `H(G(X)|G) ≥ Hc(G(X)|G)`, the
conditional Shannon entropy of the hashed output dominates its conditional collision entropy. Per
`g`, `-log Pc(g(X)) ≤ H(g(X))` (`log_collisionProb_inv_le_entropy`, the nat-log form of
`Hc(g(X)) ≤ H(g(X))`); the conditional statement is obtained by averaging over `g` and applying
Jensen's inequality to the concave `Real.log` — `-log₂` of the average collision probability is at
most the average of the per-`g` collision entropies. -/
theorem avgCollisionEntropy_le_avgShannonEntropy [Nonempty γ] {h : γ → α → β} {p : α → ℝ}
    (h0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    avgCollisionEntropy h p ≤ avgShannonEntropy h p := by
  have hγ : (0 : ℝ) < Fintype.card γ := by exact_mod_cast Fintype.card_pos
  have hγne : (Fintype.card γ : ℝ) ≠ 0 := ne_of_gt hγ
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Jensen for the concave `log`: `∑_g |γ|⁻¹ • log Pc_g ≤ log (∑_g |γ|⁻¹ • Pc_g)`.
  have hjensen : ∑ g, (Fintype.card γ : ℝ)⁻¹ • Real.log (collisionProb (law p (h g)))
      ≤ Real.log (∑ g, (Fintype.card γ : ℝ)⁻¹ • collisionProb (law p (h g))) := by
    refine (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (fun g _ => by positivity) ?_
      (fun g _ => Set.mem_Ioi.mpr (collisionProb_law_pos hsum g))
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hγne]
  -- Identify the two `|γ|⁻¹`-weighted sums.
  have hsum_prob : ∑ g, (Fintype.card γ : ℝ)⁻¹ • collisionProb (law p (h g))
      = avgCollisionProb h p := by
    rw [avgCollisionProb_eq, div_eq_inv_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => smul_eq_mul _ _
  have hsum_log : ∑ g, (Fintype.card γ : ℝ)⁻¹ • Real.log (collisionProb (law p (h g)))
      = (∑ g, Real.log (collisionProb (law p (h g)))) / Fintype.card γ := by
    rw [div_eq_inv_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => smul_eq_mul _ _
  rw [hsum_prob, hsum_log] at hjensen
  -- Per-`g` first inequality (nat-log form): `-log Pc_g ≤ H(g(X))`.
  have hperg : ∀ g, -Real.log (collisionProb (law p (h g))) ≤ entropy (law p (h g)) := by
    intro g
    have hh := log_collisionProb_inv_le_entropy (law_nonneg h0 (h g)) (sum_law_hash hsum g)
    rwa [Real.log_inv] at hh
  have hsumperg : (∑ g, -Real.log (collisionProb (law p (h g)))) ≤ ∑ g, entropy (law p (h g)) :=
    Finset.sum_le_sum fun g _ => hperg g
  -- Combine (nat-log): `-log (avgCollisionProb) ≤ (∑_g H(g(X)))/|γ|`.
  have hnat : -Real.log (avgCollisionProb h p)
      ≤ (∑ g, entropy (law p (h g))) / Fintype.card γ := by
    calc -Real.log (avgCollisionProb h p)
        ≤ -((∑ g, Real.log (collisionProb (law p (h g)))) / Fintype.card γ) := by linarith
      _ = (∑ g, -Real.log (collisionProb (law p (h g)))) / Fintype.card γ := by
          rw [Finset.sum_neg_distrib, neg_div]
      _ ≤ (∑ g, entropy (law p (h g))) / Fintype.card γ :=
          (div_le_div_iff_of_pos_right hγ).2 hsumperg
  -- Convert to base-2 (bits) by dividing through by `log 2 > 0`.
  have hShannon : avgShannonEntropy h p
      = ((∑ g, entropy (law p (h g))) / Fintype.card γ) / Real.log 2 := by
    rw [avgShannonEntropy_eq, div_div]
  rw [avgCollisionEntropy_eq, hShannon, ← Real.log_div_log, ← neg_div]
  exact (div_le_div_iff_of_pos_right hlog2).2 hnat

end Real
