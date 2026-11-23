/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupCount
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Concrete: the Ettinger–Høyer–Knill collision sum — its threshold split and far tail

This file assembles the **candidate-sum** side of the Ettinger–Høyer–Knill identification bound
behind Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem). To identify the
hidden subgroup `K` from the `m`-copy coset reduced state `σ_K^{⊗m}`, the
distinguishing-measurement analysis must control the **sum over all candidate hidden subgroups**
`K'` of the pairwise *affinity* of the reduced states,

`∑_{K'≠K} A(σ_K^{⊗m}, σ_{K'}^{⊗m}) = ∑_{K'≠K} (|K∩K'| / √(|K|·|K'|))^m`

(the per-pair affinity is `A(σ_K, σ_{K'}) = |K∩K'|/√(|K||K'|)`,
`AxQM.cosetDensityState_affinity`, raised to the sample count `m` under tensor powers,
`AxQM.cosetDensityState_pi_affinity`). This file works with the *concrete shadow* of that
per-pair affinity,

`cosetAffinity K K' = |K∩K'| / √(|K|·|K'|)`,

a plain real number, and studies the sum `∑_{K'} cosetAffinity K K'^m`
directly as finite-group arithmetic.

## What is proved

* `cosetAffinity` with its basic API — `cosetAffinity_nonneg` (`0 ≤ A`), `cosetAffinity_self`
  (`A(K,K) = 1`), and the **near-orthogonality bound** `cosetAffinity_le_of_ne`
  (`K ≠ K' ⟹ A ≤ 1/√2`, the concrete form of `AxQM.cosetDensityState_affinity_le`, whose
  group-theoretic core is `two_mul_card_inf_sq_le`, `2·|K∩K'|² ≤ |K||K'|`).
* `sum_cosetAffinity_pow_le_of_forall_le` — the reusable **count × separation** tail tool: over any
  finset `𝒮` of subgroups on which `cosetAffinity K · ≤ b`, the sum `∑_{K'∈𝒮} A^m ≤ |𝒮|·b^m`.
* `sum_cosetAffinity_pow_threshold_le` — the **threshold split** of the collision sum at a chosen
  separation `θ`: splitting the candidate set into a *near* part (`A > θ`) and a *far* part
  (`A ≤ θ`),

  `∑_{K'∈𝒮} A^m ≤ |{K'∈𝒮 : A > θ}| · (1/√2)^m + |𝒮| · θ^m`,

  the near terms bounded by the universal per-copy separation `1/√2`, the far terms by `θ`.
* `sum_cosetAffinity_pow_univ_le` — the split specialised to the full candidate set
  `Subgroup G ∖ {K}`, the far-part count discharged by the subgroup-count bound `card_subgroup_le`:

  `∑_{K'≠K} A^m ≤ |{K'≠K : A > θ}| · (1/√2)^m + |G|^{log₂|G|+1} · θ^m`.

## Why the split — and what remains

A *naive* union bound charges every candidate the maximal per-copy separation `1/√2`, giving
`∑ ≤ (#subgroups)·(1/√2)^m ≤ |G|^{log₂|G|+1}·2^{-m/2}` (the `θ = 1/√2` degenerate case of the split,
where the near part is everything). Because a group can have `|G|^{Θ(log|G|)} = 2^{Θ((log|G|)²)}`
subgroups, that forces a **quadratic** `m = Θ((log|G|)²)` to push the sum below `1/|G|`. The
threshold split is a valid decomposition and a reusable tool, **but a single threshold with the
crude subgroup count is not the route to the linear sample count** `m = 4 log₂|G| + 2`
(N&C's value).
At that `m`, `(1/√2)^m = 1/(2|G|²)` and the far constant `|G|^{log₂|G|+1} = 2^{(log₂|G|)²+log₂|G|}`,
so the far term `|G|^{log₂|G|+1}·θ^m` has exponent `(log₂|G|)² + (1 + 4 log₂θ)·log₂|G|`: for any
*constant* `θ < 1/√2` the quadratic `(log₂|G|)²` dominates and the far term diverges (a constant `θ`
forces a *quadratic* `m = Θ((log₂|G|)²)`), while any `θ` small enough to suppress it drives the near
count `|{K'≠K : A > θ}|` up to the full super-polynomial `|G|^{Θ(log₂|G|)}`. No single threshold
with the crude count is linear.

The linear bound instead uses a **dyadic-shell** decomposition: group the candidates by the value of
`A(K,K')`, and count each shell with the *index-refined* subgroup count
`AxQM.Concrete.card_subgroup_index_le` (`Concrete/SubgroupIndexCount.lean`) rather than the
crude total `card_subgroup_le`. A shell `A(K,K') ≥ 2^{-j/2}` has `≤ |G|^{j+1}` members (they lie
above `K∩K'` with `[K':K∩K'] ≤ 2^j`), *polynomial* per shell, so `∑_j |G|^{O(j)}·2^{-jm/2}`
converges for `m = O(log₂|G|)`. This file supplies the threshold split (a single shell boundary) and
the
far-tail arithmetic; the per-shell count is `card_subgroup_index_le`, and assembling the shells into
`∑_{K'≠K} A^m ≤ 1/|G|` at `m = 4 log₂|G| + 2` is the remaining bookkeeping.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

/-- **The concrete coset affinity** `A(K, K') = |K ∩ K'| / √(|K|·|K'|)` of two subgroups `K, K'` of
a finite group `G`: the real-number shadow of the quantum affinity of the coset reduced states
`A(σ_K, σ_{K'}) = tr(√σ_K √σ_{K'})` (`AxQM.cosetDensityState_affinity`). It is the pairwise
fidelity-family distinguishability quantity whose *sum* over candidate hidden subgroups governs the
error of the Ettinger–Høyer–Knill identification measurement for Nielsen & Chuang, Problem 5.5. -/
noncomputable def cosetAffinity (K K' : Subgroup G) : ℝ :=
  (Nat.card ↥(K ⊓ K') : ℝ) / Real.sqrt (Nat.card ↥K * Nat.card ↥K')

/-- **The coset affinity is nonnegative**: `0 ≤ A(K, K')`, being a quotient of a nonnegative
numerator `|K ∩ K'|` by the nonnegative square root `√(|K|·|K'|)`. -/
theorem cosetAffinity_nonneg (K K' : Subgroup G) : 0 ≤ cosetAffinity K K' := by
  unfold cosetAffinity; positivity

/-- **The self-affinity is one**: `A(K, K) = |K| / √(|K|·|K|) = |K|/|K| = 1`, the concrete form of
`AxQM.State.affinity_self` (`A(σ_K, σ_K) = 1`). -/
theorem cosetAffinity_self [Finite G] (K : Subgroup G) : cosetAffinity K K = 1 := by
  have hK : (0 : ℝ) < Nat.card ↥K := by exact_mod_cast Nat.card_pos
  unfold cosetAffinity
  rw [inf_idem, Real.sqrt_mul_self hK.le, div_self hK.ne']

/-- **The squared coset affinity on an overgroup is the index ratio**: for `K ≤ K'`,
`A(K, K')² = |K|/|K'|`, since `K ∩ K' = K`. Generalises `cosetAffinity_self` (the `K' = K` case,
where `|K|/|K'| = 1`); it reads the squared affinity off the closed form once the intersection
collapses to `K`. -/
theorem cosetAffinity_sq_of_le [Finite G] {K K' : Subgroup G} (h : K ≤ K') :
    cosetAffinity K K' ^ 2 = (Nat.card ↥K : ℝ) / Nat.card ↥K' := by
  have hKpos : (0 : ℝ) < Nat.card ↥K := by exact_mod_cast Nat.card_pos
  unfold cosetAffinity
  rw [inf_eq_left.mpr h, div_pow, Real.sq_sqrt (by positivity), pow_two,
    mul_div_mul_left _ _ hKpos.ne']

/-- **Near-orthogonality of the coset affinity** (Nielsen & Chuang, Problem 5.5, per-pair form). For
*distinct* subgroups `K ≠ K'` of a finite group `G`,

`A(K, K') = |K ∩ K'| / √(|K|·|K'|) ≤ 1/√2`.

This is the concrete form of `AxQM.cosetDensityState_affinity_le`; its group-theoretic core
is `two_mul_card_inf_sq_le` (`2·|K∩K'|² ≤ |K|·|K'|`, from a proper subgroup having at most half the
order of its overgroup). It bounds every *near* term of the collision sum by the universal per-copy
separation `1/√2`. -/
theorem cosetAffinity_le_of_ne [Finite G] (K K' : Subgroup G) (hne : K ≠ K') :
    cosetAffinity K K' ≤ 1 / Real.sqrt 2 := by
  unfold cosetAffinity
  have hK : (0 : ℝ) < Nat.card ↥K := by exact_mod_cast Nat.card_pos
  have hK' : (0 : ℝ) < Nat.card ↥K' := by exact_mod_cast Nat.card_pos
  have hsqrt : (0 : ℝ) < Real.sqrt (Nat.card ↥K * Nat.card ↥K') := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff₀ hsqrt (by positivity), one_mul, Real.le_sqrt (by positivity) (by positivity),
    mul_pow, Real.sq_sqrt (by norm_num), mul_comm]
  exact_mod_cast two_mul_card_inf_sq_le K K' hne

/-- **The count × separation tail bound.** If the coset affinity `A(K, ·)` is at most `b ≥ 0` on
every subgroup in a finset `𝒮`, then the `m`-th-power collision sum over `𝒮` is at most `|𝒮|·b^m`:

`∑_{K'∈𝒮} A(K, K')^m ≤ |𝒮| · b^m`.

This is the reusable *far-tail* tool: applied to the far part of the collision sum (candidates
whose per-copy overlap is `≤ θ`) it gives the `(#candidates)·θ^m` term whose geometric decay
overwhelms the super-polynomial subgroup count. Proof: `A(K, K')^m ≤ b^m` termwise
(`pow_le_pow_left₀`, using
`cosetAffinity_nonneg`), then sum a constant. -/
theorem sum_cosetAffinity_pow_le_of_forall_le (K : Subgroup G) (m : ℕ) {𝒮 : Finset (Subgroup G)}
    {b : ℝ} (hbnd : ∀ K' ∈ 𝒮, cosetAffinity K K' ≤ b) :
    ∑ K' ∈ 𝒮, cosetAffinity K K' ^ m ≤ 𝒮.card * b ^ m := by
  calc ∑ K' ∈ 𝒮, cosetAffinity K K' ^ m
      ≤ ∑ _K' ∈ 𝒮, b ^ m :=
        Finset.sum_le_sum fun K' hK' => pow_le_pow_left₀ (cosetAffinity_nonneg K K') (hbnd K' hK') m
    _ = 𝒮.card * b ^ m := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The threshold split of the collision sum** (Nielsen & Chuang, Problem 5.5, the
Ettinger–Høyer–Knill sum decomposition). For a finite group `G`, a subgroup `K`, a candidate set `𝒮`
of subgroups *not containing* `K` (`hK : K ∉ 𝒮`), a sample count `m`, and any threshold `θ ≥ 0`,
splitting `𝒮` into a *near* part (`A(K, K') > θ`) and a *far* part (`A(K, K') ≤ θ`) gives

`∑_{K'∈𝒮} A(K, K')^m ≤ |{K'∈𝒮 : A(K,K') > θ}| · (1/√2)^m + |𝒮| · θ^m`.

Each near term is bounded by the universal per-copy separation `1/√2` (`cosetAffinity_le_of_ne`, all
`K' ∈ 𝒮` are distinct from `K` since `K ∉ 𝒮`); each far term by the chosen threshold `θ`; both parts
by `sum_cosetAffinity_pow_le_of_forall_le`. The two contributions trade off: pushing `θ` down
shrinks the far term but grows the near part, and the linear sample count `m = 4 log₂|G| + 2` works
because a *constant* `θ < 1/√2` makes `θ^m` beat the candidate count while the near part stays small
(the
remaining Ettinger–Høyer–Knill near-count estimate). -/
theorem sum_cosetAffinity_pow_threshold_le [Finite G] (K : Subgroup G)
    (m : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) {𝒮 : Finset (Subgroup G)} (hK : K ∉ 𝒮) :
    ∑ K' ∈ 𝒮, cosetAffinity K K' ^ m
      ≤ (𝒮.filter fun K' => θ < cosetAffinity K K').card * (1 / Real.sqrt 2) ^ m
        + 𝒮.card * θ ^ m := by
  classical
  -- Split `𝒮` into near (`θ < A`) and far (`¬ θ < A`, i.e. `A ≤ θ`).
  rw [← Finset.sum_filter_add_sum_filter_not 𝒮 (fun K' => θ < cosetAffinity K K')
    (fun K' => cosetAffinity K K' ^ m)]
  refine add_le_add ?_ ?_
  · -- Near: every `K' ∈ 𝒮` is `≠ K` (as `K ∉ 𝒮`), so `A(K, K') ≤ 1/√2`.
    exact sum_cosetAffinity_pow_le_of_forall_le K m fun K' hK' =>
      cosetAffinity_le_of_ne K K' (by
        rintro rfl; exact hK (Finset.mem_of_mem_filter K hK'))
  · -- Far: the filter gives `¬ θ < A`, i.e. `A ≤ θ`; the count `≤ |𝒮|`.
    refine (sum_cosetAffinity_pow_le_of_forall_le K m fun K' hK' =>
      not_lt.mp (Finset.mem_filter.mp hK').2).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _)
      (pow_nonneg hθ m)

/-- **The threshold split over the full candidate set** (Nielsen & Chuang, Problem 5.5). Summing
over *all* candidate hidden subgroups `K' ≠ K` of a finite group `G`, the collision sum obeys, for
any sample count `m` and threshold `θ ≥ 0`,

`∑_{K'≠K} A(K, K')^m ≤ |{K'≠K : A(K,K') > θ}| · (1/√2)^m + |G|^{log₂|G|+1} · θ^m`.

This is `sum_cosetAffinity_pow_threshold_le` applied to the full candidate set `Subgroup G ∖ {K}`,
with the far-part count `|Subgroup G ∖ {K}| ≤ |Subgroup G| ≤ |G|^{log₂|G|+1}` discharged by the
subgroup-count bound `card_subgroup_le`. The `|G|^{log₂|G|+1} · θ^m` far tail is the concrete term
the Ettinger–Høyer–Knill argument suppresses geometrically; the residual near-count
`|{K'≠K : A(K,K') > θ}|` is the remaining refined-counting ingredient (see the module docstring). -/
theorem sum_cosetAffinity_pow_univ_le [Finite G] [Fintype (Subgroup G)] [DecidableEq (Subgroup G)]
    (K : Subgroup G) (m : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ m
      ≤ ((Finset.univ.erase K).filter fun K' => θ < cosetAffinity K K').card
          * (1 / Real.sqrt 2) ^ m
        + (Nat.card G : ℝ) ^ (Nat.log 2 (Nat.card G) + 1) * θ ^ m := by
  refine (sum_cosetAffinity_pow_threshold_le K m hθ (by simp)).trans ?_
  -- The near terms are identical; only the far constant `|𝒮|` is enlarged to `|G|^{log₂|G|+1}`.
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hθ m))
  -- `|Subgroup G ∖ {K}| ≤ |Subgroup G| ≤ |G|^{log₂|G|+1}`.
  calc ((Finset.univ.erase K).card : ℝ)
      ≤ ((Finset.univ : Finset (Subgroup G)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
    _ = (Nat.card (Subgroup G) : ℝ) := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ (Nat.card G : ℝ) ^ (Nat.log 2 (Nat.card G) + 1) := by exact_mod_cast card_subgroup_le

end AxQM.Concrete
