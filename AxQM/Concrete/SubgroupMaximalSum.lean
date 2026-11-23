/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CosetCollisionSum

/-!
# Concrete: the EHK collision sum — reducing its outer low-index sum to maximal subgroups

This file supplies the **maximal-subgroup reduction** of the *outer* low-index sum that
`Concrete/OvergroupOrderSum.lean` isolated as the one remaining counting ingredient of the
Ettinger–Høyer–Knill identification bound behind Nielsen & Chuang, Problem 5.5 (the non-Abelian
hidden subgroup problem).

## The context

Reindexing the affinity collision sum by the intersection `H = K ∩ K'` and discharging the *inner*
(overgroup) direction sharply (`Concrete.sum_cosetAffinity_pow_collision_proper_le_of_sq`) leaves

`∑_{K'≠K} A(K, K')^{2s} ≤ 1/|G| + 2 · ∑_{H < K} (|H|/|K|)^s`

at N&C's sample exponent (`2·|G|² ≤ 2^s`, i.e. `s = 2 log₂|G| + 1`, `m = 4 log₂|G| + 2 = 2s`). The
**outer** sum `∑_{H < K} (|H|/|K|)^s = ∑_{H < K} [K:H]^{-s}` runs over the *proper subgroups* of `K`
weighted by inverse index. It is the dual, low-index counting direction — **not** reachable by the
overgroup binomial injection (a generating set of the *fixed* `K` over a *varying* `H` does not
recover `H`), and needs a genuinely different combinatorial input: a bound on the number of *large*
subgroups of `K` (subgroups of small index), of Gaussian-binomial strength, which Mathlib does not
have.

## What is proved — the reduction to maximal subgroups

This file does not supply that Gaussian-binomial count; it **reduces** the whole proper-subgroup sum
to a sum over the **maximal** subgroups of `K` (its coatoms `M ⋖ K`) — the classical, far smaller,
far better-studied "probability of generation" quantity — so that only the maximal bound remains.

* `sum_subgroup_ratio_pow_lt_le_maximal_mul` — the **coatom recursion**. Every proper `H < K` lies
  below some maximal subgroup `M ⋖ K` (`exists_le_covBy_of_lt`, from the strong coatomicity of the
  finite subgroup lattice), so summing over the coatoms with multiplicity and factoring the index
  `[K:H] = [K:M]·[M:H]`,

  `∑_{H < K} (|H|/|K|)^s ≤ ∑_{M ⋖ K} (|M|/|K|)^s · (∑_{H ≤ M} (|H|/|M|)^s)`.

  A pure union bound over the coatoms (`Finset.sum_fiberwise_of_maps_to` along a choice of enclosing
  coatom) plus the ratio factoring `(|H|/|K|)^s = (|H|/|M|)^s · (|M|/|K|)^s`.
* `sum_subgroup_ratio_pow_le_le_two_of_maximal` — the **whole-subgroup sum is `≤ 2`** once every
  maximal sum is `≤ 1/2`. Under the hypothesis `∀ J, ∑_{M ⋖ J} (|M|/|J|)^s ≤ 1/2` (the mild
  generation bound — every maximal sum small), strong induction on `|K|` through the coatom
  recursion gives

  `∑_{H ≤ K} (|H|/|K|)^s ≤ 2`

  (the `H = K` term contributes `1`; the proper part is
  `≤ ∑_{M ⋖ K} (|M|/|K|)^s · 2 ≤ 2·(1/2) = 1` by the recursion, the inductive `≤ 2` at each coatom
  `M` — `|M| < |K|` — and the hypothesis).
* `sum_subgroup_ratio_pow_lt_le_two_mul_maximal` — the **usable reduction**. Combining the two,
  under the same hypothesis,

  `∑_{H < K} (|H|/|K|)^s ≤ 2 · ∑_{M ⋖ K} (|M|/|K|)^s`,

  i.e. the proper-subgroup low-index sum is at most twice the maximal-subgroup sum. This is what a
  future *sharp maximal count* plugs into.
* `sum_cosetAffinity_pow_collision_maximal_le_of_sq` — the **composed collision bound**, connecting
  the abstract reduction back to Problem 5.5. Feeding the reduction into
  `sum_cosetAffinity_pow_collision_proper_le_of_sq`, under the same hypothesis and at N&C's sample
  exponent (`2·|G|² ≤ 2^s`),

  `∑_{K'≠K} A(K, K')^{2s} ≤ 1/|G| + 4 · ∑_{M ⋖ K} (|M|/|K|)^s`.

  So the entire remaining counting tail of the Ettinger–Høyer–Knill collision sum is now carried by
  the single **maximal-subgroup** sum `∑_{M ⋖ K} (|M|/|K|)^s`.

## What remains

The reduction isolates one ingredient: a bound `∑_{M ⋖ K} (|M|/|K|)^s ≤ c/|G|` on the
maximal-subgroup low-index sum (which in particular implies the mild `≤ 1/2` hypothesis above). That
is the classical generation-probability quantity — its dominant part is the index-`2` maximals,
whose count `2^{d₂(K)} - 1 < |K|` is elementary, while the higher-index maximals still call for a
Gaussian-binomial-strength count.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

/-- **Index factoring of the order-ratio power.** For subgroups `H, M, K` of `G` (any three; only
`|M| ≠ 0` is used), the order ratio `|H|/|K|` splits multiplicatively through `M`,

`(|H|/|K|)^s = (|H|/|M|)^s · (|M|/|K|)^s`,

the elementary `(a/b)·(b/c) = a/c` (`div_mul_div_cancel₀`, `|M| > 0`) raised to the `s`-th power.
When `H ≤ M ≤ K` this is the index identity `[K:H] = [K:M]·[M:H]` read as
`[K:H]^{-s} = [M:H]^{-s}·[K:M]^{-s}`. -/
private lemma ratio_pow_factor [Finite G] (M K H : Subgroup G) (s : ℕ) :
    ((Nat.card H : ℝ) / Nat.card K) ^ s
      = ((Nat.card H : ℝ) / Nat.card M) ^ s * ((Nat.card M : ℝ) / Nat.card K) ^ s := by
  rw [← mul_pow]
  congr 1
  rw [div_mul_div_cancel₀]
  exact_mod_cast (Nat.card_pos (α := M)).ne'

open Classical in
/-- **The coatom recursion for the proper-subgroup low-index sum.** For a subgroup `K` of a finite
group `G` and an exponent `s`, the low-index sum over the *proper* subgroups `H < K` is bounded by a
sum over the *maximal* subgroups `M ⋖ K` (coatoms of `K`) of the maximal-index weight times the
subgroup sum of that coatom:

`∑_{H < K} (|H|/|K|)^s ≤ ∑_{M ⋖ K} (|M|/|K|)^s · (∑_{H ≤ M} (|H|/|M|)^s)`.

Every proper `H < K` sits below some coatom `M ⋖ K` (`exists_le_covBy_of_lt`, from the strong
coatomicity of the finite subgroup lattice — `Fintype (Subgroup G) ⇒ WellFoundedGT (Subgroup G) ⇒
IsStronglyCoatomic (Subgroup G)`), so choosing one enclosing coatom for each `H` and summing along
the choice map (`Finset.sum_fiberwise_of_maps_to`, an over-count since one `H` may lie below several
coatoms) collects the sum into the coatom fibres; each fibre is a subset of `{H ≤ M}`, and the ratio
factoring `(|H|/|K|)^s = (|H|/|M|)^s·(|M|/|K|)^s` (`ratio_pow_factor`) peels off the coatom weight
`(|M|/|K|)^s`. -/
theorem sum_subgroup_ratio_pow_lt_le_maximal_mul [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) (s : ℕ) :
    ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
        ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s
      ≤ ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
          ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
            * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ M),
                ((Nat.card ↥H : ℝ) / Nat.card ↥M) ^ s := by
  -- Choose, for each `H < K`, a maximal `M ⋖ K` with `H ≤ M` — `exists_le_covBy_of_lt`, via the
  -- strong coatomicity of the finite subgroup lattice (`Fintype (Subgroup G) ⇒ WellFoundedGT`).
  have key : ∀ H : Subgroup G, ∃ M, (H < K → H ≤ M ∧ M ⋖ K) := by
    intro H
    by_cases h : H < K
    · obtain ⟨M, hM⟩ := exists_le_covBy_of_lt h; exact ⟨M, fun _ => hM⟩
    · exact ⟨H, fun h' => absurd h' h⟩
  choose g hg using key
  -- `g` maps every proper subgroup into the coatoms of `K`.
  have hmaps : ∀ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
      g H ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K) := by
    intro H hH
    rw [Finset.mem_filter] at hH ⊢
    exact ⟨Finset.mem_univ _, (hg H hH.2).2⟩
  calc ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
          ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s
      = ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
          ∑ H ∈ (Finset.univ.filter (fun H : Subgroup G => H < K)).filter (fun H => g H = M),
            ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
          ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ M),
            ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := by
        refine Finset.sum_le_sum fun M _ => ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun H _ _ => by positivity)
        intro H hH
        rw [Finset.mem_filter] at hH ⊢
        obtain ⟨hHmem, hgH⟩ := hH
        rw [Finset.mem_filter] at hHmem
        exact ⟨Finset.mem_univ _, hgH ▸ (hg H hHmem.2).1⟩
    _ = ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
          ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
            * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ M),
                ((Nat.card ↥H : ℝ) / Nat.card ↥M) ^ s := by
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun H _ => ?_
        rw [ratio_pow_factor M K H s, mul_comm]

open Classical in
/-- **The whole-subgroup low-index sum is `≤ 2` once every maximal sum is `≤ 1/2`.** For a finite
group `G` and an exponent `s`, if every subgroup `J` has maximal-subgroup low-index sum
`∑_{M ⋖ J} (|M|/|J|)^s ≤ 1/2`, then for every `K`,

`∑_{H ≤ K} (|H|/|K|)^s ≤ 2`.

Proved by strong induction on `|K|` through the coatom recursion
`sum_subgroup_ratio_pow_lt_le_maximal_mul`: the `H = K` term is `1`; each coatom `M ⋖ K` has
`|M| < |K|` (`Set.ncard_lt_ncard`), so the inductive hypothesis gives its inner sum `≤ 2`, whence
the proper part is `≤ ∑_{M ⋖ K} (|M|/|K|)^s · 2 = 2·(∑_{M ⋖ K} (|M|/|K|)^s) ≤ 2·(1/2) = 1`. The
hypothesis is the mild "generation" bound implied by any genuine (`≤ c/|G|`) maximal count. -/
theorem sum_subgroup_ratio_pow_le_le_two_of_maximal [Finite G] [Fintype (Subgroup G)] {s : ℕ}
    (hμ : ∀ J : Subgroup G,
      ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ J),
        ((Nat.card ↥M : ℝ) / Nat.card ↥J) ^ s ≤ 1 / 2)
    (K : Subgroup G) :
    ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K),
        ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s ≤ 2 := by
  suffices H2 : ∀ n (K : Subgroup G), Nat.card ↥K = n →
      ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K),
        ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s ≤ 2 from H2 (Nat.card ↥K) K rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro K hK
    -- Split off the `H = K` term (`(|K|/|K|)^s = 1`) from the subgroup sum.
    have hKmem : K ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _⟩
    have herase : (Finset.univ.filter (fun H : Subgroup G => H ≤ K)).erase K
        = Finset.univ.filter (fun H : Subgroup G => H < K) := by
      ext H
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, lt_iff_le_and_ne]
      tauto
    have hsplit : ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K),
          ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s
        = ((Nat.card ↥K : ℝ) / Nat.card ↥K) ^ s
          + ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
              ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := by
      rw [← herase]; exact (Finset.add_sum_erase _ _ hKmem).symm
    have hKterm : ((Nat.card ↥K : ℝ) / Nat.card ↥K) ^ s = 1 := by
      rw [div_self, one_pow]; exact_mod_cast (Nat.card_pos (α := K)).ne'
    rw [hsplit, hKterm]
    -- Bound the proper sum by `2·(maximal sum) ≤ 1` via the recursion, the IH at each coatom, `hμ`.
    have hprop : ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
        ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s ≤ 1 := by
      refine (sum_subgroup_ratio_pow_lt_le_maximal_mul K s).trans ?_
      calc ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
              ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
                * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ M),
                    ((Nat.card ↥H : ℝ) / Nat.card ↥M) ^ s
          ≤ ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
              ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s * 2 := by
            refine Finset.sum_le_sum fun M hM => ?_
            rw [Finset.mem_filter] at hM
            have hcard : Nat.card ↥M < n := by
              rw [← hK]
              exact Set.ncard_lt_ncard (SetLike.coe_ssubset_coe.mpr hM.2.1) (Set.toFinite _)
            exact mul_le_mul_of_nonneg_left (IH _ hcard M rfl) (by positivity)
        _ = 2 * ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
              ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun M _ => by ring
        _ ≤ 2 * (1 / 2) := mul_le_mul_of_nonneg_left (hμ K) (by norm_num)
        _ = 1 := by norm_num
    linarith

open Classical in
/-- **The proper-subgroup low-index sum is `≤ 2·(maximal-subgroup sum)`.** For a finite group `G`
and an exponent `s`, if every subgroup `J` has maximal-subgroup low-index sum `≤ 1/2`, then for
every `K`,

`∑_{H < K} (|H|/|K|)^s ≤ 2 · ∑_{M ⋖ K} (|M|/|K|)^s`.

The coatom recursion `sum_subgroup_ratio_pow_lt_le_maximal_mul` bounds the left side by
`∑_{M ⋖ K} (|M|/|K|)^s · (∑_{H ≤ M} (|H|/|M|)^s)`; `sum_subgroup_ratio_pow_le_le_two_of_maximal`
bounds each inner factor `∑_{H ≤ M} (|H|/|M|)^s ≤ 2`. This is the usable reduction: it transfers the
whole
remaining low-index count from *all* proper subgroups onto the *maximal* subgroups of `K`. -/
theorem sum_subgroup_ratio_pow_lt_le_two_mul_maximal [Finite G] [Fintype (Subgroup G)] {s : ℕ}
    (hμ : ∀ J : Subgroup G,
      ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ J),
        ((Nat.card ↥M : ℝ) / Nat.card ↥J) ^ s ≤ 1 / 2)
    (K : Subgroup G) :
    ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
        ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s
      ≤ 2 * ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
          ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s := by
  refine (sum_subgroup_ratio_pow_lt_le_maximal_mul K s).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun M _ => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right
    (sum_subgroup_ratio_pow_le_le_two_of_maximal hμ M) (by positivity)

open Classical in
/-- **The affinity collision sum, bounded by the maximal-subgroup sum** (Nielsen & Chuang, Problem
5.5). Feeding the maximal-subgroup reduction `sum_subgroup_ratio_pow_lt_le_two_mul_maximal` into the
diagonal-corrected collision-sum bound `sum_cosetAffinity_pow_collision_proper_le_of_sq`, at N&C's
sample exponent (`2·|G|² ≤ 2^s`, i.e. `s = 2 log₂|G| + 1`, `m = 2s = 4 log₂|G| + 2`) and under the
mild generation hypothesis (`∀ J, ∑_{M ⋖ J} (|M|/|J|)^s ≤ 1/2`),

`∑_{K'≠K} A(K, K')^{2s} ≤ 1/|G| + 4 · ∑_{M ⋖ K} (|M|/|K|)^s`.

So the entire remaining counting tail of the Ettinger–Høyer–Knill collision sum is carried by the
single maximal-subgroup low-index sum `∑_{M ⋖ K} (|M|/|K|)^s`. Driving that below `≤ c/|G|` (the one
missing subgroup count) then makes the collision sum `≤ 1/|G|` at N&C's linear sample count. -/
theorem sum_cosetAffinity_pow_collision_maximal_le_of_sq [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hμ : ∀ J : Subgroup G,
      ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ J),
        ((Nat.card ↥M : ℝ) / Nat.card ↥J) ^ s ≤ 1 / 2) :
    ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * s)
      ≤ (Nat.card G : ℝ)⁻¹
        + 4 * ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ⋖ K),
            ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s := by
  refine (sum_cosetAffinity_pow_collision_proper_le_of_sq K hs).trans ?_
  have hred := sum_subgroup_ratio_pow_lt_le_two_mul_maximal hμ K
  linarith

end AxQM.Concrete
