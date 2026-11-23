/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.OvergroupOrderSum

/-!
# Concrete: the Ettinger–Høyer–Knill collision sum — reduction to the outer low-index sum

This file performs the **reindexing assembly** of the Ettinger–Høyer–Knill identification bound
behind Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem). Identifying the
hidden subgroup `K` from the `m`-copy coset reduced state `σ_K^{⊗m}` requires controlling the
collision sum over all candidate hidden subgroups `K'` of the pairwise affinity,

`∑_{K'≠K} A(K, K')^{2s}`,   `A(K, K') = |K∩K'| / √(|K|·|K'|)`

(`AxQM.Concrete.cosetAffinity`, `AxQM.cosetDensityState_pi_affinity`; the even
exponent `2s` matches N&C's sample count `m = 4 log₂|G| + 2 = 2·(2 log₂|G| + 1)`). The inner
(overgroup) geometric sum has been discharged **sharply** in
`AxQM.Concrete.OvergroupOrderSum` — for a fixed intersection `H = K ∩ K'`,

`∑_{K' : K∩K' = H} A(K, K')^{2s} ≤ (|H|/|K|)^s · 2`   (`sum_cosetAffinity_pow_inter_le`),

an **absolute** constant `2` with no factor of `|G|`. This file collects those per-intersection
bounds — one for each intersection `H ≤ K` — into the full collision sum.

## What is proved

* `sum_cosetAffinity_pow_collision_le` — the **collision-sum reduction**. For a subgroup `K` of a
  finite group `G` and an exponent `s` with `2·|G| ≤ 2^s`,

  `∑_{K'≠K} A(K, K')^{2s} ≤ 2 · ∑_{H ≤ K} (|H|/|K|)^s`.

  Every candidate `K'` has intersection `K ∩ K' ≤ K`, so the map `K' ↦ K ∩ K'` fibres the whole
  candidate lattice over the subgroups `H ≤ K`. Reindexing the sum along that map
  (`Finset.sum_fiberwise_of_maps_to`) and bounding each fibre by the sharp per-intersection
  contribution `sum_cosetAffinity_pow_inter_le` turns the collision sum into `2` times the
  **outer** sum over the *sub*groups of `K`.

* `sum_cosetAffinity_pow_collision_proper_le` — the **diagonal-corrected reduction**. The bound
  above is `≥ 2` (the `H = K` term alone contributes `(|K|/|K|)^s · 2 = 2`), because the sharp `≤ 2`
  per-intersection factor does not peel off the trivial `K' = K` diagonal. Peeling the `H = K` fibre
  off exactly (`Finset.add_sum_erase`) and bounding it instead by its **true** proper-overgroup tail
  `∑_{K'⊋K}(|K|/|K'|)^s ≤ 2·|G|·2^{-s}` (`sum_proper_overgroup_ratio_pow_le`, `OvergroupOrderSum`)
  replaces that `2` with a term that vanishes with `s`:

  `∑_{K'≠K} A(K, K')^{2s} ≤ 2·|G|·2^{-s} + 2 · ∑_{H < K} (|H|/|K|)^s`.

* `sum_cosetAffinity_pow_collision_proper_le_of_sq` — at N&C's sample exponent `s = 2 log₂|G| + 1`
  (`2·|G|² ≤ 2^s`) the `H = K` term `2·|G|·2^{-s}` is `≤ 1/|G|`, so
  `∑_{K'≠K} A(K, K')^{2s} ≤ 1/|G| + 2·∑_{H < K} (|H|/|K|)^s` — the `H = K` contribution already
  inside the identification clause's `1/|G|` budget, leaving only the proper-subgroup outer sum.

## The role in the full bound — and what remains

This is the exact reduction both `OvergroupOrderSum.lean` and the statement of Problem 5.5
(`AxQM/NC/Ch5/Problem5_5.lean`) describe in prose ("summing over `H ≤ K` reduces the full sum to
`2·∑_{H ≤ K} (|H|/|K|)^s`"), now a theorem.
It isolates the **one remaining ingredient** of the Ettinger–Høyer–Knill counting tail: the
**outer low-index sum** `∑_{H ≤ K} (|H|/|K|)^s = ∑_{H ≤ K} [K:H]^{-s}`, a sum over the *sub*groups
of `K` weighted by inverse index. That outer sum is the **dual** counting direction, and — as
`OvergroupOrderSum.lean` explains — it is **not** reachable by the binomial /
relative-generating-set injection used for the inner sum: there
`K' ↦ (generating set of K' over the fixed H)` is injective because the closure recovers `K'`,
whereas here `H` varies *below* the fixed `K` and a generating set of `K` over `H` does not recover
`H`. Bounding it needs a genuinely different combinatorial input (a bound on the number of *large*
subgroups of `K`, i.e. subgroups of small index — sharp subgroup-index growth, of
Gaussian-binomial strength: the crude generating-set and homomorphism counts are both too loose to
keep the sample count linear).

The first of the two tightening steps is now done here:
`sum_cosetAffinity_pow_collision_proper_le` replaces the loose `H = K` term `2` with its true tail
`∑_{K' ⊋ K} (|K|/|K'|)^s ≤ 2·|G|·2^{-s}`, so at N&C's linear sample exponent `s = 2 log₂|G| + 1` the
collision sum is `≤ 1/|G| + 2·∑_{H < K} (|H|/|K|)^s`
(`sum_cosetAffinity_pow_collision_proper_le_of_sq`). The **one remaining step** is then the
outer sum over the *proper* subgroups `∑_{H < K} (|H|/|K|)^s`, whose bound drives the collision sum
below `1/|G|` — the dual, low-index counting direction described above.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

open Classical in
/-- **The Ettinger–Høyer–Knill collision-sum reduction** (Nielsen & Chuang, Problem 5.5). For a
subgroup `K` of a finite group `G` and an exponent `s` with `2·|G| ≤ 2^s`, the affinity collision
sum over all candidate hidden subgroups `K' ≠ K` reduces to twice the outer low-index sum over the
subgroups of `K`:

`∑_{K'≠K} A(K, K')^{2s} ≤ 2 · ∑_{H ≤ K} (|H|/|K|)^s`.

Every candidate `K'` has intersection `K ∩ K' ≤ K`, so the map `K' ↦ K ∩ K'` fibres the candidate
lattice `Subgroup G` over the subgroups `H ≤ K`. Reindexing the sum along it
(`Finset.sum_fiberwise_of_maps_to`, after dropping the `K' = K` term whose omission only decreases
the nonnegative sum) and bounding each fibre `∑_{K' : K∩K' = H} A^{2s}` by the sharp
per-intersection contribution `sum_cosetAffinity_pow_inter_le` (`≤ (|H|/|K|)^s · 2`, whose inner
geometric sum is the absolute-constant `sum_overgroup_ratio_pow_le`) leaves `2` times the sum over
`H ≤ K`.

This is the exact reduction stated in prose by `OvergroupOrderSum.lean` and in the statement of
Problem 5.5 (`AxQM/NC/Ch5/Problem5_5.lean`), now a theorem. It isolates the **outer low-index sum**
`∑_{H ≤ K} (|H|/|K|)^s` (equivalently `∑_{H ≤ K} [K:H]^{-s}`, over the *sub*groups of `K`) as the
one remaining ingredient — the dual, low-index counting direction, not reachable by the inner sum's
generating-set injection. The bound is the honest reduction, not the final estimate: its right side
is `≥ 2` because the `H = K` term is `(|K|/|K|)^s · 2 = 2` (the sharp per-intersection factor does
not peel off the trivial `K' = K` diagonal); sharpening the `H = K` fibre and the proper-subgroup
outer sum are the remaining steps to the collision sum's `≤ 1/|G|` bound at N&C's linear sample
count `m = 4 log₂|G| + 2`. -/
theorem sum_cosetAffinity_pow_collision_le [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ≤ 2 ^ s) :
    ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * s)
      ≤ 2 * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K),
          ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := by
  -- The fibre map `K' ↦ K ⊓ K'` lands in the subgroups of `K` (`K ⊓ K' ≤ K`).
  have hmaps : ∀ K' ∈ (Finset.univ : Finset (Subgroup G)), K ⊓ K' ∈
      Finset.univ.filter (fun H : Subgroup G => H ≤ K) :=
    fun K' _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, inf_le_left⟩
  calc ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * s)
      -- Drop the `K' = K` term: the remaining candidate sum over all of `Subgroup G` is larger,
      -- every summand being a nonnegative even power of `cosetAffinity`.
      ≤ ∑ K' ∈ (Finset.univ : Finset (Subgroup G)), cosetAffinity K K' ^ (2 * s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun K' _ _ => pow_nonneg (cosetAffinity_nonneg K K') _)
      -- Reindex the candidate sum by the intersection `H = K ⊓ K'`.
    _ = ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K),
          ∑ K' ∈ Finset.univ.filter (fun K' => K ⊓ K' = H), cosetAffinity K K' ^ (2 * s) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      -- Bound each fibre by the sharp per-intersection contribution `(|H|/|K|)^s · 2`.
    _ ≤ ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K),
          2 * ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s :=
        Finset.sum_le_sum fun H _ =>
          (sum_cosetAffinity_pow_inter_le K H hs).trans_eq (mul_comm _ _)
    _ = 2 * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K),
          ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := by rw [Finset.mul_sum]

open Classical in
/-- **The diagonal-corrected Ettinger–Høyer–Knill collision-sum reduction** (Nielsen & Chuang,
Problem 5.5). For a subgroup `K` of a finite group `G` and an exponent `s` with `2·|G| ≤ 2^s`, the
affinity collision sum over the candidate hidden subgroups `K' ≠ K` splits into its `H = K` fibre —
now bounded by its **true** proper-overgroup tail, not the loose per-intersection factor `2` — and
the outer sum over the **proper** subgroups `H < K`:

`∑_{K'≠K} A(K, K')^{2s} ≤ 2·|G|·2^{-s} + 2 · ∑_{H < K} (|H|/|K|)^s`.

This sharpens `sum_cosetAffinity_pow_collision_le` (`≤ 2·∑_{H ≤ K} (|H|/|K|)^s`) by handling the
`H = K` fibre **exactly**. Reindexing the candidate sum `∑_{K'≠K}` along `K' ↦ K ∩ K'` fibres it
over the subgroups `H ≤ K` (`Finset.sum_fiberwise_of_maps_to`); peeling off the `H = K` fibre
(`Finset.add_sum_erase`) leaves the proper fibres `H < K`. The `H = K` fibre is exactly the
candidates `K' ⊋ K` — since `K ∩ K' = K ↔ K ≤ K'` (`inf_eq_left`) and the trivial `K' = K` diagonal
is dropped by the `erase` — on which `A(K, K')^{2s} = (|K|/|K'|)^s`, so it equals the
proper-overgroup order-sum `∑_{K'⊋K}(|K|/|K'|)^s ≤ 2·|G|·2^{-s}`
(`sum_proper_overgroup_ratio_pow_le` at `H = K`), **not** the loose `2`. Each proper fibre `H < K`
is bounded, as in `sum_cosetAffinity_pow_collision_le`, by the sharp per-intersection contribution
`sum_cosetAffinity_pow_inter_le` (`≤ (|H|/|K|)^s·2`).

Where the earlier reduction's right side was `≥ 2` (useless — the `H = K` term alone contributed
`2`), this one's first term `2·|G|·2^{-s}` is `≤ 1/|G|` at N&C's sample exponent `s = 2 log₂|G| + 1`
(so `2^s = 2·|G|²`; see `sum_cosetAffinity_pow_collision_proper_le_of_sq`). It thus isolates the
**one remaining ingredient** cleanly and with the right constants: the outer low-index sum
`∑_{H < K} (|H|/|K|)^s` over the *proper* subgroups of `K` — the dual counting direction not
reachable by the inner sum's generating-set injection (see `OvergroupOrderSum.lean`). -/
theorem sum_cosetAffinity_pow_collision_proper_le [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ≤ 2 ^ s) :
    ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * s)
      ≤ 2 * (Nat.card G : ℝ) * ((2 : ℝ) ^ s)⁻¹
        + 2 * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
            ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := by
  -- The fibre map `K' ↦ K ⊓ K'` sends every candidate to a subgroup `H ≤ K`.
  have hmaps : ∀ K' ∈ Finset.univ.erase K, K ⊓ K' ∈
      Finset.univ.filter (fun H : Subgroup G => H ≤ K) :=
    fun K' _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, inf_le_left⟩
  have hKmem : K ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl K⟩
  -- `{H ≤ K}.erase K = {H < K}`.
  have herase : (Finset.univ.filter (fun H : Subgroup G => H ≤ K)).erase K
      = Finset.univ.filter (fun H : Subgroup G => H < K) := by
    ext H
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, lt_iff_le_and_ne]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  -- **`H = K` fibre**: `∑_{K'∈erase K, K⊓K'=K} A^{2s} = ∑_{K'⊋K}(|K|/|K'|)^s ≤ 2·|G|·2^{-s}`.
  have hFK : ∑ K' ∈ (Finset.univ.erase K).filter (fun K' => K ⊓ K' = K),
        cosetAffinity K K' ^ (2 * s)
      ≤ 2 * (Nat.card G : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    have hset : (Finset.univ.erase K).filter (fun K' : Subgroup G => K ⊓ K' = K)
        = Finset.univ.filter (fun K' : Subgroup G => K < K') := by
      ext K'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
        inf_eq_left, lt_iff_le_and_ne]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, fun h => h1 h.symm⟩, fun ⟨h1, h2⟩ => ⟨fun h => h2 h.symm, h1⟩⟩
    rw [hset]
    -- On `K < K'` the intersection is `K`, so `A(K,K')^{2s} = (A²)^s = (|K|/|K'|)^s`.
    have hval : ∀ K' ∈ Finset.univ.filter (fun K' : Subgroup G => K < K'),
        cosetAffinity K K' ^ (2 * s) = ((Nat.card ↥K : ℝ) / Nat.card ↥K') ^ s :=
      fun K' hK' => by rw [pow_mul, cosetAffinity_sq_of_le (Finset.mem_filter.mp hK').2.le]
    rw [Finset.sum_congr rfl hval]
    exact sum_proper_overgroup_ratio_pow_le K hs
  -- **Proper fibres `H < K`**: each `≤ (|H|/|K|)^s·2`, so their sum `≤ 2·∑_{H<K}(|H|/|K|)^s`.
  have hFprop : ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
        ∑ K' ∈ (Finset.univ.erase K).filter (fun K' => K ⊓ K' = H),
          cosetAffinity K K' ^ (2 * s)
      ≤ 2 * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
          ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun H _ => ?_
    calc ∑ K' ∈ (Finset.univ.erase K).filter (fun K' => K ⊓ K' = H),
            cosetAffinity K K' ^ (2 * s)
        ≤ ∑ K' ∈ Finset.univ.filter (fun K' : Subgroup G => K ⊓ K' = H),
            cosetAffinity K K' ^ (2 * s) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
            (fun K' _ _ => pow_nonneg (cosetAffinity_nonneg K K') _)
      _ ≤ ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s * 2 := sum_cosetAffinity_pow_inter_le K H hs
      _ = 2 * ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := mul_comm _ _
  -- Reindex by the intersection, peel off the `H = K` fibre, and combine.
  calc ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * s)
      = ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H ≤ K),
          ∑ K' ∈ (Finset.univ.erase K).filter (fun K' => K ⊓ K' = H),
            cosetAffinity K K' ^ (2 * s) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = (∑ K' ∈ (Finset.univ.erase K).filter (fun K' => K ⊓ K' = K),
            cosetAffinity K K' ^ (2 * s))
          + ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
              ∑ K' ∈ (Finset.univ.erase K).filter (fun K' => K ⊓ K' = H),
                cosetAffinity K K' ^ (2 * s) := by
        rw [← herase]; exact (Finset.add_sum_erase _ _ hKmem).symm
    _ ≤ 2 * (Nat.card G : ℝ) * ((2 : ℝ) ^ s)⁻¹
          + 2 * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
              ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := add_le_add hFK hFprop

open Classical in
/-- **At N&C's sample exponent the `H = K` fibre is within the `1/|G|` budget** (Nielsen & Chuang,
Problem 5.5). Strengthening the hypothesis of `sum_cosetAffinity_pow_collision_proper_le` from
`2·|G| ≤ 2^s` to `2·|G|² ≤ 2^s` — i.e. `s ≥ 2 log₂|G| + 1`, exactly the exponent behind N&C's
sample count `m = 4 log₂|G| + 2 = 2·(2 log₂|G| + 1)` — makes the `H = K` proper-overgroup tail
`2·|G|·2^{-s}` itself `≤ 1/|G|`:

`∑_{K'≠K} A(K, K')^{2s} ≤ 1/|G| + 2 · ∑_{H < K} (|H|/|K|)^s`.

So at N&C's linear sample count the entire `H = K` contribution already sits inside the
identification clause's `1/|G|` error budget, and the **sole** remaining term is the outer low-index
sum over the *proper* subgroups `2·∑_{H < K} (|H|/|K|)^s` — the one Ettinger–Høyer–Knill counting
ingredient still to be bounded (see `OvergroupOrderSum.lean` and `AxQM/NC/Ch5/Problem5_5.lean`). -/
theorem sum_cosetAffinity_pow_collision_proper_le_of_sq [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    ∑ K' ∈ Finset.univ.erase K, cosetAffinity K K' ^ (2 * s)
      ≤ (Nat.card G : ℝ)⁻¹
        + 2 * ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => H < K),
            ((Nat.card ↥H : ℝ) / Nat.card ↥K) ^ s := by
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hGne : (Nat.card G : ℝ) ≠ 0 := hGpos.ne'
  -- `2·|G| ≤ 2·|G|² ≤ 2^s`, so the main reduction applies.
  have hs' : 2 * Nat.card G ≤ 2 ^ s := by
    have hle : Nat.card G ≤ Nat.card G ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  refine (sum_cosetAffinity_pow_collision_proper_le K hs').trans ?_
  gcongr
  -- `2·|G|·(2^s)⁻¹ ≤ |G|⁻¹`, since `2·|G|·|G| = 2·|G|² ≤ 2^s`.
  have hle : (Nat.card G : ℝ)⁻¹ = 2 * (Nat.card G : ℝ) * (2 * (Nat.card G : ℝ) ^ 2)⁻¹ := by
    field_simp
  rw [hle]
  gcongr
  exact_mod_cast hs

end AxQM.Concrete
