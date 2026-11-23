/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupSimpleQuotientMaximalSum
import AxQM.Concrete.SimpleQuotientTypeCount

/-!
# Concrete: the aggregated simple-quotient normal-subgroup sum (type-aggregation step)

This file performs the **type-aggregation** that closes the *simple normal-maximal* part of the
residual maximal-subgroup low-index sum `∑_{M ⋖ K} (|M|/|K|)^s` behind the Ettinger–Høyer–Knill
identification bound of Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem).

## The context

`Concrete/SubgroupMaximalSum.lean` reduced the Ettinger–Høyer–Knill collision tail to the
**maximal-subgroup low-index sum** `∑_{M ⋖ K} (|M|/|K|)^s`. Its normal maximals `M` have a *simple*
quotient `K/M`; the **abelian** (prime-index) case is discharged in
`Concrete/SubgroupPrimeIndexNormalCount.lean`, and the residual is the **nonabelian simple**
quotients (index `|Q| ≥ 60`), counted **one quotient type at a time**. Two ingredients feed the
aggregation:

* `Concrete/SubgroupSimpleQuotientMaximalSum.lean` — the **per-type** contribution
  (`sum_fixed_quotient_ratio_pow_le_of_sq`): for a *fixed* finite `Q` with `4 ≤ |Q|`, at N&C's
  sample exponent `2·|G|² ≤ 2^s`, the whole `Q`-fibre `∑_{M ≤ K, K/M ≅ Q} (|M|/|K|)^s ≤ 1/(2|G|²)`;
* `Concrete/SimpleQuotientTypeCount.lean` — the **type-count**
  (`exists_subset_cover_card_le_log_of_simpleQuotient`): *any* family of normal subgroups of a
  finite `H` realises `≤ log₂|H|` distinct simple quotient types (via a pairwise-non-isomorphic
  covering subfamily).

This file combines them: reindexing the sum fibrewise over the `≤ log₂|K|` realised types and
bounding each fibre by `1/(2|G|²)` gives the target `≤ log₂|K| · 1/(2|G|²) ≤ |G| · 1/(2|G|²) =
1/(2|G|)`.

## What is proved

* `sum_simple_quotient_ratio_pow_le_of_sq` — for a subgroup `K ≤ G` of a finite group `G` and N&C's
  sample exponent `2·|G|² ≤ 2^s` (`s ≥ 2 log₂|G| + 1`, `m = 2s = 4 log₂|G| + 2`), the total weight
  of the subgroups `M ≤ K` that are **normal in `K` with a simple quotient `K/M` of order `≥ 4`** is

  `∑_{M ≤ K, K/M simple, |K/M| ≥ 4} (|M|/|K|)^s ≤ 1/(2|G|)`.

  This is the aggregation across quotient *types*: a `Finset.sum_fiberwise` over a set of
  `≤ log₂|K|` type-representatives (`exists_subset_cover_card_le_log_of_simpleQuotient`), bounding
  each type's fibre by `sum_fixed_quotient_ratio_pow_le_of_sq` (`≤ 1/(2|G|²)`), then
  `log₂|K| ≤ |G|`. It is deliberately stated over *all* simple normal quotients of order `≥ 4`
  rather than the nonabelian-simple maximals specifically — the order threshold `|Q| ≥ 4` (met by
  every nonabelian simple `Q`, `|Q| ≥ 60`) is exactly what the per-type bound needs, and neither
  simplicity of the sum nor a maximality (coatom) hypothesis is required, so the statement is the
  natural reusable form that *contains* the nonabelian-simple normal maximals as a subset (all
  weights are nonnegative, so the subset sum inherits the bound). The quotient conditions are
  phrased through the canonical quotient `↥K ⧸ (M.subgroupOf K)`, with the required normality
  supplied inside the filter predicate via an existential over the `Normal` instance.
-/

namespace AxQM.Concrete

variable {G : Type*} [Group G]

open Classical in
/-- **The simple normal-maximal sum aggregated over quotient types is `≤ 1/(2|G|)`.** For a subgroup
`K ≤ G` of a finite group `G` and N&C's sample exponent `2·|G|² ≤ 2^s` (`s ≥ 2 log₂|G| + 1`,
`m = 2s = 4 log₂|G| + 2`), the total weight of the subgroups `M ≤ K` whose relative subgroup
`M.subgroupOf K` is normal in `↥K` with **simple** quotient `↥K ⧸ (M.subgroupOf K)` of **order
`≥ 4`** is

`∑ (|M|/|K|)^s ≤ 1/(2|G|)`.

The proof reindexes the sum fibrewise over a set of `≤ log₂|K|` quotient-type representatives
(`exists_subset_cover_card_le_log_of_simpleQuotient` — an arbitrary family of normal subgroups with
simple quotients realises `≤ log₂|K|` distinct types), bounds each type's whole fibre by
`sum_fixed_quotient_ratio_pow_le_of_sq` (`≤ 1/(2|G|²)`, using `4 ≤ |Q|` and the sample exponent),
and closes with `log₂|K| ≤ |K| ≤ |G|`: `log₂|K| · 1/(2|G|²) ≤ |G| · 1/(2|G|²) = 1/(2|G|)`. Each
representative `j` supplies a fixed target `Q₀ = ↥K ⧸ (j.1.subgroupOf K)`, and every fibre member
`M` maps into the fixed-quotient fibre of `Q₀` by transporting its chosen quotient isomorphism
(`QuotientGroup.congr`) into a surjection `↥K →* Q₀` with kernel `M.subgroupOf K`. Applied at a
nonabelian simple quotient (`|Q| ≥ 60 ≥ 4`) this is the residual nonabelian-simple normal-maximal
part of the maximal-subgroup sum. -/
theorem sum_simple_quotient_ratio_pow_le_of_sq [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    ∑ M ∈ Finset.univ.filter
        (fun M : Subgroup G => M ≤ K ∧
          ∃ _ : (M.subgroupOf K).Normal,
            IsSimpleGroup (↥K ⧸ M.subgroupOf K) ∧ 4 ≤ Nat.card (↥K ⧸ M.subgroupOf K)),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ (2 * Nat.card G : ℝ)⁻¹ := by
  classical
  set P := (fun M : Subgroup G => M ≤ K ∧
      ∃ _ : (M.subgroupOf K).Normal,
        IsSimpleGroup (↥K ⧸ M.subgroupOf K) ∧ 4 ≤ Nat.card (↥K ⧸ M.subgroupOf K)) with hPdef
  have hwnn : ∀ M : Subgroup G, 0 ≤ ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s := fun M => by positivity
  -- Move the sum to the subtype `SubT` of the (normal, simple, order-≥4) family.
  have hmemP : ∀ x : Subgroup G, x ∈ Finset.univ.filter P ↔ P x := by
    intro x; simp [Finset.mem_filter]
  have hsub : (∑ M ∈ Finset.univ.filter P, ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s)
      = ∑ i : {M : Subgroup G // P M}, ((Nat.card ↥(i.1) : ℝ) / Nat.card ↥K) ^ s :=
    Finset.sum_subtype (Finset.univ.filter P) hmemP _
  rw [hsub]
  set SubT := {M : Subgroup G // P M} with hSubT
  have hnorm : ∀ i : SubT, (i.1.subgroupOf K).Normal := fun i => i.2.2.choose
  have : ∀ i : SubT, (i.1.subgroupOf K).Normal := hnorm
  have hsimple : ∀ i ∈ (Finset.univ : Finset SubT), IsSimpleGroup (↥K ⧸ i.1.subgroupOf K) :=
    fun i _ => i.2.2.choose_spec.1
  -- Covering subfamily `r`: one representative per realised quotient type, `#r ≤ log₂|K|`.
  obtain ⟨r, _hrs, hcov, hrcard⟩ :=
    exists_subset_cover_card_le_log_of_simpleQuotient (H := ↥K)
      (fun i : SubT => i.1.subgroupOf K) Finset.univ hsimple
  -- The representative-choosing function on the subtype (into `r`).
  set ψ : SubT → SubT := fun i => (hcov i (Finset.mem_univ _)).choose with hψdef
  have hψmem : ∀ i ∈ (Finset.univ : Finset SubT), ψ i ∈ r :=
    fun i _ => (hcov i (Finset.mem_univ _)).choose_spec.1
  have hψiso : ∀ i : SubT,
      Nonempty (↥K ⧸ i.1.subgroupOf K ≃* ↥K ⧸ (ψ i).1.subgroupOf K) :=
    fun i => (hcov i (Finset.mem_univ _)).choose_spec.2
  -- Fiberwise reindexing over the representatives.
  rw [← Finset.sum_fiberwise_of_maps_to hψmem
      (fun i : SubT => ((Nat.card ↥(i.1) : ℝ) / Nat.card ↥K) ^ s)]
  -- Bound each representative's fibre by the per-type contribution `≤ 1/(2|G|²)`.
  have hfib : ∀ j ∈ r,
      ∑ i ∈ Finset.univ.filter (fun i : SubT => ψ i = j),
          ((Nat.card ↥(i.1) : ℝ) / Nat.card ↥K) ^ s
        ≤ (2 * Nat.card G ^ 2 : ℝ)⁻¹ := by
    intro j _hjr
    have hjN : (j.1.subgroupOf K).Normal := hnorm j
    have hQ4 : 4 ≤ Nat.card (↥K ⧸ j.1.subgroupOf K) := j.2.2.choose_spec.2
    -- Inject the fibre (image under `Subtype.val`) into the fixed-quotient fibre for
    -- `Q₀ = ↥K ⧸ (j.1.subgroupOf K)`.
    have himg : (Finset.univ.filter (fun i : SubT => ψ i = j)).image Subtype.val ⊆
        Finset.univ.filter (fun M : Subgroup G => M ≤ K ∧
          ∃ χ : ↥K →* (↥K ⧸ j.1.subgroupOf K), Function.Surjective χ ∧
            χ.ker = M.subgroupOf K) := by
      intro M hM
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hM
      rw [Finset.mem_filter] at hi
      have hij : ψ i = j := hi.2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, i.2.1, ?_⟩
      -- transport the iso `↥K/(i.1.subgroupOf K) ≃* ↥K/((ψ i).1.subgroupOf K)` to the target `j`.
      obtain ⟨e'⟩ := hψiso i
      have hsubeq : (ψ i).1.subgroupOf K = j.1.subgroupOf K := by rw [hij]
      let etr : (↥K ⧸ (ψ i).1.subgroupOf K) ≃* (↥K ⧸ j.1.subgroupOf K) :=
        QuotientGroup.congr _ _ (MulEquiv.refl ↥K) (by simpa using hsubeq)
      let e : (↥K ⧸ i.1.subgroupOf K) ≃* (↥K ⧸ j.1.subgroupOf K) := e'.trans etr
      refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (i.1.subgroupOf K)), ?_, ?_⟩
      · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
      · have hkc : (e.toMonoidHom.comp (QuotientGroup.mk' (i.1.subgroupOf K))).ker
            = (QuotientGroup.mk' (i.1.subgroupOf K)).ker := by
          ext x
          simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
            map_eq_one_iff e e.injective]
        rw [hkc, QuotientGroup.ker_mk']
    calc ∑ i ∈ Finset.univ.filter (fun i : SubT => ψ i = j),
            ((Nat.card ↥(i.1) : ℝ) / Nat.card ↥K) ^ s
        = ∑ M ∈ (Finset.univ.filter (fun i : SubT => ψ i = j)).image Subtype.val,
            ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s := by
          rw [Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
      _ ≤ ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ≤ K ∧
            ∃ χ : ↥K →* (↥K ⧸ j.1.subgroupOf K), Function.Surjective χ ∧
              χ.ker = M.subgroupOf K),
            ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun M _ _ => hwnn M)
      _ ≤ (2 * Nat.card G ^ 2 : ℝ)⁻¹ :=
          sum_fixed_quotient_ratio_pow_le_of_sq K (↥K ⧸ j.1.subgroupOf K) hQ4 hs
  -- Sum the per-fibre bounds over the `≤ log₂|K| ≤ |G|` representatives.
  refine (Finset.sum_le_card_nsmul r _ _ hfib).trans ?_
  rw [nsmul_eq_mul]
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hrCard : (r.card : ℝ) ≤ Nat.card G := by
    have h3 : Nat.log 2 (Nat.card ↥K) ≤ Nat.card ↥K := Nat.log_le_self 2 _
    have h4 : Nat.card ↥K ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card K)
    have : r.card ≤ Nat.card G := le_trans hrcard (le_trans h3 h4)
    exact_mod_cast this
  calc (r.card : ℝ) * (2 * Nat.card G ^ 2 : ℝ)⁻¹
      ≤ (Nat.card G : ℝ) * (2 * Nat.card G ^ 2 : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hrCard (by positivity)
    _ = (2 * Nat.card G : ℝ)⁻¹ := by rw [eq_comm]; field_simp

end AxQM.Concrete
