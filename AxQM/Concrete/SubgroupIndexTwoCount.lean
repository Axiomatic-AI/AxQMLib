/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Map
import AxQM.Concrete.SubgroupIndexCount

/-!
# Concrete: how many index-two subgroups a finite group has

This file supplies the **elementary index-`2` count** that `Concrete/SubgroupMaximalSum.lean`
isolated as the dominant part of the one remaining counting ingredient of the Ettinger–Høyer–Knill
identification bound behind Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem).

## The context

`Concrete/SubgroupMaximalSum.lean` reduced the Ettinger–Høyer–Knill collision tail to the single
**maximal-subgroup low-index sum** `∑_{M ⋖ K} (|M|/|K|)^s = ∑_{M ⋖ K} [K:M]^{-s}`, whose dominant
part — the index-`2` maximals — the docstring there flagged as *elementary*: an index-`2` subgroup
of `K` contributes the maximal per-copy weight `(1/2)^s` (the smallest possible index, hence the
largest weight), so bounding this part needs only a bound on the **number** of index-`2` subgroups.
The higher-index maximals decay faster but still call for the sharper Gaussian-binomial-strength
count; this file discharges the index-`2` part.

## What is proved

* `signChar` — the real **sign character** `χ_H : G →* ℝ` of an index-`2` subgroup `H`, sending an
  element to `1` if it lies in `H` and to `-1` otherwise. It is a genuine monoid homomorphism
  because `H` has index `2`: a product lies in `H` iff its two factors have the *same* membership
  status (`Subgroup.mul_mem_iff_of_index_two`), which is exactly the `±1` multiplication rule. Its
  fibre over `1` recovers `H` (`signChar_apply_eq_one_iff`), so distinct index-`2` subgroups give
  distinct characters (`signChar_injective`).
* `card_index_two_subgroup_le` — **the number of index-`2` subgroups of a finite group `G` is at
  most `|G|`.** The sign characters inject the index-`2` subgroups into the monoid homomorphisms
  `G →* ℝ`, and by **Dedekind's linear independence of characters** (`linearIndependent_monoidHom`)
  those homomorphisms are linearly independent in the `|G|`-dimensional real function space
  `G → ℝ`, so there are at most `|G|` of them (`LinearIndependent.cardinalMk_le_finrank`,
  `Module.finrank_pi`).
* `card_relIndex_two_subgroup_le` — the **relative** form: the number of subgroups `M ≤ K` of
  relative index `[K:M] = 2` is at most `|K|`. These are exactly the index-`2` subgroups of `↥K`
  (`Subgroup.subgroupOf`, injective on subgroups `≤ K` via `Subgroup.map_subgroupOf_eq_of_le`),
  so the previous count applied to `↥K` bounds them by `|K|`.
* `sum_index_two_maximal_ratio_pow_le` — the **index-`2` part of the maximal-subgroup sum**. Every
  relative-index-`2` subgroup `M ≤ K` has weight `(|M|/|K|)^s = (1/2)^s`, and there are at most
  `|K|` of them, so `∑_{M ≤ K, [K:M] = 2} (|M|/|K|)^s ≤ |K| · (1/2)^s`.
* `sum_index_two_maximal_ratio_pow_le_of_sq` — its value at N&C's sample exponent: once
  `2·|G|² ≤ 2^s`, the index-`2` part is `≤ 1/(2|G|)`. This is the elementary half of the maximal
  sum's `≤ c/|G|` target; the higher-index maximals are the residual (Gaussian-binomial-strength)
  ingredient.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

open Classical in
/-- **The real sign character of an index-two subgroup.** For a subgroup `H` of index `2`, the map
`χ_H : G →* ℝ` sends `g` to `1` if `g ∈ H` and to `-1` otherwise. It is multiplicative because for
an index-`2` subgroup `g₁ g₂ ∈ H ↔ (g₁ ∈ H ↔ g₂ ∈ H)` (`Subgroup.mul_mem_iff_of_index_two`), the
`±1` multiplication rule. -/
noncomputable def signChar (H : Subgroup G) (hH : H.index = 2) : G →* ℝ where
  toFun g := if g ∈ H then 1 else -1
  map_one' := by simp
  map_mul' a b := by
    rw [Subgroup.mul_mem_iff_of_index_two hH]
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ha, hb]

/-- The sign character of an index-`2` subgroup `H` takes the value `1` exactly on `H`: its fibre
over `1` recovers `H`. -/
lemma signChar_apply_eq_one_iff (H : Subgroup G) (hH : H.index = 2) (g : G) :
    signChar H hH g = 1 ↔ g ∈ H := by
  classical
  unfold signChar
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  by_cases hg : g ∈ H
  · simp [hg]
  · simp only [hg, ite_false]
    norm_num

/-- Distinct index-`2` subgroups have distinct sign characters, since each subgroup is the fibre of
its character over `1` (`signChar_apply_eq_one_iff`). -/
lemma signChar_injective :
    Function.Injective
      (fun p : {H : Subgroup G // H.index = 2} => signChar p.1 p.2) := by
  rintro ⟨H1, h1⟩ ⟨H2, h2⟩ heq
  simp only at heq
  ext g
  rw [← signChar_apply_eq_one_iff H1 h1 g, ← signChar_apply_eq_one_iff H2 h2 g, heq]

/-- **The number of index-two subgroups of a finite group is at most its order.** The sign
characters `signChar` inject the index-`2` subgroups into the monoid homomorphisms `G →* ℝ`, which
by Dedekind's linear independence of characters (`linearIndependent_monoidHom`) are linearly
independent in the `|G|`-dimensional space `G → ℝ`, hence number at most `|G|`. -/
theorem card_index_two_subgroup_le [Finite G] :
    Nat.card {H : Subgroup G // H.index = 2} ≤ Nat.card G := by
  have hfin : Fintype G := Fintype.ofFinite G
  -- Dedekind independence: the homs `G →* ℝ` are linearly independent as functions.
  have hli : LinearIndependent ℝ (fun f : (G →* ℝ) => (f : G → ℝ)) :=
    linearIndependent_monoidHom G ℝ
  have hcard : Cardinal.mk (G →* ℝ) ≤ (Module.finrank ℝ (G → ℝ) : Cardinal) :=
    hli.cardinalMk_le_finrank
  have hfr : Module.finrank ℝ (G → ℝ) = Nat.card G := by
    rw [Module.finrank_pi, Nat.card_eq_fintype_card]
  rw [hfr] at hcard
  -- So there are finitely many, at most `|G|`, homs `G →* ℝ`.
  have : Finite (G →* ℝ) :=
    Cardinal.lt_aleph0_iff_finite.mp (lt_of_le_of_lt hcard Cardinal.natCast_lt_aleph0)
  have hhom : Nat.card (G →* ℝ) ≤ Nat.card G := by
    have := Cardinal.toNat_le_toNat hcard Cardinal.natCast_lt_aleph0
    rwa [Cardinal.toNat_natCast] at this
  -- The sign characters inject the index-`2` subgroups into `G →* ℝ`.
  exact (Nat.card_le_card_of_injective _ signChar_injective).trans hhom

/-- **The number of subgroups of relative index two below `K` is at most `|K|`.** These are exactly
the index-`2` subgroups of the group `↥K` (`Subgroup.subgroupOf`, injective on subgroups `≤ K`), so
`card_index_two_subgroup_le` applied to `↥K` bounds them by `|K|`. -/
theorem card_relIndex_two_subgroup_le [Finite G] (K : Subgroup G) :
    Nat.card {M : Subgroup G // M ≤ K ∧ M.relIndex K = 2} ≤ Nat.card ↥K := by
  have hfin : Finite ↥K := Subtype.finite
  have : Finite (Subgroup ↥K) := Finite.of_injective _ SetLike.coe_injective
  -- `M ↦ M.subgroupOf K` sends a relative-index-`2` subgroup below `K` to an index-`2` subgroup of
  -- `↥K`, and is injective on subgroups `≤ K` (`map_subgroupOf_eq_of_le` is a left inverse).
  have hinj : Function.Injective
      (fun p : {M : Subgroup G // M ≤ K ∧ M.relIndex K = 2} =>
        (⟨p.1.subgroupOf K, p.2.2⟩ : {J : Subgroup ↥K // J.index = 2})) := by
    rintro ⟨M1, hM1le, hM1⟩ ⟨M2, hM2le, hM2⟩ heq
    simp only [Subtype.ext_iff] at heq
    have : M1 = M2 := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hM1le, ← Subgroup.map_subgroupOf_eq_of_le hM2le, heq]
    simp [this]
  calc Nat.card {M : Subgroup G // M ≤ K ∧ M.relIndex K = 2}
      ≤ Nat.card {J : Subgroup ↥K // J.index = 2} := Nat.card_le_card_of_injective _ hinj
    _ ≤ Nat.card ↥K := card_index_two_subgroup_le

/-- **The order-ratio of a subgroup `M ≤ K` is the reciprocal of its relative index**:
`|M|/|K| = 1/[K:M]`. The single shared Lagrange cardinality fact (`|K| = |M|·[K:M]`, from
`Subgroup.card_mul_index` on `M.subgroupOf K` together with `Subgroup.subgroupOfEquivOfLe`) behind
every per-relative-index order-ratio bound: the index-`2` value `ratio_of_relIndex_two` (below), the
index-`≥ 3` bound `ratio_le_of_three_le_relIndex` (`SubgroupNonNormalMaximalSum.lean`), and the
class-refined sum (`SubgroupNonNormalMaximalConjugacy.lean`) all consume it as a one-liner. -/
theorem ratio_eq_one_div_relIndex [Finite G] {K M : Subgroup G} (hle : M ≤ K) :
    ((Nat.card ↥M : ℝ) / Nat.card ↥K) = 1 / (M.relIndex K : ℝ) := by
  have hcard : Nat.card ↥(M.subgroupOf K) * (M.subgroupOf K).index = Nat.card ↥K :=
    Subgroup.card_mul_index (M.subgroupOf K)
  have hsub : Nat.card ↥(M.subgroupOf K) = Nat.card ↥M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hsub] at hcard
  have hM0 : (Nat.card ↥M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hKeq : (Nat.card ↥K : ℝ) = Nat.card ↥M * (M.relIndex K) := by
    rw [Subgroup.relIndex]; exact_mod_cast hcard.symm
  rw [hKeq, ← div_div, div_self hM0]

/-- A subgroup `M ≤ K` of relative index `2` has order-ratio `|M|/|K| = 1/2`
(`ratio_eq_one_div_relIndex` at `[K:M] = 2`). -/
lemma ratio_of_relIndex_two [Finite G] {K M : Subgroup G} (hle : M ≤ K) (h2 : M.relIndex K = 2) :
    ((Nat.card ↥M : ℝ) / Nat.card ↥K) = 1 / 2 := by
  rw [ratio_eq_one_div_relIndex hle, h2]; norm_num

open Classical in
/-- **The index-`2` part of the maximal-subgroup low-index sum.** For a subgroup `K` and exponent
`s`, the subgroups `M ≤ K` of relative index `2` (equivalently, the index-`2` — hence maximal —
subgroups of `K`) each contribute the weight `(|M|/|K|)^s = (1/2)^s`, and there are at most `|K|` of
them (`card_relIndex_two_subgroup_le`), so

`∑_{M ≤ K, [K:M] = 2} (|M|/|K|)^s ≤ |K| · (1/2)^s`. -/
theorem sum_index_two_maximal_ratio_pow_le [Finite G] [Fintype (Subgroup G)] (K : Subgroup G)
    (s : ℕ) :
    ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ≤ K ∧ M.relIndex K = 2),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ (Nat.card ↥K : ℝ) * (1 / 2) ^ s := by
  have hconst : ∀ M ∈ Finset.univ.filter (fun M : Subgroup G => M ≤ K ∧ M.relIndex K = 2),
      ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s = (1 / 2) ^ s := by
    intro M hM
    rw [Finset.mem_filter] at hM
    rw [ratio_of_relIndex_two hM.2.1 hM.2.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.filter (fun M : Subgroup G => M ≤ K ∧ M.relIndex K = 2)).card : ℝ)
      ≤ Nat.card ↥K := by
    have h1 : (Finset.univ.filter (fun M : Subgroup G => M ≤ K ∧ M.relIndex K = 2)).card
        = Nat.card {M : Subgroup G // M ≤ K ∧ M.relIndex K = 2} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1]
    exact_mod_cast card_relIndex_two_subgroup_le K
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

open Classical in
/-- **The index-`2` part is `≤ 1/(2|G|)` at N&C's sample exponent.** Once `2·|G|² ≤ 2^s` (i.e.
`s = 2 log₂|G| + 1`, N&C's exponent `m = 2s = 4 log₂|G| + 2`), the index-`2` contribution to the
maximal-subgroup sum is at most `1/(2|G|)`: the count `≤ |K| ≤ |G|` times the weight
`(1/2)^s = 2^{-s} ≤ 1/(2|G|²)`. This is the elementary half of the maximal sum's `≤ c/|G|` target;
the higher-index maximals are the residual Gaussian-binomial-strength ingredient. -/
theorem sum_index_two_maximal_ratio_pow_le_of_sq [Finite G] [Fintype (Subgroup G)] (K : Subgroup G)
    {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    ∑ M ∈ Finset.univ.filter (fun M : Subgroup G => M ≤ K ∧ M.relIndex K = 2),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ (2 * Nat.card G : ℝ)⁻¹ := by
  refine (sum_index_two_maximal_ratio_pow_le K s).trans ?_
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hne : (Nat.card G : ℝ) ≠ 0 := ne_of_gt hGpos
  have hKle : (Nat.card ↥K : ℝ) ≤ Nat.card G := by
    have : Nat.card ↥K ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card K)
    exact_mod_cast this
  have hsR : (2 : ℝ) * Nat.card G ^ 2 ≤ 2 ^ s := by exact_mod_cast hs
  -- `(1/2)^s = (2^s)⁻¹ ≤ (2|G|²)⁻¹` since `2|G|² ≤ 2^s`.
  have hweight : ((1 : ℝ) / 2) ^ s ≤ (2 * Nat.card G ^ 2 : ℝ)⁻¹ := by
    rw [div_pow, one_pow, inv_eq_one_div (2 * Nat.card G ^ 2 : ℝ)]
    exact one_div_le_one_div_of_le (by positivity) hsR
  calc (Nat.card ↥K : ℝ) * (1 / 2) ^ s
      ≤ (Nat.card G : ℝ) * (2 * Nat.card G ^ 2 : ℝ)⁻¹ :=
        mul_le_mul hKle hweight (by positivity) (by positivity)
    _ = (2 * Nat.card G : ℝ)⁻¹ := by
        rw [eq_comm]
        field_simp

end AxQM.Concrete
