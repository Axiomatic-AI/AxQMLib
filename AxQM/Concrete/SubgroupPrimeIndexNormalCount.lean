/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import AxQM.Concrete.SubgroupIndexTwoCount

/-!
# Concrete: how many normal subgroups of prime index a finite group has

This file extends the **elementary index-`2` count** of `Concrete/SubgroupIndexTwoCount.lean` from
the single prime `2` to **all primes**, discharging the *normal* prime-index part of the
maximal-subgroup low-index sum `∑_{M ⋖ K} (|M|/|K|)^s` that `Concrete/SubgroupMaximalSum.lean`
isolated as the one remaining counting ingredient of the Ettinger–Høyer–Knill identification bound
behind Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem).

## The context

`Concrete/SubgroupMaximalSum.lean` reduced the Ettinger–Høyer–Knill collision tail to the
**maximal-subgroup low-index sum** `∑_{M ⋖ K} (|M|/|K|)^s = ∑_{M ⋖ K} [K:M]^{-s}`. A maximal
subgroup `M ⋖ K` that is **normal in `K`** has *simple* quotient `K/M`; when that quotient is
**abelian** it is cyclic of prime order, i.e. `M` has **prime index**. `SubgroupIndexTwoCount.lean`
counted the index-`2` case (there normality is automatic); the general prime-index normal case needs
a genuine character argument, supplied here. Every finite **nilpotent** group has *all* its maximal
subgroups normal of prime index, so this file discharges the entire counting tail for that class.

## What is proved

* `exists_monoidHom_complexUnits_ker_eq` — for a normal subgroup `N ◁ G` of **prime** index, a
  monoid homomorphism `χ : G →* ℂˣ` whose kernel is *exactly* `N`. Because `[G:N]` is prime, the
  quotient `G ⧸ N` is cyclic of prime order, hence simple; a character not killing a chosen
  nonidentity element (`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, using that `ℂ`
  has enough roots of unity) has trivial kernel there, so lifting it along `G → G ⧸ N` gives a
  character of `G` with kernel `N`. This is the prime-index analogue of the sign character.
* `card_monoidHom_complexUnits_le` — the number of complex characters `G →* ℂˣ` of a finite group
  is at most `|G|`. Characters factor through the abelianization (`Abelianization.lift`), and for
  the finite abelian group `Gᵃᵇ` the character group has cardinality exactly `|Gᵃᵇ| ≤ |G|`
  (`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`).
* `card_prime_index_normal_le` — **the number of normal subgroups of prime index of a finite group
  `G` is at most `|G|`.** The characters above inject the prime-index normal subgroups (each is the
  kernel of its character) into `G →* ℂˣ`, whose cardinality is `≤ |G|`. This generalizes
  `card_index_two_subgroup_le` (`p = 2`).
* `card_relIndex_prime_normal_le` — the **relative** form: the number of subgroups `M ≤ K` that are
  normal in `K` of prime relative index `[K:M]` is at most `|K|`. These are exactly the prime-index
  normal subgroups of `↥K`.
* `ratio_of_relIndex_prime` — a subgroup `M ≤ K` of prime relative index has order-ratio
  `|M|/|K| = 1/[K:M] ≤ 1/2` (the index is `≥ 2`).
* `sum_prime_index_normal_maximal_ratio_pow_le` — the **normal prime-index part of the
  maximal-subgroup sum**: each such `M` has weight `(|M|/|K|)^s ≤ (1/2)^s`, and there are at most
  `|K|` of them, so `∑ (|M|/|K|)^s ≤ |K| · (1/2)^s`.
* `sum_prime_index_normal_maximal_ratio_pow_le_of_sq` — its value at N&C's sample exponent: once
  `2·|G|² ≤ 2^s`, the normal prime-index part is `≤ 1/(2|G|)`. Together with the residual — the
  *non-normal* maximals and the (index-`≥ 60`) nonabelian-simple normal maximals — this drives the
  maximal-subgroup sum below `c/|G|`.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

/-- **A complex character with a prescribed prime-index normal kernel.** For a normal subgroup
`N ◁ G` of prime index, there is a monoid homomorphism `χ : G →* ℂˣ` with `χ.ker = N`. The quotient
`G ⧸ N` has prime order, hence is cyclic and simple; a character of `G ⧸ N` not killing a chosen
nonidentity element has trivial kernel there (its kernel, being normal, is `⊥` or `⊤`, and it is not
`⊤`), so lifting it along `G → G ⧸ N` produces a character of `G` whose kernel is exactly `N`. This
is the prime-index analogue of the real sign character `signChar` of an index-`2` subgroup. -/
theorem exists_monoidHom_complexUnits_ker_eq [Finite G] (N : Subgroup G) [N.Normal]
    (hp : N.index.Prime) : ∃ χ : G →* ℂˣ, χ.ker = N := by
  have hcard : Nat.card (G ⧸ N) = N.index := N.index_eq_card.symm
  have hfact : Fact (N.index).Prime := ⟨hp⟩
  have hcyc : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  let : CommGroup (G ⧸ N) := hcyc.commGroup
  have hsimple : IsSimpleGroup (G ⧸ N) := isSimpleGroup_of_prime_card hcard
  have hnt : Nontrivial (G ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp (hcard ▸ hp.one_lt)
  obtain ⟨a, ha⟩ : ∃ a : G ⧸ N, a ≠ 1 := exists_ne 1
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ N) ℂ ha
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exact absurd (by rw [← MonoidHom.mem_ker, h]; trivial) hψ
  refine ⟨ψ.comp (QuotientGroup.mk' N), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    ← map_one ψ, hψinj.eq_iff, QuotientGroup.eq_one_iff]

/-- **The number of complex characters of a finite group is at most its order.** Every homomorphism
`G →* ℂˣ` factors through the abelianization (`Abelianization.lift`), and for the finite abelian
group `Gᵃᵇ` the character group has cardinality exactly `|Gᵃᵇ|`
(`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`, `ℂ` having enough roots of unity), which is at
most `|G|` since `Gᵃᵇ` is a quotient of `G`. -/
theorem card_monoidHom_complexUnits_le [Finite G] :
    Nat.card (G →* ℂˣ) ≤ Nat.card G := by
  have e : (G →* ℂˣ) ≃ (Group.Abelianization G →* ℂˣ) := Group.Abelianization.lift
  rw [Nat.card_congr e,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Group.Abelianization G) ℂ]
  exact Nat.card_le_card_of_surjective Group.Abelianization.of (QuotientGroup.mk'_surjective _)

/-- **The number of normal subgroups of prime index of a finite group is at most its order.** Each
prime-index normal subgroup `N` is the kernel of a complex character
(`exists_monoidHom_complexUnits_ker_eq`), and distinct kernels give distinct characters, so the
prime-index normal subgroups inject into `G →* ℂˣ`, which has at most `|G|` elements
(`card_monoidHom_complexUnits_le`). This generalizes `card_index_two_subgroup_le` from `p = 2` to
every prime. -/
theorem card_prime_index_normal_le [Finite G] :
    Nat.card {N : Subgroup G // N.Normal ∧ N.index.Prime} ≤ Nat.card G := by
  classical
  have hex : ∀ p : {N : Subgroup G // N.Normal ∧ N.index.Prime}, ∃ χ : G →* ℂˣ, χ.ker = p.1 :=
    fun p => by have := p.2.1; exact exists_monoidHom_complexUnits_ker_eq p.1 p.2.2
  choose f hker using hex
  have hinj : Function.Injective f := by
    intro p q hpq
    exact Subtype.ext (by rw [← hker p, ← hker q, hpq])
  exact (Nat.card_le_card_of_injective f hinj).trans card_monoidHom_complexUnits_le

/-- **The number of subgroups of prime relative index that are normal in `K` is at most `|K|`.**
These are exactly the prime-index normal subgroups of the group `↥K` (`Subgroup.subgroupOf`,
injective on subgroups `≤ K`), so `card_prime_index_normal_le` applied to `↥K` bounds them by `|K|`.
The relative-index-`2` special case is `card_relIndex_two_subgroup_le`. -/
theorem card_relIndex_prime_normal_le [Finite G] (K : Subgroup G) :
    Nat.card {M : Subgroup G // M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime}
      ≤ Nat.card ↥K := by
  have hfin : Finite ↥K := Subtype.finite
  have : Finite (Subgroup ↥K) := Finite.of_injective _ SetLike.coe_injective
  have hinj : Function.Injective
      (fun p : {M : Subgroup G // M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime} =>
        (⟨p.1.subgroupOf K, p.2.2.1, by rw [← Subgroup.relIndex]; exact p.2.2.2⟩ :
          {N : Subgroup ↥K // N.Normal ∧ N.index.Prime})) := by
    rintro ⟨M1, hle1, _, _⟩ ⟨M2, hle2, _, _⟩ heq
    simp only [Subtype.mk.injEq] at heq
    have : M1 = M2 := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hle1, ← Subgroup.map_subgroupOf_eq_of_le hle2, heq]
    simp [this]
  calc Nat.card {M : Subgroup G // M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime}
      ≤ Nat.card {N : Subgroup ↥K // N.Normal ∧ N.index.Prime} :=
        Nat.card_le_card_of_injective _ hinj
    _ ≤ Nat.card ↥K := card_prime_index_normal_le

/-- A subgroup `M ≤ K` of prime relative index has order-ratio `|M|/|K| = 1/[K:M] ≤ 1/2`, since a
prime index is `≥ 2`. -/
lemma ratio_of_relIndex_prime [Finite G] {K M : Subgroup G} (hle : M ≤ K)
    (hp : (M.relIndex K).Prime) :
    ((Nat.card ↥M : ℝ) / Nat.card ↥K) ≤ 1 / 2 := by
  have hcard : Nat.card ↥(M.subgroupOf K) * (M.subgroupOf K).index = Nat.card ↥K :=
    Subgroup.card_mul_index (M.subgroupOf K)
  have hsub : Nat.card ↥(M.subgroupOf K) = Nat.card ↥M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← Subgroup.relIndex, hsub] at hcard
  have hKpos : (0 : ℝ) < Nat.card ↥K := by exact_mod_cast Nat.card_pos
  have hMpos : (0 : ℝ) < Nat.card ↥M := by exact_mod_cast Nat.card_pos
  have hK : (Nat.card ↥K : ℝ) = Nat.card ↥M * (M.relIndex K) := by exact_mod_cast hcard.symm
  have h2le : (2 : ℝ) ≤ (M.relIndex K : ℝ) := by exact_mod_cast hp.two_le
  rw [div_le_div_iff₀ hKpos (by norm_num), hK]
  nlinarith [hMpos]

open Classical in
/-- **The normal prime-index part of the maximal-subgroup low-index sum.** The subgroups `M ≤ K`
that are normal in `K` of prime relative index — a subclass of the maximal (coatom) subgroups of
`K` — each contribute weight `(|M|/|K|)^s ≤ (1/2)^s` (`ratio_of_relIndex_prime`), and there are at
most `|K|` of them (`card_relIndex_prime_normal_le`), so

`∑ (|M|/|K|)^s ≤ |K| · (1/2)^s`. -/
theorem sum_prime_index_normal_maximal_ratio_pow_le [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) (s : ℕ) :
    ∑ M ∈ Finset.univ.filter
        (fun M : Subgroup G => M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ (Nat.card ↥K : ℝ) * (1 / 2) ^ s := by
  have hbound : ∀ M ∈ Finset.univ.filter
      (fun M : Subgroup G => M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime),
      ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s ≤ (1 / 2) ^ s := by
    intro M hM
    rw [Finset.mem_filter] at hM
    refine pow_le_pow_left₀ (by positivity) (ratio_of_relIndex_prime hM.2.1 hM.2.2.2) s
  refine (Finset.sum_le_card_nsmul _ _ _ hbound).trans ?_
  rw [nsmul_eq_mul]
  have hcard : ((Finset.univ.filter
      (fun M : Subgroup G => M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime)).card : ℝ)
      ≤ Nat.card ↥K := by
    have h1 : (Finset.univ.filter
        (fun M : Subgroup G => M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime)).card
        = Nat.card {M : Subgroup G // M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1]
    exact_mod_cast card_relIndex_prime_normal_le K
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

open Classical in
/-- **The normal prime-index part is `≤ 1/(2|G|)` at N&C's sample exponent.** Once `2·|G|² ≤ 2^s`
(i.e. `s = 2 log₂|G| + 1`, N&C's exponent `m = 2s = 4 log₂|G| + 2`), the normal prime-index
contribution to the maximal-subgroup sum is at most `1/(2|G|)`: the count `≤ |K| ≤ |G|` times the
weight `(1/2)^s = 2^{-s} ≤ 1/(2|G|²)`. This generalizes `sum_index_two_maximal_ratio_pow_le_of_sq`
from `p = 2` to every prime; the residual is the non-normal maximals and the nonabelian-simple
(index `≥ 60`) normal maximals. -/
theorem sum_prime_index_normal_maximal_ratio_pow_le_of_sq [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s) :
    ∑ M ∈ Finset.univ.filter
        (fun M : Subgroup G => M ≤ K ∧ (M.subgroupOf K).Normal ∧ (M.relIndex K).Prime),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ (2 * Nat.card G : ℝ)⁻¹ := by
  refine (sum_prime_index_normal_maximal_ratio_pow_le K s).trans ?_
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hKle : (Nat.card ↥K : ℝ) ≤ Nat.card G := by
    have : Nat.card ↥K ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card K)
    exact_mod_cast this
  have hsR : (2 : ℝ) * Nat.card G ^ 2 ≤ 2 ^ s := by exact_mod_cast hs
  have hweight : ((1 : ℝ) / 2) ^ s ≤ (2 * Nat.card G ^ 2 : ℝ)⁻¹ := by
    rw [div_pow, one_pow, inv_eq_one_div (2 * Nat.card G ^ 2 : ℝ)]
    exact one_div_le_one_div_of_le (by positivity) hsR
  calc (Nat.card ↥K : ℝ) * (1 / 2) ^ s
      ≤ (Nat.card G : ℝ) * (2 * Nat.card G ^ 2 : ℝ)⁻¹ :=
        mul_le_mul hKle hweight (by positivity) (by positivity)
    _ = (2 * Nat.card G : ℝ)⁻¹ := by rw [eq_comm]; field_simp

end AxQM.Concrete
