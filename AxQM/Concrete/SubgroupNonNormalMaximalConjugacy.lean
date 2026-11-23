/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.GroupTheory.IndexNormal
import AxQM.Concrete.SubgroupNonNormalMaximalSum

/-!
# Conjugacy-class refinement of the non-normal maximal-subgroup sum (Ettinger–Høyer–Knill piece ii)

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Problem 5.5.)* This file **sharpens** the
isolated counting ingredient of the Ettinger–Høyer–Knill maximal-subgroup sum
`∑_{M ⋖ K} (|M|/|K|)^s` produced by `SubgroupNonNormalMaximalSum.lean`. That file reduces the
**non-normal** maximals to the raw count `#{non-normal maximals of K}`, needing a polynomial bound
`≤ |K|²` (Liebeck–Pyber–Shalev-strength). Here that raw count is replaced by the far smaller
**number of `K`-conjugacy classes** of non-normal maximals, exploiting the structural fact that a
non-normal maximal subgroup is **self-normalizing**.

## The structural core: non-normal maximals are self-normalizing

`normalizer_inf_eq_self_of_covBy_of_not_normal`: a maximal subgroup `M ⋖ K` that is **not** normal
in `K` satisfies `N_K(M) = M` (i.e. `normalizer M ⊓ K = M`). Indeed `M ≤ N_K(M) ≤ K` and `M ⋖ K`
forces `N_K(M) ∈ {M, K}`; `N_K(M) = K` means `K ≤ normalizer M`, i.e. `M ◁ K`
(`Subgroup.normal_subgroupOf_iff_le_normalizer`) — excluded. Consequently, under the `K`-conjugation
action, the orbit (conjugacy class) of `M` has cardinality exactly the index
`(MulAction.orbit ↥K M).ncard = [K : N_K(M)] = [K : M]`
(`ncard_kConj_orbit_eq_relIndex_of_covBy_of_not_normal`, via `MulAction.index_stabilizer` — the
orbit–stabilizer theorem — with `stabilizer = N_K(M)`). So each conjugacy class of non-normal
maximals contributes `#class · (1/[K:M])^s = [K:M] · [K:M]^{-s} = [K:M]^{1-s} ≤ (1/3)^{s-1}`
(relative index `≥ 3`, `three_le_relIndex_of_lt_of_not_normal`) to the sum — an **extra factor
`[K:M] ≥ 3` of decay** per class over the naive per-subgroup bound.

## The refinement

Summing the per-class bound over the `K`-conjugacy classes (`Finset.sum_fiberwise_of_maps_to`
grouped by the orbit-relation quotient) gives, for `1 ≤ s`,

`∑_{M ⋖ K, M ⋪ K} (|M|/|K|)^s ≤ #{K-conjugacy classes of non-normal maximals} · (1/3)^{s-1}`
(`sum_nonnormal_maximal_ratio_pow_le_classCard`),

and hence at N&C's sample exponent (`2·|G|² ≤ 2^s`), the **weaker** counting hypothesis
`3 · #classes ≤ |K|²` (implied by, but strictly weaker than, the raw
`#{non-normal maximals} ≤ |K|²`, since `#{non-normal maximals} = ∑_class [K:M] ≥ 3 · #classes`)
already drives the non-normal part below `1/(2|G|)`
(`sum_nonnormal_maximal_ratio_pow_le_classCard_of_sq`).

This isolates the **class**-count `#{K-conjugacy classes of non-normal maximals of K}` as the
remaining piece-(ii) ingredient — the natural quantity, since a non-normal maximal's class is a full
orbit of size its index and the collision sum only sees one weight per class. (The class count is
still Gaussian-binomial-strength in the worst case — e.g. affine primitive quotients `V ⋊ H` realise
`|H¹(H,V)|` classes of complements — so, like the raw count, it is genuinely deep group theory, not
a gap closed here; this file provides the sharpest elementary reduction and the self-normalization
structure any such count consumes.
-/

namespace AxQM.Concrete

open Finset
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **A non-normal maximal subgroup of `K` is self-normalizing in `K`.** If `M ⋖ K` (maximal in `K`)
and `M.subgroupOf K` is **not** normal in `K`, then `N_K(M) = normalizer M ⊓ K = M`. The normalizer
`normalizer M ⊓ K` lies between `M` and `K` (`M ≤ normalizer M`, and it is `≤ K`), so by maximality
(`CovBy.eq_or_eq`) it is `M` or `K`; equality with `K` would give `K ≤ normalizer M`, i.e. `M ◁ K`
(`Subgroup.normal_subgroupOf_iff_le_normalizer`), contradicting non-normality — so it is `M`. -/
theorem normalizer_inf_eq_self_of_covBy_of_not_normal {K M : Subgroup G}
    (hcov : M ⋖ K) (hnn : ¬ (M.subgroupOf K).Normal) :
    Subgroup.normalizer (M : Set G) ⊓ K = M := by
  have hle : M ≤ K := hcov.lt.le
  have h1 : M ≤ Subgroup.normalizer (M : Set G) ⊓ K := le_inf Subgroup.le_normalizer hle
  have h2 : Subgroup.normalizer (M : Set G) ⊓ K ≤ K := inf_le_right
  rcases hcov.eq_or_eq h1 h2 with h | h
  · exact h
  · exfalso
    apply hnn
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    calc K = Subgroup.normalizer (M : Set G) ⊓ K := h.symm
      _ ≤ Subgroup.normalizer (M : Set G) := inf_le_left

/-- The `K`-conjugation homomorphism `↥K →* ConjAct G`, sending `k` to conjugation `x ↦ kxk⁻¹`. Used
to make `↥K` act on `Subgroup G` by conjugation (`kConjAction`), so the `K`-conjugacy class of a
subgroup `M ≤ K` is the orbit of `M`. -/
noncomputable def kConjHom (K : Subgroup G) : ↥K →* ConjAct G :=
  (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp K.subtype

/-- The conjugation action of `↥K` on `Subgroup G`: `k • M = kMk⁻¹`. The `K`-conjugacy class of `M`
is `MulAction.orbit ↥K M`. Exported (a genuine `instance`, keyed on `↥K`) so that the class-count
`MulAction.orbitRel ↥K (Subgroup G)` appearing in the statements of
`sum_nonnormal_maximal_ratio_pow_le_classCard` and `…_of_sq` can be stated directly. -/
noncomputable instance kConjAction (K : Subgroup G) :
    MulAction ↥K (Subgroup G) := MulAction.compHom (Subgroup G) (kConjHom K)

/-- The stabilizer of `M` under the `K`-conjugation action is `N_K(M)` (as a subgroup of `↥K`):
`k` fixes `M` iff `k` normalizes `M`. -/
theorem stabilizer_kConj_eq (K M : Subgroup G) :
    MulAction.stabilizer ↥K M = (Subgroup.normalizer (M : Set G)).subgroupOf K := by
  ext k
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  exact Subgroup.conjAct_pointwise_smul_iff

/-- **The size of a `K`-conjugacy class of subgroups is the relative index of the normalizer.** By
the orbit–stabilizer theorem (`MulAction.index_stabilizer`) and `stabilizer_kConj_eq`, the number of
`K`-conjugates of `M` is `[K : N_K(M)] = (normalizer M).relIndex K`. -/
theorem ncard_kConj_orbit_eq (K M : Subgroup G) :
    (MulAction.orbit ↥K M).ncard = (Subgroup.normalizer (M : Set G)).relIndex K := by
  have hidx := MulAction.index_stabilizer ↥K M
  rw [stabilizer_kConj_eq] at hidx
  unfold Subgroup.relIndex
  exact hidx.symm

/-- **A non-normal maximal subgroup's `K`-conjugacy class has exactly `[K:M]` members.** Combining
`ncard_kConj_orbit_eq` with the self-normalization `N_K(M) = M`
(`normalizer_inf_eq_self_of_covBy_of_not_normal`): the class of `M` is a full orbit of size
`[K : N_K(M)] = [K : M] = M.relIndex K`. -/
theorem ncard_kConj_orbit_eq_relIndex_of_covBy_of_not_normal {K M : Subgroup G}
    (hcov : M ⋖ K) (hnn : ¬ (M.subgroupOf K).Normal) :
    (MulAction.orbit ↥K M).ncard = M.relIndex K := by
  rw [ncard_kConj_orbit_eq]
  have hself : Subgroup.normalizer (M : Set G) ⊓ K = M :=
    normalizer_inf_eq_self_of_covBy_of_not_normal hcov hnn
  have hsub : (Subgroup.normalizer (M : Set G)).subgroupOf K = M.subgroupOf K := by
    rw [← Subgroup.inf_subgroupOf_right, hself]
  unfold Subgroup.relIndex
  rw [hsub]

/-- Conjugation preserves subgroup cardinality: `|k • M| = |M|` for the `K`-conjugation action
(conjugation by `k` is an automorphism of `G`, so `M ≃ k • M`). -/
theorem card_kConj_smul (K : Subgroup G) (k : ↥K) (M : Subgroup G) :
    Nat.card ↥(k • M) = Nat.card ↥M :=
  Nat.card_congr
    (Subgroup.equivMapOfInjective M _ (MulAut.conj (K.subtype k)).injective).symm.toEquiv

open Classical in
/-- **The conjugacy-class-refined non-normal maximal sum bound.** For `1 ≤ s`, grouping the
non-normal maximals of `K` by their `K`-conjugacy class (each a full orbit of size `[K:M]`, by
self-normalization) gives

`∑_{M ⋖ K, M ⋪ K} (|M|/|K|)^s ≤ #{K-conjugacy classes of non-normal maximals} · (1/3)^{s-1}`.

Each class `C` with representative index `n = [K:M] ≥ 3` contributes
`(#C) · (1/n)^s = n · (1/n)^s = (1/n)^{s-1} ≤ (1/3)^{s-1}` (the fiber weight is constant `(1/n)^s`
on the class, and the class has exactly `n` members), so summing over the `#classes` classes gives
the stated bound. This is the `[K:M] ≥ 3`-times sharper form of `sum_nonnormal_maximal_ratio_pow_le`
(which bounds by `#{non-normal maximals} · (1/3)^s`). -/
theorem sum_nonnormal_maximal_ratio_pow_le_classCard [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hs1 : 1 ≤ s) :
    ∑ M ∈ Finset.univ.filter
        (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ ((Finset.univ.filter
            (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal)).image
          (fun M => Quotient.mk (MulAction.orbitRel ↥K (Subgroup G)) M)).card
        * (1 / 3 : ℝ) ^ (s - 1) := by
  set S := Finset.univ.filter
    (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal) with hS
  set q : Subgroup G → Quotient (MulAction.orbitRel ↥K (Subgroup G)) :=
    fun M => Quotient.mk (MulAction.orbitRel ↥K (Subgroup G)) M with hq
  have hmaps : ∀ M ∈ S, q M ∈ S.image q := fun M hM => Finset.mem_image_of_mem q hM
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine (Finset.sum_le_card_nsmul (S.image q) _ ((1 / 3 : ℝ) ^ (s - 1)) ?_).trans_eq ?_
  · -- Each conjugacy-class fiber contributes `≤ (1/3)^(s-1)`.
    intro c hc
    obtain ⟨M0, hM0S, hM0c⟩ := Finset.mem_image.mp hc
    have hM0S' := hM0S
    rw [hS, Finset.mem_filter] at hM0S'
    obtain ⟨-, hcov0, hnn0⟩ := hM0S'
    have hleM0 : M0 ≤ K := hcov0.lt.le
    set n : ℕ := M0.relIndex K with hn
    have h3 : 3 ≤ n := by rw [hn]; exact three_le_relIndex_of_lt_of_not_normal hcov0.lt hnn0
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hval : ∀ M ∈ S.filter (fun M => q M = c),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s = (1 / (n : ℝ)) ^ s := by
      intro M hM
      rw [Finset.mem_filter] at hM
      have hqM : q M = q M0 := by rw [hM.2, hM0c]
      have hmem : M ∈ MulAction.orbit ↥K M0 := MulAction.orbitRel_apply.mp (Quotient.exact hqM)
      obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hmem
      have hcardM : Nat.card ↥M = Nat.card ↥M0 := by rw [← hk]; exact card_kConj_smul K k M0
      rw [hcardM, ratio_eq_one_div_relIndex hleM0, ← hn]
    have hcardF : ((S.filter (fun M => q M = c)).card : ℝ) ≤ (n : ℝ) := by
      have hsubset : (↑(S.filter (fun M => q M = c)) : Set (Subgroup G))
          ⊆ MulAction.orbit ↥K M0 := by
        intro M hM
        rw [Finset.mem_coe, Finset.mem_filter] at hM
        have hqM : q M = q M0 := by rw [hM.2, hM0c]
        exact MulAction.orbitRel_apply.mp (Quotient.exact hqM)
      have hle : (S.filter (fun M => q M = c)).card ≤ (MulAction.orbit ↥K M0).ncard := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsubset (Set.toFinite _)
      rw [ncard_kConj_orbit_eq_relIndex_of_covBy_of_not_normal hcov0 hnn0, ← hn] at hle
      exact_mod_cast hle
    have hstep : (1 / (n : ℝ)) ^ s = (1 / (n : ℝ)) ^ (s - 1) * (1 / (n : ℝ)) :=
      (pow_sub_one_mul (by omega) _).symm
    have hn3 : (1 / (n : ℝ)) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h3)
    calc ∑ M ∈ S.filter (fun M => q M = c), ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
        = ∑ _M ∈ S.filter (fun M => q M = c), (1 / (n : ℝ)) ^ s := Finset.sum_congr rfl hval
      _ = ((S.filter (fun M => q M = c)).card : ℝ) * (1 / (n : ℝ)) ^ s := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * (1 / (n : ℝ)) ^ s := mul_le_mul_of_nonneg_right hcardF (by positivity)
      _ = (1 / (n : ℝ)) ^ (s - 1) := by
          rw [hstep, mul_comm ((1 / (n : ℝ)) ^ (s - 1)) (1 / (n : ℝ)), ← mul_assoc, mul_one_div,
            div_self hn0, one_mul]
      _ ≤ (1 / 3 : ℝ) ^ (s - 1) := pow_le_pow_left₀ (by positivity) hn3 (s - 1)
  · rw [nsmul_eq_mul]

open Classical in
/-- **The conjugacy-class-refined non-normal part is `≤ 1/(2|G|)` at N&C's sample exponent.** Once
`2·|G|² ≤ 2^s` (N&C's exponent `m = 2s = 4 log₂|G| + 2`), the counting hypothesis
`3 · #{K-conjugacy classes of non-normal maximals} ≤ |K|²` drives the non-normal part below
`1/(2|G|)`. This hypothesis is **strictly weaker** than the raw count bound
`#{non-normal maximals} ≤ |K|²` used by `sum_nonnormal_maximal_ratio_pow_le_of_sq`, because a
non-normal maximal's conjugacy class is a full orbit of size its index `≥ 3`, so
`#{non-normal maximals} = ∑_class [K:M] ≥ 3 · #classes`. It thus isolates the (still deep) **class**
count as the sharpest remaining piece-(ii) ingredient. -/
theorem sum_nonnormal_maximal_ratio_pow_le_classCard_of_sq [Finite G] [Fintype (Subgroup G)]
    (K : Subgroup G) {s : ℕ} (hs : 2 * Nat.card G ^ 2 ≤ 2 ^ s)
    (hcount : 3 * ((Finset.univ.filter
        (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal)).image
        (fun M => Quotient.mk (MulAction.orbitRel ↥K (Subgroup G)) M)).card
      ≤ (Nat.card ↥K) ^ 2) :
    ∑ M ∈ Finset.univ.filter
        (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal),
        ((Nat.card ↥M : ℝ) / Nat.card ↥K) ^ s
      ≤ (2 * Nat.card G : ℝ)⁻¹ := by
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      simp only [pow_zero] at hs
      nlinarith [Nat.card_pos (α := G)]
    · exact h
  refine (sum_nonnormal_maximal_ratio_pow_le_classCard K hs1).trans ?_
  set c : ℕ := ((Finset.univ.filter
      (fun M : Subgroup G => M ⋖ K ∧ ¬ (M.subgroupOf K).Normal)).image
      (fun M => Quotient.mk (MulAction.orbitRel ↥K (Subgroup G)) M)).card with hc
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hKle : (Nat.card ↥K : ℝ) ≤ Nat.card G := by
    have : Nat.card ↥K ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card K)
    exact_mod_cast this
  have hsR : (2 : ℝ) * (Nat.card G : ℝ) ^ 2 ≤ 2 ^ s := by exact_mod_cast hs
  have hcube : (2 : ℝ) * (Nat.card G : ℝ) ^ 3 ≤ 3 ^ s :=
    two_mul_cube_le_three_pow (by positivity) hsR
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
  have hcountR : (3 : ℝ) * (c : ℝ) ≤ (Nat.card ↥K : ℝ) ^ 2 := by exact_mod_cast hcount
  have hpow : (1 / 3 : ℝ) ^ (s - 1) = 3 * (1 / 3 : ℝ) ^ s := by
    rw [← pow_sub_one_mul (by omega : s ≠ 0) (1 / 3 : ℝ)]; ring
  calc (c : ℝ) * (1 / 3 : ℝ) ^ (s - 1)
      = 3 * (c : ℝ) * (1 / 3 : ℝ) ^ s := by rw [hpow]; ring
    _ ≤ (Nat.card ↥K : ℝ) ^ 2 * (1 / 3 : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hcountR (by positivity)
    _ ≤ (Nat.card G : ℝ) ^ 2 * (1 / 3 : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hKle 2) (by positivity)
    _ ≤ (2 * Nat.card G : ℝ)⁻¹ := by
        rw [div_pow, one_pow, mul_one_div, inv_eq_one_div (2 * (Nat.card G : ℝ)),
          div_le_div_iff₀ h3pos (by positivity)]
        nlinarith [hcube]

end AxQM.Concrete
