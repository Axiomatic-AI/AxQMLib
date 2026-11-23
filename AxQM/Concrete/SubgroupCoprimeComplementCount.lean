/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupComplementOrbitCount
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The complement count for coprime chief factors: all complements are conjugate

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Prob. 5.5 — Ettinger–Høyer–Knill piece
ii.)* The orbit-counting factorization `SubgroupComplementOrbitCount.lean` reduced the sharp
per-chief-factor complement bound `#{complements of an abelian minimal normal N in H} ≤ |H|` to the
strictly **cohomological** class count `#{N-conjugacy classes of complements} = |H¹(H ⧸ N, N)| ≤
|H : N|`. Other files prove that class count for **central** chief factors
(`SubgroupCentralComplementCount.lean`, `N ≤ Z(H)`) and for **cyclic-quotient** chief factors
(`SubgroupComplementCount.lean`, `H ⧸ N` cyclic).

This file discharges it for the **coprime** chief factors — those where `gcd(|N|, [H : N]) = 1` — by
proving the classical vanishing `H¹(H ⧸ N, N) = 0`: **all complements of `N` are `N`-conjugate**
(`exists_conjAct_smul_of_isComplement'_of_coprime`). This is the abelian, coprime case of the
Schur–Zassenhaus conjugacy theorem, which Mathlib does **not** provide (only the existence half,
`Subgroup.exists_right_complement'_of_coprime`), so it is proved here from scratch by the standard
**cocycle-averaging** argument:

* each complement `K` gives a homomorphic section `sₖ : H ⧸ N →* H` (`K ≃* H ⧸ N` via
  `Subgroup.IsComplement'.QuotientMulEquiv`), and two complements `K₁, K₂` differ by the 1-cocycle
  `c q = s₂ q · (s₁ q)⁻¹ ∈ N`, satisfying `c(q₁q₂) = c(q₁) · ᵍc(q₂)` with `g = s₁ q₁` acting by
  conjugation (`MulAut.conjNormal`);
* summing the cocycle identity over `H ⧸ N` gives `c(q)^{[H:N]} = T · ᵍT⁻¹` for `T = ∏_q c q`, and —
  since `|N|` is coprime to `[H : N]`, so `x ↦ x^{[H:N]}` is a bijection of `N` (`powCoprime`) — the
  element `t = T^{1/[H:N]}` satisfies `c(q) = t · ᵍt⁻¹`, i.e. `s₂ q = t · s₁ q · t⁻¹`, whence
  `K₂ = t K₁ t⁻¹` (`ConjAct.toConjAct t • K₁`).

Consequently the `N`-conjugation orbit of complements is a single class
(`card_orbitRel_quotient_isComplement'_le_one_of_coprime`), so `#{complements} ≤ |N|`
(`card_isComplement'_le_card_of_coprime`) and the class count is `≤ [H : N]`
(`card_isComplement'_orbits_le_index_of_coprime`) — exactly the `horb` hypothesis of
`card_isCoatom_le_two_mul_card_of_isSolvable_of_orbitBound` for coprime chief factors. Unlike the
central case this covers **non-central** factors, and unlike the cyclic-quotient case it needs no
constraint on the quotient's generation — the two remaining open slices of the solvable residual are
now only the chief factors that are simultaneously non-central, non-cyclic-quotient **and**
non-coprime (`p | [H : N]` for `N` an elementary abelian `p`-group), where `|H¹|` genuinely fails to
vanish.
-/

open scoped Pointwise

open Subgroup QuotientGroup MulAction

namespace AxQM.Concrete

variable {G : Type*} [Group G]

/-- **Coprime complement conjugacy** (Nielsen & Chuang, Problem 5.5 — Ettinger–Høyer–Knill piece
ii). If `N` is an abelian normal subgroup of a finite group `G` whose order is coprime to its index,
then any two complements `K₁, K₂` of `N` are conjugate by an element of `N`:
`∃ n : N, n K₁ n⁻¹ = K₂`. This is the abelian, coprime case of Schur–Zassenhaus conjugacy — the
vanishing `H¹(G ⧸ N, N) = 0` — proved by cocycle averaging: the difference cocycle
`c q = s₂ q · (s₁ q)⁻¹` of the two complements' homomorphic sections is a coboundary because
`x ↦ x^{[G:N]}` is a bijection of the coprime-order `N` (`powCoprime`), so `c q = t · s₁ q · t⁻¹ ·
(s₁ q)⁻¹` for `t = (∏_q c q)^{1/[G:N]}`, giving `s₂ q = t · s₁ q · t⁻¹` and `K₂ = t K₁ t⁻¹`. -/
theorem exists_conjAct_smul_of_isComplement'_of_coprime [Finite G] {N : Subgroup G} [N.Normal]
    (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hcop : (Nat.card ↥N).Coprime N.index)
    {K₁ K₂ : Subgroup G} (hK₁ : N.IsComplement' K₁) (hK₂ : N.IsComplement' K₂) :
    ∃ n : ↥N, ConjAct.toConjAct (↑n : G) • K₁ = K₂ := by
  classical
  let : Fintype (G ⧸ N) := Fintype.ofFinite _
  let : CommGroup ↥N :=
    { (inferInstance : Group ↥N) with mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }
  -- The homomorphic sections of the two complements.
  set e₁ := hK₁.symm.QuotientMulEquiv with he₁
  set e₂ := hK₂.symm.QuotientMulEquiv with he₂
  set s₁ : (G ⧸ N) →* G := K₁.subtype.comp e₁.toMonoidHom with hs₁def
  set s₂ : (G ⧸ N) →* G := K₂.subtype.comp e₂.toMonoidHom with hs₂def
  have hs₁val : ∀ q, s₁ q = (↑(e₁ q) : G) := fun _ => rfl
  have hs₂val : ∀ q, s₂ q = (↑(e₂ q) : G) := fun _ => rfl
  have hsec₁ : ∀ q, (mk' N) (s₁ q) = q := by
    intro q
    have hsymm : ∀ k : ↥K₁, e₁.symm k = (QuotientGroup.mk (↑k : G) : G ⧸ N) := fun _ => rfl
    have := e₁.symm_apply_apply q
    rw [hsymm] at this
    simpa [hs₁val, QuotientGroup.mk'_apply] using this
  have hsec₂ : ∀ q, (mk' N) (s₂ q) = q := by
    intro q
    have hsymm : ∀ k : ↥K₂, e₂.symm k = (QuotientGroup.mk (↑k : G) : G ⧸ N) := fun _ => rfl
    have := e₂.symm_apply_apply q
    rw [hsymm] at this
    simpa [hs₂val, QuotientGroup.mk'_apply] using this
  have hmemK₁ : ∀ q, s₁ q ∈ K₁ := fun q => by rw [hs₁val]; exact (e₁ q).2
  -- The difference cocycle `c q = s₂ q · (s₁ q)⁻¹ ∈ N`.
  have hcmem : ∀ q, s₂ q * (s₁ q)⁻¹ ∈ N := by
    intro q
    have h1 : (mk' N) (s₂ q * (s₁ q)⁻¹) = 1 := by
      rw [map_mul, map_inv, hsec₁ q, hsec₂ q, mul_inv_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  set c : (G ⧸ N) → ↥N := fun q => ⟨s₂ q * (s₁ q)⁻¹, hcmem q⟩ with hcdef
  have hcval : ∀ q, (↑(c q) : G) = s₂ q * (s₁ q)⁻¹ := fun _ => rfl
  -- The cocycle identity `c(q₁ q₂) = c q₁ · ᵍc q₂` with `g = s₁ q₁`.
  have cocycle : ∀ q₁ q₂, c (q₁ * q₂) = c q₁ * (MulAut.conjNormal (s₁ q₁)) (c q₂) := by
    intro q₁ q₂
    apply Subtype.ext
    rw [Subgroup.coe_mul, MulAut.conjNormal_apply (s₁ q₁) (c q₂), hcval, hcval, hcval,
      map_mul s₁, map_mul s₂]
    group
  -- Averaging: `T = ∏_q c q`.
  set T : ↥N := ∏ q : G ⧸ N, c q with hTdef
  have hcardQ : Fintype.card (G ⧸ N) = N.index := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
  set t : ↥N := (powCoprime hcop).symm T with htdef
  have hpow : t ^ N.index = T := by
    have h := powCoprime_apply hcop t
    rw [htdef, ← h, Equiv.apply_symm_apply]
  -- For each `q₀`: `c q₀ ^ [G:N] = T · (ᵍT)⁻¹`.
  have key : ∀ q₀ : G ⧸ N,
      c q₀ ^ N.index = T * ((MulAut.conjNormal (s₁ q₀)) T)⁻¹ := by
    intro q₀
    set φ : MulAut ↥N := MulAut.conjNormal (s₁ q₀) with hφ
    have reindex : ∏ q, c (q₀ * q) = T := Equiv.prod_comp (Equiv.mulLeft q₀) c
    have expand : ∏ q, c (q₀ * q) = c q₀ ^ N.index * φ T := by
      have h1 : (∏ q, c (q₀ * q)) = ∏ _q : G ⧸ N, (c q₀ * φ (c _q)) :=
        Finset.prod_congr rfl (fun q _ => cocycle q₀ q)
      rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcardQ,
        ← map_prod]
    rw [reindex] at expand
    exact eq_mul_inv_of_mul_eq expand.symm
  -- Hence `c q₀ = t · ᵍt⁻¹`, i.e. `s₂ q₀ = t · s₁ q₀ · t⁻¹`.
  have hconj : ∀ q₀ : G ⧸ N, c q₀ = t * ((MulAut.conjNormal (s₁ q₀)) t)⁻¹ := by
    intro q₀
    set φ : MulAut ↥N := MulAut.conjNormal (s₁ q₀) with hφ
    have hpow' : c q₀ ^ N.index = (t * (φ t)⁻¹) ^ N.index := by
      rw [key q₀, ← hpow, map_pow, mul_pow, ← inv_pow]
    exact hcop.pow_left_bijective.injective hpow'
  have hs₂conj : ∀ q, s₂ q = (↑t : G) * s₁ q * (↑t : G)⁻¹ := by
    intro q
    have h := congrArg (Subtype.val) (hconj q)
    rw [hcval, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply (s₁ q) t] at h
    -- h : s₂ q * (s₁ q)⁻¹ = ↑t * (s₁ q * ↑t * (s₁ q)⁻¹)⁻¹
    have h2 : s₂ q * (s₁ q)⁻¹ = ((↑t : G) * s₁ q * (↑t : G)⁻¹) * (s₁ q)⁻¹ := by
      rw [h]; group
    exact mul_right_cancel h2
  -- `s₂` fixes each element of `K₂`: for `x ∈ K₂`, `s₂ (mk x) = x`.
  have hs₂fix : ∀ x, x ∈ K₂ → s₂ ((mk' N) x) = x := by
    intro x hx
    have hsymm : e₂.symm ⟨x, hx⟩ = ((mk' N) x) := by
      rw [QuotientGroup.mk'_apply]; rfl
    have h2 : e₂ ((mk' N) x) = ⟨x, hx⟩ := by rw [← hsymm, MulEquiv.apply_symm_apply]
    rw [hs₂val, h2]
  -- Assemble `K₂ = ConjAct.toConjAct t • K₁`.
  refine ⟨t, ?_⟩
  have hle : K₂ ≤ ConjAct.toConjAct (↑t : G) • K₁ := by
    intro x hx
    have hxeq : x = (↑t : G) * s₁ ((mk' N) x) * (↑t : G)⁻¹ := by
      rw [← hs₂conj ((mk' N) x), hs₂fix x hx]
    rw [hxeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hs : (ConjAct.toConjAct (↑t : G))⁻¹ •
        ((↑t : G) * s₁ ((mk' N) x) * (↑t : G)⁻¹) = s₁ ((mk' N) x) := by
      simp only [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]
      group
    rw [hs]
    exact hmemK₁ _
  have hcardeq : Nat.card ↥(ConjAct.toConjAct (↑t : G) • K₁) = Nat.card ↥K₂ := by
    rw [← Nat.card_congr (Subgroup.equivSMul (ConjAct.toConjAct (↑t : G)) K₁).toEquiv]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hK₁.card_mul_card.trans hK₂.card_mul_card.symm)
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardeq)).symm

/-- **The `N`-conjugacy classes of complements of a coprime chief factor number `≤ 1`** (Nielsen &
Chuang, Problem 5.5 — Ettinger–Høyer–Knill piece ii). Since all complements are `N`-conjugate
(`exists_conjAct_smul_of_isComplement'_of_coprime`), the orbit set of the `N`-conjugation action on
complements is a subsingleton, so has cardinality at most one — the vanishing `|H¹(G ⧸ N, N)| ≤ 1`
in the coprime case. -/
theorem card_orbitRel_quotient_isComplement'_le_one_of_coprime [Finite G] {N : Subgroup G}
    [N.Normal] (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hcop : (Nat.card ↥N).Coprime N.index) :
    Nat.card (MulAction.orbitRel.Quotient ↥N {K : Subgroup G // N.IsComplement' K}) ≤ 1 := by
  rw [Finite.card_le_one_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn' with
  | h K₁ =>
    induction b using Quotient.inductionOn' with
    | h K₂ =>
      apply Quotient.sound'
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      obtain ⟨n, hn⟩ := exists_conjAct_smul_of_isComplement'_of_coprime hab hcop K₂.2 K₁.2
      exact ⟨n, Subtype.ext hn⟩

/-- **A coprime chief factor has at most `|N|` complements** (Nielsen & Chuang, Problem 5.5 —
Ettinger–Høyer–Knill piece ii). All complements being `N`-conjugate collapses the orbit-counting
factorization `#{complements} ≤ |N| · #{classes}` (`card_isComplement'_le_card_mul_card_orbits`) to
`#{complements} ≤ |N| · 1 = |N|`. This is the coprime analogue of the tight cyclic-quotient bound
`card_isComplement'_le_card_of_isCyclic_quotient`, now covering the non-central, non-cyclic-quotient
factors with coprime action. -/
theorem card_isComplement'_le_card_of_coprime [Finite G] {N : Subgroup G} [N.Normal]
    (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hcop : (Nat.card ↥N).Coprime N.index) :
    Nat.card {K : Subgroup G // N.IsComplement' K} ≤ Nat.card ↥N := by
  calc Nat.card {K : Subgroup G // N.IsComplement' K}
      ≤ Nat.card ↥N *
          Nat.card (MulAction.orbitRel.Quotient ↥N {K : Subgroup G // N.IsComplement' K}) :=
        card_isComplement'_le_card_mul_card_orbits N
    _ ≤ Nat.card ↥N * 1 := by
        gcongr
        exact card_orbitRel_quotient_isComplement'_le_one_of_coprime hab hcop
    _ = Nat.card ↥N := mul_one _

/-- **The cohomological class-count hypothesis holds for coprime chief factors** (Nielsen & Chuang,
Problem 5.5 — Ettinger–Høyer–Knill piece ii). The number of `N`-conjugacy classes of complements is
`≤ [G : N]` — the exact `horb` hypothesis of
`card_isCoatom_le_two_mul_card_of_isSolvable_of_orbitBound` — because that count is `≤ 1` (all
complements conjugate) and the index of a subgroup of a finite group is positive. This discharges
the solvable maximal-count recursion's per-chief-factor hypothesis for every abelian chief factor
whose order is coprime to its index, narrowing the residual to the non-coprime factors. -/
theorem card_isComplement'_orbits_le_index_of_coprime [Finite G] {N : Subgroup G} [N.Normal]
    (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hcop : (Nat.card ↥N).Coprime N.index) :
    Nat.card (MulAction.orbitRel.Quotient ↥N {K : Subgroup G // N.IsComplement' K}) ≤ N.index :=
  (card_orbitRel_quotient_isComplement'_le_one_of_coprime hab hcop).trans
    (Nat.one_le_iff_ne_zero.mpr (Subgroup.index_ne_zero_of_finite))

end AxQM.Concrete
