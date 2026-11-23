/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupMinimalNormalComplement
import AxQM.Concrete.SubgroupCount
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# An elementary bound on the number of complements of a normal subgroup

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Prob. 5.5 — Ettinger–Høyer–Knill piece
ii.)* The abelian minimal-normal recursion `SubgroupMinimalNormalComplement.lean` reduced the
maximal-subgroup count of `G` to `#{maximal subgroups of G ⧸ N} + #{complements of N in G}` for an
abelian minimal normal `N ◁ G`. Iterated down a chief series, the residual is the **complement
count** `#{complements of each abelian chief factor}` — the honest hard core. This file gives that
residual its concrete elementary bounds — with no cohomology and no CFSG — via one **section-count**
engine parametrised by any generating finset of the quotient:

`#{complements of N in G} ≤ |N| ^ |s|`   for any `s` with `⟨s⟩ = G ⧸ N`
(`card_isComplement'_le_pow_card_of_closure_eq_top`).

The mechanism is the section picture. Fix a set-theoretic representative `rep : G ⧸ N → G`
(`Quotient.out`, so `rep x` maps to `x`). A complement `M` decomposes each `rep x` uniquely as
`nₓ · pₓ` with `nₓ ∈ N`, `pₓ ∈ M` (the complement equivalence `Subgroup.IsComplement.equiv`); the
map `M ↦ (x ↦ nₓ)` sends complements into the functions `↥s → ↥N`, of which there are `|N| ^ |s|`.
It is **injective** because a complement is recovered from those `N`-parts: the `M`-parts
`pₓ = nₓ⁻¹ · rep x` lie in `M`, project onto the generators `x` of `G ⧸ N` (as `nₓ ∈ N`), so the
subgroup `T = ⟨pₓ⟩` joins `N` to `⊤`; being `≤ M` and jointly generating `G` with `N`, `T` is itself
a complement of `N`, hence has order `|G|/|N| = |M|`, so `T = M`
(`eq_of_isComplement'_of_le_of_sup`). Equal `N`-parts thus force equal `M`.

Optimising the generating set `s` yields the two concrete bounds:

* **`card_isComplement'_le`** (the `log₂|G ⧸ N|`-size generating set of
  `exists_closure_finset_card_le_log`): `#{complements} ≤ |N| ^ log₂|G ⧸ N|`. This is deliberately
  **crude** — `|N| ^ log₂|G|` can be super-polynomial — so, like the recursion it feeds, it does not
  close Problem 5.5's remaining count (whose linear sample count needs the *sharp* per-factor bound
  `|H¹(H, V)| ≤ |V|`, elementary for solvable `G` by Wall, CFSG in general).
* **`card_isComplement'_le_card_of_isCyclic_quotient`** (when `G ⧸ N` is **cyclic**, a *single*
  generator): `#{complements} ≤ |N|`. This is **tight** (e.g. `N = A₃ ◁ S₃`) and covers
  **non-central** chief factors — unlike the central-case
  `card_isComplement'_le_index_of_le_center` (which needs `N ≤ Z(G)`) — so it discharges the
  per-factor complement hypothesis of
  `card_isCoatom_le_two_mul_card_of_isSolvable_of_complementBound` for every chief factor with
  cyclic quotient action, narrowing that recursion's residual to the non-cyclic-quotient factors.
-/

open scoped Pointwise

open Subgroup QuotientGroup

namespace AxQM.Concrete

variable {G : Type*} [Group G]

/-- **A subgroup of a complement that still generates `G` with `N` is that whole complement**
(Nielsen & Chuang, Problem 5.5 — Ettinger–Høyer–Knill piece ii). If `N.IsComplement' M` and
`T ≤ M` with `N ⊔ T = ⊤`, then `T = M`. The point is that `T` is then *itself* a complement of `N`
(`Disjoint N T` from `T ≤ M` and disjointness of the complement `M`; `↑N * ↑T = univ` from
`N ⊔ T = ⊤` with `N` normal), so `|N| · |T| = |G| = |N| · |M|` forces `|T| = |M|`, and a subgroup of
`M` with the same order is all of `M`. -/
theorem eq_of_isComplement'_of_le_of_sup [Finite G] {N M T : Subgroup G} [N.Normal]
    (hM : N.IsComplement' M) (hTM : T ≤ M) (hsup : N ⊔ T = ⊤) : T = M := by
  have hTc : N.IsComplement' T := by
    refine isComplement'_of_disjoint_and_mul_eq_univ (hM.disjoint.mono_right hTM) ?_
    rw [← Subgroup.normal_mul N T, hsup]; rfl
  have hcard : Nat.card ↥T = Nat.card ↥M :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hTc.card_mul_card.trans hM.card_mul_card.symm)
  exact eq_of_le_of_card_ge hTM hcard.ge

/-- **The number of complements of a normal subgroup `N` is at most `|N| ^ |s|`, for any generating
finset `s` of the quotient `G ⧸ N`** (Nielsen & Chuang, Problem 5.5 — Ettinger–Høyer–Knill piece
ii). This is the elementary section count, in the form parametrised by the generating set: a
complement `M` decomposes the representatives `rep x` of the generators `x ∈ s` as `nₓ · pₓ`
(`Subgroup.IsComplement.equiv`), and `M ↦ (x ↦ nₓ ∈ N)` injects the complements into `↥s → ↥N`
(`|N| ^ |s|` functions). Injectivity: the `M`-parts `pₓ = nₓ⁻¹ · rep x ∈ M` project onto the
generators `x` of `G ⧸ N`, so the subgroup they generate joins `N` to `⊤` and — being `≤ M` —
equals `M` (`eq_of_isComplement'_of_le_of_sup`); thus `M` is determined by the `N`-parts.

Specialising `s` gives the concrete bounds: the `log₂|G ⧸ N|`-size generating set of
`exists_closure_finset_card_le_log` yields the (crude) `card_isComplement'_le`, and — for a
**cyclic** quotient — the single-generator set yields the (tight)
`card_isComplement'_le_card_of_isCyclic_quotient`. -/
theorem card_isComplement'_le_pow_card_of_closure_eq_top [Finite G] (N : Subgroup G) [N.Normal]
    (s : Finset (G ⧸ N)) (hs : Subgroup.closure (↑s : Set (G ⧸ N)) = ⊤) :
    Nat.card {M : Subgroup G // N.IsComplement' M} ≤ Nat.card ↥N ^ s.card := by
  classical
  -- A set-theoretic representative of each coset.
  set rep : G ⧸ N → G := fun x => Quotient.out x with hrepdef
  have hrep : ∀ x : G ⧸ N, (rep x : G ⧸ N) = x := fun x => QuotientGroup.out_eq' x
  -- The injection `M ↦ (x ↦ N-part of rep x)`.
  refine (Nat.card_le_card_of_injective
    (fun M => fun x : ↥s => (M.2.equiv (rep ↑x)).1) ?_).trans ?_
  · -- Injectivity: equal `N`-parts on the generators force equal complements.
    rintro ⟨M, hM⟩ ⟨M', hM'⟩ hEq
    -- Equal `N`-parts of `rep x` for every generator `x ∈ s`.
    have hNeq : ∀ x : ↥s, (↑(hM.equiv (rep ↑x)).1 : G) = ↑(hM'.equiv (rep ↑x)).1 :=
      fun x => congrArg Subtype.val (congrFun hEq x)
    -- Hence equal `M`-parts.
    have hmeq : ∀ x : ↥s, (↑(hM.equiv (rep ↑x)).2 : G) = ↑(hM'.equiv (rep ↑x)).2 := by
      intro x
      have h1 := hM.equiv_fst_mul_equiv_snd (rep ↑x)
      have h2 := hM'.equiv_fst_mul_equiv_snd (rep ↑x)
      rw [hNeq x] at h1
      exact mul_left_cancel (h1.trans h2.symm)
    -- The subgroup generated by the `M`-parts.
    set T : Subgroup G :=
      Subgroup.closure (Set.range fun x : ↥s => (↑(hM.equiv (rep ↑x)).2 : G)) with hTdef
    have hpM : ∀ x : ↥s, (↑(hM.equiv (rep ↑x)).2 : G) ∈ M := fun x => (hM.equiv (rep ↑x)).2.2
    have hpM' : ∀ x : ↥s, (↑(hM.equiv (rep ↑x)).2 : G) ∈ M' := by
      intro x; rw [hmeq x]; exact (hM'.equiv (rep ↑x)).2.2
    have hTM : T ≤ M := (Subgroup.closure_le _).mpr (by rintro _ ⟨x, rfl⟩; exact hpM x)
    have hTM' : T ≤ M' := (Subgroup.closure_le _).mpr (by rintro _ ⟨x, rfl⟩; exact hpM' x)
    -- `mk (M-part of rep x) = x` for `x ∈ s`.
    have hmkp : ∀ x : ↥s, (mk' N) (↑(hM.equiv (rep ↑x)).2 : G) = (↑x : G ⧸ N) := by
      intro x
      have hf := hM.equiv_fst_mul_equiv_snd (rep ↑x)
      have hn : (mk' N) (↑(hM.equiv (rep ↑x)).1 : G) = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (hM.equiv (rep ↑x)).1.2
      have hstep : (mk' N) (↑(hM.equiv (rep ↑x)).1 : G) * (mk' N) (↑(hM.equiv (rep ↑x)).2 : G)
          = (mk' N) (rep ↑x) := by rw [← map_mul, hf]
      rw [hn, one_mul] at hstep
      rw [hstep, QuotientGroup.mk'_apply]; exact hrep ↑x
    -- `map (mk' N) T = ⊤`, hence `N ⊔ T = ⊤`.
    have hmapT : Subgroup.map (mk' N) T = ⊤ := by
      rw [eq_top_iff, ← hs]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_map]
      exact ⟨↑(hM.equiv (rep x)).2, Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩, hmkp ⟨x, hx⟩⟩
    have hsup : N ⊔ T = ⊤ := by
      have h := Subgroup.comap_map_eq (mk' N) T
      rw [hmapT, QuotientGroup.ker_mk', Subgroup.comap_top] at h
      rw [sup_comm]; exact h.symm
    -- Both `M` and `M'` equal `T`.
    have hTMeq : T = M := eq_of_isComplement'_of_le_of_sup hM hTM hsup
    have hTM'eq : T = M' := eq_of_isComplement'_of_le_of_sup hM' hTM' hsup
    exact Subtype.ext (hTMeq.symm.trans hTM'eq)
  · -- The function-space count `|N| ^ |s|`.
    simp [Nat.card_fun]

/-- **The number of complements of a normal subgroup `N` is at most `|N| ^ log₂|G ⧸ N|`** (Nielsen &
Chuang, Problem 5.5 — Ettinger–Høyer–Knill piece ii). The section count
`card_isComplement'_le_pow_card_of_closure_eq_top` applied to the `≤ log₂|G ⧸ N|`-size generating
finset of `exists_closure_finset_card_le_log`.

The bound is crude (`|N| ^ log₂|G|` may be super-polynomial): iterated over a chief series it
reduces the maximal-subgroup count to the complement counts but does not by itself yield the
polynomial (Liebeck–Pyber–Shalev / Wall) bound Problem 5.5's linear sample count needs — that
requires the sharp per-factor complement bound `|H¹| ≤ |V|`, of which this is the elementary
predecessor. -/
theorem card_isComplement'_le [Finite G] (N : Subgroup G) [N.Normal] :
    Nat.card {M : Subgroup G // N.IsComplement' M}
      ≤ Nat.card ↥N ^ Nat.log 2 (Nat.card (G ⧸ N)) := by
  -- A generating finset of `G ⧸ N` of size `≤ log₂|G ⧸ N|`.
  obtain ⟨s, hs, hcard⟩ := exists_closure_finset_card_le_log (⊤ : Subgroup (G ⧸ N))
  exact (card_isComplement'_le_pow_card_of_closure_eq_top N s hs).trans
    (Nat.pow_le_pow_right Nat.card_pos hcard)

/-- **When the quotient `G ⧸ N` is cyclic, `N` has at most `|N|` complements** (Nielsen & Chuang,
Problem 5.5 — Ettinger–Høyer–Knill piece ii). A cyclic quotient is generated by a *single* element,
so the section count `card_isComplement'_le_pow_card_of_closure_eq_top` with a one-element
generating set gives `#{complements of N} ≤ |N| ^ 1 = |N|`.

The picture: a complement `M`, being `≃ G ⧸ N` (`Subgroup.IsComplement'.QuotientMulEquiv`), is
cyclic and generated by its unique element over a fixed generator of `G ⧸ N`; that element lies
in one `N`-coset, of which there are `|N|`, and determines `M`. The bound is **tight** —
e.g. `N = A₃ ◁ S₃` with `G ⧸ N ≅ ℤ/2`: the three order-two complements `⟨(i j)⟩` number exactly
`|A₃| = 3` — and it covers **non-central** chief factors, unlike the central-case bound
`card_isComplement'_le_index_of_le_center` (needs `N ≤ Z(G)`). Since `|N| ≤ |G|`, it discharges
the per-factor complement hypothesis of
`card_isCoatom_le_two_mul_card_of_isSolvable_of_complementBound` for every chief factor with cyclic
quotient action, narrowing that recursion's residual to the factors whose quotient action is
non-cyclic. -/
theorem card_isComplement'_le_card_of_isCyclic_quotient [Finite G] (N : Subgroup G) [N.Normal]
    (hcyc : IsCyclic (G ⧸ N)) :
    Nat.card {M : Subgroup G // N.IsComplement' M} ≤ Nat.card ↥N := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  -- A cyclic quotient is generated by the single element `g`.
  have htop : Subgroup.closure (↑({g} : Finset (G ⧸ N)) : Set (G ⧸ N)) = ⊤ := by
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]
    exact (Subgroup.eq_top_iff' _).mpr hg
  simpa using card_isComplement'_le_pow_card_of_closure_eq_top N ({g} : Finset (G ⧸ N)) htop

/-- **The concrete abelian minimal-normal recursion for the maximal-subgroup count** (Nielsen &
Chuang, Problem 5.5 — Ettinger–Høyer–Knill piece ii). Composing the abelian minimal-normal
recursion `card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement'` with the elementary
complement count `card_isComplement'_le` gives, for an **abelian minimal normal** subgroup `N ◁ G`
of a finite group,

`#{maximal subgroups of G} ≤ #{maximal subgroups of G ⧸ N} + |N| ^ log₂|G ⧸ N|`.

This turns the recursion's abstract complement count into an explicit numeric term: iterated down a
chief series it bounds the maximal count of a solvable `G` by a sum of complement powers. The bound
is crude (the complement term may be super-polynomial), so it does not close Problem 5.5's remaining
count; it is the elementary form the sharp Wall / Liebeck–Pyber–Shalev refinement sharpens. -/
theorem card_isCoatom_le_card_isCoatom_quotient_add_pow [Finite G]
    (N : Subgroup G) [N.Normal]
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hNmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) :
    Nat.card {M : Subgroup G // IsCoatom M}
      ≤ Nat.card {K : Subgroup (G ⧸ N) // IsCoatom K}
        + Nat.card ↥N ^ Nat.log 2 (Nat.card (G ⧸ N)) :=
  (card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement' N hNab hNmin).trans
    (Nat.add_le_add_left (card_isComplement'_le N) _)

end AxQM.Concrete
