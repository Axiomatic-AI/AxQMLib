/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The Frattini reduction of the maximal-subgroup count (Ettinger–Høyer–Knill piece ii)

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Prob. 5.5.)* The sole remaining general-`G`
ingredient of the Ettinger–Høyer–Knill collision tail is the **maximal-subgroup count**: every
finite group `J` has `3 · #{maximal subgroups of J} ≤ |J|²` (a weak form of the
Liebeck–Pyber–Shalev bound, `SubgroupMaximalCount.lean`). This file discharges the **first classical
reduction** of that count — the standard opening move of every proof of a maximal-subgroup bound —
namely that the count is unchanged on passing to the **Frattini quotient** `G ⧸ Φ(G)`:

`#{maximal subgroups of G} = #{maximal subgroups of G ⧸ Φ(G)}`
(`card_isCoatom_eq_card_isCoatom_quotient_frattini`).

Every maximal (proper) subgroup `M` of `G` is a **coatom** of the subgroup lattice, and contains the
Frattini subgroup `Φ(G) = ⋂ {maximal subgroups}` (`frattini_le_coatom`). The correspondence theorem
(fourth isomorphism theorem) therefore restricts to a bijection between the coatoms of `G` and the
coatoms of `G ⧸ Φ(G)`, realised concretely by `M ↦ M.map (mk' Φ)` with inverse `K ↦ K.comap (mk' Φ)`
(`coatomEquivQuotientFrattini`). The two coatom-preservation halves are Mathlib's
`Subgroup.isCoatom_comap_of_surjective` (a coatom of `G ⧸ N` pulls back to a coatom of `G`) and its
dual `isCoatom_map_of_ker_le` (a coatom containing `ker f` pushes to a coatom of the image), which
this file supplies — the subgroup analogue of `Submodule.isCoatom_map_of_ker_le`, absent from
Mathlib. Both hold from the mutually inverse `map`/`comap` along a surjection: the coatom property
transports across the order-preserving bijection between the subgroups `≥ ker f` and the subgroups
of the image.

Since `|G ⧸ Φ(G)| ≤ |G|`, the count bound for `G` **follows from** the same bound for the smaller,
Frattini-free quotient (`three_mul_card_isCoatom_le_sq_of_quotient_frattini`): the item's residual
maximal-subgroup count is reduced to **groups with trivial Frattini subgroup** — the shape in
which the deeper (Liebeck–Pyber–Shalev / CFSG-strength) analysis is actually carried out. This does
*not* close the count (Frattini-free groups are still hard — simple and almost-simple groups
have trivial Frattini subgroup), but it removes the solvable-Frattini padding, the genuine
first step.
-/

namespace AxQM.Concrete

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

/-- **A coatom containing `ker f` maps to a coatom of the image under a surjection** — the subgroup
analogue of `Submodule.isCoatom_map_of_ker_le`, and the `map`-dual of Mathlib's
`Subgroup.isCoatom_comap_of_surjective`. For a surjective group homomorphism `f : G →* H` and a
coatom (maximal proper subgroup) `M` of `G` with `ker f ≤ M`, the image `M.map f` is a coatom of
`H`. Because `ker f ≤ M`, the maps `M ↦ M.map f` and `comap f` are mutually inverse on the subgroups
`≥ ker f`, so the maximality of `M` (nothing strictly between `M` and `⊤`) transports to `M.map f`:
any subgroup strictly above it pulls back strictly above `M`, forced to be `⊤`, whence (pushing
forward along the surjection) the original is `⊤`. -/
theorem isCoatom_map_of_ker_le {H : Type*} [Group H] {f : G →* H} (hf : Function.Surjective f)
    {M : Subgroup G} (hker : f.ker ≤ M) (hM : IsCoatom M) : IsCoatom (M.map f) := by
  have hself : (M.map f).comap f = M := Subgroup.comap_map_eq_self hker
  refine ⟨?_, ?_⟩
  · intro htop
    exact hM.1 (by rw [← hself, htop, Subgroup.comap_top])
  · intro B' hlt
    have hle : M ≤ B'.comap f := by
      have h := Subgroup.comap_mono (f := f) hlt.le; rwa [hself] at h
    have hstrict : M < B'.comap f :=
      lt_of_le_of_ne hle fun heq => hlt.ne (by
        rw [heq]; exact Subgroup.map_comap_eq_self_of_surjective hf B')
    have hcm := hM.2 _ hstrict
    calc B' = (B'.comap f).map f := (Subgroup.map_comap_eq_self_of_surjective hf B').symm
      _ = (⊤ : Subgroup G).map f := by rw [hcm]
      _ = ⊤ := Subgroup.map_top_of_surjective _ hf

/-- **The correspondence bijection between the coatoms of `G` and the coatoms of `G ⧸ Φ(G)`.** Every
coatom `M ⋖ ⊤` contains the Frattini subgroup `Φ(G)` (`frattini_le_coatom`,
as `Φ(G)` is the intersection of all coatoms), so `M ↦ M.map (mk' Φ(G))` — with inverse
`K ↦ K.comap (mk' Φ(G))` — is a bijection of coatoms, the coatom-preservation supplied by
`isCoatom_map_of_ker_le` (using `ker (mk' Φ(G)) = Φ(G) ≤ M`) and Mathlib's
`Subgroup.isCoatom_comap_of_surjective`, and the round trips by the `map`/`comap` self-inverse
identities (`Subgroup.comap_map_eq_self`; `Subgroup.map_comap_eq_self_of_surjective`
for the surjection `mk' Φ(G)`). -/
def coatomEquivQuotientFrattini (G : Type*) [Group G] :
    {M : Subgroup G // IsCoatom M} ≃ {K : Subgroup (G ⧸ frattini G) // IsCoatom K} where
  toFun M := ⟨M.1.map (mk' (frattini G)), isCoatom_map_of_ker_le (mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact frattini_le_coatom M.2) M.2⟩
  invFun K := ⟨K.1.comap (mk' (frattini G)),
    Subgroup.isCoatom_comap_of_surjective (mk'_surjective _) K.2⟩
  left_inv M := Subtype.ext (Subgroup.comap_map_eq_self
    (by rw [QuotientGroup.ker_mk']; exact frattini_le_coatom M.2))
  right_inv K := Subtype.ext (Subgroup.map_comap_eq_self_of_surjective (mk'_surjective _) K.1)

/-- **The number of maximal subgroups is Frattini-invariant** (Nielsen & Chuang, Problem 5.5 —
Ettinger–Høyer–Knill piece ii, first reduction). For any group `G`,

`#{maximal subgroups of G} = #{maximal subgroups of G ⧸ Φ(G)}`,

the counts of coatoms of the two subgroup lattices agreeing via `coatomEquivQuotientFrattini` (every
maximal subgroup contains the Frattini subgroup, so the correspondence theorem restricts to a
bijection of coatoms). This is the standard opening reduction of any maximal-subgroup count — it
reduces the count to the **Frattini-free** quotient `G ⧸ Φ(G)` (where `Φ(G ⧸ Φ(G))` is trivial). -/
theorem card_isCoatom_eq_card_isCoatom_quotient_frattini (G : Type*) [Group G] :
    Nat.card {M : Subgroup G // IsCoatom M}
      = Nat.card {K : Subgroup (G ⧸ frattini G) // IsCoatom K} :=
  Nat.card_congr (coatomEquivQuotientFrattini G)

/-- **The maximal-subgroup count bound for `G` reduces to its Frattini quotient** (Nielsen & Chuang,
Problem 5.5 — the item-facing form). For a finite group `G`, the count bound
`3 · #{maximal subgroups of G} ≤ |G|²` — the Liebeck–Pyber–Shalev-strength ingredient the
Ettinger–Høyer–Knill collision tail needs (via `nonnormal_maximal_classCard_le_of_card_maximal_le`,
`SubgroupMaximalCount.lean`) — **follows from the same bound on the Frattini quotient**
`3 · #{maximal subgroups of G ⧸ Φ(G)} ≤ |G ⧸ Φ(G)|²`, since the coatom counts are equal
(`card_isCoatom_eq_card_isCoatom_quotient_frattini`) and `|G ⧸ Φ(G)| ≤ |G|`. So Problem 5.5's sole
open general-`G` count may be assumed on **Frattini-free** groups only — the shape in which the
Liebeck–Pyber–Shalev reduction to almost-simple groups proceeds. -/
theorem three_mul_card_isCoatom_le_sq_of_quotient_frattini [Finite G]
    (h : 3 * Nat.card {K : Subgroup (G ⧸ frattini G) // IsCoatom K}
          ≤ Nat.card (G ⧸ frattini G) ^ 2) :
    3 * Nat.card {M : Subgroup G // IsCoatom M} ≤ Nat.card G ^ 2 := by
  rw [card_isCoatom_eq_card_isCoatom_quotient_frattini]
  exact h.trans (Nat.pow_le_pow_left
    (Nat.card_le_card_of_surjective (mk' (frattini G)) (mk'_surjective _)) 2)

end AxQM.Concrete
