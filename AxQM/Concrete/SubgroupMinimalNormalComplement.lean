/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupFrattiniMaximalCount
import Mathlib.GroupTheory.Complement
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The abelian minimal-normal complement recursion for the maximal-subgroup count

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Prob. 5.5 — Ettinger–Høyer–Knill piece
ii.)* The sole remaining general-`G` ingredient of the Ettinger–Høyer–Knill collision tail is the
**maximal-subgroup count** `3 · #{maximal subgroups of J} ≤ |J|²` (a weak Liebeck–Pyber–Shalev
bound, `SubgroupMaximalCount.lean`). The two known CFSG-free routes to a maximal-subgroup count are
the reduction to **Frattini-free** groups (`SubgroupFrattiniMaximalCount.lean`, the socle route) and
the **chief-series recursion** (the route Wall used to prove `#{maximals} < |G|` for *solvable*
groups without CFSG). This file supplies the foundational step of the second route.

Fix an **abelian minimal normal subgroup** `N ◁ G` (every nontrivial solvable group has one — its
minimal normal subgroups are elementary abelian). The maximal subgroups `M ⋖ G` split by whether
they contain `N`:

* those with `N ≤ M` correspond bijectively to the maximal subgroups of `G ⧸ N`
  (the correspondence theorem, `coatomLeEquivQuotient`);
* those with `N ⊄ M` are **complements of `N`** (`isComplement'_of_isCoatom_of_not_le`): `M ⊔ N = ⊤`
  by maximality, and `M ⊓ N` — normal in `G` because `N` is abelian — is a proper normal subgroup of
  the minimal `N`, hence trivial, so `N ⊓ M = ⊥` and `↑N · ↑M = G`.

Hence the **recursion** (`card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement'`):

`#{maximal subgroups of G} ≤ #{maximal subgroups of G ⧸ N} + #{complements of N in G}`.

Iterated down a chief series, this reduces the maximal-subgroup count to the **complement counts**
`#{complements of each abelian chief factor}` — the genuine hard core (an affine primitive quotient
`V ⋊ H` has `|H¹(H, V)|` conjugacy classes of complements; bounding that sum is exactly what Wall's
theorem does for solvable `G`, and what Liebeck–Pyber–Shalev does — via CFSG — in general). So this
recursion does **not** close the count; it isolates the complement count as the residual, and is the
CFSG-free tool a future extension of Problem 5.5's unconditional identification headline from
nilpotent `G` (already done — nilpotent groups have *no* non-normal maximals) to **solvable** `G`
would build on.
-/

open scoped Pointwise

open Subgroup QuotientGroup

namespace AxQM.Concrete

variable {G : Type*} [Group G]

/-- **A maximal subgroup avoiding an abelian minimal normal subgroup complements it** (Nielsen &
Chuang, Problem 5.5 — Ettinger–Høyer–Knill piece ii). Let `N ◁ G` be **abelian** (`hNab`) and
**minimal normal** (`hNmin`: the only normal subgroups `≤ N` are `⊥` and `N`). If `M` is a maximal
subgroup (`IsCoatom M`) with `N ⊄ M`, then `N` and `M` are complements: `N.IsComplement' M`.

The proof is the classical splitting argument. Maximality forces `M ⊔ N = ⊤` (as `M < M ⊔ N`, since
`N ⊄ M`). The intersection `M ⊓ N` is **normal in `G`**: writing an arbitrary `g = n · m`
(`n ∈ N`, `m ∈ M`, using `↑N · ↑M = ↑(N ⊔ M) = G`), conjugation of `x ∈ M ⊓ N` gives
`g x g⁻¹ = n (m x m⁻¹) n⁻¹ = m x m⁻¹` — the last step because `m x m⁻¹ ∈ N` (as `x ∈ N ◁ G`) and `N`
is abelian, so `n` commutes with it — and `m x m⁻¹ ∈ M ⊓ N`. Being a normal subgroup contained in
the minimal `N` and strictly smaller than it (`N ⊄ M` gives `M ⊓ N ≠ N`), `M ⊓ N = ⊥`, so `N ⊓ M`
is trivial and `↑N · ↑M = G`, i.e. `N.IsComplement' M`. -/
theorem isComplement'_of_isCoatom_of_not_le (N : Subgroup G) [hN : N.Normal]
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hNmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N)
    {M : Subgroup G} (hM : IsCoatom M) (hNM : ¬ N ≤ M) :
    N.IsComplement' M := by
  have hlt : M < M ⊔ N := lt_of_le_of_ne le_sup_left (fun h => hNM (le_sup_right.trans h.ge))
  have hsup : M ⊔ N = ⊤ := hM.2 _ hlt
  have hNsupM : N ⊔ M = ⊤ := by rw [sup_comm]; exact hsup
  have hmulNM : (N : Set G) * (M : Set G) = Set.univ := by
    rw [← Subgroup.normal_mul N M, hNsupM]; rfl
  -- `M ⊓ N` is normal in `G`.
  have hnorm : (M ⊓ N).Normal := by
    constructor
    intro x hx g
    obtain ⟨hxM, hxN⟩ := hx
    have hg : g ∈ (N : Set G) * (M : Set G) := by rw [hmulNM]; trivial
    obtain ⟨n, hn, m, hm, rfl⟩ := hg
    have hmxM : m * x * m⁻¹ ∈ M := mul_mem (mul_mem hm hxM) (inv_mem hm)
    have hmxN : m * x * m⁻¹ ∈ N := hN.conj_mem x hxN m
    have hconj : n * m * x * (n * m)⁻¹ = m * x * m⁻¹ := by
      have hc := hNab n hn (m * x * m⁻¹) hmxN
      calc n * m * x * (n * m)⁻¹ = n * (m * x * m⁻¹) * n⁻¹ := by group
        _ = (m * x * m⁻¹) * n * n⁻¹ := by rw [hc]
        _ = m * x * m⁻¹ := by group
    rw [hconj]
    exact ⟨hmxM, hmxN⟩
  -- Minimality forces `M ⊓ N = ⊥`.
  have hbot : M ⊓ N = ⊥ := (hNmin _ hnorm inf_le_right).resolve_right fun h => hNM (h ▸ inf_le_left)
  have hdisj : Disjoint N M := by rw [disjoint_iff, inf_comm]; exact hbot
  exact Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmulNM

/-- **The maximal subgroups avoiding `N` inject into the complements of `N`** (Nielsen & Chuang,
Problem 5.5 — Ettinger–Høyer–Knill piece ii). For an abelian minimal normal subgroup `N ◁ G` of a
finite group, the number of maximal subgroups `M` with `N ⊄ M` is at most the number of complements
of `N` in `G`, since each such `M` is a complement (`isComplement'_of_isCoatom_of_not_le`) and the
assignment `M ↦ M` is injective. -/
theorem card_isCoatom_not_le_le_card_isComplement' [Finite G] (N : Subgroup G) [N.Normal]
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hNmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) :
    Nat.card {M : Subgroup G // IsCoatom M ∧ ¬ N ≤ M}
      ≤ Nat.card {M : Subgroup G // N.IsComplement' M} := by
  apply Nat.card_le_card_of_injective
    (f := fun x => ⟨x.1, isComplement'_of_isCoatom_of_not_le N hNab hNmin x.2.1 x.2.2⟩)
  intro a b hab
  apply Subtype.ext
  simpa using congrArg (fun t : {M : Subgroup G // N.IsComplement' M} => t.1) hab

/-- **The correspondence bijection between the maximal subgroups of `G` containing a normal subgroup
`N` and the maximal subgroups of `G ⧸ N`** (Nielsen & Chuang, Problem 5.5 — Ettinger–Høyer–Knill
piece ii). The subgroup correspondence theorem: `M ↦ M.map (mk' N)` — with inverse
`K ↦ K.comap (mk' N)` — is a bijection between the coatoms `M ⋖ G` with `N ≤ M` and the coatoms of
`G ⧸ N`, the coatom-preservation supplied by `isCoatom_map_of_ker_le` (using `ker (mk' N) = N ≤ M`)
and Mathlib's `Subgroup.isCoatom_comap_of_surjective`, and the round trips by the `map`/`comap`
self-inverse identities. This generalizes the Frattini-specific `coatomEquivQuotientFrattini` to an
arbitrary normal `N` (where only the coatoms *containing* `N` correspond). -/
def coatomLeEquivQuotient (N : Subgroup G) [N.Normal] :
    {M : Subgroup G // IsCoatom M ∧ N ≤ M} ≃ {K : Subgroup (G ⧸ N) // IsCoatom K} where
  toFun M := ⟨M.1.map (mk' N),
    isCoatom_map_of_ker_le (mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact M.2.2) M.2.1⟩
  invFun K := ⟨K.1.comap (mk' N),
    Subgroup.isCoatom_comap_of_surjective (mk'_surjective _) K.2,
    by have h := Subgroup.ker_le_comap (mk' N) K.1; rwa [QuotientGroup.ker_mk'] at h⟩
  left_inv M := Subtype.ext (Subgroup.comap_map_eq_self
    (by rw [QuotientGroup.ker_mk']; exact M.2.2))
  right_inv K := Subtype.ext (Subgroup.map_comap_eq_self_of_surjective (mk'_surjective _) K.1)

/-- **The maximal subgroups containing `N` are equinumerous with those of `G ⧸ N`** (Nielsen &
Chuang, Problem 5.5 — Ettinger–Høyer–Knill piece ii): the cardinality form of
`coatomLeEquivQuotient`, `#{M ⋖ G : N ≤ M} = #{maximal subgroups of G ⧸ N}`. -/
theorem card_isCoatom_and_le_eq_card_isCoatom_quotient (N : Subgroup G) [N.Normal] :
    Nat.card {M : Subgroup G // IsCoatom M ∧ N ≤ M}
      = Nat.card {K : Subgroup (G ⧸ N) // IsCoatom K} :=
  Nat.card_congr (coatomLeEquivQuotient N)

/-- **The abelian minimal-normal recursion for the maximal-subgroup count** (Nielsen & Chuang,
Problem 5.5 — Ettinger–Høyer–Knill piece ii). For an **abelian minimal normal** subgroup `N ◁ G` of
a finite group `G`,

`#{maximal subgroups of G} ≤ #{maximal subgroups of G ⧸ N} + #{complements of N in G}`.

This is the foundational step of the chief-series recursion underlying every CFSG-free
maximal-subgroup count (Wall's `#{maximals} < |G|` for solvable groups): the coatoms of `G` split
into those containing `N` — equinumerous with the coatoms of `G ⧸ N`
(`card_isCoatom_and_le_eq_card_isCoatom_quotient`) — and those avoiding `N`, which inject into the
complements of `N` (`card_isCoatom_not_le_le_card_isComplement'`). Iterating down a chief series
reduces the maximal count to the complement counts of the abelian chief factors — the residual whose
sum Wall (solvable) / Liebeck–Pyber–Shalev (general, CFSG) bound. It therefore does **not** close
Problem 5.5's remaining count, but isolates the complement count as the honest hard core and is the
tool a solvable-`G` extension of the unconditional identification headline would build on. -/
theorem card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement' [Finite G]
    (N : Subgroup G) [N.Normal]
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hNmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) :
    Nat.card {M : Subgroup G // IsCoatom M}
      ≤ Nat.card {K : Subgroup (G ⧸ N) // IsCoatom K}
        + Nat.card {M : Subgroup G // N.IsComplement' M} := by
  classical
  -- Partition the coatoms by whether they contain `N`.
  have e1 : {M : Subgroup G // IsCoatom M ∧ N ≤ M}
      ≃ {x : {M : Subgroup G // IsCoatom M} // N ≤ x.1} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun M => IsCoatom M) (fun M => N ≤ M)).symm
  have e2 : {M : Subgroup G // IsCoatom M ∧ ¬ N ≤ M}
      ≃ {x : {M : Subgroup G // IsCoatom M} // ¬ N ≤ x.1} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun M => IsCoatom M) (fun M => ¬ N ≤ M)).symm
  have hpart : Nat.card {M : Subgroup G // IsCoatom M}
      = Nat.card {M : Subgroup G // IsCoatom M ∧ N ≤ M}
        + Nat.card {M : Subgroup G // IsCoatom M ∧ ¬ N ≤ M} := by
    rw [Nat.card_congr e1, Nat.card_congr e2, ← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun x : {M : Subgroup G // IsCoatom M} => N ≤ x.1)).symm
  rw [hpart, card_isCoatom_and_le_eq_card_isCoatom_quotient]
  exact Nat.add_le_add_left
    (card_isCoatom_not_le_le_card_isComplement' N hNab hNmin) _

end AxQM.Concrete
