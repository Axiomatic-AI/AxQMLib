/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupMinimalNormalComplement

/-!
# Solvable groups have an abelian minimal normal subgroup — the recursion's entry point

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Prob. 5.5 — Ettinger–Høyer–Knill piece
ii.)* The abelian minimal-normal recursion for the maximal-subgroup count
(`card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement'`,
`SubgroupMinimalNormalComplement.lean`) takes as input an **abelian minimal normal** subgroup
`N ◁ G`. To drive it as a *chief-series recursion* on a **solvable** group — the CFSG-free route
Wall used to prove `#{maximals} < |G|` for solvable groups — one must know such an `N` always
exists. This file supplies exactly that existence step, discharging the recursion's hypotheses for
every nontrivial finite solvable group, and packages the resulting single descent step in
strong-induction-ready form.

The existence is elementary. In a finite group the nontrivial normal subgroups form a nonempty
(it contains `⊤`) finite — hence well-founded — collection, so a **minimal** one `N` exists (no
nontrivial normal subgroup lies strictly below it): this is the minimality hypothesis `hNmin`. Its
**abelianness** is where solvability enters: the commutator `⁅N, N⁆` is normal in `G`
(`Subgroup.commutator_normal`, both factors normal) and contained in `N`
(`Subgroup.commutator_le_self`), so by minimality it is `⊥` or `N`; it cannot be `N` because in a
solvable group every nontrivial subgroup strictly contains its own commutator
(`Group.IsSolvable.commutator_lt_of_ne_bot`), so `⁅N, N⁆ = ⊥`, i.e. `N` is abelian
(`commutatorElement_eq_one_iff_commute`). (A minimal normal subgroup of a solvable group is in fact
elementary abelian; only its abelianness is needed here.)

Composing with the recursion yields the **solvable descent step**
(`exists_normal_card_isCoatom_le_of_isSolvable`): a nontrivial finite solvable `G` has a normal
`N ≠ ⊥` with `|G ⧸ N| < |G|` and

`#{maximal subgroups of G} ≤ #{maximal subgroups of G ⧸ N} + #{complements of N in G}`,

with `G ⧸ N` again finite solvable (`solvable_quotient_of_solvable`) — precisely the shape a strong
induction on `|G|` consumes. As emphasised in `SubgroupMinimalNormalComplement.lean`, this recursion
isolates but does **not** close the count: the residual is the sum of the **complement counts** of
the abelian chief factors (Wall's theorem for solvable `G`; Liebeck–Pyber–Shalev, via CFSG, in
general).
-/

open Subgroup QuotientGroup

namespace AxQM.Concrete

variable {G : Type*} [Group G] [Finite G]

/-- **A nontrivial finite solvable group has an abelian minimal normal subgroup** (Nielsen &
Chuang, Problem 5.5 — Ettinger–Høyer–Knill piece ii). For a nontrivial finite solvable group `G`
there is a normal subgroup `N ≠ ⊥` that is **abelian** (all its elements commute) and **minimal
normal** (the only normal subgroups `≤ N` are `⊥` and `N`) — exactly the hypotheses the
maximal-subgroup recursion `card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement'`
consumes.

Existence of a minimal nontrivial normal subgroup is well-foundedness of the finite subgroup lattice
applied to the nonempty set `{N normal | N ≠ ⊥}` (it contains `⊤`). Abelianness uses solvability:
`⁅N, N⁆` is normal in `G` and `≤ N`, so it is `⊥` or `N` by minimality, and
`Group.IsSolvable.commutator_lt_of_ne_bot` (`⁅N, N⁆ < N` for `N ≠ ⊥`) rules out `N`, forcing
`⁅N, N⁆ = ⊥`.
This is the entry point of the chief-series recursion on solvable groups. -/
theorem exists_abelian_minimalNormal_of_isSolvable [Nontrivial G] [Group.IsSolvable G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧
      ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N := by
  classical
  -- The nontrivial normal subgroups form a nonempty (`⊤` is one), finite, well-founded family.
  have hne : {N : Subgroup G | N.Normal ∧ N ≠ ⊥}.Nonempty :=
    ⟨⊤, ⟨inferInstance, top_ne_bot⟩⟩
  obtain ⟨N, ⟨hNnorm, hNbot⟩, hNmin⟩ :=
    (Finite.to_wellFoundedLT (α := Subgroup G)).has_min _ hne
  have := hNnorm
  -- Minimality: a normal subgroup `≤ N` that is nontrivial cannot lie strictly below `N`.
  have hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N := by
    intro K hKnorm hKle
    by_cases hKbot : K = ⊥
    · exact Or.inl hKbot
    · exact Or.inr (hKle.lt_or_eq.resolve_left (hNmin K ⟨hKnorm, hKbot⟩))
  refine ⟨N, hNnorm, hNbot, ?_, hmin⟩
  -- Abelianness: `⁅N, N⁆` is normal in `G` and `≤ N`, hence `⊥` or `N`; solvability rules out `N`.
  have hcbot : ⁅N, N⁆ = ⊥ := by
    rcases hmin ⁅N, N⁆ (Subgroup.commutator_normal N N) (Subgroup.commutator_le_self N) with h | h
    · exact h
    · exact absurd h (ne_of_lt (Group.IsSolvable.commutator_lt_of_ne_bot hNbot))
  intro a ha b hb
  have hmem := Subgroup.commutator_mem_commutator (H₁ := N) (H₂ := N) ha hb
  rw [hcbot, Subgroup.mem_bot] at hmem
  exact (commutatorElement_eq_one_iff_commute.mp hmem).eq

/-- **The solvable descent step of the maximal-subgroup recursion** (Nielsen & Chuang, Problem 5.5 —
Ettinger–Høyer–Knill piece ii). A nontrivial finite solvable group `G` has a normal subgroup
`N ≠ ⊥` with strictly smaller quotient `|G ⧸ N| < |G|` and

`#{maximal subgroups of G} ≤ #{maximal subgroups of G ⧸ N} + #{complements of N in G}`.

This composes `exists_abelian_minimalNormal_of_isSolvable` (which discharges the abelian and
minimal-normal hypotheses) with the recursion
`card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement'`. Since `G ⧸ N` is again finite
solvable (`solvable_quotient_of_solvable`) and strictly smaller, this is the single step a strong
induction on `|G|` iterates down a chief series — the CFSG-free route to Wall's solvable
maximal-subgroup count. (The cardinality drop `|G ⧸ N| = [G : N] < |G|` is Lagrange:
`[G : N] · |N| = |G|` with `|N| > 1` since `N ≠ ⊥`.) The residual left open by iterating is the sum
of the complement counts of the abelian chief factors. -/
theorem exists_normal_card_isCoatom_le_of_isSolvable [Nontrivial G] [Group.IsSolvable G] :
    ∃ (N : Subgroup G) (_ : N.Normal), N ≠ ⊥ ∧ Nat.card (G ⧸ N) < Nat.card G ∧
      Nat.card {M : Subgroup G // IsCoatom M} ≤
        Nat.card {K : Subgroup (G ⧸ N) // IsCoatom K}
          + Nat.card {M : Subgroup G // N.IsComplement' M} := by
  obtain ⟨N, hNnorm, hNbot, hNab, hNmin⟩ :=
    exists_abelian_minimalNormal_of_isSolvable (G := G)
  have := hNnorm
  refine ⟨N, hNnorm, hNbot, ?_,
    card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement' N hNab hNmin⟩
  -- `|G ⧸ N| = [G : N] < |G|`, since `[G : N] · |N| = |G|` and `|N| > 1`.
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
  have hmul : N.index * Nat.card ↥N = Nat.card G := Subgroup.index_mul_card N
  have hidx : N.index = Nat.card (G ⧸ N) := rfl
  have h1 : 1 < Nat.card ↥N := Finite.one_lt_card
  have hpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  nlinarith [hmul, hidx, h1, hpos]

end AxQM.Concrete
