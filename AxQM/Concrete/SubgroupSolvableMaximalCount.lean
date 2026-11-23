/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupSolvableMinimalNormal

/-!
# The chief-series recursion, assembled: a linear maximal-subgroup bound for solvable groups

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Prob. 5.5 — Ettinger–Høyer–Knill piece
ii.)* The prior files built the **single descent step** of the CFSG-free chief-series recursion
(Wall's route to a maximal-subgroup count for solvable groups): for an abelian minimal normal
`N ◁ G`,

`#{maximal subgroups of G} ≤ #{maximal subgroups of G ⧸ N} + #{complements of N in G}`

(`card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement'`), and every nontrivial finite
solvable `G` has such an `N` with `|G ⧸ N| < |G|` and `G ⧸ N` again solvable
(`exists_abelian_minimalNormal_of_isSolvable`) — "the exact shape a strong induction on `|G|`
iterates". This file performs that **iteration**: a genuine strong induction on the group order
assembles the single step into a bound on the maximal count of the *whole* solvable class.

The result is conditional on the honest hard core — the **sharp per-chief-factor complement bound**
`#{complements of an abelian minimal normal N in H} ≤ |H|` (the cohomological Wall /
Aschbacher–Guralnick ingredient `|Z¹(H ⧸ N, N)| ≤ |H|`, whose elementary predecessor is the crude
`|N| ^ log₂|H ⧸ N|` of `SubgroupComplementCount.lean`) — and delivers

`#{maximal subgroups of a finite solvable G} ≤ 2 · |G|`

(`card_isCoatom_le_two_mul_card_of_isSolvable_of_complementBound`). This is **linear** in `|G|` —
Wall strength, up to the factor `2` — not the super-polynomial `|G| ^ log₂|G|` that the crude
per-step bound (or the type-independent `card_subgroup_le`) yields; the geometric decay of the
successive quotient orders (`|G_{i+1}| ≤ |G_i| / 2`) collapses the sum of per-factor complement
counts to `|G|(1 + ½ + ¼ + ⋯) < 2|G|`.

Its significance for Problem 5.5: the item's sole open general-`G` ingredient is the
Liebeck–Pyber–Shalev-strength count `#{maximals of J} ≤ |J|²/3` (CFSG). This file shows that **on
the solvable class that count is not a wall but a single isolated cohomological bound**: once the
per-chief-factor complement count is bounded by the group order, the whole solvable maximal count is
linear, hence far inside the quadratic gate (`6|G| ≤ |G|²` for `|G| ≥ 6`). It reduces the solvable
case of the residual to one clean statement about `H¹` — the CFSG-free route Wall's theorem realizes
unconditionally — and is the assembly on which extending the item's *unconditional* nilpotent-`G`
identification to *solvable* `G` would rest.
-/

open Subgroup QuotientGroup

namespace AxQM.Concrete

universe u

/-- **A linear bound on the number of maximal subgroups of a finite solvable group**, conditional on
the sharp per-chief-factor complement bound (Nielsen & Chuang, Problem 5.5 — Ettinger–Høyer–Knill
piece ii). If for every finite group `H` and every **abelian minimal normal** subgroup `N ◁ H` the
number of complements of `N` in `H` is at most `|H|` (the hypothesis `hcomp` — the cohomological
Wall / Aschbacher–Guralnick ingredient `|Z¹(H ⧸ N, N)| ≤ |H|`), then every finite solvable group `G`
has at most `2 · |G|` maximal subgroups.

The proof is the strong induction on `|G|` that the chief-series descent step
(`exists_abelian_minimalNormal_of_isSolvable` composed with
`card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement'`) was built to feed. A nontrivial
solvable `G` has an abelian minimal normal `N`; then

`#{maximals G} ≤ #{maximals G ⧸ N} + #{complements N} ≤ 2·|G ⧸ N| + |G| ≤ |G| + |G| = 2·|G|`,

using the induction hypothesis on the strictly smaller solvable quotient `G ⧸ N`, the complement
bound `hcomp`, and `2·|G ⧸ N| ≤ |G|` (from `|G| = |G ⧸ N|·|N|` with `|N| ≥ 2`). The trivial group
has no maximal subgroups. The bound is **linear** — the geometric decay of the quotient orders
telescopes the per-factor complement sum to `< 2|G|`; contrast the super-polynomial crude bound. -/
theorem card_isCoatom_le_two_mul_card_of_isSolvable_of_complementBound
    (hcomp : ∀ (H : Type u) [Group H] [Finite H] (N : Subgroup H), N.Normal →
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) →
      (∀ K : Subgroup H, K.Normal → K ≤ N → K = ⊥ ∨ K = N) →
      Nat.card {M : Subgroup H // N.IsComplement' M} ≤ Nat.card H) :
    ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card {M : Subgroup G // IsCoatom M} ≤ 2 * Nat.card G := by
  -- Strong induction on the order, packaged so the quotient (same universe, smaller order) can
  -- invoke the induction hypothesis.
  have key : ∀ n : ℕ, ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card G = n → Nat.card {M : Subgroup G // IsCoatom M} ≤ 2 * Nat.card G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro G _ _ _ hn
      rcases subsingleton_or_nontrivial G with hss | hnt
      · -- Trivial group: every subgroup is `⊤`, so there are no coatoms.
        have : IsEmpty {M : Subgroup G // IsCoatom M} :=
          ⟨fun M => M.2.1 (Subsingleton.elim _ _)⟩
        rw [Nat.card_of_isEmpty]
        exact Nat.zero_le _
      · -- Nontrivial solvable `G`: descend along an abelian minimal normal subgroup.
        obtain ⟨N, hNnorm, hNbot, hNab, hNmin⟩ :=
          exists_abelian_minimalNormal_of_isSolvable (G := G)
        have := hNnorm
        have : Group.IsSolvable (G ⧸ N) := inferInstance
        have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
        have h2N : 2 ≤ Nat.card ↥N := Finite.one_lt_card
        have hqpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
        have hlag : Nat.card G = Nat.card (G ⧸ N) * Nat.card ↥N :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup N
        -- The quotient is strictly smaller, so the induction hypothesis applies.
        have hqlt : Nat.card (G ⧸ N) < n := by
          rw [← hn, hlag]; nlinarith [hqpos, h2N]
        have hih := IH (Nat.card (G ⧸ N)) hqlt (G ⧸ N) rfl
        have hrec :=
          card_isCoatom_le_card_isCoatom_quotient_add_card_isComplement' N hNab hNmin
        have hcp := hcomp G N hNnorm hNab hNmin
        -- `2·|G ⧸ N| ≤ |G|` since `|G| = |G ⧸ N|·|N|` with `|N| ≥ 2`.
        have hquot : 2 * Nat.card (G ⧸ N) ≤ Nat.card G := by rw [hlag]; nlinarith [hqpos, h2N]
        -- Combine: `#{maximals G} ≤ #{maximals G ⧸ N} + #{complements N} ≤ 2|G ⧸ N| + |G| ≤ 2|G|`.
        calc Nat.card {M : Subgroup G // IsCoatom M}
            ≤ Nat.card {K : Subgroup (G ⧸ N) // IsCoatom K}
                + Nat.card {M : Subgroup G // N.IsComplement' M} := hrec
          _ ≤ 2 * Nat.card (G ⧸ N) + Nat.card G := Nat.add_le_add hih hcp
          _ ≤ 2 * Nat.card G := by omega
  intro G _ _ _
  exact key (Nat.card G) G rfl

end AxQM.Concrete
