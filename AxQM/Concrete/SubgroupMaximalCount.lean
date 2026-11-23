/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupNonNormalMaximalConjugacy

/-!
# The item's residual as the standard maximal-subgroup count (Ettinger–Høyer–Knill piece ii)

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Problem 5.5.)* The whole ~ten-file
maximal-subgroup development for the Ettinger–Høyer–Knill collision tail isolates the sole remaining
general-`G` counting ingredient as the **conjugacy-class** count
`3 · #{J-conjugacy classes of non-normal maximal subgroups of J} ≤ |J|²`
(`SubgroupNonNormalMaximalConjugacy.lean`, the sharpest elementary form). That hypothesis is stated
over the orbit quotient of the `J`-conjugation action, which — while the natural quantity the
collision sum sees — is a bespoke shape. This file certifies, in one line of counting, that it is
**no stronger than the standard bound on the number of maximal subgroups**:

`#{maximal subgroups of J} ≤ |J|²/3   ⟹   3 · #{J-conjugacy classes of non-normal maximals} ≤ |J|²`

(`nonnormal_maximal_classCard_le_of_card_maximal_le`), because the conjugacy classes inject into the
non-normal maximals, which are a subset of *all* maximals (coatoms `M ⋖ J`):

`#{classes} ≤ #{non-normal maximals} ≤ #{maximals}`.

So the item's entire residual counting hypothesis is implied by a *recognizable, named* group-theory
statement — a weak form of the **Liebeck–Pyber–Shalev** bound `#{maximals of G} ≤ c·|G|^{3/2}` (the
sharp count uses the Classification of Finite Simple Groups; the quadratic slack here is far
weaker, but still has no elementary polynomial proof — the elementary subgroup-growth bounds are
super-polynomial (M. Hall `(n!)^{log|G|}`)). This makes precise, and machine-checkable, that Problem
5.5's sole open ingredient is not a contrived hypothesis rigged to the proof but exactly the
standard question *"are there polynomially many maximal subgroups?"*.

The **sharper** form (dropping the factor `3`, i.e. deriving the class count from
`#{maximals} ≤ |J|²` rather than `≤ |J|²/3`) additionally uses that a non-normal maximal's conjugacy
class is a full orbit of size its index `≥ 3` (self-normalization,
`ncard_kConj_orbit_eq_relIndex_of_covBy_of_not_normal`), so
`#{non-normal maximals} = ∑_class [J:M] ≥ 3 · #{classes}`; that refinement is recorded in the
docstring of `SubgroupNonNormalMaximalConjugacy.lean` and not needed here, where the transparent
`#{classes} ≤ #{non-normal maximals} ≤ #{maximals}` already ties the residual to the standard count.
-/

namespace AxQM.Concrete

open Finset

variable {G : Type*} [Group G]

open Classical in
/-- **The item's residual class-count hypothesis follows from the standard maximal-subgroup count.**
For a group `G` with a finite subgroup lattice `Fintype (Subgroup G)` and a subgroup `J`, if the
number of maximal subgroups of `J` (coatoms `M ⋖ J`) is at most `|J|²/3`, then
`3 · #{J-conjugacy classes of non-normal maximal subgroups of J} ≤ |J|²` — the exact hypothesis the
Ettinger–Høyer–Knill collision tail (`sum_cosetAffinity_pow_collision_classCard_le_of_sq`, and
hence the general-`G` identification headlines of `Problem5_5.lean`) consumes.

The proof is the transparent counting chain: the `J`-conjugacy classes are the image of the
non-normal maximals under the orbit-quotient map, so their count is at most the number of non-normal
maximals (`Finset.card_image_le`), which is at most the number of *all* maximals (the non-normal
ones are a subset, `Finset.card_le_card`), which is `#{M // M ⋖ J}` (`Fintype.card_subtype`). This
pins
the item's sole remaining general-`G` ingredient to the standard, recognizable — and still
Liebeck–Pyber–Shalev-strength — question of whether a finite group has polynomially many maximal
subgroups. -/
theorem nonnormal_maximal_classCard_le_of_card_maximal_le [Fintype (Subgroup G)]
    (J : Subgroup G)
    (h : 3 * Nat.card {M : Subgroup G // M ⋖ J} ≤ Nat.card ↥J ^ 2) :
    3 * ((Finset.univ.filter (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
        (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
      ≤ Nat.card ↥J ^ 2 :=
  le_trans (Nat.mul_le_mul_left 3 <|
    calc ((Finset.univ.filter (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).image
            (fun M => Quotient.mk (MulAction.orbitRel ↥J (Subgroup G)) M)).card
        ≤ (Finset.univ.filter (fun M : Subgroup G => M ⋖ J ∧ ¬ (M.subgroupOf J).Normal)).card :=
          Finset.card_image_le
      _ ≤ (Finset.univ.filter (fun M : Subgroup G => M ⋖ J)).card :=
          Finset.card_le_card (fun M hM => by
            rw [Finset.mem_filter] at hM ⊢; exact ⟨hM.1, hM.2.1⟩)
      _ = Nat.card {M : Subgroup G // M ⋖ J} := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]) h

end AxQM.Concrete
