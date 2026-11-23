/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.GroupTheory.Nilpotent

/-!
# Maximal subgroups of nilpotent groups are normal (Ettinger–Høyer–Knill piece ii, nilpotent case)

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Problem 5.5.)* The Ettinger–Høyer–Knill
collision-sum tail (piece ii) of Problem 5.5 was reduced, through the ~ten-file maximal-subgroup
development culminating in `AxQM/Concrete/CosetCollisionSumClassCard.lean`, to a **single**
Liebeck–Pyber–Shalev-strength group-theoretic hypothesis:
`∀ J, 3 · #{J-conjugacy classes of non-normal maximal subgroups} ≤ |J|²`. That count is
Gaussian-binomial-strength for a *general* finite group (its worst case realises `|H¹(H, V)|`
complement classes of affine primitive quotients `V ⋊ H`), and is the genuine deep-group-theory
residual of the item.

For a **nilpotent** group it is, however, **trivial**: a nilpotent group — and every subgroup of
one — has *no* non-normal maximal subgroups at all, so the filtered set is empty and the count is
`0`. This file records the two structural facts behind that observation, as general
finite-group theory:

* `isCoatom_subgroupOf_of_covBy`: a subgroup `M` **maximal in `J`** (`M ⋖ J`, covered by `J` in the
  subgroup lattice of `G`) corresponds to a **coatom** `M.subgroupOf J` of the subgroup lattice of
  `↥J`. This is the order correspondence between subgroups of `↥J` and subgroups of `G` lying in the
  interval `[⊥, J]`: `subgroupOf J = comap J.subtype` is a strictly monotone bijection onto that
  interval carrying `J` to `⊤`, so it sends the cover `M ⋖ J` to the cover `M.subgroupOf J ⋖ ⊤`,
  i.e. a coatom.
* `normal_subgroupOf_of_covBy_of_isNilpotent`: in a nilpotent group `G`, every maximal subgroup
  `M ⋖ J` of any subgroup `J` is **normal** in `J`. Indeed `↥J` is again nilpotent (nilpotency
  passes to subgroups), hence satisfies the **normalizer condition**
  (`normalizerCondition_of_isNilpotent`), under which every coatom is normal
  (`Subgroup.NormalizerCondition.normal_of_coatom`).

Consequently the non-normal maximal filter of Problem 5.5's `classCard` hypothesis is empty for
nilpotent `G`, discharging piece (ii) **unconditionally** for the entire class of nilpotent groups
(all abelian groups, all `p`-groups, and their direct products). This is used in
`cosetDensityState_pi_prettyGoodMeasurement_bornProb_ge_of_paired_of_nilpotent`, whose only
remaining hypothesis is then the piece-(i)(a) paired-trace operator inequality.
-/

namespace AxQM.Concrete

open Subgroup

variable {G : Type*} [Group G]

/-- **A subgroup maximal in `J` is a coatom of `↥J`.** If `M ⋖ J` (i.e. `M` is covered by `J` in the
subgroup lattice of `G` — `M` is maximal among subgroups strictly below `J`), then its image
`M.subgroupOf J = comap J.subtype M` is a **coatom** in the subgroup lattice of `↥J`.

This is the order correspondence between subgroups of `↥J` and the interval `[⊥, J]` of subgroups of
`G`: `subgroupOf J` is a strictly monotone bijection onto that interval sending `J` to `⊤`, so it
carries the cover `M ⋖ J` to the cover `M.subgroupOf J ⋖ ⊤`, i.e. a coatom. Concretely: it is proper
(`M.subgroupOf J = ⊤ ↔ J ≤ M`, excluded by `M < J`), and any `Y` with `M.subgroupOf J < Y` maps up
to a subgroup `M < Y.map J.subtype ≤ J`, which `M ⋖ J` forces to equal `J`, i.e. `Y = ⊤`. -/
theorem isCoatom_subgroupOf_of_covBy {M J : Subgroup G} (h : M ⋖ J) :
    IsCoatom (M.subgroupOf J) := by
  constructor
  · rw [Ne, Subgroup.subgroupOf_eq_top]
    exact h.1.not_ge
  · intro Y hY
    have hMJ : M ≤ J := le_of_lt h.1
    -- `Y` maps up to `Y.map J.subtype`, a subgroup strictly above `M` and below `J`.
    have hstrict : M < Y.map J.subtype := by
      have hlt := Subgroup.map_subtype_lt_map_subtype.mpr hY
      rwa [Subgroup.map_subgroupOf_eq_of_le hMJ] at hlt
    have hle : Y.map J.subtype ≤ J := Subgroup.map_subtype_le Y
    -- `M ⋖ J` leaves nothing strictly between `M` and `J`, so `Y.map J.subtype = J`.
    have hYJ : Y.map J.subtype = J := eq_of_le_of_not_lt hle (h.2 hstrict)
    -- Pull back along the injective `subtype`: `Y = (Y.map J.subtype).subgroupOf J = ⊤`.
    have hself : (Y.map J.subtype).subgroupOf J = Y := by
      rw [Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective J)]
    rw [← hself, hYJ, Subgroup.subgroupOf_self]

/-- **In a nilpotent group, every maximal subgroup of every subgroup is normal.** For a nilpotent
group `G`, a subgroup `J`, and `M ⋖ J` (maximal in `J`), the relative subgroup `M.subgroupOf J` is
normal in `↥J`.

The subgroup `↥J` inherits nilpotency, hence satisfies the normalizer condition
(`normalizerCondition_of_isNilpotent`), under which the coatom `M.subgroupOf J`
(`isCoatom_subgroupOf_of_covBy`) is normal (`Subgroup.NormalizerCondition.normal_of_coatom`). Since
this holds for *every* subgroup `J`, the set of non-normal maximal subgroups of any `J ≤ G` is empty
for nilpotent `G` — the trivial case of Problem 5.5's class-count hypothesis. -/
theorem normal_subgroupOf_of_covBy_of_isNilpotent [Group.IsNilpotent G] {M J : Subgroup G}
    (h : M ⋖ J) : (M.subgroupOf J).Normal :=
  Subgroup.NormalizerCondition.normal_of_coatom _ Group.normalizerCondition_of_isNilpotent
    (isCoatom_subgroupOf_of_covBy h)

end AxQM.Concrete
