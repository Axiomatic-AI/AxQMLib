/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import AxQM.Concrete.SubgroupIndexCount

/-!
# Concrete: how many normal subgroups with a *fixed* quotient a finite group has

This file supplies a **fixed-quotient normal-subgroup count** for the residual of the
maximal-subgroup low-index sum `∑_{M ⋖ K} (|M|/|K|)^s` behind the Ettinger–Høyer–Knill
identification bound of Nielsen & Chuang, Problem 5.5 (the non-Abelian hidden subgroup problem).

## The context

`Concrete/SubgroupMaximalSum.lean` reduced the Ettinger–Høyer–Knill collision tail to the
**maximal-subgroup low-index sum** `∑_{M ⋖ K} (|M|/|K|)^s = ∑_{M ⋖ K} [K:M]^{-s}`. A maximal
subgroup `M ⋖ K` normal in `K` has *simple* quotient `K/M`; when that quotient is **abelian** it is
cyclic of prime order, and `Concrete/SubgroupPrimeIndexNormalCount.lean` discharged that part by
injecting the prime-index normal subgroups into the **complex characters** `G →* ℂˣ` — a *single*
target group into which every abelian quotient embeds (`card_monoidHom_complexUnits_le ≤ |G|`). That
single-target trick has **no analogue for nonabelian simple quotients**: a nonabelian simple group
is perfect, so it has no nontrivial characters, and there is no one finite group receiving all
nonabelian simple quotients. The residual — the normal maximals with a nonabelian simple quotient
`Q` (necessarily of index `|Q| ≥ 60`) — must instead be counted **one quotient type `Q` at a time**,
which is what this file provides.

Throughout, "`N` has quotient `Q`" is phrased instance-free as "`N` is the kernel of a *surjective*
homomorphism `G →* Q`": by the first isomorphism theorem this holds iff `G ⧸ N ≃* Q` (and it forces
`N` to be normal, being a kernel).

## What is proved

* `card_monoidHom_le_pow_log` — for finite groups `G, Q`, the number of monoid homomorphisms
  `G →* Q` is at most `|Q|^{log₂|G|}`. A homomorphism is determined by its values on a generating
  set, and a finite group has a generating finset of size `≤ log₂|G|`
  (`exists_closure_finset_card_le_log`); restricting to that finset injects `G →* Q` into the
  functions from a set of size `≤ log₂|G|` to `Q`. This is the general (nonabelian-codomain)
  analogue of the character count `card_monoidHom_complexUnits_le` (there `Q = ℂˣ`, and abelianizing
  gives the sharper `≤ |G|`).
* `card_kernel_surjective_hom_le` — for a **fixed** finite group `Q`, the number of subgroups
  `N ≤ G` arising as the kernel of some surjective homomorphism `G →* Q` (i.e. with `G ⧸ N ≃* Q`) is
  at most `|Q|^{log₂|G|}`. Each such `N` is the kernel of a chosen surjection, and distinct `N` are
  distinct kernels, so these subgroups inject into `G →* Q`, counted by the previous lemma. This is
  the nonabelian generalization of `card_prime_index_normal_le`.
* `card_relIndex_kernel_surjective_hom_le` — the **relative** form: for subgroups of `K`, the number
  of `M ≤ K` such that `M.subgroupOf K` is the kernel of a surjective homomorphism `↥K →* Q` (i.e.
  `↥K ⧸ (M.subgroupOf K) ≃* Q`) is at most `|Q|^{log₂|K|}`. These are exactly the quotient-`Q`
  kernels in `↥K` (`Subgroup.subgroupOf`, injective on subgroups `≤ K`), so the previous count
  applied to `↥K` bounds them. Applied at a nonabelian simple `Q`, this counts (per type `Q`) the
  nonabelian-simple normal maximals of `K` — the tool the residual maximal-subgroup sum needs.
  Aggregating over the quotient types `Q` (bounding the number of distinct nonabelian simple
  quotient types of `K` by its composition length `≤ log₂|K|`) is the remaining step, tracked
  separately.
-/

namespace AxQM.Concrete

variable {G : Type*} [Group G]

/-- **The number of homomorphisms into a fixed finite group is at most `|Q|^{log₂|G|}`.** A monoid
homomorphism `G →* Q` is determined by its values on a generating set of `G`, and a finite group has
a generating finset `s` of cardinality `≤ log₂|G|` (`exists_closure_finset_card_le_log`).
Restricting a homomorphism to `s` therefore injects `G →* Q` into the functions `↥s → Q`, of which
there are
`|Q|^{|s|} ≤ |Q|^{log₂|G|}`. This is the general-codomain analogue of the complex-character count
`card_monoidHom_complexUnits_le`; unlike that count it makes no use of commutativity, so it applies
to nonabelian target groups `Q`. -/
theorem card_monoidHom_le_pow_log [Finite G] {Q : Type*} [Group Q] [Finite Q] :
    Nat.card (G →* Q) ≤ Nat.card Q ^ Nat.log 2 (Nat.card G) := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_closure_finset_card_le_log (⊤ : Subgroup G)
  -- A homomorphism is determined by its restriction to the generating finset `s`.
  have hinj : Function.Injective (fun f : G →* Q => fun x : ↥s => f (x : G)) := by
    intro f g hfg
    apply MonoidHom.ext
    have hEq : Set.EqOn (⇑f) (⇑g) (↑s : Set G) := fun x hx => congrFun hfg ⟨x, hx⟩
    have h2 := MonoidHom.eqOn_closure hEq
    rw [hs] at h2
    intro x; exact h2 (by trivial)
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  calc Nat.card (G →* Q) ≤ Nat.card (↥s → Q) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card Q ^ s.card := by rw [Nat.card_fun, Nat.card_eq_finsetCard]
    _ ≤ Nat.card Q ^ Nat.log 2 (Nat.card G) := Nat.pow_le_pow_right hQpos hcard

/-- Homomorphisms between finite groups form a finite type (they inject into the finite function
type `G → Q`). -/
instance instFiniteMonoidHom {Q : Type*} [Finite G] [Group Q] [Finite Q] : Finite (G →* Q) :=
  Finite.of_injective (β := G → Q) (⇑·) DFunLike.coe_injective

/-- **The number of subgroups with a fixed quotient `Q` is at most `|Q|^{log₂|G|}`.** For a finite
group `Q`, each subgroup `N ≤ G` arising as the kernel of a surjective homomorphism `G →* Q` (i.e.
with `G ⧸ N ≃* Q`, by the first isomorphism theorem) is recovered as *that* homomorphism's kernel,
so distinct such `N` come from distinct homomorphisms. These subgroups therefore inject into
`G →* Q`,
whose cardinality is `≤ |Q|^{log₂|G|}` (`card_monoidHom_le_pow_log`). This is the nonabelian
generalization of `card_prime_index_normal_le`: where the prime-index (cyclic-quotient) case injects
*all* such subgroups into the single character group `G →* ℂˣ`, here a *fixed* nonabelian target `Q`
is used one type at a time. -/
theorem card_kernel_surjective_hom_le [Finite G] (Q : Type*) [Group Q] [Finite Q] :
    Nat.card {N : Subgroup G // ∃ χ : G →* Q, Function.Surjective χ ∧ χ.ker = N}
      ≤ Nat.card Q ^ Nat.log 2 (Nat.card G) := by
  classical
  -- Choose, for each such `N`, a surjection with kernel `N`.
  choose f hf using
    fun p : {N : Subgroup G // ∃ χ : G →* Q, Function.Surjective χ ∧ χ.ker = N} => p.2
  have hinj : Function.Injective f := fun p q hpq =>
    Subtype.ext (by rw [← (hf p).2, ← (hf q).2, hpq])
  exact (Nat.card_le_card_of_injective f hinj).trans card_monoidHom_le_pow_log

/-- **The relative form: kernels in `K` with a fixed quotient `Q` number at most `|Q|^{log₂|K|}`.**
The subgroups `M ≤ K` such that `M.subgroupOf K` is the kernel of a surjective homomorphism
`↥K →* Q` (i.e. `↥K ⧸ (M.subgroupOf K) ≃* Q`) are exactly the quotient-`Q` kernels of `↥K`
(`Subgroup.subgroupOf`, injective on subgroups `≤ K` via `Subgroup.map_subgroupOf_eq_of_le`), so
`card_kernel_surjective_hom_le` applied to `↥K` bounds them by `|Q|^{log₂|K|}`. Applied at a
nonabelian simple `Q`, this counts the nonabelian-simple normal maximals of `K` with quotient type
`Q` — the per-type ingredient of the residual maximal-subgroup low-index sum. It is the general-`Q`
analogue of `card_relIndex_prime_normal_le`. -/
theorem card_relIndex_kernel_surjective_hom_le [Finite G] (K : Subgroup G) (Q : Type*) [Group Q]
    [Finite Q] :
    Nat.card {M : Subgroup G // M ≤ K ∧
        ∃ χ : ↥K →* Q, Function.Surjective χ ∧ χ.ker = M.subgroupOf K}
      ≤ Nat.card Q ^ Nat.log 2 (Nat.card ↥K) := by
  have : Finite (Subgroup ↥K) := Finite.of_injective _ SetLike.coe_injective
  have hinj : Function.Injective
      (fun p : {M : Subgroup G // M ≤ K ∧
          ∃ χ : ↥K →* Q, Function.Surjective χ ∧ χ.ker = M.subgroupOf K} =>
        (⟨p.1.subgroupOf K, p.2.2⟩ :
          {N : Subgroup ↥K // ∃ χ : ↥K →* Q, Function.Surjective χ ∧ χ.ker = N})) := by
    rintro ⟨M1, hle1, _⟩ ⟨M2, hle2, _⟩ heq
    simp only [Subtype.mk.injEq] at heq
    have : M1 = M2 := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hle1, ← Subgroup.map_subgroupOf_eq_of_le hle2, heq]
    simp [this]
  calc Nat.card {M : Subgroup G // M ≤ K ∧
          ∃ χ : ↥K →* Q, Function.Surjective χ ∧ χ.ker = M.subgroupOf K}
      ≤ Nat.card {N : Subgroup ↥K // ∃ χ : ↥K →* Q, Function.Surjective χ ∧ χ.ker = N} :=
        Nat.card_le_card_of_injective _ hinj
    _ ≤ Nat.card Q ^ Nat.log 2 (Nat.card ↥K) := card_kernel_surjective_hom_le Q

end AxQM.Concrete
