/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SubgroupPrimeIndexNormalCount
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Concrete: how many homomorphisms a finite group has into a finite cyclic group

*(Supporting `AxQM/NC/Ch5/Problem5_5.lean`, N&C Prob. 5.5 — Ettinger–Høyer–Knill piece
ii.)*

The chief-series recursion of `Concrete/SubgroupComplementOrbitCount.lean` pins the solvable
maximal-subgroup count on the per-chief-factor complement bound
`#{complements of an abelian minimal normal `N` in `H`} ≤ |H|`, whose remaining strictly
cohomological factor is the number of `N`-conjugacy classes of complements
`|H¹(H ⧸ N, N)| ≤ |H : N|`. In the **trivial-action (central) case** — `N ≤ Z(H)`, so `H ⧸ N`
acts trivially on `N` — the first cohomology collapses to the plain hom count
`H¹(H ⧸ N, N) = Hom(H ⧸ N, N)` (coboundaries vanish, cocycles are homomorphisms). This file proves
the ingredient that then closes that case **sharply when `N` is cyclic**:

`card_monoidHom_le_card_of_isCyclic` — for a finite group `G` and a finite **cyclic** group `C`,
`Nat.card (G →* C) ≤ Nat.card G`.

Applied with `G = H ⧸ N` and `C = N` (a cyclic minimal normal subgroup, i.e. of prime order) this
gives `|Hom(H ⧸ N, N)| ≤ |H : N|`, exactly the cohomological factor's target in the central cyclic
case.

The bound is a genuine sharpening of the two counts already in `Concrete/` for cyclic targets:

* `card_monoidHom_le_pow_log` (`Concrete/SubgroupFixedQuotientCount.lean`) gives only
  `|C|^{log₂|G|}` — exponential in `log|G|`, hence super-linear in `|G|`;
* `card_monoidHom_complexUnits_le` (`Concrete/SubgroupPrimeIndexNormalCount.lean`) is the special
  case `C = ℂˣ` (which is not finite cyclic).

The proof reduces the cyclic target to that complex-character count: a finite cyclic group carries a
**faithful** character `C ↪ ℂˣ` (`exists_injective_monoidHom_complexUnits_of_isCyclic`, built from
`ZMod.toCircle` on `C ≃* Multiplicative (ZMod |C|)` composed with `Circle ↪ ℂˣ`), post-composition
with which injects `(G →* C) ↪ (G →* ℂˣ)`, and the latter has at most `|G|` elements
(`card_monoidHom_complexUnits_le`).
-/

namespace AxQM.Concrete

variable {G : Type*} [Group G]

/-- **A finite cyclic group has a faithful complex character.** The composite
`C ≃* Multiplicative (ZMod |C|) → Circle ↪ ℂˣ` — the multiplicative isomorphism
`zmodCyclicMulEquiv`, the additive character `ZMod.toCircle` (injective), and the inclusion
`Circle.toUnits` (injective) — is an injective monoid homomorphism `C →* ℂˣ`. -/
theorem exists_injective_monoidHom_complexUnits_of_isCyclic
    {C : Type*} [Group C] [Finite C] [IsCyclic C] :
    ∃ f : C →* ℂˣ, Function.Injective f := by
  have : NeZero (Nat.card C) := ⟨Nat.card_pos.ne'⟩
  let e : Multiplicative (ZMod (Nat.card C)) ≃* C := zmodCyclicMulEquiv (inferInstance)
  let χ : Multiplicative (ZMod (Nat.card C)) →* Circle :=
    (ZMod.toCircle (N := Nat.card C)).toMonoidHom
  refine ⟨(Circle.toUnits.comp χ).comp (e.symm : C →* _), ?_⟩
  have hχ : Function.Injective χ := ZMod.injective_toCircle
  have htu : Function.Injective (Circle.toUnits) := by
    intro a b h; apply Circle.coe_injective; simpa using congrArg (Units.val) h
  exact (htu.comp hχ).comp e.symm.injective

/-- **The number of homomorphisms from a finite group into a finite cyclic group is at most the
order of the group.** For finite `G` and finite cyclic `C`, `Nat.card (G →* C) ≤ Nat.card G`. A
faithful character `C ↪ ℂˣ` (`exists_injective_monoidHom_complexUnits_of_isCyclic`) injects
`(G →* C) ↪ (G →* ℂˣ)` by post-composition, and the complex-character count bounds the target by
`|G|` (`card_monoidHom_complexUnits_le`). This sharpens `card_monoidHom_le_pow_log` (which gives
only `|C|^{log₂|G|}`) to a linear bound whenever the target is cyclic. -/
theorem card_monoidHom_le_card_of_isCyclic [Finite G]
    {C : Type*} [Group C] [Finite C] [IsCyclic C] :
    Nat.card (G →* C) ≤ Nat.card G := by
  obtain ⟨j, hj⟩ := exists_injective_monoidHom_complexUnits_of_isCyclic (C := C)
  refine (Nat.card_le_card_of_injective (fun g : G →* C => j.comp g) ?_).trans
    card_monoidHom_complexUnits_le
  exact fun g₁ g₂ h => MonoidHom.ext fun a => hj (DFunLike.congr_fun h a)

end AxQM.Concrete
