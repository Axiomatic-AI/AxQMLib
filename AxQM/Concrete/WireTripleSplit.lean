/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Concrete: splitting a register so three chosen wires lead (N&C Ex 4.44)

Its single statement involves only `Equiv`, `Fin`, `Sum` and `Set`, with no matrices.

## Motivation: the `a, b, j → e` construction

The general-wire naming of the Deutsch gate `G = C²(iR_x(πα))` (Nielsen & Chuang, Exercise 4.44)
names `G` placed on the *leading* three wires `e.symm (Sum.inl 0)`, `e.symm (Sum.inl 1)`,
`e.symm (Sum.inl 2)` of a wire-splitting `e : Fin M ≃ Fin 3 ⊕ Fin (M - 3)`
(`Postulates/API/DeutschGateWirePlacement.lean`). To name `G` placed on an *arbitrary* triple of
distinct control/target wires `a, b, j`, one needs a wire-splitting `e` whose three leading wires
are exactly `a, b, j`; that is the `a, b, j → e` construction.

This file supplies it. Given three distinct wires `a, b, j : Fin M`, the embedding
`![a, b, j] : Fin 3 ↪ Fin M` has a `3`-element range; splitting `Fin M` as that range plus its
`(M - 3)`-element complement (`Equiv.Set.sumCompl`) and identifying the range with `Fin 3`
(`Equiv.ofInjective`) and the complement with `Fin (M - 3)` yields an equivalence
`e : Fin M ≃ Fin 3 ⊕ Fin (M - 3)` whose inverse sends `Sum.inl 0, 1, 2` to `a, b, j`.
-/

namespace AxQM.Concrete

open Equiv

/-- **A wire-splitting with three chosen wires leading.** For three distinct wires
`a, b, j : Fin M`, there is an equivalence `e : Fin M ≃ Fin 3 ⊕ Fin (M - 3)` whose inverse sends the
three leading indices `Sum.inl 0, Sum.inl 1, Sum.inl 2` to `a, b, j` respectively. (The trailing
block `Fin (M - 3)` enumerates the remaining wires.)

Constructed from the injective `![a, b, j] : Fin 3 ↪ Fin M` (injectivity from the three
distinctness hypotheses): its range is identified with `Fin 3` by `Equiv.ofInjective` and its
`(M - 3)`-element complement with `Fin (M - 3)`, and `Equiv.Set.sumCompl` glues range and complement
back to `Fin M`. The three leading-index values are then read off by `Equiv.ofInjective_apply` /
`Equiv.Set.sumCompl_apply_inl`, each reducing to `![a, b, j]` evaluated at `0, 1, 2`.

This is the `a, b, j → e` step the general-wire naming of the Deutsch gate defers: instantiating the
leading-wire naming at this `e` names `deutschGate α` placed on the arbitrary distinct triple
`a, b, j`. -/
theorem exists_wireSplitEquiv_of_distinct {M : ℕ} (a b j : Fin M)
    (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j) :
    ∃ e : Fin M ≃ Fin 3 ⊕ Fin (M - 3),
      e.symm (Sum.inl 0) = a ∧ e.symm (Sum.inl 1) = b ∧ e.symm (Sum.inl 2) = j := by
  have hf : Function.Injective (![a, b, j] : Fin 3 → Fin M) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [Fin.ext_iff]
  set f : Fin 3 ↪ Fin M := ⟨![a, b, j], hf⟩ with hfdef
  set er : Fin 3 ≃ ↥(Set.range f) := Equiv.ofInjective f f.injective with herdef
  have hcard : Fintype.card (↥(Set.range f)ᶜ) = M - 3 := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective f.injective]
    simp
  refine ⟨((Equiv.sumCongr er (Fintype.equivFinOfCardEq hcard).symm).trans
      (Equiv.Set.sumCompl (Set.range f))).symm, ?_, ?_, ?_⟩
  all_goals
    simp only [Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.Set.sumCompl_apply_inl]
  all_goals rfl

end AxQM.Concrete
