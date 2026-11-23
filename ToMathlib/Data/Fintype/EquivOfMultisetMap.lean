/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic

/-!
# An index bijection from equal image multisets

For finitely-indexed families `f : ι → α` and `g : κ → α` over (possibly different) finite index
types, `exists_equiv_of_map_univ_val_eq` produces a *value-preserving* bijection `e : ι ≃ κ` — one
with `g (e i) = f i` for every `i` — from the single hypothesis that the two image multisets agree,
`Multiset.map f univ.val = Multiset.map g univ.val`.

This is a general `Fintype`/`Multiset`/`Equiv` fact with no dependence on order, convexity, or
analysis. It is the rigidity tool shared by majorization-up-to-reindexing
(`ToMathlib/Analysis/Convex/Majorization.lean`, `majorize_congr_multiset`) and the `≅`-relation on
vectors (`ToMathlib/Analysis/Convex/SameNonzero.lean`, `SameNonzero.exists_equiv`): identical
multisets of values pin down a permutation of the indices.

## Main statements

* `exists_equiv_of_map_univ_val_eq`: equal image multisets give a value-preserving index bijection.
-/

public section

variable {α ι κ : Type*}

/-- The number of indices a finitely-indexed family `F : β → α` sends to a fixed value `c` is the
multiplicity of `c` in the family's image multiset: `#{i // F i = c} = count c (map F univ.val)`
(`Fintype.card_subtype` re-presents the fiber as `univ.filter`; `Multiset.count_map` re-presents the
count as the same filter, up to `eq_comm` in the predicate). The fiber-counting step of
`exists_equiv_of_map_univ_val_eq`, factored out so the `f`- and `g`-side counts share one proof:
they sit in different index universes, so a single in-proof `have` cannot serve both. -/
private theorem card_fiber_eq_count {β α : Type*} [Fintype β] [DecidableEq α] (F : β → α) (c : α) :
    Fintype.card {i // F i = c} = Multiset.count c (Multiset.map F Finset.univ.val) := by
  rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
  exact congrArg Multiset.card (Multiset.filter_congr fun x _ => eq_comm)

/-- **Equal full multisets give a value-preserving index bijection.** If two finitely-indexed
families `f : ι → α` and `g : κ → α` have equal image multisets over their whole index types
(`Multiset.map f univ.val = Multiset.map g univ.val`), then there is a bijection `e : ι ≃ κ`
matching the values entry-by-entry, `g (e i) = f i`. Identical multisets of values (not just
identical non-zero parts) pin down a permutation of the indices.

Proof: for each value `c`, the two fibers `{i // f i = c}` and `{j // g j = c}` have equal
cardinality — each is the multiplicity of `c` in the respective image multiset
(`card_fiber_eq_count`), and those multiplicities agree by hypothesis. `Equiv.ofFiberEquiv` glues
the fiber-wise cardinality bijections (`Fintype.equivOfCardEq`) into `e : ι ≃ κ`; value preservation
is the defining property of the target fiber. -/
theorem exists_equiv_of_map_univ_val_eq [Fintype ι] [Fintype κ] {f : ι → α} {g : κ → α}
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ e : ι ≃ κ, ∀ i, g (e i) = f i := by
  classical
  have hcard : ∀ c : α, Fintype.card {i // f i = c} = Fintype.card {j // g j = c} := fun c => by
    rw [card_fiber_eq_count f c, card_fiber_eq_count g c, h]
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcard c)), fun i => ?_⟩
  rw [Equiv.ofFiberEquiv_apply]
  exact ((Fintype.equivOfCardEq (hcard (f i))) _).2
