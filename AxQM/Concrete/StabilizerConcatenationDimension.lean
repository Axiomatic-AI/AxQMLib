/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerConcatenation
import AxQM.Concrete.StabilizerConcatenationIndependence
import AxQM.Concrete.StabilizerCodeDimension

/-! # Concatenated stabilizer codes have parameters `[n₁n₂, 1]` (Nielsen & Chuang, Exercise 10.62)

The sibling files build, from an inner `[n₁, 1]` code `C₁ : StabCode1 g₁` (`n₁ = g₁ + 1`) and an
outer `[n₂, 1]` code `C₂ : StabCode1 g₂` (`n₂ = g₂ + 1`), the explicit concatenated generator family
`concatGen C₁ C₂ : ConcatIdx g₁ g₂ → (Fin (n₁n₂) → Fin 4)` on `n₁n₂ = (g₂+1)(g₁+1)` qubits, together
with the two facts that make it a stabilizer code:

* `concatIdx_card` — there are `Fintype.card (ConcatIdx g₁ g₂) = n₁n₂ − 1` generators;
* `concatGen_commute` — they pairwise **commute**;
* `concatGen_checkRow_linearIndependent` — their check rows are `𝔽₂`-**linearly independent**
  (N&C Proposition 10.3: independent generators).

This file supplies the last step of Exercise 10.62: the **`[n₁n₂, 1]` parameter conclusion**. The
`n₁n₂ − 1` generators are reindexed off the abstract index `ConcatIdx g₁ g₂` onto `Fin (n₁n₂ − 1)`
(the shape N&C's Proposition 10.5, `stabilizedSubspace_finrank`, consumes: `n − k` generators on
`n` qubits with `k = 1`), and Proposition 10.5 then gives that the stabilized subspace is
`2 = 2¹`-dimensional — precisely `k = 1` encoded qubit. Combined with the `n₁n₂`-qubit register and
the `n₁n₂ − 1` independent commuting generators, this is the `[n₁n₂, 1]` code.

The whole development is symplectic / check-matrix linear algebra over `𝔽₂` together with the honest
`finrank` statement of Proposition 10.5, over the types `Fin n → Fin 4`, `Matrix`, `Submodule`,
`Module.finrank`. The statement of Exercise 10.62 is in `AxQM/NC/Ch10/Exercise10_62.lean`.
-/

namespace AxQM.Concrete

variable {g₁ g₂ : ℕ}

/-- The bijection `ConcatIdx g₁ g₂ ≃ Fin (n₁n₂ − 1)` obtained from the generator count
`concatIdx_card` (`Fintype.card (ConcatIdx g₁ g₂) = (g₂+1)(g₁+1) − 1`). Noncomputable: it is a
choice-extracted enumeration of the index set. -/
noncomputable def concatIdxEquivFin : ConcatIdx g₁ g₂ ≃ Fin ((g₂ + 1) * (g₁ + 1) - 1) :=
  Fintype.equivFinOfCardEq concatIdx_card

/-- **The concatenated generators reindexed onto `Fin (n₁n₂ − 1)`.** This is `concatGen` composed
with the enumeration `concatIdxEquivFin`, so that the family has the `Fin (n − k)`-index shape
(`n = n₁n₂`, `k = 1`) that Proposition 10.5 (`stabilizedSubspace_finrank`) consumes. Reindexing by a
bijection preserves both commutation and check-row independence, so all the stabilizer-code
properties transport verbatim. -/
noncomputable def concatGenFin (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    Fin ((g₂ + 1) * (g₁ + 1) - 1) → (Fin ((g₂ + 1) * (g₁ + 1)) → Fin 4) :=
  fun j => concatGen C₁ C₂ (concatIdxEquivFin.symm j)

/-- The reindexed concatenated generators pairwise **commute** (transport of `concatGen_commute`
along the enumeration `concatIdxEquivFin`). -/
theorem concatGenFin_commute (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂)
    (i j : Fin ((g₂ + 1) * (g₁ + 1) - 1)) :
    Commute (pauliString (concatGenFin C₁ C₂ i)) (pauliString (concatGenFin C₁ C₂ j)) :=
  concatGen_commute C₁ C₂ _ _

/-- The reindexed concatenated generators have `𝔽₂`-**linearly independent check rows** (transport
of `concatGen_checkRow_linearIndependent`: precomposing a linearly independent family with the
injective `concatIdxEquivFin.symm` keeps it independent). -/
theorem concatGenFin_checkRow_linearIndependent (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    LinearIndependent (ZMod 2) (fun j => checkRow (concatGenFin C₁ C₂ j)) :=
  (concatGen_checkRow_linearIndependent C₁ C₂).comp _ concatIdxEquivFin.symm.injective

/-- **Nielsen & Chuang, Exercise 10.62.** Concatenating an inner `[n₁, 1]` stabilizer code
`C₁` (`n₁ = g₁ + 1`) with an outer `[n₂, 1]` code `C₂` (`n₂ = g₂ + 1`) yields an `[n₁n₂, 1]` code:
on the `n₁n₂ = (g₂+1)(g₁+1)`-qubit register, the `n₁n₂ − 1` commuting, `𝔽₂`-independent concatenated
generators (`concatGenFin`) stabilize a code space of dimension `2 = 2¹`, i.e. exactly `k = 1`
encoded qubit.

This is Proposition 10.5 (`stabilizedSubspace_finrank`, the `finrank = 2^k` dimension count for
`n − k` independent commuting generators) applied with `n = n₁n₂` and `k = 1`, fed the concatenated
generators' commutation (`concatGenFin_commute`) and independence
(`concatGenFin_checkRow_linearIndependent`). -/
theorem concat_stabilizedSubspace_finrank (C₁ : StabCode1 g₁) (C₂ : StabCode1 g₂) :
    Module.finrank ℂ (stabilizedSubspace (concatGenFin C₁ C₂)) = 2 := by
  simpa using stabilizedSubspace_finrank (n := (g₂ + 1) * (g₁ + 1)) (k := 1)
    (Nat.pos_of_ne_zero (by positivity)) (concatGenFin C₁ C₂) (concatGenFin_commute C₁ C₂)
    (concatGenFin_checkRow_linearIndependent C₁ C₂)

end AxQM.Concrete
