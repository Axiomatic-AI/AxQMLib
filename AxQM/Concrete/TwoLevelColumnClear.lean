/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelEmbedding
import AxQM.Concrete.GivensRotation

/-!
# Concrete: clearing a column with two-level unitaries (N&C §4.5.1, eqs. 4.44–4.50)

The two-level decomposition of an arbitrary `d × d` unitary (Nielsen & Chuang §4.5.1, p. 189)
proceeds by repeatedly *clearing a column*: given a unitary `U`, one multiplies it on the left by a
sequence `U₁, U₂, …` of two-level unitaries so that the product's first column becomes a multiple of
`e₀` (all entries below the top are zeroed — eqs. (4.44)–(4.50)). Each `Uₖ` is the Givens rotation
`givensRotation` (`Concrete/GivensRotation.lean`) embedded into the coordinate pair `{0, q}`
(`twoLevelEmbed`, `Concrete/TwoLevelEmbedding.lean`), which zeroes one below-diagonal entry while
leaving the already-cleared entries fixed.

This file provides that step as reusable `Concrete/` lemmas, phrased first for a **vector** and then
for the **first column of a matrix**:

* `exists_twoLevelUnitaryList_mulVec_eq_zero_of_ne` — for every `v : Fin (d+1) → ℂ` there is a list
  `L` of two-level unitaries whose product sends `v` to a vector supported on coordinate `0`
  (`(L.prod *ᵥ v) j = 0` for every `j ≠ 0`).
* `exists_twoLevelUnitaryList_clear_first_column` — the same, applied to the first column of a
  matrix `U`: `(L.prod * U) i 0 = 0` for every `i ≠ 0`. This is the form the block-diagonal peel of
  the §4.5.1 induction (`Concrete/TwoLevelDecomposition.lean`) consumes.

The value that accumulates in coordinate `0` is deliberately left unspecified: the induction that
uses this step recovers it (it is a unit modulus when `v` is a column of a unitary) from the
unitarity of `L.prod * U`, so pinning it here would only add noise.

## Use

This is a shared building block for the §4.5.1 development (Exercise 4.43's `n`-qubit lift, also
used by Ex 4.37/4.38/4.39); the statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **Clearing a chosen set of coordinates into coordinate `0`.** For a finite set `S` of
coordinates not containing `0`, there is a list `L` of two-level unitaries — each a Givens rotation
embedded in a pair `{0, q}` with `q ∈ S` — whose product zeroes every coordinate in `S` while
leaving every coordinate outside `S ∪ {0}` unchanged (coordinate `0` accumulates the cleared mass
and is left unconstrained). Proved by induction on `S`: each step adds one Givens factor on `{0, q}`
that zeroes `q` without disturbing the coordinates already handled. -/
theorem exists_twoLevelUnitaryList_clear_finset (S : Finset (Fin (d + 1)))
    (hS : (0 : Fin (d + 1)) ∉ S) (v : Fin (d + 1) → ℂ) :
    ∃ L : List (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ),
      (∀ M ∈ L, IsTwoLevelUnitary M) ∧
        (∀ j ∈ S, (L.prod *ᵥ v) j = 0) ∧
        (∀ j, j ≠ 0 → j ∉ S → (L.prod *ᵥ v) j = v j) := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨[], by simp, by simp, fun j _ _ => by simp [Matrix.one_mulVec]⟩
  | @insert q S' hqS' ih =>
    have hq0 : q ≠ 0 := fun h => hS (h ▸ Finset.mem_insert_self q S')
    have hS' : (0 : Fin (d + 1)) ∉ S' := fun h => hS (Finset.mem_insert_of_mem h)
    obtain ⟨L', hL', hzero', hfix'⟩ := ih hS'
    set w := L'.prod *ᵥ v with hw
    -- each step's product·ᵥv is the new Givens factor applied to the previous `w`
    have hstep : ∀ j, (List.prod (twoLevelEmbed 0 q (givensRotation (w 0) (w q)) :: L') *ᵥ v) j
        = (twoLevelEmbed 0 q (givensRotation (w 0) (w q)) *ᵥ w) j := fun j => by
      rw [List.prod_cons, ← Matrix.mulVec_mulVec]
    refine ⟨twoLevelEmbed 0 q (givensRotation (w 0) (w q)) :: L', ?_, ?_, ?_⟩
    · intro M hM
      rcases List.mem_cons.mp hM with hM | hM
      · exact hM ▸ isTwoLevelUnitary_twoLevelEmbed (Ne.symm hq0)
          (givensRotation_mem_unitaryGroup _ _)
      · exact hL' M hM
    · -- every coordinate of `insert q S'` is zeroed
      intro j hj
      rw [hstep j, twoLevelEmbed_mulVec (Ne.symm hq0)]
      rcases Finset.mem_insert.mp hj with hjq | hjS'
      · -- `j = q`: the Givens rotation zeroes it
        have hjne0 : j ≠ 0 := hjq ▸ hq0
        rw [ite_eq_right hjne0, ite_eq_left hjq]
        exact givensRotation_row_one_dotProduct (w 0) (w q)
      · -- `j ∈ S'`: untouched by this Givens step, already zero by the IH
        have hjne0 : j ≠ 0 := fun h => hS' (h ▸ hjS')
        have hjneq : j ≠ q := fun h => hqS' (h ▸ hjS')
        rw [ite_eq_right hjne0, ite_eq_right hjneq]
        exact hzero' j hjS'
    · -- coordinates outside `insert q S' ∪ {0}` are unchanged
      intro j hj0 hjins
      have hjq : j ≠ q := fun h => hjins (h ▸ Finset.mem_insert_self q S')
      have hjS' : j ∉ S' := fun h => hjins (Finset.mem_insert_of_mem h)
      rw [hstep j, twoLevelEmbed_mulVec (Ne.symm hq0), ite_eq_right hj0, ite_eq_right hjq]
      exact hfix' j hj0 hjS'

/-- **Column clearing for a vector (N&C eqs. 4.44–4.50).** For every `v : Fin (d+1) → ℂ` there is a
list `L` of two-level unitaries whose product sends `v` to a vector supported on coordinate `0`:
`(L.prod *ᵥ v) j = 0` for every `j ≠ 0`. Instance of `exists_twoLevelUnitaryList_clear_finset` with
`S` the set of all nonzero coordinates. -/
theorem exists_twoLevelUnitaryList_mulVec_eq_zero_of_ne (v : Fin (d + 1) → ℂ) :
    ∃ L : List (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ),
      (∀ M ∈ L, IsTwoLevelUnitary M) ∧ ∀ j : Fin (d + 1), j ≠ 0 → (L.prod *ᵥ v) j = 0 := by
  obtain ⟨L, hL, hzero, _⟩ :=
    exists_twoLevelUnitaryList_clear_finset (Finset.univ.erase 0) (by simp) v
  exact ⟨L, hL, fun j hj => hzero j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)⟩

/-- **Column clearing for the first column of a matrix (N&C eq. 4.50).** For every
`U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ` there is a list `L` of two-level unitaries such that the
first column of `L.prod * U` is a multiple of `e₀`: `(L.prod * U) i 0 = 0` for every `i ≠ 0`. This
is the first step of the §4.5.1 two-level decomposition, applied to `U`'s first column. -/
theorem exists_twoLevelUnitaryList_clear_first_column (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ∃ L : List (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ),
      (∀ M ∈ L, IsTwoLevelUnitary M) ∧ ∀ i : Fin (d + 1), i ≠ 0 → (L.prod * U) i 0 = 0 := by
  obtain ⟨L, hL, hzero⟩ := exists_twoLevelUnitaryList_mulVec_eq_zero_of_ne (fun k => U k 0)
  refine ⟨L, hL, fun i hi => ?_⟩
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hzero i hi

end AxQM.Concrete
