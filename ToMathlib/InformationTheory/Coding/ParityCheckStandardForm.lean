/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.ParityCheck
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Reducing a parity-check matrix to standard form `[A ∣ I]`

Following Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.4.1, the second
half of **Exercise 10.16** (p. 447): once we know that elementary row operations leave the code
unchanged (`LinearCode.ofParityCheck_updateRow_add`, the first half), *"using Gaussian elimination
and swapping of bits it is therefore possible to assume that the parity check matrix has the
standard form `[A ∣ I_{n−k}]`, where `A` is an `(n − k) × k` matrix."*

This file proves the mathematical content of that reduction. A parity-check matrix `H` of an
`[n, k]` code is an `(n − k) × n` matrix of **full row rank** `n − k`: its `n − k` parity checks
are independent, equivalently the map `x ↦ H *ᵥ x` is surjective. We show that such an `H` can be
brought, by an invertible row operation and a choice of which `n − k` coordinates carry the
identity block, to a matrix with an identity submatrix on those coordinates while defining the very
same code. This is exactly `[A ∣ I]` up to the coordinate reordering ("swapping of bits") that
moves the check positions to the end.

## Main results

* `Matrix.exists_injective_isUnit_submatrix_of_mulVecLin_surjective`: the linear-algebra crux — a
  matrix over a field whose map `x ↦ H *ᵥ x` is surjective (full row rank) has an **invertible
  square column submatrix**. There is an injective `f : μ → ι` selecting `n − k` columns such that
  `H.submatrix id f` is a unit. (Its columns are a basis of the row space; this is the invertible
  `(n − k) × (n − k)` minor of a full-row-rank matrix.)
* `LinearCode.ofParityCheck_mul_left_of_isUnit`: **an invertible row operation leaves the code
  unchanged** — for a unit `E`, the matrices `E * H` and `H` are parity-check matrices for the same
  code. This is the "Gaussian elimination" half of the exercise: it packages an arbitrary sequence
  of the elementary steps `ofParityCheck_updateRow_add` into a single invertible `E`.
* `LinearCode.exists_isUnit_submatrix_eq_one_of_mulVecLin_surjective`: **the standard form**
  (Exercise 10.16, second claim). For a full-row-rank `H` there is an invertible row operation `E`
  and a choice of `n − k` coordinates `f` such that `E * H` has the identity on those coordinates,
  `(E * H).submatrix id f = 1`, and still checks the same code, `ofParityCheck (E * H) =
  ofParityCheck H`. Reordering the coordinates so that `f` lands last exhibits `E * H = [A ∣ I]`.

## Implementation notes

Coordinates are the arbitrary column index type `ι` (`= Fin n` for N&C's binary codes) and the
check index is `μ` (`= Fin (n − k)`); the field is `K` (`= ZMod 2` for N&C). Rather than physically
permute columns into the literal block form `Matrix.fromCols A 1` (`Matrix.stdParityCheck`,
Exercise 10.19), which would require reindexing `ι ≃ κ ⊕ μ`, we state the standard form as "there is
an identity submatrix on a subset `f` of the coordinates". This is faithful to N&C's "it is
possible to *assume* the standard form": the entries of `E * H` off the `f`-columns are the block
`A`, and the "swapping of bits" is precisely the relabelling of coordinates that moves the
`f`-columns to the end to read off `[A ∣ I]`.

The full-row-rank hypothesis is not a weakening but a necessity: `[A ∣ I_{n−k}]` has rank `n − k`,
so only a rank-`(n − k)` parity check can be reduced to it, and the parity-check matrix of an
`[n, k]` code has exactly this rank. The crux is the standard fact that the columns of a
full-row-rank matrix span the row space and hence contain a basis (`exists_linearIndependent'`); a
square matrix whose columns are a basis is invertible (`Matrix.linearIndependent_col_iff_isUnit`).
The row operation `E` is then the inverse of that invertible minor, which clears it to the identity.
-/

open Matrix

@[expose] public section

namespace Matrix

variable {K : Type*} [Field K] {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]

/-- **A full-row-rank matrix over a field has an invertible square column submatrix.** If the map
`x ↦ H *ᵥ x` is surjective (`H` has full row rank `n − k`), then some `n − k` of its columns are
linearly independent: there is an injective `f : μ → ι` for which the square submatrix
`H.submatrix id f` is a unit. This is the invertible `(n − k) × (n − k)` minor underlying the
standard-form reduction of Nielsen & Chuang, Exercise 10.16.

The columns of `H` span the whole codomain `μ → K` (`Matrix.range_mulVecLin`), so they contain a
basis (`exists_linearIndependent'`); such a basis has `n − k = Fintype.card μ` elements, indexing an
injective selection `f` of columns, and a square matrix whose columns form a basis is invertible
(`Matrix.linearIndependent_col_iff_isUnit`). -/
theorem exists_injective_isUnit_submatrix_of_mulVecLin_surjective
    (H : Matrix μ ι K) (hH : Function.Surjective H.mulVecLin) :
    ∃ f : μ → ι, Function.Injective f ∧ IsUnit (H.submatrix id f) := by
  have hspan : Submodule.span K (Set.range H.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]; exact hH
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K H.col
  have hsp' : Submodule.span K (Set.range (H.col ∘ a)) = ⊤ := by rw [hsp, hspan]
  let b : Module.Basis κ K (μ → K) := Module.Basis.mk hli hsp'.ge
  have : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card μ = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_pi K]
  let e : μ ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  rw [← Matrix.linearIndependent_col_iff_isUnit]
  exact hli.comp e e.injective

end Matrix

namespace LinearCode

variable {K : Type*} [Field K] {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]

/-- **An invertible row operation leaves the parity-check code unchanged.** For a unit `E`, the
matrices `E * H` and `H` define the same code: `ofParityCheck (E * H) = ofParityCheck H`. Since the
invertible matrices over a field are generated by the elementary row operations, this packages an
arbitrary Gaussian-elimination sequence of `ofParityCheck_updateRow_add` steps into one statement
(Nielsen & Chuang, Exercise 10.16). A word `x` is annihilated by `E * H` iff `E *ᵥ (H *ᵥ x) = 0`
iff `H *ᵥ x = 0` (as `E *ᵥ ·` is injective), i.e. iff it is annihilated by `H`. -/
theorem ofParityCheck_mul_left_of_isUnit {E : Matrix μ μ K} (hE : IsUnit E) (H : Matrix μ ι K) :
    ofParityCheck (E * H) = ofParityCheck H := by
  have hinj : Function.Injective E.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hE
  ext x
  rw [mem_ofParityCheck_iff, mem_ofParityCheck_iff, ← Matrix.mulVec_mulVec]
  nth_rewrite 1 [← Matrix.mulVec_zero E]
  rw [hinj.eq_iff]

/-- **Standard form of a parity-check matrix** (Nielsen & Chuang, Exercise 10.16, p. 447, second
claim). A full-row-rank parity-check matrix `H` — one whose map `x ↦ H *ᵥ x` is surjective — can be
reduced, by an invertible row operation `E` (Gaussian elimination) and a choice of `n − k`
coordinates `f` (the positions carrying the identity block, fixed by "swapping of bits"), to a
matrix `E * H` with an **identity submatrix on those coordinates**, `(E * H).submatrix id f = 1`,
that checks the **same code**, `ofParityCheck (E * H) = ofParityCheck H`. Reordering the coordinates
so that `f` comes last displays `E * H = [A ∣ I_{n−k}]`, where the off-`f` columns form `A`.

The invertible minor `H.submatrix id f` exists by
`Matrix.exists_injective_isUnit_submatrix_of_mulVecLin_surjective`; taking `E` to be its inverse
clears it to the identity, and `ofParityCheck_mul_left_of_isUnit` guarantees the code is
preserved. -/
theorem exists_isUnit_submatrix_eq_one_of_mulVecLin_surjective
    (H : Matrix μ ι K) (hH : Function.Surjective H.mulVecLin) :
    ∃ E : Matrix μ μ K, IsUnit E ∧ ∃ f : μ → ι, Function.Injective f ∧
      (E * H).submatrix id f = 1 ∧ ofParityCheck (E * H) = ofParityCheck H := by
  obtain ⟨f, hf, hB⟩ := H.exists_injective_isUnit_submatrix_of_mulVecLin_surjective hH
  have hdet : IsUnit (H.submatrix id f).det := (Matrix.isUnit_iff_isUnit_det _).mp hB
  have hE : IsUnit (H.submatrix id f)⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hB
  refine ⟨(H.submatrix id f)⁻¹, hE, f, hf, ?_, ofParityCheck_mul_left_of_isUnit hE H⟩
  rw [Matrix.submatrix_mul _ _ id id f Function.bijective_id, Matrix.submatrix_id_id]
  exact Matrix.nonsing_inv_mul _ hdet

end LinearCode

end
