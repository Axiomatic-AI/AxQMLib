/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Field.ZMod

/-!
# A polynomial bound on the number of transvections reducing a matrix

`Mathlib.LinearAlgebra.Matrix.Transvection` shows that any square matrix over a field can be
reduced to diagonal form by left/right multiplication by transvections
(`Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`), but *discards* the lengths of
the transvection lists. Here we re-run that reduction tracking the lengths, obtaining an **`O(n²)`
bound** on the number of transvections (`n` the size of the matrix). This is the quantitative
content of Gaussian elimination: an `n × n` matrix is cleared with `O(n²)` elementary row/column
operations.

Over `ZMod 2` the determinant of an invertible matrix is `1`, so the reduction's diagonal factor is
the identity and an **invertible `𝔽₂` matrix is a product of at most `2n²` transvections**
(`Matrix.exists_transvecStruct_prod_length_le`). Each `𝔽₂`-transvection with coefficient `1` is a
`CNOT` gate — adding one coordinate into another — so this says every invertible `𝔽₂`-linear map is
realised by `O(n²)` `CNOT` gates, the standard *linear-reversible circuit synthesis* used e.g. in
Nielsen & Chuang Problem 7.1 to make a cyclic-permutation circuit efficient.

## Main results

* `Matrix.Pivot.exists_diagonal_length` / `Matrix.Pivot.exists_transvec_mul_diagonal_length` — the
  length-tracked diagonal reduction: transvection lists of length `≤ card²`.
* `Matrix.exists_transvecStruct_prod_length_le` — an invertible matrix over `ZMod 2` is a product of
  at most `2 * card²` transvections.
* `Matrix.exists_transvecStruct_prod_toMatrix_length_le` — the matrix (in any basis) of an
  `𝔽₂`-linear automorphism of a finite-dimensional space is a product of at most `2 * dim²`
  transvections.
-/

@[expose] public section

namespace Matrix

namespace Pivot

open Unit Sum _root_.Fin TransvectionStruct

variable {𝕜 : Type*} [Field 𝕜]

/-- Length-tracked version of `Matrix.Pivot.exists_isTwoBlockDiagonal_of_ne_zero`: when the last
coefficient is nonzero, the two transvection lists that clear the last row and column have length
exactly `r`. -/
theorem exists_isTwoBlockDiagonal_of_ne_zero_length {r : ℕ}
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) (hM : M (inr unit) (inr unit) ≠ 0) :
    ∃ L L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod)
        ∧ L.length = r ∧ L'.length = r := by
  let L : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr unit, by simp, -M (inl i) (inr unit) / M (inr unit) (inr unit)⟩
  let L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inr unit, inl i, by simp, -M (inr unit) (inl i) / M (inr unit) (inr unit)⟩
  refine ⟨L, L', ?_, by simp [L], by simp [L']⟩
  have A : L.map toMatrix = listTransvecCol M := by simp [L, listTransvecCol, Function.comp_def]
  have B : L'.map toMatrix = listTransvecRow M := by simp [L', listTransvecRow, Function.comp_def]
  rw [A, B]
  exact isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM

/-- Length-tracked version of
`Matrix.Pivot.exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec`: a matrix over
`Fin r ⊕ Unit` is made two-block-diagonal by transvection lists of length `≤ r + 1`. -/
theorem exists_isTwoBlockDiagonal_length {r : ℕ}
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) :
    ∃ L L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod)
        ∧ L.length ≤ r + 1 ∧ L'.length ≤ r + 1 := by
  by_cases H : IsTwoBlockDiagonal M
  · exact ⟨[], [], by simpa using H, by simp, by simp⟩
  by_cases hM : M (inr unit) (inr unit) = 0; swap
  · obtain ⟨L, L', hLL', hLlen, hL'len⟩ := exists_isTwoBlockDiagonal_of_ne_zero_length M hM
    exact ⟨L, L', hLL', by omega, by omega⟩
  simp only [not_and_or, IsTwoBlockDiagonal, toBlocks₁₂, toBlocks₂₁, ← Matrix.ext_iff] at H
  have : ∃ i : Fin r, M (inl i) (inr unit) ≠ 0 ∨ M (inr unit) (inl i) ≠ 0 := by
    rcases H with H | H
    · contrapose! H; rintro i ⟨⟩; exact (H i).1
    · contrapose! H; rintro ⟨⟩ j; exact (H j).2
  rcases this with ⟨i, h | h⟩
  · let M' := transvection (inr Unit.unit) (inl i) 1 * M
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [M', hM]
    obtain ⟨L, L', hLL', hLlen, hL'len⟩ := exists_isTwoBlockDiagonal_of_ne_zero_length M' hM'
    rw [Matrix.mul_assoc] at hLL'
    refine ⟨L ++ [⟨inr unit, inl i, by simp, 1⟩], L', ?_, by simp [hLlen], by omega⟩
    simp only [List.map_append, List.prod_append, Matrix.mul_one, toMatrix_mk, List.prod_cons,
      List.prod_nil, List.map, Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'
  · let M' := M * transvection (inl i) (inr unit) 1
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [M', hM]
    obtain ⟨L, L', hLL', hLlen, hL'len⟩ := exists_isTwoBlockDiagonal_of_ne_zero_length M' hM'
    refine ⟨L, ⟨inl i, inr unit, by simp, 1⟩::L', ?_, by omega, by simp [hL'len]⟩
    simp only [← Matrix.mul_assoc, toMatrix_mk, List.prod_cons, List.map]
    rw [Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'

/-- Length-tracked inductive step of the diagonal reduction: if size-`r` matrices reduce with
lists of length `≤ r²`, then matrices over `Fin r ⊕ Unit` reduce with lists of length `≤ (r + 1)²`
(one extra block costs `≤ r + 1` transvections). -/
theorem exists_diagonal_induction_length {r : ℕ}
    (IH : ∀ M : Matrix (Fin r) (Fin r) 𝕜,
        ∃ (L₀ L₀' : List (TransvectionStruct (Fin r) 𝕜)) (D₀ : Fin r → 𝕜),
          (L₀.map toMatrix).prod * M * (L₀'.map toMatrix).prod = diagonal D₀
            ∧ L₀.length ≤ r ^ 2 ∧ L₀'.length ≤ r ^ 2)
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) :
    ∃ (L L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜)) (D : Fin r ⊕ Unit → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D
        ∧ L.length ≤ (r + 1) ^ 2 ∧ L'.length ≤ (r + 1) ^ 2 := by
  obtain ⟨L₁, L₁', hM, hL1, hL1'⟩ := exists_isTwoBlockDiagonal_length M
  let M' := (L₁.map toMatrix).prod * M * (L₁'.map toMatrix).prod
  let M'' := toBlocks₁₁ M'
  obtain ⟨L₀, L₀', D₀, h₀, hL0, hL0'⟩ := IH M''
  set c := M' (inr unit) (inr unit) with hc
  refine ⟨L₀.map (sumInl Unit) ++ L₁, L₁' ++ L₀'.map (sumInl Unit),
      Sum.elim D₀ fun _ => c, ?_, ?_, ?_⟩
  · suffices (L₀.map (toMatrix ∘ sumInl Unit)).prod * M'
        * (L₀'.map (toMatrix ∘ sumInl Unit)).prod = diagonal (Sum.elim D₀ fun _ => c) by
      simpa [M', c, Matrix.mul_assoc]
    have : M' = fromBlocks M'' 0 0 (diagonal fun _ => c) := by
      rw [← fromBlocks_toBlocks M', hM.1, hM.2]; rfl
    rw [this]; simp [h₀]
  · simp only [List.length_append, List.length_map]
    have hexp : (r + 1) ^ 2 = r ^ 2 + (r + 1) + r := by ring
    omega
  · simp only [List.length_append, List.length_map]
    have hexp : (r + 1) ^ 2 = r ^ 2 + (r + 1) + r := by ring
    omega

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

/-- The length-tracked diagonal reduction is invariant under reindexing the matrix. -/
theorem reindex_exists_diagonal_length {B : ℕ} (M : Matrix p p 𝕜) (e : p ≃ n)
    (H : ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
        (L.map toMatrix).prod * Matrix.reindexAlgEquiv 𝕜 _ e M * (L'.map toMatrix).prod
          = diagonal D ∧ L.length ≤ B ∧ L'.length ≤ B) :
    ∃ (L L' : List (TransvectionStruct p 𝕜)) (D : p → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D
        ∧ L.length ≤ B ∧ L'.length ≤ B := by
  obtain ⟨L₀, L₀', D₀, h₀, hL0, hL0'⟩ := H
  refine ⟨L₀.map (reindexEquiv e.symm), L₀'.map (reindexEquiv e.symm), D₀ ∘ e, ?_,
    by simpa using hL0, by simpa using hL0'⟩
  have : M = reindexAlgEquiv 𝕜 _ e.symm (reindexAlgEquiv 𝕜 _ e M) := by
    simp only [Equiv.symm_symm, submatrix_submatrix, reindex_apply, submatrix_id_id,
      Equiv.symm_comp_self, coe_reindexAlgEquiv]
  rw [this]
  simp only [toMatrix_reindexEquiv_prod, List.map_map, coe_reindexAlgEquiv]
  simp only [← coe_reindexAlgEquiv 𝕜, ← map_mul, h₀]
  simp only [Equiv.symm_symm, reindex_apply, submatrix_diagonal_equiv, coe_reindexAlgEquiv]

/-- Auxiliary `Type 0` form (for the induction on `Fintype.card`) of the length-tracked reduction:
any matrix reduces to diagonal form with transvection lists of length `≤ card²`. -/
theorem exists_diagonal_length_aux (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D
        ∧ L.length ≤ Fintype.card n ^ 2 ∧ L'.length ≤ Fintype.card n ^ 2 := by
  suffices H : ∀ cn, Fintype.card n = cn →
      ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
        (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D
          ∧ L.length ≤ cn ^ 2 ∧ L'.length ≤ cn ^ 2 by exact H _ rfl
  intro cn hn
  induction cn generalizing n M with
  | zero =>
    refine ⟨[], [], fun _ => 1, ?_, by simp, by simp⟩
    ext i j
    rw [Fintype.card_eq_zero_iff] at hn
    exact hn.elim' i
  | succ r IH =>
    have e : n ≃ Fin r ⊕ Unit := by
      refine Fintype.equivOfCardEq ?_
      rw [hn, @Fintype.card_sum (Fin r) Unit _ _]
      simp
    apply reindex_exists_diagonal_length M e
    apply exists_diagonal_induction_length (fun N => IH (Fin r) N (by simp))

/-- **Length-bounded reduction to diagonal form.** Any `n × n` matrix over a field can be reduced
to diagonal form by left/right multiplication by transvections, using at most `card²` transvections
on each side. This is the quantitative form of
`Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`. -/
theorem exists_diagonal_length (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D
        ∧ L.length ≤ Fintype.card n ^ 2 ∧ L'.length ≤ Fintype.card n ^ 2 := by
  have e : n ≃ Fin (Fintype.card n) := Fintype.equivOfCardEq (by simp)
  apply reindex_exists_diagonal_length M e
  simpa using exists_diagonal_length_aux (Fin (Fintype.card n)) (reindexAlgEquiv 𝕜 _ e M)

/-- **Length-bounded transvection–diagonal–transvection factorisation.** Any `n × n` matrix over a
field is a product of a transvection product, a diagonal matrix, and a transvection product, with at
most `card²` transvections on each side. Quantitative form of
`Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`. -/
theorem exists_transvec_mul_diagonal_length (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod
        ∧ L.length ≤ Fintype.card n ^ 2 ∧ L'.length ≤ Fintype.card n ^ 2 := by
  obtain ⟨L, L', D, h, hL, hL'⟩ := exists_diagonal_length M
  refine ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, ?_,
    by simpa using hL, by simpa using hL'⟩
  suffices M = (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M
        * ((L'.map toMatrix).prod * (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod)
    by simpa [← h, Matrix.mul_assoc]
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]

end Pivot

open Pivot TransvectionStruct

/-- **An invertible matrix over `ZMod 2` is a product of `O(card²)` transvections.** Concretely, at
most `2 * card²` transvections; since an `𝔽₂`-transvection with coefficient `1` is a `CNOT` gate,
this is the linear-reversible synthesis of an invertible `𝔽₂` matrix as an `O(n²)`-`CNOT` circuit.
The determinant argument uses that over `ZMod 2` the reduction's diagonal factor has all diagonal
entries equal to `1` (the only nonzero element), hence is the identity. -/
theorem exists_transvecStruct_prod_length_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (ZMod 2)) (hM : M.det ≠ 0) :
    ∃ T : List (TransvectionStruct n (ZMod 2)),
      M = (T.map toMatrix).prod ∧ T.length ≤ 2 * Fintype.card n ^ 2 := by
  obtain ⟨L, L', D, hMeq, hL, hL'⟩ := exists_transvec_mul_diagonal_length M
  have hdet : M.det = ∏ i, D i := by
    rw [hMeq]; simp [Matrix.det_mul, det_toMatrix_prod, Matrix.det_diagonal]
  have hne : (∏ i, D i) ≠ 0 := hdet ▸ hM
  have h2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide +revert
  have hDi : ∀ i, D i = 1 := fun i =>
    h2 (D i) (fun h => hne (Finset.prod_eq_zero (Finset.mem_univ i) h))
  have hdiag : diagonal D = (1 : Matrix n n (ZMod 2)) := by
    rw [show D = (fun _ => 1) from funext hDi]; exact Matrix.diagonal_one
  rw [hdiag, Matrix.mul_one] at hMeq
  refine ⟨L ++ L', ?_, ?_⟩
  · rw [hMeq, List.map_append, List.prod_append]
  · simp only [List.length_append]; omega

/-- **The matrix of an `𝔽₂`-linear automorphism is a product of `O(dim²)` transvections.** For a
finite-dimensional `ZMod 2`-vector space `V` with basis `b` and a linear equivalence `L`, the matrix
`LinearMap.toMatrix b b L` is a product of at most `2 * card ι²` transvections (`CNOT` gates). -/
theorem exists_transvecStruct_prod_toMatrix_length_le {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 2) V) (L : V ≃ₗ[ZMod 2] V) :
    ∃ T : List (TransvectionStruct ι (ZMod 2)),
      LinearMap.toMatrix b b L.toLinearMap = (T.map toMatrix).prod
        ∧ T.length ≤ 2 * Fintype.card ι ^ 2 := by
  apply exists_transvecStruct_prod_length_le
  rw [LinearMap.det_toMatrix]
  exact (LinearEquiv.isUnit_det' L).ne_zero

end Matrix
