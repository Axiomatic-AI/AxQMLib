/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ProcessTomography
import ToMathlib.LinearAlgebra.Matrix.Kronecker
import ToMathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.PEquiv

/-!
# Concrete: two-qubit quantum process tomography (Nielsen & Chuang, Exercise 8.34)

This file lifts the single-qubit
process-reconstruction identity of Box 8.5 (`AxQM/Concrete/ProcessTomography.lean`) to **two
qubits**, formalizing Nielsen & Chuang's Exercise 8.34, eqs. (8.180)–(8.181).

A two-qubit quantum operation is written in the `16`-element operator basis `Ẽ_M = Ẽ_{m₁} ⊗ Ẽ_{m₂}`
(`tomoBasis2`, the pairwise Kronecker products of the single-qubit basis `{I, X, -iY, Z}`) as
`E₂(ρ) = Σ_{MN} χ₂_{MN} Ẽ_M ρ Ẽ_N†` (`chiProcess2`), the `16 × 16` matrix `χ₂` being what process
tomography determines. Box 8.5's reconstruction lifts through the Kronecker product: with

`Λ₂ = Λ ⊗ Λ`   (`chiLambda2`, N&C `Λ₂ = Λ ⊗ Λ`)

and the block matrix `M` of measured density matrices whose block `(A, B)` is `E₂(|A⟩⟨B|)`
(`chiGrid2`), the reconstruction reads

`χ₂ = Λ₂ (Pᵀ M P) Λ₂`   (`chiLambda2_chiGrid2_chiLambda2`, N&C eqs. (8.180)–(8.181)),

where `P` is the perfect-shuffle permutation matrix (`shuffleMatrix`, N&C's `P = I ⊗ SWAP ⊗ I`).

## Index convention and the role of `P`

All `16 × 16` matrices carry the index type `(Fin 2 × Fin 2) × (Fin 2 × Fin 2)`. The single-qubit
`Λ` (`Concrete.chiLambda`) pairs an *operator* index with a *grid* index `(basis, entry)`; its
Kronecker square `Λ₂` therefore pairs its four atomic `Fin 2` slots **qubit-by-qubit**, in the
order `(a₁, i₁, a₂, i₂)` — qubit `1`'s `(basis, entry)` then qubit `2`'s. The physically measured
grid `chiGrid2`, by contrast, is a block matrix indexed **role-by-role**: outer block index the full
two-qubit basis state `(a₁, a₂)`, inner index the full two-qubit entry `(i₁, i₂)`. These two
groupings differ by swapping the two middle slots `i₁ ↔ a₂`; the permutation `P` that performs this
swap is exactly `shuffle` (`Equiv.prodProdProdComm`), i.e. Nielsen & Chuang's `I ⊗ SWAP ⊗ I`
(identity on the outer two slots, `SWAP` on the middle two). `P` is a symmetric involution
(`shuffleMatrix_transpose`, `shuffleMatrix_transpose_mul`), so `Pᵀ = P = P⁻¹` and the sandwich
`Pᵀ M P` is the reindexing of the role-grouped grid into the qubit-grouped order `Λ₂` consumes.

## The measured blocks (eq. 8.181)

N&C write the grid blocks as `ρ'_{nm} = E₂(ρ_{nm})` with `ρ_{nm} = T_n |00⟩⟨00| T_m` and
`T₁ = I⊗I`, `T₂ = I⊗X`, `T₃ = X⊗I`, `T₄ = X⊗X`. Here `tomoT n = (I,X)_{n₁} ⊗ (I,X)_{n₂}` realizes
the `T_n`, and `rhoBlock_eq` proves `ρ_{nm} = |n⟩⟨m|` (i.e. `T_n |00⟩⟨00| T_m = single n m 1`),
so the block `(n, m)` of `chiGrid2` is `E₂(ρ_{nm})` as required.

## Proof strategy

The reconstruction reduces, via the Kronecker mixed-product law `(A⊗A')(B⊗B') = (AB)⊗(A'B')`
(`Matrix.mul_kronecker_mul`), to two copies of the single-qubit sandwich
`Λ (Ẽ_m|·⟩⟨·|Ẽ_n†) Λ = single m n 1` (`Concrete.chiLambda_tomoOuter_chiLambda`):
`Λ₂ (O_{m₁n₁} ⊗ O_{m₂n₂}) Λ₂ = single M N 1` (`chiLambda2_tomoOuter2Kron_chiLambda2`). The
role-grouped grid decomposes into the same rank-one pieces `O_{MN}` up to the shuffle `P`
(`chiGrid2_submatrix_shuffle`), and `Pᵀ · M · P` realizes that shuffle as a matrix product
(`shuffleMatrix_conj`).

It is the two-qubit half of the process-tomography pair, sharing the single-qubit foundation with
Exercise 8.35.
-/

namespace AxQM.Concrete

open Matrix
open scoped Matrix Kronecker

noncomputable section

/-- Row/column index type of the two-qubit `16 × 16` matrices: `(Fin 2 × Fin 2) × (Fin 2 × Fin 2)`.
The first `Fin 2 × Fin 2` is qubit `1`'s slot, the second qubit `2`'s; each carries the single-qubit
Box 8.5 operator/grid index. -/
abbrev TomoIdx2 : Type := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- The two-qubit operator basis `Ẽ_M = Ẽ_{m₁} ⊗ Ẽ_{m₂}`, the pairwise Kronecker products of the
single-qubit Box 8.5 basis `{I, X, -iY, Z}` (`tomoBasis`), indexed by `M = (m₁, m₂)`. -/
def tomoBasis2 (M : TomoIdx2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tomoBasis M.1 ⊗ₖ tomoBasis M.2

/-- Lambda for two qubits: `Λ₂ = Λ ⊗ Λ` (Kronecker square of Box 8.5's `Λ`). -/
def chiLambda2 : Matrix TomoIdx2 TomoIdx2 ℂ :=
  chiLambda ⊗ₖ chiLambda

/-- The two-qubit process `E₂(ρ) = Σ_{MN} χ₂_{MN} Ẽ_M ρ Ẽ_N†`. -/
def chiProcess2 (χ : Matrix TomoIdx2 TomoIdx2 ℂ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ M, ∑ N, χ M N • (tomoBasis2 M * ρ * (tomoBasis2 N)ᴴ)

/-- The block matrix of measured outputs, block `(A, B)` = `E₂(|A⟩⟨B|)`, indexed role-by-role:
the outer index is the two-qubit basis state, the inner index the two-qubit entry. -/
def chiGrid2 (χ : Matrix TomoIdx2 TomoIdx2 ℂ) : Matrix TomoIdx2 TomoIdx2 ℂ :=
  Matrix.of fun U V => chiProcess2 χ (Matrix.single U.1 V.1 1) U.2 V.2

/-- The role-grouped rank-one piece `Ẽ_M |·⟩⟨·| Ẽ_N†` of the two-qubit grid (the direct two-qubit
analogue of `Concrete.tomoOuter`). -/
def tomoOuter2 (M N : TomoIdx2) : Matrix TomoIdx2 TomoIdx2 ℂ :=
  Matrix.of fun U V => tomoBasis2 M U.2 U.1 * star (tomoBasis2 N V.2 V.1)

/-- The qubit-grouped rank-one piece `O_{m₁n₁} ⊗ O_{m₂n₂}`, the Kronecker product of the two
single-qubit outers (`Concrete.tomoOuter`) — the form on which `Λ₂` acts by the mixed-product
law. -/
def tomoOuter2Kron (M N : TomoIdx2) : Matrix TomoIdx2 TomoIdx2 ℂ :=
  tomoOuter M.1 N.1 ⊗ₖ tomoOuter M.2 N.2

/-- The perfect-shuffle permutation of the four atomic `Fin 2` slots that swaps the middle two
(`(a₁, i₁, a₂, i₂) ↦ (a₁, a₂, i₁, i₂)`), converting the qubit-grouped order to the role-grouped
order. This is Nielsen & Chuang's `I ⊗ SWAP ⊗ I`. -/
def shuffle : Equiv.Perm TomoIdx2 :=
  Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)

/-- The permutation matrix `P` of the perfect shuffle (`shuffle`); Nielsen & Chuang's
`P = I ⊗ SWAP ⊗ I` from eq. (8.181). -/
def shuffleMatrix : Matrix TomoIdx2 TomoIdx2 ℂ :=
  Equiv.Perm.permMatrix ℂ shuffle

/-- The two-qubit grid decomposes into the role-grouped rank-one pieces weighted by `χ₂`
(the two-qubit analogue of `Concrete.chiGrid_eq`). -/
theorem chiGrid2_eq (χ : Matrix TomoIdx2 TomoIdx2 ℂ) :
    chiGrid2 χ = ∑ M, ∑ N, χ M N • tomoOuter2 M N := by
  ext U V
  simp only [chiGrid2, Matrix.of_apply, chiProcess2, Matrix.sum_apply, Matrix.smul_apply,
    mul_single_mul_conjTranspose, tomoOuter2, smul_eq_mul]

/-- **Kronecker sandwich of a rank-one piece** (eq. 8.180 core): `Λ₂ (O_{m₁n₁} ⊗ O_{m₂n₂}) Λ₂`
recovers the elementary matrix `single M N 1`, by the Kronecker mixed-product law applied to two
copies of the single-qubit sandwich `Concrete.chiLambda_tomoOuter_chiLambda`. -/
theorem chiLambda2_tomoOuter2Kron_chiLambda2 (M N : TomoIdx2) :
    chiLambda2 * tomoOuter2Kron M N * chiLambda2 = Matrix.single M N 1 := by
  rw [chiLambda2, tomoOuter2Kron, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    chiLambda_tomoOuter_chiLambda, chiLambda_tomoOuter_chiLambda, Matrix.single_kronecker_single,
    mul_one]

/-- Reconstruction over the qubit-grouped grid: `Λ₂ (Σ χ₂_{MN} O_{m₁n₁} ⊗ O_{m₂n₂}) Λ₂ = χ₂`. -/
theorem chiLambda2_tomoOuter2Kron_sum (χ : Matrix TomoIdx2 TomoIdx2 ℂ) :
    chiLambda2 * (∑ M, ∑ N, χ M N • tomoOuter2Kron M N) * chiLambda2 = χ := by
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    chiLambda2_tomoOuter2Kron_chiLambda2, Matrix.smul_single, smul_eq_mul, mul_one,
    ← Matrix.matrix_eq_sum_single]

/-- The role-grouped and qubit-grouped rank-one pieces are related by the perfect shuffle:
`(tomoOuter2 M N).submatrix shuffle shuffle = O_{m₁n₁} ⊗ O_{m₂n₂}`. Both sides are the product
of the same four operator-basis entries; the shuffle only regroups the four atomic index slots. -/
theorem tomoOuter2_submatrix_shuffle (M N : TomoIdx2) :
    (tomoOuter2 M N).submatrix shuffle shuffle = tomoOuter2Kron M N := by
  ext u v
  simp only [Matrix.submatrix_apply, shuffle, Equiv.prodProdProdComm_apply, tomoOuter2,
    tomoOuter2Kron, tomoOuter, tomoBasis2, Matrix.of_apply, Matrix.kroneckerMap_apply, star_mul']
  ring

/-- The reindexed grid is the qubit-grouped weighted sum of rank-one pieces:
`(chiGrid2 χ).submatrix shuffle shuffle = Σ χ₂_{MN} O_{m₁n₁} ⊗ O_{m₂n₂}`. -/
theorem chiGrid2_submatrix_shuffle (χ : Matrix TomoIdx2 TomoIdx2 ℂ) :
    (chiGrid2 χ).submatrix shuffle shuffle = ∑ M, ∑ N, χ M N • tomoOuter2Kron M N := by
  rw [chiGrid2_eq]
  ext u v
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun N _ => ?_
  rw [← tomoOuter2_submatrix_shuffle M N, Matrix.submatrix_apply]

/-- The perfect shuffle is its own inverse (a symmetric involution). Since all four factors of
`Equiv.prodProdProdComm` coincide here, this is Mathlib's `Equiv.prodProdProdComm_symm` (whose
`β ↔ γ` swap is a no-op). -/
theorem shuffle_symm : shuffle.symm = shuffle :=
  Equiv.prodProdProdComm_symm (Fin 2) (Fin 2) (Fin 2) (Fin 2)

/-- `Pᵀ = P`: the perfect-shuffle permutation matrix is symmetric (its permutation is an
involution, so `P⁻¹ = P`). -/
theorem shuffleMatrix_transpose : shuffleMatrixᵀ = shuffleMatrix := by
  have h : shuffle⁻¹ = shuffle := shuffle_symm
  rw [shuffleMatrix, Matrix.transpose_permMatrix, h]

/-- Conjugating any matrix by the shuffle permutation matrix reindexes it by the shuffle:
`Pᵀ M P = M.submatrix shuffle shuffle`. -/
theorem shuffleMatrix_conj (M : Matrix TomoIdx2 TomoIdx2 ℂ) :
    shuffleMatrixᵀ * M * shuffleMatrix = M.submatrix shuffle shuffle := by
  rw [shuffleMatrix_transpose, shuffleMatrix]
  simp only [Equiv.Perm.permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix,
    shuffle_symm]
  simp only [Function.comp_id, Function.id_comp]

/-- `P` is a permutation matrix: `Pᵀ · P = 1` (so `Pᵀ = P⁻¹`; with `shuffleMatrix_transpose`,
`P` is a symmetric orthogonal permutation matrix). From `shuffleMatrix_conj` applied to `1`. -/
theorem shuffleMatrix_transpose_mul : shuffleMatrixᵀ * shuffleMatrix = 1 := by
  have h := shuffleMatrix_conj 1
  rwa [Matrix.mul_one, Matrix.submatrix_one_equiv] at h

/-- **Two-qubit process reconstruction** (Nielsen & Chuang, Exercise 8.34, eqs. (8.180)–(8.181)):
`χ₂ = Λ₂ (Pᵀ M P) Λ₂`, with `Λ₂ = Λ ⊗ Λ`, `M` the block matrix of measured outputs `E₂(|A⟩⟨B|)`
(`chiGrid2`), and `P` the perfect-shuffle permutation matrix `I ⊗ SWAP ⊗ I`. -/
theorem chiLambda2_chiGrid2_chiLambda2 (χ : Matrix TomoIdx2 TomoIdx2 ℂ) :
    chiLambda2 * (shuffleMatrixᵀ * chiGrid2 χ * shuffleMatrix) * chiLambda2 = χ := by
  rw [shuffleMatrix_conj, chiGrid2_submatrix_shuffle]
  exact chiLambda2_tomoOuter2Kron_sum χ

/-! ### The measured blocks `ρ_{nm} = T_n |00⟩⟨00| T_m` (eq. 8.181) -/

/-- The single-qubit factors of the state-preparation operators `T_n`: `(I, X)` indexed by `Fin 2`
(`0 ↦ I`, `1 ↦ X`). -/
def flipIX : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![1, pauliX]

/-- The two-qubit state-preparation operators `T_n = (I,X)_{n₁} ⊗ (I,X)_{n₂}` of eq. (8.181):
`T₁ = I⊗I`, `T₂ = I⊗X`, `T₃ = X⊗I`, `T₄ = X⊗X` under `n = (n₁, n₂)`. -/
def tomoT (n : Fin 2 × Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  flipIX n.1 ⊗ₖ flipIX n.2

/-- The measured input block `ρ_{nm} = T_n |00⟩⟨00| T_m` of eq. (8.181). -/
def rhoBlock (n m : Fin 2 × Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tomoT n * Matrix.single (0, 0) (0, 0) 1 * tomoT m

/-- Each single-qubit factor `(I, X)` is Hermitian. -/
theorem flipIX_isHermitian (k : Fin 2) : (flipIX k)ᴴ = flipIX k := by
  fin_cases k <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [flipIX, pauliX, Matrix.conjTranspose_apply])

/-- `T_n` is Hermitian. -/
theorem tomoT_isHermitian (n : Fin 2 × Fin 2) : (tomoT n)ᴴ = tomoT n := by
  rw [tomoT, Matrix.conjTranspose_kronecker, flipIX_isHermitian, flipIX_isHermitian]

/-- The column-`(0,0)` of `T_n` is the basis vector `|n⟩`: `T_n i (0,0) = δ_{i,n}`, because
`T_n |00⟩ = |n⟩`. -/
theorem tomoT_apply_zero (n i : Fin 2 × Fin 2) :
    tomoT n i (0, 0) = if i = n then 1 else 0 := by
  obtain ⟨n1, n2⟩ := n
  obtain ⟨i1, i2⟩ := i
  fin_cases n1 <;> fin_cases n2 <;> fin_cases i1 <;> fin_cases i2 <;>
    simp [tomoT, flipIX, pauliX, Matrix.kroneckerMap_apply, Prod.ext_iff]

/-- **The measured blocks are computational-basis outer products** (eq. 8.181):
`ρ_{nm} = T_n |00⟩⟨00| T_m = |n⟩⟨m|`. So the block `(n, m)` of `chiGrid2` is `E₂(ρ_{nm})`. -/
theorem rhoBlock_eq (n m : Fin 2 × Fin 2) : rhoBlock n m = Matrix.single n m 1 := by
  rw [rhoBlock, ← tomoT_isHermitian m]
  ext i j
  rw [mul_single_mul_conjTranspose, tomoT_apply_zero, tomoT_apply_zero, Matrix.single_apply]
  simp only [apply_ite (star : ℂ → ℂ), star_one, star_zero]
  split_ifs <;> simp_all

/-- The `(n, m)` block of the measured grid is `E₂(ρ_{nm})` with `ρ_{nm} = T_n |00⟩⟨00| T_m`,
tying `chiGrid2` to Nielsen & Chuang's eq. (8.181) presentation of the measured data. -/
theorem chiGrid2_apply_rhoBlock (χ : Matrix TomoIdx2 TomoIdx2 ℂ) (U V : TomoIdx2) :
    chiGrid2 χ U V = chiProcess2 χ (rhoBlock U.1 V.1) U.2 V.2 := by
  rw [chiGrid2, Matrix.of_apply, rhoBlock_eq]

end

end AxQM.Concrete
