/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlockOneEmbedding

/-!
# Concrete: the block-diagonal peel of §4.5.1 (`phase ⊕ corner` from a cleared first column)

The two-level decomposition of an arbitrary `d × d` unitary (Nielsen & Chuang §4.5.1, p. 189–191)
proceeds by an induction on the dimension. Column-clearing
(`AxQM.Concrete.exists_twoLevelUnitaryList_clear_first_column`) reduces a `(d+1) × (d+1)`
unitary, after left-multiplication by two-level unitaries, to a matrix `W` whose first column is a
multiple of `e₀` (`W i 0 = 0` for `i ≠ 0`). N&C eq. (4.51) then reads off that such a `W`, *being
unitary*, is **block-diagonal**: its first row is also a multiple of `e₀`, so `W = 1 ⊕ V'` up to a
phase on coordinate `0`, with `V'` a `d × d` unitary on the remaining coordinates. The inductive
step then decomposes `V'`.

This file supplies that **peel** as reusable mathematics, independently of the induction
itself (`AxQM/Concrete/TwoLevelDecomposition.lean`):

* `phaseShift c` — the single-coordinate phase `diag(c, 1, …, 1)`, unitary for `|c| = 1`
  (`phaseShift_mem_unitaryGroup`) and a two-level unitary (`isTwoLevelUnitary_phaseShift`), acting
  nontrivially only on coordinate `0`.
* `apply_zero_of_clearFirstColumn` — the unitarity input: a unitary whose first column is a multiple
  of `e₀` has its **first row** a multiple of `e₀` too (`W 0 j = 0` for `j ≠ 0`), and `|W 0 0| = 1`.
* `exists_phaseShift_mul_blockOne_of_clearFirstColumn` — the peel: for such a `W` there is a
  phase `c` (with `|c| = 1`) and a `d × d` unitary `C` (the lower-right corner
  `W.submatrix Fin.succ Fin.succ`) with `W = phaseShift c * blockOne C`. Both factors are two-level
  unitaries (`phaseShift` directly, `blockOne` of a product of two-level factors via
  `isTwoLevelUnitary_blockOne`), which is what lets the §4.5.1 induction reassemble the corner's
  decomposition into two-level factors on the full space.

## Use

This is a shared building block for the §4.5.1 development (Exercise 4.43's `n`-qubit lift,
reusable by Exercises 4.37/4.38). The statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **The single-coordinate phase** `diag(c, 1, …, 1)`: the `(d+1) × (d+1)` diagonal matrix with `c`
in the top-left corner and `1` on the rest of the diagonal. It fixes every coordinate except `0`,
where it multiplies by `c`; for `|c| = 1` it is a (one-level, hence two-level) unitary. This is the
phase factor of the §4.5.1 block-diagonal peel `W = phaseShift (W 0 0) * blockOne C`. -/
def phaseShift (c : ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal (Fin.cons c (1 : Fin d → ℂ))

@[simp] theorem phaseShift_zero_zero (c : ℂ) :
    (phaseShift c : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) 0 0 = c := by
  simp [phaseShift, Matrix.diagonal_apply_eq]

/-- `phaseShift c` acts as the identity on the tail: its `(i.succ, i.succ)` entry is `1`. -/
@[simp] theorem phaseShift_succ_succ (c : ℂ) (i : Fin d) :
    (phaseShift c : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i.succ i.succ = 1 := by
  simp [phaseShift, Matrix.diagonal_apply_eq]

/-- `phaseShift c` is diagonal: off-diagonal entries vanish. -/
theorem phaseShift_apply_of_ne (c : ℂ) {i j : Fin (d + 1)} (h : i ≠ j) :
    phaseShift c i j = 0 :=
  Matrix.diagonal_apply_ne _ h

/-- **`phaseShift c` is unitary** when `|c| = 1` (equivalently `Complex.normSq c = 1`): a diagonal
matrix is unitary iff each diagonal entry has unit modulus, and here they are `c` and `1`. -/
theorem phaseShift_mem_unitaryGroup {c : ℂ} (hc : Complex.normSq c = 1) :
    (phaseShift c : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈
      Matrix.unitaryGroup (Fin (d + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, phaseShift,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.star_apply]
  induction i using Fin.cases with
  | zero => rw [Fin.cons_zero]; simp [mul_comm, Complex.mul_conj, hc]
  | succ i => rw [Fin.cons_succ]; simp

/-- **`phaseShift c` is a two-level unitary** when `|c| = 1`: it is unitary and agrees with the
identity outside the single coordinate `0` (take `p = q = 0` in `IsTwoLevelUnitary`). -/
theorem isTwoLevelUnitary_phaseShift {c : ℂ} (hc : Complex.normSq c = 1) :
    IsTwoLevelUnitary (phaseShift c : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
  refine ⟨phaseShift_mem_unitaryGroup hc, 0, 0, ?_⟩
  rintro i j hij'
  rcases eq_or_ne i j with rfl | hij
  · induction i using Fin.cases with
    | zero => rcases hij' with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd rfl h
    | succ i => simp
  · rw [phaseShift_apply_of_ne c hij, Matrix.one_apply_ne hij]

/-- **A unitary with cleared first column has a cleared first row too.** If `W` is unitary and its
first column is a multiple of `e₀` (`W i 0 = 0` for `i ≠ 0`), then `Wᴴ W = 1` forces
`conj (W 0 0) · W 0 j = (1) 0 j` for every `j`; taking `j = 0` gives `|W 0 0|² = 1`, and for `j ≠ 0`
the right side is `0` and `conj (W 0 0) ≠ 0`, so `W 0 j = 0`. -/
theorem apply_zero_of_clearFirstColumn {W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin (d + 1)) ℂ) (hcol : ∀ i, i ≠ 0 → W i 0 = 0) :
    Complex.normSq (W 0 0) = 1 ∧ ∀ j, j ≠ 0 → W 0 j = 0 := by
  have h1 : Wᴴ * W = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hW
  -- the collapsed `(0, j)` entry of `Wᴴ W = 1`
  have key : ∀ j, (starRingEnd ℂ) (W 0 0) * W 0 j =
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) 0 j := by
    intro j
    have hj := congrFun (congrFun h1 0) j
    rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)
      (fun k _ hk => by rw [Matrix.conjTranspose_apply, hcol k hk, star_zero, zero_mul])] at hj
    rwa [Matrix.conjTranspose_apply] at hj
  have hnorm : Complex.normSq (W 0 0) = 1 := by
    have h0 := key 0
    rw [Matrix.one_apply_eq, ← Complex.normSq_eq_conj_mul_self] at h0
    exact_mod_cast h0
  refine ⟨hnorm, fun j hj => ?_⟩
  have hne : (starRingEnd ℂ) (W 0 0) ≠ 0 := by
    simp only [ne_eq, map_eq_zero]
    intro h; rw [h] at hnorm; simp at hnorm
  have hkj := key j
  rw [Matrix.one_apply_ne (Ne.symm hj)] at hkj
  exact (mul_eq_zero.mp hkj).resolve_left hne

/-- **The block-diagonal peel (N&C eq. 4.51).** A `(d+1) × (d+1)` unitary `W` whose first column is
a multiple of `e₀` factors as `W = phaseShift c * blockOne C`, where the phase `c = W 0 0` has unit
modulus and the corner `C = W.submatrix Fin.succ Fin.succ` (the lower-right `d × d` block) is
unitary. Both factors are two-level-unitary building blocks: `phaseShift c` directly
(`isTwoLevelUnitary_phaseShift`), and `blockOne` sends a decomposition of `C` into two-level factors
back to two-level factors on the full space (`isTwoLevelUnitary_blockOne`). This is the step
of the §4.5.1 induction that peels off one dimension. -/
theorem exists_phaseShift_mul_blockOne_of_clearFirstColumn
    {W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (hW : W ∈ Matrix.unitaryGroup (Fin (d + 1)) ℂ)
    (hcol : ∀ i, i ≠ 0 → W i 0 = 0) :
    ∃ (c : ℂ) (C : Matrix (Fin d) (Fin d) ℂ),
      Complex.normSq c = 1 ∧ C ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        W = phaseShift c * blockOne C := by
  obtain ⟨hnorm, hrow⟩ := apply_zero_of_clearFirstColumn hW hcol
  set C : Matrix (Fin d) (Fin d) ℂ := W.submatrix Fin.succ Fin.succ with hC
  have h1 : Wᴴ * W = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hW
  -- the corner `C` is unitary: `Cᴴ C = 1` from the `(i.succ, j.succ)` entries of `Wᴴ W = 1`
  have hCunit : C ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    have hij := congrFun (congrFun h1 i.succ) j.succ
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at hij
    have hz : Wᴴ i.succ 0 * W 0 j.succ = 0 := by
      rw [Matrix.conjTranspose_apply, hrow i.succ (Fin.succ_ne_zero i), star_zero, zero_mul]
    rw [hz, zero_add] at hij
    have hsum : (∑ k : Fin d, Cᴴ i k * C k j)
        = ∑ k : Fin d, Wᴴ i.succ k.succ * W k.succ j.succ :=
      Finset.sum_congr rfl fun k _ => by
        simp only [hC, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
    rw [Matrix.mul_apply, hsum, hij]
    simp [Matrix.one_apply, Fin.succ_inj]
  refine ⟨W 0 0, C, hnorm, hCunit, ?_⟩
  ext i j
  rw [phaseShift, Matrix.diagonal_mul]
  induction i using Fin.cases with
  | zero =>
    rw [Fin.cons_zero]
    induction j using Fin.cases with
    | zero => rw [blockOne_zero_zero, mul_one]
    | succ j => rw [blockOne_zero_succ, mul_zero]; exact hrow j.succ (Fin.succ_ne_zero j)
  | succ i =>
    rw [Fin.cons_succ, Pi.one_apply, one_mul]
    induction j using Fin.cases with
    | zero => rw [blockOne_succ_zero]; exact hcol i.succ (Fin.succ_ne_zero i)
    | succ j => rw [blockOne_succ_succ, hC, Matrix.submatrix_apply]

end AxQM.Concrete
