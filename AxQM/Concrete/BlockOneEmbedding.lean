/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QFTTwoLevel
import Mathlib.Data.Matrix.Mul

/-!
# Concrete: the `1 ⊕ M` block embedding fixing the first coordinate (N&C §4.5.1 block peel)

The two-level decomposition of an arbitrary `d × d` unitary (Nielsen & Chuang §4.5.1, p. 189–191)
proceeds by an induction on the dimension. Column-clearing
(`AxQM.Concrete.exists_twoLevelUnitaryList_clear_first_column`) reduces a `(d+1) × (d+1)`
unitary `U`, after left-multiplication by two-level unitaries, to a matrix whose first row and
column are those of the identity — a **block-diagonal** matrix `1 ⊕ V'` with `V'` a `d × d` unitary
on the remaining coordinates `1, …, d` (N&C eq. (4.51): "repeat this procedure for the `d − 1` by
`d − 1` unitary submatrix in the lower right hand corner"). The inductive step then decomposes `V'`.

This file provides the **embedding** underlying that peel, `blockOne`, independently of the peel and
induction themselves: `blockOne M` places a `d × d` matrix `M` into the lower-right
`{1, …, d}` block of a `(d+1) × (d+1)` matrix, fixing the first coordinate `0`.

## The construction and its algebra

`blockOne M` fixes coordinate `0` and acts as `M` on the tail (`i ↦ i.succ`): its `(0,0)` entry is
`1`, the rest of its first row and column are `0`, and `blockOne M i.succ j.succ = M i j`. Exactly
as for `twoLevelEmbed`, `blockOne` is a **`*`-homomorphism**:

* `blockOne_one` — it sends `1 ↦ 1`;
* `blockOne_mul` — it is multiplicative, `blockOne A * blockOne B = blockOne (A * B)`;
* `blockOne_conjTranspose` — it commutes with `ᴴ`, `(blockOne M)ᴴ = blockOne Mᴴ`.

Unitarity then needs no block manipulation: `(blockOne M)ᴴ * blockOne M = blockOne (Mᴴ * M) =
blockOne 1 = 1`, so `blockOne` sends a unitary to a unitary (`blockOne_mem_unitaryGroup`). A
two-level unitary maps to a two-level unitary (`isTwoLevelUnitary_blockOne`), its distinguished
block `{p, q}` shifted to `{p.succ, q.succ}` — this is what lets the inductive step re-assemble the
smaller decomposition into two-level factors on the full space.

## Use

This is a shared building block for the §4.5.1 development (Exercise 4.43's `n`-qubit lift). The
statement of Exercise 4.43 is in `AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **The `1 ⊕ M` block embedding.** `blockOne M` is the `(d+1) × (d+1)` matrix that fixes the first
coordinate `0` and acts as the `d × d` matrix `M` on the remaining coordinates `1, …, d` (identified
with `Fin d` via `Fin.succ`): its `(0,0)` entry is `1`, it agrees with the identity elsewhere in the
first row and column, and `blockOne M i.succ j.succ = M i j`. This is the block-diagonal form
`1 ⊕ V'` of the §4.5.1 two-level-decomposition induction. -/
def blockOne (M : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of (Fin.cons (Fin.cons 1 0) fun i => Fin.cons 0 (M i))

@[simp] theorem blockOne_zero_zero (M : Matrix (Fin d) (Fin d) ℂ) : blockOne M 0 0 = 1 := rfl

@[simp] theorem blockOne_zero_succ (M : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    blockOne M 0 j.succ = 0 := rfl

@[simp] theorem blockOne_succ_zero (M : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    blockOne M i.succ 0 = 0 := rfl

@[simp] theorem blockOne_succ_succ (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    blockOne M i.succ j.succ = M i j := rfl

/-- The embedding of the `d × d` identity is the `(d+1) × (d+1)` identity. -/
theorem blockOne_one : blockOne (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, eq_comm, Fin.succ_inj]

/-- **`blockOne` is multiplicative**: embedding respects matrix products,
`blockOne A * blockOne B = blockOne (A * B)`. The structural core making an embedded unitary
unitary. -/
theorem blockOne_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    blockOne A * blockOne B = blockOne (A * B) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [Matrix.mul_apply]

/-- **`blockOne` commutes with the conjugate transpose**: `(blockOne M)ᴴ = blockOne Mᴴ`. The block
`ᴴ` is `M`'s; the fixed coordinate and the zeros are real. -/
theorem blockOne_conjTranspose (M : Matrix (Fin d) (Fin d) ℂ) :
    (blockOne M)ᴴ = blockOne Mᴴ := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [Matrix.conjTranspose_apply]

/-- **`blockOne` sends unitaries to unitaries.** From the `*`-homomorphism laws:
`(blockOne M)ᴴ · blockOne M = blockOne (Mᴴ · M) = blockOne 1 = 1`. -/
theorem blockOne_mem_unitaryGroup {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    blockOne M ∈ Matrix.unitaryGroup (Fin (d + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hM ⊢
  rw [Matrix.star_eq_conjTranspose] at hM ⊢
  rw [blockOne_conjTranspose, blockOne_mul, hM, blockOne_one]

/-- **`blockOne` sends two-level unitaries to two-level unitaries**, with the distinguished block
`{p, q}` shifted to `{p.succ, q.succ}`. This is what lets the §4.5.1 inductive step re-assemble the
`d`-dimensional decomposition into two-level factors on the `(d+1)`-dimensional space. -/
theorem isTwoLevelUnitary_blockOne {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : IsTwoLevelUnitary M) : IsTwoLevelUnitary (blockOne M) := by
  obtain ⟨hunit, p, q, hpq⟩ := hM
  refine ⟨blockOne_mem_unitaryGroup hunit, p.succ, q.succ, ?_⟩
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp
    | succ j => simp [(Fin.succ_ne_zero j).symm]
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [Fin.succ_ne_zero i]
    | succ j =>
      rw [blockOne_succ_succ, hpq i j (by simpa only [ne_eq, Fin.succ_inj] using hij)]
      simp [Matrix.one_apply, Fin.succ_inj]

end AxQM.Concrete
