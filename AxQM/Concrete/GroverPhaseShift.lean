/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelLowerBound

/-!
# Concrete: the Grover conditional phase shift `2|0⟩⟨0| − I` (N&C Exercise 6.1)

Nielsen & Chuang, §6.1.2, eq. (6.5) (p. 250–251): step (3) of the Grover iteration performs a
**conditional phase shift** on the `n`-qubit register, with every computational basis state except
`|0⟩` receiving a phase of `−1`,
`|x⟩ ↦ -(-1)^{δ_{x0}} |x⟩`
(so `|0⟩` is fixed and every other basis state is negated). **Exercise 6.1** asks to show that the
unitary operator realising this phase shift is `2|0⟩⟨0| − I`.

This file supplies that operator and the exercise's identity, for an arbitrary register dimension
`N = d + 1` (indices `Fin (d + 1)`; the claim holds for every `N ≥ 1`, not only for powers of
two):

* `groverPhaseShift` — the operator of (6.5), the diagonal matrix `diag(1, −1, …, −1)`.
* `groverPhaseShift_mulVec_stdVec` — its action `|x⟩ ↦ -(-1)^{δ_{x0}} |x⟩`, verbatim (6.5), which
  is why this matrix *is* the phase shift.
* `groverPhaseShift_eq_two_ketBraZero_sub_one` — **Exercise 6.1**: `groverPhaseShift = 2|0⟩⟨0| − I`,
  with `|0⟩⟨0|` the outer product `vecMulVec |0⟩ ⟨0|` of the computational basis vector with its
  conjugate transpose.
* `groverPhaseShift_mem_unitaryGroup` — it is indeed a *unitary* operator (a real `±1` diagonal, so
  a Hermitian involution).

The statement of Exercise 6.1 is in `AxQM/NC/Ch6/Exercise6_1.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **The Grover conditional phase shift** (Nielsen & Chuang eq. (6.5)): the `(d+1) × (d+1)`
operator that fixes `|0⟩` and negates every other computational basis state, i.e. the diagonal
matrix `diag(1, −1, …, −1)`. Applied to `|x⟩` it multiplies by `-(-1)^{δ_{x0}}`
(`groverPhaseShift_mulVec_stdVec`), and Exercise 6.1 identifies it with `2|0⟩⟨0| − I`
(`groverPhaseShift_eq_two_ketBraZero_sub_one`). -/
def groverPhaseShift (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal fun x => if x = 0 then 1 else -1

/-- The `(0, 0)` entry of the Grover phase shift is `1`: the basis state `|0⟩` is fixed. -/
@[simp] theorem groverPhaseShift_apply_zero_zero :
    groverPhaseShift d 0 0 = 1 := by
  simp [groverPhaseShift, Matrix.diagonal_apply_eq]

/-- **N&C eq. (6.5): the Grover phase shift acts as `|x⟩ ↦ -(-1)^{δ_{x0}} |x⟩`.** Applied to the
computational basis vector `|x⟩`, `groverPhaseShift` multiplies it by the scalar `-(-1)^{δ_{x0}}`,
which is `1` at `x = 0` and `−1` otherwise — fixing `|0⟩` and negating every other basis state.
This is the defining action of the conditional phase shift, so `groverPhaseShift` really is the
operator the exercise refers to. -/
theorem groverPhaseShift_mulVec_stdVec (x : Fin (d + 1)) :
    (groverPhaseShift d).mulVec (stdVec x)
      = -((-1 : ℂ) ^ (if x = 0 then 1 else 0 : ℕ)) • stdVec x := by
  rw [groverPhaseShift, stdVec, Matrix.diagonal_mulVec_single, mul_one]
  funext k
  rcases eq_or_ne k x with rfl | hk
  · simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one]
    split_ifs <;> norm_num
  · simp only [Pi.single_eq_of_ne hk, Pi.smul_apply, smul_eq_mul, mul_zero]

/-- **Nielsen & Chuang, Exercise 6.1.** The Grover conditional phase shift equals `2|0⟩⟨0| − I`,
where `|0⟩⟨0| = vecMulVec |0⟩ ⟨0|` is the rank-one projector onto the computational basis state
`|0⟩` (the outer product of `|0⟩ = stdVec 0` with its conjugate transpose `⟨0| = star (stdVec 0)`).
Both sides are the diagonal matrix `diag(1, −1, …, −1)`: on the `(0,0)` corner `2 · 1 − 1 = 1`, on
the rest of the diagonal `2 · 0 − 1 = −1`, and off the diagonal `0`. -/
theorem groverPhaseShift_eq_two_ketBraZero_sub_one :
    groverPhaseShift d
      = (2 : ℂ) • Matrix.vecMulVec (stdVec 0) (star (stdVec 0)) - 1 := by
  ext i j
  simp only [groverPhaseShift, Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Matrix.one_apply, stdVec, Pi.single_apply, Pi.star_apply, smul_eq_mul]
  split_ifs <;> norm_num <;> simp_all

/-- **The Grover phase shift is a unitary matrix.** It is the real diagonal `diag(1, −1, …, −1)`,
whose entries all have unit modulus, so `star U * U = 1`; equivalently it is a Hermitian
involution. -/
theorem groverPhaseShift_mem_unitaryGroup :
    groverPhaseShift d ∈ Matrix.unitaryGroup (Fin (d + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', groverPhaseShift, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs with h <;> simp

end AxQM.Concrete
