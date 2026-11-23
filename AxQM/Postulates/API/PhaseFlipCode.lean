/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.QubitThree
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Postulates.API.QuantumErrorCorrection

/-!
# AxQM.Postulates.API — the three-qubit phase-flip code and its QEC conditions

Nielsen & Chuang's **Exercise 10.8** (p. 441) asks to verify that the three-qubit *phase-flip code*
with logical states

  `|0_L⟩ = |+++⟩`,  `|1_L⟩ = |−−−⟩`

satisfies the quantum error-correction conditions (Theorem 10.1, eq. (10.16)) for the error set
`{I, Z₁, Z₂, Z₃}` (identity and a Pauli `Z` on each of the three qubits).

The phase-flip code is the Hadamard-conjugate of the bit-flip code: in the `{|+⟩, |−⟩}` orthonormal
basis of each qubit it looks exactly like the bit-flip code in the computational basis, with the
Pauli `Z` (which sends `|+⟩ ↔ |−⟩`) playing the role of the bit-flip `X`. So the verification is a
computation over the `±`-basis: the eight vectors `Zᵢ|+++⟩` and `Zᵢ|−−−⟩` (`i = 0` meaning no error)
are mutually orthonormal `±`-basis vectors, whence `⟪Eᵢ v_a, Eⱼ v_b⟫ = δᵢⱼ δ_{a,b}` and the QEC
conditions hold with the **identity** coefficient matrix `α = 1` (a Hermitian matrix, as required).

## Contents

* `pmQubit` — the single-qubit `±` orthonormal frame `0 ↦ |+⟩`, `1 ↦ |−⟩`; `pmQubit_orthonormal`
  and `pauliZGate_op_pmQubit` (`Z` flips the `±` label) are its two structural facts.
* `pmThreeVec` — the three-qubit `±`-basis vector `|σ₁σ₂σ₃⟩`; `pmThreeVec_inner` records that these
  eight vectors are orthonormal.
* `phaseFlipErrorGate` / `phaseFlipErrorOp` — the error gates `{I, Z₁, Z₂, Z₃}` as evolutions and as
  operators; `phaseFlipErrorOp_apply` computes their action on the `±` basis as a coordinate flip.
* `phaseFlipCodeword` — the logical codewords `|+++⟩`, `|−−−⟩`; `phaseFlipCodeProj` — the code
  projector `P = |+++⟩⟨+++| + |−−−⟩⟨−−−|`.
* `phaseFlipCode_satisfiesQECConditions` — **Exercise 10.8**: `SatisfiesQECConditions
  phaseFlipCodeProj phaseFlipErrorOp` (the conditions hold with the identity Hermitian matrix).

The statement of Exercise 10.8 is in `AxQM/NC/Ch10/Exercise10_8.lean`. The Knill–Laflamme core
`ContinuousLinearMap.satisfiesKLConditions_of_inner_error_images` (the codeword-basis verification,
reusable for Exercises 10.7/10.9/10.10) is in
`ToMathlib/Analysis/InnerProductSpace/QuantumErrorCorrection.lean`.
-/

open scoped InnerProductSpace TensorProduct Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The single-qubit `±` frame -/

/-- **The Pauli-`Z` gate sends `|+⟩` to `|−⟩`:** `Z|+⟩ = |−⟩`, at operator level. -/
theorem pauliZGate_op_qubitPlus : pauliZGate.op qubitPlus.vec = qubitMinus.vec := by
  rw [pauliZGate_op, qubitPlus_vec, qubitMinus_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ)
        (WithLp.toLp 2 Concrete.xPlus)).ofLp = (WithLp.toLp 2 Concrete.xMinus).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.pauliZ, Concrete.xPlus, Concrete.xMinus, Matrix.mulVec, dotProduct]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **The Pauli-`Z` gate sends `|−⟩` to `|+⟩`:** `Z|−⟩ = |+⟩`, at operator level. -/
theorem pauliZGate_op_qubitMinus : pauliZGate.op qubitMinus.vec = qubitPlus.vec := by
  rw [pauliZGate_op, qubitPlus_vec, qubitMinus_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ)
        (WithLp.toLp 2 Concrete.xMinus)).ofLp = (WithLp.toLp 2 Concrete.xPlus).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.pauliZ, Concrete.xPlus, Concrete.xMinus, Matrix.mulVec, dotProduct]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- `⟨−|−⟩ = 1`: the `|−⟩` state is a unit vector. -/
theorem inner_qubitMinus_self : ⟪qubitMinus.vec, qubitMinus.vec⟫_ℂ = 1 := by
  have := qubitMinus.normalized
  rw [inner_self_eq_norm_sq_to_K, this]; norm_num

/-- `⟨−|+⟩ = 0`: `|−⟩` and `|+⟩` are orthogonal (the conjugate of `inner_qubitPlus_qubitMinus`). -/
theorem inner_qubitMinus_qubitPlus : ⟪qubitMinus.vec, qubitPlus.vec⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_qubitPlus_qubitMinus, map_zero]

/-- **The single-qubit `±` orthonormal frame** `{|+⟩, |−⟩}`, as a family indexed by `Fin 2`
(`0 ↦ |+⟩`, `1 ↦ |−⟩`). This is the Hadamard basis in which the phase-flip code and its `Z`-errors
mirror the bit-flip code and its `X`-errors in the computational basis. -/
def pmQubit : Fin 2 → qubit.space := ![qubitPlus.vec, qubitMinus.vec]

/-- **The `±` frame is orthonormal:** `⟪|±⟩, |±⟩⟫ = δ`. -/
theorem pmQubit_orthonormal : Orthonormal ℂ pmQubit := by
  rw [orthonormal_iff_ite]
  intro s t
  fin_cases s <;> fin_cases t <;>
    simp only [pmQubit, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue, inner_qubitPlus_self, inner_qubitPlus_qubitMinus, inner_qubitMinus_self,
      inner_qubitMinus_qubitPlus, Fin.reduceEq, ite_true, ite_false]

/-- **The Pauli-`Z` gate flips the `±` label:** `Z|σ⟩ = |σ ⊕ 1⟩` (`Z|+⟩ = |−⟩`, `Z|−⟩ = |+⟩`). This
is the exact analogue, in the `±` basis, of the bit-flip `X|i⟩ = |i ⊕ 1⟩` in the computational
basis. -/
theorem pauliZGate_op_pmQubit (s : Fin 2) : pauliZGate.op (pmQubit s) = pmQubit (s + 1) := by
  fin_cases s
  · exact pauliZGate_op_qubitPlus
  · exact pauliZGate_op_qubitMinus

/-! ### The three-qubit `±` basis -/

/-- **The three-qubit `±`-basis vector** `|σ₁σ₂σ₃⟩ = |σ₁⟩ ⊗ (|σ₂⟩ ⊗ |σ₃⟩)` (each `σᵢ` selecting
`|+⟩` or `|−⟩`) of the register `qubit ⊗ (qubit ⊗ qubit)`. The eight such vectors form an
orthonormal basis; the two codewords `|+++⟩`, `|−−−⟩` are the `(0,0,0)` and `(1,1,1)` members. -/
def pmThreeVec (s : Fin 2 × Fin 2 × Fin 2) : (qubit ⊗ (qubit ⊗ qubit)).space :=
  pmQubit s.1 ⊗ₜ[ℂ] (pmQubit s.2.1 ⊗ₜ[ℂ] pmQubit s.2.2)

/-- **The three-qubit `±`-basis vectors are orthonormal:** `⟪|σ⟩, |τ⟩⟫ = δ_{σ,τ}`, from the
multiplicativity of the tensor inner product and orthonormality of the single-qubit `±` frame. -/
theorem pmThreeVec_inner (s t : Fin 2 × Fin 2 × Fin 2) :
    ⟪pmThreeVec s, pmThreeVec t⟫_ℂ = if s = t then 1 else 0 := by
  obtain ⟨s1, s2, s3⟩ := s
  obtain ⟨t1, t2, t3⟩ := t
  change inner ℂ (pmQubit s1 ⊗ₜ[ℂ] (pmQubit s2 ⊗ₜ[ℂ] pmQubit s3))
    (pmQubit t1 ⊗ₜ[ℂ] (pmQubit t2 ⊗ₜ[ℂ] pmQubit t3)) = _
  rw [TensorProduct.inner_tmul, TensorProduct.inner_tmul,
    orthonormal_iff_ite.mp pmQubit_orthonormal, orthonormal_iff_ite.mp pmQubit_orthonormal,
    orthonormal_iff_ite.mp pmQubit_orthonormal]
  by_cases h1 : s1 = t1 <;> by_cases h2 : s2 = t2 <;> by_cases h3 : s3 = t3 <;>
    simp [h1, h2, h3, Prod.ext_iff]

/-! ### The error operators `{I, Z₁, Z₂, Z₃}` -/

/-- **The error gates** `{I, Z₁, Z₂, Z₃}` on the three-qubit register, as evolutions (Postulate 5):
`0 ↦ I`, `1 ↦ Z⊗I⊗I`, `2 ↦ I⊗Z⊗I`, `3 ↦ I⊗I⊗Z`, built from `pauliZGate` and the single-wire
embeddings `Evolution.onLeft` / `Evolution.onRight`. -/
def phaseFlipErrorGate : Fin 4 → Evolution (qubit ⊗ (qubit ⊗ qubit))
  | 0 => Evolution.id
  | 1 => pauliZGate.onLeft (qubit ⊗ qubit)
  | 2 => (pauliZGate.onLeft qubit).onRight qubit
  | 3 => (pauliZGate.onRight qubit).onRight qubit

/-- **The error operators** `{I, Z₁, Z₂, Z₃}` as operators on the register state space — the
operation elements of the noise the phase-flip code protects against (the `.op` of
`phaseFlipErrorGate`). -/
def phaseFlipErrorOp (i : Fin 4) :
    (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ] (qubit ⊗ (qubit ⊗ qubit)).space :=
  (phaseFlipErrorGate i).op

/-- **The coordinate flip induced by each error on the `±`-basis index:** `I` fixes the index,
`Zₖ` flips the `k`-th `±` label. The combinatorial shadow of `phaseFlipErrorOp_apply`. -/
def phaseFlipFlip : Fin 4 → (Fin 2 × Fin 2 × Fin 2) → (Fin 2 × Fin 2 × Fin 2)
  | 0, s => s
  | 1, (a, b, c) => (a + 1, b, c)
  | 2, (a, b, c) => (a, b + 1, c)
  | 3, (a, b, c) => (a, b, c + 1)

/-- **The errors permute the `±` basis:** `Eᵢ |σ⟩ = |phaseFlipFlip i σ⟩`. Each `Zₖ` flips the `k`-th
`±` label (because `Z|+⟩ = |−⟩`, `Z|−⟩ = |+⟩`), and `I` fixes the state. -/
theorem phaseFlipErrorOp_apply (i : Fin 4) (s : Fin 2 × Fin 2 × Fin 2) :
    phaseFlipErrorOp i (pmThreeVec s) = pmThreeVec (phaseFlipFlip i s) := by
  obtain ⟨a, b, c⟩ := s
  fin_cases i
  · change (Evolution.id : Evolution (qubit ⊗ (qubit ⊗ qubit))).op (pmThreeVec (a, b, c))
      = pmThreeVec (a, b, c)
    rw [Evolution.id_op, one_apply_eq_self]
  · change (pauliZGate.onLeft (qubit ⊗ qubit)).op (pmThreeVec (a, b, c))
      = pmThreeVec (a + 1, b, c)
    rw [pmThreeVec]
    have h := Evolution.onLeft_op_tmul pauliZGate (qubit ⊗ qubit) (pmQubit a)
      (pmQubit b ⊗ₜ[ℂ] pmQubit c)
    rw [h, pauliZGate_op_pmQubit]
    rfl
  · change ((pauliZGate.onLeft qubit).onRight qubit).op (pmThreeVec (a, b, c))
      = pmThreeVec (a, b + 1, c)
    rw [pmThreeVec]
    have h := Evolution.onRight_op_tmul (pauliZGate.onLeft qubit) qubit (pmQubit a)
      (pmQubit b ⊗ₜ[ℂ] pmQubit c)
    rw [h, Evolution.onLeft_op_tmul, pauliZGate_op_pmQubit]
    rfl
  · change ((pauliZGate.onRight qubit).onRight qubit).op (pmThreeVec (a, b, c))
      = pmThreeVec (a, b, c + 1)
    rw [pmThreeVec]
    have h := Evolution.onRight_op_tmul (pauliZGate.onRight qubit) qubit (pmQubit a)
      (pmQubit b ⊗ₜ[ℂ] pmQubit c)
    rw [h]
    have h2 := Evolution.onRight_op_tmul pauliZGate qubit (pmQubit b) (pmQubit c)
    rw [h2, pauliZGate_op_pmQubit]
    rfl

/-! ### The code and the QEC conditions -/

/-- **The logical codewords of the three-qubit phase-flip code:** `|0_L⟩ = |+++⟩` (`a = 0`) and
`|1_L⟩ = |−−−⟩` (`a = 1`). -/
def phaseFlipCodeword (a : Fin 2) : (qubit ⊗ (qubit ⊗ qubit)).space := pmThreeVec (a, a, a)

/-- **The code projector** `P = |+++⟩⟨+++| + |−−−⟩⟨−−−|` onto the phase-flip code space. -/
def phaseFlipCodeProj : (qubit ⊗ (qubit ⊗ qubit)).space →L[ℂ] (qubit ⊗ (qubit ⊗ qubit)).space :=
  ∑ a, InnerProductSpace.rankOne ℂ (phaseFlipCodeword a) (phaseFlipCodeword a)

/-- **The codeword matrix elements of the errors:** `⟪Eᵢ v_a, Eⱼ v_b⟫ = δᵢⱼ δ_{a,b}`, i.e. the
identity coefficient matrix. Each `Eᵢ v_a` is a `±`-basis vector (a single flip of the codeword
`|σσσ⟩`), and the eight such vectors — `{|+++⟩, |−++⟩, |+−+⟩, |++−⟩}` (weight `≤ 1`) for the `|+++⟩`
codeword and their bit-complements for `|−−−⟩` — are mutually orthonormal, so the overlap is `1`
exactly when `(i, a) = (j, b)`. -/
theorem phaseFlipError_inner_codeword (i j : Fin 4) (a b : Fin 2) :
    ⟪phaseFlipErrorOp i (phaseFlipCodeword a), phaseFlipErrorOp j (phaseFlipCodeword b)⟫_ℂ
      = (1 : Matrix (Fin 4) (Fin 4) ℂ) i j * (if a = b then 1 else 0) := by
  simp only [phaseFlipCodeword, phaseFlipErrorOp_apply, pmThreeVec_inner, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [phaseFlipFlip, Prod.ext_iff]

/-- **Nielsen & Chuang, Exercise 10.8.** The three-qubit phase-flip code
(`|0_L⟩ = |+++⟩`, `|1_L⟩ = |−−−⟩`) satisfies the quantum error-correction conditions (Theorem 10.1)
for the error set `{I, Z₁, Z₂, Z₃}`: the code projector `phaseFlipCodeProj` and error operators
`phaseFlipErrorOp` satisfy `SatisfiesQECConditions` with the **identity** Hermitian coefficient
matrix `α = 1` (`P Eᵢ† Eⱼ P = δᵢⱼ P`). Hence `{I, Z₁, Z₂, Z₃}` is a correctable set. -/
theorem phaseFlipCode_satisfiesQECConditions :
    SatisfiesQECConditions phaseFlipCodeProj phaseFlipErrorOp :=
  ⟨1, Matrix.isHermitian_one,
    ContinuousLinearMap.satisfiesKLConditions_of_inner_error_images
      phaseFlipCodeword phaseFlipErrorOp 1 phaseFlipError_inner_codeword⟩

end AxQM
