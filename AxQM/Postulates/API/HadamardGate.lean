/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Evolution
import AxQM.Postulates.API.Qubit
import AxQM.Concrete.Hadamard

/-!
# AxQM.Postulates.API — the Hadamard gate as a qubit evolution

Nielsen & Chuang's Hadamard gate as an evolution of the qubit.

* `hadamardGate` — the **evolution** `H` on the qubit (Postulate 2 / `Evolution`), obtained by
  promoting the concrete complex Hadamard matrix `Concrete.hadamardC` to a continuous linear
  operator via the C\*-algebra isomorphism `Matrix.toEuclideanCLM`. Its `unitary` field — the
  proof obligation bundled into `Evolution` — is exactly **Nielsen & Chuang, Exercise 2.51**
  (`H` is unitary): constructing `hadamardGate` *is* the verification that `H` is a legitimate
  closed-system evolution. The statement of Exercise 2.51 is in `AxQM/NC/Ch2/Exercise2_51.lean`.
* `hadamardGate_op` — a `simp` bridge exposing the underlying operator
  `hadamardGate.op = Matrix.toEuclideanCLM Concrete.hadamardC`, for operator
  computations (e.g. the Hadamard involution `H² = I` of Exercise 2.52 and the eigenvector
  analysis of Exercise 2.53).
* `hadamardGate_inner_qubitBasis` — the **computational-basis matrix element** `⟪|i⟩, H|j⟩⟫ = Hᵢⱼ`,
  the single-qubit companion of `pauliXObservable_inner_qubitBasis`
  (`AxQM/Postulates/API/Qubit.lean`); the input to the two-qubit gate matrices of Exercise 4.16.

## Design notes

* **Unitarity.** "The Hadamard gate is unitary" is carried by the structure
  `Evolution`: a value of type `Evolution qubit` cannot be formed without discharging
  `op ∈ unitary (…)`. We supply that from the matrix-level fact
  `Concrete.hadamardC_mem_unitaryGroup` (Ex 2.51 as a `Matrix.unitaryGroup` membership),
  transported through `Matrix.toEuclideanCLM` by `Unitary.map_mem`: a `⋆`-monoid homomorphism
  maps unitaries to unitaries, so the operator inherits unitarity from the matrix with no
  operator-level entrywise computation.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **Hadamard gate** `H` as a closed-system evolution of the qubit (Nielsen & Chuang,
Postulate 2 and eq. 2.85). Its operator is the concrete complex Hadamard matrix
`Concrete.hadamardC` promoted to a continuous linear map through the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM`; unitarity — the `Evolution` proof obligation, and the content of
**Exercise 2.51** — is transported from `Concrete.hadamardC_mem_unitaryGroup`. -/
def hadamardGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
      Concrete.hadamardC_mem_unitaryGroup

/-- The underlying operator of `hadamardGate` is the `Matrix.toEuclideanCLM` image of the concrete
complex Hadamard matrix `Concrete.hadamardC`. A `simp` lemma exposing the operator for
operator computations (the involution `H² = I` and the eigenvector analysis of Exercises 2.52,
2.53). -/
@[simp]
theorem hadamardGate_op :
    hadamardGate.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC :=
  rfl

/-- **Matrix element of the Hadamard gate in the computational basis:** `⟪|i⟩, H|j⟩⟫ = Hᵢⱼ`. The
inner product `⟨i|H|j⟩` is the `(i, j)` entry of the concrete complex Hadamard matrix
`Concrete.hadamardC`, read off through the matrix-to-operator bridge `Matrix.toEuclideanCLM`. The
single-qubit companion of `hadamardGate_op` (mirroring the Pauli-`X` matrix element
`pauliXObservable_inner_qubitBasis` of `AxQM/Postulates/API/Qubit.lean`); the input to the
two-qubit gate matrices of Exercise 4.16 (`AxQM/Postulates/API/TwoQubitGateMatrix.lean`). -/
theorem hadamardGate_inner_qubitBasis (i j : Fin 2) :
    inner ℂ (qubitBasis i).vec (hadamardGate.op (qubitBasis j).vec) = Concrete.hadamardC i j := by
  rw [hadamardGate_op]
  change inner ℂ (EuclideanSpace.single i (1 : ℂ))
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC)
        (EuclideanSpace.single j 1)) = _
  rw [EuclideanSpace.inner_single_left, Matrix.ofLp_toEuclideanCLM]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mulVec, dotProduct, Concrete.hadamardC]

end AxQM
