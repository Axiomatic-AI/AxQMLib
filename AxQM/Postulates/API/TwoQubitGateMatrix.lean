/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardGate
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.Composite
import AxQM.Concrete.HadamardKronecker

/-!
# AxQM.Postulates.API — the computational-basis matrix of a two-qubit gate (N&C Ex 4.16)

Nielsen & Chuang's Exercise 4.16: the `4 × 4` matrix, in the
computational basis, of a gate acting on a two-qubit register `qubit ⊗ qubit`, and — the
exercise's answer — the matrices of the **Hadamard gate applied to one qubit** of the register:
`H ⊗ I` (Hadamard on the top/first qubit, `hadamardGate.onLeft qubit`) and `I ⊗ H` (Hadamard on
the bottom/second qubit, `hadamardGate.onRight qubit`).

## What this file provides

* `Evolution.twoQubitStdMatrix` — the operator→matrix bridge for an `Evolution` on the two-qubit
  register `qubit ⊗ qubit`: its matrix in the computational **product** basis `{|i⟩ ⊗ |j⟩}` (indexed
  by `Fin 2 × Fin 2`), whose `(i, j)` entry is the matrix element `⟨i|U|j⟩ = ⟪|i⟩, U|j⟩⟫`. This is
  the two-qubit-composite analogue of `Observable.stdMatrix` (`Postulates/API/PauliExpansion.lean`),
  built directly from `⟪·, U·⟫` on the tensor-product orthonormal basis so it needs no
  change-of-basis apparatus on the composite space.
* `Evolution.twoQubitStdMatrix_apply` — the entry formula
  `⟨(i₁,i₂)|U|(j₁,j₂)⟩ = ⟪|i₁⟩⊗|i₂⟩, U(|j₁⟩⊗|j₂⟩)⟫`.
* `Evolution.twoQubitStdMatrix_tmul_apply` — the **tensor factorization**, the physical heart of
  the exercise: for a product gate `U ⊗ V` the matrix element **factorizes** as
  `⟨(i₁,i₂)|U⊗V|(j₁,j₂)⟩ = ⟪|i₁⟩, U|j₁⟩⟫ · ⟪|i₂⟩, V|j₂⟩⟫`. This is *why* a single-qubit gate on one
  wire of a register becomes a Kronecker product with the identity on the other.
* `hadamardOnLeft_twoQubitStdMatrix` / `hadamardOnRight_twoQubitStdMatrix` — **Exercise 4.16**: the
  computational-basis matrices are the Kronecker products `hadamardC ⊗ₖ pauliI` (`H ⊗ I`) and
  `pauliI ⊗ₖ hadamardC` (`I ⊗ H`).
* `hadamardOnLeft_flattenFin4` / `hadamardOnRight_flattenFin4` — the same, flattened to the explicit
  `4 × 4` arrays of N&C's answer (via the concrete `flattenFin4_*` computations), in the big-endian
  basis order `00, 01, 10, 11`.

## Design notes

* **Register model / grounding.** N&C's two-qubit register is the composite system `qubit ⊗ qubit`
  (Postulate 6), and "apply `H` to one qubit" is the product evolution `hadamardGate.onLeft qubit`
  (`= H ⊗ 1`) / `hadamardGate.onRight qubit` (`= 1 ⊗ H`) built from the Hadamard `Evolution`
  (Postulate 5). The gate is an `Evolution`: it cannot be formed without
  discharging unitarity, so its matrix is automatically a **unitary** matrix (the "unitary matrix"
  of the exercise); the matrix-level unitarity of the answers is also recorded directly at the
  concrete level (`Concrete.hadamardC_kronecker_pauliI_mem_unitaryGroup` and its `I ⊗ H` twin).
* **The matrix, not just its action.** The exercise asks for *the matrix*, an inherently
  matrix-level object; `twoQubitStdMatrix` produces a genuine `Matrix (Fin 2 × Fin 2) …`, and the
  theorems are honest matrix equalities (proved entrywise from the factorization), so the answer is
  the array N&C writes, not merely the gate's action on basis states.
* **The `⟪·, U·⟫`-on-a-basis definition.** For an orthonormal basis, the `(i, j)` matrix entry *is*
  `⟪bᵢ, U bⱼ⟫`; defining `twoQubitStdMatrix` this way (rather than via
  `LinearMap.toMatrixOrthonormal` on the composite space, whose `qubit.space ⊗ qubit.space` head
  does not present as an `EuclideanSpace`) keeps every proof at the raw tensor head where
  `TensorProduct.mapL_tmul` and `TensorProduct.inner_tmul` fire, matching the `change`-to-raw-head
  style of `ControlledUnitary`.

The statement of Exercise 4.16 is in `AxQM/NC/Ch4/Exercise4_16.lean`.
-/

open scoped InnerProductSpace TensorProduct Kronecker

open Matrix AxQM.Concrete

noncomputable section

namespace AxQM

/-- The **computational-basis matrix** of an evolution on the two-qubit register `qubit ⊗ qubit`:
the matrix in the product basis `{|i⟩ ⊗ |j⟩}` (indexed by `Fin 2 × Fin 2`), whose `(i, j)` entry is
the matrix element `⟨i|U|j⟩ = ⟪|i⟩, U|j⟩⟫`. The two-qubit-composite operator→matrix bridge, the
analogue of `Observable.stdMatrix`; its entry formula is `twoQubitStdMatrix_apply`. -/
def Evolution.twoQubitStdMatrix (U : Evolution (qubit ⊗ qubit)) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j => inner ℂ (qubitBasis i.1 ⊗ qubitBasis i.2).vec
    (U.op (qubitBasis j.1 ⊗ qubitBasis j.2).vec)

/-- **Entry formula for the two-qubit computational-basis matrix**: the `(i, j)` entry of
`U.twoQubitStdMatrix` is the matrix element `⟪|i₁⟩⊗|i₂⟩, U(|j₁⟩⊗|j₂⟩)⟫` of `U.op` between the
computational-basis product states. -/
@[simp]
theorem Evolution.twoQubitStdMatrix_apply (U : Evolution (qubit ⊗ qubit)) (i j : Fin 2 × Fin 2) :
    U.twoQubitStdMatrix i j = inner ℂ (qubitBasis i.1 ⊗ qubitBasis i.2).vec
      (U.op (qubitBasis j.1 ⊗ qubitBasis j.2).vec) := rfl

/-- **Tensor factorization of a product-gate matrix element** — the physical content of a gate
acting on one qubit of a register. For a product evolution `U ⊗ V` on `qubit ⊗ qubit`, its
computational-basis matrix element factorizes into the single-qubit matrix elements:
`⟪|i₁⟩⊗|i₂⟩, (U⊗V)(|j₁⟩⊗|j₂⟩)⟫ = ⟪|i₁⟩, U|j₁⟩⟫ · ⟪|i₂⟩, V|j₂⟩⟫` (`TensorProduct.inner_tmul` applied
to `(U⊗V)(x⊗y) = Ux ⊗ Vy`). Specialising `V = 1` (or `U = 1`) turns a single-qubit gate on one wire
into a Kronecker product with the identity on the other. -/
theorem Evolution.twoQubitStdMatrix_tmul_apply (U V : Evolution qubit) (i j : Fin 2 × Fin 2) :
    (U.tmul V).twoQubitStdMatrix i j
      = inner ℂ (qubitBasis i.1).vec (U.op (qubitBasis j.1).vec)
        * inner ℂ (qubitBasis i.2).vec (V.op (qubitBasis j.2).vec) := by
  rw [Evolution.twoQubitStdMatrix_apply, Evolution.tmul_op, PureState.tmul_vec, PureState.tmul_vec]
  change inner ℂ ((qubitBasis i.1).vec ⊗ₜ[ℂ] (qubitBasis i.2).vec)
      (U.op (qubitBasis j.1).vec ⊗ₜ[ℂ] V.op (qubitBasis j.2).vec) = _
  rw [TensorProduct.inner_tmul]

/-- **Nielsen & Chuang, Exercise 4.16 (first circuit).** The computational-basis matrix of the
Hadamard gate applied to the **top (first) qubit** of a two-qubit register,
`hadamardGate.onLeft qubit = H ⊗ 1`, is the Kronecker product `hadamardC ⊗ₖ pauliI` (`H ⊗ I`).
Proved entrywise from the factorization `twoQubitStdMatrix_tmul_apply`: the first factor is the
Hadamard matrix element `Hᵢⱼ` (`hadamardGate_inner_qubitBasis`), the second is `⟨i₂|j₂⟩ = Iᵢ₂ⱼ₂`. -/
theorem hadamardOnLeft_twoQubitStdMatrix :
    (hadamardGate.onLeft qubit).twoQubitStdMatrix = hadamardC ⊗ₖ pauliI := by
  ext i j
  rw [Evolution.onLeft, Evolution.twoQubitStdMatrix_tmul_apply, hadamardGate_inner_qubitBasis,
      Evolution.id_op, one_apply_eq_self, qubitBasis_inner_qubitBasis,
      Matrix.kroneckerMap_apply, pauliI, Matrix.one_apply]

/-- **Nielsen & Chuang, Exercise 4.16 (second circuit).** The computational-basis matrix of the
Hadamard gate applied to the **bottom (second) qubit** of a two-qubit register,
`hadamardGate.onRight qubit = 1 ⊗ H`, is the Kronecker product `pauliI ⊗ₖ hadamardC` (`I ⊗ H`).
Proved entrywise from `twoQubitStdMatrix_tmul_apply`: the first factor is `⟨i₁|j₁⟩ = Iᵢ₁ⱼ₁`, the
second is the Hadamard matrix element `Hᵢ₂ⱼ₂` (`hadamardGate_inner_qubitBasis`). -/
theorem hadamardOnRight_twoQubitStdMatrix :
    (hadamardGate.onRight qubit).twoQubitStdMatrix = pauliI ⊗ₖ hadamardC := by
  ext i j
  rw [Evolution.onRight, Evolution.twoQubitStdMatrix_tmul_apply, hadamardGate_inner_qubitBasis,
      Evolution.id_op, one_apply_eq_self, qubitBasis_inner_qubitBasis,
      Matrix.kroneckerMap_apply, pauliI, Matrix.one_apply]

/-- **Nielsen & Chuang, Exercise 4.16 (first circuit), explicit `4 × 4` matrix.** In the big-endian
computational basis `00, 01, 10, 11`, the Hadamard gate on the top qubit of a two-qubit register
has matrix `(1/√2) !![1,0,1,0; 0,1,0,1; 1,0,-1,0; 0,1,0,-1]` — the flattening of `H ⊗ I`
(`Concrete.flattenFin4_hadamardC_kronecker_pauliI`). -/
theorem hadamardOnLeft_flattenFin4 :
    flattenFin4 (hadamardGate.onLeft qubit).twoQubitStdMatrix
      = (Real.sqrt 2 : ℂ)⁻¹ • !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] := by
  rw [hadamardOnLeft_twoQubitStdMatrix, flattenFin4_hadamardC_kronecker_pauliI]

/-- **Nielsen & Chuang, Exercise 4.16 (second circuit), explicit `4 × 4` matrix.** In the
big-endian computational basis `00, 01, 10, 11`, the Hadamard gate on the bottom qubit of a
two-qubit register has matrix `(1/√2) !![1,1,0,0; 1,-1,0,0; 0,0,1,1; 0,0,1,-1]` — the flattening of
`I ⊗ H` (`Concrete.flattenFin4_pauliI_kronecker_hadamardC`). -/
theorem hadamardOnRight_flattenFin4 :
    flattenFin4 (hadamardGate.onRight qubit).twoQubitStdMatrix
      = (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1] := by
  rw [hadamardOnRight_twoQubitStdMatrix, flattenFin4_pauliI_kronecker_hadamardC]

end AxQM
