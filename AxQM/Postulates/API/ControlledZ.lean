/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.HadamardGate
import AxQM.Concrete.HadamardPauliConjugation

/-!
# AxQM.Postulates.API — the controlled-`Z` gate

Nielsen & Chuang's controlled-`Z` (controlled-phase) gate (N&C §4.3), plus the gate-level
Hadamard–Pauli conjugation identity used to relate it to `CNOT`. It is defined alongside `cnotGate`
and reused throughout Chapter 4 (Exercises 4.17, 4.18, 4.19, 4.20).

## What is formalised

* `controlledZGate = controlledUnitary pauliZGate` — the **controlled-`Z`** gate on `qubit ⊗ qubit`
  (N&C's `diag(1, 1, 1, -1)`): the `Evolution` `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z` that applies the phase
  flip `Z` to the target exactly when the control qubit is `|1⟩`. As a `controlledUnitary` instance
  it inherits the defining action lemmas (`controlledUnitary_evolvePure_ketZero` / `_ketOne`).
* `controlledZGate_op` — its operator form `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z`.
* `hadamardGate_comp_pauliZGate_comp_hadamardGate` — the **gate-level circuit identity `H Z H = X`**
  (N&C Exercise 4.13, eq. 4.18) at the level of the `Evolution` gates: `H · Z · H = X` in the gate
  monoid. This is the fact that makes conjugating a controlled-`Z`'s target by Hadamards produce a
  `CNOT`.

## Design notes

* **N&C fidelity.** The controlled-`Z` gate is, by definition, "apply `Z` to the target iff the
  control is `|1⟩`" — exactly `controlledUnitary pauliZGate`, whose operator is the block-diagonal
  `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z`. In the computational basis this is N&C's specifying matrix
  `diag(1, 1, 1, -1)` (the only non-identity entry is the `|11⟩` phase from `Z`'s `-1`). Building it
  as a `controlledUnitary` instance (rather than a bespoke `4 × 4` matrix) makes it an `Evolution`
  and immediately reuses the controlled-`U` action lemmas.
* **Gate-level `H Z H = X`.** The matrix identity `Concrete.hadamardC_mul_pauliZ_mul_hadamardC`
  (Exercise 4.13, in `Concrete/`) is here lifted to the gate `Evolution`s by reducing
  (`Evolution.ext`) to the operator identity `H.op ∘ Z.op ∘ H.op = X.op` and transporting it across
  the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` (`map_mul`). This is the physics reading of
  Exercise 4.13 needed for the controlled-gate construction, complementing the raw matrix version.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The controlled-`Z` gate** on two qubits (Nielsen & Chuang §4.3), the controlled-`U` gate with
`U = Z`: it applies the phase flip `Z` to the target qubit exactly when the control qubit is `|1⟩`.
Its operator `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z` is N&C's specifying matrix `diag(1, 1, 1, -1)` in the
computational basis. -/
def controlledZGate : Evolution (qubit ⊗ qubit) := controlledUnitary pauliZGate

/-- The underlying operator of `controlledZGate` is `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ Z`. -/
@[simp]
theorem controlledZGate_op :
    controlledZGate.op
      = TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec) 1
        + TensorProduct.mapL (InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec)
            pauliZGate.op := rfl

/-- **Gate-level circuit identity `H Z H = X`** (Nielsen & Chuang, Exercise 4.13, eq. 4.18), at the
level of the `Evolution` gates: `hadamardGate · pauliZGate · hadamardGate = pauliXGate`. Reducing
(`Evolution.ext`) to the operator identity `H.op ∘ Z.op ∘ H.op = X.op` and transporting the matrix
identity `Concrete.hadamardC_mul_pauliZ_mul_hadamardC` across the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM` (`map_mul`) closes it. This is the fact that turns a controlled-`Z` into a
`CNOT` when the target is conjugated by Hadamards (Exercise 4.17). -/
theorem hadamardGate_comp_pauliZGate_comp_hadamardGate :
    hadamardGate.comp (pauliZGate.comp hadamardGate) = pauliXGate := by
  apply Evolution.ext
  -- All three gate operators are `Matrix.toEuclideanCLM` of the corresponding concrete matrix
  -- (defeq via `hadamardGate_op` / `pauliZGate` / `pauliXGate` definitions); transport the product.
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC).comp
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ).comp
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC))
    = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul, ← map_mul,
    ← mul_assoc, Concrete.hadamardC_mul_pauliZ_mul_hadamardC]

/-- **Gate-level circuit identity `H Z = X H`** — the two-factor commuted form of
`hadamardGate_comp_pauliZGate_comp_hadamardGate` (`H Z H = X`):
`hadamardGate.comp pauliZGate = pauliXGate.comp hadamardGate` in the gate monoid.  Equivalent to
`H Z H = X` together with the Hadamard involution `H² = 1`; proved by reducing (`Evolution.ext`) to
the concrete matrix identity `hadamardC * pauliZ = pauliX * hadamardC` (from
`Concrete.hadamardC_mul_pauliZ_mul_hadamardC` and `Concrete.hadamardC_mul_self`) and transporting it
across the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`.  This is the rule that pushes a decoding
`Hadamard` past a `Z` error (e.g. in the fault-tolerant measurement of N&C Exercise 10.70, turning a
`Z` on the ancilla into an `X` on the readout after the decoding `Hadamard`). -/
theorem hadamardGate_comp_pauliZGate :
    hadamardGate.comp pauliZGate = pauliXGate.comp hadamardGate := by
  apply Evolution.ext
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC).comp
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliZ)
    = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX).comp
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.hadamardC)
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul, ← map_mul]
  congr 1
  rw [← Concrete.hadamardC_mul_pauliZ_mul_hadamardC, mul_assoc, Concrete.hadamardC_mul_self,
    mul_one]

/-- **A `Z` error on the control commutes with a controlled gate.**  For every target gate `U`,
`C(U) · (Z ⊗ 1) = (Z ⊗ 1) · C(U)` on `qubit ⊗ S`, where `Z ⊗ 1 = pauliZGate.onLeft S` acts on the
control qubit.  No commutativity hypothesis on `U` is needed: `Z = |0⟩⟨0| - |1⟩⟨1|` is diagonal in
the control basis and `C(U) = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U` is block-diagonal there, so both products are
`|0⟩⟨0| ⊗ 1 - |1⟩⟨1| ⊗ U`.  The general controlled-gate∘Pauli-`Z` propagation fact (sibling of the
`CNOT`/`Toffoli` propagation rules); it is why a `Z` error on the measurement ancilla of N&C
Exercise 10.70 slides through the controlled-`M′` interaction and never acts on the encoded data.
Proved by cracking to `.op` (`controlledUnitary_op` + `TensorProduct.mapL` algebra), the
projector–`Z` commutations `|i⟩⟨i| · Z = Z · |i⟩⟨i|` coming from `rankOne_comp`/`comp_rankOne`,
Pauli-`Z` self-adjointness (`Concrete.pauliZ_isHermitian` mapped through `Matrix.toEuclideanCLM`),
and `pauliZGate_op_apply_qubitBasis`. -/
theorem controlledUnitary_comm_pauliZGate_onLeft {S : QSystem} (U : Evolution S) :
    (controlledUnitary U).comp (pauliZGate.onLeft S)
      = (pauliZGate.onLeft S).comp (controlledUnitary U) := by
  have hSA : IsSelfAdjoint pauliZGate.op := by
    have hM : IsSelfAdjoint Concrete.pauliZ := Concrete.pauliZ_isHermitian
    rw [pauliZGate_op]; exact hM.map Matrix.toEuclideanCLM
  have hadj : ContinuousLinearMap.adjoint pauliZGate.op = pauliZGate.op := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hSA
  set p0 := InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec with hp0
  set p1 := InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec with hp1
  have hz0 : p0.comp pauliZGate.op = pauliZGate.op.comp p0 := by
    rw [hp0, InnerProductSpace.rankOne_comp, InnerProductSpace.comp_rankOne, hadj,
      pauliZGate_op_apply_qubitBasis]
    simp only [Fin.val_zero, pow_zero, one_smul]
  have hz1 : p1.comp pauliZGate.op = pauliZGate.op.comp p1 := by
    rw [hp1, InnerProductSpace.rankOne_comp, InnerProductSpace.comp_rankOne, hadj,
      pauliZGate_op_apply_qubitBasis]
    rw [map_smulₛₗ, map_smul, _root_.smul_apply]; norm_num
  apply Evolution.ext
  change (TensorProduct.mapL p0 (1 : S.space →L[ℂ] S.space) + TensorProduct.mapL p1 U.op).comp
      (TensorProduct.mapL pauliZGate.op 1)
    = (TensorProduct.mapL pauliZGate.op 1).comp
      (TensorProduct.mapL p0 (1 : S.space →L[ℂ] S.space) + TensorProduct.mapL p1 U.op)
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp,
    ← TensorProduct.mapL_comp]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp,
    hz0, hz1]

end AxQM
