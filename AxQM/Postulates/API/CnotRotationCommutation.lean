/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateCommute
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Postulates.API.PiEighthGate
import AxQM.Postulates.API.HadamardRotation

/-!
# AxQM.Postulates.API — CNOT commutes with rotations on the untouched axis

The **rotation-commutation** companions of `AxQM/Postulates/API/CnotPauliPropagation.lean`
(which handles how the discrete Pauli gates propagate through `CNOT`): the two
continuous-rotation identities needed to complete Nielsen & Chuang **Exercise 4.31**,
eqs. (4.38)–(4.39), in
`AxQM/NC/Ch4/Exercise4_31.lean`.

Where a Pauli *conjugation* rewrites `CNOT · P · CNOT` to a new Pauli, a rotation on the axis that
`CNOT` leaves invariant simply **commutes** with `CNOT`:

* `cnotGate_comp_rotZGate_onLeft` — a `z`-rotation on the **control** commutes with `CNOT`:
  `CNOT · (R_z(θ) ⊗ 1) = (R_z(θ) ⊗ 1) · CNOT`.  `CNOT` acts on the control only through the
  computational-basis label `|c⟩`, which `R_z(θ)` merely rephases (`R_z(θ)|c⟩ = e_c |c⟩`); the
  control label — hence the whole `CNOT` action — is untouched.
* `cnotGate_comp_rotXGate_onRight` — an `x`-rotation on the **target** commutes with `CNOT`:
  `CNOT · (1 ⊗ R_x(θ)) = (1 ⊗ R_x(θ)) · CNOT`.  `CNOT` acts on the target by the Pauli `X`, and
  `R_x(θ)` is a function of `X`, so the two commute on the target factor; the general
  `controlledUnitary_comm_onRight` (from `Postulates/API/GateCommute.lean`) then lifts that to the
  controlled gate.

## Supporting lemmas

* `rotZGate_op_apply_qubitBasis` — the **eigen-action of `R_z(θ)` on the computational basis**:
  `R_z(θ)|c⟩ = (R_z(θ))_{cc} |c⟩` (the `c`-th diagonal entry of the diagonal `Concrete.rotZ`).
  The workhorse that lets the phase `e_c` slide through `CNOT`, exactly as
  `pauliZGate_op_apply_qubitBasis` does for the `Z` gate in `CnotPauliPropagation.lean`.
* `pauliXGate_comp_rotXGate` — **`X` commutes with `R_x(θ)`** as single-qubit gates
  (`X · R_x(θ) = R_x(θ) · X`), the hypothesis `controlledUnitary_comm_onRight` needs.  A concrete
  `2×2` matrix commutation (`Concrete.pauliX` with `Concrete.rotX θ`) pulled through the `⋆`-algebra
  isomorphism `Matrix.toEuclideanCLM`.

## Design notes

* **Statement shape (fidelity).**  Each commutation rule is a genuine equality of the gate
  `Evolution`s (Postulate 5), holding on every input, in the form `CNOT · R = R · CNOT` — the same
  commutation shape as the Pauli propagation rules, so `AxQM/NC/Ch4/Exercise4_31.lean` reads
  the identities off directly (with `.symm`, matching N&C's `R·C = C·R` orientation).
* **Relation to the Pauli rules.**  These are the continuous rotations commuting through `CNOT`,
  as opposed to the discrete Paulis being conjugated in `CnotPauliPropagation.lean` and
  `CnotPauliYPropagation.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Eigen-action of the `z`-rotation gate on the computational basis:**
`R_z(θ)|c⟩ = (R_z(θ))_{cc} |c⟩`, i.e. `(rotZGate θ).op` sends `|c⟩` to the `c`-th diagonal entry of
the (diagonal) matrix `Concrete.rotZ θ` times `|c⟩`.  `R_z(θ) = exp(-iθZ/2)` is diagonal in the
computational basis, so every `|c⟩` is an eigenvector; the eigenvalue is left as the abstract
diagonal entry because only its passing *through* `CNOT` as a scalar matters.  Proved on
the underlying vectors via `Matrix.ofLp_toEuclideanCLM` and the explicit diagonal form
`Concrete.rotZ_eq`, mirroring `pauliZGate_op_apply_qubitBasis`. -/
theorem rotZGate_op_apply_qubitBasis (θ : ℝ) (c : Fin 2) :
    (rotZGate θ).op (qubitBasis c).vec = Concrete.rotZ θ c c • (qubitBasis c).vec := by
  rw [rotZGate_op, qubitBasis_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotZ θ))
        (EuclideanSpace.single c 1)).ofLp
      = ((Concrete.rotZ θ c c) • (EuclideanSpace.single c 1 : EuclideanSpace ℂ (Fin 2))).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases c <;> fin_cases j <;>
      simp [Concrete.rotZ_eq, Matrix.mulVec, dotProduct, EuclideanSpace.single]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **The Pauli `X` gate commutes with the `x`-rotation gate:** `X · R_x(θ) = R_x(θ) · X`.  Since
`R_x(θ) = exp(-iθX/2)` is a function of `X`, the two commute; formally, the concrete matrices
`Concrete.pauliX` and `Concrete.rotX θ` commute, and the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM` (multiplicative) carries that to the gate operators.  This is the hypothesis
`controlledUnitary_comm_onRight` needs to conclude `cnotGate_comp_rotXGate_onRight`. -/
theorem pauliXGate_comp_rotXGate (θ : ℝ) :
    pauliXGate.comp (rotXGate θ) = (rotXGate θ).comp pauliXGate := by
  have hm : Concrete.pauliX * Concrete.rotX θ = Concrete.rotX θ * Concrete.pauliX := by
    rw [Concrete.rotX_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Concrete.pauliX, Matrix.mul_apply, Fin.sum_univ_two]
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.comp_op, pauliXGate_op, rotXGate_op]
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX)
      * (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotX θ))
    = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.rotX θ))
      * (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliX)
  rw [← map_mul, ← map_mul, hm]

/-- **A `z`-rotation on the control commutes with `CNOT`:**
`CNOT · (R_z(θ) ⊗ 1) = (R_z(θ) ⊗ 1) · CNOT`.  `R_z(θ)` merely rephases each control label
`|c⟩ ↦ e_c|c⟩`, and `CNOT` depends on the control only through that label, so the phase `e_c`
factors out and rides through `CNOT` unchanged.  A basis-state verification via
`twoQubit_evolution_ext`, descending to the vector level (`PureState.ext`) for the phase and moving
it through `CNOT` with `cnotGate_op_smul`, exactly as in `cnotGate_comp_pauliZGate_onLeft`. -/
theorem cnotGate_comp_rotZGate_onLeft (θ : ℝ) :
    cnotGate.comp ((rotZGate θ).onLeft qubit)
      = ((rotZGate θ).onLeft qubit).comp cnotGate := by
  apply twoQubit_evolution_ext
  intro c t
  apply PureState.ext
  simp only [Evolution.evolvePure_comp, Evolution.evolvePure_vec, PureState.tmul_vec]
  rw [Evolution.onLeft_op_tmul, rotZGate_op_apply_qubitBasis, ← TensorProduct.smul_tmul',
    cnotGate_op_smul, cnotGate_op_qubitBasisVec_tmul]
  rw [Evolution.onLeft_op_tmul, rotZGate_op_apply_qubitBasis, ← TensorProduct.smul_tmul']
  rfl

/-- **An `x`-rotation on the target commutes with `CNOT`:**
`CNOT · (1 ⊗ R_x(θ)) = (1 ⊗ R_x(θ)) · CNOT`.  `CNOT = C(X)` acts on the target by `X`, and
`R_x(θ)` is a function of `X` (so they commute on the target, `pauliXGate_comp_rotXGate`); the
general controlled-gate/target-gate commutation `controlledUnitary_comm_onRight` then lifts that to
`CNOT`, since `cnotGate = controlledUnitary pauliXGate`. -/
theorem cnotGate_comp_rotXGate_onRight (θ : ℝ) :
    cnotGate.comp ((rotXGate θ).onRight qubit)
      = ((rotXGate θ).onRight qubit).comp cnotGate := by
  rw [cnotGate_def]
  exact controlledUnitary_comm_onRight pauliXGate (rotXGate θ) (pauliXGate_comp_rotXGate θ)

end AxQM
