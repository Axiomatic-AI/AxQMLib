/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary

/-!
# AxQM.Postulates.API — the Pauli-`Y` gate

The **Pauli-`Y` gate** as a closed-system `Evolution` of the qubit, completing the Pauli gate
family (`pauliXGate` in `ControlledUnitary.lean`, `pauliZGate` in `Teleportation.lean`).  It is the
missing single-qubit gate needed to state the `Y`-conjugation circuit identities of Nielsen &
Chuang **Exercise 4.31** (`CY₁C = Y₁X₂`, `CY₂C = Z₁Y₂`).

## What is formalised

* `pauliYGate` — `Y` as an `Evolution qubit`: its operator is `Concrete.pauliY = !![0,-i; i,0]`
  promoted through `Matrix.toEuclideanCLM`, with unitarity transported from
  `Concrete.pauliY_mem_unitaryGroup` (exactly as `pauliZGate` promotes `Concrete.pauliZ`).
* `pauliYGate_op` — the underlying operator is `Matrix.toEuclideanCLM Concrete.pauliY`.
* `pauliYGate_op_apply_qubitBasis` — the computational-basis action `Y|i⟩ = i·(-1)ⁱ |i + 1⟩`
  (i.e. `Y|0⟩ = i|1⟩`, `Y|1⟩ = -i|0⟩`): a bit flip `i ↦ i + 1` carrying the phase `i·(-1)ⁱ`.  This
  is the `Y`-analogue of `pauliZGate_op_apply_qubitBasis` (`Z|i⟩ = (-1)ⁱ|i⟩`) and
  `pauliXGate_op_apply_qubitBasis` (`X|i⟩ = |i + 1⟩`), and the form in which `Y` enters the
  basis-action proofs of the CNOT–`Y` propagation rules.

## Design notes

* `pauliYGate` is an `Evolution` (Postulate 5), so it cannot be formed without discharging
  unitarity.  It mirrors `pauliXGate` and `pauliZGate`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **Pauli-`Y` gate** `Y` as a closed-system `Evolution` of the qubit: its operator is the
concrete matrix `Concrete.pauliY = !![0,-i; i,0]` promoted through `Matrix.toEuclideanCLM`, with
unitarity transported from `Concrete.pauliY_mem_unitaryGroup`. -/
def pauliYGate : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliY
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)) Concrete.pauliY_mem_unitaryGroup

/-- The underlying operator of `pauliYGate` is `Matrix.toEuclideanCLM Concrete.pauliY`. -/
@[simp]
theorem pauliYGate_op :
    pauliYGate.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliY := rfl

/-- **The Pauli-`Y` gate action on the computational basis:** `Y|i⟩ = i·(-1)ⁱ |i + 1⟩`, i.e.
`pauliYGate.op` sends `|i⟩` to `(i·(-1)ⁱ) • |i + 1⟩` (`Y|0⟩ = i|1⟩`, `Y|1⟩ = -i|0⟩`): a bit flip
carrying the phase `i·(-1)ⁱ`.  The `Y`-analogue of `pauliZGate_op_apply_qubitBasis`, proved the same
way (compute `pauliY ·ᵥ eᵢ` entrywise through `Matrix.ofLp_toEuclideanCLM`). -/
theorem pauliYGate_op_apply_qubitBasis (i : Fin 2) :
    pauliYGate.op (qubitBasis i).vec
      = (Complex.I * (-1 : ℂ) ^ (i : ℕ)) • (qubitBasis (i + 1)).vec := by
  rw [pauliYGate_op, qubitBasis_vec, qubitBasis_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.pauliY)
        (EuclideanSpace.single i 1)).ofLp
      = ((Complex.I * (-1 : ℂ) ^ (i : ℕ)) •
          (EuclideanSpace.single (i + 1) 1 : EuclideanSpace ℂ (Fin 2))).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases i <;> fin_cases j <;>
      simp [Concrete.pauliY, Matrix.mulVec, dotProduct, EuclideanSpace.single]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

end AxQM
