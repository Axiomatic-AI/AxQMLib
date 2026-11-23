/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.CnotXBasis

/-!
# AxQM — the Toffoli ancilla (magic) state (N&C Exercises 10.68, 10.72)

The entangled three-qubit *ancilla state* at the heart of Nielsen & Chuang's fault-tolerant Toffoli
construction (Exercise 10.68, the leftmost dotted box of the Figure on p. 488; the state prepared in
Exercise 10.72):

  `|Θ_T⟩ = ½ (|000⟩ + |010⟩ + |100⟩ + |111⟩)`.

It is produced by the (non-fault-tolerant) preparation circuit that applies a Hadamard to each of
the two control ancilla wires and then a Toffoli gate to the state `|000⟩`:

  `|Θ_T⟩ = C²(X) · (H₁ · H₂) |000⟩ = C²(X) (|+⟩|+⟩|0⟩)`.

This is the Toffoli analogue of the π/8-gate ancilla `|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2` of Exercise
10.66: the resource whose consumption teleports the non-Clifford gate onto the data. The part-(2)
circuit of Exercise 10.68 prepares exactly this state in its ancilla block, and Exercise 10.72 asks
for a *fault-tolerant* preparation of it; the state itself and the elementary circuit that produces
it are the shared object formalised here.

## What is formalised

* `toffoliAncillaPrep` — the preparation `Evolution` `C²(X) · H₁ · H₂` on the three-qubit register
  (Hadamards on the two control wires, then the Toffoli).
* `toffoliAncilla` — the ancilla state, defined as the output `toffoliAncillaPrep |000⟩` of that
  circuit (a genuine `PureState`, no normalization side-condition, since `Evolution`s are unitary).
* `toffoliAncilla_prep_ketPlus` — the intermediate reduction `toffoliAncilla = C²(X) (|+⟩|+⟩|0⟩)`:
  the two Hadamards turn the control wires into `|+⟩`.
* `toffoliAncilla_vec` — **the value of the ancilla state:**
  `|Θ_T⟩ = ½ (|000⟩ + |010⟩ + |100⟩ + |111⟩)` (N&C eq. of Exercise 10.72), the explicit
  computational-basis expansion.

The bare-`⊗ₜ` Toffoli truth table `toffoliGate_op_qubitBasisVec_tmul` used in the proof is a
general lemma in `AxQM/Postulates/API/ControlledControlledUnitary.lean` (beside
`toffoliGate_op_qubitBasis_vec`).

## Design notes

* **State as circuit output.** `toffoliAncilla` is defined as `toffoliAncillaPrep.evolvePure |000⟩`
  rather than packaged directly from its vector: unitarity gives normalization for free, and it
  records the *physical origin* of the state (the prep circuit) that both consuming exercises need.
  Its explicit value is the content of `toffoliAncilla_vec`.
* **Proof route.** The two Hadamards are discharged at the `PureState` level (`H|0⟩ = |+⟩` is a
  single pure state, so no superposition-distribution is needed there); only under the final Toffoli
  is `|+⟩ = (|0⟩+|1⟩)/√2` expanded, distributed into the four control-basis tensors, and the truth
  table applied — where `|110⟩ ↦ |111⟩` is the sole flip. The `invSqrt2 · invSqrt2 = ½` collapse
  gives the `½` prefactor.
* **Instance-diamond friction.** As in `OneBitTeleportation`, pushing `toffoliGate.op` through the
  distributed superposition uses `erw` for the `map_add`/`map_smul` steps (the gate's domain
  `(qubit ⊗ (qubit ⊗ qubit)).space` and the raw tensor head are defeq but carry different
  `Add`/`SMul` instances), after which the per-basis truth table fires by `rw` and `module` closes
  the linear identity.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The Toffoli ancilla preparation circuit** (Nielsen & Chuang, Exercise 10.68 part (2), leftmost
dotted box; Exercise 10.72): a Hadamard on each of the two control qubits, then a Toffoli gate, on
the three-qubit register `qubit ⊗ (qubit ⊗ qubit)`. Applied to `|000⟩` it prepares the entangled
ancilla `toffoliAncilla`. -/
def toffoliAncillaPrep : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  toffoliGate.comp
    ((hadamardGate.onLeft (qubit ⊗ qubit)).comp ((hadamardGate.onLeft qubit).onRight qubit))

/-- **The Toffoli ancilla (magic) state** `|Θ_T⟩ = ½(|000⟩ + |010⟩ + |100⟩ + |111⟩)`, defined as the
output `C²(X)·H₁·H₂ |000⟩` of the preparation circuit `toffoliAncillaPrep`. This is the resource
state consumed by the fault-tolerant Toffoli circuit (N&C Exercise 10.68) and the state prepared in
Exercise 10.72; its explicit value is `toffoliAncilla_vec`. -/
def toffoliAncilla : PureState (qubit ⊗ (qubit ⊗ qubit)) :=
  toffoliAncillaPrep.evolvePure (qubitThreeBasis (0, 0, 0))

/-- **The two Hadamards prepare `|+⟩|+⟩|0⟩`:** `toffoliAncilla = C²(X)(|+⟩ ⊗ |+⟩ ⊗ |0⟩)`. Applying
the preparation circuit's two Hadamards to `|000⟩` turns the control wires into `|+⟩` (a single pure
state each), leaving the Toffoli to act on the product `|+⟩|+⟩|0⟩`. -/
theorem toffoliAncilla_prep_ketPlus :
    toffoliAncilla = toffoliGate.evolvePure (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)) := by
  simp only [toffoliAncilla, toffoliAncillaPrep, qubitThreeBasis, Evolution.evolvePure_comp,
    Evolution.onRight_evolvePure, Evolution.onLeft_evolvePure,
    hadamardGate_evolvePure_qubitBasis_zero]

/-- **The value of the Toffoli ancilla state** (Nielsen & Chuang, Exercise 10.72; the ancilla of
Exercise 10.68 part (2)):

  `|Θ_T⟩ = ½ (|000⟩ + |010⟩ + |100⟩ + |111⟩)`.

Expanding the two `|+⟩` control wires and applying the Toffoli truth table: the sole basis component
with both controls set, `|110⟩`, has its target flipped to `|111⟩`; the other three are unchanged.
The `½` is `(1/√2)²`. -/
theorem toffoliAncilla_vec :
    toffoliAncilla.vec
      = (2⁻¹ : ℂ) • ((qubitThreeBasis (0, 0, 0)).vec + (qubitThreeBasis (0, 1, 0)).vec
          + (qubitThreeBasis (1, 0, 0)).vec + (qubitThreeBasis (1, 1, 1)).vec) := by
  have hpre : (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)).vec
      = (2⁻¹ : ℂ) • ((qubitThreeBasis (0, 0, 0)).vec + (qubitThreeBasis (1, 0, 0)).vec
          + (qubitThreeBasis (0, 1, 0)).vec + (qubitThreeBasis (1, 1, 0)).vec) := by
    rw [PureState.tmul_vec, PureState.tmul_vec, qubitPlus_vec_eq_smul_add,
      ← Concrete.invSqrt2_mul_self]
    simp only [qubitThreeBasis, PureState.tmul_vec, TensorProduct.add_tmul,
      ← TensorProduct.smul_tmul']
    erw [TensorProduct.smul_tmul_smul, TensorProduct.add_tmul, TensorProduct.tmul_add,
      TensorProduct.tmul_add]
    generalize (qubitBasis 0).vec = a
    generalize (qubitBasis 1).vec = b
    generalize (Concrete.invSqrt2 : ℂ) = s
    congr 1
    abel
  rw [toffoliAncilla_prep_ketPlus, Evolution.evolvePure_vec, hpre]
  simp only [qubitThreeBasis, PureState.tmul_vec]
  erw [map_smul, map_add, map_add, map_add, toffoliGate_op_qubitBasisVec_tmul,
    toffoliGate_op_qubitBasisVec_tmul, toffoliGate_op_qubitBasisVec_tmul,
    toffoliGate_op_qubitBasisVec_tmul]
  simp only [Fin.isValue, mul_zero, mul_one, add_zero, zero_add]
  generalize (qubitBasis 0).vec = a
  generalize (qubitBasis 1).vec = b
  congr 1
  congr 1
  apply add_right_comm

/-- **The Toffoli ancilla state as the AND-magic superposition** `|Θ_T⟩ = ½ Σ_{a,b} |a, b, a·b⟩`:
the sum form of `toffoliAncilla_vec`. Summing `|a, b, a·b⟩` over the two control bits `a, b` gives
the four terms `½(|000⟩ + |010⟩ + |100⟩ + |111⟩)` — only the both-controls-set branch `a = b = 1`
carries a set target `a·b = 1`, the AND of the controls. This is the form consumed by the
gate-teleportation reshape of Exercise 10.68 (`toffoliTeleportReshapedInput`, which is
`reshape(|Θ_T⟩ ⊗ |xyz⟩)`), where the summation index `(a, b)` becomes the teleportation-branch
label. Proved from `toffoliAncilla_vec` by expanding the two `Fin 2` sums and reducing `a·b`. -/
theorem toffoliAncilla_vec_sum :
    toffoliAncilla.vec
      = (2⁻¹ : ℂ) • ∑ a : Fin 2, ∑ b : Fin 2, (qubitThreeBasis (a, b, a * b)).vec := by
  rw [toffoliAncilla_vec]
  simp only [Fin.sum_univ_two, Fin.isValue, mul_zero, mul_one]
  module

end AxQM
