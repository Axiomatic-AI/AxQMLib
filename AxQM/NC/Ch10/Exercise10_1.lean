/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ThreeQubitBitFlipCode

/-!
# Nielsen & Chuang, Exercise 10.1 — the three-qubit bit-flip encoding circuit

Verify the encoding circuit of Fig 10.2 encodes a|0>+b|1> as a|000>+b|111>.

The three-qubit bit-flip code (Nielsen & Chuang §10.1.1) protects one logical qubit against a
single bit-flip (`X`) error by *encoding* it into three physical qubits. Figure 10.2 shows the
encoder: the data qubit in state `a|0⟩ + b|1⟩` is fed in on the top wire alongside two ancillae
prepared in `|0⟩`, and **two CNOT gates, both controlled by the data qubit**, copy its value onto
the two ancillae — `CNOT₁₂` (control qubit 1, target qubit 2) and `CNOT₁₃` (control qubit 1,
target qubit 3). The result is the logical state `a|000⟩ + b|111⟩`.

## What this file provides

The **objects** — the input state `qubitSuperposition a b h` (`a|0⟩ + b|1⟩`), the encoder
`bitFlipEncode` (the Figure 10.2 circuit `C(X ⊗ 1) ∘ C(1 ⊗ X)`), and the output codeword
`bitFlipCodeword a b h` (`a|000⟩ + b|111⟩`) — are constructed in
`AxQM.Postulates.API.ThreeQubitBitFlipCode`, together with their normalization proofs. This file
holds the **verification theorems** of the exercise:

* `bitFlipEncode_evolvePure_ket0` / `bitFlipEncode_evolvePure_ket1` — the action on the two
  computational-basis inputs: `|0⟩|00⟩ ↦ |000⟩` and `|1⟩|00⟩ ↦ |111⟩`. These are exactly the two
  logical codewords produced by the encoder, and are the basis-level content the general claim
  rests on.
* `bitFlipEncode_evolvePure_qubitSuperposition` — **the exercise:** the encoder takes
  `a|0⟩ + b|1⟩` (with the two `|0⟩` ancillae) to `a|000⟩ + b|111⟩`, i.e.
  `bitFlipEncode.evolvePure (qubitSuperposition a b h ⊗ |0⟩ ⊗ |0⟩) = bitFlipCodeword a b h`.

## Design notes

* **The input is the general state.** `qubitSuperposition a b h` is the arbitrary normalized qubit
  `a|0⟩ + b|1⟩`, so the theorem verifies the circuit on *every* input, not just basis states; the
  general claim is reduced to the two basis actions (`bitFlipEncode_evolvePure_ket{0,1}`) by
  linearity of the underlying unitary.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The encoder maps `|0⟩` (with `|0⟩|0⟩` ancillae) to the logical zero `|000⟩`.** With the data
qubit in `|0⟩` both CNOTs leave the ancillae untouched, so `|0⟩|00⟩ ↦ |000⟩`. This is the logical
codeword `|0_L⟩`. -/
theorem bitFlipEncode_evolvePure_ket0 :
    bitFlipEncode.evolvePure (qubitBasis 0 ⊗ qubitBasis 0 ⊗ qubitBasis 0)
      = qubitBasis 0 ⊗ qubitBasis 0 ⊗ qubitBasis 0 := by
  rw [bitFlipEncode, Evolution.evolvePure_comp, controlledUnitary_evolvePure_ketZero,
    controlledUnitary_evolvePure_ketZero]

/-- **The encoder maps `|1⟩` (with `|0⟩|0⟩` ancillae) to the logical one `|111⟩`.** With the data
qubit in `|1⟩` both CNOTs flip their target ancilla, so `|1⟩|00⟩ ↦ |111⟩`. This is the logical
codeword `|1_L⟩`. -/
theorem bitFlipEncode_evolvePure_ket1 :
    bitFlipEncode.evolvePure (qubitBasis 1 ⊗ qubitBasis 0 ⊗ qubitBasis 0)
      = qubitBasis 1 ⊗ qubitBasis 1 ⊗ qubitBasis 1 := by
  rw [bitFlipEncode, Evolution.evolvePure_comp, controlledUnitary_evolvePure_ketOne,
    controlledUnitary_evolvePure_ketOne]
  simp only [Evolution.tmul_evolvePure, Evolution.id_evolvePure, pauliXGate_evolvePure_qubitBasis]
  norm_num

/-- **Nielsen & Chuang, Exercise 10.1.** The encoding circuit of Figure 10.2 takes the general
single-qubit state `a|0⟩ + b|1⟩` (fed in with two `|0⟩` ancillae) to the three-qubit codeword
`a|000⟩ + b|111⟩`:
`bitFlipEncode.evolvePure (qubitSuperposition a b h ⊗ |0⟩ ⊗ |0⟩) = bitFlipCodeword a b h`.

The proof reduces to the two computational-basis actions `bitFlipEncode_evolvePure_ket{0,1}` by
linearity of the encoding unitary: writing the input vector as `a • |0⟩|00⟩ + b • |1⟩|00⟩` and
pushing the unitary through the sum sends it to `a • |000⟩ + b • |111⟩`, which is exactly the
codeword's vector. -/
theorem bitFlipEncode_evolvePure_qubitSuperposition (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    bitFlipEncode.evolvePure (qubitSuperposition a b h ⊗ qubitBasis 0 ⊗ qubitBasis 0)
      = bitFlipCodeword a b h := by
  have hop0 := congrArg PureState.vec bitFlipEncode_evolvePure_ket0
  have hop1 := congrArg PureState.vec bitFlipEncode_evolvePure_ket1
  rw [Evolution.evolvePure_vec] at hop0 hop1
  -- Decompose the input vector into `a • |0⟩|00⟩ + b • |1⟩|00⟩` at the composite-system head, so
  -- the unitary's linearity (`map_add`/`map_smul`) applies. `change` re-presents the right-hand
  -- side at the raw tensor head, where `TensorProduct.add_tmul`/`smul_tmul'` fire (they agree by
  -- defeq, as `PureState.tmul_vec` is a `rfl`).
  have hin : (qubitSuperposition a b h ⊗ qubitBasis 0 ⊗ qubitBasis 0).vec
      = a • (qubitBasis 0 ⊗ qubitBasis 0 ⊗ qubitBasis 0).vec
        + b • (qubitBasis 1 ⊗ qubitBasis 0 ⊗ qubitBasis 0).vec := by
    change (qubitSuperposition a b h ⊗ qubitBasis 0 ⊗ qubitBasis 0).vec
        = a • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0 ⊗ qubitBasis 0).vec)
          + b • ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0 ⊗ qubitBasis 0).vec)
    rw [PureState.tmul_vec, qubitSuperposition_vec, TensorProduct.add_tmul,
      ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
  apply PureState.ext
  rw [Evolution.evolvePure_vec, hin, map_add, map_smul, map_smul, hop0, hop1, bitFlipCodeword_vec]

end AxQM
