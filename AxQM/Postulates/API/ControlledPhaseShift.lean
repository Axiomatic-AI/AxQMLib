/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitaryDecomposition

/-!
# AxQM.Postulates.API — the controlled phase-shift gate `C(P(φ))`

The quantum-Fourier-transform circuit's two-qubit gate (Nielsen & Chuang, §5.1): the controlled
phase-shift gate `C(P(φ))` on two qubits, the controlled version of the single-qubit phase gate
`P(φ) = phaseShiftGate φ = diag(1, exp(iφ))`. It parallels `controlledUnitary`, `cnotGate` and
`controlledZGate`, in particular `controlledZGate = controlledUnitary pauliZGate`.

* `controlledPhaseShift φ = controlledUnitary (phaseShiftGate φ)` — the **controlled phase-shift
  gate** `C(P(φ)) = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ P(φ)` on `qubit ⊗ qubit` (control qubit on the left), the
  *only* kind of two-qubit gate appearing in the quantum-Fourier-transform circuit. As an instance
  of `controlledUnitary` it is a genuine `Evolution` (Postulate 5). The QFT's phase gate `C(R_k)` is
  the instance `φ = 2π/2ᵏ`.

## Uses

The Fourier-addition circuit of Problem 5.6 and the controlled-`R_k` decomposition of Exercise 5.4
use this gate, as `controlledZGate` is defined in `Postulates.API.ControlledZ`. That measuring the
control turns `C(P(φ))` into a classically-controlled single-qubit gate (N&C Problem 5.2, via the
deferred-measurement engine and Exercise 4.35) is stated in `AxQM/NC/Ch5/Problem5_2.lean`.
-/

noncomputable section

namespace AxQM

/-- The **controlled phase-shift gate** `C(P(φ)) = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ P(φ)` on `qubit ⊗ qubit`
(control qubit on the left), Nielsen & Chuang's controlled phase rotation — the *only* kind of
two-qubit gate appearing in the quantum-Fourier-transform circuit (§5.1). Defined as the
`controlledUnitary` instance at the phase-shift gate `P(φ) = phaseShiftGate φ = diag(1, exp(iφ))`,
mirroring `controlledZGate = controlledUnitary pauliZGate`; it is a genuine `Evolution` (Postulate
5). The QFT's phase gate `C(R_k)` is the instance `φ = 2π/2ᵏ`. -/
def controlledPhaseShift (φ : ℝ) : Evolution (qubit ⊗ qubit) :=
  controlledUnitary (phaseShiftGate φ)

@[simp]
theorem controlledPhaseShift_eq (φ : ℝ) :
    controlledPhaseShift φ = controlledUnitary (phaseShiftGate φ) := rfl

end AxQM
