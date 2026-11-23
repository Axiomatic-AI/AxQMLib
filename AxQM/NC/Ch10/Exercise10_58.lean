/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasureObservable
import AxQM.Postulates.API.SwapCircuit
import AxQM.Postulates.API.GateCommute
import AxQM.Postulates.API.PauliGateEigenstate
import AxQM.NC.Ch4.Exercise4_34
import AxQM.NC.Ch4.Exercise4_17

/-!
# Nielsen & Chuang, Exercise 10.58 (Verifying the operator-measurement circuits)

*(N&C p. 474.)*

Verify circuits of Figs 10.13-10.15 measure operator M / X / Z, and the claimed equivalences.

The three figures give circuits for **measuring a single-qubit operator**:

* **Figure 10.13** — the general circuit `(H ⊗ 1) · C(M) · (H ⊗ 1)` measuring a Hermitian involution
  `M` (eigenvalues `±1`), with the ancilla flagging the eigenvalue.  This is exactly N&C
  **Exercise 4.34**, already formalised as `measureObservableCircuit` and its action theorem
  `measureObservableCircuit_op_qubitBasisZero_tmul`
  (`AxQM/Postulates/API/MeasureObservable.lean`): with the ancilla in `|0⟩` the circuit sends
  `|0⟩ ⊗ |ψ⟩` to `|0⟩ ⊗ P₊|ψ⟩ + |1⟩ ⊗ P₋|ψ⟩` (the `±1`
  eigenprojectors / `signMeasurement` operators), and on a `±1` eigenstate the ancilla reads the
  eigenvalue deterministically (the `..._of_hasEigenstate_*` theorems in `NC/Ch4`).
  Figures 10.14 and 10.15 are the `M = X` and `M = Z` instances, each paired with a **second,
  equivalent circuit**.

## What this file formalises

The genuinely new content of Exercise 10.58 is the **claimed circuit equivalences** of Figures 10.14
and 10.15, together with the fact that the two figures measure `X` and `Z`:

* `measureObservableCircuit_pauliZGate_eq_reversedCnotGate` — **Figure 10.15**: the `Z`-measurement
  circuit `(H ⊗ 1) · C(Z) · (H ⊗ 1)` *equals* the reversed CNOT `reversedCnotGate` (control on the
  data qubit) — the "useful simplification" replacing the two Hadamards and a controlled-`Z` by a
  single controlled-`NOT` into the ancilla.
* `measureObservableCircuit_pauliXGate_eq_hadamardConjReversedCnot` — **Figure 10.14**: the
  `X`-measurement circuit `(H ⊗ 1) · C(X) · (H ⊗ 1)` *equals* the reversed CNOT conjugated by
  Hadamards on the data qubit, `(1 ⊗ H) · reversedCNOT · (1 ⊗ H)` — the "useful equivalent circuit".
* `measureObservableCircuit_pauliZGate_evolvePure_ketZero_*` / `_pauliXGate_evolvePure_ketZero_*` —
  the two circuits **measure `Z` and `X`**: on the corresponding `±1` eigenstates (`|0⟩, |1⟩` for
  `Z`; `|+⟩, |-⟩` for `X`) the ancilla deterministically reads `0 ↦ +1`, `1 ↦ -1`, leaving the
  target in the eigenvector.  Deterministic readings of Figure 10.13 (Exercise 4.34) applied to `X`
  and `Z`, via the gate-eigenstate facts of `AxQM/Postulates/API/PauliGateEigenstate.lean`.

## Design notes

* **Fidelity.**  N&C's Figures 10.14/10.15 assert that *two circuits are equivalent*.  We render
  each as a full **gate equality** of `Evolution`s (equal unitaries), the strongest faithful
  reading — not a mere "agree on `|0⟩ ⊗ ψ`" surrogate.  The right-hand circuits are the pre-existing
  reversed CNOT `reversedCnotGate` (control on the second/data qubit), which is precisely N&C's
  "data qubit controls the ancilla".
* **Reuse.**  Both equivalences are `Evolution` equalities proved by reusing the library's
  controlled-`Z`/reversed-CNOT identities:
  - Fig 10.15 is `reversedCnotGate_eq_hadamard_conj_controlledZGate.symm`: since
    `measureObservableCircuit pauliZGate` is defeq to `(H ⊗ 1) · CZ · (H ⊗ 1)`
    (`controlledZGate = controlledUnitary pauliZGate`), the equivalence *is* that lemma reversed.
  - Fig 10.14 combines `cnotGate_eq_hadamard_conj_controlledZGate` (N&C Ex 4.17) and
    `reversedCnotGate_eq_hadamard_conj_controlledZGate` with the commutation of `onLeft`/`onRight`
    Hadamards (`Evolution.onLeft_comm_onRight`): both sides reduce to `(H⊗1)·(1⊗H)·CZ·(1⊗H)·(H⊗1)`.
* **Why Figure 10.13 is not re-proved here.**  Figure 10.13 is Exercise 4.34 verbatim; the `X`/`Z`
  readings below *are* Figure 10.13 applied to the two Pauli instances.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-! ### Figure 10.15: the `Z`-measurement equivalence -/

/-- **Nielsen & Chuang, Figure 10.15 (circuit equivalence).** The `Z`-measurement circuit
`(H ⊗ 1) · C(Z) · (H ⊗ 1)` equals the reversed CNOT (control on the data qubit) — the "useful
simplification": measuring `Z` needs no Hadamards, just a single controlled-`NOT` into the ancilla.
Since `controlledZGate = controlledUnitary pauliZGate`, `measureObservableCircuit pauliZGate` is
definitionally `(H ⊗ 1) · CZ · (H ⊗ 1)`, so this is exactly
`reversedCnotGate_eq_hadamard_conj_controlledZGate` reversed. -/
theorem measureObservableCircuit_pauliZGate_eq_reversedCnotGate :
    measureObservableCircuit pauliZGate = reversedCnotGate :=
  reversedCnotGate_eq_hadamard_conj_controlledZGate.symm

/-! ### Figure 10.14: the `X`-measurement equivalence -/

/-- **Nielsen & Chuang, Figure 10.14 (circuit equivalence).** The `X`-measurement circuit
`(H ⊗ 1) · C(X) · (H ⊗ 1)` equals the reversed CNOT conjugated by Hadamards on the *data* qubit,
`(1 ⊗ H) · reversedCNOT · (1 ⊗ H)` — the "useful equivalent circuit": flip to the `X`-eigenbasis on
the data qubit, do the data-controlled `NOT` into the ancilla, and flip back.  Rewriting
`cnotGate` (N&C Ex 4.17) and `reversedCnotGate` to their controlled-`Z` conjugations, both sides
become `(H ⊗ 1) · (1 ⊗ H) · CZ · (1 ⊗ H) · (H ⊗ 1)` once the commuting `onLeft`/`onRight` Hadamards
are reordered (`Evolution.onLeft_comm_onRight`). -/
theorem measureObservableCircuit_pauliXGate_eq_hadamardConjReversedCnot :
    measureObservableCircuit pauliXGate
      = (hadamardGate.onRight qubit).comp (reversedCnotGate.comp (hadamardGate.onRight qubit)) := by
  have hc : (hadamardGate.onLeft qubit).comp (hadamardGate.onRight qubit)
      = (hadamardGate.onRight qubit).comp (hadamardGate.onLeft qubit) :=
    Evolution.onLeft_comm_onRight hadamardGate hadamardGate
  rw [reversedCnotGate_eq_hadamard_conj_controlledZGate, measureObservableCircuit,
    ← cnotGate_def, cnotGate_eq_hadamard_conj_controlledZGate]
  simp only [← Evolution.mul_def] at hc ⊢
  simp only [mul_assoc]
  rw [hc]
  rw [← mul_assoc, ← mul_assoc, hc, mul_assoc, mul_assoc]

/-! ### The `Z`-measurement circuit measures `Z` -/

/-- **Figure 10.15 measures `Z`, outcome `+1`.** On the `+1` eigenstate `|0⟩`, the `Z`-measurement
circuit sends `|0⟩ ⊗ |0⟩` to `|0⟩ ⊗ |0⟩`: the ancilla reads `0` (eigenvalue `+1`) with certainty and
the target is left in `|0⟩`. -/
theorem measureObservableCircuit_pauliZGate_evolvePure_ketZero_qubitBasisZero :
    (measureObservableCircuit pauliZGate).evolvePure ((qubitBasis 0) ⊗ (qubitBasis 0))
      = (qubitBasis 0) ⊗ (qubitBasis 0) :=
  measureObservableCircuit_evolvePure_ketZero_tmul_of_hasEigenstate_one pauliZGate
    pauliZGate_hasEigenstate_one_qubitBasisZero

/-- **Figure 10.15 measures `Z`, outcome `-1`.** On the `-1` eigenstate `|1⟩`, the `Z`-measurement
circuit sends `|0⟩ ⊗ |1⟩` to `|1⟩ ⊗ |1⟩`: the ancilla reads `1` (eigenvalue `-1`) with certainty and
the target is left in `|1⟩`. -/
theorem measureObservableCircuit_pauliZGate_evolvePure_ketZero_qubitBasisOne :
    (measureObservableCircuit pauliZGate).evolvePure ((qubitBasis 0) ⊗ (qubitBasis 1))
      = (qubitBasis 1) ⊗ (qubitBasis 1) :=
  measureObservableCircuit_evolvePure_ketZero_tmul_of_hasEigenstate_neg_one pauliZGate
    pauliZGate_hasEigenstate_negOne_qubitBasisOne

/-! ### The `X`-measurement circuit measures `X` -/

/-- **Figure 10.14 measures `X`, outcome `+1`.** On the `+1` eigenstate `|+⟩`, the `X`-measurement
circuit sends `|0⟩ ⊗ |+⟩` to `|0⟩ ⊗ |+⟩`: the ancilla reads `0` (eigenvalue `+1`) with certainty and
the target is left in `|+⟩`. -/
theorem measureObservableCircuit_pauliXGate_evolvePure_ketZero_qubitPlus :
    (measureObservableCircuit pauliXGate).evolvePure ((qubitBasis 0) ⊗ qubitPlus)
      = (qubitBasis 0) ⊗ qubitPlus :=
  measureObservableCircuit_evolvePure_ketZero_tmul_of_hasEigenstate_one pauliXGate
    pauliXGate_hasEigenstate_one_qubitPlus

/-- **Figure 10.14 measures `X`, outcome `-1`.** On the `-1` eigenstate `|-⟩`, the `X`-measurement
circuit sends `|0⟩ ⊗ |-⟩` to `|1⟩ ⊗ |-⟩`: the ancilla reads `1` (eigenvalue `-1`) with certainty and
the target is left in `|-⟩`. -/
theorem measureObservableCircuit_pauliXGate_evolvePure_ketZero_qubitMinus :
    (measureObservableCircuit pauliXGate).evolvePure ((qubitBasis 0) ⊗ qubitMinus)
      = (qubitBasis 1) ⊗ qubitMinus :=
  measureObservableCircuit_evolvePure_ketZero_tmul_of_hasEigenstate_neg_one pauliXGate
    pauliXGate_hasEigenstate_negOne_qubitMinus

end AxQM
