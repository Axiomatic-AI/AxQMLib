/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EigenspaceCollapse

/-!
# Nielsen & Chuang, Exercise 5.9 — collapsing `|ψ⟩` into an eigenspace of a `±1` unitary

*(N&C p. 225.)*

For U with eigenvalues +-1, construct circuit collapsing |psi> into one of the two eigenspaces with
indicator.

A unitary `U` with eigenvalues `±1` is a self-adjoint involution
(`U² = I`), so — exactly as in Exercise 4.34 — it is both a gate and an observable. Phase estimation
for a `±1` unitary needs only a **single** control qubit: the two eigenvalues have phases
`φ ∈ {0, ½}`, resolved exactly by one bit, and the `t = 1` phase-estimation circuit is precisely
Exercise 4.34's circuit `measureObservableCircuit U = (H ⊗ 1) · C(U) · (H ⊗ 1)` — a Hadamard on the
control, controlled-`U`, and a second Hadamard (the one-qubit inverse QFT). This is why the exercise
says to *compare with 4.34*: the phase-estimation answer for `±1` eigenvalues **is** the 4.34
circuit, now on an *arbitrary* target register (not just a single qubit).

## The formalisation

The circuit `measureObservableCircuit U` sends `|0⟩ ⊗ |ψ⟩` to the correlated state
`|0⟩ ⊗ P₊|ψ⟩ + |1⟩ ⊗ P₋|ψ⟩`, whose `|i⟩`-ancilla branch carries the target through the `i`-th
operator `M₀ = P₊`, `M₁ = P₋` of the projective measurement `Observable.signMeasurement` of `U`
(`measureObservableCircuit_op_qubitBasisZero_tmul_signMeasurement`, now over an arbitrary target).
Reading the single ancilla in the computational basis is therefore the sign measurement of `U`:
outcome `i ∈ {0, 1}` — the **classical indicator** — occurs with Born probability `‖Mᵢ|ψ⟩‖²`, and
the target **collapses into an eigenspace of `U`**:

* outcome `0` (indicator `+1`) → the target collapses to `Observable.postMeasPlus`, and
  `Observable.postMeasPlus_hasEigenstate` proves this is a genuine `+1` eigenstate of `U`;
* outcome `1` (indicator `−1`) → the target collapses to `Observable.postMeasMinus`
  (`Observable.postMeasurement_signMeasurement_minus`), a genuine `−1` eigenstate of `U`
  (`Observable.postMeasMinus_hasEigenstate`).

These collapse statements, about the eigenprojectors `P±` and the normalized
projected vectors, are in `AxQM/Postulates/API/EigenspaceCollapse.lean` (with the
`+1` machinery in `AxQM/Postulates/API/PauliMeasurement.lean`). Together they are the exercise's
"collapse `|ψ⟩` into one of the two eigenspaces of `U`, with a classical indicator as to which".

The statements in this file are the *deterministic* special case of that collapse, on a `±1`
eigenstate input, where the outcome is certain and the indicator flags the eigenvalue exactly (the
direct generalisation of Exercise 4.34's two eigenstate readings from a single qubit to an arbitrary
target register):

* `measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_one` — if `|ψ⟩` is a `+1`
  eigenstate of `U` (`U|ψ⟩ = |ψ⟩`), the circuit sends `|0⟩ ⊗ |ψ⟩` to `|0⟩ ⊗ |ψ⟩`: the ancilla reads
  `0` with certainty — indicating the `+1` eigenspace — and the target is left in the eigenvector.
* `measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_neg_one` — if `|ψ⟩` is a `−1`
  eigenstate (`U|ψ⟩ = −|ψ⟩`), the circuit sends `|0⟩ ⊗ |ψ⟩` to `|1⟩ ⊗ |ψ⟩`: the ancilla reads `1` —
  indicating the `−1` eigenspace — and the target is again left in the eigenvector.

## Design notes

* **Fidelity.** `U`'s `±1` eigenvalues, Hermiticity and unitarity are honoured:
  `U : Evolution S` is a genuine unitary gate on an *arbitrary* system `S` (matching N&C's "a state
  `|ψ⟩`", not a single qubit), the eigenvalue hypothesis is the grounded `Evolution.HasEigenstate`
  predicate, and the eigenstate readings are full equalities of `Evolution.evolvePure` on the
  composite input. The general-input collapse is the sign-measurement statement in the API file,
  quantifying over *every* input `|ψ⟩` (not just eigenstates), with the two collapsed states proved
  to be `±1` eigenstates.
* **Comparison with 4.34.** Exercise 4.34 is this same circuit at `S = qubit`; Exercise 5.9 is the
  observation that phase estimation supplies the same circuit for a `±1` unitary on any register,
  and its emphasis is the *eigenspace collapse with indicator*. Accordingly the content added over
  4.34 is the arbitrary-target generality and the explicit eigenspace-membership of the two
  collapsed states (`postMeasPlus_hasEigenstate` / `postMeasMinus_hasEigenstate`) — "the
  post-measurement state is *the corresponding eigenvector*".
* **Scope.** As in 4.34, the ancilla readout is realised as the target-system sign measurement
  `Observable.signMeasurement U` (whose Born statistics and post-measurement collapse are the API
  theorems above), rather than as a separate composite-system measurement of the ancilla wire; the
  two are physically identical (the `|i⟩`-branch amplitude is `Mᵢ|ψ⟩`), and this route states the
  collapse directly on the target register `|ψ⟩` the exercise asks about.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem} {ψ : PureState S}

/-- **Nielsen & Chuang, Exercise 5.9 (`+1` eigenspace, deterministic reading).** If the target input
`|ψ⟩` is a `+1` eigenstate of the `±1` unitary `U` (`U|ψ⟩ = |ψ⟩`), the phase-estimation circuit
`measureObservableCircuit U = (H ⊗ 1) · C(U) · (H ⊗ 1)` sends `|0⟩ ⊗ |ψ⟩` to `|0⟩ ⊗ |ψ⟩`: the
single ancilla is measured `0` — the classical indicator of the `+1` eigenspace — with certainty,
and the target is left in the corresponding eigenvector `|ψ⟩`. The arbitrary-target generalisation
of Exercise 4.34's `+1` reading; a deterministic special case of the general eigenspace collapse
(`measureObservableCircuit_op_qubitBasisZero_tmul_signMeasurement`). -/
theorem measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_one (U : Evolution S)
    (h : U.HasEigenstate 1 ψ) :
    (measureObservableCircuit U).evolvePure ((qubitBasis 0) ⊗ ψ) = (qubitBasis 0) ⊗ ψ := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec]
  rw [measureObservableCircuit_op_qubitBasisZero_tmul]
  have hev : U.op ψ.vec = (1 : ℂ) • ψ.vec := h
  rw [hev]
  simp only [TensorProduct.tmul_smul, one_smul, sub_self, smul_zero, ← two_smul ℂ, smul_smul,
    TensorProduct.tmul_zero, add_zero]
  norm_num
  rfl

/-- **Nielsen & Chuang, Exercise 5.9 (`−1` eigenspace, deterministic reading).** If the target input
`|ψ⟩` is a `−1` eigenstate of the `±1` unitary `U` (`U|ψ⟩ = −|ψ⟩`), the phase-estimation circuit
sends `|0⟩ ⊗ |ψ⟩` to `|1⟩ ⊗ |ψ⟩`: the single ancilla is measured `1` — the classical indicator of
the `−1` eigenspace — with certainty, and the target is left in the corresponding eigenvector `|ψ⟩`.
The arbitrary-target generalisation of Exercise 4.34's `−1` reading. -/
theorem measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_neg_one (U : Evolution S)
    (h : U.HasEigenstate (-1) ψ) :
    (measureObservableCircuit U).evolvePure ((qubitBasis 0) ⊗ ψ) = (qubitBasis 1) ⊗ ψ := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, PureState.tmul_vec]
  rw [measureObservableCircuit_op_qubitBasisZero_tmul]
  have hev : U.op ψ.vec = (-1 : ℂ) • ψ.vec := h
  rw [hev]
  simp only [TensorProduct.tmul_smul, neg_one_smul, add_neg_cancel, smul_zero, sub_neg_eq_add,
    ← two_smul ℂ, smul_smul, TensorProduct.tmul_zero, zero_add]
  norm_num
  rfl

end AxQM
