/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasureObservable
import AxQM.Postulates.API.ControlledZ
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.EvolutionTensorHom
import AxQM.NC.Ch5.Exercise5_9
import AxQM.NC.Ch10.Exercise10_6

/-!
# Nielsen & Chuang, Exercise 10.70 (Z errors in the fault-tolerant measurement ancilla)

*(N&C §10.6.3, p. 491.)*

Show Z errors in the ancilla do not propagate to encoded data but give an incorrect measurement
result.

## Context — the fault-tolerant measurement of Figure 10.28

To measure an encoded observable `M` fault-tolerantly, N&C (Fig. 10.28) use an ancilla in a **cat
state** `|00…0⟩ + |11…1⟩`, **one ancilla qubit per data qubit**.  After the cat is verified,
**controlled-`M′` gates** couple it to the data — ancilla qubit `i` is the *control* of a
`controlled-M′` on data qubit `i` (transversal `M = M′⊗⋯⊗M′`) — and the measurement result is read
off by *decoding* the cat with `CNOT`s and a `Hadamard`.  Figure 10.28 draws the cat in **three
qubits** "for simplicity"; that is the model formalised here (as for the companion Exercise 10.69),
on the block register `bitFlipReg = qubit ⊗ (qubit ⊗ qubit)` carrying the cat ancilla
`catBlockState σ = (|000⟩ + (−1)^σ |111⟩)/√2` (`Postulates/API/ShorCodeBlock`).

The exercise has two halves, and each turns on one structural fact:

* **(A) `Z` errors do not propagate to the data** — because the ancilla qubits are the *controls* of
  the `controlled-M′` gates, and a `Z` on the control **commutes** with a controlled gate (`Z` is
  diagonal in the control basis, `C(M′)` block-diagonal there).  The error slides through the
  ancilla–data interaction unchanged and never becomes an operation on the data.
* **(B) `Z` errors give an incorrect measurement result** — because the outcome *is* the sign of the
  cat, read by `blockXObservable = X⊗X⊗X` (eigenvalue `(−1)^σ` on `catBlockState σ`); a phase-flip
  `Z` on any ancilla qubit sends `catBlockState σ ↦ catBlockState (σ+1)`, flipping the readout.

## The formalisation

### The atomic mechanism (a single control/target pair, fully general)

The cat scheme is the single-qubit operator-measurement circuit
`measureObservableCircuit M = (H ⊗ 1) · C(M) · (H ⊗ 1)` (`Postulates/API/MeasureObservable`,
Fig. 10.26) with the ancilla *encoded* as a cat.  The atomic layer records both claims at this
control/target level, for **every** target system `S` and gate `M`:

* `controlledUnitary_comm_pauliZGate_onLeft` (in `AxQM/Postulates/API/ControlledZ.lean`) —
  **(A) local reason:** `C(U) · (Z ⊗ 1) = (Z ⊗ 1) · C(U)` for every `U` — a `Z` on the control
  commutes with the controlled gate.
* `measureObservableCircuitZError` / `measureObservableCircuit_zError_pre_eq` — the circuit with a
  `Z` error on the control between `C(M)` and the decoding `H`, and the error's position on that
  wire being immaterial.
* `measureObservableCircuitZError_eq_pauliXGate_onLeft_comp` — **the key identity, both claims at
  once:** since `H Z H = X`, the corrupted circuit equals `(X ⊗ 1) · measureObservableCircuit M` —
  an `X` on the ancilla **only** (data untouched = **A**, readout bit flipped = **B**).
* `measureObservableCircuit_evolvePure_qubitBasisZero_of_eigenstate` /
  `measureObservableCircuitZError_evolvePure_qubitBasisZero_of_eigenstate` — the concrete reading on
  a `+1` eigenstate `x` of `M`: ideal reports `0` (correct), corrupted reports `1` (incorrect), and
  in both the data factor is still `x` (unchanged).

### The genuine three-qubit cat ancilla of Figure 10.28

* **(B), cat level** — `blockXObservable_hasEigenstate_blockPhaseFlip_catBlockState`: a `Z` error on
  any one of the three ancilla qubits makes the sign readout `blockXObservable` report the
  *opposite* eigenvalue `(−1)^{σ+1}` (incorrect).  The `..._blockPhaseFlip_blockPhaseFlip_...`
  theorem records the *parity* structure: two `Z` errors cancel (`σ+1+1 = σ`), so an odd number of
  ancilla `Z` errors flips the readout and an even number leaves it correct.
* **(A), transversal level** — `transversalCoupling` is the transversal `C(M′)⊗C(M′)⊗C(M′)` coupling
  of the three (ancilla, data) pairs; `transversalCoupling_comm_transversalAncillaPhaseError` shows
  a `Z` error on any ancilla qubit **commutes past** the coupling, so it never becomes a data
  operation.  Several such (mutually commuting) errors compose, so *multiple* `Z` errors likewise do
  not propagate.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The atomic mechanism: a single control/target measurement pair -/

/-- The operator-measurement circuit `measureObservableCircuit M` **with a `Z` error on the
ancilla** (the control qubit), inserted between the controlled-`M` gate and the decoding `Hadamard`:
`(H ⊗ 1) · (Z ⊗ 1) · C(M) · (H ⊗ 1)`.  This models a `Z` error "in the ancilla" of the
fault-tolerant measurement of `M`. -/
def measureObservableCircuitZError (M : Evolution S) : Evolution (qubit.compose S) :=
  (hadamardGate.onLeft S).comp
    ((pauliZGate.onLeft S).comp ((controlledUnitary M).comp (hadamardGate.onLeft S)))

/-- **The `Z` error's position on the ancilla wire is immaterial.**  A `Z` error *before* the
controlled-`M` gate gives the same circuit as one *after* it — because a `Z` on the control commutes
with the controlled gate (`controlledUnitary_comm_pauliZGate_onLeft`).  This is the circuit form of
claim **(A)**: the error passes through the data interaction without touching the data. -/
theorem measureObservableCircuit_zError_pre_eq (M : Evolution S) :
    (hadamardGate.onLeft S).comp
        ((controlledUnitary M).comp ((pauliZGate.onLeft S).comp (hadamardGate.onLeft S)))
      = measureObservableCircuitZError M := by
  have hc : (controlledUnitary M).comp ((pauliZGate.onLeft S).comp (hadamardGate.onLeft S))
      = (pauliZGate.onLeft S).comp ((controlledUnitary M).comp (hadamardGate.onLeft S)) := by
    rw [← Evolution.comp_assoc, controlledUnitary_comm_pauliZGate_onLeft, Evolution.comp_assoc]
  unfold measureObservableCircuitZError
  rw [hc]

/-- **The key identity of Exercise 10.70.**  Because `H Z H = X`, a `Z` error on the ancilla is
equivalent to a bit-flip `X` on the ancilla readout applied at the very end of the (ideal)
measurement circuit: `measureObservableCircuitZError M = (X ⊗ 1) · measureObservableCircuit M`, with
`X ⊗ 1 = pauliXGate.onLeft S`.  The extra operator acts on the ancilla **only** (`onLeft`) and as
the identity on the data `S`, so it captures both halves of the exercise at once: **(A)** the
encoded data is untouched, and **(B)** the measured bit is flipped (incorrect result). -/
theorem measureObservableCircuitZError_eq_pauliXGate_onLeft_comp (M : Evolution S) :
    measureObservableCircuitZError M
      = (pauliXGate.onLeft S).comp (measureObservableCircuit M) := by
  unfold measureObservableCircuitZError measureObservableCircuit
  rw [← Evolution.comp_assoc, Evolution.onLeft_comp, hadamardGate_comp_pauliZGate,
    ← Evolution.onLeft_comp,
    Evolution.comp_assoc]

/-- **The ideal measurement is correct on a `+1` eigenstate.**  If `x` is a `+1` eigenstate of `M`
(`M x = x`), the operator-measurement circuit sends `|0⟩ ⊗ x` to `|0⟩ ⊗ x`: the ancilla reads `0`
with certainty (the correct outcome for eigenvalue `+1`) and the data is left in the eigenstate `x`.
Discharged by the general operator-measurement eigenstate reading
`measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_one` (N&C Ex 5.9), bridging the
fixed-point hypothesis `M.evolvePure x = x` to the `+1` eigenstate hypothesis `M.HasEigenstate 1 x`
(`M x = 1 • x`). -/
theorem measureObservableCircuit_evolvePure_qubitBasisZero_of_eigenstate
    (M : Evolution S) (x : PureState S) (hx : M.evolvePure x = x) :
    (measureObservableCircuit M).evolvePure ((qubitBasis 0).tmul x)
      = (qubitBasis 0).tmul x := by
  apply measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_one
  change M.op x.vec = (1 : ℂ) • x.vec
  rw [one_smul, ← Evolution.evolvePure_vec, hx]

/-- **(B) A `Z` error gives an incorrect measurement result, with the data unaffected.**  On the
same `+1` eigenstate `x` of `M` for which the ideal circuit reads `0`
(`measureObservableCircuit_evolvePure_qubitBasisZero_of_eigenstate`), the corrupted circuit sends
`|0⟩ ⊗ x` to `|1⟩ ⊗ x`: the ancilla now reads `1` — the *wrong* outcome — while the data factor is
still `x`, unchanged.  Thus the `Z` error does not propagate to the encoded data but does produce an
incorrect measurement result. -/
theorem measureObservableCircuitZError_evolvePure_qubitBasisZero_of_eigenstate
    (M : Evolution S) (x : PureState S) (hx : M.evolvePure x = x) :
    (measureObservableCircuitZError M).evolvePure ((qubitBasis 0).tmul x)
      = (qubitBasis 1).tmul x := by
  rw [measureObservableCircuitZError_eq_pauliXGate_onLeft_comp, Evolution.evolvePure_comp,
    measureObservableCircuit_evolvePure_qubitBasisZero_of_eigenstate M x hx,
    Evolution.onLeft_evolvePure, pauliXGate_evolvePure_qubitBasis]
  rfl

/-! ### The genuine three-qubit cat ancilla of Figure 10.28: incorrect readout (claim B)

The atomic picture above encodes the ancilla in a **single** control qubit; the fault-tolerant
measurement of N&C Fig. 10.28 instead uses a three-qubit **cat ancilla**
`catBlockState σ = (|000⟩ + (−1)^σ |111⟩)/√2`, one qubit per data qubit.  Its measurement outcome is
the sign `σ`, read by the sign-observable `blockXObservable = X⊗X⊗X`, whose eigenvalue on
`catBlockState σ` is `(−1)^σ` (`blockXObservable_hasEigenstate_catBlockState`). -/

/-- **(B), cat level — a single `Z` error on the cat ancilla flips the measurement readout.**  A
phase-flip `Z` error on *any* of the three ancilla qubits sends `catBlockState σ ↦ catBlockState
(σ+1)` (`blockPhaseFlip_evolvePure_catBlockState`), so the errored ancilla is read by
`blockXObservable` with the eigenvalue `(−1)^{σ+1}` — the **opposite** of the ideal `(−1)^σ` (since
`σ+1 ≠ σ` in `Fin 2`): the measured result is flipped, i.e. incorrect. -/
theorem blockXObservable_hasEigenstate_blockPhaseFlip_catBlockState (i : Fin 3) (σ : Fin 2) :
    blockXObservable.HasEigenstate ((-1 : ℝ) ^ ((σ + 1 : Fin 2) : ℕ))
      ((blockPhaseFlip i).evolvePure (catBlockState σ)) := by
  rw [blockPhaseFlip_evolvePure_catBlockState]
  exact blockXObservable_hasEigenstate_catBlockState (σ + 1)

/-- **(B), cat level — the readout flip is by parity: two `Z` errors cancel.**  Two phase-flip `Z`
errors on the cat ancilla (on any qubits `i, j`) restore the correct readout eigenvalue `(−1)^σ`,
because each `Z` flips the sign and `σ+1+1 = σ` in `Fin 2`.  Thus the measurement error is governed
by the **parity** of the number of ancilla `Z` errors — an odd number flips it (incorrect), an even
number leaves it correct.  (This parity structure is exactly why repeating the measurement and
taking a majority vote, N&C Fig. 10.28, suppresses the error probability to `O(p²)`.) -/
theorem blockXObservable_hasEigenstate_blockPhaseFlip_blockPhaseFlip_catBlockState
    (i j : Fin 3) (σ : Fin 2) :
    blockXObservable.HasEigenstate ((-1 : ℝ) ^ (σ : ℕ))
      ((blockPhaseFlip i).evolvePure ((blockPhaseFlip j).evolvePure (catBlockState σ))) := by
  have h2 : (σ + 1 + 1 : Fin 2) = σ := by fin_cases σ <;> decide
  rw [blockPhaseFlip_evolvePure_catBlockState, blockPhaseFlip_evolvePure_catBlockState, h2]
  exact blockXObservable_hasEigenstate_catBlockState σ

/-! ### The transversal coupling: `Z` errors do not propagate to the data (claim A)

The ancilla–data coupling of Fig. 10.28 is **transversal**: ancilla qubit `i` is the *control* of a
`controlled-M′` gate on data qubit `i`, and the three (ancilla, data) pairs are coupled
independently.  Working over an arbitrary data-qubit system `D`, this is the tensor product of three
`controlledUnitary M′` gates on the register of three (ancilla, data) pairs. -/

variable {D : QSystem}

/-- **The transversal controlled-`M′` coupling of Figure 10.28.**  Three independent (ancilla, data)
pairs, each coupled by a `controlledUnitary M′` whose control is the ancilla qubit (the left factor
of `qubit ⊗ D`) and whose target is the data qubit: `C(M′) ⊗ C(M′) ⊗ C(M′)`.  If the cat ancilla is
`|000⟩` nothing is done to the data; if `|111⟩` the transversal `M = M′⊗M′⊗M′` is applied — as in
N&C. -/
def transversalCoupling (M : Evolution D) :
    Evolution ((qubit.compose D).compose ((qubit.compose D).compose (qubit.compose D))) :=
  (controlledUnitary M) ⊗ ((controlledUnitary M) ⊗ (controlledUnitary M))

/-- **A phase-flip `Z` error on the `i`-th ancilla qubit** of the transversal coupling — the control
of pair `i` (the left factor of that pair's `qubit ⊗ D`) — acting as the identity on the two other
pairs. -/
def transversalAncillaPhaseError :
    Fin 3 → Evolution ((qubit.compose D).compose ((qubit.compose D).compose (qubit.compose D)))
  | 0 => (pauliZGate.onLeft D) ⊗
      ((Evolution.id : Evolution (qubit.compose D)) ⊗ (Evolution.id : Evolution (qubit.compose D)))
  | 1 => (Evolution.id : Evolution (qubit.compose D)) ⊗
      ((pauliZGate.onLeft D) ⊗ (Evolution.id : Evolution (qubit.compose D)))
  | 2 => (Evolution.id : Evolution (qubit.compose D)) ⊗
      ((Evolution.id : Evolution (qubit.compose D)) ⊗ (pauliZGate.onLeft D))

/-- **(A) — a `Z` error on the ancilla commutes past the coupling, so it does not propagate to the
data.**  A phase-flip `Z` error on ancilla qubit `i` commutes with the transversal coupling:
`transversalCoupling M · Zᵢ = Zᵢ · transversalCoupling M`.  Because the ancilla qubits are the
*controls*, the error slides through the ancilla–data interaction unchanged (per pair,
`controlledUnitary_comm_pauliZGate_onLeft`; on the other pairs it acts as the identity) and never
becomes an operation on the data.  Composing several such (mutually commuting) errors shows that
*multiple* ancilla `Z` errors likewise do not propagate. -/
theorem transversalCoupling_comm_transversalAncillaPhaseError (M : Evolution D) (i : Fin 3) :
    (transversalCoupling M).comp (transversalAncillaPhaseError i)
      = (transversalAncillaPhaseError i).comp (transversalCoupling M) := by
  fin_cases i <;>
    simp only [transversalCoupling, transversalAncillaPhaseError, Evolution.tmul_comp,
      controlledUnitary_comm_pauliZGate_onLeft, Evolution.comp_id, Evolution.id_comp]

end AxQM
