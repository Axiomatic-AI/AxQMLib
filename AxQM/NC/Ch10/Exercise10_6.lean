/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorCodePhaseFlip

/-!
# Nielsen & Chuang, Exercise 10.6 — recovery from a phase flip via `Z₁Z₂Z₃`

Recovery from a phase flip on any of first three Shor-code qubits via applying Z1Z2Z3.

## Setting

In the nine-qubit Shor code each logical qubit is encoded, at the outer (phase-flip) level, into
three **blocks** of three physical qubits, every block being a bit-flip cat state
`catBlockVec σ = |000⟩ + (−1)^σ |111⟩` (`σ = 0 ↔ |000⟩+|111⟩`, the encoding of `|+⟩`;
`σ = 1 ↔ |000⟩−|111⟩`, the encoding of `|−⟩`). The "first three qubits" of the exercise are exactly
the three physical qubits of the first block, carried by `bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`.

N&C describe the physics (§10.2, p. 433): *"a phase flip on any of the first three qubits ... flips
the sign of the first block of qubits, changing `|000⟩+|111⟩` to `|000⟩−|111⟩`, and vice versa ...
We recover from this by flipping the sign in the first block of three qubits back to its original
value."* The claim of the exercise is that this sign-restoring recovery is realised by the single
operator `Z₁Z₂Z₃`.

## This file

The content is the physics of recovery, in terms of `Evolution` (Postulate 2 — a
unitary gate) and its action on states, `Evolution.evolvePure`. The phase-flip errors
`blockPhaseFlip i` (`Z` on qubit `i ∈ {0,1,2}` of the block) and the recovery gate `blockZGate`
(`Z₁Z₂Z₃ = Z ⊗ Z ⊗ Z`) are built in `AxQM/Postulates/API/ShorCodePhaseFlip.lean`; the
statements here involve only `Evolution`, `evolvePure` and the block cat state `catBlockState`.

* `blockPhaseFlip_evolvePure_catBlockState` — **the error flips the block sign**: a phase flip on
  *any* of the three qubits sends `catBlockState σ` to `catBlockState (σ+1)`, the oppositely-signed
  cat state. This is N&C's "`|000⟩+|111⟩ ↔ |000⟩−|111⟩`".
* `blockZGate_evolvePure_catBlockState` — **the recovery operator flips the block sign too**:
  `Z₁Z₂Z₃` sends `catBlockState σ` to `catBlockState (σ+1)`.
* `blockPhaseFlip_recovery` — **the exercise**: applying `Z₁Z₂Z₃` after a phase flip on any of the
  three qubits returns the block to its original encoded state,
  `Z₁Z₂Z₃ · Zᵢ · |catBlockState σ⟩ = |catBlockState σ⟩`. Both the error and the recovery flip the
  sign (`σ ↦ σ+1`), so together they act as the identity on the code state (`σ ↦ σ+1+1 = σ` in
  `Fin 2`). The recovery is *independent of which* of the three qubits was hit — the single operator
  `Z₁Z₂Z₃` corrects all three phase-flip locations, exactly as the exercise asserts.

### Modelling

Physical recovery is a **unitary gate applied to a state**, so both the error and the recovery are
modelled as `Evolution`s (Pauli `Z` gates) and acted through `evolvePure`, rather than as
observables — the operator `Z₁Z₂Z₃` in the exercise is a corrective operation, not a measurement.
The equalities are `PureState` equalities: after error + recovery the encoded state is literally
recovered. The supporting operator identities on the cat vectors, and the lift to the normalised
cat states, are in `AxQM/Postulates/API/ShorCodePhaseFlip.lean`, as the supporting results of
Exercise 10.3 are for its statement.

N&C Exercise 10.6, p. 433.
-/

noncomputable section

namespace AxQM

/-- **Exercise 10.6 — a phase flip flips the block sign.** A phase-flip error `Zᵢ` on *any* of the
block's three qubits (`i : Fin 3`) maps the cat state `catBlockState σ` to the oppositely-signed
cat state `catBlockState (σ+1)`: this is N&C's "`|000⟩+|111⟩` to `|000⟩−|111⟩`, and vice versa".
Immediate from the operator identity `blockPhaseFlip_op_catBlockVec` via the unitary-normalisation
bridge `Evolution.evolvePure_normalize_of_op_eq`. -/
theorem blockPhaseFlip_evolvePure_catBlockState (i : Fin 3) (σ : Fin 2) :
    (blockPhaseFlip i).evolvePure (catBlockState σ) = catBlockState (σ + 1) :=
  (blockPhaseFlip i).evolvePure_normalize_of_op_eq (catBlockVec_ne_zero σ)
    (catBlockVec_ne_zero (σ + 1)) (blockPhaseFlip_op_catBlockVec i σ)

/-- **Exercise 10.6 — the recovery operator `Z₁Z₂Z₃` flips the block sign.** `blockZGate` maps
`catBlockState σ` to `catBlockState (σ+1)`, the same sign flip a single-qubit phase flip performs.
Immediate from `blockZGate_op_catBlockVec` via `Evolution.evolvePure_normalize_of_op_eq`. -/
theorem blockZGate_evolvePure_catBlockState (σ : Fin 2) :
    blockZGate.evolvePure (catBlockState σ) = catBlockState (σ + 1) :=
  blockZGate.evolvePure_normalize_of_op_eq (catBlockVec_ne_zero σ)
    (catBlockVec_ne_zero (σ + 1)) (blockZGate_op_catBlockVec σ)

/-- **Exercise 10.6 — recovery from a phase flip via `Z₁Z₂Z₃`.** Applying the recovery gate
`Z₁Z₂Z₃` (`blockZGate`) *after* a phase flip on *any* of the block's three qubits
(`blockPhaseFlip i`, `i : Fin 3`) returns the block to its original encoded state `catBlockState σ`.
Both the error and the recovery flip the block's sign (`σ ↦ σ+1`,
`blockPhaseFlip_evolvePure_catBlockState` / `blockZGate_evolvePure_catBlockState`), so their
composite restores it (`σ+1+1 = σ` in `Fin 2`). The single operator `Z₁Z₂Z₃` corrects the
phase-flip error irrespective of which of the three qubits it occurred on — the content of the
exercise. -/
theorem blockPhaseFlip_recovery (i : Fin 3) (σ : Fin 2) :
    blockZGate.evolvePure ((blockPhaseFlip i).evolvePure (catBlockState σ)) = catBlockState σ := by
  rw [blockPhaseFlip_evolvePure_catBlockState, blockZGate_evolvePure_catBlockState]
  congr 1
  fin_cases σ <;> rfl

end AxQM
