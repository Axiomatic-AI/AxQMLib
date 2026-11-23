/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ToffoliGateTeleportMeasure
import AxQM.Postulates.API.RelativePhaseToffoli
import AxQM.Postulates.API.ToffoliPauliPropagation

/-!
# AxQM.Postulates.API — the byproduct correction of Toffoli gate teleportation

The **classically-controlled correction stage** of the fault-tolerant Toffoli gate-teleportation
circuit of Nielsen & Chuang **Exercise 10.68** (the Figure on p. 488, part (2)). The measurement
step (`AxQM/Postulates/API/ToffoliGateTeleportMeasure.lean`) shows that measuring the three data
qubits with outcome `(m₁, m₂, m₃)` collapses the pre-measurement state to a single branch whose
**ancilla block** (the left qubit of each ancilla↔data pair) is left in the computational-basis
state

  `|x ⊕ m₁, y ⊕ m₂, (x ⊕ m₁)·(y ⊕ m₂) ⊕ z⟩`

(`toffoliDataMeasurement_op_toffoliTeleportPreMeasure`), with branch amplitude
`2⁻³ᐟ² (-1)^{m₃·z}`. This file supplies the **outcome-conditioned corrections** that turn that
collapsed ancilla into the exact `Toffoli|xyz⟩` — the Toffoli analogue of the single-qubit Pauli
corrections `pauliByproduct` of the CNOT gate-teleportation identity
(`cnotGateTeleportation_identity`, Problem 4.6).

## The correction, and why it recovers the Toffoli

The measured-swap gadgets leave the raw byproducts `X₁^{m₁} X₂^{m₂} Z₃^{m₃}` between the swap
network and the Toffoli; the Exercise 10.67 propagation rules move the Toffoli left past them,
depositing the **propagated** Clifford
`Bₘ = X₁^{m₁} CNOT₂₃^{m₁} · X₂^{m₂} CNOT₁₃^{m₂} · Z₃^{m₃} CZ₁₂^{m₃}` (the outcome-conditioned form
of `toffoliSwapByproductsPropagated`, `AxQM/NC/Ch10/Exercise10_68_FTToffoli.lean`) on the ancilla.
The classically-controlled **correction** the circuit applies is `Bₘ⁻¹ = Bₘ†` (every factor a
self-inverse Pauli/`CNOT`/`CZ`), split here into

* the **control corrections** `toffoliTeleportControlCorrection m₁ m₂` — the `X`-byproduct part
  `CNOT₁₃^{m₂} X₂^{m₂} · CNOT₂₃^{m₁} X₁^{m₁}` (the inverse of the propagated `X` byproducts,
  depending only on the two `Z`-basis control outcomes `m₁, m₂`), which recovers the **exact**
  Toffoli of the data on the ancilla; and
* the **target phase correction** `Z₃^{m₃} CZ₁₂^{m₃}` (the inverse of the propagated `Z` byproduct
  from the `X`-basis target measurement, depending on `m₃`), which contributes only the global sign
  `(-1)^{m₃·z}` on the ancilla output — physically irrelevant on its own, and exactly cancelling the
  branch amplitude's `(-1)^{m₃·z}` so the corrected branch is `2⁻³ᐟ² Toffoli|xyz⟩` for **every**
  outcome.

## What is formalised

* `evolPow m U` — the gate `U` applied *conditioned on the classical outcome bit* `m` (`U^m`:
  identity if `m = 0`, `U` if `m = 1`), with which the outcome-dependent byproduct corrections are
  assembled.

* `toffoliTeleportAncillaBranch x y z m₁ m₂` — the **collapsed ancilla block**
  `|x ⊕ m₁, y ⊕ m₂, (x ⊕ m₁)·(y ⊕ m₂) ⊕ z⟩`, the definite computational-basis state the three
  data-qubit measurements leave on the ancilla wires (the left qubit of each pair of
  `toffoliDataMeasurement_op_toffoliTeleportPreMeasure`).

* `toffoliTeleportControlCorrection m₁ m₂` — the classically-controlled **`X`-byproduct correction**
  `CNOT₁₃^{m₂} X₂^{m₂} CNOT₂₃^{m₁} X₁^{m₁}`, and
  `toffoliTeleportControlCorrection_evolvePure_ancillaBranch`: for every control outcome `(m₁, m₂)`
  it maps the collapsed ancilla to **exactly** `Toffoli|xyz⟩` —
  the Toffoli of the *original* data recovered on the ancilla. (The two `X` corrections fix the
  controls to `x, y`; the propagated `CNOT`s then fix the target to `z ⊕ xy`.)

* `toffoliTeleportCorrection m₁ m₂ m₃` — the **full** classically-controlled correction `Bₘ†`
  (control corrections followed by the target phase correction `Z₃^{m₃} CZ₁₂^{m₃}`), and
  `toffoliTeleportCorrection_op_ancillaBranch`: it maps the collapsed ancilla to
  `(-1)^{m₃·z} Toffoli|xyz⟩` (the global sign is the `Z`-byproduct phase).

* `toffoliTeleportCorrection_op_ancillaBranch_toffoli` — applying the full correction to the
  collapsed ancilla-block *value* *carrying its branch sign* `(-1)^{m₃·z}` yields the **exact**
  `Toffoli|xyz⟩`, phase-free — the two `(-1)^{m₃·z}` factors cancel. This is the correction's
  correctness on the ancilla-block *value* the collapse produces; it holds for every one of the
  eight outcomes.

**Not proved here.** These lemmas establish that the correction is correct *on the collapsed
ancilla value*; they do not compose the correction with the actual measured state on the
coupled-pairs register. The assembled identity — the Toffoli analogue of
`bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen` (Problem 4.6) — applies the
correction *lifted onto the ancilla wires* (via `toffoliTeleportReshape` / `onLeft` / `onRight`) to
the actual `toffoliDataMeasurement.postMeasurement` state and reads off the ancilla marginal
(`State.reducedLeft`), showing that it equals `(Toffoli|xyz⟩).toState` for every outcome. The
de-interleaving reshape action and the corrected-branch factorisation it needs are in
`AxQM/Postulates/API/ToffoliGateTeleportCompose.lean`.
-/

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace AxQM

/-- **A gate applied conditioned on a classical outcome bit** `m : Fin 2`: `U^m`, i.e. the identity
when `m = 0` and `U` when `m = 1`. The classically-controlled byproduct corrections of
Exercise 10.68 are assembled from elementary gates by conditioning each on its measurement
outcome via `evolPow`.
The `Evolution`-level analogue of the single-qubit `targetXPow`. -/
def evolPow {S : QSystem} (m : Fin 2) (U : Evolution S) : Evolution S :=
  if m = 0 then Evolution.id else U

@[simp] theorem evolPow_zero {S : QSystem} (U : Evolution S) : evolPow 0 U = Evolution.id := rfl

@[simp] theorem evolPow_one {S : QSystem} (U : Evolution S) : evolPow 1 U = U := rfl

/-- **The collapsed ancilla block** of the Toffoli gate-teleportation measurement: for input `|xyz⟩`
and outcome `(m₁, m₂, m₃)`, measuring the three data qubits leaves the three ancilla wires (the left
qubit of each ancilla↔data pair) in the computational-basis state

  `|x ⊕ m₁, y ⊕ m₂, (x ⊕ m₁)·(y ⊕ m₂) ⊕ z⟩`

— the ancilla factor of the single surviving branch of
`toffoliDataMeasurement_op_toffoliTeleportPreMeasure` (independent of the target outcome `m₃`, which
affects only the branch phase). This is the state the classically-controlled corrections act on. -/
def toffoliTeleportAncillaBranch (x y z m₁ m₂ : Fin 2) : PureState (qubit ⊗ (qubit ⊗ qubit)) :=
  qubitThreeBasis (x + m₁, y + m₂, (x + m₁) * (y + m₂) + z)

/-- **The classically-controlled `X`-byproduct correction** of Exercise 10.68, conditioned on the
two control-qubit (`Z`-basis) measurement outcomes `(m₁, m₂)`:

  `CNOT₁₃^{m₂} · X₂^{m₂} · CNOT₂₃^{m₁} · X₁^{m₁}`

— the inverse `Bₘ†` of the propagated `X` byproducts
`X₁^{m₁} CNOT₂₃^{m₁} · X₂^{m₂} CNOT₁₃^{m₂}` that the Exercise 10.67 rules deposit when the
Toffoli is moved left past `X₁^{m₁} X₂^{m₂}`. Here
`X₁ = pauliXGate.onLeft (qubit ⊗ qubit)` and `X₂ = (pauliXGate.onLeft qubit).onRight qubit` are the
control-ancilla bit flips, `CNOT₂₃ = cnotGate.onRight qubit` and `CNOT₁₃ = cnotFirstThirdGate` the
propagated `CNOT`s, each conditioned on its outcome via `evolPow`. -/
def toffoliTeleportControlCorrection (m₁ m₂ : Fin 2) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (evolPow m₂ cnotFirstThirdGate).comp
    ((evolPow m₂ ((pauliXGate.onLeft qubit).onRight qubit)).comp
      ((evolPow m₁ (cnotGate.onRight qubit)).comp
        (evolPow m₁ (pauliXGate.onLeft (qubit ⊗ qubit)))))

set_option maxHeartbeats 3200000 in
-- The `fin_cases` sweep over the two outcomes and the three input bits (32 branches), each firing
-- the gate truth tables on the 64-dimensional `qubit ⊗ (qubit ⊗ qubit)` register, exceeds the
-- default elaboration budget.
/-- **The control corrections recover the exact Toffoli of the data on the ancilla.** For every
input `|xyz⟩` and every pair of control-measurement outcomes `(m₁, m₂)`, applying the classically
controlled `X`-byproduct correction to the collapsed ancilla block yields exactly `Toffoli|xyz⟩`:

  `toffoliTeleportControlCorrection m₁ m₂ (|x ⊕ m₁, y ⊕ m₂, (x ⊕ m₁)·(y ⊕ m₂) ⊕ z⟩)
      = Toffoli|xyz⟩`.

The two bit flips `X₁^{m₁}, X₂^{m₂}` restore the ancilla controls to `x, y`, and the propagated
`CNOT`s then repair the target from `(x ⊕ m₁)·(y ⊕ m₂) ⊕ z` to `z ⊕ xy` (all cross terms cancel in
`Fin 2`). Verified on the computational basis (`fin_cases` on the outcomes and the input, then the
gate truth tables). -/
theorem toffoliTeleportControlCorrection_evolvePure_ancillaBranch (x y z m₁ m₂ : Fin 2) :
    (toffoliTeleportControlCorrection m₁ m₂).evolvePure (toffoliTeleportAncillaBranch x y z m₁ m₂)
      = toffoliGate.evolvePure (qubitThreeBasis (x, y, z)) := by
  simp only [toffoliTeleportAncillaBranch, qubitThreeBasis, toffoliTeleportControlCorrection,
    toffoliGate_evolvePure_qubitBasis]
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [evolPow, targetXPow, Evolution.evolvePure_comp, Evolution.id_evolvePure,
      Evolution.onLeft_evolvePure, Evolution.onRight_evolvePure, cnotGate_evolvePure_qubitBasis,
      cnotFirstThirdGate_evolvePure, pauliXGate_evolvePure_qubitBasis]

/-- **The full classically-controlled correction** `Bₘ†` of Exercise 10.68: the control corrections
`toffoliTeleportControlCorrection m₁ m₂` followed by the **target phase correction**
`Z₃^{m₃} · CZ₁₂^{m₃}` — the inverse of the propagated `Z` byproduct `Z₃^{m₃} CZ₁₂^{m₃}` left by the
`X`-basis measurement of the target data qubit (outcome `m₃`), with `Z₃ = (pauliZGate.onRight
qubit).onRight qubit` and `CZ₁₂ = controlledZLeftGate`, each conditioned on `m₃` via `evolPow`. This
is the complete correction the fault-tolerant circuit applies, exercising all three Exercise 10.67
propagation rules. -/
def toffoliTeleportCorrection (m₁ m₂ m₃ : Fin 2) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (evolPow m₃ controlledZLeftGate).comp
    ((evolPow m₃ ((pauliZGate.onRight qubit).onRight qubit)).comp
      (toffoliTeleportControlCorrection m₁ m₂))

set_option maxHeartbeats 3200000 in
-- Reducing the control correction on the 64-dimensional register and then the `Z`/`CZ` phase case
-- split over the target outcome and input bits exceeds the default elaboration budget.
/-- **The full correction recovers the Toffoli up to the byproduct phase.** For every input `|xyz⟩`
and every outcome `(m₁, m₂, m₃)`, applying the full classically-controlled correction to the
collapsed ancilla block yields `Toffoli|xyz⟩` up to the global sign `(-1)^{m₃·z}`:

  `toffoliTeleportCorrection m₁ m₂ m₃ (|x ⊕ m₁, y ⊕ m₂, (x ⊕ m₁)·(y ⊕ m₂) ⊕ z⟩)
      = (-1)^{m₃·z} Toffoli|xyz⟩`.

The control corrections restore the exact Toffoli
(`toffoliTeleportControlCorrection_evolvePure_ancillaBranch`); the target phase correction
`Z₃^{m₃} CZ₁₂^{m₃}` then contributes `(-1)^{m₃·(z ⊕ xy)} (-1)^{m₃·xy} = (-1)^{m₃·z}` on the Toffoli
output `|x, y, z ⊕ xy⟩` (`pauliZGate_onRight_onRight_op_apply_qubitBasis`,
`controlledZLeftGate_op_apply_qubitBasis`). -/
theorem toffoliTeleportCorrection_op_ancillaBranch (x y z m₁ m₂ m₃ : Fin 2) :
    (toffoliTeleportCorrection m₁ m₂ m₃).op (toffoliTeleportAncillaBranch x y z m₁ m₂).vec
      = ((-1 : ℂ) ^ (m₃.val * z.val)) •
          (toffoliGate.evolvePure (qubitThreeBasis (x, y, z))).vec := by
  rw [toffoliTeleportCorrection, Evolution.comp_op, ContinuousLinearMap.comp_apply,
    Evolution.comp_op, ContinuousLinearMap.comp_apply, ← Evolution.evolvePure_vec,
    toffoliTeleportControlCorrection_evolvePure_ancillaBranch]
  simp only [qubitThreeBasis, toffoliGate_evolvePure_qubitBasis]
  fin_cases m₃
  · simp only [Fin.zero_eta, Fin.isValue, evolPow_zero, Evolution.id_op, PureState.tmul_vec,
      qubitBasis_vec, FunLike.coe_one_eq_id, one_apply_eq_self, zero_mul, pow_zero]
    exact (one_smul ℂ _).symm
  · simp only [Fin.mk_one, Fin.isValue, evolPow_one]
    rw [pauliZGate_onRight_onRight_op_apply_qubitBasis, map_smul,
      controlledZLeftGate_op_apply_qubitBasis, smul_smul, ← pow_add]
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp

/-- **The full correction, applied to the *signed* collapsed ancilla-block value, recovers the exact
Toffoli** (Nielsen & Chuang, Exercise 10.68, part (2)). Applying the full correction to the
collapsed
ancilla-block *value* *carrying its branch sign* `(-1)^{m₃·z}` — the sign with which the branch
appears in the collapse `toffoliDataMeasurement_op_toffoliTeleportPreMeasure` — yields
`Toffoli|xyz⟩`
with no residual phase:

  `toffoliTeleportCorrection m₁ m₂ m₃ ((-1)^{m₃·z} • |x ⊕ m₁, y ⊕ m₂, (x ⊕ m₁)·(y ⊕ m₂) ⊕ z⟩)
      = Toffoli|xyz⟩`.

The correction contributes a second `(-1)^{m₃·z}` (`toffoliTeleportCorrection_op_ancillaBranch`),
and the two signs cancel (`(-1)^{2 m₃ z} = 1`), so the corrected ancilla-block value is
`Toffoli|xyz⟩`
for every one of the eight outcomes.

This establishes the correction's correctness *on the ancilla-block value* the collapse produces; it
is the ancilla-block core of Exercise 10.68's fault-tolerant Toffoli. The **assembled** identity —
composing this correction (lifted onto the ancilla wires) with the *actual*
`toffoliDataMeasurement.postMeasurement` state on the coupled-pairs register and reading off the
ancilla marginal `= (Toffoli|xyz⟩).toState` (the Problem 4.6 standard,
`bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen`) — is not proved here (see
the module docstring); it needs the de-interleaving reshape action and the corrected-branch
factorisation. -/
theorem toffoliTeleportCorrection_op_ancillaBranch_toffoli (x y z m₁ m₂ m₃ : Fin 2) :
    (toffoliTeleportCorrection m₁ m₂ m₃).op
        (((-1 : ℂ) ^ (m₃.val * z.val)) • (toffoliTeleportAncillaBranch x y z m₁ m₂).vec)
      = (toffoliGate.evolvePure (qubitThreeBasis (x, y, z))).vec := by
  rw [map_smul, toffoliTeleportCorrection_op_ancillaBranch, smul_smul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_smul]

end AxQM
