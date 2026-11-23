/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.QubitThree
import AxQM.Postulates.API.Swap
import AxQM.Postulates.API.SwapCircuit
import AxQM.Postulates.API.RelativePhaseToffoli
import AxQM.Postulates.API.ControlBranchExt
import AxQM.Postulates.API.ToffoliGateTeleportCompose
import AxQM.NC.Ch10.Exercise10_67

/-!
# Nielsen & Chuang, Exercise 10.68 (Fault-tolerant Toffoli gate construction)

*(N&C §10.6.2, p. 488.)*

Fault-tolerant Toffoli gate construction via swap+Toffoli circuit and commutation moves (Steane
code).

This is the Toffoli analogue of the fault-tolerant π/8-gate construction of Exercise 10.66: instead
of applying the non-Clifford gate directly to the data, one *swaps the data onto fresh qubits* and
then commutes the gate leftward until it acts only on a fixed, known input — turning it into an
offline resource-state preparation (`toffoliAncilla`, `|Θ_T⟩ = ½(|000⟩+|010⟩+|100⟩+|111⟩)`) that is
consumed by gate teleportation. The upshot (part (3)) is that a Toffoli — which is *not* transversal
on the Steane code — can nonetheless be implemented fault-tolerantly.

## What is formalised here

* **Part (1)** — `swapThenToffoli` and `swapThenToffoli_evolvePure_ancillaZero`: the circuit that
  swaps the (unknown) three-qubit data block `|ψ⟩` with a known `|000⟩` block and then applies a
  Toffoli to the block now holding the data does compute the Toffoli of the data,
  `|ψ⟩ ⊗ |000⟩ ↦ |000⟩ ⊗ Toffoli|ψ⟩`. `swapThenToffoli_evolvePure_qubitThreeBasis` records the
  explicit computational-basis truth table `|xyz⟩ ⊗ |000⟩ ↦ |000⟩ ⊗ |x, y, z ⊕ xy⟩`.
* **Part (2), the commutation core** — `toffoliGate_comp_swapByproducts_propagates`: *moving the
  final Toffoli all the way back to the left side* begins by commuting it leftward past the
  classically-controlled byproduct Paulis the swap gadgets leave on the ancilla wires — `X` on the
  two control ancillas (qubits 1, 2) and `Z` on the target ancilla (qubit 3), read off the Figure on
  p. 488. This is exactly where "the commutation rules from Exercise 10.67" are used:
  `T · (X₁·X₂·Z₃) = (X₁·CNOT₂₃ · X₂·CNOT₁₃ · Z₃·CZ₁₂) · T`, so the Toffoli passes to the left
  (into the ancilla-preparation box) and leaves the propagated Clifford byproducts behind. It rests
  on the control-1 and target rules of Exercise 10.67 together with their control-2 companion,
  `toffoliGate_comp_pauliXGate_control2_propagates` (`T · X₂ = (X₂·CNOT₁₃)·T`, whose byproduct
  `CNOT₁₃` is the pre-existing long-range `CNOT` `cnotFirstThirdGate` (control 1 → target),
  reused from `Postulates/API/RelativePhaseToffoli`).
* **Part (2), operator-level move** — `swapThenToffoli_eq_swap_comp_toffoliOnLeft`: read as a bare
  operator identity (the swap network taken as the ideal deterministic `Evolution.swap`), "moving
  the final Toffoli all the way back to the left side" is `swapThenToffoli = SWAP · (T ⊗ 1)` — the
  Toffoli sits at the *front* of the circuit. `swap_comp_toffoliOnLeft_evolvePure_ancillaZero`
  records that this gate-moved circuit still computes the Toffoli (`|ψ⟩ ⊗ |000⟩ ↦ |000⟩ ⊗
  Toffoli|ψ⟩`). This is the deterministic complement of the commutation core: the core commutes the
  Toffoli past the *measured-swap byproducts* (the fault-tolerant realisation), this identity
  commutes it past the *ideal swap* (the operator content of the move).
* **The resource state (the leftmost dotted box)** — `toffoliAncilla`, the entangled ancilla
  `|Θ_T⟩ = ½(|000⟩+|010⟩+|100⟩+|111⟩)` prepared by loading the moved Toffoli onto the two
  Hadamarded control wires, `|Θ_T⟩ = C²(X)(|+⟩|+⟩|0⟩)` (`toffoliAncilla_prep_ketPlus`,
  `toffoliAncilla_vec`). It is the Toffoli analogue of the π/8-gate ancilla
  `|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2` of Exercise 10.66, and the state Exercise 10.72 asks to prepare
  fault-tolerantly. It is defined in `AxQM/Postulates/API/ToffoliAncilla.lean` (shared with
  Exercise 10.72).
* **Part (2), the byproduct-correction step** — `toffoliSwapByproducts`,
  `toffoliSwapByproductsPropagated`, `toffoliSwapByproductCorrection` and
  `toffoliSwapByproductCorrection_comp_toffoliGate_comp_byproducts`: applying the classically
  controlled corrections `B† = toffoliSwapByproductCorrection` (the inverse of the propagated
  byproducts `B`) after the moved Toffoli-with-byproducts recovers the clean Toffoli,
  `B† · (T · X₁X₂Z₃) = T`. This is the correction stage of the measured gate-teleportation identity
  (see the Scope section) — the classically-controlled Cliffords the measurement outcomes trigger
  undo the swap byproducts, leaving the exact Toffoli of the data.

## The role of the swap, and its fault-tolerant realisation

The "task" of part (1) is exactly the deterministic operation *swap the data block onto the fresh
`|000⟩` block, then Toffoli that block* — which is what `swapThenToffoli` is, an honest `Evolution`
on the six-qubit register `(qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit))`. N&C's "following
circuit" realises the *swap* one data qubit at a time using the measured-swap gadget of Exercise
10.65 (a single `CNOT`, a Hadamard, a computational-basis measurement of the control qubit, and a
classically-controlled Pauli correction): that gadget was already shown to accomplish the swap task,
`measuredSwapCircuit1_corrected` / `measuredSwapCircuit2_corrected`, so composing three of them with
the block Toffoli reproduces `swapThenToffoli`. This is the point of the construction — the swap can
be done with the fault-tolerant operations of §10.6, so it is the swap, not a bare `SWAP` gate, that
matters physically; the deterministic identity here isolates *what the circuit computes*.

## Supporting results

The statements below use `Evolution.swap`, `toffoliGate`, `Evolution.onLeft`, `Evolution.onRight`,
`Evolution.comp`, `Evolution.evolvePure`, `PureState.tmul` and `qubitThreeBasis`. They rest on
`toffoliAncilla` in `AxQM/Postulates/API/ToffoliAncilla.lean`, the measured-swap results in
`AxQM/Postulates/API/OneBitTeleportation.lean`, and the Toffoli propagation rules in
`AxQM/Postulates/API/ToffoliPauliPropagation.lean` used by Exercise 10.67.

## Design notes

* **Strength of the statement.** `swapThenToffoli_evolvePure_ancillaZero` holds for an *arbitrary*
  three-qubit data state `|ψ⟩` (not just computational-basis inputs) — the swap moves the whole
  block and the Toffoli then acts as `toffoliGate.evolvePure`; no dimension is specialised. The
  basis form is a corollary. The known register is exactly `|000⟩` as in the exercise.
* **Register layout.** The data occupies the *left* block and the fresh `|000⟩` the *right* block;
  `Evolution.swap` exchanges the two identical three-qubit blocks and `toffoliGate.onRight` then
  acts on the right block, now holding the data — so the result is `|000⟩ ⊗ Toffoli|ψ⟩`.
* **Elaboration cost.** `swapThenToffoli` is an `Evolution` on the 64-dimensional composite
  `(qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit))`; composing the two blockwise gates there
  needs a raised `maxHeartbeats` (as for other large-composite `Evolution`s in the library).

## Scope: the measured gate-teleportation identity and part (3)

The mathematical payoff of Exercise 10.68 is the **measured gate-teleportation identity** that
implements the Toffoli: the offline `toffoliAncilla` preparation (the leftmost dotted box), the
three data↔ancilla coupling `CNOT`s, the three data-qubit measurements (eight outcome branches),
and the classically-controlled Clifford corrections that recover `Toffoli|ψ⟩` on the ancilla — the
Toffoli analogue of `cnotGateTeleportation_identity` (Problem 4.6) and of the resulting-circuit
correctness `Concrete.piEighthCircuitOut_measure_zero` / `_measure_one` of the π/8 template
(Exercise 10.66). It uses the measurement / Born / classical-control machinery, the measured-swap
gadgets of Exercise 10.65, `toffoliAncilla`, and the Exercise 10.67 propagation rules, and is
comparable to the `CNOT` gate-teleportation development `GateTeleportProtocolReshape` /
`GateTeleportResource` / `GateTeleportProtocolCnot` / `GateTeleportationIdentity`, with coupling
here by measured-swap teleportation on a 64-dimensional register rather than Bell measurement:

* **Formalised:** the swap-then-Toffoli identity (part 1); the operator-level "move the Toffoli to
  the front" (part 2); the Exercise-10.67-consuming byproduct commutation
  `toffoliGate_comp_swapByproducts_propagates` (part 2 core); the resource state `toffoliAncilla`
  (`Postulates/API/ToffoliAncilla`); the **byproduct-correction step**
  `toffoliSwapByproductCorrection_comp_toffoliGate_comp_byproducts`: the classically-controlled
  corrections `B†` undo the propagated byproducts and recover the clean Toffoli
  (`B† · (T · X₁X₂Z₃) = T`); and the **data↔ancilla coupling and pre-measurement gate-teleportation
  state** (`Postulates/API/ToffoliGateTeleport`): `toffoliTeleportCoupling`
  (`CNOT(a₁→d_x) · CNOT(a₂→d_y) · CNOT(d_z→a₃)`), its basis truth table
  `toffoliTeleportCoupling_evolvePure_qubitBasis`, and — coupling the AND magic state to the data —
  `toffoliTeleportCoupling_op_toffoliTeleportReshapedInput`:
  `coupling (½ Σ_{a,b} |a,x⟩|b,y⟩|a·b, z⟩) = ½ Σ_{a,b} |a, x⊕a⟩|b, y⊕b⟩|a·b ⊕ z, z⟩` (the Toffoli
  analogue of the π/8 eq. 10.119); and the **reshape isometry realising the resource-consuming
  input** (`Postulates/API/ToffoliGateTeleportReshape`): `toffoliTeleportReshape`, the interleaving
  `QSystem.Iso` `(a₁ ⊗ (a₂ ⊗ a₃)) ⊗ (x ⊗ (y ⊗ z)) ≃ₛ (a₁ ⊗ x) ⊗ ((a₂ ⊗ y) ⊗ (a₃ ⊗ z))`, with
  `toffoliTeleportReshape_toIsometry_toffoliAncilla_tmul`:
  `reshape(toffoliAncilla ⊗ |xyz⟩) = toffoliTeleportReshapedInput` — identifying the coupling's
  abstract input with the honest reshape of the *prepared* offline resource beside the data (so the
  pre-measurement state is genuinely the coupling applied to `|Θ_T⟩ ⊗ |xyz⟩`); and the
  **eight-outcome branch decomposition** (`Postulates/API/ToffoliGateTeleportBranches`):
  `toffoliTeleportCoupling_op_reshape_toffoliAncilla_tmul` (and the abstract-input form
  `..._toffoliTeleportReshapedInput_hadamardBranches`), which expands the target data qubit `|z⟩`
  over the `X` eigenbasis (`qubitBasis_vec_eq_invSqrt2_sum_hadamard`) to exhibit the three
  data-qubit measurements as the manifest superposition
  `2⁻³ᐟ² Σ_{a,b,m₃} (-1)^{m₃·z} |a, x⊕a⟩|b, y⊕b⟩|a·b ⊕ z, H|m₃⟩⟩` — one branch per joint outcome
  `(d_x, d_y, d_z^X) = (x⊕a, y⊕b, m₃)` (the two controls in the `Z` basis, the target in the `X`
  basis), the Toffoli analogue of the CNOT correction-free branch form
  `gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_teleport`; and the **three data-qubit
  measurements read through `Measurement`**
  (`Postulates/API/ToffoliGateTeleportMeasure`): `toffoliDataMeasurement` (the joint measurement of
  the three data qubits — `d_x, d_y` in the `Z` basis, `d_z` in the `X` basis — each on the data
  qubit of its ancilla↔data pair), the **collapse identity**
  `toffoliDataMeasurement_op_toffoliTeleportPreMeasure`: measuring with outcome `(m₁, m₂, m₃)`
  collapses the honest pre-measurement state `toffoliTeleportPreMeasure` (offline ancilla prep,
  reshape, coupling) to the single branch
  `2⁻³ᐟ² (-1)^{m₃·z} |x⊕m₁, m₁⟩|y⊕m₂, m₂⟩|(x⊕m₁)·(y⊕m₂) ⊕ z, H|m₃⟩⟩`, and the **Born rule**
  `toffoliDataMeasurement_bornProb_pos` (every one of the eight outcomes is possible); and the
  **classically-controlled byproduct corrections**
  (`Postulates/API/ToffoliGateTeleportCorrection`). The collapse leaves the ancilla block (the left
  qubit of each pair) in
  `toffoliTeleportAncillaBranch x y z m₁ m₂ = |x⊕m₁, y⊕m₂, (x⊕m₁)·(y⊕m₂) ⊕ z⟩`. The
  outcome-conditioned correction `Bₘ⁻¹` — the inverse of the Exercise-10.67-propagated byproducts —
  is built with `evolPow` (a gate applied conditioned on its classical outcome bit); its
  `X`-byproduct part `toffoliTeleportControlCorrection m₁ m₂` recovers the **exact** Toffoli of the
  ancilla-block value for every control outcome
  (`toffoliTeleportControlCorrection_evolvePure_ancillaBranch`:
  `Bₘ⁻¹|x⊕m₁, y⊕m₂, (x⊕m₁)·(y⊕m₂) ⊕ z⟩ = Toffoli|xyz⟩`), and the full correction
  `toffoliTeleportCorrection m₁ m₂ m₃` (adding the target `X`-measurement's `Z`-byproduct correction
  `Z₃^{m₃} CZ₁₂^{m₃}`, Exercise 10.67(b)) recovers it up to the global phase `(-1)^{m₃·z}`
  (`toffoliTeleportCorrection_op_ancillaBranch`); since that phase is the branch amplitude's sign,
  `toffoliTeleportCorrection_op_ancillaBranch_toffoli` shows the corrected ancilla-block value is,
  phase-free, `Toffoli|xyz⟩` for every outcome.

* **The assembled measured identity.** The whole circuit is
  composed end to end for an **arbitrary input state** `ψ`:
  `toffoliDataMeasurement_corrected_reducedLeft_toffoliTeleportPreMeasureGen` (below) — the Toffoli
  analogue of Problem 4.6's `bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen`
  (also over an arbitrary input, as a gate claim demands). Measuring the three data qubits of the
  honest pre-measurement state (`toffoliDataMeasurement.postMeasurement`, Postulate 4),
  **de-interleaving** the coupled-pairs register into ancilla block ⊗ data block
  (`State.congr toffoliTeleportReshape.symm`), applying the classically-controlled correction on the
  ancilla wires (`(toffoliTeleportCorrection m₁ m₂ m₃).onLeft`, `Evolution.evolve`), and reading off
  the ancilla marginal (`State.reducedLeft`) gives `(toffoliGate.evolvePure ψ).toState` for
  **every** input and **every** outcome (the eight-basis truth-table form
  `toffoliDataMeasurement_corrected_reducedLeft_toffoliTeleportPreMeasure` is its `ψ = |xyz⟩`
  corollary). The de-interleaving reshape action (`toffoliTeleportReshape_symm_toIsometry_tmul`),
  the general-input corrected-branch factorisation
  (`toffoliTeleportCorrection_onLeft_evolvePure_congr_normalizeGen` — the corrected, de-interleaved,
  normalised branch is the product `Toffoli(ψ) ⊗ (data residual)`), and its extension off the
  computational basis by `Module.Basis.ext` live in
  `Postulates/API/ToffoliGateTeleportCompose`; the assembled identity is the theorem
  below.

* **Part (3), the Steane-code fault-tolerance argument.** "Assuming the ancilla preparation can be
  done fault-tolerantly, show that this circuit gives a fault-tolerant implementation of the Toffoli
  using the Steane code" is a single-fault error-propagation argument about the *fault-tolerance*
  of the whole procedure. The postulate framework has no fault-tolerance vocabulary (no
  fault-locations model, no single-fault propagation calculus, no transversality framework) — the
  same boundary recorded in `AxQM/NC/Ch10/Problem10_5.lean` for "fault-tolerant stabilizer state
  preparation" and "normalizer gates applied transversally". The offline resource whose
  fault-tolerant
  preparation part (3) assumes is `toffoliAncilla` (Exercise 10.72), formalised as a state; the
  fault-tolerance of its preparation and of the encoded measurements is not formalised.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

set_option maxHeartbeats 800000 in
-- `Evolution` on the 64-dimensional composite `T₃ ⊗ T₃`: composing the two blockwise gates
-- (`toffoliGate.onRight` and `Evolution.swap`) there exceeds the default elaboration budget.
/-- **The swap-then-Toffoli circuit** (Nielsen & Chuang, Exercise 10.68 part (1)): on the six-qubit
register `(qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit))` — a three-qubit *data* block (left)
and a three-qubit *known-`|000⟩`* block (right) — first `SWAP` the two blocks (`Evolution.swap`),
then apply a Toffoli to the right block, now holding the data (`toffoliGate.onRight`). It computes
the Toffoli of the data (`swapThenToffoli_evolvePure_ancillaZero`). The swap is realised
fault-tolerantly one qubit at a time by the measured-swap gadget of Exercise 10.65. -/
def swapThenToffoli :
    Evolution ((qubit ⊗ (qubit ⊗ qubit)) ⊗ (qubit ⊗ (qubit ⊗ qubit))) :=
  (toffoliGate.onRight (qubit ⊗ (qubit ⊗ qubit))).comp Evolution.swap

/-- **Part (1): the swap-then-Toffoli circuit computes the Toffoli.** Swapping an arbitrary
three-qubit data state `|ψ⟩` with the known `|000⟩` block and then applying a Toffoli to the block
now holding the data yields `|000⟩ ⊗ Toffoli|ψ⟩`:

  `swapThenToffoli (|ψ⟩ ⊗ |000⟩) = |000⟩ ⊗ Toffoli|ψ⟩`.

The `SWAP` moves `|ψ⟩` into the right block (`Evolution.swap_evolvePure_tmul`) and the
`toffoliGate.onRight` then acts there (`Evolution.onRight_evolvePure`). Holding for every input
`|ψ⟩`, this is the exact content of "swap the state you wish to transform with `|000⟩`, then apply a
Toffoli". -/
theorem swapThenToffoli_evolvePure_ancillaZero (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) :
    swapThenToffoli.evolvePure (ψ.tmul (qubitThreeBasis (0, 0, 0)))
      = (qubitThreeBasis (0, 0, 0)).tmul (toffoliGate.evolvePure ψ) := by
  rw [swapThenToffoli, Evolution.evolvePure_comp, Evolution.swap_evolvePure_tmul,
    Evolution.onRight_evolvePure]

/-- **Part (1), computational-basis truth table:** on a basis data input `|xyz⟩` the
swap-then-Toffoli circuit produces `|000⟩ ⊗ |x, y, z ⊕ xy⟩` — the Toffoli of `|xyz⟩` on the
swapped-in block, with the target `z` flipped exactly when both controls `x, y` are `1`
(`z + x * y` in `Fin 2`). -/
theorem swapThenToffoli_evolvePure_qubitThreeBasis (x y z : Fin 2) :
    swapThenToffoli.evolvePure ((qubitThreeBasis (x, y, z)).tmul (qubitThreeBasis (0, 0, 0)))
      = (qubitThreeBasis (0, 0, 0)).tmul (qubitThreeBasis (x, y, z + x * y)) := by
  rw [swapThenToffoli_evolvePure_ancillaZero]
  simp only [qubitThreeBasis]
  rw [toffoliGate_evolvePure_qubitBasis]

/-! ## Part (2): moving the final Toffoli to the left via the Exercise 10.67 rules

Part (1)'s circuit realises the swap one data qubit at a time with the measured-swap gadgets of
Exercise 10.65; each gadget leaves a classically-controlled **byproduct Pauli** on the ancilla wire
it swapped the data onto — `X` on the two control ancillas (qubits 1, 2) and `Z` on the target
ancilla (qubit 3), read off the Figure on p. 488. These byproducts sit *between* the swap network
and the final Toffoli. "Moving the final Toffoli all the way back to the left side" (part (2))
begins by commuting it leftward past those byproducts, and this is exactly where the Exercise 10.67
rules are used. -/

/-- **Exercise 10.67 (a), second-control form:** an `X` on the *second* control of the Toffoli
propagates, past the gate, to an `X` on that control together with a `CNOT` from the *first* control
to the target: `T · X₂ = (X₂ · CNOT₁₃) · T` on `qubit ⊗ (qubit ⊗ qubit)`, where `X₂ =
(pauliXGate.onLeft qubit).onRight qubit` and `CNOT₁₃ = cnotFirstThirdGate` — the pre-existing
long-range `CNOT` with control qubit 1 and target qubit 3 (`Postulates/API/RelativePhaseToffoli`,
where it is the `CNOT₁₃` of the Exercise 4.26 relative-phase Toffoli circuit). This is the
control-symmetric companion of `toffoliGate_comp_pauliXGate_control_propagates` (which handles the
first control); part (2) needs both, since the swap gadgets leave an `X` byproduct on each of the
two control ancillas. Both sides send `|q₁,q₂,q₃⟩` to `|q₁, q₂⊕1, q₃ ⊕ q₁·(q₂⊕1)⟩`; a permutation
identity, verified on the computational basis (mirroring the control-1 proof, with the `CNOT₁₃`
action supplied by the general `cnotFirstThirdGate_evolvePure`). -/
theorem toffoliGate_comp_pauliXGate_control2_propagates :
    toffoliGate.comp ((pauliXGate.onLeft qubit).onRight qubit)
      = (((pauliXGate.onLeft qubit).onRight qubit).comp cnotFirstThirdGate).comp toffoliGate := by
  apply threeQubit_evolution_ext
  intro q1 q2 q3
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue, Evolution.evolvePure_comp,
      Evolution.onLeft_evolvePure, Evolution.onRight_evolvePure, pauliXGate_evolvePure_qubitBasis,
      cnotFirstThirdGate_evolvePure, toffoliGate_evolvePure_qubitBasis, targetXPow_zero,
      targetXPow_one, Evolution.id_evolvePure] <;> rfl

/-- **Part (2), the commutation core: moving the final Toffoli left past the swap byproducts.**
The measured-swap gadgets of part (1) leave, between the swap network and the final Toffoli, the
byproduct Paulis `X₁ = pauliXGate.onLeft (qubit ⊗ qubit)` and
`X₂ = (pauliXGate.onLeft qubit).onRight qubit` on the two control ancillas and
`Z₃ = (pauliZGate.onRight qubit).onRight qubit` on the target
ancilla. Commuting the Toffoli leftward past all three, via the three Exercise 10.67 propagation
rules, moves it to the left (into the ancilla-preparation box) and leaves the propagated Clifford
byproducts behind:

  `T · (X₁·X₂·Z₃) = (X₁·CNOT₂₃ · X₂·CNOT₁₃ · Z₃·CZ₁₂) · T`,

with `CNOT₂₃ = cnotGate.onRight qubit`, `CNOT₁₃ = cnotFirstThirdGate`, and
`CZ₁₂ = controlledZLeftGate`.
This is the sole step of "moving the final Toffoli all the way back to the left side" that consumes
the Exercise 10.67 rules — the Toffoli then commutes trivially past the swap-coupling `CNOT`s.
Proved by rewriting with the control-1 (`toffoliGate_comp_pauliXGate_control_propagates`), control-2
(`toffoliGate_comp_pauliXGate_control2_propagates`) and target
(`toffoliGate_comp_pauliZGate_target_propagates`) rules, re-associating with `Evolution.comp_assoc`
to re-expose `T · Pᵢ` before each. -/
theorem toffoliGate_comp_swapByproducts_propagates :
    toffoliGate.comp ((pauliXGate.onLeft (qubit ⊗ qubit)).comp
        (((pauliXGate.onLeft qubit).onRight qubit).comp
          ((pauliZGate.onRight qubit).onRight qubit)))
      = (((pauliXGate.onLeft (qubit ⊗ qubit)).comp (cnotGate.onRight qubit)).comp
          ((((pauliXGate.onLeft qubit).onRight qubit).comp cnotFirstThirdGate).comp
            (((pauliZGate.onRight qubit).onRight qubit).comp controlledZLeftGate))).comp
        toffoliGate := by
  rw [← Evolution.comp_assoc toffoliGate (pauliXGate.onLeft (qubit ⊗ qubit))
        (((pauliXGate.onLeft qubit).onRight qubit).comp ((pauliZGate.onRight qubit).onRight qubit)),
    toffoliGate_comp_pauliXGate_control_propagates,
    Evolution.comp_assoc ((pauliXGate.onLeft (qubit ⊗ qubit)).comp (cnotGate.onRight qubit))
        toffoliGate
        (((pauliXGate.onLeft qubit).onRight qubit).comp ((pauliZGate.onRight qubit).onRight qubit)),
    ← Evolution.comp_assoc toffoliGate ((pauliXGate.onLeft qubit).onRight qubit)
        ((pauliZGate.onRight qubit).onRight qubit),
    toffoliGate_comp_pauliXGate_control2_propagates,
    Evolution.comp_assoc (((pauliXGate.onLeft qubit).onRight qubit).comp cnotFirstThirdGate)
        toffoliGate ((pauliZGate.onRight qubit).onRight qubit),
    toffoliGate_comp_pauliZGate_target_propagates,
    ← Evolution.comp_assoc (((pauliXGate.onLeft qubit).onRight qubit).comp cnotFirstThirdGate)
        (((pauliZGate.onRight qubit).onRight qubit).comp controlledZLeftGate) toffoliGate,
    ← Evolution.comp_assoc ((pauliXGate.onLeft (qubit ⊗ qubit)).comp (cnotGate.onRight qubit))
        ((((pauliXGate.onLeft qubit).onRight qubit).comp cnotFirstThirdGate).comp
          (((pauliZGate.onRight qubit).onRight qubit).comp controlledZLeftGate)) toffoliGate]

/-! ### Part (2), the byproduct correction: recovering the clean Toffoli

Moving the final Toffoli left past the measured-swap byproducts
(`toffoliGate_comp_swapByproducts_propagates`)
leaves the propagated Clifford operator `B = X₁·CNOT₂₃ · X₂·CNOT₁₃ · Z₃·CZ₁₂` sitting *after* the
Toffoli, on the three ancilla wires. In the fault-tolerant circuit these are the
**classically-controlled corrections** the measurement outcomes trigger; applying them (the inverse
`B†` of the propagated byproduct — each factor is a self-inverse Pauli/`CNOT`/`CZ`, so `B†` is the
same gates run in reverse) removes the byproduct and leaves the clean Toffoli acting on the data.
This is the correction step of the measured gate-teleportation identity; the remaining pieces (the
offline `toffoliAncilla` preparation, the three data↔ancilla coupling `CNOT`s, and the three data
measurements collapsing the eight outcome branches) are built separately. -/

/-- **The raw swap byproducts** left on the three ancilla wires by the measured-swap gadgets of part
(1), *before* the final Toffoli: `X` on each of the two control ancillas
(`X₁ = pauliXGate.onLeft (qubit ⊗ qubit)`, `X₂ = (pauliXGate.onLeft qubit).onRight qubit`) and `Z`
on the target ancilla (`Z₃ = (pauliZGate.onRight qubit).onRight qubit`), read off the Figure on
p. 488 (`X` corrections from the measured-swap circuit 2 on the controls, `Z` from circuit 1 on the
target). -/
def toffoliSwapByproducts : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (pauliXGate.onLeft (qubit ⊗ qubit)).comp
    (((pauliXGate.onLeft qubit).onRight qubit).comp ((pauliZGate.onRight qubit).onRight qubit))

/-- **The propagated swap byproducts** left *after* the Toffoli once it is moved to the front, i.e.
the right-hand Clifford of `toffoliGate_comp_swapByproducts_propagates`:
`B = X₁·CNOT₂₃ · X₂·CNOT₁₃ · Z₃·CZ₁₂` with `CNOT₂₃ = cnotGate.onRight qubit`,
`CNOT₁₃ = cnotFirstThirdGate`, `CZ₁₂ = controlledZLeftGate`. These are the Cliffords the Exercise
10.67 rules deposit on the ancilla when the Toffoli commutes past `toffoliSwapByproducts`. -/
def toffoliSwapByproductsPropagated : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  ((pauliXGate.onLeft (qubit ⊗ qubit)).comp (cnotGate.onRight qubit)).comp
    ((((pauliXGate.onLeft qubit).onRight qubit).comp cnotFirstThirdGate).comp
      (((pauliZGate.onRight qubit).onRight qubit).comp controlledZLeftGate))

/-- **The classically-controlled byproduct correction**: the inverse `B†` of the propagated
byproducts `toffoliSwapByproductsPropagated`. Since every factor of `B` is a self-inverse
Pauli/`CNOT`/`CZ`, `B† = B⁻¹` is exactly those same gates run in reverse — the corrections the
fault-tolerant circuit applies to the ancilla wires, conditioned on the three measurement outcomes,
to undo the byproducts. -/
def toffoliSwapByproductCorrection : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  toffoliSwapByproductsPropagated.adjoint

/-- **The commutation core, in the named-operator form.** `T · (X₁·X₂·Z₃) = B · T`: the Toffoli
moved left past the raw swap byproducts `toffoliSwapByproducts` deposits the propagated Cliffords
`toffoliSwapByproductsPropagated`. This is `toffoliGate_comp_swapByproducts_propagates` restated
over the two named byproduct operators, so the correction identity below reads cleanly. -/
theorem toffoliGate_comp_toffoliSwapByproducts :
    toffoliGate.comp toffoliSwapByproducts
      = toffoliSwapByproductsPropagated.comp toffoliGate := by
  rw [toffoliSwapByproducts, toffoliSwapByproductsPropagated]
  exact toffoliGate_comp_swapByproducts_propagates

/-- **The byproduct correction recovers the clean Toffoli.** Applying the correction
`toffoliSwapByproductCorrection = B†` after the moved Toffoli-with-byproducts recovers the bare
Toffoli:

  `B† · (T · (X₁·X₂·Z₃)) = T`.

This is the correction step of Exercise 10.68's fault-tolerant circuit: the classically-controlled
Cliffords the measurement outcomes trigger undo the propagated swap byproducts `B`, leaving the
clean Toffoli on the data. Proved from the commutation core
(`toffoliGate_comp_toffoliSwapByproducts`) by cancelling `B† · B = 1`
(`Evolution.adjoint_comp_self'`, unitarity of the byproduct Clifford). -/
theorem toffoliSwapByproductCorrection_comp_toffoliGate_comp_byproducts :
    toffoliSwapByproductCorrection.comp (toffoliGate.comp toffoliSwapByproducts) = toffoliGate := by
  rw [toffoliSwapByproductCorrection, toffoliGate_comp_toffoliSwapByproducts,
    ← Evolution.comp_assoc, Evolution.adjoint_comp_self', Evolution.id_comp]

/-- **The corrected moved-Toffoli circuit computes the Toffoli, on states.** For an arbitrary
three-qubit state `|ψ⟩`, running the raw swap byproducts, then the Toffoli, then the classically
controlled correction sends `|ψ⟩` to `Toffoli|ψ⟩`:

  `B† · T · (X₁·X₂·Z₃) |ψ⟩ = Toffoli|ψ⟩`.

The `evolvePure` reading of `toffoliSwapByproductCorrection_comp_toffoliGate_comp_byproducts` — the
byproduct-corrected core of the measured circuit reproduces the exact Toffoli action of part (1). -/
theorem toffoliSwapByproductCorrection_comp_toffoliGate_comp_byproducts_evolvePure
    (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) :
    (toffoliSwapByproductCorrection.comp (toffoliGate.comp toffoliSwapByproducts)).evolvePure ψ
      = toffoliGate.evolvePure ψ := by
  rw [toffoliSwapByproductCorrection_comp_toffoliGate_comp_byproducts]

/-! ### Part (2), operator-level move: the final Toffoli at the front of the circuit

The commutation core above moves the final Toffoli leftward *through the byproducts* of the
measured-swap realisation. Read purely as an operator identity — with the swap network taken as the
ideal deterministic `Evolution.swap` of part (1) rather than its measured-swap realisation — "moving
the final Toffoli all the way back to the left side" is literally the statement that the Toffoli may
sit at the *front* of the circuit: `(1 ⊗ T) · SWAP = SWAP · (T ⊗ 1)` (composition applies the right
operand first). This is the deterministic complement of the commutation core; together with part (1)
it exhibits a gate-moved circuit that still computes the Toffoli. -/

/-- **Part (2), operator form: the final Toffoli moved to the front.** The swap-then-Toffoli circuit
of part (1) equals the circuit that applies the Toffoli to the *left* block first and then swaps:

  `swapThenToffoli = SWAP · (T ⊗ 1)`   (i.e. `Evolution.swap.comp (toffoliGate.onLeft _)`).

This is the operator-level reading of "moving the final Toffoli all the way back to the left side"
(N&C Exercise 10.68 part (2)): with the swap taken as the ideal deterministic `Evolution.swap`, the
Toffoli commutes to the front of the circuit. Proved by conjugating the right-block Toffoli by the
involutive `SWAP` (`Evolution.swap_comp_onRight_comp_swap` turns `SWAP · (1 ⊗ T) · SWAP` into
`T ⊗ 1`, and `Evolution.swap_comp_self` cancels the trailing `SWAP`). The *fault-tolerant*
realisation of the same move — through the measured-swap byproducts onto the offline ancilla
preparation — is `toffoliGate_comp_swapByproducts_propagates`. -/
theorem swapThenToffoli_eq_swap_comp_toffoliOnLeft :
    swapThenToffoli = Evolution.swap.comp (toffoliGate.onLeft (qubit ⊗ (qubit ⊗ qubit))) := by
  rw [swapThenToffoli, ← Evolution.swap_comp_onRight_comp_swap toffoliGate,
    ← Evolution.comp_assoc, Evolution.swap_comp_self, Evolution.id_comp]

/-- **The gate-moved circuit computes the Toffoli.** With the final Toffoli moved to the front
(`SWAP · (T ⊗ 1)`), the circuit still sends an arbitrary three-qubit data state `|ψ⟩ ⊗ |000⟩` to
`|000⟩ ⊗ Toffoli|ψ⟩`: the front Toffoli acts on the data block first and the swap then moves the
transformed data onto the known block. Being equal to `swapThenToffoli`
(`swapThenToffoli_eq_swap_comp_toffoliOnLeft`), it accomplishes the same task as part (1) — so the
proof rewrites back to `swapThenToffoli` and applies `swapThenToffoli_evolvePure_ancillaZero`. This
is the operator-level content of part (2)'s "moving the final Toffoli … gives [a circuit that
computes the Toffoli]". -/
theorem swap_comp_toffoliOnLeft_evolvePure_ancillaZero
    (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) :
    (Evolution.swap.comp (toffoliGate.onLeft (qubit ⊗ (qubit ⊗ qubit)))).evolvePure
        (ψ.tmul (qubitThreeBasis (0, 0, 0)))
      = (qubitThreeBasis (0, 0, 0)).tmul (toffoliGate.evolvePure ψ) := by
  rw [← swapThenToffoli_eq_swap_comp_toffoliOnLeft, swapThenToffoli_evolvePure_ancillaZero]

/-! ## The assembled measured gate-teleportation identity (part (2))

The measured gate-teleportation identity is assembled end to end: run the fault-tolerant Toffoli
circuit — offline `toffoliAncilla` preparation, reshape,
the three data↔ancilla coupling `CNOT`s (all bundled into `toffoliTeleportPreMeasure`), **measure
the three data qubits** through `Measurement` (`toffoliDataMeasurement`, Postulate 4),
**apply the classically-controlled byproduct corrections** on the ancilla wires
(`toffoliTeleportCorrection`, `Evolution.evolve`), and read off the **ancilla marginal**
(`State.reducedLeft`, the §2.4.3 partial trace). The result is `(Toffoli|xyz⟩).toState` for
**every** one of the eight measurement outcomes — the Toffoli of the data, recovered
deterministically. This is
the Toffoli analogue of Problem 4.6's `bellPairsMeasurement_corrected_reducedRight_…`, and the
faithful "this circuit implements the Toffoli" that Exercise 10.68 part (2) asserts. -/

/-- **The assembled measured Toffoli gate-teleportation identity, for an arbitrary input** (Nielsen
& Chuang, Exercise 10.68 part (2)): the fault-tolerant Toffoli circuit implements the Toffoli
**gate**, deterministically, on **every** input state and **every** measurement outcome.

For every **three-qubit input pure state** `ψ` — including one **entangled** between its three wires
— and every joint outcome `(m₁, m₂, m₃)` of the three data-qubit measurements (with nonzero Born
probability `hp` — every outcome is possible, `toffoliDataMeasurement_bornProb_pos`): measure the
three data qubits of the honest pre-measurement state
(`toffoliDataMeasurement.postMeasurement`, Postulate 4), **de-interleave** the coupled-pairs
register into ancilla block ⊗ data block (`State.congr toffoliTeleportReshape.symm`), apply the
outcome-determined classically-controlled **byproduct correction** on the ancilla block
(`(toffoliTeleportCorrection m₁ m₂ m₃).onLeft _`, `Evolution.evolve`), and trace out the data block
(`State.reducedLeft`). The ancilla marginal is `(toffoliGate.evolvePure ψ).toState` — the Toffoli of
the *whole* input `ψ` — **independent of the outcome** (the right-hand side does not mention
`m₁, m₂, m₃`).

Quantifying over an arbitrary `ψ` (not merely the eight computational-basis inputs `|xyz⟩`) is what
makes this "the circuit implements the Toffoli **gate**": a gate must act correctly on every input,
and the induced operation normalises the collapsed branch — so is *not* linear in the input — hence
a basis-only statement (its `ψ = |xyz⟩` corollary
`toffoliDataMeasurement_corrected_reducedLeft_toffoliTeleportPreMeasure` below) would certify merely
the classical truth table, not the coherent gate action on superpositions. This is the Toffoli
analogue of Problem 4.6's `bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen`
(also over an arbitrary input) — the composable input→output map that a fault-tolerance argument
(part (3)) consumes. It is stated with `State`, `Measurement`, `Evolution` and the transport
`State.congr`. Proved by reducing the
post-measurement state to the normalised measured vector (`Measurement.postMeasurement_pure`) and
applying the general-input bridge
`toffoliTeleportCorrection_onLeft_evolvePure_congr_normalizeGen`
(`Postulates/API/ToffoliGateTeleportCompose`): the corrected, de-interleaved, normalised branch is
the product `Toffoli(ψ) ⊗ (data residual)`, whose left marginal (`State.reducedLeft_tmul`) is the
Toffoli output. -/
theorem toffoliDataMeasurement_corrected_reducedLeft_toffoliTeleportPreMeasureGen
    (ψ : PureState (qubit ⊗ (qubit ⊗ qubit))) (m₁ m₂ m₃ : Fin 2)
    (hp : toffoliDataMeasurement.bornProb
        (toffoliTeleportPreMeasureGen ψ).toState (m₁, m₂, m₃) ≠ 0) :
    (((toffoliTeleportCorrection m₁ m₂ m₃).onLeft (qubit ⊗ (qubit ⊗ qubit))).evolve
        ((toffoliDataMeasurement.postMeasurement
              (toffoliTeleportPreMeasureGen ψ).toState (m₁, m₂, m₃) hp).congr
            toffoliTeleportReshape.symm)).reducedLeft
      = (toffoliGate.evolvePure ψ).toState := by
  have hv : toffoliDataMeasurement.op (m₁, m₂, m₃) (toffoliTeleportPreMeasureGen ψ).vec ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_toffoliDataMeasurement_op_toffoliTeleportPreMeasureGen,
      norm_ne_zero_iff]
    exact pow_ne_zero 3 Concrete.invSqrt2_ne_zero
  rw [Measurement.postMeasurement_pure toffoliDataMeasurement (toffoliTeleportPreMeasureGen ψ)
      (m₁, m₂, m₃) hp hv, ← PureState.congr_toState, ← toState_evolvePure,
    toffoliTeleportCorrection_onLeft_evolvePure_congr_normalizeGen ψ m₁ m₂ m₃ hv,
    PureState.toState_tmul, State.reducedLeft_tmul]

/-- **The assembled measured Toffoli gate-teleportation identity on a computational-basis input**
(Nielsen & Chuang, Exercise 10.68 part (2)): the `ψ = |xyz⟩` corollary of
`toffoliDataMeasurement_corrected_reducedLeft_toffoliTeleportPreMeasureGen`. For every basis input
`|xyz⟩` and outcome `(m₁, m₂, m₃)`, measure → de-interleave → correct → trace-out sends the ancilla
marginal to `(toffoliGate.evolvePure |xyz⟩).toState` — the Toffoli truth table on the eight
computational-basis inputs. A definitional special case
(`toffoliTeleportPreMeasure_eq_gen`), so it takes the computational-basis hypothesis `hp`
directly. -/
theorem toffoliDataMeasurement_corrected_reducedLeft_toffoliTeleportPreMeasure
    (x y z m₁ m₂ m₃ : Fin 2)
    (hp : toffoliDataMeasurement.bornProb
        (toffoliTeleportPreMeasure x y z).toState (m₁, m₂, m₃) ≠ 0) :
    (((toffoliTeleportCorrection m₁ m₂ m₃).onLeft (qubit ⊗ (qubit ⊗ qubit))).evolve
        ((toffoliDataMeasurement.postMeasurement
              (toffoliTeleportPreMeasure x y z).toState (m₁, m₂, m₃) hp).congr
            toffoliTeleportReshape.symm)).reducedLeft
      = (toffoliGate.evolvePure (qubitThreeBasis (x, y, z))).toState :=
  toffoliDataMeasurement_corrected_reducedLeft_toffoliTeleportPreMeasureGen
    (qubitThreeBasis (x, y, z)) m₁ m₂ m₃ hp

end AxQM
