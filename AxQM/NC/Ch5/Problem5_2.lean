/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch2.Exercise2_57
import AxQM.NC.Ch4.Exercise4_35
import AxQM.Postulates.API.ControlledPhaseShift
import AxQM.Postulates.API.ToffoliHadamard
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Postulates.API.AdaptiveMeasurement
import AxQM.Postulates.API.DeferredMeasurementOnRight
import AxQM.Core.QtowerCtrlWireGate
import AxQM.Core.QtowerMeasurement
import AxQM.Core.DeferredMeasurementReading
import AxQM.Core.QftTowerHeadLayer
import AxQM.Core.MeasuredQftOuterStep
import AxQM.Core.QftTowerRecursion
import AxQM.Postulates.API.OnRightProductState
import AxQM.Postulates.API.MeasurementPrecompose
import AxQM.NC.Ch5.MeasuredQftHeadCollapse

/-!
# Nielsen & Chuang, Problem 5.2 (the measured quantum Fourier transform)

*(N&C p. 243.)*

Measured QFT: QFT then measurement equals a circuit of only one-qubit gates + measurement with
classical control.

## The formalisation

The faithful statement of Problem 5.2 is a whole-circuit equivalence: the QFT followed by measuring
every wire is equivalent — same outcome statistics, same collapsed states up to the classical wire
relabelling the Figure 5.1 swaps become — to a circuit built *only* from single-wire gates and
measurements with classical control, with no gate touching two wires. (The QFT enters the postulates
only as the *monolithic* unitary `qftEvolution`, never as a composition of wire-addressed
`Evolution` gates; the supporting results below express it gate by gate.)

The theorems are stated on the explicit `(n+1)`-qubit control tower `qtower n qubit`, where
`qftTowerEvolution n := Evolution.congr (quditPowTower n) (qftEvolution (2ⁿ⁺¹))` is N&C's QFT
transported wire-for-wire onto the register and `qtowerMeasurement n` is the per-wire
computational-basis measurement, faithfully the register measurement `quditMeasurement (2ⁿ⁺¹)`
transported (`qtowerMeasurement_eq_congr_quditMeasurement`) — so "measure the QFT
output register in the computational basis" is exactly "measure every wire of the tower":

* **The semiclassical circuit** `semiclassicalMeasuredQft n : Measurement (Fin (n+1) → Fin 2)
  (qtower n qubit)` — built *only* from the single-wire head Hadamard
  `Evolution.qtowerSingleWire (n+1) 0 hadamardGate`, computational-basis wire measurements
  (`controlMeasurement`), classical control (`Measurement.adaptiveCascade` on the measured head bit,
  applying the single-wire phase branch `qftTailBranch`), and a classical outcome relabelling
  (`reindexOutcome`, the swaps become bit bookkeeping). **No two-qubit gate** appears; that every
  classically-controlled branch is a composition of single-wire gates is
  `qftTailBranch_eq_qtowerSingleWire_prod` (the "no two qubit gates" clause, made an explicit
  proposition — see the final section).
* **Same outcome statistics** — `semiclassicalMeasuredQft_bornProb_eq`: for every input `ρ` and
  outcome `r`, `p(r ∣ measured QFT) = p(r ∣ semiclassicalMeasuredQft n)`. For a terminal measurement
  the outcome distribution *is* the observable content, so this is the whole-circuit equivalence
  Problem 5.2 asks for.
* **Same collapse, up to the swap relabelling** — the measured QFT collapses at outcome `r` to the
  recorded state `towerKet n r` (`qftTowerEvolution_measure_postMeasurement_eq_towerKet`) and the
  semiclassical circuit to its bit-reversal `towerKet n (fun i => r i.rev)`
  (`semiclassicalMeasuredQft_postMeasurement_eq_towerKet`), independent of the input: the two agree
  exactly up to the `Fin.rev` wire relabelling the Figure 5.1 swap network became once measurement
  is the last step (§4.4 deferred measurement) — no swap *gate* survives.

The per-gate deferred-measurement reduction (`controlledPhaseShift_measure_control_*`) and the
per-control-wire cascade reduction (`controlledUnitaryCascade_*`) these compose over are proved in
this file; the reusable engines and wire-addressed gates are in `AxQM/Postulates/API/` and
`AxQM/Core/` (named below).

## The supporting results

The QFT circuit (§5.1, product form 5.4) followed by measuring every wire is reduced to the
semiclassical circuit through the following results.

1. **The per-gate reduction (this file).** The QFT circuit's only two-qubit gate is the controlled
   phase-shift gate `C(R_k)`, `R_k = P(2π/2ᵏ)` (§5.1, eq. 5.3), which is
   `controlledPhaseShift` (`AxQM/Postulates/API/ControlledPhaseShift.lean`) at `φ = 2π/2ᵏ`. Under
   terminal measurement of its control, deferred measurement (§4.4 / Exercise 4.35) turns it into a
   classically-controlled single-wire gate. This is the local step the whole-circuit reduction
   composes over; it is proved here both for a bare two-qubit gate and for the gate **placed on a
   wire pair of a register** (control wire, target wire, spectator wires idle).
2. **The QFT circuit as an `Evolution`-gate composition** — the Figure 5.1 gates (Hadamards,
   controlled-`Rₖ` rotations, swap) as `Evolution`s, composed via the `Evolution`-monoid product
   and tied to `qftEvolution` in `AxQM/Postulates/API/QftGateEvolution.lean`
   (`qftEvolution_eq_qftCircuitEvolution : qftEvolution (2ⁿ) = qftCircuitEvolution n`). It works on
   the `qudit (2ⁿ)` register where `qftEvolution` lives: each Figure 5.1 gate is the `Concrete`
   wire-gate matrix (`singleQubitOnWire` Hadamards, `mcCtrlSingleQubit` controlled-`Rₖ`) promoted
   by `quditGate`, and the composition-equals-transform claim transports the `Concrete`
   correctness `qftGateCircuit_eq_qftMatrix` across `quditGate`.
3. **The per-control-wire cascade reduction (this file).** A single control wire of the QFT drives
   a whole *cascade* of controlled-`Rₖ` gates (one on every earlier target wire). The measurement
   of that control is deferred past the entire cascade at once, via the reading-level product
   engine
   (`Measurement.{bornProb,postMeasurement}_evolve_prod_of_forall_defers`,
   `AxQM/Core/DeferredMeasurementReading.lean`), turning the whole cascade of two-wire controlled
   gates into a composition of classically-controlled single-wire gates, with nothing left touching
   the control wire (`controlledUnitaryCascade` and its three theorems below). This lifts (1) from
   one gate to one control wire's worth of the circuit.
4. **The whole-circuit reduction over `qftEvolution`.** It uses a system isomorphism putting
   `qftEvolution (2ⁿ)` onto an explicit `n`-qubit tensor register, a per-wire computational-basis
   measurement on that register, each Figure 5.1 gate re-expressed as a wire-addressed `Evolution`,
   and the semiclassical rearrangement/induction assembling the per-control-wire reductions (3)
   under the terminal all-wire measurement — the Hadamards interleave the diagonal controlled-`Rₖ`
   cascades, so the measurement cannot be deferred past the whole circuit in one step. Its
   ingredients are:
   - **Tensor factorisation** (`AxQM/Postulates/API/QuditTensorFactor.lean`): the iso
     `quditProdIso : qudit (d·e) ≃ₛ qudit d ⊗ qudit e`, the building block of the register split.
   - **Register bridge** (`AxQM/Core/QftRegisterBridge.lean` and
     `AxQM/Postulates/API/QuditDimCongr.lean`): `quditPowTower : qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit`
     (iterating `quditProdIso` big-endian onto the right-nested `(n+1)`-qubit control tower — the
     `qubit ⊗ S` setting of (1) and (3)) and the QFT transported onto it,
     `qftTowerEvolution := Evolution.congr quditPowTower qftEvolution` (equally the transport of
     the Figure 5.1 circuit of (2)).
   - **Binary-expansion dictionary** (`AxQM/Core/QftTowerBasis.lean`):
     `quditPowTower_congr_quditBasis` gives the closed form
     `quditPowTower n |j⟩ = towerKet n (i ↦ (bits j) i.rev)` (the big-endian bridge and the
     little-endian `finFunctionFinEquiv` wire-indexing of the Figure 5.1 matrix gates meet through
     the reversal `Fin.rev`), with the encode form `quditPowTower_congr_quditBasis_apply` that the
     matrix gates use.
   - **Tower reader** (`AxQM/Core/QftTowerCircuit.lean` and
     `AxQM/Postulates/API/SystemIsoComm.lean`): any gate `U` transported onto the tower reads a
     basis ket through the dictionary, `(Φₙ • U).evolvePure (towerKet n b) = Φₙ • U.evolvePure
     |finFunctionFinEquiv (b ∘ rev)⟩` (`quditPowTower_congr_evolvePure_towerKet`), and the
     transported QFT circuit is the **product of the transported Figure 5.1 gates**
     `qftTowerEvolution_eq_map_congr_prod` (via the monoid-homomorphism law
     `Evolution.congr_prod`) — the explicit gate list the reduction defers the measurement past —
     together with `qftTowerEvolution_evolvePure_towerKet`, which reads the whole QFT on the tower
     basis.
   - **Single-wire gate placement** (`AxQM/Core/QtowerSingleWireGate.lean` and
     `AxQM/Core/EvolutionTowerBasisExt.lean`): the gate `Evolution.qtowerSingleWire` on the tower
     (with its wire-locality action `qtowerSingleWire_evolvePure_towerKet`, compare the
     wire-permutation gate `Evolution.qtowerPermWires`), and the **re-expression combinator**
     `quditPowTower_congr_eq_of_evolvePure_towerKet`, built from tower computational-basis
     extensionality `Evolution.ext_towerKet` and the tower reader, which turns each Figure 5.1
     gate's wire-addressed re-expression into a `towerKet`-basis check.
   - **Per-gate re-expressions** — each Figure 5.1 gate as a wire-addressed tower `Evolution`, via
     the combinator. (i) The **swap layer** (`AxQM/Postulates/API/QftSwapEvolution.lean` and
     `AxQM/Core/QftTowerSwap.lean`): the register swap `qftSwapEvolution (n+1)` transported onto
     the tower is the wire reversal `Evolution.qtowerPermWires Fin.revPerm`
     (`quditPowTower_congr_qftSwapEvolution`) — a bare relabelling of the `n+1` wires, no two-wire
     gate. (ii) The **Hadamard** on a wire (`AxQM/Postulates/API/QftHadamardEvolution.lean` and
     `AxQM/Core/QftTowerHadamard.lean`): the register Hadamard `qftHadamardEvolution (n+1) t`
     transported onto the tower is the single-wire gate
     `Evolution.qtowerSingleWire n t.rev hadamardGate` (`quditPowTower_congr_qftHadamardEvolution`)
     — a genuine one-qubit gate on the single wire `t.rev`. (Unlike the swap, the Hadamard maps a
     basis ket to a *superposition*, matched at the vector level via the tensor multilinearity of
     the tower product state; the register-side column bridge
     `quditGate_singleQubitOnWire_evolvePure_quditBasis` serves any single-wire gate.)
     (iii) The **controlled-`Rₖ`** on a wire pair, the circuit's only *two-wire* gate. Its tower
     placement is the **controlled single-wire gate** `Evolution.qtowerCtrlWire n c t g`
     (`AxQM/Core/QtowerCtrlWireGate.lean`) — control wire `c` above target wire `t` (the `c < t`
     the QFT produces after the reversal), applying `g` to wire `t` gated on wire `c`, the
     two-wire sibling of `Evolution.qtowerSingleWire` — with its wire-locality action
     `qtowerCtrlWire_evolvePure_towerKet` (fires on the `|1⟩` branch of the control, then acts as
     `g` on the target). The re-expression itself
     (`AxQM/Postulates/API/QftControlledEvolution.lean` and `AxQM/Core/QftTowerControlled.lean`):
     the register-side conditional rotation `qftControlledEvolution (n+1) t c` (the `quditGate`
     promotion of the diagonal Figure 5.1 gate matrix `qftControlledGate n t c`, with diagonal
     basis action `qftControlledEvolution_evolvePure_quditBasis`) transported onto the tower is the
     controlled single-wire phase gate
     `Evolution.qtowerCtrlWire n c.rev t.rev (phaseShiftGate (2π/2^{(c-t)+1}))`
     (`quditPowTower_congr_qftControlledEvolution`, for `t < c`) — the circuit's only two-wire gate
     placed as a controlled one-qubit phase gate on the wire pair `(c.rev, t.rev)`. So all three
     Figure 5.1 gate shapes (swap, Hadamard, controlled-`Rₖ`) have wire-addressed tower
     re-expressions.
   - **Per-wire terminal measurement** (`AxQM/Core/QtowerMeasurement.lean` and
     `AxQM/Postulates/API/MeasurementExt.lean`): `qtowerMeasurement n :
     Measurement (Fin (n+1) → Fin 2) (qtower n qubit)`, the joint computational-basis measurement
     of all `n+1` wires, built *head-first* by `Measurement.cascade` (N&C Ex. 2.57):
     `qtowerMeasurement (n+1)` cascades `controlMeasurement (qtower n qubit)` (measure the head
     wire) with `(qtowerMeasurement n).onRight qubit` (the recursive tail), relabelled by
     `Fin.consEquiv`. Its head peel `qtowerMeasurement_succ` is **definitional** — it exhibits the
     head wire's measurement as exactly the `controlMeasurement` that
     `controlledUnitaryCascade_measure_control_*` defers a control wire's `Rₖ` cascade past.
     Faithfulness `qtowerMeasurement_eq_congr_quditMeasurement`: this per-wire measurement **is**
     the single-register computational-basis measurement `quditMeasurement (2ⁿ⁺¹)` — the
     measurement N&C performs on the QFT output — transported onto the tower by `quditPowTower n`
     (matched by the wire↔index relabelling `towerMeasurementOutcomeEquiv`, the `Fin.rev`
     endianness flip), so "measure every wire in the computational basis" *is* "measure the
     register in the computational basis". Also the general lemma `Measurement.ext_op` (two
     measurements agree once their operators do).
   - **The semiclassical induction** assembling (3) under the terminal measurement:
     (a) the **head control wire's cascade defers under its own measurement**
     (`qtowerHeadCtrlCascade` and its three theorems below), applying (3)'s abstract engine to the
     concrete tower gates the QFT produces; and the **cascade-deferral engine**
     (`AxQM/Postulates/API/DeferredCascadeMeasurement.lean`,
     `Measurement.{op_comp,bornProb_evolve,postMeasurement_evolve}_cascade_of_comm`) lifting the
     single-measurement deferral engine to a `Measurement.cascade` — since the terminal all-wire
     measurement `qtowerMeasurement (n+1)` is the cascade of the head-wire measurement and the
     recursive tail, a gate defers past it once it defers past the head measurement (3) and
     each branch gate defers past the tail. (b) The **diagonal branch gates pass through the
     terminal measurement** — a single-wire phase gate
     (`qtowerSingleWire_phaseShiftGate_measure_{bornProb,postMeasurement}`) and, below, a whole
     *cascade* of them (`qtowerPhaseWireCascade` and its two theorems) defers past
     `qtowerMeasurement n`; the head cascade's deferred outcome-`1` branch is exactly such a product
     of single-wire phase rotations on the tail wires, so this is the `hM` reading the
     cascade-deferral engine consumes. (c) The **`onRight` lift of a deferral**
     (`AxQM/Postulates/API/DeferredMeasurementOnRight.lean`,
     `Measurement.{op_comp,bornProb_evolve,postMeasurement_evolve}_onRight_of_comm`): a right-factor
     gate `g.onRight T = 1 ⊗ g` defers past the right-factor measurement `m.onRight T = 1 ⊗ m`
     whenever `g` defers past `m` — the shape a control wire's deferred branch cascade (b) takes
     on the *tail* factor of the terminal measurement's `Measurement.cascade`. (d) The
     **reading-level cascade-deferral engine** (`qtowerMeasurement` is a `Core` cascade, so the
     operator engine (a) cannot be applied to the tower gates — their operator commutations cannot
     be named; this is the reading-level analog composing the readings
     (`hLb`/`hLp`/`hMb`/`hMp`) across a `Measurement.cascade`,
     `Measurement.{bornProb,postMeasurement}_evolve_cascade_of_defers` below, over N&C Ex. 2.57's
     chain rule). It combines the head-wire deferral (a) with the branch gates' tail deferral (the
     reading output of (e)) into "the gate defers past the whole cascade measurement", at the
     reading level. (e) The **branch cascade's tail deferral**
     (`qtowerPhaseWireCascade_onRight_measure_{bornProb,postMeasurement}` below): the concrete `hM`
     premise (d) consumes for the head wire. After (a) defers the head cascade past the head
     measurement, each classically-controlled branch is a product of single-wire phase gates on the
     tail wires, idle on the head wire — the `onRight`-shaped
     `(qtowerPhaseWireCascade n gs).onRight qubit`, which defers past the tail factor
     `(qtowerMeasurement n).onRight qubit` of the terminal cascade. It is the `onRight` lift (c) of
     the diagonal single-gate commutation (b), composed across the branch product by the
     reading-level product engine (3); the lift is packaged as two more projections of the
     single-gate bundled `defers` theorem (b), from the one commutation. (f) The **head control
     wire's whole cascade defers past the whole terminal measurement**
     (`qtowerHeadPhaseCascade_measure_{bornProb,postMeasurement}` below): it instantiates the
     reading-level cascade-deferral engine (d) with the tower head/tail measurements — `hLb`/`hLp`
     from (a), `hMb`/`hMp` from (e) — and transfers the result across the `Fin.consEquiv`
     relabelling of `qtowerMeasurement_succ`
     (`Measurement.{bornProb,postMeasurement}_evolve_reindexOutcome_of_defers` below and
     `Measurement.reindexOutcome_postMeasurement` in `AxQM/Postulates/API/`). The head cascade
     `qtowerHeadPhaseCascade n gs` defers past `qtowerMeasurement (n+1)` to the
     **classically-controlled** single-wire phase cascade `qtowerHeadPhaseBranch n gs (r 0)`:
     the tail phase rotations controlled on the measured head bit `r 0`, nothing on the head wire.
     The outer tower induction expresses `qftTowerEvolution` as its Figure 5.1 head layer
     (Hadamard + this controlled-`Rₖ` cascade) followed by the tail recursion, and recurses (f)
     over the tower (the tail wires are still measured, and the Hadamards interleave the diagonal
     cascades). A subtlety exposed by the phase recursion below: because `qftEvolution` is the
     *symmetric* DFT (the Figure 5.1 output-reversal baked into its formula), the head Hadamard +
     cascade produce the phase of the **last** output wire, not the head, so the peel is not
     `tail ∘ head-cascade ∘ head-Hadamard` but that composition followed by a cyclic wire
     permutation (the Figure 5.1 swap layer, `Evolution.qtowerPermWires`) routing the
     head-produced wire to the last position — the tail wires then carry exactly the `n`-tower QFT
     of the tail input.
   - **Base case** (`AxQM/Core/QftTowerRecursion.lean`): at depth `0` the tower QFT is a single
     one-qubit Hadamard, `qftTowerEvolution_zero : qftTowerEvolution 0 = hadamardGate` — already a
     one-wire gate with no two-wire gate and nothing to defer, so the measured-QFT reduction holds
     at `n = 0`. It rests on `qftEvolution_two_eq_qftHadamardEvolution` (the quantum Fourier
     transform on one qubit *is* the Hadamard gate, N&C §5.1 `F₂ = H`), read onto the tower
     through the Hadamard re-expression `quditPowTower_congr_qftHadamardEvolution`.
   - **Product form on the tower** (N&C eq. 5.4, `AxQM/Core/QftTowerProductForm.lean`): the
     transported QFT sends `towerKet n b` to the tensor product state
     `qftTowerEvolution_evolvePure_towerKet_towerProd : (qftTowerEvolution n).evolvePure (towerKet n
     b) = towerProd n (fun i => qubitPhasePlus (qftTowerWirePhase n b i))` — a phased-plus state
     `(|0⟩ + e^{iθᵢ}|1⟩)/√2` on every wire, no entanglement. The peel
     `qftTowerEvolution (n+1) = tail ∘ head-cascade ∘ head-Hadamard` is an `Evolution` identity
     checked on every `towerKet` (`Evolution.ext_towerKet`), and *both* sides of that check are read
     against this product form (the transported QFT on the left, the composed head-and-tail gates
     on the right). It is proved via the tower reader from the monolithic `qftEvolution`, so it
     sidesteps the Figure 5.1 block/permutation bookkeeping; the register Fourier sum factorises
     over the wires through an inline all-wire multilinear expansion of `towerProd`.
   - **Head cascade on a phased-plus head** (`AxQM/Core/QtowerHeadPhaseControl.lean` and
     `AxQM/Postulates/API/ControlledUnitaryPhasePlus.lean`): after the head Hadamard puts the head
     wire into `|+_α⟩`, the head control wire's controlled-`Rₖ` phase cascade sends
     `|+_α⟩ ⊗ towerKet n c` to `|+_{α + Σ φₜ·cₜ}⟩ ⊗ towerKet n c`
     (`qtowerHeadCtrlPhaseCascade_evolvePure_qubitPhasePlus`) — phase kickback advancing the head
     angle, the tail returned unchanged, no entanglement.
   - **Phase recursion** of the product form (`AxQM/Core/QftTowerPhaseRecursion.lean`), the
     number-theoretic bookkeeping of the peel: `qftTowerWirePhase_castSucc_qubitPhasePlus` (the
     first `n+1` output wires carry exactly the `n`-tower QFT phases of the tail input
     `Fin.tail b`, since the phases differ by an integer multiple of `2π` —
     `qubitPhasePlus_two_pi_nat_add`) and `qftTowerWirePhase_last` (the new last wire carries
     `π·(b 0) + Σₜ (Fin.tail b t)·2π·2^{t.rev}/2ⁿ⁺²`, the full fraction the head Hadamard + cascade
     imprint). Together these give the peel above: head-produced phase → last wire (needing the
     `Evolution.qtowerPermWires` cyclic shift), tail wires → `n`-tower QFT recursion.
   - **Head layer's action** (`AxQM/Core/QftTowerHeadLayer.lean`), the state-level content of the
     peel's head step. The head layer `qftHeadLayer n` (a head-wire Hadamard
     `Evolution.qtowerSingleWire (n+1) 0 hadamardGate` then the head control wire's controlled-`Rₖ`
     phase cascade over `qftHeadRotationList n`, the angles `2π·2^{t.rev}/2ⁿ⁺²`) sends
     `towerKet (n+1) b` to `|+_θ⟩ ⊗ towerKet n (Fin.tail b)` with
     `θ = qftTowerWirePhase (n+1) b (Fin.last (n+1))` the **last** output wire's phase
     (`qftHeadLayer_evolvePure_towerKet`): the head Hadamard puts the head wire into `|+_{π·b 0}⟩`
     (`qtowerSingleWire_zero_hadamardGate_evolvePure_towerKet`, via
     `hadamardGate_evolvePure_qubitBasis_qubitPhasePlus` / `qubitMinus_eq_qubitPhasePlus_pi` in
     `AxQM/Postulates/API/PhasedPlus.lean`), the cascade advances it by the total Fourier fraction,
     and the two together match `qftTowerWirePhase_last`. This confirms the symmetric-DFT finding
     concretely — the head gates produce the *last* wire.
   - **Peel identity** (`AxQM/Core/QftTowerPeel.lean`):
     `qftTowerEvolution_succ_eq_qftHeadLayer_peel`,
     `qftTowerEvolution (n+1) = Φ · qftTailEvolution n · qftHeadLayer n` with `Φ =
     Evolution.qtowerPermWires (finRotate (n+2)).symm` the cyclic wire permutation and
     `qftTailEvolution n = (qftTowerEvolution n).onRight qubit` the tail QFT recursion. Proved on
     every `towerKet (n+1) b` (`Evolution.ext_towerKet`): the head layer then the tail QFT (product
     form on the tail, phase-matched by `qftTowerWirePhase_castSucc_qubitPhasePlus`) leave wire `0`
     holding output wire `n+1` and wire `j+1` holding output wire `j`, and `Φ`'s cyclic shift
     (`finRotate` on the product-state permutation `qtowerPermWires_evolvePure_towerProd`, built
     from the product-state bridge `qtowerQubitTensorPow_congr_towerProd`) routes each output wire
     back into place, reproducing the product form. The outer tower induction then recurses over
     this peel, deferring each head cascade under the terminal measurement (base case above,
     engine (f)).
   - **The swap network becomes a classical relabelling**
     (`AxQM/Core/QtowerPermMeasurement.lean` and
     `AxQM/Postulates/API/DeferredMeasurementReindex.lean`): the peel's outermost cyclic wire
     permutation `Φ = qtowerPermWires σ` defers past the terminal measurement
     (`qtowerPermWires_measure_{bornProb,postMeasurement}`): `p(r ∣ Φ ρ Φ†) = p(r ∘ σ ∣ ρ)`,
     `postMeas(Φ ρ Φ†, r) = Φ · postMeas(ρ, r ∘ σ)` — the Figure 5.1 swaps become a relabelling of
     the recorded bits, *no two-qubit gate*. It rests on a **reindexing** deferred-measurement
     engine (a basis-permuting gate `Mᵢ V = Wᵢ M_{e i}`); the `Core` instantiation discharges that
     operator relation in its proof body via the measurement's rank-one projector form
     (`qtowerMeasurement_eq_congr_quditMeasurement`).

Items (1), (3), the reading-level cascade deferral (d), the branch-cascade tail deferral (e) and
the head-cascade terminal deferral (f) are proved below in this file; the other items are in
`AxQM/Postulates/API/` and `AxQM/Core/` (named above). Together they give the whole-circuit
reduction: the measured QFT's outcome statistics and collapsed states are those of the manifestly
semiclassical circuit `semiclassicalMeasuredQft`, no gate of which touches two wires.

## The per-gate reduction

The replacement is N&C's **principle of deferred measurement** (§4.4), in the form of **Exercise
4.35** ("measurements commute with controls"): a controlled gate `C(U)` whose control qubit is
measured in the computational basis is equivalent to measuring the control *first* and then applying
`U` to the target, classically controlled on the outcome. A measurement circuit is fixed, for each
outcome, by its probability (Postulate 3) and its post-measurement state (Postulate 4), so the
equivalence is the following triple, at `U = phaseShiftGate φ` (bare) and
`U = (phaseShiftGate φ).onLeft R` (register-placed):

* `controlledPhaseShift_measure_control_bornProb` /
  `controlledPhaseShiftWire_measure_control_bornProb` — **the outcome statistics agree**: measuring
  the control after `C(P(φ))` gives the same Born probability as measuring it on the input directly,
  `p(i ∣ C(P(φ)) ρ C(P(φ))†) = p(i ∣ ρ)`.
* `controlledPhaseShift_measure_control_postMeasurement` /
  `controlledPhaseShiftWire_measure_control_postMeasurement` — **the post-measurement state defers
  the gate**: the state after `C(P(φ))` then measuring the control equals the
  classically-controlled gate `Wᵢ` applied to the state obtained by measuring the control first,
  `postMeas(C(P(φ)) ρ C(P(φ))†, i) = Wᵢ · postMeas(ρ, i)`.
* `classicalControl_phaseShiftGate_isSingleQubitGate` /
  `controlledPhaseShiftWire_classicalControl_isSingleWireGate` — **no two-wire gate**: each branch
  gate `Wᵢ` acts on the target wire alone — bare, `Wᵢ = 1 ⊗ gᵢ` (`Evolution.onRight`); placed,
  `Wᵢ = 1 ⊗ (gᵢ ⊗ 1_R)` (`(gᵢ.onLeft R).onRight qubit`), the identity on the control wire and on
  every spectator wire — with `g₀ = 1` and `g₁ = P(φ)`. After deferring the measurement the
  register's two-qubit `C(P(φ))` has become a classically-controlled *one-wire* gate.

The bare form is the clean statement of the reduction; the register form is the same reduction with
the target and spectator wires carried along, i.e. how `C(R_k)` actually sits inside the QFT's
`n`-qubit register — the local step that (3) composes.
-/

-- This file contains the full multi-step measured-QFT development (Problem 5.2 is a deep
-- induction; see the module docstring), so it exceeds the default file-length limit.
set_option linter.style.longFile 2700

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The bare two-qubit gate `C(P(φ))` -/

/-- **Problem 5.2 (outcome statistics).** Measuring the control qubit of the QFT's controlled
phase-shift gate `C(P(φ))` commutes with the gate at the level of the Born probabilities: for every
outcome `i`, the probability of `i` when the control is measured *after* applying `C(P(φ))` equals
the probability when it is measured on the input `ρ` directly,
`p(i ∣ C(P(φ)) ρ C(P(φ))†) = p(i ∣ ρ)`. The instance at `U = phaseShiftGate φ` of Exercise 4.35's
deferred-measurement Born-rule invariance `controlMeasurement_commute_bornProb`. -/
theorem controlledPhaseShift_measure_control_bornProb (φ : ℝ) (ρ : State (qubit ⊗ qubit))
    (i : Fin 2) :
    (controlMeasurement qubit).bornProb ((controlledPhaseShift φ).evolve ρ) i
      = (controlMeasurement qubit).bornProb ρ i :=
  controlMeasurement_commute_bornProb (phaseShiftGate φ) ρ i

/-- **Problem 5.2 (post-measurement state — deferring the gate).** Measuring the control qubit of
the QFT's controlled phase-shift gate `C(P(φ))` commutes with the gate at the level of the collapsed
state: for every outcome `i` possible on `ρ`, the state after applying `C(P(φ))` and *then*
measuring the control equals the classically-controlled gate
`Wᵢ = classicalControl (phaseShiftGate φ) i` applied to the state obtained by measuring the control
*first*,

  `postMeas(C(P(φ)) ρ C(P(φ))†, i) = Wᵢ · postMeas(ρ, i)`.

This is the measured-QFT reduction: the two-qubit gate then measurement becomes measurement then a
classically-controlled gate. The outcome is equally possible after `C(P(φ))` because the
probabilities agree (`controlledPhaseShift_measure_control_bornProb`). The instance at
`U = phaseShiftGate φ` of Exercise 4.35's deferred-measurement collapse law
`controlMeasurement_commute_postMeasurement`. -/
theorem controlledPhaseShift_measure_control_postMeasurement (φ : ℝ) (ρ : State (qubit ⊗ qubit))
    (i : Fin 2) (hp : (controlMeasurement qubit).bornProb ρ i ≠ 0) :
    (controlMeasurement qubit).postMeasurement ((controlledPhaseShift φ).evolve ρ) i
        (by rw [controlledPhaseShift_measure_control_bornProb]; exact hp)
      = (classicalControl (phaseShiftGate φ) i).evolve
          ((controlMeasurement qubit).postMeasurement ρ i hp) :=
  controlMeasurement_commute_postMeasurement (phaseShiftGate φ) ρ i hp

/-- **Problem 5.2 (no two-qubit gates).** Each classical-control branch gate
`Wᵢ = classicalControl (phaseShiftGate φ) i` that replaces the two-qubit gate `C(P(φ))` is a
*single-qubit* gate on the target wire: it factors as `Wᵢ = 1 ⊗ gᵢ` (`Evolution.onRight gᵢ qubit`,
the identity on the control qubit), with `g₀ = 1` (nothing) on outcome `0` and `g₁ = P(φ)` (the
single-qubit phase gate) on outcome `1`. This is the "one qubit gates only, no two qubit gates"
conclusion of Problem 5.2 for the bare gate: after deferring the measurement, the QFT's controlled
phase gate has become a classically-controlled one-qubit gate. -/
theorem classicalControl_phaseShiftGate_isSingleQubitGate (φ : ℝ) (i : Fin 2) :
    ∃ g : Evolution qubit, classicalControl (phaseShiftGate φ) i = Evolution.onRight g qubit := by
  fin_cases i
  · refine ⟨Evolution.id, ?_⟩
    change classicalControl (phaseShiftGate φ) 0 = Evolution.onRight Evolution.id qubit
    rw [classicalControl_zero, Evolution.id_onRight]
  · exact ⟨phaseShiftGate φ, classicalControl_one (phaseShiftGate φ)⟩

/-! ### The gate placed on a wire pair of a register `qubit ⊗ (qubit ⊗ R)`

The form the whole-circuit reduction composes over: control on wire `0`, the phase
gate `P(φ)` on the target wire `1`, and the remaining wires `R` idle. -/

variable {R : QSystem}

/-- The QFT's controlled phase-shift gate `C(P(φ))` **placed on a wire pair of a register**
`qubit ⊗ (qubit ⊗ R)`: control on wire `0`, the single-qubit phase gate `P(φ)` on the target wire
`1`, and the remaining wires `R` idle. Here `(phaseShiftGate φ).onLeft R` is `P(φ)` on wire `1` and
the identity on `R`, so `controlledUnitary` of it controls that on wire `0`. This is how the QFT
circuit's only two-qubit gate `C(R_k)` (§5.1; `R_k` is the instance `φ = 2π/2ᵏ`) actually sits
inside the full `n`-qubit register — a control wire, a target wire, and spectator wires it leaves —
the form the whole-circuit reduction needs. -/
def controlledPhaseShiftWire (φ : ℝ) (R : QSystem) : Evolution (qubit ⊗ (qubit ⊗ R)) :=
  controlledUnitary ((phaseShiftGate φ).onLeft R)

/-- **Register form of Problem 5.2 (outcome statistics).** Measuring the control *wire* of the
register-placed controlled phase-shift gate `controlledPhaseShiftWire φ R` (control wire `0`, target
wire `1`, spectators `R`) leaves the Born probabilities unchanged: for every outcome `i`,
`p(i ∣ C(P(φ)) ρ C(P(φ))†) = p(i ∣ ρ)`, whatever the spectator wires carry. The instance at
`U = (phaseShiftGate φ).onLeft R` of Exercise 4.35's `controlMeasurement_commute_bornProb`. -/
theorem controlledPhaseShiftWire_measure_control_bornProb (φ : ℝ)
    (ρ : State (qubit ⊗ (qubit ⊗ R))) (i : Fin 2) :
    (controlMeasurement (qubit ⊗ R)).bornProb ((controlledPhaseShiftWire φ R).evolve ρ) i
      = (controlMeasurement (qubit ⊗ R)).bornProb ρ i :=
  controlMeasurement_commute_bornProb ((phaseShiftGate φ).onLeft R) ρ i

/-- **Register form of Problem 5.2 (post-measurement state — deferring the gate).** Measuring the
control wire *after* the register-placed gate `controlledPhaseShiftWire φ R` equals the
classically-controlled gate `Wᵢ = classicalControl ((phaseShiftGate φ).onLeft R) i` applied to the
state obtained by measuring the control wire *first*,

  `postMeas(C(P(φ)) ρ C(P(φ))†, i) = Wᵢ · postMeas(ρ, i)`,

the deferred-measurement reduction with the target and spectator wires carried along. The instance
at `U = (phaseShiftGate φ).onLeft R` of Exercise 4.35's
`controlMeasurement_commute_postMeasurement`. -/
theorem controlledPhaseShiftWire_measure_control_postMeasurement (φ : ℝ)
    (ρ : State (qubit ⊗ (qubit ⊗ R))) (i : Fin 2)
    (hp : (controlMeasurement (qubit ⊗ R)).bornProb ρ i ≠ 0) :
    (controlMeasurement (qubit ⊗ R)).postMeasurement ((controlledPhaseShiftWire φ R).evolve ρ) i
        (by rw [controlledPhaseShiftWire_measure_control_bornProb]; exact hp)
      = (classicalControl ((phaseShiftGate φ).onLeft R) i).evolve
          ((controlMeasurement (qubit ⊗ R)).postMeasurement ρ i hp) :=
  controlMeasurement_commute_postMeasurement ((phaseShiftGate φ).onLeft R) ρ i hp

/-- **Register form of Problem 5.2 (no two-wire gate).** Each classical-control branch gate
`Wᵢ = classicalControl ((phaseShiftGate φ).onLeft R) i` that replaces the register-placed two-qubit
gate `controlledPhaseShiftWire φ R` acts on the **target wire alone**: there is a single-qubit gate
`g` with `Wᵢ = (g.onLeft R).onRight qubit`, i.e. `1 ⊗ (g ⊗ 1_R)` — the identity on the control wire
`0` and on every spectator wire `R`, `g` only on the target wire `1` — with `g₀ = 1` (nothing) on
outcome `0` and `g₁ = P(φ)` on outcome `1`. This is the "no two qubit gates" content in the register
setting: after deferring the measurement the register's controlled phase gate has become a
classically-controlled *one-wire* gate. -/
theorem controlledPhaseShiftWire_classicalControl_isSingleWireGate (φ : ℝ) (i : Fin 2) :
    ∃ g : Evolution qubit,
      classicalControl ((phaseShiftGate φ).onLeft R) i = (g.onLeft R).onRight qubit := by
  fin_cases i
  · refine ⟨Evolution.id, ?_⟩
    change classicalControl ((phaseShiftGate φ).onLeft R) 0 = (Evolution.id.onLeft R).onRight qubit
    rw [classicalControl_zero, Evolution.id_onLeft, Evolution.id_onRight]
  · exact ⟨phaseShiftGate φ, classicalControl_one ((phaseShiftGate φ).onLeft R)⟩

/-! ### A whole control wire's cascade of gates defers together

The reduction above is the *per-gate* step. In the QFT circuit a single control wire carries a whole
*cascade* of controlled gates — that wire controls a phase rotation on every earlier target wire —
so the whole-circuit reduction must defer the measurement of that control past the *entire* cascade
at once. The reading-level product engine
(`Measurement.{bornProb,postMeasurement}_evolve_prod_of_forall_defers`,
`AxQM/Core/DeferredMeasurementReading.lean`) does exactly that: it composes the single-gate deferral
readings past a composition of controlled gates one gate at a time, accumulating the
classically-controlled branch gates. The conclusion is that an
entire control wire's cascade of two-wire controlled gates, followed by measuring the control,
equals measuring the control first and then a composition of classically-controlled *single-wire*
gates — with nothing left touching the control wire. This is the "no two qubit gates" content at the
scale of one control wire's worth of the circuit; the QFT instantiates the cascade `Us` with the
single-qubit phase gates `phaseShiftGate (2π/2ᵏ)` placed on the various target wires. -/

variable {S : QSystem}

/-- The **cascade of controlled gates on one control wire**: the composition `C(Uₖ) ⋯ C(U₁)` of the
controlled gates `controlledUnitary Uⱼ` for each `Uⱼ` on the wire's gate list `Us`, all sharing the
control qubit of `qubit ⊗ S` (the targets live inside `S`). This is how one control wire of the QFT
circuit sits: the controlled-`Rₖ` rotations it drives on the earlier target wires, taken in order.
For the QFT the `Uⱼ` are the single-qubit phase gates `phaseShiftGate (2π/2ᵏ)` on the target wires;
`controlledUnitaryCascade` is the object over which the whole-circuit reduction defers a control's
entire block. -/
def controlledUnitaryCascade (Us : List (Evolution S)) : Evolution (qubit ⊗ S) :=
  (Us.map controlledUnitary).prod

/-- **Measured cascade — outcome statistics.** Measuring the control wire *after* a whole cascade
`controlledUnitaryCascade Us` of controlled gates gives, for every outcome `i`, the same Born
probability as measuring it on the input `ρ` directly: the entire cascade is invisible to the
control statistics. A thin instance of the reading-level engine
`Measurement.bornProb_evolve_prod_of_forall_defers` at `V = controlledUnitary`, each gate's
invariance supplied by Exercise 4.35's `controlMeasurement_commute_bornProb`. -/
theorem controlledUnitaryCascade_measure_control_bornProb (Us : List (Evolution S))
    (ρ : State (qubit ⊗ S)) (i : Fin 2) :
    (controlMeasurement S).bornProb ((controlledUnitaryCascade Us).evolve ρ) i
      = (controlMeasurement S).bornProb ρ i :=
  Measurement.bornProb_evolve_prod_of_forall_defers (controlMeasurement S) controlledUnitary
    (fun U ρ i => controlMeasurement_commute_bornProb U ρ i) Us ρ i

/-- **Measured cascade — post-measurement state (deferring the whole cascade).** Measuring the
control wire *after* the cascade `controlledUnitaryCascade Us` equals the composition of the
classically-controlled branch gates applied to the state obtained by measuring the control *first*,

  `postMeas(C(Uₖ) ⋯ C(U₁) · ρ · (C(Uₖ) ⋯ C(U₁))†, i) = (Wₖ ⋯ W₁)ᵢ · postMeas(ρ, i)`,

with `Wⱼᵢ = classicalControl Uⱼ i` and `(Wₖ ⋯ W₁)ᵢ = (Us.map (fun U => classicalControl U i)).prod`.
The whole cascade of two-wire controlled gates has been deferred to a composition of
classically-controlled gates. A thin instance of the reading-level engine
`Measurement.postMeasurement_evolve_prod_of_forall_defers` (branch family `W = classicalControl`),
each gate's readings supplied by Exercise 4.35's
`controlMeasurement_commute_{bornProb,postMeasurement}`. -/
theorem controlledUnitaryCascade_measure_control_postMeasurement (Us : List (Evolution S))
    (ρ : State (qubit ⊗ S)) (i : Fin 2) (hp : (controlMeasurement S).bornProb ρ i ≠ 0) :
    (controlMeasurement S).postMeasurement ((controlledUnitaryCascade Us).evolve ρ) i
        (by rw [controlledUnitaryCascade_measure_control_bornProb]; exact hp)
      = ((Us.map (fun U => classicalControl U i)).prod).evolve
          ((controlMeasurement S).postMeasurement ρ i hp) :=
  Measurement.postMeasurement_evolve_prod_of_forall_defers (controlMeasurement S) controlledUnitary
    classicalControl (fun U ρ i => controlMeasurement_commute_bornProb U ρ i)
    (fun U ρ i hρ _ => controlMeasurement_commute_postMeasurement U ρ i hρ) Us ρ i hp
    (fun h => hp ((controlledUnitaryCascade_measure_control_bornProb Us ρ i).symm.trans h))

/-- **The deferred cascade leaves the control wire untouched (no two-wire gate).** For every outcome
`i` there is a gate `g : Evolution S` on the *target register alone* with

  `(Us.map (fun U => classicalControl U i)).prod = Evolution.onRight g qubit = 1 ⊗ g`,

the identity on the control wire. On outcome `0` nothing is applied (`g = 1`); on outcome `1` the
gate is `g = Us.prod`, the composition of the cascade's target gates. So when each `Uⱼ` is a
single-qubit gate — as the QFT's `phaseShiftGate (2π/2ᵏ)` — the deferred cascade is a circuit of
single-qubit gates on the target wires, and no gate touches two wires: after deferring the control
measurement, an entire control wire's worth of the QFT's two-qubit gates has become single-wire
gates. Proved from `classicalControl_zero`/`_one` and the right-factor list-product homomorphism
`Evolution.onRight_list_prod`. -/
theorem controlledUnitaryCascade_classicalControl_isSingleWireGate (Us : List (Evolution S))
    (i : Fin 2) :
    ∃ g : Evolution S,
      (Us.map (fun U => classicalControl U i)).prod = Evolution.onRight g qubit := by
  fin_cases i
  · refine ⟨Evolution.id, ?_⟩
    rw [Evolution.id_onRight]
    refine List.prod_eq_one (fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨U, _, rfl⟩ := hx
    exact classicalControl_zero U
  · refine ⟨Us.prod, ?_⟩
    -- each `classicalControl U 1 = Evolution.onRight U qubit`, so the branch product is the
    -- right-factor image of `Us.prod` (`Evolution.onRight_list_prod`).
    rw [← Evolution.onRight_list_prod qubit S Us]
    exact congrArg List.prod (List.map_congr_left fun U _ => classicalControl_one U)

/-! ### The head control wire's cascade on the tower defers under its measurement

The cascade reduction above is stated abstractly over the control qubit of `qubit ⊗ S`. This
section places it on the concrete wire-addressed gates the measured quantum Fourier transform
produces on the `(n+1)`-qubit control tower `qtower (n+1) qubit` (see `AxQM/Core/`),
the register on which `qftEvolution` is read gate by gate. There one control wire — the
**head wire** `0` of the tower — drives a cascade of the Figure 5.1 controlled-`Rₖ` gates, each
re-expressed as the tower controlled single-wire gate
`Evolution.qtowerCtrlWire (n+1) 0 t g`: control on the head wire, the phase gate on a tail target
wire `t`. On the head wire that gate is exactly `controlledUnitary` of the single-wire gate on the
tail (`Evolution.qtowerCtrlWire_ctrl_zero`), so the head wire's *whole* cascade is a
`controlledUnitaryCascade`; and the head wire's computational-basis measurement is
`controlMeasurement (qtower n qubit)`, definitionally the head of the terminal per-wire measurement
`qtowerMeasurement (n+1)` (`qtowerMeasurement_succ`). The cascade reduction above
therefore defers the head wire's entire controlled-`Rₖ` block, under measurement of the head wire,
to a composition of classically-controlled *single-wire* gates on the tail wires, with nothing left
on the head wire. This is the head-wire step of the whole-circuit semiclassical reduction: it binds
the abstract engine of (3a) to the concrete tower gates the QFT is re-expressed into. The outer
induction below carries it over the tower under the *whole* terminal measurement (the tail wires
are still measured, and the Hadamards interleave the diagonal cascades). -/

/-- The **head wire's cascade of controlled single-wire gates** on the tower `qtower (n+1) qubit`:
the composition of the tower controlled single-wire gates
`Evolution.qtowerCtrlWire (n+1) 0 t.succ g`, one for each pair `(t, g)` of `gs`, all sharing the
head wire `0` as control and each acting on the tail wire `t.succ` (`t : Fin (n+1)`). This is how
one control wire of the QFT circuit sits on the
tower once the Figure 5.1 controlled-`Rₖ` gates it drives are re-expressed as wire-addressed tower
gates; for the QFT the gates `g` are the single-qubit phase gates
`phaseShiftGate (2π/2ᵏ)`. -/
def qtowerHeadCtrlCascade (n : ℕ) (gs : List (Fin (n + 1) × Evolution qubit)) :
    Evolution (qtower (n + 1) qubit) :=
  (gs.map fun p => Evolution.qtowerCtrlWire (n + 1) 0 p.1.succ p.2).prod

/-- **The head wire's cascade is a `controlledUnitaryCascade`.** Each head-controlled tower gate
`Evolution.qtowerCtrlWire (n+1) 0 t.succ g` is `controlledUnitary` of the single-wire gate on the
tail `Evolution.qtowerSingleWire n t g` (`Evolution.qtowerCtrlWire_ctrl_zero`), so the head cascade
equals the abstract cascade over those single-wire gates,
`controlledUnitaryCascade (gs.map fun (t, g) => Evolution.qtowerSingleWire n t g)`. This bridge lets
the deferred-measurement engine above run on the concrete tower gates the QFT produces. -/
theorem qtowerHeadCtrlCascade_eq_controlledUnitaryCascade (n : ℕ)
    (gs : List (Fin (n + 1) × Evolution qubit)) :
    qtowerHeadCtrlCascade n gs
      = controlledUnitaryCascade (gs.map fun p => Evolution.qtowerSingleWire n p.1 p.2) := by
  rw [qtowerHeadCtrlCascade, controlledUnitaryCascade, List.map_map]
  exact congrArg List.prod
    (List.map_congr_left fun p _ => Evolution.qtowerCtrlWire_ctrl_zero n p.1 p.2)

/-- **Measured head cascade — outcome statistics.** Measuring the head wire *after* its entire
controlled-`Rₖ` cascade `qtowerHeadCtrlCascade n gs` gives, for every outcome `i`, the same Born
probability as measuring it on the input `ρ` directly: the cascade is invisible to the head-wire
statistics. The head-wire instance of `controlledUnitaryCascade_measure_control_bornProb` through
the bridge `qtowerHeadCtrlCascade_eq_controlledUnitaryCascade`. -/
theorem qtowerHeadCtrlCascade_measure_head_bornProb (n : ℕ)
    (gs : List (Fin (n + 1) × Evolution qubit)) (ρ : State (qtower (n + 1) qubit)) (i : Fin 2) :
    (controlMeasurement (qtower n qubit)).bornProb ((qtowerHeadCtrlCascade n gs).evolve ρ) i
      = (controlMeasurement (qtower n qubit)).bornProb ρ i := by
  rw [qtowerHeadCtrlCascade_eq_controlledUnitaryCascade]
  exact controlledUnitaryCascade_measure_control_bornProb _ ρ i

/-- **Measured head cascade — post-measurement state (deferring the whole cascade).** Measuring the
head wire *after* the cascade `qtowerHeadCtrlCascade n gs` equals the composition of the
classically-controlled branch gates applied to the state obtained by measuring the head wire
*first*: the whole head cascade of two-wire controlled gates has been deferred to a composition of
classically-controlled single-wire gates (each branch a
`classicalControl (Evolution.qtowerSingleWire n t g) i` on a tail wire). The head-wire instance of
`controlledUnitaryCascade_measure_control_postMeasurement` through the bridge. -/
theorem qtowerHeadCtrlCascade_measure_head_postMeasurement (n : ℕ)
    (gs : List (Fin (n + 1) × Evolution qubit)) (ρ : State (qtower (n + 1) qubit)) (i : Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb ρ i ≠ 0) :
    (controlMeasurement (qtower n qubit)).postMeasurement ((qtowerHeadCtrlCascade n gs).evolve ρ) i
        (by rw [qtowerHeadCtrlCascade_measure_head_bornProb]; exact hp)
      = (((gs.map fun p => Evolution.qtowerSingleWire n p.1 p.2).map
            fun U => classicalControl U i).prod).evolve
          ((controlMeasurement (qtower n qubit)).postMeasurement ρ i hp) := by
  apply State.ext
  -- `erw`: the measured state's system `qtower (n+1) qubit` is only definitionally
  -- `qubit ⊗ qtower n qubit`, the system `controlMeasurement` reads.
  erw [Measurement.postMeasurement_op, qtowerHeadCtrlCascade_eq_controlledUnitaryCascade]
  have h := congrArg State.op (controlledUnitaryCascade_measure_control_postMeasurement
    (gs.map fun p => Evolution.qtowerSingleWire n p.1 p.2) ρ i hp)
  rw [Measurement.postMeasurement_op] at h
  exact h

/-- **The deferred head cascade leaves the head wire untouched (no two-wire gate).** For every
outcome `i` there is a gate `g : Evolution (qtower n qubit)` on the tail register alone with the
deferred branch product equal to `Evolution.onRight g qubit = 1 ⊗ g`, the identity on the head wire
(on outcome `0`, `g = 1`; on outcome `1`, the composition of the cascade's single-wire tail gates).
Since each `Evolution.qtowerSingleWire n t g` is a single-qubit gate on one tail wire, the deferred
head cascade is a circuit of single-wire gates touching the head wire nowhere: after deferring the
head wire's measurement, its whole controlled-`Rₖ` block has become single-wire gates with classical
control. The head-wire instance of `controlledUnitaryCascade_classicalControl_isSingleWireGate`. -/
theorem qtowerHeadCtrlCascade_classicalControl_isSingleWireGate (n : ℕ)
    (gs : List (Fin (n + 1) × Evolution qubit)) (i : Fin 2) :
    ∃ g : Evolution (qtower n qubit),
      ((gs.map fun p => Evolution.qtowerSingleWire n p.1 p.2).map
          fun U => classicalControl U i).prod = Evolution.onRight g qubit :=
  controlledUnitaryCascade_classicalControl_isSingleWireGate
    (gs.map fun p => Evolution.qtowerSingleWire n p.1 p.2) i

/-! ### A single-wire phase gate passes through the terminal measurement

The head-wire cascade above defers past the *head-wire* measurement
(`qtowerHeadCtrlCascade_measure_head_*`); the cascade-deferral engine
(`Measurement.…_cascade_of_comm`) lifts that to the *whole* terminal per-wire measurement
`qtowerMeasurement` provided each classically-controlled branch gate
in turn defers past the tail measurement. For the QFT those branch gates are the single-qubit phase
gates `phaseShiftGate (2π/2ᵏ)` placed on a tail wire — **diagonal** in the computational basis,
hence commuting with the computational-basis measurement of every wire. This section proves exactly
that, as the deferral of a single-wire phase gate
`Evolution.qtowerSingleWire n t (phaseShiftGate φ)` past the terminal measurement
`qtowerMeasurement n`: measuring every wire *after* the phase gate has the same outcome statistics
and the same collapsed states as measuring first and applying the phase gate afterwards. This is the
`hM` hypothesis the semiclassical induction feeds to the cascade-deferral engine for
the QFT's diagonal branch gates.

The gate is unitary and sends each computational tower ket `towerKet n b` to a phase multiple of
itself (eigenvalue `[1, e^{iφ}]_{b t}` — the phase gate acting on wire `t`'s bit); its operator
therefore commutes with each measurement operator `|towerKet r⟩⟨towerKet r|` of `qtowerMeasurement`,
and the deferred-measurement engine (`Measurement.{bornProb,postMeasurement}_evolve_of_comm`,
Exercise 4.35) reads off the two Postulate-3/4 conclusions. The commutation is proved with `.op`
only in proof bodies; both public theorems are stated for states and measurements. -/

section MeasuredPhaseWire

open InnerProductSpace ContinuousLinearMap

/-- **Both readings of the single-wire phase-gate deferral, from one commutation.** For the
single-wire phase gate `V = Evolution.qtowerSingleWire n t (phaseShiftGate φ)` — diagonal in the
computational basis — the terminal per-wire measurement `qtowerMeasurement n` sees no gate:
measuring after `V` gives the same statistics (first conjunct) and the same collapsed states (second
conjunct, with the gate deferred unchanged as its own branch gate) as measuring first. Both are
instances of the deferred-measurement engine (Exercise 4.35) at `Wᵣ = V`; the shared commutation
`Mᵣ · V.op = V.op · Mᵣ` — established here once via the eigenvalue action of the phase gate on the
computational tower kets and the rank-one projector form of the measurement — carries both. Bundling
the readings in one statement shares that commutation (it names `.op` only inside this
proof). The commutation carries **four** readings: the two for the base measurement
`qtowerMeasurement n`, and — via the `onRight` lift (the commutation tensored
with the identity on the head wire) — the two for the tail measurement
`(qtowerMeasurement n).onRight qubit`, the `hM` premise the reading-level cascade-deferral engine
needs when a branch gate sits idle on the head wire. The public readings below project it. -/
private theorem qtowerSingleWire_phaseShiftGate_measure_defers (n : ℕ) (t : Fin (n + 1)) (φ : ℝ) :
    (∀ (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2),
        (qtowerMeasurement n).bornProb
            ((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).evolve ρ) r
          = (qtowerMeasurement n).bornProb ρ r)
    ∧ (∀ (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2)
        (hp : (qtowerMeasurement n).bornProb ρ r ≠ 0)
        (hp' : (qtowerMeasurement n).bornProb
            ((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).evolve ρ) r ≠ 0),
        (qtowerMeasurement n).postMeasurement
            ((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).evolve ρ) r hp'
          = (Evolution.qtowerSingleWire n t (phaseShiftGate φ)).evolve
              ((qtowerMeasurement n).postMeasurement ρ r hp))
    ∧ (∀ (τ : State (qubit ⊗ qtower n qubit)) (r : Fin (n + 1) → Fin 2),
        ((qtowerMeasurement n).onRight qubit).bornProb
            (((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).onRight qubit).evolve τ) r
          = ((qtowerMeasurement n).onRight qubit).bornProb τ r)
    ∧ (∀ (τ : State (qubit ⊗ qtower n qubit)) (r : Fin (n + 1) → Fin 2)
        (hp : ((qtowerMeasurement n).onRight qubit).bornProb τ r ≠ 0)
        (hp' : ((qtowerMeasurement n).onRight qubit).bornProb
            (((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).onRight qubit).evolve τ) r ≠ 0),
        ((qtowerMeasurement n).onRight qubit).postMeasurement
            (((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).onRight qubit).evolve τ) r hp'
          = ((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).onRight qubit).evolve
              (((qtowerMeasurement n).onRight qubit).postMeasurement τ r hp)) := by
  -- (1) The phase gate on wire `s` fixes each tower ket up to the phase `[1,e^{iφ}]_{b s}`.
  have heig : ∀ (m : ℕ) (s : Fin (m + 1)) (b : Fin (m + 1) → Fin 2),
      (Evolution.qtowerSingleWire m s (phaseShiftGate φ)).op (towerKet m b).vec
        = ![(1 : ℂ), Complex.exp ((φ : ℂ) * Complex.I)] (b s) • (towerKet m b).vec := by
    intro m
    induction m with
    | zero =>
        intro s b
        obtain rfl := Fin.fin_one_eq_zero s
        rw [towerKet_zero]
        exact phaseShiftGate_op_apply_qubitBasis φ (b 0)
    | succ k ih =>
        intro s b
        refine Fin.cases ?_ ?_ s
        · rw [Evolution.qtowerSingleWire_zero, towerKet_succ, PureState.tmul_vec]
          -- `erw`: the tower head-peel `qtower (n+1) qubit = qubit ⊗ qtower n qubit` is only
          -- definitional, so `onLeft_op_tmul` matches up to reducible defeq, not syntactically.
          erw [Evolution.onLeft_op_tmul]
          rw [phaseShiftGate_op_apply_qubitBasis]
          exact (TensorProduct.smul_tmul' _ _ _).symm
        · intro s'
          rw [Evolution.qtowerSingleWire_succ, towerKet_succ, PureState.tmul_vec]
          erw [Evolution.onRight_op_tmul]
          rw [ih s' (fun i => b i.succ)]
          exact TensorProduct.tmul_smul _ _ _
  -- (2) Each `qtowerMeasurement` operator is the rank-one projector onto its tower basis vector.
  have hmeas : ∀ (m : ℕ) (b : Fin (m + 1) → Fin 2),
      (qtowerMeasurement m).op b = rankOne ℂ (towerKet m b).vec (towerKet m b).vec := by
    intro m
    induction m with
    | zero =>
        intro b
        rw [qtowerMeasurement_zero, Measurement.reindexOutcome_op, quditMeasurement_op,
          towerKet_zero, quditBasis_vec, qubitBasis_vec]
        rfl
    | succ k ih =>
        intro b
        have hstep : (qtowerMeasurement (k + 1)).op b
            = TensorProduct.mapL (rankOne ℂ (qubitBasis (b 0)).vec (qubitBasis (b 0)).vec)
                (rankOne ℂ (towerKet k (fun i => b i.succ)).vec
                  (towerKet k (fun i => b i.succ)).vec) := by
          rw [qtowerMeasurement_succ, Measurement.reindexOutcome_op, Measurement.cascade_op,
            Measurement.onRight_op, controlMeasurement_op, ih,
            show ((Fin.consEquiv fun _ : Fin (k + 2) => Fin 2).symm b).1 = b 0 from rfl,
            show ((Fin.consEquiv fun _ : Fin (k + 2) => Fin 2).symm b).2
              = fun i => b i.succ from rfl]
          refine (TensorProduct.mapL_comp _ _ _ _).symm.trans ?_
          simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
            ContinuousLinearMap.comp_id]
        rw [hstep, towerKet_succ, PureState.tmul_vec]
        exact (InnerProductSpace.rankOne_tmul_self _ _).symm
  -- (3) The shared commutation `Mᵣ · V.op = V.op · Mᵣ`, from the eigenvector (heig) and the
  --     projector form (hmeas): the eigenvalue has unit modulus, so the adjoint conjugates it.
  have hcomm : ∀ r : Fin (n + 1) → Fin 2,
      ((qtowerMeasurement n).op r).comp (Evolution.qtowerSingleWire n t (phaseShiftGate φ)).op
        = (Evolution.qtowerSingleWire n t (phaseShiftGate φ)).op.comp
            ((qtowerMeasurement n).op r) := by
    intro r
    have hVu := heig n t r
    have hcc : (starRingEnd ℂ) (![(1 : ℂ), Complex.exp ((φ : ℂ) * Complex.I)] (r t))
        * ![(1 : ℂ), Complex.exp ((φ : ℂ) * Complex.I)] (r t) = 1 := by
      generalize r t = j
      fin_cases j
      · change (starRingEnd ℂ) (1 : ℂ) * (1 : ℂ) = 1
        simp
      · change (starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I))
            * Complex.exp ((φ : ℂ) * Complex.I) = 1
        rw [← Complex.exp_conj, ← Complex.exp_add,
          show (starRingEnd ℂ) ((φ : ℂ) * Complex.I) + (φ : ℂ) * Complex.I = 0 by
            rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring,
          Complex.exp_zero]
    have hadj : adjoint (Evolution.qtowerSingleWire n t (phaseShiftGate φ)).op (towerKet n r).vec
        = (starRingEnd ℂ) (![(1 : ℂ), Complex.exp ((φ : ℂ) * Complex.I)] (r t))
            • (towerKet n r).vec := by
      have h2 : adjoint (Evolution.qtowerSingleWire n t (phaseShiftGate φ)).op
            ((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).op (towerKet n r).vec)
          = (towerKet n r).vec := by
        rw [← ContinuousLinearMap.comp_apply,
          (Evolution.qtowerSingleWire n t (phaseShiftGate φ)).adjoint_comp_self,
          one_apply_eq_self]
      rw [hVu, map_smul] at h2
      have h3 := congrArg
        (fun w => (starRingEnd ℂ) (![(1 : ℂ), Complex.exp ((φ : ℂ) * Complex.I)] (r t)) • w) h2
      simp only [smul_smul] at h3
      rw [hcc, one_smul] at h3
      exact h3
    rw [hmeas n r, InnerProductSpace.rankOne_comp, comp_rankOne, hadj, hVu, ← smul_rankOne]
    -- Pull the conjugate eigenvalue off the ket via the library sesquilinearity of `rankOne`
    -- (`rankOne_smul_smul` at `s = 1`), rather than a bespoke right-argument helper.
    have key := rankOne_smul_smul (1 : ℂ)
      ((starRingEnd ℂ) (![(1 : ℂ), Complex.exp ((φ : ℂ) * Complex.I)] (r t)))
      (towerKet n r).vec (towerKet n r).vec
    rwa [one_smul, one_mul, Complex.conj_conj] at key
  -- (4) Feed the commutation to the deferred-measurement engine — for the base measurement
  --     `qtowerMeasurement n` (first two readings) and, via the `onRight` lift
  --     (the same commutation tensored with the identity on the head wire), for the tail
  --     measurement `(qtowerMeasurement n).onRight qubit` (last two readings). The `onRight`
  --     versions are the
  --     `hM` premise the reading-level cascade-deferral engine consumes: after the head-wire
  --     deferral each branch gate sits idle on the head wire (`onRight`-shaped) and must defer past
  --     the recursive tail factor of the terminal cascade measurement.
  refine ⟨fun ρ r => ?_, fun ρ r hp hp' => ?_, fun τ r => ?_, fun τ r hp hp' => ?_⟩
  · exact Measurement.bornProb_evolve_of_comm (qtowerMeasurement n)
      (Evolution.qtowerSingleWire n t (phaseShiftGate φ))
      (fun _ => Evolution.qtowerSingleWire n t (phaseShiftGate φ)) hcomm ρ r
  · exact Measurement.postMeasurement_evolve_of_comm (qtowerMeasurement n)
      (Evolution.qtowerSingleWire n t (phaseShiftGate φ))
      (fun _ => Evolution.qtowerSingleWire n t (phaseShiftGate φ)) hcomm ρ r hp
  · exact Measurement.bornProb_evolve_onRight_of_comm (qtowerMeasurement n)
      (Evolution.qtowerSingleWire n t (phaseShiftGate φ))
      (fun _ => Evolution.qtowerSingleWire n t (phaseShiftGate φ)) hcomm qubit τ r
  · exact Measurement.postMeasurement_evolve_onRight_of_comm (qtowerMeasurement n)
      (Evolution.qtowerSingleWire n t (phaseShiftGate φ))
      (fun _ => Evolution.qtowerSingleWire n t (phaseShiftGate φ)) hcomm qubit τ r hp

/-- **Problem 5.2 (a single-wire phase gate passes through the terminal measurement — statistics).**
Measuring every wire of the tower *after* the single-wire phase gate
`Evolution.qtowerSingleWire n t (phaseShiftGate φ)` — the shape of the QFT's classically-controlled
branch rotations — gives the same Born probability of every outcome bit-string `r` as measuring the
input `ρ` directly: the diagonal phase gate is invisible to the computational-basis statistics of
the terminal per-wire measurement `qtowerMeasurement n`. The first projection of
`qtowerSingleWire_phaseShiftGate_measure_defers` (the deferred-measurement engine at `Wᵣ = V`). This
is the `hM` premise the semiclassical induction feeds to the cascade-deferral engine for the QFT's
branch gates. -/
theorem qtowerSingleWire_phaseShiftGate_measure_bornProb (n : ℕ) (t : Fin (n + 1)) (φ : ℝ)
    (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2) :
    (qtowerMeasurement n).bornProb
        ((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).evolve ρ) r
      = (qtowerMeasurement n).bornProb ρ r :=
  (qtowerSingleWire_phaseShiftGate_measure_defers n t φ).1 ρ r

/-- **Problem 5.2 (a single-wire phase gate passes through the terminal measurement — collapse).**
The state after measuring outcome `r` on the input evolved by the single-wire phase gate
`Evolution.qtowerSingleWire n t (phaseShiftGate φ)` equals that same gate applied to the state after
measuring `ρ`:

  `postMeas(V ρ V†, r) = V · postMeas(ρ, r)`,

with `V = Evolution.qtowerSingleWire n t (phaseShiftGate φ)`. The gate **defers past** the terminal
per-wire measurement `qtowerMeasurement n` unchanged (its own branch gate on every outcome), because
it is diagonal in the computational basis and so commutes with each measurement projector. The
second projection of `qtowerSingleWire_phaseShiftGate_measure_defers`; the outcome is equally
possible after `V` because the probabilities agree
(`qtowerSingleWire_phaseShiftGate_measure_bornProb`). This — with the branch gate carried along a
control wire's cascade — is how the semiclassical induction
defers the terminal measurement past the QFT's diagonal branch rotations. -/
theorem qtowerSingleWire_phaseShiftGate_measure_postMeasurement (n : ℕ) (t : Fin (n + 1)) (φ : ℝ)
    (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2)
    (hp : (qtowerMeasurement n).bornProb ρ r ≠ 0) :
    (qtowerMeasurement n).postMeasurement
        ((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).evolve ρ) r
        (by rw [qtowerSingleWire_phaseShiftGate_measure_bornProb]; exact hp)
      = (Evolution.qtowerSingleWire n t (phaseShiftGate φ)).evolve
          ((qtowerMeasurement n).postMeasurement ρ r hp) :=
  (qtowerSingleWire_phaseShiftGate_measure_defers n t φ).2.1 ρ r hp
    (by rw [qtowerSingleWire_phaseShiftGate_measure_bornProb]; exact hp)

/-- **A single-wire phase gate on the tail passes through the tail measurement — statistics.** With
the head wire left idle, the lifted single-wire phase gate
`(Evolution.qtowerSingleWire n t (phaseShiftGate φ)).onRight qubit = 1 ⊗ V` is invisible to the
statistics of the lifted terminal measurement `(qtowerMeasurement n).onRight qubit = 1 ⊗
qtowerMeasurement n`: measuring after it gives the same Born probabilities as measuring first. The
third projection of `qtowerSingleWire_phaseShiftGate_measure_defers` — the `onRight` lift of the
base reading, from the same commutation. This is the single-gate `hM` premise the reading-level
cascade-deferral engine consumes for a control wire's deferred branch rotations on the recursive
tail factor of the terminal per-wire measurement. -/
theorem qtowerSingleWire_phaseShiftGate_onRight_measure_bornProb (n : ℕ) (t : Fin (n + 1)) (φ : ℝ)
    (τ : State (qubit ⊗ qtower n qubit)) (r : Fin (n + 1) → Fin 2) :
    ((qtowerMeasurement n).onRight qubit).bornProb
        (((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).onRight qubit).evolve τ) r
      = ((qtowerMeasurement n).onRight qubit).bornProb τ r :=
  (qtowerSingleWire_phaseShiftGate_measure_defers n t φ).2.2.1 τ r

/-- **A single-wire phase gate on the tail passes through the tail measurement — collapse.** With
the head wire left idle, the lifted single-wire phase gate
`(Evolution.qtowerSingleWire n t (phaseShiftGate φ)).onRight qubit` **defers past** the lifted
terminal measurement `(qtowerMeasurement n).onRight qubit` unchanged (its own branch gate):

  `postMeas((1 ⊗ V) τ (1 ⊗ V)†, r) = (1 ⊗ V) · postMeas(τ, r)`.

The fourth projection of `qtowerSingleWire_phaseShiftGate_measure_defers` — the `onRight` lift of
the base collapse reading, from the same commutation; the outcome is equally possible after the gate
because the probabilities agree (`qtowerSingleWire_phaseShiftGate_onRight_measure_bornProb`). This
is the single-gate `hM` collapse premise the reading-level cascade-deferral engine consumes. -/
theorem qtowerSingleWire_phaseShiftGate_onRight_measure_postMeasurement (n : ℕ) (t : Fin (n + 1))
    (φ : ℝ) (τ : State (qubit ⊗ qtower n qubit)) (r : Fin (n + 1) → Fin 2)
    (hp : ((qtowerMeasurement n).onRight qubit).bornProb τ r ≠ 0) :
    ((qtowerMeasurement n).onRight qubit).postMeasurement
        (((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).onRight qubit).evolve τ) r
        (by rw [qtowerSingleWire_phaseShiftGate_onRight_measure_bornProb]; exact hp)
      = ((Evolution.qtowerSingleWire n t (phaseShiftGate φ)).onRight qubit).evolve
          (((qtowerMeasurement n).onRight qubit).postMeasurement τ r hp) :=
  (qtowerSingleWire_phaseShiftGate_measure_defers n t φ).2.2.2 τ r hp
    (by rw [qtowerSingleWire_phaseShiftGate_onRight_measure_bornProb]; exact hp)

end MeasuredPhaseWire

/-! ### A whole cascade of single-wire phase gates passes through the terminal measurement

The previous section defers a *single* single-wire phase gate past the terminal per-wire measurement
`qtowerMeasurement n`. A control wire's *deferred* classical-control branch gate is, however, not
one gate but a whole **product** of them: after the head cascade's control measurement is deferred
(`qtowerHeadCtrlCascade_measure_head_postMeasurement`), its outcome-`1` branch is exactly the
composition of the single-wire phase gates on the tail wires
(`qtowerHeadCtrlCascade_classicalControl_isSingleWireGate`). The semiclassical induction must
therefore defer that whole product past the terminal measurement — the product form of
the `hM` premise the cascade-deferral engine
(`Measurement.…_cascade_of_comm`) consumes.

This section supplies it, as a thin instance of the reading-level deferral engine
`Measurement.{bornProb,postMeasurement}_evolve_prod_of_forall_defers`
(`AxQM/Core/DeferredMeasurementReading.lean`): the diagonal phase gates all pass through the
computational-basis measurement — each invisible to its statistics and deferring past it to itself
— so their whole composition `qtowerPhaseWireCascade n gs` has the same outcome
statistics and the same collapsed states as measuring first and applying the composition afterwards.
No new operator commutation is needed: the engine composes the single-gate *readings* down the list,
so both public readings are stated at the level of statistics and collapsed states. -/

section MeasuredPhaseWireCascade

/-- The **cascade of single-wire phase gates** on the tower `qtower n qubit`: the composition of the
single-wire phase gates `Evolution.qtowerSingleWire n t (phaseShiftGate φ)`, one for each pair
`(t, φ)` of `gs` (place `phaseShiftGate φ` on wire `t`). This is the shape of a control wire's
*deferred* classical-control branch gate:
`qtowerHeadCtrlCascade_classicalControl_isSingleWireGate`'s outcome-`1` branch is precisely such a
product of the single-wire phase rotations `phaseShiftGate (2π/2ᵏ)` on the tail wires, so the
semiclassical reduction defers this whole object past the terminal measurement. -/
def qtowerPhaseWireCascade (n : ℕ) (gs : List (Fin (n + 1) × ℝ)) : Evolution (qtower n qubit) :=
  (gs.map fun p => Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).prod

/-- **Problem 5.2 (a whole phase-gate cascade passes through the terminal measurement —
statistics).**
Measuring every wire of the tower *after* a cascade `qtowerPhaseWireCascade n gs` of single-wire
phase gates — the shape of a control wire's deferred classically-controlled branch rotations — gives
the same Born probability of every outcome bit-string `r` as measuring the input `ρ` directly: the
diagonal phase gates are invisible to the computational-basis statistics of the terminal per-wire
measurement `qtowerMeasurement n`. A thin instance of the engine
`Measurement.bornProb_evolve_prod_of_forall_defers`, each gate's invariance supplied by the
single-gate reading `qtowerSingleWire_phaseShiftGate_measure_bornProb`. This is the product form of
the `hM` premise the semiclassical induction feeds to the cascade-deferral engine (3b-v-b1). -/
theorem qtowerPhaseWireCascade_measure_bornProb (n : ℕ) (gs : List (Fin (n + 1) × ℝ))
    (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2) :
    (qtowerMeasurement n).bornProb ((qtowerPhaseWireCascade n gs).evolve ρ) r
      = (qtowerMeasurement n).bornProb ρ r := by
  have hb : ∀ (p : Fin (n + 1) × ℝ) (σ : State (qtower n qubit)) (s : Fin (n + 1) → Fin 2),
      (qtowerMeasurement n).bornProb
          ((Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).evolve σ) s
        = (qtowerMeasurement n).bornProb σ s :=
    fun p σ s => qtowerSingleWire_phaseShiftGate_measure_bornProb n p.1 p.2 σ s
  unfold qtowerPhaseWireCascade
  exact Measurement.bornProb_evolve_prod_of_forall_defers (qtowerMeasurement n) _ hb gs ρ r

/-- **Problem 5.2 (a whole phase-gate cascade passes through the terminal measurement — collapse).**
The state after measuring outcome `r` on the input evolved by a cascade
`qtowerPhaseWireCascade n gs` of single-wire phase gates equals that same cascade applied to the
state after measuring `ρ`:

  `postMeas(V ρ V†, r) = V · postMeas(ρ, r)`,

with `V = qtowerPhaseWireCascade n gs`. The whole product of diagonal phase gates **defers past**
the terminal per-wire measurement `qtowerMeasurement n` unchanged (its own branch gate on every
outcome), because each factor is diagonal in the computational basis. A thin instance of the
engine `Measurement.postMeasurement_evolve_prod_of_forall_defers` with branch family
`W p _ = V p` (each gate defers to itself), the per-gate deferral supplied by the single-gate
reading `qtowerSingleWire_phaseShiftGate_measure_defers`; the outcome is equally possible after `V`
because
the probabilities agree (`qtowerPhaseWireCascade_measure_bornProb`). This — a control wire's whole
deferred branch cascade — is what the semiclassical induction defers past the tail measurement. -/
theorem qtowerPhaseWireCascade_measure_postMeasurement (n : ℕ) (gs : List (Fin (n + 1) × ℝ))
    (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2)
    (hp : (qtowerMeasurement n).bornProb ρ r ≠ 0) :
    (qtowerMeasurement n).postMeasurement ((qtowerPhaseWireCascade n gs).evolve ρ) r
        (by rw [qtowerPhaseWireCascade_measure_bornProb]; exact hp)
      = (qtowerPhaseWireCascade n gs).evolve
          ((qtowerMeasurement n).postMeasurement ρ r hp) := by
  -- Feed the per-gate readings to the shared engine as *typed* hypotheses, letting it infer the
  -- gate family `V` and branch family `W` from them (passing the gate lambda explicitly instead
  -- makes the elaborator diverge unifying it against this large-outcome measurement).
  have hb : ∀ (p : Fin (n + 1) × ℝ) (σ : State (qtower n qubit)) (s : Fin (n + 1) → Fin 2),
      (qtowerMeasurement n).bornProb
          ((Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).evolve σ) s
        = (qtowerMeasurement n).bornProb σ s :=
    fun p σ s => qtowerSingleWire_phaseShiftGate_measure_bornProb n p.1 p.2 σ s
  have hpm : ∀ (p : Fin (n + 1) × ℝ) (σ : State (qtower n qubit)) (s : Fin (n + 1) → Fin 2)
      (hσ : (qtowerMeasurement n).bornProb σ s ≠ 0)
      (hσ' : (qtowerMeasurement n).bornProb
          ((Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).evolve σ) s ≠ 0),
      (qtowerMeasurement n).postMeasurement
          ((Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).evolve σ) s hσ'
        = (Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).evolve
            ((qtowerMeasurement n).postMeasurement σ s hσ) :=
    fun p σ s hσ hσ' => (qtowerSingleWire_phaseShiftGate_measure_defers n p.1 p.2).2.1 σ s hσ hσ'
  have hp' : (qtowerMeasurement n).bornProb ((qtowerPhaseWireCascade n gs).evolve ρ) r ≠ 0 := by
    rw [qtowerPhaseWireCascade_measure_bornProb]; exact hp
  exact Measurement.postMeasurement_evolve_prod_of_forall_defers (qtowerMeasurement n) _ _ hb hpm
    gs ρ r hp hp'

end MeasuredPhaseWireCascade

/-! ### The deferred branch cascade passes through the *tail* measurement (`hM`)

The terminal per-wire measurement is a **cascade** (`qtowerMeasurement_succ`): the head-wire
measurement `controlMeasurement (qtower n qubit)`, then the recursive tail
`(qtowerMeasurement n).onRight qubit` measuring the remaining wires. After the head control wire's
controlled-`Rₖ` cascade is deferred past the *head* measurement
(`qtowerHeadCtrlCascade_measure_head_*` — the `hL` premise), each
classically-controlled branch gate is a whole product of single-wire phase gates on the *tail*
wires, idle on the head wire: an `onRight`-shaped cascade
`(qtowerPhaseWireCascade n gs).onRight qubit = 1 ⊗ (phase cascade)`
(`qtowerHeadCtrlCascade_classicalControl_isSingleWireGate`, outcome-`1` branch). For the
reading-level cascade-deferral engine (`Measurement.…_evolve_cascade_of_defers`) to
defer the head cascade past the *whole* terminal measurement, that branch must in turn defer past
the *tail* factor `(qtowerMeasurement n).onRight qubit` — the engine's **`hM`** premise.

This section supplies it. Each single-wire phase gate on the tail defers past the tail measurement
(the `onRight` readings `qtowerSingleWire_phaseShiftGate_onRight_measure_*` above, the `onRight`
lift of the diagonal-gate commutation), so the reading-level product engine
(`Measurement.{bornProb,postMeasurement}_evolve_prod_of_forall_defers`,
`AxQM/Core/DeferredMeasurementReading.lean`) composes them into the whole branch cascade's
deferral — `Evolution.onRight_list_prod` identifying the product of the lifted gates with the lift
of the product. -/

section MeasuredPhaseWireCascadeOnRight

/-- **The `onRight` lift of a phase-wire cascade is the product of the lifted single-wire gates:**
`(∏ⱼ Vⱼ).onRight qubit = ∏ⱼ (Vⱼ.onRight qubit)`, i.e. leaving the head wire idle commutes with
taking the cascade. `Evolution.onRight` is a monoid homomorphism (`Evolution.onRight_list_prod`), so
it carries the `List.prod` defining `qtowerPhaseWireCascade` through the map. This lets both
readings below run the shared reading-level product engine on the lifted single-gate gates. -/
theorem qtowerPhaseWireCascade_onRight_eq_prod (n : ℕ) (gs : List (Fin (n + 1) × ℝ)) :
    (qtowerPhaseWireCascade n gs).onRight qubit
      = (gs.map fun p =>
          (Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).onRight qubit).prod := by
  unfold qtowerPhaseWireCascade
  rw [← Evolution.onRight_list_prod qubit (qtower n qubit), List.map_map]
  rfl

/-- **The branch phase-cascade passes through the tail measurement — statistics (`hM`).** With the
head wire left idle, a whole cascade of single-wire phase gates on the tail
`(qtowerPhaseWireCascade n gs).onRight qubit = 1 ⊗ (phase cascade)` — the shape of a control wire's
deferred classically-controlled branch rotations — is invisible to the statistics of the tail
measurement `(qtowerMeasurement n).onRight qubit`: measuring after it gives the same Born
probabilities as measuring first. A thin instance of the engine
`Measurement.bornProb_evolve_prod_of_forall_defers` over the lifted single-gate readings
`qtowerSingleWire_phaseShiftGate_onRight_measure_bornProb`, `Evolution.onRight_list_prod` reducing
the product of lifted gates to the lifted product. This is the statistics half of the `hM` premise
the reading-level cascade-deferral engine consumes for the head wire's deferred branches. -/
theorem qtowerPhaseWireCascade_onRight_measure_bornProb (n : ℕ) (gs : List (Fin (n + 1) × ℝ))
    (τ : State (qubit ⊗ qtower n qubit)) (r : Fin (n + 1) → Fin 2) :
    ((qtowerMeasurement n).onRight qubit).bornProb
        (((qtowerPhaseWireCascade n gs).onRight qubit).evolve τ) r
      = ((qtowerMeasurement n).onRight qubit).bornProb τ r := by
  rw [qtowerPhaseWireCascade_onRight_eq_prod]
  have hb : ∀ (p : Fin (n + 1) × ℝ) (σ : State (qubit ⊗ qtower n qubit))
      (s : Fin (n + 1) → Fin 2),
      ((qtowerMeasurement n).onRight qubit).bornProb
          (((Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).onRight qubit).evolve σ) s
        = ((qtowerMeasurement n).onRight qubit).bornProb σ s :=
    fun p σ s => qtowerSingleWire_phaseShiftGate_onRight_measure_bornProb n p.1 p.2 σ s
  exact Measurement.bornProb_evolve_prod_of_forall_defers
    ((qtowerMeasurement n).onRight qubit) _ hb gs τ r

/-- **The branch phase-cascade passes through the tail measurement — collapse (`hM`).** With the
head wire left idle, a whole cascade of single-wire phase gates on the tail
`(qtowerPhaseWireCascade n gs).onRight qubit` **defers past** the tail measurement
`(qtowerMeasurement n).onRight qubit` unchanged (its own branch gate on every outcome):

  `postMeas((1 ⊗ V) τ (1 ⊗ V)†, r) = (1 ⊗ V) · postMeas(τ, r)`,   `V = qtowerPhaseWireCascade n gs`.

A thin instance of the engine
`Measurement.postMeasurement_evolve_prod_of_forall_defers` (branch family the gate itself) over the
lifted single-gate readings, `Evolution.onRight_list_prod` reducing the product of lifted gates —
and of their branch gates — to the lifted product; the outcome is equally possible after the gate
because the probabilities agree (`qtowerPhaseWireCascade_onRight_measure_bornProb`). This is the
collapse half of the `hM` premise the reading-level cascade-deferral engine consumes for the head
wire's deferred branches. -/
theorem qtowerPhaseWireCascade_onRight_measure_postMeasurement (n : ℕ) (gs : List (Fin (n + 1) × ℝ))
    (τ : State (qubit ⊗ qtower n qubit)) (r : Fin (n + 1) → Fin 2)
    (hp : ((qtowerMeasurement n).onRight qubit).bornProb τ r ≠ 0) :
    ((qtowerMeasurement n).onRight qubit).postMeasurement
        (((qtowerPhaseWireCascade n gs).onRight qubit).evolve τ) r
        (by rw [qtowerPhaseWireCascade_onRight_measure_bornProb]; exact hp)
      = ((qtowerPhaseWireCascade n gs).onRight qubit).evolve
          (((qtowerMeasurement n).onRight qubit).postMeasurement τ r hp) := by
  have hb : ∀ (p : Fin (n + 1) × ℝ) (σ : State (qubit ⊗ qtower n qubit))
      (s : Fin (n + 1) → Fin 2),
      ((qtowerMeasurement n).onRight qubit).bornProb
          (((Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).onRight qubit).evolve σ) s
        = ((qtowerMeasurement n).onRight qubit).bornProb σ s :=
    fun p σ s => qtowerSingleWire_phaseShiftGate_onRight_measure_bornProb n p.1 p.2 σ s
  have hpm : ∀ (p : Fin (n + 1) × ℝ) (σ : State (qubit ⊗ qtower n qubit))
      (s : Fin (n + 1) → Fin 2)
      (hσ : ((qtowerMeasurement n).onRight qubit).bornProb σ s ≠ 0)
      (hσ' : ((qtowerMeasurement n).onRight qubit).bornProb
          (((Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).onRight qubit).evolve σ) s ≠ 0),
      ((qtowerMeasurement n).onRight qubit).postMeasurement
          (((Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).onRight qubit).evolve σ) s hσ'
        = ((Evolution.qtowerSingleWire n p.1 (phaseShiftGate p.2)).onRight qubit).evolve
            (((qtowerMeasurement n).onRight qubit).postMeasurement σ s hσ) :=
    fun p σ s hσ _ =>
      qtowerSingleWire_phaseShiftGate_onRight_measure_postMeasurement n p.1 p.2 σ s hσ
  have hp' : ((qtowerMeasurement n).onRight qubit).bornProb
      (((qtowerPhaseWireCascade n gs).onRight qubit).evolve τ) r ≠ 0 := by
    rw [qtowerPhaseWireCascade_onRight_measure_bornProb]; exact hp
  -- Go through operators (`State.ext` + `postMeasurement_op`) to avoid rewriting the gate
  -- (`qtowerPhaseWireCascade_onRight_eq_prod`) underneath the dependent possibility proof of
  -- `postMeasurement`. Pass the gate/branch families as `_` (inferred from the typed `hb`/`hpm`);
  -- giving the gate lambda explicitly diverges the elaborator's `whnf` on this large
  -- function-outcome measurement.
  have hmain := congrArg State.op (Measurement.postMeasurement_evolve_prod_of_forall_defers
    ((qtowerMeasurement n).onRight qubit) _ _ hb hpm gs τ r hp
    (qtowerPhaseWireCascade_onRight_eq_prod n gs ▸ hp'))
  rw [Measurement.postMeasurement_op] at hmain
  apply State.ext
  rw [Measurement.postMeasurement_op, qtowerPhaseWireCascade_onRight_eq_prod]
  exact hmain

end MeasuredPhaseWireCascadeOnRight

/-! ### A gate defers past a *cascade* of measurements, at the reading level

The terminal per-wire measurement `qtowerMeasurement (n+1)` is a **cascade**
(`qtowerMeasurement_succ`): measure the head wire (`controlMeasurement`), then the recursive tail
(`(qtowerMeasurement n).onRight qubit`). The semiclassical reduction defers a control wire's
controlled-`Rₖ` cascade past that whole terminal measurement one measured factor at a time, so it
needs to defer a gate past a `Measurement.cascade`. There is already an operator-level engine for
this — `Measurement.{bornProb,postMeasurement}_evolve_cascade_of_comm`
(`AxQM/Postulates/API/DeferredCascadeMeasurement.lean`) — but it consumes the *operator*
commutations `Mᵢ V = Wᵢ Mᵢ`, which are not available as lemmas for the tower gates
(`qtowerSingleWire` past `qtowerMeasurement`). What is available for the tower gates is their two
Postulate *readings* — the head cascade's head-wire deferral
(`qtowerHeadCtrlCascade_measure_head_*`) and each branch gate's tail deferral (through the
`onRight` lift).

This section is the **reading-level analog of that operator engine**: it composes those readings
across a `Measurement.cascade`, so a gate that defers past the head measurement (readings
`hLb`/`hLp`) and
whose head-branch gates each defer past the tail measurement (readings `hMb`/`hMp`) defers past the
whole cascade, with no operator commutation needed — as for
`AxQM/Core/DeferredMeasurementReading.lean` (the product engine), which is also stated at the
reading level. The bridge from the cascade's readings to the two factors' readings is N&C
Exercise 2.57's chain rule `cascade_bornProb` / `cascade_postMeasurement`
(`AxQM/NC/Ch2/Exercise2_57.lean`). Every statement is about `Measurement.bornProb`,
`Measurement.postMeasurement`, `Measurement.cascade` and `Evolution.evolve`. The semiclassical
induction instantiates it with the tower head/tail measurements and the QFT's controlled-`Rₖ`
cascade. -/

section CascadeDeferralReading

open ContinuousLinearMap InnerProductSpace

variable {κ μ : Type*} [Fintype κ] [Fintype μ] {S : QSystem}

/-- **A joint cascade outcome is bounded by its first-stage probability.** For the cascade
`L.cascade M`, `p(l, m) ≤ p(l)`: measuring `M` after `L` can only lose probability. The
plain-cascade counterpart of `adaptiveCascade_bornProb_le_fst`, from `re_trace_postOp_le` on the
positive branch
operator `Eₗ(ρ) = Lₗ ρ Lₗ†` (`postOp_cascade`). Used below to discharge the impossible first-stage
branches (where `p(l) = 0`) of the reading-level cascade deferral. -/
private theorem Measurement.cascade_bornProb_le_fst (L : Measurement κ S) (M : Measurement μ S)
    (ρ : State S) (l : κ) (m : μ) :
    (L.cascade M).bornProb ρ (l, m) ≤ L.bornProb ρ l := by
  rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.bornProb_eq_re_trace_postOp,
    Measurement.postOp_cascade]
  exact M.re_trace_postOp_le (ContinuousLinearMap.postOp L.op ρ.op l)
    ((ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.postOp_isPositive L.op ρ.isPositive_op l)) m

/-- **A possible joint cascade outcome forces its first stage to be possible.** If the cascade's
joint outcome `(l, m)` has nonzero probability, then so does the first-stage outcome `l`
(`p(l, m) ≤ p(l)` with `p(l, m) > 0`). This discharges the first-stage possibility hypothesis of the
chain rule `cascade_bornProb` / `cascade_postMeasurement` in the deferral below, where only the
joint outcome's possibility is given. -/
private theorem Measurement.cascade_bornProb_fst_ne_zero (L : Measurement κ S) (M : Measurement μ S)
    (ρ : State S) (l : κ) (m : μ) (h : (L.cascade M).bornProb ρ (l, m) ≠ 0) :
    L.bornProb ρ l ≠ 0 := fun hL =>
  h (le_antisymm (hL ▸ Measurement.cascade_bornProb_le_fst L M ρ l m)
    ((L.cascade M).bornProb_nonneg ρ (l, m)))

/-- **Joint outcome probabilities are unchanged when a gate is deferred past a cascade measurement,
from the per-factor readings** (Postulate 3). If the gate `V` is invisible to the head measurement
`L`'s statistics (`hLb`) and defers past `L` to a head-branch family `W` (`hLp`), and each
head-branch gate `Wᵢ` is in turn invisible to the tail measurement `M`'s statistics (`hMb`), then
the joint
outcome `(i, r)` of the cascade `L.cascade M` has the same Born probability on `V ρ V†` as on `ρ`:
the cascade's statistics do not see `V`. Cases on whether the first stage is possible: on an
impossible first-stage outcome both joint probabilities vanish (`cascade_bornProb_le_fst`); on a
possible one the chain rule `cascade_bornProb` factors both sides as `p(i) · p(r ∣ i)`, and `hLb`,
`hLp`, `hMb` rewrite the deferred factors back to the undeferred ones. The reading-level analog of
`bornProb_evolve_cascade_of_comm`, usable when the per-gate commutation cannot be
named over `.op`. -/
theorem Measurement.bornProb_evolve_cascade_of_defers (L : Measurement κ S) (M : Measurement μ S)
    (V : Evolution S) (W : κ → Evolution S)
    (hLb : ∀ (ρ : State S) (i : κ), L.bornProb (V.evolve ρ) i = L.bornProb ρ i)
    (hLp : ∀ (ρ : State S) (i : κ) (hp : L.bornProb ρ i ≠ 0)
        (hp' : L.bornProb (V.evolve ρ) i ≠ 0),
        L.postMeasurement (V.evolve ρ) i hp' = (W i).evolve (L.postMeasurement ρ i hp))
    (hMb : ∀ (i : κ) (σ : State S) (r : μ), M.bornProb ((W i).evolve σ) r = M.bornProb σ r)
    (ρ : State S) (p : κ × μ) :
    (L.cascade M).bornProb (V.evolve ρ) p = (L.cascade M).bornProb ρ p := by
  obtain ⟨i, r⟩ := p
  by_cases hi : L.bornProb ρ i = 0
  · have hLV : L.bornProb (V.evolve ρ) i = 0 := (hLb ρ i).trans hi
    rw [le_antisymm ((Measurement.cascade_bornProb_le_fst L M (V.evolve ρ) i r).trans_eq hLV)
          ((L.cascade M).bornProb_nonneg (V.evolve ρ) (i, r)),
        le_antisymm ((Measurement.cascade_bornProb_le_fst L M ρ i r).trans_eq hi)
          ((L.cascade M).bornProb_nonneg ρ (i, r))]
  · have hiV : L.bornProb (V.evolve ρ) i ≠ 0 := by rw [hLb]; exact hi
    rw [cascade_bornProb L M (V.evolve ρ) i r hiV, cascade_bornProb L M ρ i r hi,
        hLb ρ i, hLp ρ i hi hiV, hMb i (L.postMeasurement ρ i hi) r]

/-- **The joint post-measurement state defers the gate past a cascade measurement, from the
per-factor readings** (Postulate 4). Under the four readings — `V` invisible to / deferring past the
head measurement `L` (`hLb`/`hLp`, to head-branch `W`), and each head-branch `Wᵢ` invisible to /
deferring past the tail measurement `M` (`hMb`/`hMp`, to `W'ᵢᵣ`) — the state after measuring the
joint outcome `(i, r)` of `L.cascade M` on `V ρ V†` equals the branch gate `W'ᵢᵣ` applied to the
state after measuring `ρ`:

  `postMeas(V ρ V†, (i, r)) = W'ᵢᵣ · postMeas(ρ, (i, r))`.

The chain rule `cascade_postMeasurement` collapses both cascade post-states into "collapse under
`L`, then under `M`"; `hLp` defers `V` off the inner `L`-collapse (leaving `Wᵢ` on the branch),
then `hMp` defers `Wᵢ` off the outer `M`-collapse (leaving `W'ᵢᵣ`), with
`postMeasurement_congr_state` moving
the measured state across the peel without dependent-cast friction. First-stage and second-stage
possibility are recovered from the joint possibility `hp` via `cascade_bornProb_fst_ne_zero` and
`cascade_bornProb`. The reading-level analog of `postMeasurement_evolve_cascade_of_comm`. -/
theorem Measurement.postMeasurement_evolve_cascade_of_defers (L : Measurement κ S)
    (M : Measurement μ S) (V : Evolution S) (W : κ → Evolution S) (W' : κ → μ → Evolution S)
    (hLb : ∀ (ρ : State S) (i : κ), L.bornProb (V.evolve ρ) i = L.bornProb ρ i)
    (hLp : ∀ (ρ : State S) (i : κ) (hp : L.bornProb ρ i ≠ 0)
        (hp' : L.bornProb (V.evolve ρ) i ≠ 0),
        L.postMeasurement (V.evolve ρ) i hp' = (W i).evolve (L.postMeasurement ρ i hp))
    (hMb : ∀ (i : κ) (σ : State S) (r : μ), M.bornProb ((W i).evolve σ) r = M.bornProb σ r)
    (hMp : ∀ (i : κ) (σ : State S) (r : μ) (hq : M.bornProb σ r ≠ 0)
        (hq' : M.bornProb ((W i).evolve σ) r ≠ 0),
        M.postMeasurement ((W i).evolve σ) r hq' = (W' i r).evolve (M.postMeasurement σ r hq))
    (ρ : State S) (p : κ × μ) (hp : (L.cascade M).bornProb ρ p ≠ 0) :
    (L.cascade M).postMeasurement (V.evolve ρ) p
        (by rw [Measurement.bornProb_evolve_cascade_of_defers L M V W hLb hLp hMb]; exact hp)
      = (W' p.1 p.2).evolve ((L.cascade M).postMeasurement ρ p hp) := by
  obtain ⟨i, r⟩ := p
  have hi : L.bornProb ρ i ≠ 0 := Measurement.cascade_bornProb_fst_ne_zero L M ρ i r hp
  have hiV : L.bornProb (V.evolve ρ) i ≠ 0 := by rw [hLb]; exact hi
  have hr : M.bornProb (L.postMeasurement ρ i hi) r ≠ 0 := fun h0 =>
    hp (by rw [cascade_bornProb L M ρ i r hi, h0, mul_zero])
  have hLpost : L.postMeasurement (V.evolve ρ) i hiV = (W i).evolve (L.postMeasurement ρ i hi) :=
    hLp ρ i hi hiV
  have hrV : M.bornProb (L.postMeasurement (V.evolve ρ) i hiV) r ≠ 0 := by
    rw [hLpost, hMb]; exact hr
  rw [cascade_postMeasurement L M (V.evolve ρ) i r hiV hrV,
      cascade_postMeasurement L M ρ i r hi hr]
  have hrV' : M.bornProb ((W i).evolve (L.postMeasurement ρ i hi)) r ≠ 0 := by rw [hMb]; exact hr
  rw [M.postMeasurement_congr_state hLpost hrV hrV', hMp i (L.postMeasurement ρ i hi) r hr hrV']

end CascadeDeferralReading

/-! ### The head control-wire phase cascade defers past the *whole* terminal measurement

The cascade reduction above defers a control wire's controlled-`Rₖ` cascade past the *head-wire*
measurement `controlMeasurement (qtower n qubit)` — bound to the concrete tower gates the measured
quantum Fourier transform produces (`qtowerHeadCtrlCascade_measure_head_*`, the head
readings
`hLb`/`hLp`). But the measured QFT measures *every* wire: the terminal measurement is the
whole-tower
`qtowerMeasurement (n+1)`, which is a **cascade** (`qtowerMeasurement_succ`) of the
head-wire measurement and the recursive tail `(qtowerMeasurement n).onRight qubit`, relabelled by
`Fin.consEquiv`. This section combines the head-wire deferral with the branches' tail deferral
(`qtowerPhaseWireCascade_onRight_measure_*`, the tail readings `hMb`/`hMp`) through the
reading-level cascade-deferral engine
(`Measurement.{bornProb,postMeasurement}_evolve_cascade_of_defers`): the head control wire's
*entire*
controlled-`Rₖ` phase cascade `qtowerHeadPhaseCascade n gs` defers past the whole terminal
measurement. Measuring every wire after the cascade has the same statistics
(`qtowerHeadPhaseCascade_measure_bornProb`) and the same collapsed states
(`qtowerHeadPhaseCascade_measure_postMeasurement`) as measuring first and then applying the
**classically-controlled** single-wire phase cascade `qtowerHeadPhaseBranch n gs (r 0)` — control
the
tail phase rotations on the measured head bit `r 0`, with nothing left on the head wire. This is the
head-wire step of the semiclassical reduction at the scale of the whole terminal measurement; the
outer tower induction recurses it over the tail.

The engine works on a bare `Measurement.cascade`, but `qtowerMeasurement (n+1)` is that cascade
**relabelled** (`reindexOutcome`) by `Fin.consEquiv`. Relabelling only renames outcomes, so a gate
defers past `m.reindexOutcome e` exactly when it defers past `m`, with its branch family reindexed
along `e`; the two reading-level transfer lemmas
`Measurement.{bornProb,postMeasurement}_evolve_reindexOutcome_of_defers` are proved here from
`reindexOutcome_bornProb` / `reindexOutcome_postMeasurement`. -/

section MeasuredHeadPhaseCascade

/-- **A deferral survives an outcome relabelling — statistics.** Relabelling the outcomes leaves the
Born probability of each renamed outcome equal to the original's (`reindexOutcome_bornProb`), so a
gate `V` invisible to `m`'s statistics is invisible to those of `m.reindexOutcome e`. -/
theorem Measurement.bornProb_evolve_reindexOutcome_of_defers {ι Y : Type*} [Fintype ι] [Fintype Y]
    {S : QSystem} (m : Measurement ι S) (e : Y ≃ ι) (V : Evolution S)
    (hb : ∀ (ρ : State S) (i : ι), m.bornProb (V.evolve ρ) i = m.bornProb ρ i)
    (ρ : State S) (y : Y) :
    (m.reindexOutcome e).bornProb (V.evolve ρ) y = (m.reindexOutcome e).bornProb ρ y := by
  rw [Measurement.reindexOutcome_bornProb, Measurement.reindexOutcome_bornProb, hb]

/-- **A deferral survives an outcome relabelling — collapse.** If `V` defers past `m` to a branch
family `W` (`hp`), then it defers past `m.reindexOutcome e` to the reindexed branch `W ∘ e`:
relabelling only renames outcomes, so the collapse reading `y` is the collapse of `m` reading `e y`
(`reindexOutcome_postMeasurement`), off which `hp` defers `V`. -/
theorem Measurement.postMeasurement_evolve_reindexOutcome_of_defers {ι Y : Type*} [Fintype ι]
    [Fintype Y] {S : QSystem} (m : Measurement ι S) (e : Y ≃ ι) (V : Evolution S)
    (W : ι → Evolution S)
    (hp : ∀ (ρ : State S) (i : ι) (h : m.bornProb ρ i ≠ 0) (h' : m.bornProb (V.evolve ρ) i ≠ 0),
        m.postMeasurement (V.evolve ρ) i h' = (W i).evolve (m.postMeasurement ρ i h))
    (ρ : State S) (y : Y) (hy : (m.reindexOutcome e).bornProb ρ y ≠ 0)
    (hy' : (m.reindexOutcome e).bornProb (V.evolve ρ) y ≠ 0) :
    (m.reindexOutcome e).postMeasurement (V.evolve ρ) y hy'
      = (W (e y)).evolve ((m.reindexOutcome e).postMeasurement ρ y hy) := by
  rw [Measurement.reindexOutcome_postMeasurement, Measurement.reindexOutcome_postMeasurement]
  exact hp ρ (e y) _ _

/-- **`classicalControl · i` carries a list product to the product of the controlled gates:**
`(l.map (classicalControl · i)).prod = classicalControl l.prod i`. On outcome `0` every factor is
the identity (`classicalControl_zero`) and both sides are `1`; on outcome `1` every factor is the
right-factor embedding (`classicalControl_one`), so `Evolution.onRight_list_prod` carries the
product. Lets a cascade of classically-controlled branch gates collapse to the single classical
control of the cascade. -/
theorem classicalControl_list_prod {S : QSystem} (l : List (Evolution S)) (i : Fin 2) :
    (l.map fun U => classicalControl U i).prod = classicalControl l.prod i := by
  fin_cases i <;>
    simp only [Fin.mk_zero, Fin.mk_one, classicalControl_zero, classicalControl_one,
      ← Evolution.one_def, List.prod_map_one, Evolution.onRight_list_prod]

/-- The QFT's **head control wire cascade specialised to phase gates**: the head-controlled
controlled-`Rₖ` block `qtowerHeadCtrlCascade` with each target gate the single-qubit phase gate
`phaseShiftGate φ` of `gs` (for the QFT, `φ = 2π/2ᵏ`). The head wire `0` controls a
`phaseShiftGate (gs.get j).2` on the tail wire `(gs.get j).1.succ` for each `j`. This is how one
control wire of the measured quantum Fourier transform sits on the tower once its Figure 5.1
controlled-`Rₖ` gates are re-expressed as wire-addressed tower gates. -/
def qtowerHeadPhaseCascade (n : ℕ) (gs : List (Fin (n + 1) × ℝ)) :
    Evolution (qtower (n + 1) qubit) :=
  qtowerHeadCtrlCascade n (gs.map fun p => (p.1, phaseShiftGate p.2))

/-- The **classically-controlled branch gate** the deferred head phase cascade leaves on outcome `i`
of the head wire: `classicalControl (qtowerPhaseWireCascade n gs) i` — control the whole tail phase
cascade `qtowerPhaseWireCascade n gs` on the head bit. On outcome `0` it is the identity; on outcome
`1` it is the phase cascade on the tail wires (`(qtowerPhaseWireCascade n gs).onRight qubit`),
idle on
the head wire. After the head wire is measured, its two-wire controlled-`Rₖ` block has become this
single-wire phase cascade with classical control — the "no two qubit gates" conclusion at the head
wire. -/
def qtowerHeadPhaseBranch (n : ℕ) (gs : List (Fin (n + 1) × ℝ)) (i : Fin 2) :
    Evolution (qtower (n + 1) qubit) :=
  classicalControl (qtowerPhaseWireCascade n gs) i

/-- The head cascade's deferred branch (its classically-controlled single-wire gates) is
exactly `qtowerHeadPhaseBranch`: the product of classically-controlled single-wire phase gates
equals
the classical control of the phase cascade (`classicalControl_list_prod`), and that phase cascade is
`qtowerPhaseWireCascade n gs`. This identifies the head readings' branch family with the clean
classically-controlled phase cascade. -/
theorem qtowerHeadPhaseBranch_eq (n : ℕ) (gs : List (Fin (n + 1) × ℝ)) (i : Fin 2) :
    (((gs.map fun p => (p.1, phaseShiftGate p.2)).map
          fun p => Evolution.qtowerSingleWire n p.1 p.2).map fun U => classicalControl U i).prod
      = qtowerHeadPhaseBranch n gs i := by
  rw [qtowerHeadPhaseBranch, classicalControl_list_prod]
  congr 1
  rw [qtowerPhaseWireCascade, List.map_map]
  rfl

/-- Each branch gate is invisible to the tail measurement's statistics:
`qtowerHeadPhaseBranch n gs i` defers past `(qtowerMeasurement n).onRight qubit`. Outcome `0` is the
identity (trivial); outcome `1` is the tail phase cascade `(qtowerPhaseWireCascade n gs).onRight
qubit`, invisible to the tail statistics by `qtowerPhaseWireCascade_onRight_measure_bornProb`.
This is the engine's `hMb` premise for the head wire's branches. -/
theorem qtowerHeadPhaseBranch_onRight_measure_bornProb (n : ℕ) (gs : List (Fin (n + 1) × ℝ))
    (i : Fin 2) (σ : State (qubit ⊗ qtower n qubit)) (r : Fin (n + 1) → Fin 2) :
    ((qtowerMeasurement n).onRight qubit).bornProb ((qtowerHeadPhaseBranch n gs i).evolve σ) r
      = ((qtowerMeasurement n).onRight qubit).bornProb σ r := by
  fin_cases i
  · -- outcome `0`: the branch is the identity (`classicalControl _ 0 = Evolution.id`)
    change ((qtowerMeasurement n).onRight qubit).bornProb (Evolution.id.evolve σ) r
        = ((qtowerMeasurement n).onRight qubit).bornProb σ r
    rw [Evolution.evolve_id]
  · -- outcome `1`: the branch is the tail phase cascade (`classicalControl _ 1 = ·.onRight qubit`)
    change ((qtowerMeasurement n).onRight qubit).bornProb
        (((qtowerPhaseWireCascade n gs).onRight qubit).evolve σ) r
        = ((qtowerMeasurement n).onRight qubit).bornProb σ r
    exact qtowerPhaseWireCascade_onRight_measure_bornProb n gs σ r

/-- Each branch gate defers past the tail measurement to itself:
`qtowerHeadPhaseBranch n gs i` defers past `(qtowerMeasurement n).onRight qubit`, its own branch
gate on every outcome. Outcome `0` is the identity; outcome `1` is the tail phase cascade, deferring
the tail measurement by `qtowerPhaseWireCascade_onRight_measure_postMeasurement` (the diagonal phase
gates commute with the computational-basis measurement). This is the engine's `hMp` premise for the
head wire's branches, with branch family
`W' i r = qtowerHeadPhaseBranch n gs i` (each defers to itself). -/
theorem qtowerHeadPhaseBranch_onRight_measure_postMeasurement (n : ℕ) (gs : List (Fin (n + 1) × ℝ))
    (i : Fin 2) (σ : State (qubit ⊗ qtower n qubit)) (r : Fin (n + 1) → Fin 2)
    (hq : ((qtowerMeasurement n).onRight qubit).bornProb σ r ≠ 0)
    (hq' : ((qtowerMeasurement n).onRight qubit).bornProb ((qtowerHeadPhaseBranch n gs i).evolve
    σ) r
      ≠ 0) :
    ((qtowerMeasurement n).onRight qubit).postMeasurement ((qtowerHeadPhaseBranch n gs i).evolve
    σ) r
        hq'
      = (qtowerHeadPhaseBranch n gs i).evolve
          (((qtowerMeasurement n).onRight qubit).postMeasurement σ r hq) := by
  fin_cases i
  · -- outcome `0`: the branch is the identity, deferring past any measurement trivially
    change ((qtowerMeasurement n).onRight qubit).postMeasurement (Evolution.id.evolve σ) r hq'
        = Evolution.id.evolve (((qtowerMeasurement n).onRight qubit).postMeasurement σ r hq)
    rw [Evolution.evolve_id (((qtowerMeasurement n).onRight qubit).postMeasurement σ r hq)]
    exact Measurement.postMeasurement_congr_state _ (Evolution.evolve_id σ) hq' hq
  · -- outcome `1`: the tail phase cascade, deferring past the tail measurement (3b-v-e)
    change ((qtowerMeasurement n).onRight qubit).postMeasurement
          (((qtowerPhaseWireCascade n gs).onRight qubit).evolve σ) r hq'
        = ((qtowerPhaseWireCascade n gs).onRight qubit).evolve
            (((qtowerMeasurement n).onRight qubit).postMeasurement σ r hq)
    exact qtowerPhaseWireCascade_onRight_measure_postMeasurement n gs σ r hq

/-- The head control wire's whole controlled-`Rₖ` phase cascade `qtowerHeadPhaseCascade n gs` defers
past the head-wire measurement `controlMeasurement (qtower n qubit)` to the clean
classically-controlled branch `qtowerHeadPhaseBranch n gs i`: the head reading
(`qtowerHeadCtrlCascade_measure_head_postMeasurement`) restated in the branch-cascade vocabulary via
`qtowerHeadPhaseBranch_eq`. This is the engine's `hLp` premise for the head wire. -/
theorem qtowerHeadPhaseCascade_measure_head_postMeasurement (n : ℕ) (gs : List (Fin (n + 1) × ℝ))
    (ρ : State (qtower (n + 1) qubit)) (i : Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb ρ i ≠ 0)
    (hp' : (controlMeasurement (qtower n qubit)).bornProb
      ((qtowerHeadPhaseCascade n gs).evolve ρ) i ≠ 0) :
    (controlMeasurement (qtower n qubit)).postMeasurement ((qtowerHeadPhaseCascade n gs).evolve ρ) i
        hp'
      = (qtowerHeadPhaseBranch n gs i).evolve
          ((controlMeasurement (qtower n qubit)).postMeasurement ρ i hp) := by
  rw [← qtowerHeadPhaseBranch_eq]
  exact qtowerHeadCtrlCascade_measure_head_postMeasurement n _ ρ i hp

/-- **Problem 5.2 (the head control wire's whole cascade is invisible to the terminal statistics).**
Measuring *every* wire of the tower (`qtowerMeasurement (n+1)`) after the head control wire's entire
controlled-`Rₖ` phase cascade `qtowerHeadPhaseCascade n gs` gives, for every outcome bit-string `r`,
the same Born probability as measuring the input `ρ` directly: the whole head cascade is
invisible to
the terminal per-wire statistics. Assembled from the head-wire reading and the tail
readings through the reading-level cascade-deferral engine,
transferred
across the `Fin.consEquiv` relabelling of `qtowerMeasurement_succ`. -/
theorem qtowerHeadPhaseCascade_measure_bornProb (n : ℕ) (gs : List (Fin (n + 1) × ℝ))
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2) :
    (qtowerMeasurement (n + 1)).bornProb ((qtowerHeadPhaseCascade n gs).evolve ρ) r
      = (qtowerMeasurement (n + 1)).bornProb ρ r := by
  rw [qtowerHeadPhaseCascade, qtowerMeasurement_succ]
  refine Measurement.bornProb_evolve_reindexOutcome_of_defers _ _ _ (fun σ p =>
    Measurement.bornProb_evolve_cascade_of_defers _ _ _ (qtowerHeadPhaseBranch n gs)
      (qtowerHeadCtrlCascade_measure_head_bornProb n _)
      (qtowerHeadPhaseCascade_measure_head_postMeasurement n gs)
      (qtowerHeadPhaseBranch_onRight_measure_bornProb n gs) σ p) ρ r

/-- **Problem 5.2 (the terminal measurement defers the head control wire's whole cascade).** The
state
after applying the head control wire's entire controlled-`Rₖ` phase cascade
`qtowerHeadPhaseCascade n
gs` and *then* measuring every wire equals the classically-controlled single-wire phase cascade
`qtowerHeadPhaseBranch n gs (r 0)` — control the tail phase rotations on the measured head bit `r
0`,
idle on the head wire — applied to the state obtained by measuring first:

  `postMeas(V ρ V†, r) = qtowerHeadPhaseBranch n gs (r 0) · postMeas(ρ, r)`,   `V =
  qtowerHeadPhaseCascade n gs`.

The measured head cascade of two-wire controlled gates has become a classically-controlled
*one-wire*
gate under the whole terminal measurement. Assembled from the head-wire reading
and the
tail readings through the reading-level cascade-deferral engine,
transferred across the `Fin.consEquiv` relabelling of `qtowerMeasurement_succ` (the head bit of the
relabelled outcome `r` is `r 0`). -/
theorem qtowerHeadPhaseCascade_measure_postMeasurement (n : ℕ) (gs : List (Fin (n + 1) × ℝ))
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2)
    (hp : (qtowerMeasurement (n + 1)).bornProb ρ r ≠ 0) :
    (qtowerMeasurement (n + 1)).postMeasurement ((qtowerHeadPhaseCascade n gs).evolve ρ) r
        (by rw [qtowerHeadPhaseCascade_measure_bornProb]; exact hp)
      = (qtowerHeadPhaseBranch n gs (r 0)).evolve
          ((qtowerMeasurement (n + 1)).postMeasurement ρ r hp) := by
  refine Measurement.postMeasurement_evolve_reindexOutcome_of_defers
    ((controlMeasurement (qtower n qubit)).cascade ((qtowerMeasurement n).onRight qubit))
    (Fin.consEquiv fun _ : Fin (n + 2) => Fin 2).symm
    (qtowerHeadPhaseCascade n gs) (fun p => qtowerHeadPhaseBranch n gs p.1) ?_ ρ r hp _
  exact fun σ p h _ => Measurement.postMeasurement_evolve_cascade_of_defers _ _ _
    (qtowerHeadPhaseBranch n gs) (fun i _ => qtowerHeadPhaseBranch n gs i)
    (qtowerHeadCtrlCascade_measure_head_bornProb n _)
    (qtowerHeadPhaseCascade_measure_head_postMeasurement n gs)
    (qtowerHeadPhaseBranch_onRight_measure_bornProb n gs)
    (fun i σ' s hs hs' => qtowerHeadPhaseBranch_onRight_measure_postMeasurement n gs i σ' s hs hs')
    σ p h

end MeasuredHeadPhaseCascade

/-! ### The QFT's Figure 5.1 head layer under the terminal measurement

The measured-QFT outer induction processes the Figure 5.1 head-layer peel
`qftTowerEvolution (n+1) = Φ · qftTailEvolution n · qftHeadLayer n` one control wire at a time,
under the terminal per-wire measurement `qtowerMeasurement (n+1)`. The head layer `qftHeadLayer n`
carries the only *two-wire* gates of that step — the head control wire's controlled-`Rₖ` phase
cascade. This section discharges the head wire's reduction: under the terminal measurement the head
layer is equivalent to a **single-wire** head Hadamard `Evolution.qtowerSingleWire (n+1) 0
hadamardGate` followed by a **classically-controlled** single-wire phase cascade
`qtowerHeadPhaseBranch n (qftHeadRotationList n) (r 0)`, no gate touching two wires — Problem 5.2
for one control wire's Figure 5.1 layer, and the reduction the outer induction plugs in at each
level.
-/

section MeasuredHeadLayer

/-- **The QFT head layer is its controlled-`Rₖ` phase cascade after the head Hadamard.** The head
layer `qftHeadLayer n` factors as the phase-specialised head control cascade
`qtowerHeadPhaseCascade n (qftHeadRotationList n)` composed after the head-wire Hadamard
`Evolution.qtowerSingleWire (n+1) 0 hadamardGate`: both cascades are the product of the Figure 5.1
head-controlled gates `Evolution.qtowerCtrlWire (n+1) 0 t.succ (phaseShiftGate φ)` over
`qftHeadRotationList n` (`List.map_map` collapses the phase-pairing map into the cascade's gate
map). This identifies the head layer's two-wire part with the cascade the head-cascade terminal
deferral (`qtowerHeadPhaseCascade_measure_*`) reduces to classical control. -/
theorem qftHeadLayer_eq_qtowerHeadPhaseCascade_mul (n : ℕ) :
    qftHeadLayer n
      = qtowerHeadPhaseCascade n (qftHeadRotationList n)
          * Evolution.qtowerSingleWire (n + 1) 0 hadamardGate := by
  rw [qftHeadLayer, qtowerHeadPhaseCascade, qtowerHeadCtrlCascade, List.map_map]
  rfl

/-- **Problem 5.2 (the head layer is invisible to the terminal statistics beyond its Hadamard).**
Measuring every wire (`qtowerMeasurement (n+1)`) after the QFT's Figure 5.1 head layer
`qftHeadLayer n` gives, for every outcome bit-string `r`, the same Born probability as measuring
after only the head-wire Hadamard `Evolution.qtowerSingleWire (n+1) 0 hadamardGate`: the head
control wire's whole controlled-`Rₖ` phase cascade is invisible to the terminal per-wire statistics.
The head layer factors as that cascade after the Hadamard
(`qftHeadLayer_eq_qtowerHeadPhaseCascade_mul`), and the cascade defers past the whole terminal
measurement (`qtowerHeadPhaseCascade_measure_bornProb`). -/
theorem qftHeadLayer_measure_bornProb (n : ℕ) (ρ : State (qtower (n + 1) qubit))
    (r : Fin (n + 2) → Fin 2) :
    (qtowerMeasurement (n + 1)).bornProb ((qftHeadLayer n).evolve ρ) r
      = (qtowerMeasurement (n + 1)).bornProb
          ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) r := by
  rw [qftHeadLayer_eq_qtowerHeadPhaseCascade_mul, Evolution.mul_def, Evolution.evolve_comp]
  exact qtowerHeadPhaseCascade_measure_bornProb n (qftHeadRotationList n) _ r

/-- **Problem 5.2 (the terminal measurement turns the head layer into a single-wire Hadamard plus a
classically-controlled phase cascade — no two-wire gate).** The state after the QFT's Figure 5.1
head layer `qftHeadLayer n` and *then* measuring every wire, at outcome `r`, equals the
classically-controlled single-wire phase cascade `qtowerHeadPhaseBranch n (qftHeadRotationList n)
(r 0)` — control the tail phase rotations on the measured head bit `r 0`, idle on the head wire —
applied to the state obtained by applying only the head-wire Hadamard
`Evolution.qtowerSingleWire (n+1) 0 hadamardGate` and then measuring:

  `postMeas(qftHeadLayer n · ρ, r)
     = qtowerHeadPhaseBranch n (qftHeadRotationList n) (r 0) · postMeas(H₀ · ρ, r)`.

The head layer's only two-wire gates (the controlled-`Rₖ` cascade) have become a single-wire phase
cascade with classical control on the measured head bit; what remains before the measurement is the
lone single-wire head Hadamard. This is Problem 5.2 for one control wire's Figure 5.1 layer, the
reduction the measured-QFT outer induction applies at each level. The head layer factors as the
cascade after the Hadamard (`qftHeadLayer_eq_qtowerHeadPhaseCascade_mul`), the input state is
carried across by `Measurement.postMeasurement_congr_state`, and the cascade defers past the whole
terminal measurement to `qtowerHeadPhaseBranch`
(`qtowerHeadPhaseCascade_measure_postMeasurement`). -/
theorem qftHeadLayer_measure_postMeasurement (n : ℕ) (ρ : State (qtower (n + 1) qubit))
    (r : Fin (n + 2) → Fin 2)
    (hp : (qtowerMeasurement (n + 1)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) r ≠ 0) :
    (qtowerMeasurement (n + 1)).postMeasurement ((qftHeadLayer n).evolve ρ) r
        (by rw [qftHeadLayer_measure_bornProb]; exact hp)
      = (qtowerHeadPhaseBranch n (qftHeadRotationList n) (r 0)).evolve
          ((qtowerMeasurement (n + 1)).postMeasurement
            ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) r hp) := by
  have hstate : (qftHeadLayer n).evolve ρ
      = (qtowerHeadPhaseCascade n (qftHeadRotationList n)).evolve
          ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) := by
    rw [qftHeadLayer_eq_qtowerHeadPhaseCascade_mul, Evolution.mul_def, Evolution.evolve_comp]
  refine (Measurement.postMeasurement_congr_state (qtowerMeasurement (n + 1)) hstate _
    (by rw [qtowerHeadPhaseCascade_measure_bornProb]; exact hp)).trans ?_
  exact qtowerHeadPhaseCascade_measure_postMeasurement n (qftHeadRotationList n) _ r hp

end MeasuredHeadLayer

/-! ### The swap-free circuit's head wire peels to the head Hadamard

The measured-QFT outer induction, having removed the Figure 5.1 swap layer as a classical
relabelling (`qftTowerEvolution_succ_measure_swapDefer_*`), is left measuring the
**swap-free** circuit `qftTailEvolution n · qftHeadLayer n` — apply the head layer, then the
recursive tail QFT. The terminal per-wire measurement is a cascade of its **head** factor
`controlMeasurement (qtower n qubit)` (measure wire `0`) and the recursive tail
(`qtowerMeasurement_succ`); the induction processes the head wire first.

This section peels that head wire: under the head-wire measurement, the swap-free circuit reduces to
the lone single-wire head Hadamard `Evolution.qtowerSingleWire (n+1) 0 hadamardGate`, with the head
control wire's controlled-`Rₖ` phase cascade deferred to the **classically-controlled** single-wire
branch `qtowerHeadPhaseBranch n (qftHeadRotationList n) i` on the measured head bit `i`, and the
recursive tail QFT `qftTailEvolution n` carried along — both idle on the head wire, **no two-wire
gate touching it**. It composes the two head-wire deferrals already in hand: the tail QFT slips past
the head-wire measurement (`qftTailEvolution_measure_head_*`) and the head control
cascade defers past it to `qtowerHeadPhaseBranch` (via
`qtowerHeadPhaseCascade_measure_head_postMeasurement`), the lone head Hadamard left before the
measurement. This is the **inner step of the terminal cascade unfold**: measuring the head wire of
the swap-free circuit exposes exactly this collapsed state, on whose disentangled tail factor the
recursion connector (`Measurement.*_onRight_evolve_tmul`) plugs the level-`n` measured
QFT.
-/

section SwapFreeHeadPeel

/-- **Problem 5.2 (the swap-free circuit is invisible to the head-wire statistics beyond its
Hadamard).** Measuring the head wire (`controlMeasurement (qtower n qubit)`) after the swap-free
circuit `qftTailEvolution n · qftHeadLayer n` gives, for every outcome `i`, the same Born
probability as measuring after only the head-wire Hadamard
`Evolution.qtowerSingleWire (n+1) 0 hadamardGate`: neither the recursive tail QFT nor the head
control wire's controlled-`Rₖ` phase cascade is visible to the head-wire statistics. The tail QFT
slips past the head measurement (`qftTailEvolution_measure_head_bornProb`); the head
layer factors as its phase cascade after the Hadamard
(`qftHeadLayer_eq_qtowerHeadPhaseCascade_mul`), and that cascade is invisible to the head wire
(`qtowerHeadCtrlCascade_measure_head_bornProb`). -/
theorem qftTailEvolution_qftHeadLayer_measure_head_bornProb (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (i : Fin 2) :
    (controlMeasurement (qtower n qubit)).bornProb
        ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) i
      = (controlMeasurement (qtower n qubit)).bornProb
          ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) i := by
  refine (qftTailEvolution_measure_head_bornProb ((qftHeadLayer n).evolve ρ) i).trans ?_
  rw [qftHeadLayer_eq_qtowerHeadPhaseCascade_mul, Evolution.mul_def, Evolution.evolve_comp,
    qtowerHeadPhaseCascade]
  exact qtowerHeadCtrlCascade_measure_head_bornProb n _ _ i

/-- **Problem 5.2 (the head-wire measurement peels the swap-free circuit to a Hadamard plus a
classically-controlled branch — no two-wire gate on the head wire).** The state after the swap-free
circuit `qftTailEvolution n · qftHeadLayer n` and *then* measuring the head wire, at outcome `i`,
equals the recursive tail QFT `qftTailEvolution n` composed with the classically-controlled
single-wire phase branch `qtowerHeadPhaseBranch n (qftHeadRotationList n) i` — control the tail
phase rotations on the measured head bit `i`, idle on the head wire — applied to the state obtained
by applying only the head-wire Hadamard `Evolution.qtowerSingleWire (n+1) 0 hadamardGate` and then
measuring the head wire:

  `postMeas(qftTailEvolution n · qftHeadLayer n · ρ, i)
     = qftTailEvolution n · qtowerHeadPhaseBranch n (qftHeadRotationList n) i
         · postMeas(H₀ · ρ, i)`.

Both surviving gates — the tail QFT and the classically-controlled phase branch — act on the tail
wires alone, leaving the head wire untouched: after the head wire is measured, the head control
wire's whole controlled-`Rₖ` block has become a single-wire phase cascade with classical control.
This is the inner step of the terminal cascade unfold, exposing the collapsed state whose
disentangled tail factor carries the level-`n` measured QFT. Proved by deferring the tail QFT past
the head measurement (`qftTailEvolution_measure_head_postMeasurement`), factoring the
head layer as its phase cascade after the Hadamard (`qftHeadLayer_eq_qtowerHeadPhaseCascade_mul`),
and deferring that cascade to `qtowerHeadPhaseBranch` (via
`qtowerHeadPhaseCascade_measure_head_postMeasurement`); the measured state is carried across the
head-layer factorisation by `Measurement.postMeasurement_congr_state`. -/
theorem qftTailEvolution_qftHeadLayer_measure_head_postMeasurement (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (i : Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) i ≠ 0) :
    (controlMeasurement (qtower n qubit)).postMeasurement
        ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) i
        (by rw [qftTailEvolution_qftHeadLayer_measure_head_bornProb]; exact hp)
      = (qftTailEvolution n).evolve
          ((qtowerHeadPhaseBranch n (qftHeadRotationList n) i).evolve
            ((controlMeasurement (qtower n qubit)).postMeasurement
              ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) i hp)) := by
  have hstate : (qftHeadLayer n).evolve ρ
      = (qtowerHeadPhaseCascade n (qftHeadRotationList n)).evolve
          ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) := by
    rw [qftHeadLayer_eq_qtowerHeadPhaseCascade_mul, Evolution.mul_def, Evolution.evolve_comp]
  have hpHL : (controlMeasurement (qtower n qubit)).bornProb ((qftHeadLayer n).evolve ρ) i ≠ 0 := by
    rw [hstate, qtowerHeadPhaseCascade, qtowerHeadCtrlCascade_measure_head_bornProb]; exact hp
  have hpHL' : (controlMeasurement (qtower n qubit)).bornProb
      ((qtowerHeadPhaseCascade n (qftHeadRotationList n)).evolve
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)) i ≠ 0 := by
    rw [← hstate]; exact hpHL
  refine (qftTailEvolution_measure_head_postMeasurement ((qftHeadLayer n).evolve ρ) i hpHL).trans ?_
  congr 1
  refine (Measurement.postMeasurement_congr_state (controlMeasurement (qtower n qubit))
    hstate hpHL hpHL').trans ?_
  exact qtowerHeadPhaseCascade_measure_head_postMeasurement n (qftHeadRotationList n) _ i hp hpHL'

end SwapFreeHeadPeel

/-! ### The measured swap-free circuit's head wire disentangles into a QFT-prepared product

The outer induction, after peeling the head wire of the swap-free circuit
`qftTailEvolution n · qftHeadLayer n`, is left with the head control wire's
controlled-`Rₖ` block deferred to a **classically-controlled** single-wire phase cascade and the
recursive tail QFT carried along — both idle on the measured head wire. This section resolves the
collapsed state into the **product form** the tail recursion consumes: the head-wire measurement
disentangles the register (`controlMeasurement_postMeasurement_eq_tmul`), and pushing
the two head-idle right-factor gates through that product
(`Evolution.onRight_evolve_tmul`) leaves the head wire in the measured basis state `|i⟩` tensored
with the level-`n` QFT applied to the classically-controlled phase-cascade-processed conditional
tail.

The tail-factor gate — the classically-controlled phase cascade the deferred head control wire
leaves on the tail wires — is named `qftTailBranch n i`: the restriction of the full-tower branch
`qtowerHeadPhaseBranch n (qftHeadRotationList n) i` to the `n`-tower once the idle head wire is
stripped. The disentangling theorem then exposes the tail factor as
`(qftTowerEvolution n).evolve ((qftTailBranch n i).evolve τ)` — the level-`n` transported QFT
applied to that classically-controlled tail input — the exact form on which the next inductive step
measures the remaining wires and recurses into the level-`n` measured QFT.
-/

section SwapFreeHeadTmul

/-- The **classically-controlled tail phase cascade** the deferred head control wire leaves on the
tail wires for measured head bit `i`: nothing (`Evolution.id`) on outcome `0`, and the tail phase
cascade `qtowerPhaseWireCascade n (qftHeadRotationList n)` on outcome `1`. It is the tail-factor of
the full-tower branch `qtowerHeadPhaseBranch n (qftHeadRotationList n) i` — that branch with the
(idle) head wire `0` stripped — a single-wire phase cascade with classical control on the measured
head bit, no gate touching the head wire. This is the classically-controlled input the outer
induction feeds to the level-`n` QFT on the disentangled tail. -/
def qftTailBranch (n : ℕ) (i : Fin 2) : Evolution (qtower n qubit) :=
  ![Evolution.id, qtowerPhaseWireCascade n (qftHeadRotationList n)] i

/-- The full-tower deferred branch `qtowerHeadPhaseBranch n (qftHeadRotationList n) i` is the tail
branch `qftTailBranch n i` placed on the tail wires, idle on the head wire `0`:
`qtowerHeadPhaseBranch n (qftHeadRotationList n) i = (qftTailBranch n i).onRight qubit`. Immediate
from `classicalControl U = ![Evolution.id, U.onRight qubit]` and `Evolution.id_onRight`
(`1.onRight qubit = 1`), matching `qftTailBranch`'s two branches. -/
theorem qtowerHeadPhaseBranch_qftHeadRotationList_eq_onRight (n : ℕ) (i : Fin 2) :
    qtowerHeadPhaseBranch n (qftHeadRotationList n) i = (qftTailBranch n i).onRight qubit := by
  fin_cases i <;> simp [qtowerHeadPhaseBranch, qftTailBranch, Evolution.id_onRight] <;> rfl

/-- **Problem 5.2 (the swap-free circuit's head-wire measurement disentangles into a QFT-prepared
product).** Measuring the head wire (`controlMeasurement (qtower n qubit)`, the head factor of the
terminal measurement) after the swap-free circuit `qftTailEvolution n · qftHeadLayer n` collapses
the register, at outcome `i`, to the **product state**

  `postMeas(swap-free · ρ, i) = |i⟩ ⊗ (qftTowerEvolution n · (qftTailBranch n i · τ))`,
  `τ = postMeas(H₀ · ρ, i).reducedRight`,

the head wire left in the measured basis state `|i⟩`, disentangled from the tail, and the tail wires
carrying the level-`n` transported quantum Fourier transform `qftTowerEvolution n` applied to the
classically-controlled phase cascade `qftTailBranch n i` acting on the conditional tail `τ` (the
reduced state of the head-Hadamard-measured input `H₀ · ρ`,
`H₀ = Evolution.qtowerSingleWire (n+1) 0 hadamardGate`). No gate touches the measured head wire: the
head control wire's whole controlled-`Rₖ` block has become the single-wire classically-controlled
phase cascade `qftTailBranch n i`, fed into the recursive tail QFT.

This is the state form the measured-QFT outer induction feeds to the tail recursion: measuring the
remaining wires of this product (via the recursion connector) reads only the right
factor, which is exactly the level-`n` measured QFT of `qftTailBranch n i · τ`. Proved by peeling
the head wire (`qftTailEvolution_qftHeadLayer_measure_head_postMeasurement`),
disentangling the head-Hadamard-measured collapsed state into a product
(`controlMeasurement_postMeasurement_eq_tmul`), and pushing the branch and the recursive tail QFT —
both head-idle right-factor gates (`qtowerHeadPhaseBranch_qftHeadRotationList_eq_onRight`,
`qftTailEvolution`) — through the product factorwise
(`Evolution.onRight_onRight_evolve_tmul`). -/
theorem qftTailEvolution_qftHeadLayer_measure_head_eq_tmul (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (i : Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) i ≠ 0) :
    (controlMeasurement (qtower n qubit)).postMeasurement
        ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) i
        (by rw [qftTailEvolution_qftHeadLayer_measure_head_bornProb]; exact hp)
      = (qubitBasis i).toState.tmul
          ((qftTowerEvolution n).evolve
            ((qftTailBranch n i).evolve
              (((controlMeasurement (qtower n qubit)).postMeasurement
                  ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) i
                  hp).reducedRight))) := by
  have key := qftTailEvolution_qftHeadLayer_measure_head_postMeasurement n ρ i hp
  rw [controlMeasurement_postMeasurement_eq_tmul
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) i hp,
      qtowerHeadPhaseBranch_qftHeadRotationList_eq_onRight] at key
  rw [key, qftTailEvolution]
  exact Evolution.onRight_onRight_evolve_tmul (qubitBasis i).toState (qftTowerEvolution n)
    (qftTailBranch n i) _

end SwapFreeHeadTmul

/-! ### The measured swap-free circuit's full-wire measurement factors through the level-`n`
measured QFT

Chunk 3b-v-t collapsed the head wire of the swap-free circuit `qftTailEvolution n · qftHeadLayer n`
into the product `|i⟩ ⊗ (qftTowerEvolution n · (qftTailBranch n i · τ))`. This section lifts that
head peel to the **whole terminal per-wire measurement** `qtowerMeasurement (n+1)`, whose head
factor is exactly the head-wire `controlMeasurement` collapsed above
(`qtowerMeasurement_succ`). Measuring every wire therefore splits — by the cascade
chain rule (N&C Ex. 2.57,
`cascade_bornProb` / `cascade_postMeasurement`) — into the head bit `r 0` and the recursive tail
measurement `(qtowerMeasurement n).onRight qubit` of the collapsed state; on the disentangled
product that tail measurement reads only the right factor
(`Measurement.{bornProb,postMeasurement}_onRight_tmul`), which carries the **level-`n` measured
QFT**
`qtowerMeasurement n` after `qftTowerEvolution n`, applied to the classically-controlled tail branch
`qftTailBranch n (r 0) · τ`.

So the level-`(n+1)` measured swap-free circuit is the head-Hadamard head-wire measurement followed
by the level-`n` measured QFT of a classically-controlled *single-wire* input — the recursion the
outer tower induction closes over. The head wire is left in the measured basis state `|r 0⟩`,
disentangled from the tail: no gate touches two wires. -/

section SwapFreeFullMeasure

/-- **Head/tail chain rule for the terminal per-wire measurement (outcome statistics).** Whenever
the head bit `r 0` is possible, the Born probability of the full outcome `r` under
`qtowerMeasurement (n+1)` factors as the head-wire probability times the conditional tail
probability, `p(r) = p_head(r 0) · p_tail(r∘succ ∣ head-collapse at r 0)`. The terminal measurement
is the head-wire `controlMeasurement` cascaded with the recursive tail
`(qtowerMeasurement n).onRight qubit`, relabelled by `Fin.consEquiv` (`qtowerMeasurement_succ`); the
relabelling strips via `reindexOutcome_bornProb` (taking `r` to `(r 0, r∘succ)`)
and the
cascade chain rule `cascade_bornProb` (N&C Ex. 2.57) factors the joint probability. -/
private theorem qtowerMeasurement_succ_bornProb (n : ℕ) (ρ : State (qtower (n + 1) qubit))
    (r : Fin (n + 2) → Fin 2)
    (hl : (controlMeasurement (qtower n qubit)).bornProb ρ (r 0) ≠ 0) :
    (qtowerMeasurement (n + 1)).bornProb ρ r
      = (controlMeasurement (qtower n qubit)).bornProb ρ (r 0)
        * ((qtowerMeasurement n).onRight qubit).bornProb
            ((controlMeasurement (qtower n qubit)).postMeasurement ρ (r 0) hl)
            (fun i => r i.succ) := by
  -- `qtowerMeasurement (n+1)` unfolds definitionally to the reindexed cascade
  -- (`qtowerMeasurement_succ`). Apply the reindex reader as a *term* (unification resolves the
  -- concrete measurement, unlike `rw`'s syntactic matcher), then make the `Fin.consEquiv` outcome
  -- split `e r = (r 0, r∘succ)` — a `rfl` pair equality — syntactic so the cascade chain rule
  -- applies without the outcome defeq blowing the `whnf` budget.
  have hpair : (Fin.consEquiv fun _ : Fin (n + 2) => Fin 2).symm r = (r 0, fun i => r i.succ) := rfl
  rw [qtowerMeasurement_succ]
  refine (Measurement.reindexOutcome_bornProb _ _ ρ r).trans ?_
  rw [hpair]
  exact cascade_bornProb (controlMeasurement (qtower n qubit))
    ((qtowerMeasurement n).onRight qubit) ρ (r 0) (fun i => r i.succ) hl

/-- **Head/tail chain rule for the terminal per-wire measurement (post-measurement state).** The
state after `qtowerMeasurement (n+1)` collapses at outcome `r` equals the sequential collapse: first
the head wire (`controlMeasurement (qtower n qubit)`) at `r 0`, then the recursive tail
`(qtowerMeasurement n).onRight qubit` at `r∘succ`. The head peel `qtowerMeasurement_succ`, stripped
of its `Fin.consEquiv` relabelling by `reindexOutcome_postMeasurement`, then the
cascade chain rule `cascade_postMeasurement` (N&C Ex. 2.57). Composed in term mode, so the
definitional identity `qtowerMeasurement_succ` and the dependent possibility proof stay aligned by
defeq without a `rewrite`-motive obstruction. -/
private theorem qtowerMeasurement_succ_postMeasurement (n : ℕ) (ρ : State (qtower (n + 1) qubit))
    (r : Fin (n + 2) → Fin 2)
    (hl : (controlMeasurement (qtower n qubit)).bornProb ρ (r 0) ≠ 0)
    (hm : ((qtowerMeasurement n).onRight qubit).bornProb
        ((controlMeasurement (qtower n qubit)).postMeasurement ρ (r 0) hl) (fun i => r i.succ) ≠ 0)
    (hpr : (qtowerMeasurement (n + 1)).bornProb ρ r ≠ 0) :
    (qtowerMeasurement (n + 1)).postMeasurement ρ r hpr
      = ((qtowerMeasurement n).onRight qubit).postMeasurement
          ((controlMeasurement (qtower n qubit)).postMeasurement ρ (r 0) hl) (fun i => r i.succ)
          hm := by
  -- `qtowerMeasurement (n+1)` unfolds definitionally to the reindexed cascade
  -- (`qtowerMeasurement_succ`). Revert the possibility proof so the measurement is rewritten
  -- uniformly (hypothesis type + goal together, motive stays well-formed); apply the reindex reader
  -- as a *term* (unification resolves the concrete measurement), make the `Fin.consEquiv` outcome
  -- split `e r = (r 0, r∘succ)` syntactic (a `rfl` pair equality, via `simp only` so it rewrites
  -- under the dependent possibility proof), then the cascade chain rule.
  have hpair : (Fin.consEquiv fun _ : Fin (n + 2) => Fin 2).symm r = (r 0, fun i => r i.succ) := rfl
  revert hpr
  rw [qtowerMeasurement_succ]
  intro hpr
  refine (Measurement.reindexOutcome_postMeasurement _ _ ρ r hpr).trans ?_
  simp only [hpair]
  exact cascade_postMeasurement (controlMeasurement (qtower n qubit))
    ((qtowerMeasurement n).onRight qubit) ρ (r 0) (fun i => r i.succ) hl hm

/-- **Problem 5.2 (the measured swap-free circuit's statistics factor through the level-`n` measured
QFT).** Measuring every wire (`qtowerMeasurement (n+1)`) after the swap-free circuit
`qftTailEvolution n · qftHeadLayer n` gives, for every outcome `r` whose head bit `r 0` is possible
after the head Hadamard, the product of the head-Hadamard head-wire probability and the level-`n`
measured-QFT probability of the classically-controlled tail branch:

  `p(r ∣ swap-free · ρ)
     = p(r 0 ∣ H₀ · ρ) · p(r∘succ ∣ qftTowerEvolution n · (qftTailBranch n (r 0) · τ))`,

`H₀ = Evolution.qtowerSingleWire (n+1) 0 hadamardGate`, `τ = postMeas(H₀ · ρ, r 0).reducedRight`.
The head/tail chain rule (`qtowerMeasurement_succ_bornProb`) splits the terminal measurement; the
head factor is invisible to the tail QFT and the head cascade beyond the Hadamard
(`qftTailEvolution_qftHeadLayer_measure_head_bornProb`); the head-collapsed state is the
disentangled product of `qftTailEvolution_qftHeadLayer_measure_head_eq_tmul`, on which the tail
measurement reads only the right factor (`Measurement.bornProb_onRight_tmul`) — the level-`n`
measured QFT of `qftTailBranch n (r 0) · τ`. -/
theorem qftTailEvolution_qftHeadLayer_measure_bornProb (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) (r 0) ≠ 0) :
    (qtowerMeasurement (n + 1)).bornProb
        ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) r
      = (controlMeasurement (qtower n qubit)).bornProb
          ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) (r 0)
        * (qtowerMeasurement n).bornProb
            ((qftTowerEvolution n).evolve
              ((qftTailBranch n (r 0)).evolve
                (((controlMeasurement (qtower n qubit)).postMeasurement
                    ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) (r 0) hp
                  ).reducedRight)))
            (fun i => r i.succ) := by
  have hl : (controlMeasurement (qtower n qubit)).bornProb
      ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) (r 0) ≠ 0 := by
    rw [qftTailEvolution_qftHeadLayer_measure_head_bornProb]; exact hp
  rw [qtowerMeasurement_succ_bornProb n _ r hl]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact qftTailEvolution_qftHeadLayer_measure_head_bornProb n ρ (r 0)
  · rw [qftTailEvolution_qftHeadLayer_measure_head_eq_tmul n ρ (r 0) hp,
      Measurement.bornProb_onRight_tmul]

/-- **Problem 5.2 (the measured swap-free circuit's head-wire collapse disentangles into a
QFT-prepared product).** The state after the swap-free circuit `qftTailEvolution n · qftHeadLayer n`
and *then* the whole terminal per-wire measurement `qtowerMeasurement (n+1)`, at outcome `r`, is the
**product state**

  `postMeas(swap-free · ρ, r)
     = |r 0⟩ ⊗ postMeas(qftTowerEvolution n · (qftTailBranch n (r 0) · τ), r∘succ)`,
  `τ = postMeas(H₀ · ρ, r 0).reducedRight`,

`H₀ = Evolution.qtowerSingleWire (n+1) 0 hadamardGate`: the head wire is left in the measured basis
state `|r 0⟩`, disentangled from the tail, and the tail wires carry the **level-`n` measured QFT**
(`qtowerMeasurement n` after `qftTowerEvolution n`) of the classically-controlled single-wire phase
branch `qftTailBranch n (r 0)` acting on the conditional tail `τ`. No gate touches the measured head
wire: the head control wire's whole controlled-`Rₖ` block has become the single-wire
classically-controlled cascade `qftTailBranch n (r 0)`, fed into the recursive measured QFT — the
recursion the outer tower induction closes over.

Proved by the head/tail chain rule for the terminal measurement
(`qtowerMeasurement_succ_postMeasurement`), the head-wire disentangling product
(`qftTailEvolution_qftHeadLayer_measure_head_eq_tmul`), and the tail measurement reading only the
right factor of that product (`Measurement.postMeasurement_onRight_tmul`); the tail
possibility is supplied by the statistics factorisation
(`qftTailEvolution_qftHeadLayer_measure_bornProb`). -/
theorem qftTailEvolution_qftHeadLayer_measure_eq_tmul (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) (r 0) ≠ 0)
    (hpr : (qtowerMeasurement (n + 1)).bornProb
        ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) r ≠ 0) :
    (qtowerMeasurement (n + 1)).postMeasurement
        ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) r hpr
      = (qubitBasis (r 0)).toState.tmul
          ((qtowerMeasurement n).postMeasurement
            ((qftTowerEvolution n).evolve
              ((qftTailBranch n (r 0)).evolve
                (((controlMeasurement (qtower n qubit)).postMeasurement
                    ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ) (r 0) hp
                  ).reducedRight)))
            (fun i => r i.succ)
            (right_ne_zero_of_mul
              (qftTailEvolution_qftHeadLayer_measure_bornProb n ρ r hp ▸ hpr))) := by
  have hl : (controlMeasurement (qtower n qubit)).bornProb
      ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) (r 0) ≠ 0 := by
    rw [qftTailEvolution_qftHeadLayer_measure_head_bornProb]; exact hp
  have hm : ((qtowerMeasurement n).onRight qubit).bornProb
      ((controlMeasurement (qtower n qubit)).postMeasurement
        ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) (r 0) hl) (fun i => r i.succ)
      ≠ 0 :=
    right_ne_zero_of_mul (qtowerMeasurement_succ_bornProb n _ r hl ▸ hpr)
  rw [qtowerMeasurement_succ_postMeasurement n _ r hl hm]
  refine (Measurement.postMeasurement_congr_state ((qtowerMeasurement n).onRight qubit)
    (qftTailEvolution_qftHeadLayer_measure_head_eq_tmul n ρ (r 0) hp) hm ?_).trans ?_
  · rw [← qftTailEvolution_qftHeadLayer_measure_head_eq_tmul n ρ (r 0) hp]; exact hm
  · rw [Measurement.postMeasurement_onRight_tmul]

end SwapFreeFullMeasure

/-! ### The measured QFT factors through the level-`n` measured QFT

Chunk 3b-v-u resolved the measured **swap-free** circuit `qftTailEvolution n · qftHeadLayer n`: its
full-wire measurement `qtowerMeasurement (n+1)` factors as the head-Hadamard head-wire measurement
followed by the **level-`n` measured QFT** of a classically-controlled single-wire input. This
section folds the Figure 5.1 **swap layer** `Φ = Evolution.qtowerPermWires (finRotate (n+2)).symm`
back in to reach the **actual** transported quantum Fourier transform `qftTowerEvolution (n+1)`,
which factors as `Φ · qftTailEvolution n · qftHeadLayer n` (the head-layer peel
`qftTowerEvolution_succ_eq_qftHeadLayer_peel`). The swap layer is a wire permutation,
which defers past the terminal measurement as a pure classical relabelling of the recorded bits
`r ↦ r ∘ σ`, `σ = (finRotate (n+2)).symm`
(`qftTowerEvolution_succ_measure_swapDefer_{bornProb,postMeasurement}`) — no two-wire gate.

Composing the two gives the measured QFT's **inductive step**: measuring every wire after
`qftTowerEvolution (n+1)` on `ρ` factors, at outcome `r`, into

  * the head-Hadamard head-wire measurement at the swap-relabelled head bit `r (σ 0)`, and
  * the **level-`n` measured QFT** `qtowerMeasurement n` after `qftTowerEvolution n`, applied to the
    classically-controlled single-wire phase branch `qftTailBranch n (r (σ 0))` on the conditional
    tail `τ = postMeas(H₀ · ρ, r (σ 0)).reducedRight`, read at the relabelled tail outcome
    `r ∘ σ ∘ succ`,

with a final `Φ` relabelling absorbed into the collapsed product. This expresses
`qtowerMeasurement (n+1) ∘ qftTowerEvolution (n+1)` in terms of
`qtowerMeasurement n ∘ qftTowerEvolution n` — the self-similar form the outer tower induction closes
over. Every operation separating the two levels — the head Hadamard `H₀`, the head-wire measurement,
the classically-controlled cascade `qftTailBranch n (r (σ 0))`, and the swap relabelling `Φ` — is a
single-wire gate, a measurement, classical control, or a relabelling: no gate touches two wires.
-/

section MeasuredQftOuterRecursion

/-- **Problem 5.2 (the measured QFT's statistics factor through the level-`n` measured QFT).**
Measuring every wire (`qtowerMeasurement (n+1)`) after the transported quantum Fourier transform
`qftTowerEvolution (n+1)` gives, for every outcome `r` whose swap-relabelled head bit `r (σ 0)`
(`σ = (finRotate (n+2)).symm`, the Figure 5.1 output reversal) is possible after the head Hadamard,
the product of the head-Hadamard head-wire probability and the **level-`n` measured-QFT**
probability of the classically-controlled tail branch:

  `p(r ∣ qftTowerEvolution (n+1) · ρ) = p(r (σ 0) ∣ H₀ · ρ)
     · p(r ∘ σ ∘ succ ∣ level-n measured QFT of qftTailBranch n (r (σ 0)) · τ)`,

`H₀ = Evolution.qtowerSingleWire (n+1) 0 hadamardGate`,
`τ = postMeas(H₀ · ρ, r (σ 0)).reducedRight`.
The Figure 5.1 swap layer defers past the terminal measurement as the classical relabelling
`r ↦ r ∘ σ` (`qftTowerEvolution_succ_measure_swapDefer_bornProb`), reducing the full QFT to the
swap-free circuit `qftTailEvolution n · qftHeadLayer n` on the relabelled outcome; the swap-free
circuit's statistics then factor through the level-`n` measured QFT
(`qftTailEvolution_qftHeadLayer_measure_bornProb`). This is the inductive step of the outer tower
induction at the level of the outcome statistics. -/
theorem qftTowerEvolution_measure_bornProb (n : ℕ) (ρ : State (qtower (n + 1) qubit))
    (r : Fin (n + 2) → Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
        (r ((finRotate (n + 2)).symm 0)) ≠ 0) :
    (qtowerMeasurement (n + 1)).bornProb ((qftTowerEvolution (n + 1)).evolve ρ) r
      = (controlMeasurement (qtower n qubit)).bornProb
          ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
          (r ((finRotate (n + 2)).symm 0))
        * (qtowerMeasurement n).bornProb
            ((qftTowerEvolution n).evolve
              ((qftTailBranch n (r ((finRotate (n + 2)).symm 0))).evolve
                (((controlMeasurement (qtower n qubit)).postMeasurement
                    ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
                    (r ((finRotate (n + 2)).symm 0)) hp).reducedRight)))
            (fun i => r ((finRotate (n + 2)).symm i.succ)) := by
  rw [qftTowerEvolution_succ_measure_swapDefer_bornProb]
  exact qftTailEvolution_qftHeadLayer_measure_bornProb n ρ
    (fun j => r ((finRotate (n + 2)).symm j)) hp

/-- **Problem 5.2 (the measured QFT's collapsed state factors through the level-`n` measured QFT).**
The state after the transported quantum Fourier transform `qftTowerEvolution (n+1)` and *then* the
whole terminal per-wire measurement `qtowerMeasurement (n+1)`, at outcome `r`, is the swap layer `Φ`
applied to the **product state**

  `postMeas(qftTowerEvolution (n+1) · ρ, r)
     = Φ · (|r (σ 0)⟩
       ⊗ postMeas(qftTowerEvolution n · (qftTailBranch n (r (σ 0)) · τ), r ∘ σ ∘ succ))`,

`Φ = Evolution.qtowerPermWires (finRotate (n+2)).symm`, `σ = (finRotate (n+2)).symm`,
`H₀ = Evolution.qtowerSingleWire (n+1) 0 hadamardGate`,
`τ = postMeas(H₀ · ρ, r (σ 0)).reducedRight`:
the swap-relabelled head wire left in the measured basis state `|r (σ 0)⟩`, disentangled from the
tail, and the tail wires carrying the **level-`n` measured QFT** (`qtowerMeasurement n` after
`qftTowerEvolution n`) of the classically-controlled single-wire phase branch
`qftTailBranch n (r (σ 0))` acting on the conditional tail `τ`, with a final wire relabelling `Φ`
(the Figure 5.1 swaps become a classical relabelling of the recorded bits). No gate touches two
wires: the head control wire's whole controlled-`Rₖ` block has become the single-wire
classically-controlled cascade `qftTailBranch n (r (σ 0))`, fed into the recursive measured QFT —
the recursion the outer tower induction closes over.

Proved by deferring the swap layer past the terminal measurement
(`qftTowerEvolution_succ_measure_swapDefer_postMeasurement`) and then factoring the swap-free
circuit's collapsed state through the level-`n` measured QFT
(`qftTailEvolution_qftHeadLayer_measure_eq_tmul`); the swap-free possibility is supplied by the
swap-defer statistics (`qftTowerEvolution_succ_measure_swapDefer_bornProb`). -/
theorem qftTowerEvolution_measure_postMeasurement (n : ℕ) (ρ : State (qtower (n + 1) qubit))
    (r : Fin (n + 2) → Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
        (r ((finRotate (n + 2)).symm 0)) ≠ 0)
    (hpr : (qtowerMeasurement (n + 1)).bornProb ((qftTowerEvolution (n + 1)).evolve ρ) r ≠ 0) :
    (qtowerMeasurement (n + 1)).postMeasurement ((qftTowerEvolution (n + 1)).evolve ρ) r hpr
      = (Evolution.qtowerPermWires (finRotate (n + 2)).symm).evolve
          ((qubitBasis (r ((finRotate (n + 2)).symm 0))).toState.tmul
            ((qtowerMeasurement n).postMeasurement
              ((qftTowerEvolution n).evolve
                ((qftTailBranch n (r ((finRotate (n + 2)).symm 0))).evolve
                  (((controlMeasurement (qtower n qubit)).postMeasurement
                      ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
                      (r ((finRotate (n + 2)).symm 0)) hp).reducedRight)))
              (fun i => r ((finRotate (n + 2)).symm i.succ))
              (right_ne_zero_of_mul (qftTowerEvolution_measure_bornProb n ρ r hp ▸ hpr)))) := by
  have hp' : (qtowerMeasurement (n + 1)).bornProb
      ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ))
      (fun j => r ((finRotate (n + 2)).symm j)) ≠ 0 :=
    qftTowerEvolution_succ_measure_swapDefer_bornProb ρ r ▸ hpr
  exact (qftTowerEvolution_succ_measure_swapDefer_postMeasurement ρ r hp').trans
    (congrArg (Evolution.qtowerPermWires (finRotate (n + 2)).symm).evolve
      (qftTailEvolution_qftHeadLayer_measure_eq_tmul n ρ
        (fun j => r ((finRotate (n + 2)).symm j)) hp hp'))

end MeasuredQftOuterRecursion

/-! ### The measured QFT collapses to the recorded computational-basis state

The outcome **statistics** of the measured QFT match the semiclassical circuit
(`semiclassicalMeasuredQft_bornProb_eq`, below). The other half of "equivalent as a measurement"
(Postulate 4) is the **collapsed state**: what state the register is left in for a given outcome.
Here the measured QFT's side of that is settled in closed form — measuring every wire of the tower
in the computational basis after the transported quantum Fourier transform collapses the register to
the **recorded basis state** `towerKet n r`, independent of the input `ρ`:

  `postMeas(qtowerMeasurement n · (qftTowerEvolution n · ρ), r) = (towerKet n r).toState`.

This is immediate from the general collapse of the joint computational-basis wire measurement
(`qtowerMeasurement_postMeasurement_eq_towerKet`, `Core/QtowerMeasurement.lean`): a joint
computational-basis measurement is rank-one projective, so it leaves every wire definite and forgets
the input entirely — no property of the QFT is needed beyond that its output is fed to that
measurement. It is the QFT-side half of the collapse-level equivalence; the semiclassical circuit's
collapsed state (which agrees with this up to the classical wire relabelling the swap network
became, `semiclassicalMeasuredQftOutcomeEquiv`) is developed separately over the post-measurement
recursion.
-/

section MeasuredQftCollapse

/-- **Problem 5.2 (the measured QFT collapses to the recorded computational-basis state).** The
state after the transported quantum Fourier transform `qftTowerEvolution n` and *then* the terminal
per-wire computational-basis measurement `qtowerMeasurement n`, at outcome `r`, is exactly the
computational-basis tower state `towerKet n r` — **independent of the input** `ρ`:

  `postMeas(qtowerMeasurement n · (qftTowerEvolution n · ρ), r) = (towerKet n r).toState`.

Measuring every wire in the computational basis is a rank-one projective measurement, so it fully
collapses the register onto the recorded bit-string and retains no memory of the pre-measurement
state. This is the measured QFT's half of the collapse-level (Postulate 4) content of Problem 5.2;
it holds for the QFT because the QFT output is simply fed to a computational-basis measurement — the
collapse fact `qtowerMeasurement_postMeasurement_eq_towerKet` is entirely about that measurement, so
the reduction is a direct instantiation with input `qftTowerEvolution n · ρ`. -/
theorem qftTowerEvolution_measure_postMeasurement_eq_towerKet (n : ℕ)
    (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2)
    (hp : (qtowerMeasurement n).bornProb ((qftTowerEvolution n).evolve ρ) r ≠ 0) :
    (qtowerMeasurement n).postMeasurement ((qftTowerEvolution n).evolve ρ) r hp
      = (towerKet n r).toState :=
  qtowerMeasurement_postMeasurement_eq_towerKet n _ r hp

end MeasuredQftCollapse

/-! ### The semiclassical realization of the measured QFT (outer tower induction)

The recursion step `qftTowerEvolution_measure_bornProb` expresses the measured QFT at
level `n+1` through the **level-`n`** measured QFT, with every operation separating the two
levels — a head-wire Hadamard `H₀`, the head-wire measurement, a classically-controlled
single-wire phase cascade `qftTailBranch`, and the Figure 5.1 swap layer (a wire permutation,
deferred past the
measurement as the classical outcome relabelling `σ = (finRotate (n+2)).symm`) — a single-wire gate,
a measurement, classical control, or a classical relabelling. This section **closes the induction**:
it packages that recursion into a single measurement object `semiclassicalMeasuredQft n` built
*only* from those constructors, and proves the measured QFT's outcome statistics equal it exactly.

`semiclassicalMeasuredQft n` is manifestly the circuit N&C Problem 5.2 asks for — a circuit of *one*
qubit gates and measurement with classical control, and **no two qubit gate**:

* the single-wire head Hadamard `Evolution.qtowerSingleWire (n+1) 0 hadamardGate`, applied first
  (`Measurement.precompose`);
* the head-wire computational-basis measurement `controlMeasurement (qtower n qubit)`;
* **classical control** (`Measurement.adaptiveCascade`): the measurement of the remaining wires is
  *chosen conditionally on the measured head bit* `i` — it applies the classically-controlled
  single-wire phase cascade `qftTailBranch n i` (`Measurement.precompose`, on the tail factor via
  `Measurement.onRight`) and then recurses into `semiclassicalMeasuredQft n`;
* a **classical relabelling** of the recorded bits (`Measurement.reindexOutcome`) absorbing the
  Figure 5.1 output swaps — no swap *gate* survives.

The Figure 5.1 swaps only permute *which measured wire carries which output bit*, so for the outcome
**statistics** they are exactly this relabelling; the semiclassical circuit is therefore swap-free
and reproduces the measured QFT's probabilities identically
(`semiclassicalMeasuredQft_bornProb_eq`). This is the faithful whole-circuit content of Problem 5.2:
the quantum Fourier transform followed by a computational-basis measurement is equivalent — same
outcome distribution — to a circuit built entirely of one-qubit gates and measurement with classical
control. (The collapsed *states* agree up to the same final classical wire relabelling: the measured
QFT collapses to the recorded basis state `towerKet n r`
(`qftTowerEvolution_measure_postMeasurement_eq_towerKet`, above), and the semiclassical circuit to
its bit-reversal `towerKet n (fun i => r i.rev)` — the Figure 5.1 swaps become a classical
relabelling
(`semiclassicalMeasuredQft_postMeasurement_eq_towerKet`, the section that follows).)
-/

section SemiclassicalRealization

/-- **The outcome relabelling of the semiclassical realization.** It reads a full outcome
bit-string `r : Fin (n+2) → Fin 2` as a head bit together with a tail bit-string, through the
Figure 5.1 output permutation `σ = (finRotate (n+2)).symm`:
`r ↦ ⟨r (σ 0), fun i ↦ r (σ i.succ)⟩`. This is exactly the head/tail split the measured-QFT
recursion step (`qftTowerEvolution_measure_bornProb`) records — the swap layer become a classical
relabelling — so reindexing the semiclassical measurement's `Fin 2 × (Fin (n+1) → Fin 2)` outcome
(head bit, tail bit-string) by it lines the object up with the measured QFT wire for wire. -/
def semiclassicalMeasuredQftOutcomeEquiv (n : ℕ) :
    (Fin (n + 2) → Fin 2) ≃ ((_ : Fin 2) × (Fin (n + 1) → Fin 2)) :=
  (Equiv.arrowCongr (finRotate (n + 2)) (Equiv.refl (Fin 2))).trans
    ((Fin.consEquiv (fun _ : Fin (n + 2) => Fin 2)).symm.trans
      (Equiv.sigmaEquivProd (Fin 2) (Fin (n + 1) → Fin 2)).symm)

/-- **The semiclassical realization of the measured quantum Fourier transform** (N&C Problem 5.2).
`semiclassicalMeasuredQft n : Measurement (Fin (n+1) → Fin 2) (qtower n qubit)` is the single
measurement object built *only* from one-qubit gates, computational-basis wire measurements, and
classical control — **no two-qubit gate** — whose outcome statistics equal those of the measured QFT
(`semiclassicalMeasuredQft_bornProb_eq`). It is defined by the outer tower recursion:

* at depth `0` the whole circuit is the single-wire Hadamard `qftTowerEvolution 0 = hadamardGate`
  followed by the measurement (`Measurement.precompose`);
* at depth `n+1` it applies the head-wire Hadamard `Evolution.qtowerSingleWire (n+1) 0 hadamardGate`
  (`Measurement.precompose`), measures the head wire (`controlMeasurement (qtower n qubit)`), and —
  **classically controlled** on the measured head bit `i` (`Measurement.adaptiveCascade`) — applies
  the single-wire phase cascade `qftTailBranch n i` to the remaining wires and recurses into
  `semiclassicalMeasuredQft n` (both on the tail factor, `Measurement.onRight`); the
  `Fin 2 × (Fin (n+1) → Fin 2)` (head bit, tail bit-string) outcome is relabelled to the full
  bit-string by `semiclassicalMeasuredQftOutcomeEquiv n`, absorbing the Figure 5.1 output swaps as a
  classical relabelling. -/
def semiclassicalMeasuredQft : (n : ℕ) → Measurement (Fin (n + 1) → Fin 2) (qtower n qubit)
  | 0 => (qtowerMeasurement 0).precompose hadamardGate
  | n + 1 =>
      (((controlMeasurement (qtower n qubit)).adaptiveCascade
          (fun i => ((semiclassicalMeasuredQft n).precompose (qftTailBranch n i)).onRight qubit)
        ).precompose (Evolution.qtowerSingleWire (n + 1) 0 hadamardGate)).reindexOutcome
          (semiclassicalMeasuredQftOutcomeEquiv n)

/-- **The joint terminal-measurement probability is bounded by its head-wire probability.** For
`qtowerMeasurement (n+1)`, `p(r) ≤ p_head(r 0)`: the terminal measurement is the head-wire
`controlMeasurement` cascaded with the recursive tail (`qtowerMeasurement_succ`), and a cascade
outcome never exceeds its first stage (`Measurement.cascade_bornProb_le_fst`). Used to force the
measured QFT's probability to `0` on outcomes whose head bit is impossible. -/
private theorem qtowerMeasurement_succ_bornProb_le_head (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2) :
    (qtowerMeasurement (n + 1)).bornProb ρ r
      ≤ (controlMeasurement (qtower n qubit)).bornProb ρ (r 0) := by
  rw [qtowerMeasurement_succ]
  refine (Measurement.reindexOutcome_bornProb _ _ ρ r).le.trans ?_
  exact Measurement.cascade_bornProb_le_fst (controlMeasurement (qtower n qubit))
    ((qtowerMeasurement n).onRight qubit) ρ (r 0) (fun i => r i.succ)

/-- **The semiclassical realization's outcome statistics unfold to its adaptive cascade.** Stripping
the outcome relabelling (`reindexOutcome_bornProb`, splitting `r` into the head bit `r (σ 0)` and
the tail bit-string `r ∘ σ ∘ succ` via `semiclassicalMeasuredQftOutcomeEquiv`) and the head-Hadamard
pre-composition (`precompose_bornProb`), `(semiclassicalMeasuredQft (n+1)).bornProb ρ r` equals the
Born probability of the adaptive cascade — head-wire measurement, then the classically-controlled
tail branch — on the head-Hadamard-evolved state. Isolates the object-side bookkeeping from the
outer induction. -/
private theorem semiclassicalMeasuredQft_succ_bornProb_eq_adaptiveCascade (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2) :
    (semiclassicalMeasuredQft (n + 1)).bornProb ρ r
      = ((controlMeasurement (qtower n qubit)).adaptiveCascade
          (fun i => ((semiclassicalMeasuredQft n).precompose (qftTailBranch n i)).onRight qubit)
        ).bornProb ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
          ⟨r ((finRotate (n + 2)).symm 0), fun i => r ((finRotate (n + 2)).symm i.succ)⟩ := by
  refine (Measurement.reindexOutcome_bornProb _
    (semiclassicalMeasuredQftOutcomeEquiv n) ρ r).trans ?_
  exact Measurement.precompose_bornProb _ _ ρ _

/-- **The semiclassical realization's outcome statistics factor through the level-`n` circuit.**
Whenever the swap-relabelled head bit `r (σ 0)` is achievable after the head Hadamard, the
semiclassical circuit's probability factors as the head-Hadamard head-wire probability times the
level-`n` semiclassical circuit's probability of the classically-controlled tail branch
`qftTailBranch n (r (σ 0))` on the head-collapsed conditional tail — the same head/tail form the
measured QFT's recursion step (`qftTowerEvolution_measure_bornProb`) produces, with
`semiclassicalMeasuredQft n` in place of the level-`n` measured QFT. Combines the adaptive-cascade
chain rule (`adaptiveCascade_bornProb`), the head-collapse product
(`controlMeasurement_postMeasurement_eq_tmul`), the tail measurement reading only the right factor
(`bornProb_onRight_tmul`), and the tail-gate pre-composition (`precompose_bornProb`). -/
private theorem semiclassicalMeasuredQft_succ_bornProb (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
        (r ((finRotate (n + 2)).symm 0)) ≠ 0) :
    (semiclassicalMeasuredQft (n + 1)).bornProb ρ r
      = (controlMeasurement (qtower n qubit)).bornProb
          ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
          (r ((finRotate (n + 2)).symm 0))
        * (semiclassicalMeasuredQft n).bornProb
            ((qftTailBranch n (r ((finRotate (n + 2)).symm 0))).evolve
              (((controlMeasurement (qtower n qubit)).postMeasurement
                  ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
                  (r ((finRotate (n + 2)).symm 0)) hp).reducedRight))
            (fun i => r ((finRotate (n + 2)).symm i.succ)) := by
  -- Abstract the conditional tail `τ` first, so rewriting the head collapse to the product
  -- `|i⟩ ⊗ τ` on the left factor does not disturb the `τ` on the right-hand side of the goal.
  set τ := ((controlMeasurement (qtower n qubit)).postMeasurement
      ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
      (r ((finRotate (n + 2)).symm 0)) hp).reducedRight with hτ
  rw [semiclassicalMeasuredQft_succ_bornProb_eq_adaptiveCascade,
    Measurement.adaptiveCascade_bornProb _ _ _ _ _ hp,
    controlMeasurement_postMeasurement_eq_tmul _ _ hp, ← hτ]
  simp only [Measurement.bornProb_onRight_tmul, Measurement.precompose_bornProb]

/-- **Problem 5.2 (the measured QFT's statistics are exactly those of the semiclassical circuit).**
The outcome statistics of the measured quantum Fourier transform — the QFT `qftTowerEvolution n`
followed by measuring every wire (`qtowerMeasurement n`) — equal, outcome for outcome and state for
state, those of the manifestly semiclassical circuit `semiclassicalMeasuredQft n`:

  `p(r ∣ qftTowerEvolution n · ρ) = p(r ∣ semiclassicalMeasuredQft n · ρ)`.

Since `semiclassicalMeasuredQft n` is built only from one-qubit gates, computational-basis wire
measurements, and classical control — with no two-qubit gate — this is the faithful whole-circuit
content of Problem 5.2: the QFT plus a computational-basis measurement is equivalent, as an outcome
distribution, to a circuit of one-qubit gates and measurement with classical control.

Proved by the **outer tower induction**. The base case (`qftTowerEvolution_zero`,
`precompose_bornProb`) is the single-wire Hadamard. The step cases on whether the head bit `r (σ 0)`
is achievable after the head Hadamard (`σ = (finRotate (n+2)).symm`, the swap relabelling):
* if impossible, both probabilities vanish — the measured QFT's by the head-marginal bound
  (`qftTowerEvolution_succ_measure_swapDefer_bornProb`, `qtowerMeasurement_succ_bornProb_le_head`,
  `qftTailEvolution_qftHeadLayer_measure_head_bornProb`), the semiclassical circuit's by the
  adaptive-cascade marginal bound (`adaptiveCascade_bornProb_le_fst`);
* if achievable, the recursion step `qftTowerEvolution_measure_bornProb` factors the measured QFT's
  probability as `p_head · (level-n measured QFT of the classically-controlled tail branch)`, the
  inductive hypothesis rewrites the tail to `semiclassicalMeasuredQft n`, and the semiclassical
  object's probability factors identically (`semiclassicalMeasuredQft_succ_bornProb`). -/
theorem semiclassicalMeasuredQft_bornProb_eq :
    ∀ (n : ℕ) (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2),
      (qtowerMeasurement n).bornProb ((qftTowerEvolution n).evolve ρ) r
        = (semiclassicalMeasuredQft n).bornProb ρ r := by
  intro n
  induction n with
  | zero =>
    intro ρ r
    rw [qftTowerEvolution_zero]
    exact (Measurement.precompose_bornProb (qtowerMeasurement 0) hadamardGate ρ r).symm
  | succ k ih =>
    intro ρ r
    by_cases hp : (controlMeasurement (qtower k qubit)).bornProb
        ((Evolution.qtowerSingleWire (k + 1) 0 hadamardGate).evolve ρ)
        (r ((finRotate (k + 2)).symm 0)) = 0
    · -- Impossible head bit: both probabilities vanish.
      have hLHS : (qtowerMeasurement (k + 1)).bornProb ((qftTowerEvolution (k + 1)).evolve ρ) r
          = 0 := by
        rw [qftTowerEvolution_succ_measure_swapDefer_bornProb]
        refine le_antisymm ((qtowerMeasurement_succ_bornProb_le_head k _ _).trans ?_)
          (Measurement.bornProb_nonneg _ _ _)
        rw [qftTailEvolution_qftHeadLayer_measure_head_bornProb]
        exact le_of_eq hp
      have hRHS : (semiclassicalMeasuredQft (k + 1)).bornProb ρ r = 0 := by
        rw [semiclassicalMeasuredQft_succ_bornProb_eq_adaptiveCascade]
        refine le_antisymm ((Measurement.adaptiveCascade_bornProb_le_fst _ _ _ _ _).trans ?_)
          (Measurement.bornProb_nonneg _ _ _)
        exact le_of_eq hp
      rw [hLHS, hRHS]
    · -- Achievable head bit: both probabilities factor identically through the level-`k` tail.
      rw [qftTowerEvolution_measure_bornProb k ρ r hp,
        ih _ (fun i => r ((finRotate (k + 2)).symm i.succ)),
        semiclassicalMeasuredQft_succ_bornProb k ρ r hp]

end SemiclassicalRealization

/-! ### The semiclassical circuit collapses to the recorded basis state (outer tower induction)

The outcome **statistics** of the semiclassical circuit `semiclassicalMeasuredQft n` match the
measured QFT exactly (`semiclassicalMeasuredQft_bornProb_eq`, above). This section settles the
semiclassical circuit's side of the collapse-level (Postulate 4) content: what state it leaves the
register in for a given outcome `r`.

Like the measured QFT (`qftTowerEvolution_measure_postMeasurement_eq_towerKet`, above), the
semiclassical circuit collapses to a **recorded computational-basis state, independent of the
input**
`ρ` — but to `towerKet n (fun i => r i.rev)`, the **bit-reversal** of the measured QFT's collapse
`towerKet n r`:

  `postMeas(semiclassicalMeasuredQft n · ρ, r) = (towerKet n (fun i => r i.rev)).toState`.

The reversal `Fin.rev` is precisely the Figure 5.1 **swap network become a classical wire
relabelling**: `qftTowerEvolution n` is the *symmetric* DFT with the output swaps built in, so its
measured wires already carry the output bits in place (collapse `towerKet n r`); the semiclassical
circuit is swap-free (it absorbs the swaps as the outcome relabelling
`semiclassicalMeasuredQftOutcomeEquiv` for the statistics, no swap *gate*), so its measured wires
carry the same bits in the **reversed** order. Every leaf of the recursion is a computational-basis
wire measurement, so the collapse forgets the input entirely; the reversal accumulates one cyclic
`σ = (finRotate (n+2)).symm` per recursion level (head bit `r (σ 0) = r (Fin.last (n+1))` peeled to
the front at each step) into the full `Fin.rev`.

Together with the QFT-side collapse and the statistics equivalence, this is the collapse-level half
of Problem 5.2: the QFT-plus-measurement and the semiclassical circuit collapse to the **same**
computational-basis recording up to the bit-reversal wire relabelling the Figure 5.1 swap network
became — no two-qubit gate anywhere in the semiclassical circuit.
-/

section SemiclassicalCollapse

/-- **The semiclassical realization's collapsed state unfolds to its adaptive cascade.**
Stripping the
outcome relabelling (`reindexOutcome_postMeasurement`, splitting `r` into the head bit `r (σ 0)` and
tail bit-string `r ∘ σ ∘ succ` via `semiclassicalMeasuredQftOutcomeEquiv`) and the head-Hadamard
pre-composition (`precompose_postMeasurement`), the collapsed state of
`semiclassicalMeasuredQft (n+1)`
at outcome `r` equals that of the adaptive cascade — head-wire measurement then the
classically-controlled tail branch — on the head-Hadamard-evolved state. The post-measurement mirror
of `semiclassicalMeasuredQft_succ_bornProb_eq_adaptiveCascade`; isolating it exposes the `Σ`-outcome
`⟨r (σ 0), r ∘ σ ∘ succ⟩` syntactically, so the adaptive-cascade peel
(`adaptiveCascade_postMeasurement`)
matches without unfolding the whole outcome equiv in `whnf`. -/
private theorem semiclassicalMeasuredQft_succ_postMeasurement_eq_adaptiveCascade (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2)
    (hpr : (semiclassicalMeasuredQft (n + 1)).bornProb ρ r ≠ 0)
    (hac : ((controlMeasurement (qtower n qubit)).adaptiveCascade
        (fun i =>
          ((semiclassicalMeasuredQft n).precompose (qftTailBranch n i)).onRight qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
        ⟨r ((finRotate (n + 2)).symm 0), fun i => r ((finRotate (n + 2)).symm i.succ)⟩ ≠ 0) :
    (semiclassicalMeasuredQft (n + 1)).postMeasurement ρ r hpr
      = ((controlMeasurement (qtower n qubit)).adaptiveCascade
          (fun i => ((semiclassicalMeasuredQft n).precompose (qftTailBranch n i)).onRight qubit)
        ).postMeasurement ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
          ⟨r ((finRotate (n + 2)).symm 0), fun i => r ((finRotate (n + 2)).symm i.succ)⟩ hac := by
  refine (Measurement.reindexOutcome_postMeasurement _ (semiclassicalMeasuredQftOutcomeEquiv n)
    ρ r hpr).trans ?_
  exact Measurement.precompose_postMeasurement _ _ ρ _ _

/-- **The semiclassical realization's collapsed state factors through the level-`n` circuit.** The
state after `semiclassicalMeasuredQft (n+1)` collapses at outcome `r` is the **product** of the
swap-relabelled head wire `|r (σ 0)⟩` (`σ = (finRotate (n+2)).symm`) with the collapse of the
**level-`n`** semiclassical circuit on the classically-controlled tail branch:

  `postMeas(semiclassicalMeasuredQft (n+1) · ρ, r)
     = |r (σ 0)⟩ ⊗ postMeas(semiclassicalMeasuredQft n · (qftTailBranch n (r (σ 0)) · τ),
       r∘σ∘succ)`,
  `τ = postMeas(H₀ · ρ, r (σ 0)).reducedRight`,
  `H₀ = Evolution.qtowerSingleWire (n+1) 0 hadamardGate`.

The measured head wire is left disentangled in the basis state `|r (σ 0)⟩`, and the tail wires carry
the level-`n` semiclassical circuit applied to the classically-controlled single-wire phase branch
`qftTailBranch n (r (σ 0))` on the conditional tail `τ` — no gate touches two wires. This is the
post-measurement mirror of `semiclassicalMeasuredQft_succ_bornProb` (the born-probability side), and
the object-side analogue of the measured QFT's recursion step
(`qftTowerEvolution_measure_postMeasurement`). Proved by peeling the definitional layers of the
object with their Postulate-4 laws: the outcome relabelling (`reindexOutcome_postMeasurement`, into
the head bit `r (σ 0)` and tail bit-string `r∘σ∘succ`), the head-Hadamard pre-composition
(`precompose_postMeasurement`), the adaptive-cascade chain (`adaptiveCascade_postMeasurement`), the
head-wire collapse to a product (`controlMeasurement_postMeasurement_eq_tmul`), the tail measurement
reading only the right factor (`postMeasurement_onRight_tmul`), and the tail-gate
pre-composition. -/
private theorem semiclassicalMeasuredQft_succ_postMeasurement_eq_tmul (n : ℕ)
    (ρ : State (qtower (n + 1) qubit)) (r : Fin (n + 2) → Fin 2)
    (hp : (controlMeasurement (qtower n qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
        (r ((finRotate (n + 2)).symm 0)) ≠ 0)
    (hpr : (semiclassicalMeasuredQft (n + 1)).bornProb ρ r ≠ 0)
    (htail : (semiclassicalMeasuredQft n).bornProb
        ((qftTailBranch n (r ((finRotate (n + 2)).symm 0))).evolve
          (((controlMeasurement (qtower n qubit)).postMeasurement
              ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
              (r ((finRotate (n + 2)).symm 0)) hp).reducedRight))
        (fun i => r ((finRotate (n + 2)).symm i.succ)) ≠ 0) :
    (semiclassicalMeasuredQft (n + 1)).postMeasurement ρ r hpr
      = (qubitBasis (r ((finRotate (n + 2)).symm 0))).toState.tmul
          ((semiclassicalMeasuredQft n).postMeasurement
            ((qftTailBranch n (r ((finRotate (n + 2)).symm 0))).evolve
              (((controlMeasurement (qtower n qubit)).postMeasurement
                  ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
                  (r ((finRotate (n + 2)).symm 0)) hp).reducedRight))
            (fun i => r ((finRotate (n + 2)).symm i.succ))
            htail) := by
  -- The joint probability after the outcome relabelling and head-Hadamard pre-composition — the
  -- head/tail-split born-probability of the adaptive cascade — is nonzero.
  have hpr' : ((controlMeasurement (qtower n qubit)).adaptiveCascade
        (fun i =>
          ((semiclassicalMeasuredQft n).precompose (qftTailBranch n i)).onRight qubit)).bornProb
        ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
        ⟨r ((finRotate (n + 2)).symm 0), fun i => r ((finRotate (n + 2)).symm i.succ)⟩ ≠ 0 :=
    semiclassicalMeasuredQft_succ_bornProb_eq_adaptiveCascade n ρ r ▸ hpr
  -- The tail (conditional) measurement is possible, by the adaptive-cascade chain rule.
  have hm : (((semiclassicalMeasuredQft n).precompose
        (qftTailBranch n (r ((finRotate (n + 2)).symm 0)))).onRight qubit).bornProb
        ((controlMeasurement (qtower n qubit)).postMeasurement
          ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
          (r ((finRotate (n + 2)).symm 0)) hp)
        (fun i => r ((finRotate (n + 2)).symm i.succ)) ≠ 0 := by
    have h := hpr'
    rw [Measurement.adaptiveCascade_bornProb _ _ _ _ _ hp] at h
    exact right_ne_zero_of_mul h
  -- Reduce to the adaptive cascade (syntactic `Σ`-outcome), then peel its Postulate-4 layers: the
  -- adaptive-cascade chain, the head-wire collapse to a product, and the right-factor tail
  -- collapse.
  rw [semiclassicalMeasuredQft_succ_postMeasurement_eq_adaptiveCascade n ρ r hpr hpr']
  refine (Measurement.adaptiveCascade_postMeasurement' (controlMeasurement (qtower n qubit))
    (fun i => ((semiclassicalMeasuredQft n).precompose (qftTailBranch n i)).onRight qubit)
    ((Evolution.qtowerSingleWire (n + 1) 0 hadamardGate).evolve ρ)
    (r ((finRotate (n + 2)).symm 0)) (fun i => r ((finRotate (n + 2)).symm i.succ)) hp hm
    hpr').trans ?_
  refine (Measurement.postMeasurement_congr_state _
    (controlMeasurement_postMeasurement_eq_tmul _ (r ((finRotate (n + 2)).symm 0)) hp) hm
      ?_).trans ?_
  · rw [← controlMeasurement_postMeasurement_eq_tmul _ (r ((finRotate (n + 2)).symm 0)) hp]
    exact hm
  refine (Measurement.postMeasurement_onRight_tmul _ _ _ _ _ _).trans ?_
  exact congrArg ((qubitBasis (r ((finRotate (n + 2)).symm 0))).toState.tmul)
    (Measurement.precompose_postMeasurement (semiclassicalMeasuredQft n)
      (qftTailBranch n (r ((finRotate (n + 2)).symm 0))) _ _ _)

/-- **Problem 5.2 (the semiclassical circuit collapses to the recorded basis state).** The state
after the manifestly semiclassical circuit `semiclassicalMeasuredQft n` — one-qubit gates,
computational-basis wire measurements, and classical control, with **no two-qubit gate** — collapses
at outcome `r` to the computational-basis tower state `towerKet n (fun i => r i.rev)`, **independent
of the input** `ρ`:

  `postMeas(semiclassicalMeasuredQft n · ρ, r) = (towerKet n (fun i => r i.rev)).toState`.

This is the **bit-reversal** `Fin.rev` of the measured QFT's collapse `towerKet n r`
(`qftTowerEvolution_measure_postMeasurement_eq_towerKet`) — exactly the Figure 5.1 swap network
become a classical wire relabelling: the swap-free semiclassical circuit records the output bits in
reversed wire order, differing from the symmetric-DFT measured QFT (whose swaps put the bits in
place) only by that relabelling. Every leaf of the circuit is a computational-basis wire
measurement, so the collapse forgets the input; the reversal is assembled from one cyclic
`σ = (finRotate (n+2)).symm` per level.

Proved by the **outer tower induction** mirroring the statistics equivalence: the base case is the
single-wire Hadamard (`semiclassicalMeasuredQft 0 = (qtowerMeasurement 0).precompose hadamardGate`;
`precompose_postMeasurement` then the general comp-basis collapse
`qtowerMeasurement_postMeasurement_eq_towerKet`); the step case factors the collapse into the head
wire `|r (σ 0)⟩` and the level-`n` circuit's collapse of the classically-controlled tail branch
(`semiclassicalMeasuredQft_succ_postMeasurement_eq_tmul`), rewrites the tail by the inductive
hypothesis, and reassembles the tower state (`towerKet_succ`, `PureState.toState_tmul`) — the head
peel `r (σ 0) → Fin.last (n+1)` and the tail shift `σ (i.rev.succ) = i.succ.rev` accumulating the
per-level cyclic `σ` into the full `Fin.rev`. -/
theorem semiclassicalMeasuredQft_postMeasurement_eq_towerKet :
    ∀ (n : ℕ) (ρ : State (qtower n qubit)) (r : Fin (n + 1) → Fin 2)
      (hpr : (semiclassicalMeasuredQft n).bornProb ρ r ≠ 0),
      (semiclassicalMeasuredQft n).postMeasurement ρ r hpr
        = (towerKet n (fun i => r i.rev)).toState := by
  intro n
  induction n with
  | zero =>
    intro ρ r hpr
    refine (Measurement.precompose_postMeasurement (qtowerMeasurement 0) hadamardGate ρ r
      hpr).trans ?_
    rw [qtowerMeasurement_postMeasurement_eq_towerKet]
    have hrev : (fun i : Fin 1 => r i.rev) = r := by
      funext i; rw [Subsingleton.elim i.rev i]
    rw [hrev]
  | succ k ih =>
    intro ρ r hpr
    -- A possible joint outcome forces the head bit (after the head Hadamard) to be possible.
    have hp : (controlMeasurement (qtower k qubit)).bornProb
        ((Evolution.qtowerSingleWire (k + 1) 0 hadamardGate).evolve ρ)
        (r ((finRotate (k + 2)).symm 0)) ≠ 0 :=
      Measurement.adaptiveCascade_bornProb_fst_ne_zero _ _ _ _ _
        (semiclassicalMeasuredQft_succ_bornProb_eq_adaptiveCascade k ρ r ▸ hpr)
    -- The full-outcome bit-reversal `fun i => r i.rev` is the head bit `r (σ 0)` peeled to the
    -- front
    -- (`σ 0 = Fin.last (k+1)`) with the tail bits reversed under the per-level shift
    -- (`σ (j.rev.succ) = j.succ.rev`), so the collapse tower state factors as a head ket ⊗ tail
    -- tower.
    have htk : towerKet (k + 1) (fun i => r i.rev)
        = (qubitBasis (r ((finRotate (k + 2)).symm 0))).tmul
            (towerKet k (fun i => r ((finRotate (k + 2)).symm i.rev.succ))) := by
      have harg : (fun i : Fin (k + 2) => r i.rev)
          = Fin.cons (r ((finRotate (k + 2)).symm 0))
              (fun j : Fin (k + 1) => r ((finRotate (k + 2)).symm (Fin.rev j).succ)) := by
        funext i
        induction i using Fin.cases with
        | zero =>
          have h0 : (finRotate (k + 2)).symm 0 = Fin.last (k + 1) := by
            rw [Equiv.symm_apply_eq, finRotate_last]
          rw [Fin.cons_zero, h0, Fin.rev_zero]
        | succ j =>
          have hB : (finRotate (k + 2)).symm (j.rev.succ) = j.succ.rev := by
            rw [Equiv.symm_apply_eq, finRotate_apply, Fin.rev_succ, Fin.coeSucc_eq_succ]
          rw [Fin.cons_succ, hB]
      rw [harg, towerKet_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rfl
    -- The tail (conditional) measurement is possible (the joint born-probability factors as
    -- head·tail).
    have htail := right_ne_zero_of_mul (semiclassicalMeasuredQft_succ_bornProb k ρ r hp ▸ hpr)
    rw [semiclassicalMeasuredQft_succ_postMeasurement_eq_tmul k ρ r hp hpr htail, ih _ _ _, htk]
    exact (PureState.toState_tmul _ _).symm

end SemiclassicalCollapse

/-! ### The semiclassical circuit contains no two-qubit gate

The equivalences above (`semiclassicalMeasuredQft_bornProb_eq`,
`semiclassicalMeasuredQft_postMeasurement_eq_towerKet`) match the measured QFT — statistics and
collapse — to the circuit `semiclassicalMeasuredQft n`. The following makes explicit the
**structural** half of Problem 5.2: that the matching circuit uses *no two-qubit gate*.
`semiclassicalMeasuredQft n` is built only from the single-wire head Hadamard
`Evolution.qtowerSingleWire (n+1) 0 hadamardGate`, computational-basis wire measurements, classical
control, and — inside each classically-controlled branch — the phase cascade `qftTailBranch n i`.
The head Hadamard is a single-wire gate by construction; the theorem below exhibits the remaining
branch gate as a composition of single-wire gates. Together they show every gate of the
semiclassical circuit acts on a single wire. -/

/-- **Problem 5.2 (no two-qubit gate).** Each classically-controlled branch `qftTailBranch n i` of
the semiclassical circuit `semiclassicalMeasuredQft` is a **composition of single-wire gates**:
there is a list `gs` of `(wire, gate)` pairs with

  `qftTailBranch n i = (gs.map fun p => Evolution.qtowerSingleWire n p.1 p.2).prod`,

each factor `Evolution.qtowerSingleWire n t g` acting on the single tail wire `t` alone. On outcome
`0` the branch is empty (`gs = []`, nothing applied); on outcome `1` it is the phase cascade
`qtowerPhaseWireCascade n (qftHeadRotationList n)`, whose factors are the single-wire phase gates
`Evolution.qtowerSingleWire n t (phaseShiftGate (2π·2^{t.rev}/2ⁿ⁺²))`. Since the only other gate of
the circuit is the single-wire head Hadamard `Evolution.qtowerSingleWire (n+1) 0 hadamardGate`, no
gate of `semiclassicalMeasuredQft n` touches two wires — the "no two qubit gates" conclusion of
Problem 5.2, made an explicit proposition. -/
theorem qftTailBranch_eq_qtowerSingleWire_prod (n : ℕ) (i : Fin 2) :
    ∃ gs : List (Fin (n + 1) × Evolution qubit),
      qftTailBranch n i = (gs.map fun p => Evolution.qtowerSingleWire n p.1 p.2).prod := by
  fin_cases i
  · exact ⟨[], rfl⟩
  · refine ⟨(qftHeadRotationList n).map fun p => (p.1, phaseShiftGate p.2), ?_⟩
    rw [List.map_map]
    rfl

end AxQM
