/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationDensity
import AxQM.Concrete.FourGateUniversality
import AxQM.Postulates.API.FourGateNamedTowerDensity
import AxQM.Postulates.API.FourGateMeasurementUniversal

/-!
# Nielsen & Chuang, Exercise 4.43 (universality of `H, S, CNOT, Toffoli`)

*(N&C p. 198.)*

Use prior results to show H, S, CNOT, Toffoli are universal for quantum computation.

The "previous two exercises" are:

* **Exercise 4.41** — the Figure 4.17 measurement-based circuit realises the `z`-rotation `R_z(θ)`
  with `cos θ = 3/5` (on the success branch) using only `H, S, CNOT, Toffoli`.
* **Exercise 4.42** — that `θ` is an *irrational* multiple of `2π`.

Chaining them gives universality: iterating the reachable gate `R_z(θ)` approximates every
`z`-rotation `R_z(α)` (because an irrational rotation orbit is dense); Hadamard conjugation turns
those into every `x`-rotation `R_x(α)`; and the Z–Y decomposition (Theorem 4.1) writes an arbitrary
single-qubit unitary as `e^{iα} R_z(β) R_y(γ) R_z(δ)`, so an arbitrary single-qubit gate is
approximable. Together with `CNOT` (universality of `CNOT` + arbitrary single-qubit gates, §4.5.2)
this makes the four-gate set universal.

## The statement and where it lives

The **headline** is `AxQM.Concrete.exists_phase_smul_mem_closure_reachableCircuits`
(`AxQM/Concrete/FourGateUniversality.lean`): for `cos θ = 3/5`, an encoding
`enc : (Fin m → Fin 2) ≃ Fin d` of an `m`-qubit register (`m ≥ 1`), and *any* `U ∈ U(d)`, some
global phase `e^{iα}` makes `e^{iα} • U` a limit of `reachableCircuits enc θ` — i.e. the circuits
built from `H, S, CNOT, Toffoli` are dense in `U(d)` up to an (unobservable) global phase. That is
Exercise 4.43's universality conclusion.

The four gates the exercise names are `Evolution`s in the library — `AxQM.hadamardGate`,
`AxQM.sGate` (the phase gate `S = diag(1, i)`), `AxQM.cnotGate` (`= controlledUnitary pauliXGate`)
and `AxQM.toffoliGate` (`= C²(X)`, with `toffoliFig49Circuit_eq_toffoliGate` the Figure 4.9
realisation) — together with the rotation gate `AxQM.rotZGate` and the `H, S, CNOT, Toffoli`
circuit `AxQM.rzThreeFifthsCircuit` realising `R_z(θ)` with `cos θ = 3/5` (Exercise 4.41). The
matrix generators of `reachableCircuits` are realised by those gates: the reversible
`IsToffoliPermGate` factors as `Toffoli`/`CNOT`/`NOT`, and the single-qubit wire gates as the
reachable rotations `R_z(±θ), R_x(±θ)` (`R_x` from `R_z` by Hadamard conjugation,
`H R_z(θ) H = R_x(θ)`; `R_z(θ)` by `rzThreeFifthsCircuit`).

**The four-gate statement.** Exercise 4.43's claim is that `H, S, CNOT, Toffoli` *with
measurement* are universal — the four *unitary* gates alone generate the discrete Clifford +
Toffoli group, and the irrational rotation `R_z(θ)` (`cos θ = 3/5`) is supplied by a *measurement*
of the four-gate circuit (Exercises 4.41/4.42). The statement is
`AxQM.hsCnotToffoli_measurement_universal`
(`AxQM/Postulates/API/FourGateMeasurementUniversal.lean`):
for any tower evolution `T`, some global phase `e^{iα}` makes `e^{iα} • T.op` a limit of the
operators of `fourGateMeasurementReachable n` — the circuits built from `H, S, CNOT, Toffoli`
**together with the measurement-realised rotation**. It combines the two results below.

* `exists_phase_smul_op_mem_closure_op_namedFourGateTowerGates`
  (`AxQM/Postulates/API/FourGateNamedTowerDensity.lean`) — the **density core**: with `R_z(θ)`
  *available* as a generator, the four-gate model `namedFourGateTowerGates n θ` is dense up to a
  global phase. On its own it carries `rotZGate θ` as a **free** generator.
* `rzThreeFifthsMeasurement_success_realizes_rotZ`
  (`AxQM/Postulates/API/FourGateNamedTowerDensity.lean`) — the **four-gate measurement
  realisation**: the Figure-4.17 circuit `rzThreeFifthsCircuit` (`H, S, Toffoli`) followed by the
  two-ancilla measurement `rzTwoAncillaMeasurement`, on the success outcome `(0, 0)` (probability
  `‖c‖² = 5/8`), applies `R_z(rzThreeFifthsAngle)` to the target.

**The combination (`AxQM/Postulates/API/FourGateMeasurementUniversal.lean`).** The predicate
`IsFourGateMeasurementRealised G` says the four-gate measurement gadget realises `G` (its first
conjunct is the circuit + measurement's success action — naming `rzThreeFifthsCircuit` and
`rzTwoAncillaMeasurement` — and its second pins `G = R_z(θ)` up to a global phase). The model
`fourGateMeasurementReachable n` is the density core's submonoid with the free `rotZGate θ`
generator **replaced** by the measurement-realised set `{G | IsFourGateMeasurementRealised G}`, so
no rotation is posited: every rotation in the model is present only because the four-gate gadget
realises it (`isFourGateMeasurementRealised_rotZGate_rzThreeFifthsAngle`). Density transfers from
the core by `closure_mono` along the containment
`namedFourGateTowerGates n rzThreeFifthsAngle ≤ fourGateMeasurementReachable n`. So `R_z(θ)` is
**derived** from `{H, S, CNOT, Toffoli}` + measurement, not assumed.

**Identifying the abstract gate set with the four gates.** The abstract density result is stated
over the gate set `reachableCircuits enc θ` for an abstract `θ` with `cos θ = 3/5`. Identifying its
generators with the four named gates and the Exercise 4.41 circuit `rzThreeFifthsCircuit` is done
in the following parts:

* `rotZ θ` at `θ := rzThreeFifthsAngle` via the measurement-success branch of
  `rzThreeFifthsCircuit` (`rzThreeFifthsCircuit_success_eq_rotZ`, Exercise 4.41);
* `rotX(±θ)`, `rotZ(-θ)` via Hadamard conjugation and the adjoint circuit;
* the `IsToffoliPermGate` factors via the `cnotGate` / `toffoliGate`.

**Single-qubit rotations.** `AxQM/Postulates/API/FourGateReachableRotation.lean` exhibits the
single-qubit
reachable rotations (the submonoid `Concrete.reachableRotations θ` whose members appear via
`singleQubitOnWire` among the `reachableGateSet` generators) as `H, S, CNOT, Toffoli` gates —
`sGate_comp_sGate` (`S² = Z`), `pauliXGate_eq_hadamardGate_sGateSq` (`NOT = H·S²·H`),
`rotZGate_neg_eq_hadamardGate_sGate_conj` (`R_z(-θ)` a `{H, S}` conjugate of `R_z(θ)`), the gate
submonoid `reachableRotationGates θ`, and the matrix-to-gate bridge
`exists_reachableRotationGate_op_eq`.

**Register lift of the single-qubit rotations**
(`AxQM/Postulates/API/FourGateReachableWire.lean` for the register side and
`AxQM/Core/FourGateReachableWireTower.lean` for the tower re-expression). The reachable
single-qubit rotations, placed on a *wire* of the `2ⁿ`-level register (the form
`singleQubitOnWire finFunctionFinEquiv t g` in which they appear among the `reachableGateSet`
generators), are re-expressed as the rotation gate on the corresponding tower wire, exactly
as `AxQM/Core/QftTowerHadamard.lean` does for the Figure 5.1 Hadamard. The wire gates
`rotZWireEvolution` / `rotXWireEvolution` (in `Evolution (qudit (2ⁿ))`)
place `R_z(θ)` / `R_x(θ)` on register wire `t`; the two theorems
`quditPowTower_congr_rotZWireEvolution` / `quditPowTower_congr_rotXWireEvolution` are the tower
re-expression: `Evolution.congr (quditPowTower n) (rotZWireEvolution (n+1) t θ) =
qtowerSingleWire n t.rev (rotZGate θ)` (resp. `rotXGate`). Each is proved **directly**,
with an inline tensor-multilinearity `have mult` and the two shared private ket-bookkeeping lemmas
`towerProd_update_qubitBasis` / `update_rev_eq`, exactly as `AxQM/Core/QftTowerHadamard.lean`
inlines its own `mult`. At `θ` and `-θ` these cover all four generators `R_z(±θ), R_x(±θ)` of
`Concrete.reachableRotations θ`, so every reachable single-qubit rotation generator on a register
wire is a rotation gate (built, with measurement, from `H, S, CNOT, Toffoli`) on a tower
wire.

**Register lift of the reversible gates**
(`AxQM/Postulates/API/FourGateReversibleWire.lean` for the register side and
`AxQM/Core/FourGateReversibleWireTower.lean` for the tower re-expression), the reversible
counterpart of the rotation register lift. The other `reachableGateSet` generator family is the
`≤ 2`-control reversible gates `IsToffoliPermGate finFunctionFinEquiv G` — the matrices
`permGate finFunctionFinEquiv (mcNotPerm S t)` with `|S| ≤ 2` (`Toffoli`/`CNOT`/`NOT`). The
register wire gate `mcNotWireEvolution n S t ht` (in `Evolution (qudit (2ⁿ))`) places that gate on
wires `(S, t)`; its basis action
`mcNotWireEvolution_evolvePure_quditBasis` is the classical `mcNot` on the bit-string (a basis
*permutation*). The target is `mcNotTowerGate n S t ht := Evolution.congr (qtowerQubitTensorPow
n).symm (placedMcNot S t
ht)` — the `Toffoli`/`CNOT`/`NOT` `Evolution.placedMcNot` (for `|S| ≤ 2`) transported from
the symmetric register `qubit ^⊗ₛ (n+1)` back onto the control tower `qtower n qubit`, so it lands
in the same system as the rotation half; its basis action `mcNotTowerGate_evolvePure_towerKet` is
`towerKet n b ↦ towerKet n (mcNot S t b)`. The headline `quditPowTower_congr_mcNotWireEvolution` is
the tower re-expression: `Evolution.congr (quditPowTower n) (mcNotWireEvolution (n+1) S t ht) =
mcNotTowerGate n (S.map Fin.revPerm.toEmbedding) t.rev _` (the reversed wire set; the `Fin.rev`
reconciling the big-endian register bridge with the little-endian wire-indexing, via the `mcNot`
relabelling naturality `Concrete.mcNot_map_equiv` at `σ = Fin.revPerm`). It is proved via the shared
combinator `quditPowTower_congr_eq_of_evolvePure_towerKet` with **no** tensor-multilinearity step
(the rotation half's inline `mult`), since a reversible gate is a basis permutation.

**The combined register circuit `Evolution` submonoid**
(`AxQM/Postulates/API/FourGateReachableCircuit.lean`). The two register generator families
are now collected into one submonoid of `Evolution (qudit (2ⁿ⁺¹))`, and the *whole* abstract
reachable circuit set is identified with it, one operator at a time:

* `reachableCircuitEvolutions n θ` — the submonoid generated by the whole per-wire
  reachable-rotation submonoids `reachableRotationWireEvolutions n j θ` (over every wire `j`)
  together with the `≤ 2`-control reversible register gates `mcNotWireEvolution (n+1) S t ht`
  (`|S| ≤ 2`) — the register-gate counterpart of the abstract matrix submonoid
  `Concrete.reachableCircuits`.
* `exists_reachableCircuitEvolution_op_eq` — **the matrix→submonoid bridge**: every matrix
  `M ∈ Concrete.reachableCircuits finFunctionFinEquiv θ` is the operator of some member `E` of
  `reachableCircuitEvolutions n θ` (`E.op = Matrix.toEuclideanCLM M`), by
  `Submonoid.closure_induction` — the reachable-rotation generators via the per-wire
  `exists_reachableRotationWireEvolution_op_eq`, the reversible generators via `quditGate_op` on
  `mcNotWireEvolution`, and `1`/products via the multiplicativity of `Evolution.op` and
  `Matrix.toEuclideanCLM`. The whole-circuit analogue of the single-family
  `exists_reachableRotationWireEvolution_op_eq`.

**The whole-submonoid register lift onto the control tower**
(`AxQM/Core/FourGateReachableCircuitTower.lean`). The two register generator families, each
already given a tower re-expression (rotations via
`exists_reachableRotationGate_congr_quditPowTower_eq`, reversible via
`quditPowTower_congr_mcNotWireEvolution`), are assembled into **one tower submonoid**,
and the *whole* register submonoid `reachableCircuitEvolutions n θ` is transported into it:

* `reachableTowerCircuitEvolutions n θ` — the tower circuit submonoid of
  `Evolution (qtower n qubit)` generated by the single-tower-wire reachable rotation gates
  `Evolution.qtowerSingleWire n i E` (`E ∈ reachableRotationGates θ`, every wire `i`) and the
  `≤ 2`-control reversible tower gates `mcNotTowerGate n S t ht` (`|S| ≤ 2`, `t ∉ S`).
  Every generator is a genuine `H, S, CNOT, Toffoli` circuit on a tower wire (rotations:
  `{H, S}`-conjugates of the Exercise 4.41 measurement circuit `rzThreeFifthsCircuit`; reversible:
  `placedMcNot = Toffoli/CNOT/NOT`) — the tower counterpart of the register submonoid
  `reachableCircuitEvolutions n θ`. This is where the four *named* gates enter.
* `congr_quditPowTower_mem_reachableTowerCircuitEvolutions` — **the whole-submonoid tower lift**:
  every `E ∈ reachableCircuitEvolutions n θ` has
  `Evolution.congr (quditPowTower n) E ∈ reachableTowerCircuitEvolutions n θ`, by
  `Submonoid.closure_induction` — the rotation generators via the whole-submonoid rotation lift
  (landing at wire `j.rev`), the reversible generators via `quditPowTower_congr_mcNotWireEvolution`
  (the reversed control set keeps `card ≤ 2` by `Finset.card_map` and misses the reversed target by
  `Finset.mem_map_equiv`), and `1`/products by the monoid-homomorphism laws of `Evolution.congr`
  (`Evolution.congr_id` / `Evolution.congr_comp`).

**The density transport onto the register operators**
(`AxQM/Postulates/API/FourGateReachableCircuitDensity.lean`). The matrix density is pushed
through the continuous `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` onto the register `Evolution`
operators (continuity being the general `ToMathlib/` lemma `Matrix.continuous_toEuclideanCLM`, a
`ℂ`-linear map between the finite-dimensional matrix and operator spaces via
`LinearMap.continuous_of_finiteDimensional`):

* `exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions` — **the operator-level density**:
  for `cos θ = 3/5` and any `U ∈ U(2ⁿ⁺¹)`, some global phase `e^{iα}` makes
  `e^{iα} • Matrix.toEuclideanCLM U` lie in the closure of the operator image
  `(·.op) '' reachableCircuitEvolutions n θ`. The matrix density
  `exists_phase_smul_mem_closure_reachableCircuits` supplies the phase; continuity carries the
  matrix closure into the operator closure (`image_closure_subset_closure_image`), `ℂ`-linearity
  commutes with the phase (`map_smul`), and the matrix→operator bridge
  `exists_reachableCircuitEvolution_op_eq` places the matrix image inside the operator image of the
  register submonoid (`closure_mono`).

**The density transport onto the control tower**
(`AxQM/Postulates/API/FourGateReachableTowerDensity.lean`). The register operator density is
transported onto the tower gate submonoid through the transport `⋆`-algebra isomorphism
`e.toIsometry.conjStarAlgEquiv` (`e := quditPowTower n`) — the conjugation `Evolution.congr e`
enacts on operators (`Evolution.congr_op`):

* `exists_unitaryGroup_toEuclideanCLM_eq_op` — every `Evolution (qudit d)` operator is
  `Matrix.toEuclideanCLM` of a unitary matrix (`U := Matrix.toEuclideanCLM.symm T.op`, unitary
  because the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` carries operator unitarity to matrix
  unitarity), so the matrix-indexed register density applies to an arbitrary register evolution
  (`exists_phase_smul_op_mem_closure_op_reachableCircuitEvolutions'`).
* `exists_phase_smul_op_mem_closure_op_reachableTowerCircuitEvolutions` — **the tower operator
  density**: for `cos θ = 3/5` and *any* tower evolution `T : Evolution (qtower n qubit)`, some
  global phase `e^{iα}` makes `e^{iα} • T.op ∈ closure ((·.op) '' reachableTowerCircuitEvolutions n
  θ)`. Pulling `T` back to the register (`Evolution.congr e.symm T`), the register density supplies
  `α`; the transport isomorphism `Φ := e.toIsometry.conjStarAlgEquiv` — continuous as a `ℂ`-linear
  map between the finite-dimensional operator spaces (`LinearMap.continuous_of_finiteDimensional`),
  so it carries closure into closure (`image_closure_subset_closure_image`) and commutes with the
  phase (`map_smul`) — lands `e^{iα} • T.op` (via `Φ (T'.op) = (Evolution.congr e T').op = T.op`)
  in the closure of the `Φ`-image of the register operator image, which the whole-submonoid tower
  lift `congr_quditPowTower_mem_reachableTowerCircuitEvolutions` (with `Evolution.congr_op`) places
  inside the tower operator image (`closure_mono`).

So density is stated over the *tower gate submonoid* `reachableTowerCircuitEvolutions
n θ`, whose generators are gates on individual tower wires (`Evolution.qtowerSingleWire n
i E` for reachable rotations, `mcNotTowerGate n S t ht` for the `≤ 2`-control reversible gates).

**The rotation family over the named gates `H, S`**
(`AxQM/Core/FourGateNamedRotationTower.lean`), at both the single qubit and the tower wire:

* `reachableRotationGates_le_closure_named` — `reachableRotationGates θ ≤
  Submonoid.closure {hadamardGate, sGate, rotZGate θ}`: every reachable single-qubit rotation
  generator `R_z(±θ), R_x(±θ)` is a finite `{H, S}` word around the single base rotation `R_z(θ)`
  (`R_z(-θ) = (H·S²·H)·R_z(θ)·(H·S²·H)`, `R_x(θ) = H·R_z(θ)·H`, `R_x(-θ) = H·R_z(-θ)·H`), so the
  only non-`{H, S}` ingredient is `R_z(θ)` — the measurement-realised gate (Exercise 4.41), whose
  reachability is the essential content the four *unitary* gates alone cannot supply.
* `namedRotationTowerGates n θ` / `qtowerSingleWire_mem_namedRotationTowerGates` — the tower
  counterpart: the rotation generators of `reachableTowerCircuitEvolutions n θ`, namely
  `Evolution.qtowerSingleWire n i E` for `E ∈ reachableRotationGates θ`, all lie in the submonoid
  generated by the single-tower-wire placements of `hadamardGate, sGate, rotZGate θ` (via the
  monoid-homomorphism laws of `Evolution.qtowerSingleWire`).


**The reversible generator cores over the named gates `CNOT, Toffoli`**
(`AxQM/Core/FourGateNamedReversibleTower.lean`). Each reversible generator
`mcNotTowerGate n S t ht` (`|S| ≤ 2`) is the `placedMcNot S t ht` gate transported onto the tower,
and `placedMcNot` places the arity-indexed multiply-controlled `NOT` block
`Evolution.placedMcCtrlX (S.card) …` — whose core, before any wire placement or register transport,
is `mcCtrl (S.card) pauliXGate`. For the reachable range `|S| ≤ 2` that core **is** one of the three
named reversible gates:

* `mcCtrl_one_pauliXGate_eq_cnotGate` / `mcCtrl_two_pauliXGate_eq_toffoliGate` — the **root
  identifications** `mcCtrl 1 pauliXGate = cnotGate`, `mcCtrl 2 pauliXGate = toffoliGate` (with
  `mcCtrl 0 pauliXGate = pauliXGate = NOT`, the base case `mcCtrl_zero`), from the `mcCtrl`
  recursion `mcCtrl (k+1) E = controlledUnitary (mcCtrl k E)` and the named-gate definitions
  `cnotGate = controlledUnitary pauliXGate`,
  `toffoliGate = controlledUnitary (controlledUnitary pauliXGate)`.
* `tensorPowMcCtrlX_{zero,one,two}_eq_congr_{pauliXGate,cnotGate,toffoliGate}` — the symmetric-power
  `Cᵏ(X)` block is the named gate transported along the tower ↔ tensor-power bridge, and
  `placedMcCtrlX_{zero,one,two}_eq_onWires_{…}` — the **wire-placed** form `placedMcNot` actually
  uses, `Evolution.placedMcCtrlX k b σ = (Evolution.congr (qtowerQubitTensorPow k) g).onWires b σ`
  with `g` the named gate, for `k = 0, 1, 2`.

So every reversible generator of `reachableTowerCircuitEvolutions n θ` (`|S| ≤ 2`) has as its placed
core exactly one of `pauliXGate` (the `NOT`, itself `H·S²·H`), `cnotGate`, `toffoliGate`,
mirroring the rotation half's `hadamardGate`, `sGate`.

**The named four-gate tower submonoid, its density, and the four-gate measurement realisation of
`R_z(θ)`** (`AxQM/Core/FourGateNamedTower.lean` for the assembly and
`AxQM/Postulates/API/FourGateNamedTowerDensity.lean` for the density and the realisation). The
reversible cores and the rotation containment are threaded through `placedMcNot` /
`mcNotTowerGate` onto a single named four-gate tower submonoid, the tower operator density is
transferred onto it, and the base rotation is realised by the four-gate measurement circuit:

* `namedMcNotGate k` / `namedFourGateTowerGates n θ` — the **named four-gate tower submonoid** of
  `Evolution (qtower n qubit)`, generated by the single-tower-wire placements of the three named
  gates `{hadamardGate, sGate, rotZGate θ}` and by the named reversible gates `namedMcNotGate k`
  (`k ≤ 2` — `NOT = H·S²·H`, `cnotGate`, `toffoliGate`) placed on a wire set and transported onto
  the tower (the exact form `placedMcNot` produces, with its raw `mcCtrl k pauliXGate` core replaced
  by the named gate). Its *unitary* generators are `hadamardGate, sGate, cnotGate, toffoliGate`; the
  base rotation `rotZGate θ` is a further generator (realised, below, by the four-gate measurement
  circuit — Exercise 4.41).
* `reachableTowerCircuitEvolutions_le_namedFourGateTowerGates` — the **containment**
  `reachableTowerCircuitEvolutions n θ ≤ namedFourGateTowerGates n θ`: every grounded reachable
  tower circuit is a named four-gate circuit, by `Submonoid.closure_le` — rotation generators via
  `qtowerSingleWire_mem_namedRotationTowerGates` (the rotation half) + the sub-submonoid inclusion,
  reversible generators via `mcNotTowerGate_mem_namedFourGateTowerGates` (unfolding `mcNotTowerGate`
  to expose the core `mcCtrl (S.card) pauliXGate` and rewriting it to `namedMcNotGate (S.card)` by
  `mcCtrl_pauliXGate_eq_namedMcNotGate`).
* `exists_phase_smul_op_mem_closure_op_namedFourGateTowerGates` — **the density core**: for
  `cos θ = 3/5` and any tower evolution `T : Evolution (qtower n qubit)`, some global phase `e^{iα}`
  makes `e^{iα} • T.op ∈ closure ((·.op) '' namedFourGateTowerGates n θ)`. Immediate from the
  tower density `exists_phase_smul_op_mem_closure_op_reachableTowerCircuitEvolutions` and
  the containment, by `closure_mono` (`SetLike.coe_subset_coe` + `Set.image_mono`). On its own this
  is the *unitary-submonoid* density and treats `rotZGate θ` as a **free** generator.
* `rzThreeFifthsMeasurement_success_realizes_rotZ` — **the four-gate measurement realisation** of
  the base rotation. The Figure-4.17 circuit `rzThreeFifthsCircuit` (`H, S, Toffoli` on two ancillas
  and a target) followed by the two-ancilla measurement `rzTwoAncillaMeasurement`, on the success
  outcome
  `(0, 0)` (probability `‖c‖² = 5/8`), applies `R_z(rzThreeFifthsAngle)` to the target: the success
  operator `rzTwoAncillaMeasurement.op (0,0)` on the circuit output is
  `rzThreeFifthsAmp 0 0 t • |0,0,t⟩`, whose amplitude realises `R_z(θ)` on `|t⟩`
  (`rzThreeFifthsCircuit_success_eq_rotZ`). This realises `rotZGate θ` by `{H, S, CNOT, Toffoli}` +
  measurement
  (Exercise 4.41).

The §4.5/§4.3 reduction itself (single-qubit density, the §4.5.1 two-level
decomposition, the §4.5.2 Gray-code reduction, the §4.3 controlled-gate reduction, and the §4.5.3
approximation) is linear algebra on matrices, in `AxQM/Concrete/`.

## The formalisation

**Step 1 — one-axis density.** `AxQM/Concrete/RotationDensity.lean`:

* `AxQM.Concrete.rotZ_mem_closure_range_zsmul_of_cos_eq_three_div_five` — **the core
  step**: if `cos θ = 3/5` then for every `α`, `R_z(α)` lies in the closure of `{R_z(nθ) : n ∈ ℤ}`;
  iterating `R_z(θ)` approximates any `z`-rotation to arbitrary accuracy.
* `AxQM.Concrete.rotX_mem_closure_range_zsmul_of_cos_eq_three_div_five` — the same for the
  `x`-rotations, via Hadamard conjugation.
* Their `Irrational (θ / (2π))`-hypothesis forms `rotZ_mem_closure_range_zsmul` /
  `rotX_mem_closure_range_zsmul`, plus the supporting `continuous_rotZ`, `rotZ_add_zsmul_four_pi`
  (the `4π`-periodicity), and `dense_zmultiples_sup` (density of the subgroup `⟨θ, 4π⟩ ⊆ ℝ`).

**Step 2 — single-qubit universality (up to global phase).**
`AxQM/Concrete/SingleQubitRotationUniversality.lean`:

* `AxQM.Concrete.reachableRotations θ` — the submonoid generated by `R_z(±θ), R_x(±θ)`
  (finite products of the two reachable gates and their inverses).
* `AxQM.Concrete.exists_phase_smul_mem_closure_reachableRotations` — **the single-qubit
  headline**: for `cos θ = 3/5` and every `U ∈ U(2)`, some global phase `e^{iα}` makes `e^{iα} U`
  a limit of finite products of the reachable gates. The two dense axes (Step 1) are assembled into
  every single-qubit unitary via the Z–Y decomposition (Theorem 4.1, `exists_zy_decomposition`), the
  bridge `rotY_eq_rotZ_mul_rotX_mul_rotZ` (`R_y(γ) = R_z(π/2) R_x(γ) R_z(-π/2)`, putting the third
  axis in reach), and closure of the reachable submonoid under products.

## Results relied on (already in the library)

* `irrational_div_two_pi_of_cos_eq_three_div_five` (Exercise 4.42) — `cos θ = 3/5 ⟹ θ/(2π)`
  irrational.
* `AxQM.Concrete.hadamardC_mul_rotZ_mul_hadamardC` and the gate-level
  `AxQM.hadamardGate_comp_rotZGate_comp_hadamardGate` — `H R_z(θ) H = R_x(θ)`.
* `AxQM.Concrete.exists_zy_decomposition` (Theorem 4.1) — the Z–Y decomposition of an
  arbitrary single-qubit unitary.
* `AxQM.rzThreeFifthsCircuit` and its diagonalisation (Exercise 4.41 infrastructure) — the
  circuit that realises `R_z(θ)` with `cos θ = 3/5` from `H, S, CNOT, Toffoli`.

## The `d × d` two-level decomposition (§4.5.1 — complete)

The general two-level-unitary decomposition of a `d × d` unitary (N&C §4.5.1, p. 189 — every unitary
is a product of two-level unitaries) is assembled from the lemmas below. The main result is

* `AxQM.Concrete.exists_twoLevelUnitaryList_prod_eq`
  (`AxQM/Concrete/TwoLevelDecomposition.lean`) — **every `d × d` unitary is a product of two-level
  unitaries**: for `U ∈ U(d)` there is a list `L` of two-level unitaries with `L.prod = U`. Proved
  by induction on `d`, chaining column-clearing, the block-diagonal peel, and the induction
  hypothesis on the corner; the column-clearing factors are undone by their conjugate transposes
  (`IsTwoLevelUnitary.conjTranspose`, `prod_map_blockOne`), which stay two-level. This is the
  structural input to the §4.5.2 reduction of universality to single-qubit gates and `CNOT`.

built from these lemmas:

* `AxQM.Concrete.givensRotation` (`AxQM/Concrete/GivensRotation.lean`) — the `2 × 2` Givens
  rotation of eq. (4.45) clearing a column entry.
* `AxQM.Concrete.twoLevelEmbed` (`AxQM/Concrete/TwoLevelEmbedding.lean`) — the general
  embedding of a `2 × 2` matrix into a chosen coordinate pair `{p, q}` of a `d × d` matrix,
  identity elsewhere. `twoLevelEmbed p q` is a `*`-homomorphism on the block
  (`twoLevelEmbed_one`/`twoLevelEmbed_mul`/`twoLevelEmbed_conjTranspose`), so an embedded `2 × 2`
  unitary is a two-level unitary (`isTwoLevelUnitary_twoLevelEmbed`); `twoLevelEmbed_mulVec` gives
  its action, mixing only the `p`- and `q`-components (the form the column-clearing step consumes).
* `AxQM.Concrete.exists_twoLevelUnitaryList_clear_first_column`
  (`AxQM/Concrete/TwoLevelColumnClear.lean`) — the column-clearing step of eqs.
  (4.44)–(4.50). For any `d × d` matrix `U` there is a list `L` of two-level unitaries (each a
  Givens rotation embedded in a pair `{0, q}`) such that `L.prod * U` has its first column a
  multiple of `e₀` (`(L.prod * U) i 0 = 0` for `i ≠ 0`), built from the vector-level
  `exists_twoLevelUnitaryList_mulVec_eq_zero_of_ne` by an induction that clears one coordinate at a
  time. This is the workhorse of the §4.5.1 induction's inductive step.
* `AxQM.Concrete.blockOne` (`AxQM/Concrete/BlockOneEmbedding.lean`) — the `1 ⊕ M` block
  embedding underlying the block-diagonal peel. `blockOne M` fixes coordinate `0` and acts as the
  `d × d` matrix `M` on the remaining coordinates `1, …, d` (via `Fin.succ`). Like `twoLevelEmbed`,
  `blockOne` is a `*`-homomorphism (`blockOne_one`/`blockOne_mul`/`blockOne_conjTranspose`), hence
  sends unitaries to unitaries (`blockOne_mem_unitaryGroup`) and, crucially for re-assembly, sends a
  two-level unitary to a two-level unitary with its `{p, q}` block shifted to `{p.succ, q.succ}`
  (`isTwoLevelUnitary_blockOne`). It embeds the decomposition of the `d × d` corner submatrix back
  into `d + 1` dimensions; its list form is `prod_map_blockOne`.
* `AxQM.Concrete.exists_phaseShift_mul_blockOne_of_clearFirstColumn`
  (`AxQM/Concrete/BlockDiagonalPeel.lean`) — the **block-diagonal peel** (N&C eq. 4.51): a unitary
  `W`
  whose first column is a multiple of `e₀` has its first row a multiple of `e₀` too (unitarity), so
  `W = phaseShift c * blockOne C` with `|c| = 1` and `C = W.submatrix Fin.succ Fin.succ` a `d × d`
  unitary corner. Both `phaseShift c` (`isTwoLevelUnitary_phaseShift`) and the `blockOne` factors
  are two-level, so the peel keeps the whole product inside the two-level class. This is the
  inductive step's dimension-lowering move.

## The §4.5.3 approximation calculus (chaining inequality)

The final universality step composes many *approximate* gates, so it needs N&C's error-composition
bound (§4.5.3, Box 4.1, eq. 4.63): with the error measure `E(U, V) = ‖U − V‖`, the error of a whole
sequence is at most the sum of the per-gate errors,
`E(Uₘ⋯U₁, Vₘ⋯V₁) ≤ Σⱼ E(Uⱼ, Vⱼ)`. This is pure general-normed-ring mathematics (it names no gate):

* `norm_listProd_sub_listProd_le` (`ToMathlib/Analysis/Normed/Ring/ProductTelescope.lean`) — **the
  chaining inequality**: for a list `l` of `(target, approximant)` pairs in a normed ring with
  `‖1‖ = 1`, all of norm `≤ 1` (unitaries qualify),
  `‖∏ (l j).1 − ∏ (l j).2‖ ≤ Σⱼ ‖(l j).1 − (l j).2‖`.
  The list-indexed companion of the single-generator `norm_pow_sub_pow_le`; proved by cons-induction
  on `a₀A − b₀B = a₀(A − B) + (a₀ − b₀)B`, using the helper `norm_listProd_le_one` (a product of
  sub-unit-norm factors is again sub-unit-norm).

This is the calculus that both the single-qubit approximation (eq. 4.81) and the `m`-gate circuit
approximation invoke to turn per-piece density into whole-circuit approximation.

## The §4.5.2 reduction (Gray codes)

§4.5.2 (p. 191) turns each *two-level* unitary from the §4.5.1 decomposition into a circuit of
single-qubit and `CNOT` gates. A two-level unitary acting non-trivially only on the two
computational basis states `|s⟩`, `|t⟩` is realised by walking a **Gray code** from `s` to `t` — a
sequence of bit-strings whose adjacent members differ in exactly one bit — performing a controlled
bit-flip at each one-bit step to bring `|s⟩` adjacent to `|t⟩`, applying one controlled-`Ũ`, then
undoing the swaps. The purely combinatorial ingredient — the Gray code itself — is in place:

* `AxQM.Concrete.grayCode` (`AxQM/Concrete/GrayCode.lean`) — for two bit-strings
  `s t : Fin m → Fin 2`, the path `grayCode s t` flipping, one at a time, exactly the coordinates on
  which `s` and `t` differ. It **starts at `s`** (`grayCode_head?`), **ends at `t`**
  (`grayCode_getLast?`), has **consecutive words differing in exactly one bit**
  (`grayCode_isChain`, over the relation `differsInOneBit`), and length `≤ m + 1`
  (`grayCode_length_le` — N&C's "`m ≤ n + 1`"). It is built from the reusable `grayPath t s L`
  (flip the coordinates listed in `L` in turn) via a clean structural induction:
  `grayPath_isChain_differsInOneBit` (the one-bit-per-step property, needing `L.Nodup` and each
  listed coordinate genuinely differing) and `grayPath_getLast?` (the endpoint). Pure `Fin 2` /
  `Finset` / `List` combinatorics.
  It is moreover a **simple** path — duplicate-free (`grayCode_nodup`, from the invariant
  `grayPath_apply_eq_of_not_mem` feeding `grayPath_nodup`: each entry holds the just-flipped
  coordinate at its `t`-value, so the head recurs nowhere in the tail) — hence its endpoint `t`
  occurs only as the last entry and lies off the initial segment,
  `t ∉ (grayCode s t).dropLast` (`grayCode_getLast_not_mem_dropLast`). That "`t` off the path
  `[g₁, …, g_{m-1}]`" fact is precisely the hypothesis the swap chain (`swapConj_swapChain_support`)
  consumes to keep `|t⟩ = |g_m⟩` fixed while relocating the active pair.

The **swap step** of that walk — "swap the basis states `|p⟩` and `|q⟩`" — is a
matrix operation:

* `AxQM.Concrete.isTwoLevelUnitary_swap` (`AxQM/Concrete/TwoLevelSwap.lean`) — the basis
  transposition `Matrix.swap ℂ p q` is a two-level unitary (acting non-trivially only on `{p, q}`);
  it is the elementary swap the Gray-code walk is built from.
* `AxQM.Concrete.IsTwoLevelUnitary.swap_conj` — **conjugation by a basis transposition
  relocates the support**: `Matrix.swap ℂ p q * U * Matrix.swap ℂ p q` is a two-level unitary with
  distinguished pair `{Equiv.swap p q a, Equiv.swap p q b}` when `U` had pair `{a, b}`. Iterating
  one such conjugation per one-bit Gray-code step moves the two active basis states until they
  differ in a single bit — where the two-level unitary is a controlled single-qubit gate. Its
  explicit-witness form `swap_conj_support` (unitary + support at `{swap p q a, swap p q b}` from
  unitary + support at `{a, b}`) is the shared single step both `IsTwoLevelUnitary.swap_conj` (its
  existential repackaging) and the list fold below reuse. The workhorse is the entry-reindex
  `swap_conj_apply`
  (`(Matrix.swap ℂ p q * U * Matrix.swap ℂ p q) i j = U (Equiv.swap p q i) (Equiv.swap p q j)`),
  built from the one-sided reindex identities `swap_mul_apply_eq` / `mul_swap_apply_eq`.

The **iterated** swap conjugation — folding that one step along the *whole* Gray-code walk — is:

* `AxQM.Concrete.swapConj` / `swapPerm` (`AxQM/Concrete/TwoLevelSwapList.lean`) — conjugation of
  a matrix by a *list* `L` of basis transpositions, head outermost
  (`swapConj ((p,q) :: L) U = Matrix.swap ℂ p q * swapConj L U * Matrix.swap ℂ p q`), and the
  composite index permutation `swapPerm L = Equiv.swap p₁ q₁ * ⋯ * Equiv.swap pₖ qₖ` the list
  effects. `swapConj_append` / `swapPerm_append` make the walk compose (the walk and its undo).
* `AxQM.Concrete.swapConj_unitary_support` — **the fold's headline**: if `U` is unitary
  acting non-trivially only on `{a, b}`, then `swapConj L U` is unitary acting non-trivially only
  on `{swapPerm L a, swapPerm L b}`. The support pair is carried along the walk *explicitly*
  (tracked by name, not merely existentially as in `IsTwoLevelUnitary`), so a consumer computes
  where `|s⟩`
  and `|t⟩` land — the ingredient that lets the walk conclude the two active states become
  bit-adjacent. `isTwoLevelUnitary_swapConj` packages the existential corollary. Proved by list
  induction, each step applying the shared single-transposition `swap_conj_support`.

The **swap chain** — the actual transposition list of N&C's first stage (eqs. 4.54–4.57), read off a
path of basis states — is:

* `AxQM.Concrete.swapChain` (`AxQM/Concrete/TwoLevelSwapChain.lean`) — for a path
  `path = [g₁, …, g_{m-1}]` of basis indices, the consecutive-pair transposition list
  `[(g_{m-2}, g_{m-1}), …, (g₁, g₂)]` (structural recursion
  `swapChain (a :: b :: l) = swapChain (b :: l) ++ [(a, b)]`, first swap innermost so, through the
  head-outermost `swapPerm`/`swapConj`, `|g₁⟩ ↔ |g₂⟩` is applied first). Its permutation action on
  the endpoints is pinned down by `swapPerm_swapChain_eq` — **head to last**,
  `swapPerm (swapChain path) g₁ = g_{m-1}` (N&C eq. 4.54; no `Nodup` needed, only the head tracked)
  — and `swapPerm_swapChain_apply_of_not_mem` — **fixes every index off the path** (the "all other
  states unchanged" clause, keeping `|t⟩ = |g_m⟩` fixed). The headline
  `swapConj_swapChain_support` feeds both into `swapConj_unitary_support`: conjugating a unitary
  with two-level support `{s, w}` (here `s = g₁` the path head, `w = g_m = t` off the path) by
  `swapChain path` yields a unitary with support `{g_{m-1}, g_m}` — the §4.5.2 relocation of the
  active pair to two adjacent basis states, at the matrix level.

The **Gray-code instantiation** — feeding the actual Gray-code path into that engine so the
relocated pair is *provably bit-adjacent* — finishes the first
stage:

* `AxQM.Concrete.grayCode_dropLast_head?`, `grayCode_dropLast_getLast?_differsInOneBit`
  (`AxQM/Concrete/GrayCode.lean`) — the two remaining path facts about the swap-chain path
  `(grayCode s t).dropLast = [g₁, …, g_{m-1}]` (for distinct `s ≠ t`): its head is `s`, and its
  last entry `g_{m-1}` is **bit-adjacent to `t`** (`differsInOneBit`, since `g_{m-1}`, `g_m = t` are
  consecutive Gray-code words — `grayCode_isChain`). With `grayCode_getLast_not_mem_dropLast`
  (`t` off the path, from `grayCode_nodup`) these are exactly the three hypotheses
  `swapConj_swapChain_support` consumes.
* `AxQM.Concrete.swapConj_swapChain_grayCode_support`
  (`AxQM/Concrete/TwoLevelGrayWalk.lean`) — **the §4.5.2 first-stage headline**: fixing any encoding
  `enc : (Fin m → Fin 2) ≃ Fin d` of the `m`-bit strings as the `d = 2^m` basis indices (e.g.
  `finFunctionFinEquiv`), a two-level unitary supported on `{enc s, enc t}` (`s ≠ t`), conjugated by
  the swap chain of the `enc`-image of `(grayCode s t).dropLast`, is again a two-level unitary,
  supported on `{enc e, enc t}` for some bit-string `e` with `differsInOneBit e t` — the relocated
  active pair differs in **exactly one bit**, the form of a controlled single-qubit gate. The three
  path facts are transported through the encoding (`List.head?_map` / `getLast?_map` / `mem_map` and
  injectivity of `enc`) and fed to the matrix engine.

The **controlled single-qubit gate** — N&C's "apply a controlled-`Ũ` operation, with the target
qubit located at the single bit where `g_{m-1}` and `g_m` differ" (the second-stage gate, once the
first stage has made the active pair bit-adjacent) — is an
explicit matrix:

* `AxQM.Concrete.ctrlSingleQubit` (`AxQM/Concrete/ControlledSingleQubit.lean`) — for an encoding
  `enc : (Fin m → Fin 2) ≃ Fin d`, a target bit `j`, a control pattern `c`, and a `2 × 2` matrix
  `Ũ`, the matrix that on `|enc x⟩` **applies `Ũ` to bit `j` of `x` when the other bits of `x` match
  `c`, and fixes `|enc x⟩` otherwise** — exactly the controlled-`Ũ` of the §4.5.2 second stage. The
  headline `ctrlSingleQubit_eq_twoLevelEmbed` identifies it entrywise with the §4.5.1 embedding
  `twoLevelEmbed (enc c[j↦0]) (enc c[j↦1]) Ũ` at the bit-adjacent pair `{c[j↦0], c[j↦1]}` (whose
  bit-adjacency is `differsInOneBit_update_zero_one`), so via `isTwoLevelUnitary_twoLevelEmbed`
  it is a two-level unitary when `Ũ ∈ U(2)` (`isTwoLevelUnitary_ctrlSingleQubit`). Its
  controlled action is read off from `twoLevelEmbed_mulVec`: `ctrlSingleQubit_mulVec` mixes only
  the two active components through `Ũ`, and `ctrlSingleQubit_mulVec_of_not_ctrl` fixes every
  basis state whose other bits miss the control pattern. This is the target the first-stage
  relocation (`swapConj_swapChain_grayCode_support`) hands its bit-adjacent two-level unitary to.

The **junction** — closing the loop by proving that the first-stage output *is* a controlled
single-qubit gate (not merely bit-adjacent) — joins the two
stages:

* `AxQM.Concrete.twoLevelBlock`, `eq_twoLevelEmbed_of_support`, `twoLevelEmbed_injective`,
  `twoLevelBlock_mem_unitaryGroup` (`AxQM/Concrete/TwoLevelControlledIdentification.lean`) — the
  general
  **structural converse** of `isTwoLevelUnitary_twoLevelEmbed`, reusable and naming no bit-strings:
  a matrix `W` agreeing with the identity off a coordinate pair `{p, q}` (`p ≠ q`) *is* the
  two-level embedding of its own `2 × 2` block, `W = twoLevelEmbed p q (twoLevelBlock W p q)`; the
  embedding is injective on the block, so the block of a two-level *unitary* is a `2 × 2` unitary
  (from `Wᴴ W = 1` through the `*`-homomorphism laws).
* `AxQM.Concrete.eq_ctrlSingleQubit_of_support`
  (`AxQM/Concrete/TwoLevelControlledIdentification.lean`) — **a two-level unitary supported on a
  bit-adjacent encoded pair `{enc a, enc b}` (`differsInOneBit a b`) equals
  `ctrlSingleQubit enc j c Ũ`** for the differing bit `j`, control pattern `c = a`, and a `2 × 2`
  *unitary* block `Ũ`. The two
  active states `{c[j↦0], c[j↦1]}` are exactly `{a, b}` (in one order or the other —
  `update_zero_one_eq_pair`), so the structural converse applies at `(enc c[j↦0], enc c[j↦1])` and
  `ctrlSingleQubit_eq_twoLevelEmbed` closes it. This is the *converse* of
  `isTwoLevelUnitary_ctrlSingleQubit`.
* `AxQM.Concrete.swapConj_swapChain_grayCode_eq_ctrlSingleQubit`
  (`AxQM/Concrete/TwoLevelControlledIdentification.lean`) — **the junction, assembled**: conjugating
  a
  two-level unitary supported on `{enc s, enc t}` (`s ≠ t`) by the Gray-code swap chain yields,
  verbatim, a controlled single-qubit gate `ctrlSingleQubit enc j c Ũ` with `Ũ` a `2 × 2` unitary.
  Chains the first-stage relocation (`swapConj_swapChain_grayCode_support`) straight into the
  controlled-`Ũ` identification, so the §4.5.2 first stage now hands its output to the second stage
  as an explicit controlled single-qubit gate.

## The §4.5.2 decomposition assembled (both stages, matrix level)

The two stages now compose into a decomposition of the two-level unitary *itself*, and the swaps of
the first stage are shown to be controlled single-qubit gates too:

* `AxQM.Concrete.swap_eq_twoLevelEmbed_swapTwo`,
  `AxQM.Concrete.swap_eq_ctrlSingleQubit` (`AxQM/Concrete/TwoLevelControlledDecomposition.lean`)
  — **a bit-adjacent basis transposition IS a controlled single-qubit gate.** The `d × d`
  transposition `Matrix.swap ℂ (enc a) (enc b)` of two bit-adjacent basis states
  (`differsInOneBit a b`) equals `ctrlSingleQubit enc j c (Matrix.swap ℂ 0 1)` — a controlled-`NOT`
  (the `2 × 2` block `Matrix.swap ℂ 0 1` is the `X`/`NOT` gate; `swapTwo_mem_unitaryGroup`), with
  the target on the single differing bit `j`. So every swap of the Gray-code walk is one of the same
  family of controlled single-qubit gates as the final controlled-`Ũ`. The general matrix fact is
  `swap_eq_twoLevelEmbed_swapTwo`: a transposition is the two-level embedding of the `2 × 2` swap.
* `AxQM.Concrete.swapConj_reverse_swapConj`
  (`AxQM/Concrete/TwoLevelControlledDecomposition.lean`) — conjugating by the *reversed*
  transposition
  list undoes conjugating by the list (each swap is an involution, `swap_swap_conj`), so the walk is
  invertible.
* `AxQM.Concrete.twoLevelUnitary_eq_swapConj_ctrlSingleQubit`
  (`AxQM/Concrete/TwoLevelControlledDecomposition.lean`) — **the assembled decomposition**: a
  two-level
  unitary `U` supported on `{enc s, enc t}` (`s ≠ t`) *equals* the swap-conjugate, by the reversed
  Gray-code chain, of a controlled single-qubit gate `ctrlSingleQubit enc j c Ũ` (`Ũ` a `2 × 2`
  unitary): `U = swapConj (…).reverse (ctrlSingleQubit enc j c Ũ)`. It chains the junction
  `swapConj_swapChain_grayCode_eq_ctrlSingleQubit` (conjugation *into* a controlled gate) with
  `swapConj_reverse_swapConj` (inverting the conjugation). Together with `swap_eq_ctrlSingleQubit`
  (each chain swap is itself a controlled single-qubit gate), this exhibits every two-level unitary
  as built entirely from controlled single-qubit gates — the §4.5.2 reduction, at the matrix level.

## The §4.5.2 product-of-gates form (explicit gate list)

The swap-conjugation decomposition is now flattened into an **explicit product (`List.prod`) of
controlled single-qubit gates** — the concrete "circuit as a list of gates" form:

* `AxQM.Concrete.IsCtrlSingleQubit`,
  `AxQM.Concrete.twoLevelUnitary_isProd_ctrlSingleQubit`
  (`AxQM/Concrete/TwoLevelControlledProduct.lean`) — **a two-level unitary is an explicit product of
  controlled single-qubit gates.** `IsCtrlSingleQubit enc g` is the predicate "`g = ctrlSingleQubit
  enc j c Ũ` for some target bit `j`, control pattern `c`, and `2 × 2` unitary `Ũ`" (the family both
  the Gray-code swaps and the final controlled-`Ũ` belong to). The headline
  `twoLevelUnitary_isProd_ctrlSingleQubit` states: a two-level unitary `U` supported on
  `{enc s, enc t}` (`s ≠ t`) equals `gates.prod` for an explicit list `gates`, *every* member of
  which is a controlled single-qubit gate. It flattens `twoLevelUnitary_eq_swapConj_ctrlSingleQubit`
  via the algebra `swapConj_eq_prod`
  (`swapConj L V = (L.map swap ++ V :: L.reverse.map swap).prod`),
  then classifies each factor: the middle factor is the controlled-`Ũ`, and every swap factor is a
  Gray-chain transposition, shown bit-adjacent (hence a controlled-`NOT`, `isCtrlSingleQubit_swap`)
  via the combinatorial bridge `rel_of_mem_swapChain` (every transposition of `swapChain path`
  relates its coordinates under any relation `path` is a `List.IsChain` for) fed the Gray chain
  `grayCode_isChain`. This is the §4.5.2 conclusion in gate-list form — the structural input the
  `n`-qubit lift maps over the §4.5.1 two-level factors.

## The `n`-qubit lift, first stage — every unitary is a product of controlled single-qubit gates

The two §4.5 halves now compose: mapping the §4.5.2 gate-list form over the §4.5.1 two-level factors
writes **any unitary on an `m`-bit register as an exact product of controlled single-qubit gates**
(`AxQM/Concrete/UnitaryControlledProduct.lean`):

* `AxQM.Concrete.isProd_ctrlSingleQubit_of_isTwoLevelUnitary` — **the bridge**: *any*
  two-level unitary `V` (in the `IsTwoLevelUnitary` sense, whose support pair `{p, q}` may be
  *degenerate*, `p = q` — a single-coordinate phase such as the §4.5.1 `phaseShift` factor) is a
  product of controlled single-qubit gates. For `p ≠ q` this is
  `twoLevelUnitary_isProd_ctrlSingleQubit` at `(enc.symm p, enc.symm q)`; for `p = q` the support
  `{p}` sits inside `{p, enc t}` for any partner bit-string `t ≠ enc.symm p` (one exists because
  there is at least one qubit, `Nontrivial (Fin m → Fin 2)`), so the *same* theorem applies at the
  distinct pair `(enc.symm p, t)` — the single-coordinate phase is hosted as a controlled
  single-qubit gate with a diagonal `2 × 2` block on that (arbitrary) partner qubit.
* `AxQM.Concrete.isProd_ctrlSingleQubit_of_forall_isTwoLevelUnitary` — **the list step**:
  a list all of whose members are two-level unitaries yields one list of controlled single-qubit
  gates with the *same* product (list induction, concatenating the per-factor decompositions from
  the bridge).
* `AxQM.Concrete.exists_isCtrlSingleQubit_list_prod_eq` — **the headline**: for
  `enc : (Fin m → Fin 2) ≃ Fin d` with at least one qubit and any `U ∈ U(d)`, there is an explicit
  list `gates`, **every** member a controlled single-qubit gate (`IsCtrlSingleQubit enc`), with
  `gates.prod = U`. It feeds the §4.5.1 two-level decomposition of `U` through the list step. The
  `Nontrivial (Fin m → Fin 2)` hypothesis is exactly "at least one qubit" (`m ≥ 1`) — the faithful
  scope, since a zero-qubit system has no gates and the §4.5.1 decomposition contains
  single-coordinate `phaseShift` factors that can only be hosted once a partner qubit exists.

## The `n`-qubit lift, second stage — the single-qubit gate on a wire

The §4.5.2 gates are *controlled* single-qubit gates, and a controlled gate with `SU(2)` block can
only approximate another `SU(2)`-block gate (the determinant is a topological invariant), so the
reachable set — dense in `U(2)` only *up to a global phase* — cannot approximate an arbitrary
controlled gate directly. N&C's §4.3 dissolves this: it reduces each controlled single-qubit gate to
a circuit of **uncontrolled single-qubit gates placed on individual wires** and `CNOT`s, and on an
*uncontrolled* wire gate the residual phase is a genuine *global* phase (harmless), not a relative
one. This step installs the matrix object that reduction targets and the approximation consumes
(`AxQM/Concrete/SingleQubitWire.lean`):

* `AxQM.Concrete.singleQubitOnWire enc j g` — on `|enc x⟩` applies the `2 × 2` matrix `g`
  to bit `j` of `x` (regardless of the other bits): the `ctrlSingleQubit` gate with its control
  condition dropped, block diagonal over the `j`-th bit's two-dimensional fibres. Its action is
  `singleQubitOnWire_mulVec` (mixes only the two components agreeing off wire `j`, through `g`), and
  it is a `*`-homomorphism on the block (`singleQubitOnWire_one`, `singleQubitOnWire_mul`,
  `singleQubitOnWire_conjTranspose`), hence sends unitaries to unitaries
  (`singleQubitOnWire_mem_unitaryGroup`).
* `AxQM.Concrete.singleQubitOnWire_smul` — **the phase-clean property**:
  `singleQubitOnWire enc j (c • g) = c • singleQubitOnWire enc j g`. As the gate is uncontrolled,
  a scalar on its `2 × 2` block multiplies the *whole* `d × d` matrix — the global phase that a
  controlled gate could not absorb.
* `AxQM.Concrete.exists_phase_smul_singleQubitOnWire_mem_closure` — **the headline**: for
  `cos θ = 3/5` and every `U ∈ U(2)`, some global phase `e^{iα}` makes
  `e^{iα} • singleQubitOnWire enc j U` a limit of `singleQubitOnWire enc j` applied to the reachable
  gates `R_z(±θ), R_x(±θ)`. Single-qubit universality (Step 2) is lifted to a chosen wire of the
  `m`-qubit register and kept phase-clean, via continuity of `singleQubitOnWire enc j`
  (`continuous_singleQubitOnWire`) and the global phase-equivariance above. This is the per-gate
  approximation the error-chaining inequality (`norm_listProd_sub_listProd_le`) will assemble over
  the whole circuit.

## The §4.3 reduction, first step — control-pattern normalisation

The §4.3 reduction of a controlled single-qubit gate to single-qubit and `CNOT` gates opens with
N&C's standard move: a control conditioned on the value `0` is turned into one conditioned on `1` by
conjugating that control wire with a `NOT` gate. That step is now available at the matrix level
(`AxQM/Concrete/ControlledSingleQubitConjugation.lean`):

* `AxQM.Concrete.flipWire enc k` — the basis-index involution flipping bit `k` of the
  encoded bit-string; `singleQubitOnWire_swap_apply` identifies the `X`-on-wire gate
  `singleQubitOnWire enc k (Matrix.swap ℂ 0 1)` (the `NOT` on wire `k`, an uncontrolled single-qubit
  gate already in the target family, unitary and an involution `singleQubitOnWire_swap_mul_self`)
  with its `0/1` permutation matrix.
* `AxQM.Concrete.singleQubitOnWire_swap_conj` — **conjugation by the `X`-on-wire gate is a
  reindexing**: `Wₖ * M * Wₖ = M.submatrix (flipWire enc k) (flipWire enc k)` for any `d × d` matrix
  `M` (the wire-flip analogue of `swap_conj_apply`), proved from the permutation-matrix entry form
  and the involutivity of `flipWire`.
* `AxQM.Concrete.ctrlSingleQubit_conj_singleQubitOnWire_swap` — **the headline: conjugating
  a controlled single-qubit gate by the `X`-on-wire gate flips its control bit.** For `k ≠ j`,
  `Wₖ * ctrlSingleQubit enc j c Ũ * Wₖ = ctrlSingleQubit enc j (c[k ↦ ¬c k]) Ũ` — the gate is
  unchanged except that the value control wire `k` is conditioned on is negated. Iterating this over
  the wires where `c` is `0` normalises any control pattern to all-`1` controls, the first step of
  the §4.3 reduction to the multiply-controlled gate on the all-ones pattern.

## The §4.3 reduction, second step — normalisation folded to all-`1` controls

The one-wire flip is now **folded over a list of control wires**, so an *arbitrary* control pattern
is brought to the all-`1` pattern by conjugation with a product of `X`-on-wire gates
(`AxQM/Concrete/ControlledSingleQubitNormalisation.lean`):

* `AxQM.Concrete.wireFlipProd enc L` — the product `∏ₖ Wₖ` of `X`-on-wire gates over a list
  `L` of wires, a product of uncontrolled single-qubit gates hence unitary
  (`wireFlipProd_mem_unitaryGroup`), with `wireFlipProd enc L * wireFlipProd enc L.reverse = 1`
  (`wireFlipProd_mul_reverse` — each `Wₖ` an involution, cancelling from the inside out, so the `Wₖ`
  need not commute). `AxQM.Concrete.flipPattern L c` is the pattern `c` with every bit in
  `L` negated (`flipPattern_apply_of_nodup`: exactly the listed wires, on a duplicate-free `L`).
* `AxQM.Concrete.wireFlipProd_conj_ctrlSingleQubit` — the fold of the one-wire step:
  `wireFlipProd enc L * ctrlSingleQubit enc j c Ũ * wireFlipProd enc L.reverse
      = ctrlSingleQubit enc j (flipPattern L c) Ũ` for a list `L` of wires all `≠ j`, iterating the
  one-wire flip along `L` (each step peels one `Wₖ` off each side, no commutativity used).
* `AxQM.Concrete.exists_wireFlipProd_conj_ctrlSingleQubit_one` — **the headline**: every
  controlled single-qubit gate is, up to conjugation by a product of `X`-on-wire gates, the gate
  with all controls conditioned on `1`:
  `ctrlSingleQubit enc j c Ũ
      = wireFlipProd enc L.reverse * ctrlSingleQubit enc j 1 Ũ * wireFlipProd enc L`, with `L` the
  wires `≠ j` on which `c` is `0`. This is the `Cⁿ(Ũ)` on the all-ones control pattern that the rest
  of the §4.3 reduction realises over `H, S, CNOT, Toffoli`.

## The §4.3 reduction, third step — the controlled-`ABC` reduction

With any control pattern normalised to all-`1` controls, the resulting `ctrlSingleQubit enc j 1 Ũ` —
a `Cⁿ(Ũ)` on target wire `j` — is now reduced to *uncontrolled* single-qubit wire gates and
multiply-controlled-`NOT`s, the matrix-level lift of N&C's Corollary 4.2
(`AxQM/Concrete/ControlledSingleQubitABCReduction.lean`):

* `AxQM.Concrete.wireGate enc j f` — the **fibrewise-gate abstraction** common to
  `singleQubitOnWire` and `ctrlSingleQubit`: a `d × d` matrix acting on each `j`-bit fibre
  `{x[j↦0], x[j↦1]}` by a `2 × 2` block `f x` depending only on the off-`j` pattern. Its one
  structural law is **blockwise multiplicativity** (`wireGate_mul`): fibrewise gates preserve each
  fibre, so `wireGate f * wireGate g = wireGate (fun y => f y * g y)`. Both existing gates are
  instances — `singleQubitOnWire_eq_wireGate` (a constant block) and `ctrlSingleQubit_eq_wireGate`
  (the block is `Ũ` on the controlled fibres, `1` elsewhere).
* `AxQM.Concrete.ctrlSingleQubit_one_eq_abc` — **the controlled-`ABC` identity** (Corollary
  4.2, lifted to the all-`1` pattern): for any `2 × 2` matrices `A, B, C, X` with `A B C = I`,
  `ctrlSingleQubit enc j 1 (A X B X C)
      = singleQubitOnWire enc j A · N · singleQubitOnWire enc j B · N · singleQubitOnWire enc j C`,
  where `N = ctrlSingleQubit enc j 1 X` is the multiply-controlled-`NOT` (block `X`). On the all-`1`
  fibre both `N`s fire (as `X`) so wire `j` sees `A X B X C`; off it both are the identity so wire
  `j` sees `A B C = I` — the mechanism by which two multiply-controlled-`NOT`s and three
  *uncontrolled* single-qubit gates realise a controlled gate. `ctrlSingleQubit_one_mul` (the
  all-`1`-controlled gate is multiplicative in its `2 × 2` block) is the supporting algebra.
* `AxQM.Concrete.exists_abc_reduction_ctrlSingleQubit_one` — **the general reduction**: for
  any `Ũ ∈ U(2)`, feeding the ABC decomposition (`exists_abc_decomposition`) gives
  `ctrlSingleQubit enc j 1 Ũ = ctrlSingleQubit enc j 1 (e^{iα} • 1) ·
  (singleQubitOnWire enc j A · N · singleQubitOnWire enc j B · N · singleQubitOnWire enc j C)`,
  exhibiting the all-`1`-controlled gate as three uncontrolled single-qubit gates on wire `j`, two
  multiply-controlled-`NOT`s, and one residual multiply-controlled *phase* gate
  `ctrlSingleQubit enc j 1 (e^{iα} • 1)`.

## The §4.3 reduction, fourth step — the multiply-controlled-`NOT` as a permutation gate

The ABC reduction leaves the all-`1`-controlled `X` gate `N = ctrlSingleQubit enc j 1 pauliX` — the
multiply-controlled `NOT` `Cⁿ(X)` — as the only *controlled* residue (the other pieces are
uncontrolled single-qubit wire gates and a phase). That gate is *classical reversible*: it merely
permutes the computational basis. This step exhibits it as such, connecting it to the reversible-
circuit machinery of Exercise 4.29 (`Concrete/MultiControlledNot*`, phrased on bit-string
permutations):

* `AxQM.Concrete.permGate` (`AxQM/Concrete/PermutationGate.lean`) — the **encoding-carried
  permutation gate**: for a bit-string permutation `σ : Equiv.Perm (Fin m → Fin 2)`,
  `permGate enc σ` is the `d × d` matrix realising `|enc x⟩ ↦ |enc (σ x)⟩`. It is a `*`-homomorphism
  in `σ`
  (`permGate_one`, `permGate_mul`) whose adjoint is the gate of the inverse permutation
  (`permGate_conjTranspose`), hence unitary (`permGate_mem_unitaryGroup`) — the common matrix
  incarnation of every classical reversible gate the universality reduction manipulates (`NOT`,
  `CNOT`, `Toffoli`, `Cⁿ(X)`, the Gray-code transpositions).
* `AxQM.Concrete.ctrlSingleQubit_one_pauliX_eq_permGate`
  (`AxQM/Concrete/MultiControlledNotGate.lean`) — **the bridge**:
  `ctrlSingleQubit enc j 1 pauliX = permGate enc (mcNotPerm (univ \ {j}) j)`. The matrix
  multiply-controlled `NOT` *is* the permutation gate of the combinatorial `mcNot (univ \ {j}) j`
  (controls all wires but `j`, target `j`) of `AxQM/Concrete/MultiControlledNot.lean`, proved
  entrywise
  from `pauliX`'s bit-flip action (`pauliX_apply_eq`) matching the `ctrlBit` truth table. Through
  `permGate`'s `*`-homomorphism algebra this transports the whole `O(n²)` no-work-qubit `Cⁿ(X)`
  circuit development to the matrix gate.

## The §4.3 reduction, fifth step — the multiply-controlled-`NOT` circuit as a matrix gate product

The multiply-controlled `NOT` `N = ctrlSingleQubit enc j 1 pauliX`, identified with the permutation
gate `permGate enc (mcNotPerm (univ \ {j}) j)` (fourth step), is realised as an **explicit product
of `Toffoli`/`CNOT`/`NOT` matrix gates** by transporting the combinatorial `Cⁿ(X)` circuit
(`Concrete/MultiControlledNot*`, Exercise 4.29) through `permGate`'s `*`-homomorphism
(`AxQM/Concrete/MultiControlledNotPermProduct.lean`):

* `AxQM.Concrete.IsToffoliPermGate` — the predicate "`G = permGate enc (mcNotPerm S t)` for
  a control set `S` of size `≤ 2`" (a `Toffoli`/`CNOT`/`NOT`); `IsToffoliPermGate.mem_unitaryGroup`
  gives each such factor's unitarity (the per-gate norm bound the §4.5.3 chaining calculus needs).
* `AxQM.Concrete.exists_isToffoliPermGate_prod_eq_mcNotPermGate` — **the bridge**: a valid
  combinatorial gate circuit `gs` (each gate `≤ 2`-controlled, target off its controls) with
  `mcNotDenote gs = mcNot S t` lifts to `permGate enc (mcNotPerm S ht) = Gs.prod`, an exact product
  of `IsToffoliPermGate` factors. The circuit denotation and `mcNotPerm S ht` agree as functions,
  hence as permutations (`Equiv.ext`), so the inductive core
  `exists_isToffoliPermGate_list_prod_permGate` — which folds each gate's `mcNotPerm` into the
  permutation and its `permGate` into the product via `permGate_mul` — transports across.
* `AxQM.Concrete.exists_isToffoliPermGate_prod_eq_mcNotPermGate_of_spare` — the corollary
  feeding `exists_mcNotCircuit`'s halving circuit straight in whenever a spare wire exists. The
  all-controls gate `mcNot (univ \ {j}) j` that `N` itself needs uses the *whole* register (no spare
  wire), so its circuit is the Barenco tight-register construction (a separate Exercise 4.29
  development); the bridge above is exactly the reusable transport step it plugs into.

## The tight-register `Cⁿ(X)` needs a genuine single-qubit gate (the `√NOT` foundation)

The all-controls residue `N = ctrlSingleQubit enc j 1 pauliX` — the multiply-controlled `NOT` on
the *tight* register of exactly `n + 1` wires (`n = m − 1` controls, target `j`, no spare wire) —
is, crucially, **not** realisable as a product of `Toffoli`/`CNOT`/`NOT` *permutation* gates when
`n ≥ 3`, by a **parity** obstruction: as a permutation of the `2^{n+1}` basis states `N` is a single
transposition (it swaps only the two strings with all controls `1`), hence **odd**, whereas every
`≤ 2`-controlled gate on `≥ 4` wires is an **even** permutation (it swaps `2^{k}`, `k ≥ 1`, disjoint
pairs), and a product of even permutations is even. So the §4.3/§4.5.2 permutation-gate bridge above
(`exists_isToffoliPermGate_prod_eq_mcNotPermGate`) applies only to sub-gates that *have* a spare
wire; the tight top gate `N` must be reduced with N&C's *no-work-qubit* construction (Exercise 4.30
/ Barenco *et al.* Lemma 7.5), which uses genuine **single-qubit `√X` gates** (the "single qubit
gates" of Exercise 4.29 are essential and cannot be replaced by classical `NOT`s). One Barenco step
exposes a free wire, after which every remaining `Cⁿ⁻¹(X)` sub-gate is spare-wire-equipped and feeds
the permutation bridge, and each controlled-`√X` reduces through the already-built controlled-`ABC`
machinery (`exists_abc_reduction_ctrlSingleQubit_one`) — so the only genuinely new matrix object the
tight reduction needs is the `√X` gate itself. This step installs it (`AxQM/Concrete/SqrtNot.lean`):

* `AxQM.Concrete.sqrtNot` — the **`√NOT` gate** `V = ½ !![1 + i, 1 − i; 1 − i, 1 + i]`, a
  fixed square root of the Pauli `X`/`NOT` gate. `sqrtNot_mul_self` is Barenco's defining property
  `V² = X`; `sqrtNot_conjTranspose` gives `Vᴴ` in closed form, with
  `sqrtNot_conjTranspose_mul_self_eq_pauliX` the companion `(Vᴴ)² = X`;
  `sqrtNot_conjTranspose_mul_self` / `sqrtNot_mul_conjTranspose` give `Vᴴ V = V Vᴴ = I`, hence
  `sqrtNot_mem_unitaryGroup` (`V ∈ U(2)`, a legitimate single-qubit gate). This is the matrix-level
  counterpart of Exercise 4.30's Evolution-level `sqrtChain`/`barencoNCircuit` development
  (`cnx_eq_barencoNCircuit`); the Exercise 4.43 reduction runs on the encoded-basis matrix
  gates (`ctrlSingleQubit enc`, `singleQubitOnWire enc`), so it needs a *matrix* `√X`. Pure `2 × 2`
  complex-matrix algebra.

## The subset-controlled single-qubit gate `Cᵏ(Ũ)` — the object the Barenco recursion lives in

The Barenco tight-register reduction expresses `Cⁿ(X) = Cⁿ(V²)` (with `V = √X = sqrtNot`) as a
product of *smaller* multiply-controlled gates — `Cⁿ(X) = C(V)·Cⁿ⁻¹(X)·C(V†)·Cⁿ⁻¹(X)·Cⁿ⁻¹(V)` —
whose factors are single-qubit gates controlled on **subsets** of the wires (one wire for `C(V)`,
`C(V†)`; `n − 1` wires for `Cⁿ⁻¹(X)`, `Cⁿ⁻¹(V)`). The two existing matrix gates sit at the extremes
of the control range — `ctrlSingleQubit enc j 1` is controlled on *every* wire but `j`, and
`singleQubitOnWire enc j` on *no* wire — so neither is the object those factors inhabit. This step
installs the interpolating gate (`AxQM/Concrete/MultiControlledSingleQubit.lean`):

* `AxQM.Concrete.mcCtrlSingleQubit enc S j Ũ` — on `|enc x⟩` applies the
  `2 × 2` gate `Ũ` to
  bit `j` of `x` when **every control wire in the set `S` is `1`**, fixing `|enc x⟩` otherwise.
  It is
  the fibrewise gate (`wireGate`) whose block is `Ũ` on the controlled fibres and `1` elsewhere,
  hence a `*`-homomorphism in the block on a fixed `S` (`mcCtrlSingleQubit_one` /
  `mcCtrlSingleQubit_mul` / `mcCtrlSingleQubit_conjTranspose`) sending unitaries to unitaries
  (`mcCtrlSingleQubit_mem_unitaryGroup`), with the controlled action read off by
  `mcCtrlSingleQubit_mulVec_of_ctrl` / `mcCtrlSingleQubit_mulVec_of_not_ctrl` (for `j ∉ S`). It
  **interpolates** the two extreme gates: `mcCtrlSingleQubit_empty` (`S = ∅`) is
  `singleQubitOnWire enc j Ũ` and `mcCtrlSingleQubit_univ_sdiff` (`S = univ \ {j}`) is
  `ctrlSingleQubit enc j 1 Ũ`. The reusable `wireGate_conjTranspose` (the adjoint counterpart of
  `wireGate_mul`) is added to the fibrewise-gate suite in `AxQM/Concrete/ControlledSingleQubit.lean`
  (beside its `wireGate_*` siblings) to support the algebra.
* `AxQM.Concrete.mcCtrlSingleQubit_pauliX_eq_permGate` — **the permutation bridge for the
  `NOT` block**: for `j ∉ S`, `mcCtrlSingleQubit enc S j pauliX = permGate enc (mcNotPerm S j)`,
  generalising `ctrlSingleQubit_one_pauliX_eq_permGate` (its `S = univ \ {j}` case) to an arbitrary
  control set. This is exactly the bridge that carries each *spare-wire* `Cⁿ⁻¹(X)` sub-gate of the
  Barenco reduction into the combinatorial `Cⁿ(X)` circuit development
  (`Concrete/MultiControlledNot*`) — through `permGate`'s `*`-homomorphism — hence into a product of
  `Toffoli`/`CNOT`/`NOT` gates (`exists_isToffoliPermGate_prod_eq_mcNotPermGate`). Its entrywise
  heart is `ctrlSet_pauliX_entry`, in `AxQM/Concrete/MultiControlledNotGate.lean` beside the
  all-`1`-controlled `ctrlOne_pauliX_entry`, which is now a one-line corollary of it
  (the `S`-general
  form carries the single shared control-condition/`pauliX`-entry case analysis).

## The Barenco tight-register `Cⁿ(X)` recursion — the reduction's key identity

With the subset-controlled gate `mcCtrlSingleQubit` in place as the object every Barenco factor
inhabits, the **tight-register recursion identity itself** is now proved as an exact matrix equation
(`AxQM/Concrete/MultiControlledSingleQubitBarenco.lean`):

* `AxQM.Concrete.mcCtrlSingleQubit_barenco_recursion` — **the Barenco recursion**
  (N&C §4.3 / Barenco *et al.* Lemma 7.5), for any single-qubit *unitary* `V`: distinguishing one
  control wire `c` from the remaining controls `S` (`c ∉ S`) and the target `j` (`j ≠ c`, `j ∉ S`),
  `mcCtrlSingleQubit enc (insert c S) j (V * V)
      = C(V) · Cⁿ⁻¹(X) · C(V†) · Cⁿ⁻¹(X) · Cⁿ⁻¹(V)`,
  where `C(V) = mcCtrlSingleQubit enc {c} j V` and `C(V†)` are single-qubit `V`/`V†` on wire `j`
  controlled on the one wire `c`, the two `Cⁿ⁻¹(X) = mcCtrlSingleQubit enc S c pauliX` are `NOT`s on
  wire `c` controlled on `S`, and `Cⁿ⁻¹(V) = mcCtrlSingleQubit enc S j V` is `V` on wire `j`
  controlled on `S`. Proved by collapsing the `Cⁿ⁻¹(X)·C(V†)·Cⁿ⁻¹(X)` sandwich (the two `NOT`s are
  the *same* permutation gate) to a single wire-`j` gate, whence all three surviving wire-`j`
  factors multiply blockwise (`wireGate_mul`) and the identity reduces to a per-`j`-pattern `2×2`
  check: on the four cases of `(c-bit, all-of-S-set)` the block products are `1`, `V†V = 1`,
  `VV† = 1`, `V·V`, matching the left side because `V` is unitary.
* `AxQM.Concrete.mcCtrlSingleQubit_pauliX_barenco_recursion` — **the `Cⁿ(X)` headline**,
  the `V = √X = sqrtNot` specialisation (`sqrtNot² = X`, `sqrtNot` unitary): the tight
  multiply-controlled `NOT` `Cⁿ(X) = mcCtrlSingleQubit enc (insert c S) j pauliX` factors as
  `C(√X) · Cⁿ⁻¹(X) · C(√X†) · Cⁿ⁻¹(X) · Cⁿ⁻¹(√X)`, peeling one control at the cost of a genuine
  single-qubit `√X` gate — the no-work-qubit reduction resolving the parity obstruction. Each
  `Cⁿ⁻¹(X)`/`Cⁿ⁻¹(√X)` factor uses `n − 1` controls, so on the tight `n + 1`-wire register it now
  has a spare wire: the `Cⁿ⁻¹(X)`s feed the permutation-gate bridge
  (`mcCtrlSingleQubit_pauliX_eq_permGate` → Toffoli/`CNOT`/`NOT` circuit) and each controlled-`√X`
  feeds the controlled-`ABC` machinery.

The reusable engine is the **conjugation-is-reindexing** lemma
`AxQM.Concrete.mcNotGate_conj` (`P · M · P = M.submatrix (flipCtrl …) (flipCtrl …)`, the
`mcCtrlSingleQubit`-analogue of `singleQubitOnWire_swap_conj`, since `P` is the permutation matrix
of the involution `flipCtrl` — the basis-index incarnation of the classical `mcNot`), refined to
`mcNotGate_conj_wireGate` for a wire-`j` gate (`P · wireGate enc j f · P = wireGate enc j (f ∘ mcNot
S c)`).

## The §4.3 subset-controlled `ABC` reduction — reducing each Barenco factor one recursion level

The Barenco recursion `Cⁿ(X) = C(√X)·Cⁿ⁻¹(X)·C(√X†)·Cⁿ⁻¹(X)·Cⁿ⁻¹(√X)` (above) expresses `Cⁿ(X)` in
*subset*-controlled single-qubit gates `mcCtrlSingleQubit enc S j Ũ`. To bottom the recursion out,
each such factor must be reduced to uncontrolled single-qubit gates and multiply-controlled `NOT`s —
the §4.3 controlled-`ABC` step, generalised from the all-`1`-controlled case to an arbitrary control
set `S`. This step installs that reduction and the peel of its phase residual
(`AxQM/Concrete/MultiControlledSingleQubitABCReduction.lean`):

* `AxQM.Concrete.mcCtrlSingleQubit_eq_abc` /
  `exists_abc_reduction_mcCtrlSingleQubit` — **the subset-controlled controlled-`ABC` reduction**
  (N&C Corollary 4.2, for an arbitrary control set),
  the direct generalisation of the all-`1`-controlled `ctrlSingleQubit_one_eq_abc` /
  `exists_abc_reduction_ctrlSingleQubit_one` (its `S = univ \ {j}` case, via
  `mcCtrlSingleQubit_univ_sdiff`). For `Ũ ∈ U(2)`, feeding the ABC decomposition
  (`exists_abc_decomposition`) gives `mcCtrlSingleQubit enc S j Ũ = mcCtrlSingleQubit enc S j
  (e^{iα} • 1) · (singleQubitOnWire enc j A · N · singleQubitOnWire enc j B · N ·
  singleQubitOnWire enc j C)` with `N = mcCtrlSingleQubit enc S j pauliX` — three *uncontrolled*
  single-qubit wire gates, two subset-controlled-`NOT`s (each with a spare wire on the tight
  register, so `mcCtrlSingleQubit_pauliX_eq_permGate` → the Toffoli/`CNOT`/`NOT` circuit bridge),
  and one residual subset-controlled *phase* gate. Both are `wireGate`-based: on the `S`-controlled
  fibres both `N`s fire (as `X`) so wire `j` sees `A X B X C`; off them both are the identity so
  wire `j` sees `A B C = I`.
* `AxQM.Concrete.phaseGate z` (`= diag(1, z)`, unitary for `z̄ z = 1`,
  `phaseGate_mem_unitaryGroup`) and `AxQM.Concrete.mcCtrlSingleQubit_phase_peel` — **the
  phase-residual peel**: the residual `mcCtrlSingleQubit enc S j (e^{iα} • 1)` applies the global
  phase to the target fibre exactly when every control in `S` is set — a phase on the whole
  `S`-controlled subspace, *independent of the target value* — so it equals a controlled
  **phase-block** gate on **one fewer control**, `mcCtrlSingleQubit enc (S.erase c) c (phaseGate z)`
  (for `c ∈ S`, `j ∉ S`; both sides are the common diagonal
  `diag(fun i => if all of S set then z else 1)`, `mcCtrlSingleQubit_smul_one_eq_diagonal` /
  `mcCtrlSingleQubit_phaseGate_eq_diagonal`). Iterating bottoms the phase out at the uncontrolled
  `singleQubitOnWire enc c (phaseGate z)` (`mcCtrlSingleQubit_empty`), and the phase-block gate,
  being a single-qubit unitary, recurses through the ABC reduction. Together the ABC reduction and
  this peel are the "recurse into smaller multiply-controlled gates" step: every Barenco factor
  reduces to uncontrolled wire gates, subset-controlled `NOT`s (→ Toffoli/`CNOT` via the spare-wire
  permutation bridge), and strictly-smaller multiply-controlled gates.

## The §4.3 work-qubit-assisted reduction — every spare-wire factor bottoms out (recursion closed)

The one-recursion-level pieces (ABC reduction, phase peel, spare-wire permutation bridge) are now
**assembled into a terminating recursion**: a *subset*-controlled single-qubit gate that has a spare
wire reduces to an exact product of the elementary gates the whole reduction bottoms out in —
(`AxQM/Concrete/MultiControlledSingleQubitSpareReduction.lean`):

* `AxQM.Concrete.IsToffoliOrSingleQubitGate enc G` — the **terminal gate class**: `G` is
  either a `≤ 2`-control reversible gate (`IsToffoliPermGate` — a `Toffoli`/`CNOT`/`NOT`) or an
  uncontrolled single-qubit unitary on a wire (`singleQubitOnWire enc j U`, `U ∈ U(2)`). These are
  exactly the gates directly available in / built from `H, S, CNOT, Toffoli`;
  `IsToffoliOrSingleQubitGate.mem_unitaryGroup` gives each factor's unitarity (the per-gate bound
  the §4.5.3 chaining calculus consumes).
* `AxQM.Concrete.exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX` — the
  **spare-wire subset-controlled `NOT`** `mcCtrlSingleQubit enc S j pauliX` (for `j ∉ S`,
  `(insert j S).card < m`) is an exact product of `Toffoli`/`CNOT`/`NOT` gates, composing the
  permutation bridge `mcCtrlSingleQubit_pauliX_eq_permGate` with the combinatorial `Cⁿ(X)` circuit
  `exists_isToffoliPermGate_prod_eq_mcNotPermGate_of_spare`.
* `AxQM.Concrete.exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit` — **the
  headline** (N&C §4.3, the reduction of `Cᵏ(U)` with work qubits; Barenco *et al.* Lemma 7.2): for
  any `Ũ ∈ U(2)`, `j ∉ S`, and a spare wire (`(insert j S).card < m`),
  `mcCtrlSingleQubit enc S j Ũ = gates.prod` with **every** factor an `IsToffoliOrSingleQubitGate`.
  Proved by strong induction on the control set `S` (`Finset.strongInductionOn`): the base `S = ∅`
  is the uncontrolled `singleQubitOnWire enc j Ũ` (`mcCtrlSingleQubit_empty`); the step ABC-reduces
  (`exists_abc_reduction_mcCtrlSingleQubit`) into three uncontrolled wire gates, two spare-wire
  subset-controlled `NOT`s (the `pauliX` lemma above), and a subset-controlled phase residual that
  **peels one control** (`mcCtrlSingleQubit_phase_peel`) into a gate on the strictly smaller control
  set `S.erase c ⊂ S` — the induction hypothesis. The spare-wire hypothesis persists down the
  recursion (`insert c (S.erase c) = S`), and the phase block's unitarity is
  `phaseGate_exp_mem_unitaryGroup` (`star (e^{iα}) · e^{iα} = 1`). This is the machine that
  discharges every Barenco recursion factor: once the tight-register `√X` construction exposes a
  spare wire, all remaining factors reduce to `Toffoli`/`CNOT`/single-qubit gates by this lemma —
  the "recurse until
  every gate is a `Toffoli`/`CNOT`/single-qubit gate" step, closed for the work-qubit-assisted case.

## The §4.3 reduction, closed for the tight register — every `Cⁿ(X)` bottoms out (no spare wire)

The work-qubit-assisted reduction of the previous step covers a subset-controlled gate **only when a
spare wire exists** (`(insert j S).card < m`); the **tight** top `Cⁿ(X)` — controlling *every* other
wire — is exactly the case it excludes (and, by the `AxQM/Concrete/SqrtNot.lean` parity obstruction,
genuinely cannot be a product of `Toffoli`/`CNOT`/`NOT` permutation gates). This step removes the
spare-wire hypothesis by chaining the tight-register Barenco `√X` recursion
(`mcCtrlSingleQubit_pauliX_barenco_recursion`) into the spare-wire reduction
(`AxQM/Concrete/MultiControlledSingleQubitTightReduction.lean`):

* `AxQM.Concrete.exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX'` — **the
  crux**: the multiply-controlled `NOT` `mcCtrlSingleQubit enc S j pauliX` is an exact product of
  terminal gates (`IsToffoliOrSingleQubitGate`) for **any** `j ∉ S`, with **no** spare-wire
  hypothesis (dropping the `(insert j S).card < m` of
  `exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit_pauliX`). Three cases: a spare wire → the
  spare-wire lemma; `S.card ≤ 2` → directly a single `Toffoli`/`CNOT`/`NOT`
  (`mcCtrlSingleQubit_pauliX_eq_permGate`); otherwise (`S.card ≥ 3`, no spare wire, so
  `m = S.card + 1 ≥ 4`) → the Barenco recursion peels one control `c` at the cost of a genuine
  single-qubit `√X`, and **each of the five factors `C(√X)·Cⁿ⁻¹(X)·C(√X†)·Cⁿ⁻¹(X)·Cⁿ⁻¹(√X)` uses at
  most `m − 1` wires**, hence has a spare wire and bottoms out by the (general-`Ũ` / `pauliX`)
  spare-wire reduction. This is the tight top `Cⁿ(X)` bottomed out **without** the Exercise 4.29
  tight-register combinatorial circuit `exists_mcNotCircuit_tight`: the `√X` recursion is precisely
  the device that trades the tight `Cⁿ(X)` for spare-wire factors plus a legitimate single-qubit
  gate. (`sqrtNot_conjTranspose_mem_unitaryGroup`, the unitarity of the `C(√X†)` block, is added
  beside the `sqrtNot` unitarity lemma in `AxQM/Concrete/SqrtNot.lean`.)
* `AxQM.Concrete.exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit'` — **the
  headline**: for any `Ũ ∈ U(2)` and any `j ∉ S` (no spare-wire hypothesis),
  `mcCtrlSingleQubit enc S j Ũ` is an exact product of terminal gates — the spare-wire-free
  counterpart of `exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit`. For the tight case the
  subset-controlled ABC reduction (`exists_abc_reduction_mcCtrlSingleQubit`) rewrites the gate as
  three uncontrolled wire gates, two tight `Cⁿ(X)`s (the crux above), and a phase residual that
  **peels one control** (`mcCtrlSingleQubit_phase_peel`) into
  `mcCtrlSingleQubit enc (S.erase c) c (phaseGate _)` — which now *has* a spare wire
  (`insert c (S.erase c) = S`, of card `m − 1 < m`), so bottoms out by the general spare-wire
  reduction. So **every** subset-controlled single-qubit gate on an encoded register — no constraint
  on the control set — is an exact product of `Toffoli`/`CNOT`/single-qubit gates:
  the §4.3 reduction
  of `Cᵏ(U)` in full, the form the §4.5.2 controlled single-qubit gates feed into.

## The two §4.5 halves and §4.3 composed — every unitary is an exact product of terminal gates

The §4.5 controlled-single-qubit decomposition and the §4.3 reduction now **compose** into the
exact-decomposition milestone: any unitary on an `m`-qubit register is an exact product of the
terminal gate class (`Toffoli`/`CNOT`/single-qubit gates),
(`AxQM/Concrete/UnitaryToffoliSingleQubitProduct.lean`):

* `AxQM.Concrete.exists_isToffoliOrSingleQubit_prod_eq_of_isCtrlSingleQubit` — **the
  bridge**: a controlled single-qubit gate `IsCtrlSingleQubit enc g` (i.e. `ctrlSingleQubit enc j c
  Ũ`, controlled on *all* other wires matching a pattern `c`) is an exact product of terminal gates.
  The control pattern is conjugated to all-`1` by a product of `X`-on-wire gates
  (`exists_wireFlipProd_conj_ctrlSingleQubit_one`); the all-`1`-controlled gate is the full-control
  member of the subset-controlled family (`mcCtrlSingleQubit_univ_sdiff`,
  `ctrlSingleQubit enc j 1 Ũ = mcCtrlSingleQubit enc (univ \ {j}) j Ũ`), discharged by the §4.3
  spare-wire-free reduction `exists_isToffoliOrSingleQubit_prod_eq_mcCtrlSingleQubit'`; and the two
  conjugating `wireFlipProd` factors are themselves terminal-gate products
  (`exists_isToffoliOrSingleQubit_prod_eq_wireFlipProd`, each factor an uncontrolled `NOT`-on-wire).
* `AxQM.Concrete.exists_isToffoliOrSingleQubit_list_prod_eq` — **the headline**: for an
  encoding `enc : (Fin m → Fin 2) ≃ Fin d` with at least one qubit (`Nontrivial (Fin m → Fin 2)`)
  and any `U ∈ U(d)`, there is an explicit list `gates`, **every** member an
  `IsToffoliOrSingleQubitGate`, with `gates.prod = U`. It feeds the §4.5 controlled-single-qubit
  decomposition (`exists_isCtrlSingleQubit_list_prod_eq`) through the bridge (list-folded by
  `exists_isToffoliOrSingleQubit_prod_eq_of_forall_isCtrlSingleQubit`). This is the *exact* gate
  decomposition of an arbitrary `m`-qubit unitary over the four-gate set's building blocks; the
  residual phase now sits on *uncontrolled* wire gates (a harmless *global* phase, not a relative
  one), which is exactly what makes the subsequent approximation step legitimate.

## The universality conclusion — `H, S, CNOT, Toffoli` are universal (the exercise, closed)

The approximation step now assembles the exact decomposition and the per-wire density into Exercise
4.43's conclusion — the four gates are universal (`AxQM/Concrete/FourGateUniversality.lean`):

* `AxQM.Concrete.reachableGateSet` / `AxQM.Concrete.reachableCircuits` — the
  elementary matrix gates the reduction bottoms out in and the four-gate set realises (the
  `≤ 2`-control reversible gates `IsToffoliPermGate`, and the uncontrolled single-qubit wire gates
  `singleQubitOnWire enc j g` with `g ∈ reachableRotations θ`), and the submonoid they generate —
  the matrix incarnation of "circuits assembled from `H, S, CNOT, Toffoli`". Their four-gate
  provenance is the narrative above plus the grounded `rzThreeFifthsCircuit` (Exercise 4.41).
* The assembly — each terminal gate is a limit of reachable circuits up to a phase, and the per-gate
  limits multiply with their phases adding into one global phase — is the **generic**
  `AxQM.Concrete.exists_phase_smul_mem_closure_reachableCircuitsOf`
  (`AxQM/Concrete/ReachableCircuits.lean`), the shared §4.5/§4.3 skeleton parameterised over an
  abstract
  single-qubit gate set `S` (also reused by Exercise 4.44 at `S = deutschWireGateSubmonoid α`). The
  four-gate-specific input is only the single-qubit density
  `exists_phase_smul_singleQubitOnWire_mem_closure` (N&C eq. 4.81, `cos θ = 3/5`).
* `AxQM.Concrete.exists_phase_smul_mem_closure_reachableCircuits` — **the headline** (N&C
  Exercise 4.43): for the reachability angle `θ` (`cos θ = 3/5`), an encoding
  `enc : (Fin m → Fin 2) ≃ Fin d` with at least one qubit, and *any* `U ∈ U(d)`, some global phase
  `e^{iα}` makes `e^{iα} • U ∈ closure ↑(reachableCircuits enc θ)`. In the finite-dimensional
  product topology on `Matrix (Fin d) (Fin d) ℂ`, closure is approximation to arbitrary accuracy, so
  this is exactly: **the circuits built from `H, S, CNOT, Toffoli` are dense in `U(d)` up to an
  (unobservable) global phase** — universality. A one-line instantiation of the generic assembly
  above at the single-qubit density `exists_phase_smul_singleQubitOnWire_mem_closure`.

The statement is the topological density `∈ closure` rather than an explicit `∀ ε, ∃ V, ‖·‖ < ε`
bound: in the fixed finite dimension the two coincide (`Matrix` carries the product topology, no
ambient norm), and `∈ closure` is the Mathlib-idiomatic density form. N&C's quantitative §4.5.3
error budget (eq. 4.63) is the separately-formalised `norm_listProd_sub_listProd_le`; it underlies
the convergence but is not re-invoked, the submonoid-closure route giving density directly.
-/
