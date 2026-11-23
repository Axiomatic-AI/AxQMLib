/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportChannel
import AxQM.Postulates.API.GateTeleportChannelRefMarginal
import AxQM.Postulates.API.MeasurementSimulation
import AxQM.Postulates.API.CompositeState
import AxQM.Postulates.PartialTraceTensor
import AxQM.Core.UniversalityReduction
import AxQM.Postulates.API.TensorPowSplit
import AxQM.Postulates.API.BlockGatePlacement
import AxQM.Postulates.API.LeftPairGate
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Core.McNotCircuitEvolution
import AxQM.Core.EvolutionQubitBasisExt
import AxQM.Concrete.CnotPairGatherPermutation

/-!
# Nielsen & Chuang, Problem 4.6 (Universality with prior entanglement)

*(N&C p. 213.)*

Show single-qubit unitaries + Bell-basis measurement + 4-qubit-state prep is universal.

## The reduction

Single-qubit unitaries are common to both resource sets, so — given that `{CNOT, single-qubit
gates}` is universal (the hypothesis) — the *new* set `{single-qubit unitaries, Bell-basis
measurement, four-qubit state preparation}` is universal **iff it can implement `CNOT`**, the one
missing two-qubit gate. Gottesman–Chuang implement `CNOT` by **gate teleportation**: prepare the
fixed four-qubit resource state `|χ⟩` (a `CNOT` pre-applied to the two *output* halves of two Bell
pairs — an "arbitrary four-qubit entangled state"), Bell-measure the two pairs `(q_A, a_in)` and
`(q_B, b_in)`, and — because the pre-applied `CNOT` sits on the two output halves — it lands on the
teleported result, up to a pair of **single-qubit** Pauli byproduct corrections fixed by the two
measurement outcomes. Every operation used (state prep of `|χ⟩`, two Bell measurements, single-qubit
corrections) is in the new resource set, so `CNOT` — hence, with the shared single-qubit gates,
every unitary — is implementable. That is Problem 4.6.

The **reduction core** is the `CNOT` gate-teleportation identity
(`cnotGateTeleportation_identity`, below): a theorem showing the resource set implements `CNOT` (up
to the outcome-determined single-qubit corrections). The **headline conclusion** — that the
resource set is **universal** on every register — is the theorem
`measurementResourceSetWires_realizes_of_universal` at the foot of this file: a reduction onto a
universality predicate that, given N&C's premise that `{CNOT, single-qubit}` is universal,
concludes the measurement resource set implements every evolution of `qubit ^⊗ₛ (n+2)`, for every
`n`.

## Universality in the library

Exercise 4.43 proves approximate universality of `{H, S, CNOT, Toffoli}`:
`AxQM.Concrete.exists_phase_smul_mem_closure_reachableCircuits` shows the circuits built
from those gates are dense in `U(d)` up to a global phase, over the submonoid
`Concrete.reachableCircuits`; and `Concrete.exists_isToffoliOrSingleQubit_list_prod_eq` gives the
*exact* decomposition of any unitary into `Toffoli`/`CNOT`/single-qubit gates. Problem 4.6's
conclusion is a **reduction onto that framework**.

The "resource set implements `CNOT`" theorem is **proved from the measurement postulates**, in
two steps:

* **Post-measurement collapse + Born rule** (`Postulates/API/GateTeleportMeasurement.lean`):
  `bellPairsMeasurement_op_gateTeleportResourceRegister` (Bell-measuring the two co-located pairs
  collapses the two output qubits to the single-qubit-corrected `CNOT`) and
  `bellPairsMeasurement_bornProb_pos` (each of the sixteen outcomes has positive Born probability,
  cf. `bellMeasurement_bornProb_bellState`). This reads `cnotGateTeleportation_identity` as a
  statement about the `Measurement` (Postulates 3/4).

* **Deterministic correction** (`Postulates/API/GateTeleportCorrection.lean`):
  `gateTeleportCorrection p q` is the outcome-determined correction — a tensor of two single-qubit
  `pauliByproduct` adjoints (`gateTeleportCorrection_eq_tmul`), so it uses only single-qubit
  unitaries — and
  `bellPairsMeasurement_corrected_op_gateTeleportResourceRegister` shows that applying it to the
  output pair recovers `CNOT (q_A ⊗ q_B)` **independently of the outcome**. So the resource set
  implements the `CNOT` gate *deterministically*, not merely up to a correction.

* **The induced `CNOT` operation** (this file, `bellPairsMeasurement_corrected_reducedRight_…`, with
  bridges in `Postulates/API/GateTeleportChannel.lean`): the deterministic `CNOT` read as a
  genuine **quantum operation** on the two input qubits. Preparing the register, Bell-measuring the
  two pairs (`Measurement.postMeasurement`, Postulate 4), applying the outcome-determined
  single-qubit correction (`Evolution.evolve`), and tracing out the measured pairs
  (`State.reducedRight`, the §2.4.3 marginal) sends the input to `cnotGate.evolvePure (q_A ⊗ q_B)` —
  for *every* outcome. This
  is "the resource set implements the `CNOT` **operation**" stated in the
  `State`/`Measurement`/`Evolution` API (the induced-operation form of `Problem8_2`'s
  `teleportationInducedState`), the composable input→output map used by the universality
  reduction.

The Gottesman–Chuang **reduction principle** is proved, register-general and reusable, in
`AxQM/Core/UniversalityReduction.lean`:

* `AxQM.Evolution.realizes_of_universal` — *if a resource realizes every gate of a
  universal generating family (a predicate `Realizes` containing the identity and closed under
  composition), then it realizes every evolution*. This is exactly "adding the missing gate makes
  the set universal", stated as a proved theorem rather than prose: one instantiates the family with
  `{CNOT, single-qubit}` (universal by hypothesis — N&C's given, the library's
  `linearOptics_universal`-style list-decomposition form) and shows the measurement resource set
  realizes each. Its `Submonoid` phrasing `Evolution.submonoid_eq_top_of_universal` reads "the
  closure of the resource's realizable gates is everything".

The reduction is instantiated on the **two-qubit register** by the declarations at the foot of this
file (`ResourceImplements`, `measurementResourceSet_realizes_of_universal`): assuming N&C's given
that `{CNOT, single-qubit}` is universal, the resource set implements every two-qubit evolution,
with the `CNOT` gate supplied by the gate-teleportation gadget
(`cnotResourceRealized`) — the first end-to-end use of the reduction with real resource content.
See the §"Instantiating the universality reduction on the two-qubit register" below.

**The register-general headline** is `cnotGateTeleportation_identity` (the resources implement
`CNOT`, up to single-qubit corrections) and its building blocks. It is stated as an algebraic vector
identity — the library's established form for teleportation results: the single-qubit
`teleportation_identity` (N&C §1.3.7) has the same shape, and Problem 10.4's
`encodingTeleportation_identity` follows the identical pattern. Its measurement reading is backed by
the proved Bell-measurement Born rule `bellMeasurement_bornProb_bellState`, not merely asserted.

The vector and operator forms of the teleportation identity are stated in
`AxQM/Postulates/API/` (as are the library's other teleportation developments). The item's physical
statement — *"the resource set implements the `CNOT` operation on the two input qubits,
deterministically"* — is stated in this file in terms of states, measurements and evolutions: the
induced quantum operation (`postMeasurement`/`reducedRight`/`evolve`) sends the input to the
`CNOT`-processed output. That theorem is
`bellPairsMeasurement_corrected_reducedRight_gateTeleportResourceRegister` (below); compare
`NC/Ch8/Problem8_2.lean`, the teleportation-as-a-quantum-operation item, whose
`teleportationInducedState`/`TeleportationRecovers` framework this induced-operation statement
mirrors. The bridges it uses are listed below.

## The formalisation

The development is assembled across the `Postulates/API/` files below (imported here transitively
via `GateTeleportationIdentity`), in dependency order.

### The gates (`Postulates/API/ControlledUnitary.lean`, `.../Teleportation.lean`)

* `AxQM.pauliXGate`, `AxQM.pauliZGate` — the single-qubit Pauli `X` (`NOT`) and
  `Z` gates as `Evolution`s, with their basis actions `X|i⟩ = |i+1⟩`, `Z|i⟩ = (-1)^i|i⟩`.
* `AxQM.pauliByproduct x y = X^y Z^x` — the teleportation byproduct correction, a
  single-qubit unitary; `pauliByproduct_op_apply_qubitBasis` its basis action.
* `AxQM.controlledUnitary U = |0⟩⟨0|⊗I + |1⟩⟨1|⊗U` — the general controlled-`U` gate
  `C(U)` (control = qubit, target = arbitrary system; N&C §4.3) as an `Evolution`, with a full
  operator-sum unitarity proof and its defining action (control `|0⟩ ↦ I`, `|1⟩ ↦ U`).
* `AxQM.cnotGate = controlledUnitary pauliXGate` — the `CNOT` gate, with the truth table
  `cnotGate|c,t⟩ = |c, t⊕c⟩` (`cnotGate_evolvePure_qubitBasis`). This is the missing two-qubit gate
  the protocol implements; it is reused by many other Chapter-4/8 items.

### The Bell basis and Bell measurement (`Postulates/API/BellBasis.lean`, `.../Teleportation.lean`)

* `AxQM.bellBasisVec x y` / `AxQM.bellState x y` (`|β_{xy}⟩`), the orthonormal
  `AxQM.bellBasis` of a two-qubit system, and the projective
  `AxQM.bellMeasurement` — the "measurement of a pair of qubits in the Bell basis".
  `bellMeasurement_bornProb_bellState` records its Born rule (`|β_xy⟩` gives outcome `(x,y)` with
  probability `1`), so the measurement reading of the teleportation identities is grounded in the
  measurement postulate, not merely annotated.

### The teleportation identities (`Teleportation.lean`, `DoubleTeleportation.lean`)

* `AxQM.teleportation_identity` — single-qubit teleportation:
  `|ψ⟩ ⊗ |Φ⁺⟩ = ½ Σ_{x,y} |β_{xy}⟩ ⊗ (X^y Z^x |ψ⟩)`; Bell-measuring the first pair (outcome
  `(x,y)`) leaves the third qubit in `X^y Z^x|ψ⟩`, corrected by `pauliByproduct x y`.
* `AxQM.double_teleportation_identity` — the parallel teleportation of two qubits.

### The resource state `|χ⟩` and the protocol reshape

* `AxQM.cnotGateTeleportResource` (`|χ⟩`, `Postulates/API/GateTeleportResource.lean`) — the
  four-qubit resource: `CNOT` applied to the two output halves of two `|Φ⁺⟩` Bell pairs;
  `cnotGateTeleportResource_vec` (`.../GateTeleportResourceExplicit.lean`) its explicit
  computational-basis form.
* `AxQM.gateTeleportProtocolReshape` (`Postulates/API/GateTeleportProtocolReshape.lean`) —
  the `QSystem.Iso` register reshape that co-locates the two measured pairs and the two output
  halves for Bell measurement.
* `AxQM.cnotGateTeleportResource_protocolReshape_eq_cnotOnRight`
  (`.../GateTeleportProtocolCnot.lean`) — the resource `CNOT` in operator form on the reshaped
  register.

### The Clifford propagation (`Postulates/API/CnotPauliPropagation.lean`)

* `AxQM.cnotGate_comp_pauliByproduct_tmul` — `CNOT` commuted back through a pair of
  single-qubit Pauli byproducts yields again a pair of single-qubit Pauli byproducts (the Clifford
  normaliser property that keeps the corrections single-qubit).

### The headline identity (`Postulates/API/GateTeleportationIdentity.lean`)

* `AxQM.gateTeleportProtocolReshape_bellPhiPlus_bellPhiPlus_teleport` — the correction-free
  teleportation form of the bare (no-resource-`CNOT`) protocol register.
* `AxQM.cnotGateTeleportation_identity` — **the `CNOT` gate-teleportation identity, the
  reduction core of Problem 4.6**: teleporting the two input qubits `q_A, q_B` through `|χ⟩`,
  `reshape ((q_A ⊗ q_B) ⊗ |χ⟩)
  = ¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩) ⊗ ((C_A ⊗ C_B) (CNOT (q_A ⊗ q_B)))`, `p = (x₁,y₁)`, `q = (x₂,y₂)`,
  with the two single-qubit corrections `C_A = pauliByproduct (p.1+q.1) p.2 = X^{y₁} Z^{x₁+x₂}` and
  `C_B = pauliByproduct q.1 (p.2+q.2) = X^{y₁+y₂} Z^{x₂}` (recall `pauliByproduct x y = X^y Z^x`).
  Bell-measuring the two pairs (outcomes `p, q`) yields, on the two output qubits, a single `CNOT`
  on the inputs up to the pair of corrections `C_A, C_B` — determined solely by the outcomes. Since
  those corrections are single-qubit unitaries, the protocol implements `CNOT` using only
  `{single-qubit unitaries, Bell-basis measurement, four-qubit state preparation}` — the **reduction
  core** from which the item's universality conclusion follows (once the reduction of §"Status" is
  formalised).

### The measurement grounding (`Postulates/API/GateTeleportMeasurement.lean`)

* `AxQM.bellPairsMeasurement` — the joint Bell measurement of the two co-located pairs, a
  genuine `Measurement` (Postulate 3).
* `AxQM.bellPairsMeasurement_op_gateTeleportResourceRegister` — the collapse identity: for
  outcome `(p, q)` the protocol register collapses to `¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ ((C_A ⊗ C_B)(CNOT (q_A ⊗
  q_B)))`, reading `cnotGateTeleportation_identity` as a statement about the `Measurement`.
* `AxQM.bellPairsMeasurement_bornProb_pos` — every one of the sixteen outcomes has positive
  Born probability (Postulate 3), so each is a possible measurement result.

### The deterministic `CNOT` (`Postulates/API/GateTeleportCorrection.lean`)

* `AxQM.gateTeleportCorrection x y` — the outcome-determined correction gate, the adjoint
  of the byproduct pair `C_A ⊗ C_B`; `gateTeleportCorrection_eq_tmul` exhibits it as a tensor of two
  single-qubit `pauliByproduct` adjoints, so it uses only single-qubit
  unitaries.
* `AxQM.bellPairsMeasurement_corrected_op_gateTeleportResourceRegister` — **the
  deterministic `CNOT`**: after Bell measurement, applying the correction to the output pair sends
  the register to
  `¼ (|β_p⟩ ⊗ |β_q⟩) ⊗ (CNOT (q_A ⊗ q_B))`, whose output factor is *independent of the outcome*. So
  the resource set implements `CNOT` deterministically, not merely up to a correction — completing
  step 1 of §"Status".

### The induced `CNOT` operation (this file; bridges in `Postulates/API/GateTeleportChannel.lean`)

The `State`-level reading of the deterministic `CNOT` — *the physics statement of the item*. The
bridges (in `GateTeleportChannel.lean`) lift the
corrected *vector* identity to a normalised pure state:

* `AxQM.norm_bellPairsMeasurement_op_gateTeleportResourceRegister` — the measured branch
  has norm `¼` (its amplitude), so it normalises and the `¼` divides out.
* `AxQM.gateTeleportCorrection_evolvePure_normalize` — the corrected, normalised branch is
  exactly the product pure state `(|β_p⟩ ⊗ |β_q⟩) ⊗ CNOT(q_A ⊗ q_B)`.

* `AxQM.bellPairsMeasurement_corrected_reducedRight_gateTeleportResourceRegister` — the
  induced `CNOT` operation for a **product** input: for every outcome `(p, q)`, Bell-measuring the
  two pairs (`Measurement.postMeasurement`, Postulate 4), applying the outcome-determined
  single-qubit correction (`Evolution.evolve`), and tracing out the measured pairs
  (`State.reducedRight`) sends the protocol register's output subsystem to
  `cnotGate.evolvePure (q_A ⊗ q_B)` — the `CNOT`-processed
  input, **independent of the outcome**. Stated in terms of the `State`/`Measurement`/`Evolution`
  API.

### The induced `CNOT` operation for an arbitrary input (the headline)

A product-input form would be genuinely too weak to be "the resource set implements the `CNOT`
**gate**": a gate must act correctly on *every* input, including a two-qubit state **entangled**
between its two wires (as an isolated `CNOT` in a circuit routinely receives), and because the
induced operation normalises the collapsed branch — so is **not linear** in the input — a
product-input statement does not extend to entangled inputs on its own.  So the whole
gate-teleportation chain is stated for a **general** input pure state `ψ` and the product-input
statements are its `ψ = q_A ⊗ q_B` corollaries.  The chain lives in
`GateTeleport{Measurement,Correction,Channel}.lean`: the reduction-core vector identity
(`cnotGateTeleportation_identity`) *is* linear in the input, so it extends off the product vectors
to `cnotGateTeleportation_identity_general` (arbitrary input `v`) by `TensorProduct.ext'`, and the
whole measurement/correction/normalisation chain is stated for a general input pure state `ψ`
(`gateTeleportRegisterGen`, `bellPairsMeasurement_op_gateTeleportRegisterGen`, `norm_...Gen`,
`gateTeleportCorrection_evolvePure_normalizeGen`), each product-input lemma re-expressed as a
one-line `ψ = q_A ⊗ q_B` corollary.

* `AxQM.bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen` — **the
  induced `CNOT` operation for _every_ two-qubit input** (this file's headline): for every input
  pure state `ψ` and every outcome `(p, q)`, the same measure/correct/trace-out procedure sends the
  output subsystem to `cnotGate.evolvePure ψ` — `CNOT` applied to `ψ`, **independent of the
  outcome**. Stated in terms of the `State`/`Measurement`/`Evolution` API.
  This is the faithful "the resource set implements the `CNOT` gate" — the
  composable input→output map, correct on entangled inputs — the universality reduction
  consumes.
-/

namespace AxQM

open scoped TensorProduct

/-- **The resource set implements the `CNOT` operation for _every_ two-qubit input,
deterministically** (Nielsen & Chuang, Problem 4.6 — the faithful induced-operation reading of the
Gottesman–Chuang gate-teleportation core).  This is the *workhorse*; the product-input
`bellPairsMeasurement_corrected_reducedRight_gateTeleportResourceRegister` below is its
`ψ = q_A ⊗ q_B` corollary.

The statement is over an **arbitrary** two-qubit input pure state `ψ` — including one that is
**entangled** between its two wires.  That generality is what makes this "the resource set
implements the `CNOT` **gate**": a gate must act correctly on *every* input, and the induced
operation (post-measurement collapse normalises, so it is *not* linear in the input) does not extend
from
product inputs to entangled ones on its own.  An isolated `CNOT` in a circuit routinely receives
such an entangled input from earlier gates, so this general-input form is the "resource realizes
`CNOT`" fact the measurement-based universality reduction consumes.

Run the protocol on input `ψ`: prepare the register `gateTeleportRegisterGen ψ` (the input beside
the four-qubit resource `|χ⟩`), **Bell-measure the two co-located pairs** with outcome `(p, q)`
(`bellPairsMeasurement.postMeasurement`, Postulate 4), apply the **outcome-determined single-qubit
correction** `gateTeleportCorrection p q` (`Evolution.evolve`; it is a tensor of two single-qubit
`pauliByproduct` adjoints, `gateTeleportCorrection_eq_tmul`, so it lies in resource #1), and read
off the **output subsystem** by tracing out the two measured pairs (`State.reducedRight`).  The
result is `cnotGate.evolvePure ψ` — `CNOT` applied to `ψ` — **for every outcome `(p, q)`** (the
right-hand side does not mention `p, q`).

Stated in terms of `Measurement.postMeasurement`, `Evolution.evolve`/`evolvePure`,
`State.reducedRight` and `toState`, unlike the vector/operator identities it is proved from.  It is
the induced-operation analogue of `Problem8_2`'s `teleportationInducedState`.
Proved from the general-input vector bridges (in `GateTeleport{Measurement,Correction,Channel}`):
post-measurement collapse of a pure input (`Measurement.postMeasurement_pure`) followed by the
corrected-branch factorisation (`gateTeleportCorrection_evolvePure_normalizeGen`), whose right
marginal is the output factor (`reducedRight_tmul`). -/
theorem bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen
    (ψ : PureState (qubit ⊗ qubit)) (p q : Fin 2 × Fin 2)
    (hp : bellPairsMeasurement.bornProb (gateTeleportRegisterGen ψ).toState (p, q) ≠ 0) :
    (((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).evolve
        (bellPairsMeasurement.postMeasurement
          (gateTeleportRegisterGen ψ).toState (p, q) hp)).reducedRight
      = (cnotGate.evolvePure ψ).toState := by
  have hv : (bellPairsMeasurement.op (p, q)) (gateTeleportRegisterGen ψ).vec ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_bellPairsMeasurement_op_gateTeleportRegisterGen]
    norm_num
  rw [Measurement.postMeasurement_pure bellPairsMeasurement (gateTeleportRegisterGen ψ)
      (p, q) hp hv, ← toState_evolvePure,
    gateTeleportCorrection_evolvePure_normalizeGen ψ p q hv, PureState.toState_tmul,
    State.reducedRight_tmul]

/-- **The resource set implements the `CNOT` operation on the two input qubits, deterministically**
(Nielsen & Chuang, Problem 4.6): the `ψ = q_A ⊗ q_B` corollary of
`bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen`.  For every outcome `(p, q)`,
measure→correct→trace-out sends the output subsystem to `cnotGate.evolvePure (q_A ⊗ q_B)` — `CNOT`
applied to the inputs, independent of the outcome.  Definitional special case
(`gateTeleportResourceRegister qA qB = gateTeleportRegisterGen (qA.tmul qB)`, `rfl`), so it takes
the product-register hypothesis `hp` directly. -/
theorem bellPairsMeasurement_corrected_reducedRight_gateTeleportResourceRegister
    (qA qB : PureState qubit) (p q : Fin 2 × Fin 2)
    (hp : bellPairsMeasurement.bornProb (gateTeleportResourceRegister qA qB).toState (p, q) ≠ 0) :
    (((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).evolve
        (bellPairsMeasurement.postMeasurement
          (gateTeleportResourceRegister qA qB).toState (p, q) hp)).reducedRight
      = (cnotGate.evolvePure (qA.tmul qB)).toState :=
  bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen (qA.tmul qB) p q hp

/-!
### The induced `CNOT` operation with an external reference (toward the `n`-wire lift)

Universality of a gate set is universality on **every** register, so the gate-teleportation gadget
must run on two *wires* of a larger register — wires generally **entangled with the other wires**.
That is the induced operation *tensored with the identity on a reference* `R`: the same
measure → correct → trace-out procedure, run on an input `Ψ` of `R ⊗ (qubit ⊗ qubit)` (the two
`CNOT` wires beside an arbitrary reference they may be entangled with), must produce `1_R ⊗ CNOT` on
`Ψ`.  This is the one genuinely-new ingredient the `n`-wire assembly needs (the product-input form
above does *not* extend to it: the induced operation normalises, so is nonlinear in the input, and a
`Ψ` entangled with `R` is not a product).  The vector-level chain threading `R` through the gadget
is `GateTeleportChannelRef{,Corrected,Marginal}.lean`; the state-level reading is the theorem
below.
-/

/-- **The resource set implements the `CNOT` operation on two wires entangled with a reference,
deterministically** (Nielsen & Chuang, Problem 4.6 — the induced-operation-tensors-with-identity
form; the reference generalisation of
`bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen`).

For an **arbitrary** input pure state `Ψ` of `R ⊗ (qubit ⊗ qubit)` — the two `CNOT` input wires
together with an arbitrary reference system `R` they may be **entangled** with — running the gadget
on the reference register `gateTeleportRegisterGenRef R Ψ` (input beside the four-qubit resource
`|χ⟩`): Bell-measure the two co-located pairs with outcome `(p, q)`
(`(bellPairsMeasurement.onRight R).postMeasurement`, Postulate 4), apply the outcome-determined
single-qubit correction `gateTeleportCorrection p q` on the two output wires (`Evolution.evolve`;
a tensor of single-qubit `pauliByproduct` adjoints, so in resource #1), reshape the register by the
middle-factor iso `QSystem.Iso.leftComm R M O` (bringing the two measured pairs to the front) and
trace out those pairs (`State.reducedRight`).  The result is `(cnotGate.onRight R).evolvePure Ψ` —
`1_R ⊗ CNOT` applied to `Ψ` — **for every outcome `(p, q)`**.

This is the faithful "the resource implements the `CNOT` gate on two wires of a register", correct
even when those wires are entangled with the rest of the register — the fact the register-general
universality reduction will feed into `Evolution.realizes_of_universal` for the `CNOT`-on-two-wires
gate.  Stated in terms of the `State`/`Measurement`/`Evolution` API and the transport `State.congr`.
Proved from the reference bridge
`gateTeleportCorrection_evolvePure_normalizeRef` (the corrected, normalised, reshaped state is the
product `(|β_p⟩ ⊗ |β_q⟩) ⊗ ((cnotGate.onRight R).evolvePure Ψ)`), whose right marginal
(`State.reducedRight_tmul`) is the output. -/
theorem bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGenRef
    (R : QSystem) (Ψ : PureState (R ⊗ (qubit ⊗ qubit))) (p q : Fin 2 × Fin 2)
    (hp : (bellPairsMeasurement.onRight R).bornProb
        (gateTeleportRegisterGenRef R Ψ).toState (p, q) ≠ 0) :
    (((((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).onRight
                R).evolve
          ((bellPairsMeasurement.onRight R).postMeasurement
            (gateTeleportRegisterGenRef R Ψ).toState (p, q) hp)).congr
        (QSystem.Iso.leftComm R ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) (qubit ⊗ qubit))).reducedRight
      = ((cnotGate.onRight R).evolvePure Ψ).toState := by
  have hv : (bellPairsMeasurement.onRight R).op (p, q)
      (gateTeleportRegisterGenRef R Ψ).vec ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_bellPairsMeasurement_onRight_op_gateTeleportRegisterGenRef]
    norm_num
  rw [Measurement.postMeasurement_pure (bellPairsMeasurement.onRight R)
      (gateTeleportRegisterGenRef R Ψ) (p, q) hp hv, ← toState_evolvePure,
    ← PureState.congr_toState, gateTeleportCorrection_evolvePure_normalizeRef R Ψ p q hv,
    PureState.toState_tmul, State.reducedRight_tmul]

/-!
### Instantiating the universality reduction on the two-qubit register

The pieces assembled above discharge, on the two-qubit register `qubit ⊗ qubit`, the hypotheses of
the register-general Gottesman–Chuang reduction `Evolution.realizes_of_universal`
(`Core/UniversalityReduction.lean`).  The generating family is the measurement resource set's
two-qubit action — the `CNOT` gate together with every single-qubit unitary on either wire — and
"realizes" is the closure `ResourceImplements` below.  The one genuinely-new obligation, that the
resource *realizes the `CNOT` gate*, is discharged by the general-input gate-teleportation
gadget (`bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen`), which is carried as
the witness of the `ResourceImplements.cnot` constructor — so the universality conclusion genuinely
routes through the gate-teleportation realization, not a bare assertion that `CNOT` is free.

This is the *two-qubit* instance of the reduction, conditional on N&C's given (`hUniversal`, that
`{CNOT, single-qubit}` is universal): a first end-to-end use of the reduction with real resource
content.  Universality on **every** register is the subject of the `n`-wire statements below, which
embed the `CNOT`-on-wires gadget into an `n`-wire register (`Evolution.onWires`) and use the
`n`-wire form of `hUniversal`.
-/

/-- **The measurement resource set's generating family on the two-qubit register** (Nielsen &
Chuang, Problem 4.6): the `CNOT` gate `cnotGate`, and every single-qubit unitary on either wire
(`U.onLeft qubit = U ⊗ 1`, `U.onRight qubit = 1 ⊗ U`).  These are exactly the resource set's gates
in their two-qubit action — the shared single-qubit unitaries (resource #1) and the `CNOT` that the
Bell-measurement/four-qubit-prep resources realize by gate teleportation.  This is the `IsGenerator`
family fed to `Evolution.realizes_of_universal`; N&C's premise that `{CNOT, single-qubit}` is
universal is the statement that this family generates every two-qubit evolution. -/
def IsResourceGenerator (E : Evolution (qubit ⊗ qubit)) : Prop :=
  E = cnotGate ∨ (∃ U : Evolution qubit, E = U.onLeft qubit) ∨
    (∃ U : Evolution qubit, E = U.onRight qubit)

/-- **The measurement resource set realizes the `CNOT` gate**, as a proposition: for every two-qubit
input pure state `ψ` and every Bell-measurement outcome `(p, q)`, the gate-teleportation procedure
(measure the two co-located pairs, apply the outcome-determined single-qubit correction, trace out
the measured pairs) sends the output subsystem to `cnotGate.evolvePure ψ`.  This is precisely the
statement of the general-input gadget `bellPairsMeasurement_corrected_reducedRight_…Gen`; it
is packaged as a named `Prop` so it can be carried as the witness of `ResourceImplements.cnot` and
supplied by `cnotResourceRealized`. -/
def CnotResourceRealized : Prop :=
  ∀ (ψ : PureState (qubit ⊗ qubit)) (p q : Fin 2 × Fin 2)
    (hp : bellPairsMeasurement.bornProb (gateTeleportRegisterGen ψ).toState (p, q) ≠ 0),
    (((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).evolve
        (bellPairsMeasurement.postMeasurement
          (gateTeleportRegisterGen ψ).toState (p, q) hp)).reducedRight
      = (cnotGate.evolvePure ψ).toState

/-- **The resource set realizes the `CNOT` gate** — `CnotResourceRealized` holds, witnessed by the
general-input gate-teleportation gadget.  This is the physical justification that makes the
`CNOT` a legitimate resource generator, and it is the sole nontrivial input to the two-qubit
universality reduction below. -/
theorem cnotResourceRealized : CnotResourceRealized :=
  bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGen

/-- **The gates the measurement resource set implements on the two-qubit register.**  Built by
composition from single-qubit unitaries applied directly (resource #1 — the `singleQubitLeft` /
`singleQubitRight` constructors, `U ⊗ 1` / `1 ⊗ U`) and the `CNOT` gate realized by gate
teleportation (the `cnot` constructor).  The `cnot` constructor **carries** the realization witness
`CnotResourceRealized`: a `CNOT` is admitted only together with a proof that the resource actually
induces its operation, so `ResourceImplements` is not the vacuous "closure of an abstract gate set"
but genuinely tracks resource realizability — the universality conclusion built from it routes
through the gate-teleportation gadget (`cnotResourceRealized`).

Together with `ResourceImplements.one`/`.comp` (the identity is free; realizable gates compose),
these are exactly the `Realizes 1` / `hcomp` / `hgen` obligations of
`Evolution.realizes_of_universal`. -/
inductive ResourceImplements : Evolution (qubit ⊗ qubit) → Prop
  /-- The identity is realized (do nothing). -/
  | one : ResourceImplements 1
  /-- Realizable gates compose (run one protocol after the other). -/
  | comp {U V : Evolution (qubit ⊗ qubit)} :
      ResourceImplements U → ResourceImplements V → ResourceImplements (U.comp V)
  /-- A single-qubit unitary on the left wire, `U ⊗ 1`, is realized directly (resource #1). -/
  | singleQubitLeft (U : Evolution qubit) : ResourceImplements (U.onLeft qubit)
  /-- A single-qubit unitary on the right wire, `1 ⊗ U`, is realized directly (resource #1). -/
  | singleQubitRight (U : Evolution qubit) : ResourceImplements (U.onRight qubit)
  /-- The `CNOT` gate is realized by gate teleportation, witnessed by `CnotResourceRealized`. -/
  | cnot (h : CnotResourceRealized) : ResourceImplements cnotGate

/-- **Every resource generator is resource-realized.**  Case analysis on `IsResourceGenerator`: the
`CNOT` by the gate-teleportation gadget (`cnotResourceRealized`), each single-qubit generator by
direct application.  This is the `hgen` obligation of `Evolution.realizes_of_universal`. -/
theorem ResourceImplements.of_generator {V : Evolution (qubit ⊗ qubit)}
    (hV : IsResourceGenerator V) : ResourceImplements V := by
  rcases hV with rfl | ⟨U, rfl⟩ | ⟨U, rfl⟩
  · exact .cnot cnotResourceRealized
  · exact .singleQubitLeft U
  · exact .singleQubitRight U

/-- **The measurement resource set is universal on the two-qubit register** (Nielsen & Chuang,
Problem 4.6 — the Gottesman–Chuang reduction, two-qubit instance).  Assuming N&C's given that the
gate family `{CNOT, single-qubit}` is universal — every two-qubit evolution is a finite ordered
product of `IsResourceGenerator` gates (`hUniversal`) — the resource set of *single-qubit unitaries,
Bell-basis measurement, and four-qubit state preparation* implements **every** two-qubit evolution
`E` (`ResourceImplements E`).

This is `Evolution.realizes_of_universal` instantiated with `Realizes := ResourceImplements` and
`IsGenerator := IsResourceGenerator`: the identity and composition closure are the
`ResourceImplements.one`/`.comp` constructors, and every gate of the generating family is
realized by `ResourceImplements.of_generator` — the single genuinely-new step being the `CNOT`,
realized by the gate-teleportation gadget (`cnotResourceRealized`).  So the reduction
"add the missing `CNOT` ⟹ universal" is here a proved theorem whose proof genuinely consumes
the gate-teleportation realization.

**Scope.** This is the reduction on the *two-qubit* register.  Universality of a gate set
is universality on **every** register; the `n`-wire register version (gates embedded
by `Evolution.onWires`, the `CNOT` realized by the register-embedded gate-teleportation
gadget, and the `n`-wire `hUniversal`) is given below.  N&C's
`{CNOT, single-qubit}` universality is taken here as the explicit hypothesis `hUniversal`, exactly
the problem's stated premise. -/
theorem measurementResourceSet_realizes_of_universal
    (hUniversal : ∀ E : Evolution (qubit ⊗ qubit),
      ∃ L : List (Evolution (qubit ⊗ qubit)), (∀ V ∈ L, IsResourceGenerator V) ∧ L.prod = E)
    (E : Evolution (qubit ⊗ qubit)) : ResourceImplements E :=
  Evolution.realizes_of_universal ResourceImplements.one
    (fun hU hV => hU.comp hV) (fun _ hV => ResourceImplements.of_generator hV) hUniversal E

/-!
### Toward the `n`-wire register: `CNOT` on a designated wire pair

The reference induced-operation theorem
`bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGenRef` above realizes `CNOT`
on two wires *beside an abstract reference system* `R`.  Universality of the resource set,
however, is universality on the honest `m`-wire register `qubit ^⊗ₛ m`, where the reduction's
generators are `CNOT`/single-qubit gates addressed to specific wires.  This block bridges the two:
instantiating the reference `R` with the tensor-power register `qubit ^⊗ₛ n` and reshaping
`qubit ^⊗ₛ (n+2)` into `(qubit ^⊗ₛ n) ⊗ (qubit ⊗ qubit)` (the first `n` wires as the reference,
the last two as the `CNOT` input pair), the gate-teleportation gadget realizes the `CNOT` gate
placed on the last two wires of the register — the register-level form of the reference induced
operation, correct even when those two wires are entangled with the other `n`.  That placed gate is
identified with the library's **canonical** wire-addressed controlled-`NOT`
(`placedCnotBackPair_eq_placedMcNot`: `= Evolution.placedMcNot {n} (n+1)`), so the gadget realizes
the canonical `CNOT` (`placedMcNot_gateTeleport_realized`), not a new parallel idiom.  The
arbitrary-wire-pair routing (via `Evolution.permWires`) and the `n`-wire universality assembly
build on this.
-/

/-- The two-wire register collapse `qubit ^⊗ₛ 2 ≃ₛ qubit ⊗ qubit`: the block split
`QSystem.tensorPowAdd qubit 1 1` (into two single-wire powers) followed by dropping each singleton
tail (`tensorPowOne`).  Built from `tensorPowAdd` rather than the head-peel `tensorPowSuccHead` so
that its computational-basis action `qubitTensorPowTwoIso_congr_piTensor` reduces through the
`tensorPowAdd` product dictionary. -/
noncomputable def qubitTensorPowTwoIso : (qubit.tensorPow 2).Iso (qubit ⊗ qubit) :=
  (QSystem.tensorPowAdd qubit 1 1).trans (qubit.tensorPowOne.symm.tmul qubit.tensorPowOne.symm)

/-- **Product-state action of `qubitTensorPowTwoIso`**: it carries the two-wire product state
`⨂ᵢ g i` to `g 0 ⊗ g 1`.  The `tensorPowAdd` product dictionary splits off the two single-wire
blocks, each collapsed to `qubit` by the singleton dictionary. -/
theorem qubitTensorPowTwoIso_congr_piTensor (g : Fin 2 → PureState qubit) :
    PureState.congr qubitTensorPowTwoIso (PureState.piTensor g) = (g 0).tmul (g 1) := by
  erw [qubitTensorPowTwoIso, PureState.congr_trans, QSystem.tensorPowAdd_congr_piTensor]
  erw [PureState.congr_tmul]
  rw [QSystem.congr_tensorPowOne_symm_piTensor, QSystem.congr_tensorPowOne_symm_piTensor]; rfl

/-- **The back-pair reshape** `qubit ^⊗ₛ (n+2) ≃ₛ (qubit ^⊗ₛ n) ⊗ (qubit ⊗ qubit)`: split the
`(n+2)`-wire register into its first `n` wires (the reference the `CNOT` wires may be entangled
with) and its last two wires (the `CNOT` input pair).  It is the block split
`QSystem.tensorPowAdd qubit n 2` followed by collapsing the 2-wire tail to `qubit ⊗ qubit`
(`qubitTensorPowTwoIso`). -/
noncomputable def qubitBackPairReshape (n : ℕ) :
    (qubit.tensorPow (n + 2)).Iso ((qubit.tensorPow n) ⊗ (qubit ⊗ qubit)) :=
  (QSystem.tensorPowAdd qubit n 2).trans
    ((QSystem.Iso.refl (qubit.tensorPow n)).tmul qubitTensorPowTwoIso)

/-- **Product-state action of the back-pair reshape**: it carries the `(n+2)`-wire product state
`⨂ᵢ f i` to `(⨂_{i<n} f (castAdd i)) ⊗ (f (wire n) ⊗ f (wire n+1))` — the first `n` wires as the
reference block, the last two as the `CNOT` pair. -/
theorem qubitBackPairReshape_congr_piTensor (n : ℕ) (f : Fin (n + 2) → PureState qubit) :
    PureState.congr (qubitBackPairReshape n) (PureState.piTensor f)
      = (PureState.piTensor (fun i : Fin n => f (Fin.castAdd 2 i))).tmul
          ((f (Fin.natAdd n 0)).tmul (f (Fin.natAdd n 1))) := by
  erw [qubitBackPairReshape, PureState.congr_trans, QSystem.tensorPowAdd_congr_piTensor]
  erw [PureState.congr_tmul]
  exact congr_arg₂ _ (PureState.congr_refl _) (qubitTensorPowTwoIso_congr_piTensor _)

/-- **Backward product action of the back-pair reshape**: `(qubitBackPairReshape n).symm`
reassembles a reference block `⨂ᵢ P i` and a two-qubit input `a ⊗ b` into the single `(n+2)`-wire
product
`⨂ (Fin.append P ![a, b])` — the reference on the first `n` wires, `a`/`b` on wires `n`/`n+1`. -/
theorem qubitBackPairReshape_symm_congr (n : ℕ) (P : Fin n → PureState qubit)
    (a b : PureState qubit) :
    PureState.congr (qubitBackPairReshape n).symm ((PureState.piTensor P).tmul (a.tmul b))
      = PureState.piTensor (Fin.append P ![a, b]) := by
  have h := qubitBackPairReshape_congr_piTensor n (Fin.append P ![a, b])
  have hP : (fun i : Fin n => (Fin.append P ![a, b]) (Fin.castAdd 2 i)) = P := by
    funext i; rw [Fin.append_left]
  rw [hP, Fin.append_right, Fin.append_right] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  erw [← h, PureState.congr_symm_congr]

/-- **`CNOT` on the last two wires of the `(n+2)`-wire register** `qubit ^⊗ₛ (n+2)`: the two-qubit
`cnotGate` acting on the back pair (`cnotGate.onRight (qubit ^⊗ₛ n)`), transported onto the register
through the back-pair reshape `qubitBackPairReshape n`.  This is the register-level `CNOT` gate
that the gate-teleportation gadget realizes; `placedCnotBackPair_evolvePure_congr` records that it
acts as `CNOT` on the last two wires and as the identity on the first `n`. -/
noncomputable def placedCnotBackPair (n : ℕ) : Evolution (qubit.tensorPow (n + 2)) :=
  Evolution.congr (qubitBackPairReshape n).symm (cnotGate.onRight (qubit.tensorPow n))

/-- **`placedCnotBackPair` is `CNOT` on the last two wires** (identity on the first `n`): on an
input reshaped as `u ⊗ w` — `u` on the first `n` wires, `w` on the last two — it applies `cnotGate`
to `w` and leaves `u` unchanged.  This exhibits `placedCnotBackPair` as a genuine `CNOT` gate
addressed to the back pair; that it is *the canonical* wire-addressed `CNOT` is
`placedCnotBackPair_eq_placedMcNot` (`= Evolution.placedMcNot {n} (n+1)`), against which its
computational-basis truth table is a canonical fact rather than a statement about the bespoke
reshape. -/
theorem placedCnotBackPair_evolvePure_congr (n : ℕ) (u : PureState (qubit.tensorPow n))
    (w : PureState (qubit ⊗ qubit)) :
    (placedCnotBackPair n).evolvePure
        (PureState.congr (qubitBackPairReshape n).symm (u.tmul w))
      = PureState.congr (qubitBackPairReshape n).symm (u.tmul (cnotGate.evolvePure w)) := by
  rw [placedCnotBackPair, Evolution.congr_evolvePure_congr, Evolution.onRight_evolvePure]

/-- **The resource set realizes `CNOT` on the last two wires of the register** (Nielsen & Chuang,
Problem 4.6 — the gate-teleportation gadget embedded into the `(n+2)`-wire register).  For every
input pure state `φ` of `qubit ^⊗ₛ (n+2)` and every Bell-measurement outcome `(p, q)`: reshape `φ`
into `(qubit ^⊗ₛ n) ⊗ (qubit ⊗ qubit)` (`qubitBackPairReshape n`) so the first `n` wires are the
reference and the last two are the `CNOT` input, run the reference gate-teleportation gadget on the
two input wires (`(bellPairsMeasurement.onRight _).postMeasurement`, then the outcome-determined
single-qubit correction `gateTeleportCorrection p q`, then reshape and trace out the measured
pairs), and reshape the surviving register back to `qubit ^⊗ₛ (n+2)`.  The result is
`(placedCnotBackPair n).evolvePure φ` — `CNOT` applied to the last two wires — **for every outcome
`(p, q)`** (the right-hand side does not mention `p, q`).

This is the register-level form of
`bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGenRef` (its `R = qubit ^⊗ₛ n`
instance, transported onto the honest tensor-power register): the "resource realizes the `CNOT`
generator on two wires of `qubit ^⊗ₛ (n+2)`" fact the register-general universality reduction will
consume, correct even when those two wires are entangled with the other `n`.  The
arbitrary-wire-pair generalisation (via `Evolution.permWires`) and the `n`-wire universality
assembly build on it.  Stated in terms of the `State`/`Measurement`/`Evolution` API and the
transport `State.congr`.  Proved from the reference theorem by
transport (`PureState.congr_toState` and the `Evolution.congr`/`evolvePure` naturality baked into
`placedCnotBackPair`). -/
theorem placedCnotBackPair_realized (n : ℕ) (φ : PureState (qubit.tensorPow (n + 2)))
    (p q : Fin 2 × Fin 2)
    (hp : (bellPairsMeasurement.onRight (qubit.tensorPow n)).bornProb
        (gateTeleportRegisterGenRef (qubit.tensorPow n)
          (PureState.congr (qubitBackPairReshape n) φ)).toState (p, q) ≠ 0) :
    (((((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).onRight
                (qubit.tensorPow n)).evolve
          ((bellPairsMeasurement.onRight (qubit.tensorPow n)).postMeasurement
            (gateTeleportRegisterGenRef (qubit.tensorPow n)
              (PureState.congr (qubitBackPairReshape n) φ)).toState (p, q) hp)).congr
        (QSystem.Iso.leftComm (qubit.tensorPow n) ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))
          (qubit ⊗ qubit))).reducedRight.congr (qubitBackPairReshape n).symm
      = ((placedCnotBackPair n).evolvePure φ).toState := by
  rw [bellPairsMeasurement_corrected_reducedRight_gateTeleportRegisterGenRef
      (qubit.tensorPow n) (PureState.congr (qubitBackPairReshape n) φ) p q hp,
    ← PureState.congr_toState]
  congr 1

/-!
### Reconciliation with the canonical wire-addressed `CNOT`

`placedCnotBackPair n` is *definitionally* a reshape-conjugate of `cnotGate.onRight`, the form that
makes `placedCnotBackPair_realized` a one-line transport of the gadget's induced operation.  It is
**the same evolution** as the library's canonical wire-addressed controlled-`NOT`,
`Evolution.placedMcNot {n} (n+1)` (control wire `n`, target wire `n+1` — the `|S| = 1` case of the
multiply-controlled-`NOT` placement `Evolution.placedMcNot` of Exercise 4.29).  The identity is
proved below by computational-basis extensionality (`Evolution.ext_qubitBasis`): both sides act on
`⨂ᵢ |c i⟩` by flipping wire `n+1` iff wire `n` is set.  So the two are **not** two unreconciled
placed-`CNOT` idioms — the gadget realizes the *canonical* `placedMcNot`
(`placedMcNot_gateTeleport_realized`), and its computational-basis truth table
`placedMcNot_evolvePure_qubitBasis` transfers to `placedCnotBackPair`, making the "genuine `CNOT`"
reading of `placedCnotBackPair_evolvePure_congr` a canonical fact rather than a statement about the
bespoke reshape. -/
theorem placedCnotBackPair_eq_placedMcNot (n : ℕ) :
    placedCnotBackPair n = Evolution.placedMcNot {Fin.natAdd n 0} (Fin.natAdd n 1)
      (by simp only [Finset.mem_singleton]; apply Fin.ne_of_val_ne;
          simp only [Fin.val_natAdd]; omega) := by
  have hcast : ∀ i : Fin n, (Fin.castAdd 2 i) ≠ (Fin.natAdd n 1 : Fin (n + 2)) := fun i => by
    apply Fin.ne_of_val_ne; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
  have hnat : (Fin.natAdd n 0 : Fin (n + 2)) ≠ Fin.natAdd n 1 := by
    apply Fin.ne_of_val_ne; simp only [Fin.val_natAdd]; omega
  apply Evolution.ext_qubitBasis
  intro c
  rw [Evolution.placedMcNot_evolvePure_qubitBasis]
  have hin : (PureState.piTensor fun i => qubitBasis (c i))
      = PureState.congr (qubitBackPairReshape n).symm
          ((PureState.piTensor (fun i : Fin n => qubitBasis (c (Fin.castAdd 2 i)))).tmul
            ((qubitBasis (c (Fin.natAdd n 0))).tmul (qubitBasis (c (Fin.natAdd n 1))))) := by
    rw [qubitBackPairReshape_symm_congr]
    congr 1
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left]
    · rw [Fin.append_right]
      have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      rcases hj with rfl | rfl <;> simp
  rw [hin]
  erw [placedCnotBackPair_evolvePure_congr]
  rw [cnotGate_evolvePure_qubitBasis]
  erw [qubitBackPairReshape_symm_congr]
  congr 1
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left]
    congr 1
    unfold Concrete.mcNot
    rw [Function.update_of_ne (hcast i)]
  · rw [Fin.append_right]
    have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hj with rfl | rfl
    · rw [Matrix.cons_val_zero]
      congr 1
      unfold Concrete.mcNot
      rw [Function.update_of_ne hnat]
    · rw [Matrix.cons_val_one, Matrix.cons_val_zero]
      congr 1
      unfold Concrete.mcNot
      rw [Function.update_self]
      congr 1
      exact (Concrete.ctrlBit_singleton (Fin.natAdd n 0) c).symm

/-- **The resource set realizes the canonical wire-addressed `CNOT`**
`Evolution.placedMcNot {n} (n+1)` (Nielsen & Chuang, Problem 4.6): the `placedMcNot` form of
`placedCnotBackPair_realized`, obtained by rewriting its output gate through
`placedCnotBackPair_eq_placedMcNot`.  So the gate-teleportation
gadget on the last two wires induces the *canonical* controlled-`NOT` (control wire `n`, target
`n+1`) — not merely a bespoke reshape-conjugate — for every input `φ` and every outcome `(p, q)`.
This is the register-level "resource realizes the `CNOT` gate" fact used for the
`n`-wire universality assembly, with the gate taken as the canonical `placedMcNot`. -/
theorem placedMcNot_gateTeleport_realized (n : ℕ) (φ : PureState (qubit.tensorPow (n + 2)))
    (p q : Fin 2 × Fin 2)
    (hp : (bellPairsMeasurement.onRight (qubit.tensorPow n)).bornProb
        (gateTeleportRegisterGenRef (qubit.tensorPow n)
          (PureState.congr (qubitBackPairReshape n) φ)).toState (p, q) ≠ 0) :
    (((((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).onRight
                (qubit.tensorPow n)).evolve
          ((bellPairsMeasurement.onRight (qubit.tensorPow n)).postMeasurement
            (gateTeleportRegisterGenRef (qubit.tensorPow n)
              (PureState.congr (qubitBackPairReshape n) φ)).toState (p, q) hp)).congr
        (QSystem.Iso.leftComm (qubit.tensorPow n) ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))
          (qubit ⊗ qubit))).reducedRight.congr (qubitBackPairReshape n).symm
      = ((Evolution.placedMcNot {Fin.natAdd n 0} (Fin.natAdd n 1)
          (by simp only [Finset.mem_singleton]; apply Fin.ne_of_val_ne;
              simp only [Fin.val_natAdd]; omega)).evolvePure φ).toState := by
  rw [← placedCnotBackPair_eq_placedMcNot]
  exact placedCnotBackPair_realized n φ p q hp

/-!
### `CNOT` on an arbitrary wire pair (completing the `CNOT`-generator realization)

`placedMcNot_gateTeleport_realized` above realizes the `CNOT` gate on the *fixed back pair*
`(n, n+1)` of the register `qubit ^⊗ₛ (n+2)`.  Faithful universality decomposes an arbitrary
unitary into `CNOT`s addressed to *every* ordered wire pair `(i, j)` together with single-qubit
gates (N&C's given, `{CNOT, single-qubit}` universal), so the resource must realize `CNOT` on an
**arbitrary** control/target pair `i ≠ j`, not merely the back pair.

This is obtained from the back-pair realization by **conjugating with a wire-permutation reshape**
`qubit.tensorPowCongr σ`, where `σ := Concrete.cnotPairGatherPerm n i j` (the pure `Fin`-permutation
in `Concrete/CnotPairGatherPermutation.lean`) gathers the back-pair positions
`(n, n+1)` onto `(i, j)`.  Conjugation is a `State.congr` / `PureState.congr` transport (a
register relabelling — free bookkeeping, not a resource gate), so no extra physical operation
enters: the gadget is applied to the physical wires `(i, j)` directly, and addressing them is only a
choice of which qubits to Bell-measure and which four to prepare `|χ⟩` on.  The conjugated back-pair
gate is the library's **canonical** wire-addressed `CNOT` `Evolution.placedMcNot {i} j`
(`placedCnotPair_eq_placedMcNot`, via the basis-action transport
`Evolution.congr_tensorPowCongr_evolvePure_qubitBasis`), so `cnotWiresRealized` realizes the
*canonical* `CNOT` on `(i, j)` — not a bespoke reshape idiom.  `CnotWiresRealized` packages this as
the reusable witness the `n`-wire universality assembly consumes for its `CNOT`-on-two-wires
generator, exactly as `CnotResourceRealized` did for the two-qubit instance.
-/

/-- **The back-pair `CNOT`, conjugated onto wires `(i, j)`, is the canonical `CNOT` there** (Nielsen
& Chuang, Problem 4.6): transporting `placedCnotBackPair n` (`CNOT` on the back pair) through the
wire-permutation reshape `qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j)` yields the
library's canonical wire-addressed `CNOT` `Evolution.placedMcNot {i} j` — control `i`, target `j`.

Proved on the computational basis (`Evolution.ext_qubitBasis`): the conjugated gate's basis action
is computed by `Evolution.congr_tensorPowCongr_evolvePure_qubitBasis` (feeding the back pair's
action `mcNot {n} (n+1)` from `placedCnotBackPair_eq_placedMcNot`), giving
`mcNot {n} (n+1) (c ∘ σ) (σ⁻¹ ·)`; and `placedMcNot {i} j` acts by `mcNot {i} j c`.  These agree
wire-by-wire: `σ` conjugates the classical `mcNot` (control `n ↦ i`, target `n+1 ↦ j`), a two-case
check on whether the output wire is the target. -/
theorem placedCnotPair_eq_placedMcNot (n : ℕ) (i j : Fin (n + 2)) (hij : i ≠ j) :
    Evolution.congr (qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j))
        (placedCnotBackPair n)
      = Evolution.placedMcNot {i} j (by rw [Finset.mem_singleton]; exact Ne.symm hij) := by
  have hsa : Concrete.cnotPairGatherPerm n i j (Fin.natAdd n 0) = i :=
    Concrete.cnotPairGatherPerm_apply_control n i j hij
  have hsb : Concrete.cnotPairGatherPerm n i j (Fin.natAdd n 1) = j :=
    Concrete.cnotPairGatherPerm_apply_target n i j
  have hbase : ∀ d : Fin (n + 2) → Fin 2,
      (placedCnotBackPair n).evolvePure (PureState.piTensor fun x => qubitBasis (d x))
        = PureState.piTensor fun x =>
            qubitBasis (Concrete.mcNot {Fin.natAdd n 0} (Fin.natAdd n 1) d x) := fun d => by
    rw [placedCnotBackPair_eq_placedMcNot]
    exact Evolution.placedMcNot_evolvePure_qubitBasis _ _ _ d
  apply Evolution.ext_qubitBasis
  intro c
  rw [Evolution.congr_tensorPowCongr_evolvePure_qubitBasis (placedCnotBackPair n)
      (Concrete.cnotPairGatherPerm n i j) (Concrete.mcNot {Fin.natAdd n 0} (Fin.natAdd n 1)) hbase,
    Evolution.placedMcNot_evolvePure_qubitBasis]
  congr 1
  funext k
  congr 1
  set σ := Concrete.cnotPairGatherPerm n i j
  by_cases hk : σ.symm k = Fin.natAdd n 1
  · have hkj : k = j := by rw [← hsb, ← hk, Equiv.apply_symm_apply]
    rw [hk, Concrete.mcNot_apply_self, hkj, Concrete.mcNot_apply_self,
      Concrete.ctrlBit_singleton, Concrete.ctrlBit_singleton, hsb, hsa]
  · have hkj : k ≠ j := fun h => hk (by rw [h, ← hsb, Equiv.symm_apply_apply])
    rw [Concrete.mcNot_apply_of_ne _ _ _ hk, Concrete.mcNot_apply_of_ne _ _ _ hkj,
      Equiv.apply_symm_apply]

/-- **The resource set realizes `CNOT` on _every_ ordered wire pair**, as a proposition (Nielsen &
Chuang, Problem 4.6): for every control/target pair `i ≠ j` of the `(n+2)`-wire register, every
input pure state `ψ` (possibly entangling the two `CNOT` wires with the other `n`), and every
Bell-measurement outcome `(p, q)`, the gate-teleportation gadget *addressed to wires `(i, j)`* — the
back-pair gadget conjugated by the addressing reshape
`qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j)` — sends the register to
`(Evolution.placedMcNot {i} j).evolvePure ψ`, i.e. the canonical `CNOT` on `(i, j)` applied to `ψ`,
independent of the outcome.

This is the register analogue of the two-qubit `CnotResourceRealized`; it is the witness that the
`n`-wire universality assembly carries in its `CNOT`-on-two-wires generator constructor, so that the
`n`-wire reduction genuinely routes through the gate-teleportation realization. -/
def CnotWiresRealized (n : ℕ) : Prop :=
  ∀ (i j : Fin (n + 2)) (hij : i ≠ j) (ψ : PureState (qubit.tensorPow (n + 2)))
    (p q : Fin 2 × Fin 2)
    (hp : (bellPairsMeasurement.onRight (qubit.tensorPow n)).bornProb
        (gateTeleportRegisterGenRef (qubit.tensorPow n)
          (PureState.congr (qubitBackPairReshape n)
            (PureState.congr (qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j)).symm
              ψ))).toState
        (p, q) ≠ 0),
    ((((((gateTeleportCorrection p q).onRight ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))).onRight
                  (qubit.tensorPow n)).evolve
            ((bellPairsMeasurement.onRight (qubit.tensorPow n)).postMeasurement
              (gateTeleportRegisterGenRef (qubit.tensorPow n)
                (PureState.congr (qubitBackPairReshape n)
                  (PureState.congr (qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j)).symm
                    ψ))).toState (p, q) hp)).congr
          (QSystem.Iso.leftComm (qubit.tensorPow n) ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit))
            (qubit ⊗ qubit))).reducedRight.congr (qubitBackPairReshape n).symm).congr
        (qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j))
      = ((Evolution.placedMcNot {i} j (by rw [Finset.mem_singleton]; exact Ne.symm hij)).evolvePure
          ψ).toState

/-- **The resource set realizes `CNOT` on every ordered wire pair** — `CnotWiresRealized n` holds,
witnessed by the arbitrary-wire gate-teleportation gadget (Nielsen & Chuang, Problem 4.6).  Proved
by transporting `placedCnotBackPair_realized` (the back-pair realization) through the addressing
reshape `qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j)`: the outer `State.congr` commutes
with `toState`/`evolvePure` (`PureState.congr_toState`, `Evolution.congr_evolvePure_congr`), the
conjugated back-pair `CNOT` is the canonical `placedMcNot {i} j` (`placedCnotPair_eq_placedMcNot`),
and the addressing reshape cancels its inverse on the input (`PureState.congr_congr_symm`).  This is
the register-level "resource realizes the `CNOT` gate" fact used for the `n`-wire
universality assembly. -/
theorem cnotWiresRealized (n : ℕ) : CnotWiresRealized n := by
  intro i j hij ψ p q hp
  rw [placedCnotBackPair_realized n
      (PureState.congr (qubit.tensorPowCongr (Concrete.cnotPairGatherPerm n i j)).symm ψ) p q hp,
    ← PureState.congr_toState, ← Evolution.congr_evolvePure_congr,
    placedCnotPair_eq_placedMcNot n i j hij, PureState.congr_congr_symm]

/-!
### The `n`-wire universality assembly (Nielsen & Chuang, Problem 4.6 — the headline)

The pieces above realize, on the register `qubit ^⊗ₛ (n+2)`, every gate of the family
`{canonical CNOT on any ordered wire pair, single-qubit unitary on any wire}`: the
`CNOT`-on-two-wires generator by the register-embedded gate-teleportation gadget
(`cnotWiresRealized`, correct even when those two wires are entangled with the other `n`), each
single-qubit generator by direct application (resource #1).  Feeding this into the Gottesman–Chuang
reduction `Evolution.realizes_of_universal` (`Core/UniversalityReduction.lean`) with N&C's given —
that `{CNOT, single-qubit}` is universal on the register (`hUniversal`) — yields the headline: *the
measurement resource set implements every evolution of `qubit ^⊗ₛ (n+2)`*, for every `n`.  That is
universality on every register with at least two wires — the full content of Problem 4.6.  This is
the register generalisation of the two-qubit instance
(`ResourceImplements` / `measurementResourceSet_realizes_of_universal`) assembled above.
-/

/-- **A single-qubit unitary placed on wire `i`** of the register `qubit ^⊗ₛ (n+2)` (Nielsen &
Chuang, Problem 4.6): `U` acting on wire `i`, the identity on the other `n+1` wires.  Built by
placing `U` on the head wire (`U.onLeft`, i.e. `U ⊗ 1`, through the head-peel reshape
`QSystem.tensorPowSuccHead`) and relabelling the head wire to wire `i` by the wire-swap reshape
`qubit.tensorPowCongr (Equiv.swap 0 i)` — a register relabelling (free wire addressing, not a
resource gate), so no extra physical operation enters.  This is the `(n+2)`-wire register analogue
of the two-qubit `IsResourceGenerator`'s `U.onLeft` / `U.onRight` single-qubit gates; a
single-qubit unitary on any wire is in resource #1, so it is realized directly (the
`ResourceImplementsWires.singleQubitWire` constructor). -/
noncomputable def placedSingleQubit (n : ℕ) (i : Fin (n + 2)) (U : Evolution qubit) :
    Evolution (qubit.tensorPow (n + 2)) :=
  Evolution.congr (qubit.tensorPowCongr (Equiv.swap 0 i))
    (Evolution.congr (QSystem.tensorPowSuccHead qubit (n + 1)).symm
      (U.onLeft (qubit.tensorPow (n + 1))))

/-- **The measurement resource set's generating family on the `(n+2)`-wire register** (Nielsen &
Chuang, Problem 4.6): the library's canonical wire-addressed `CNOT` `Evolution.placedMcNot {i} j` on
every ordered control/target pair `i ≠ j`, and every single-qubit unitary on every wire
(`placedSingleQubit n i U`).  These are exactly the resource set's gates in their `(n+2)`-wire
action — the shared single-qubit unitaries (resource #1) and the `CNOT`s realized by the
Bell-measurement / four-qubit-prep resources via gate teleportation.  This is the `IsGenerator`
family fed to `Evolution.realizes_of_universal`; N&C's premise that `{CNOT, single-qubit}` is
universal is the statement that this family generates every `(n+2)`-wire evolution.  It is the
register generalisation of the two-qubit `IsResourceGenerator`. -/
def IsResourceGeneratorWires (n : ℕ) (E : Evolution (qubit.tensorPow (n + 2))) : Prop :=
  (∃ (i j : Fin (n + 2)) (hij : i ≠ j),
      E = Evolution.placedMcNot {i} j (by rw [Finset.mem_singleton]; exact Ne.symm hij)) ∨
    (∃ (i : Fin (n + 2)) (U : Evolution qubit), E = placedSingleQubit n i U)

/-- **The gates the measurement resource set implements on the `(n+2)`-wire register.**  Built by
composition from single-qubit unitaries on any wire applied directly (resource #1 — the
`singleQubitWire` constructor, `placedSingleQubit n i U`) and the canonical `CNOT` on any ordered
wire pair realized by gate teleportation (the `cnotWire` constructor).  The `cnotWire` constructor
**carries** the realization witness `CnotWiresRealized n`: a `CNOT` on wires `(i, j)` is admitted
only together with a proof that the register-embedded gate-teleportation gadget actually induces its
operation (correct even when those two wires are entangled with the other `n`), so
`ResourceImplementsWires` is not the vacuous "closure of an abstract gate set" but genuinely tracks
resource realizability — the universality conclusion built from it routes through the
gate-teleportation gadget (`cnotWiresRealized`), not a bare assertion that `CNOT` is free.

Together with `one`/`comp` (the identity is free; realizable gates compose), these are exactly the
`Realizes 1` / `hcomp` / `hgen` obligations of `Evolution.realizes_of_universal`.  It is the
register generalisation of the two-qubit `ResourceImplements`. -/
inductive ResourceImplementsWires (n : ℕ) : Evolution (qubit.tensorPow (n + 2)) → Prop
  /-- The identity is realized (do nothing). -/
  | one : ResourceImplementsWires n 1
  /-- Realizable gates compose (run one protocol after the other). -/
  | comp {U V : Evolution (qubit.tensorPow (n + 2))} :
      ResourceImplementsWires n U → ResourceImplementsWires n V →
      ResourceImplementsWires n (U.comp V)
  /-- A single-qubit unitary on any wire `i`, `placedSingleQubit n i U`, is realized directly
  (resource #1). -/
  | singleQubitWire (i : Fin (n + 2)) (U : Evolution qubit) :
      ResourceImplementsWires n (placedSingleQubit n i U)
  /-- The canonical `CNOT` on any ordered wire pair `(i, j)` is realized by gate teleportation,
  witnessed by `CnotWiresRealized n`. -/
  | cnotWire (i j : Fin (n + 2)) (hij : i ≠ j) (h : CnotWiresRealized n) :
      ResourceImplementsWires n
        (Evolution.placedMcNot {i} j (by rw [Finset.mem_singleton]; exact Ne.symm hij))

/-- **Every resource generator is resource-realized.**  Case analysis on
`IsResourceGeneratorWires`: the canonical `CNOT` on `(i, j)` by the register-embedded
gate-teleportation gadget (`cnotWiresRealized`), each single-qubit generator by direct application.
This is the `hgen` obligation of `Evolution.realizes_of_universal`. -/
theorem ResourceImplementsWires.of_generator {n : ℕ} {E : Evolution (qubit.tensorPow (n + 2))}
    (hE : IsResourceGeneratorWires n E) : ResourceImplementsWires n E := by
  rcases hE with ⟨i, j, hij, rfl⟩ | ⟨i, U, rfl⟩
  · exact .cnotWire i j hij (cnotWiresRealized n)
  · exact .singleQubitWire i U

/-- **The measurement resource set is universal on every register** (Nielsen & Chuang, Problem 4.6 —
the Gottesman–Chuang reduction, register-general headline).  Assuming N&C's given that the gate
family `{CNOT, single-qubit}` is universal on the `(n+2)`-wire register — every evolution of
`qubit ^⊗ₛ (n+2)` is a finite ordered product of `IsResourceGeneratorWires` gates (`hUniversal`) —
the resource set of *single-qubit unitaries, Bell-basis measurement, and four-qubit state
preparation* implements **every** evolution `E` of that register (`ResourceImplementsWires n E`),
for **every** `n`.

This is `Evolution.realizes_of_universal` instantiated with `Realizes := ResourceImplementsWires n`
and `IsGenerator := IsResourceGeneratorWires n`: the identity and composition closure are the
`ResourceImplementsWires.one`/`.comp` constructors, and every gate of the generating family is
realized by `ResourceImplementsWires.of_generator` — the single genuinely-new step being the
`CNOT` on two wires, realized by the register-embedded gate-teleportation gadget
(`cnotWiresRealized`, correct even when those wires are entangled with the rest of the register).
So the reduction "add the missing `CNOT` ⟹ universal" is here a proved theorem, on every register,
whose proof genuinely consumes the gate-teleportation realization.

**Scope.** The statement ranges over every register `qubit ^⊗ₛ (n+2)` with at least two wires —
where the problem's content lives, since a `0`- or `1`-wire register needs no `CNOT` and its
universality is the single-qubit resource alone.  N&C's `{CNOT, single-qubit}` universality is taken
as the explicit hypothesis `hUniversal`, exactly the problem's stated premise ("Controlled-`NOT`
gates and single qubit gates form a universal set of quantum logic gates"); discharging it from the
library's exact gate decomposition (`Concrete.exists_isToffoliOrSingleQubit_list_prod_eq`, lifted to
evolutions) is an orthogonal task. -/
theorem measurementResourceSetWires_realizes_of_universal (n : ℕ)
    (hUniversal : ∀ E : Evolution (qubit.tensorPow (n + 2)),
      ∃ L : List (Evolution (qubit.tensorPow (n + 2))),
        (∀ V ∈ L, IsResourceGeneratorWires n V) ∧ L.prod = E)
    (E : Evolution (qubit.tensorPow (n + 2))) : ResourceImplementsWires n E :=
  Evolution.realizes_of_universal ResourceImplementsWires.one
    (fun hU hV => hU.comp hV) (fun _ hV => ResourceImplementsWires.of_generator hV) hUniversal E

end AxQM
