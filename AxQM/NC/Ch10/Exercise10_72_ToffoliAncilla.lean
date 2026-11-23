/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ToffoliAncilla
import AxQM.Postulates.API.PauliGateEigenstate
import AxQM.Postulates.API.PlusPlusZeroStabilizer
import AxQM.Postulates.API.RelativePhaseToffoli
import AxQM.Postulates.API.GateCommute
import AxQM.Postulates.API.OneBitTeleportation
import AxQM.Postulates.API.CnotPauliYPropagation
import AxQM.NC.Ch10.Exercise10_67

/-!
# Nielsen & Chuang, Exercise 10.72 (fault-tolerant Toffoli ancilla state)

*(N&C §10.6.3, p. 491.)*

Show how to fault-tolerantly prepare the Toffoli ancilla state
`|Θ_T⟩ = ½ (|000⟩ + |010⟩ + |100⟩ + |111⟩)` (10.121) from the dotted box of Exercise 10.68.

## What is formalised, and where

The **state itself and its (non-fault-tolerant) preparation circuit** are the object shared with
Exercise 10.68, formalised in `AxQM/Postulates/API/ToffoliAncilla.lean` and reused here:

* `toffoliAncilla` — the ancilla `|Θ_T⟩`, defined as the output of the elementary preparation
  circuit `toffoliAncillaPrep = C²(X)·H₁·H₂` applied to `|000⟩`;
* `toffoliAncilla_vec` — its explicit value `|Θ_T⟩ = ½(|000⟩ + |010⟩ + |100⟩ + |111⟩)`, i.e.
  N&C eq. (10.121): the circuit really does prepare the target state;
* `toffoliAncilla_prep_ketPlus` — the reduction `|Θ_T⟩ = C²(X)(|+⟩|+⟩|0⟩)` (the two Hadamards turn
  the control wires into `|+⟩`).

This file contributes the exercise's remaining, N&C-specific content: **the stabilizer generators of
`|Θ_T⟩`** (the exercise's own hint), the theorem that the ancilla is their common `+1` eigenstate,
and — establishing that the three operators genuinely form a *stabilizer group* — that they pairwise
**commute** (so they can be measured jointly) and are each **involutions** (self-inverse unitaries,
hence Hermitian `±1`-outcome observables). These are exactly the operators a fault-tolerant
*verification* of the ancilla measures: the fully fault-tolerant procedure of §10.6.3 (repeated
verified `cat`-state-style preparation, majority vote, error probability `O(p²)`) rests on a
cost/error model the library does not express, so it is a discussion rather than a single theorem;
its formalisable kernel is the prepared state, the circuit that prepares it, and the abelian
stabilizer group that certifies it — all present here.

## The stabilizer generators (the hint)

`|Θ_T⟩ = C²(X)(|+⟩|+⟩|0⟩)`, and `|+⟩|+⟩|0⟩` is a joint `+1` eigenstate of the Pauli operators
`X₁, X₂, Z₃`. Transporting those three generators through the preparation unitary `C²(X)` gives the
stabilizer generators of `|Θ_T⟩`, `gᵢ = C²(X)·Pᵢ·C²(X)†`. Because the Toffoli lies *outside* the
normalizer of the Pauli group (N&C §10.5.3), these conjugates are **not** Pauli operators but
Pauli × controlled-Clifford products — precisely the conjugation rules of Exercise 10.67:

* `toffoliAncillaStabX1 = X₁ · CNOT₂₃` (from `X₁`, Exercise 10.67 identity (a));
* `toffoliAncillaStabX2 = X₂ · CNOT₁₃` (from `X₂`, the symmetric sibling proved here, reusing the
  shared long-range gate `cnotFirstThirdGate`);
* `toffoliAncillaStabZ3 = Z₃ · CZ₁₂` (from `Z₃`, Exercise 10.67 identity (b)).

Each `gᵢ` is proved to fix `|Θ_T⟩` (`toffoliAncillaStab…_hasEigenstate_one`), to be a Hermitian
involution `gᵢ² = 1` (`toffoliAncillaStab…_comp_self`), and to commute with the other two
(`toffoliAncillaStab…_comm`) — so the three generate an **abelian group of commuting Hermitian
involutions**, the stabilizer group of `|Θ_T⟩`. The exercise's suggestion to "give the stabilizer
generators" is exactly this list, and jointly measuring the three is how the fault-tolerant
verification checks the prepared ancilla.

**Completeness/uniqueness.** The stabilizer group also *pins* the state: `|Θ_T⟩` is its *unique*
common `+1` eigenstate up to phase, so measuring `g₁, g₂, g₃` and post-selecting the all-`+1`
outcome prepares exactly `|Θ_T⟩` and nothing else. This is the completeness half of the
verification, proved here as `toffoliAncilla_eq_of_stabilized` (the analogue of Exercise 10.73's
`steaneLogicalZero_eq_of_stabilized_inCode`): via the Toffoli self-inverse
(`toffoliGate_comp_toffoliGate`), any common `+1` eigenstate of `g₁, g₂, g₃` maps under `C²(X)` to a
common `+1` eigenstate of `X₁, X₂, Z₃`, whose unique such state up to phase is `|+⟩|+⟩|0⟩`
(`qubitPlusPlusZero_eq_of_stabilized`, established here from the single-qubit `X`/`Z`
eigenprojectors `|+⟩⟨+|`, `|0⟩⟨0|` whose tensor product is the rank-one projector `|Θ⟩⟨Θ|`).
Together with the
`_hasEigenstate_one` soundness lemmas this makes "measure the three generators, fix the signs"
prepare exactly the ancilla — the full mathematical content of the exercise's stabilizer hint.

## Design notes

* **Statement shape.** "`gᵢ` stabilizes `|Θ_T⟩`" is rendered as `gᵢ.HasEigenstate 1 toffoliAncilla`
  (`gᵢ|Θ_T⟩ = |Θ_T⟩`), the grounded surrogate for a unitary's eigenvalue equation (cf.
  `izzObservable_hasEigenstate_one_catBlockState`). Every statement is phrased with the gates
  `toffoliGate`, `pauliXGate`/`pauliZGate` (via `onLeft`/`onRight`), `cnotGate`,
  `controlledZLeftGate`, `cnotFirstThirdGate` and `Evolution.comp`, and the `PureState`
  `toffoliAncilla`.
* **Proof.** A single engine `toffoliAncilla_hasEigenstate_one_of_propagates`: if `gᵢ` propagates
  through the Toffoli as `gᵢ·C²(X) = C²(X)·Pᵢ` and `Pᵢ` fixes `|+⟩|+⟩|0⟩`, then
  `gᵢ|Θ_T⟩ = gᵢ·C²(X)(|+⟩|+⟩|0⟩) = C²(X)·Pᵢ(|+⟩|+⟩|0⟩) = C²(X)(|+⟩|+⟩|0⟩) = |Θ_T⟩`. The propagation
  identities for `g₁`, `g₃` are Exercise 10.67's `toffoliGate_comp_pauliXGate_control_propagates` /
  `toffoliGate_comp_pauliZGate_target_propagates`; for `g₂` it is the symmetric X-on-control-2 rule
  `toffoliGate_comp_pauliXGate_controlTwo_propagates`, proved here on the eight basis states, using
  the shared long-range gate `cnotFirstThirdGate = C(1⊗X)` (control qubit 1, target qubit 3) and its
  truth table `cnotFirstThirdGate_evolvePure` from `Postulates/API/RelativePhaseToffoli`. That
  `Pᵢ` fixes `|+⟩|+⟩|0⟩` reduces via `onLeft`/`onRight` to `X|+⟩ = |+⟩` and `Z|0⟩ = |0⟩`
  (`pauliXGate_hasEigenstate_one_qubitPlus`, `pauliZGate_hasEigenstate_one_qubitBasisZero`).
* **Reuse.** The generators are given in the *explicit* Pauli × controlled form (the measurable
  operators), reusing Exercise 10.67's Toffoli-propagation vocabulary rather than the opaque
  conjugates `C²(X)·Pᵢ·C²(X)†`; the control-1 / target-3 CNOT is the shared `cnotFirstThirdGate`
  (from the Ex 4.26 relative-phase Toffoli), not a new gate.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **X-on-control-2 propagation through the Toffoli** (the symmetric sibling of Exercise 10.67's
identity (a)): `C²(X)·X₂ = (X₂·CNOT₁₃)·C²(X)` on `qubit ⊗ (qubit ⊗ qubit)`, where
`X₂ = (pauliXGate.onLeft qubit).onRight qubit` and `CNOT₁₃ = cnotFirstThirdGate` (the shared
long-range CNOT `C(1 ⊗ X)`, control qubit 1 / target qubit 3, of
`Postulates/API/RelativePhaseToffoli`). Flipping control 2 before the Toffoli copies onto the
target conditioned on control 1 (a `CNOT` from qubit 1 to qubit 3), so pushing `X₂` past the
Toffoli leaves that `CNOT₁₃` behind. A permutation identity, verified on the eight
computational-basis states using `cnotFirstThirdGate_evolvePure` (`CNOT₁₃` acts on the target by
`X^{q₁}`). -/
theorem toffoliGate_comp_pauliXGate_controlTwo_propagates :
    toffoliGate.comp ((pauliXGate.onLeft qubit).onRight qubit)
      = (((pauliXGate.onLeft qubit).onRight qubit).comp cnotFirstThirdGate).comp
          toffoliGate := by
  apply threeQubit_evolution_ext
  intro q1 q2 q3
  simp only [Evolution.evolvePure_comp, Evolution.onRight_evolvePure, Evolution.onLeft_evolvePure,
    pauliXGate_evolvePure_qubitBasis, toffoliGate_evolvePure_qubitBasis,
    cnotFirstThirdGate_evolvePure]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;>
    simp [targetXPow, pauliXGate_evolvePure_qubitBasis, Evolution.id_evolvePure]

/-- **Stabilizer propagation engine.** If a gate `g` propagates through the Toffoli as
`g·C²(X) = C²(X)·P` and the Pauli `P` fixes `|+⟩|+⟩|0⟩`, then `g` stabilizes the Toffoli ancilla:
`g|Θ_T⟩ = |Θ_T⟩`. This is the whole content of "conjugate the `|+⟩|+⟩|0⟩` stabilizer `P` through the
preparation unitary `C²(X)`": `g·C²(X)(|+⟩|+⟩|0⟩) = C²(X)·P(|+⟩|+⟩|0⟩) = C²(X)(|+⟩|+⟩|0⟩)`. -/
theorem toffoliAncilla_hasEigenstate_one_of_propagates
    {g P : Evolution (qubit ⊗ (qubit ⊗ qubit))}
    (hprop : g.comp toffoliGate = toffoliGate.comp P)
    (hP : P.evolvePure (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0))
        = qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)) :
    g.HasEigenstate 1 toffoliAncilla :=
  Evolution.hasEigenstate_one_of_evolvePure_eq <| by
    rw [toffoliAncilla_prep_ketPlus, ← Evolution.evolvePure_comp, hprop,
      Evolution.evolvePure_comp, hP]

/-- **`X₁` fixes `|+⟩|+⟩|0⟩`:** `X` on the first qubit leaves the `|+⟩` control alone. -/
theorem pauliXGate_onLeft_evolvePure_plusplus0 :
    (pauliXGate.onLeft (qubit ⊗ qubit)).evolvePure (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0))
      = qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0) := by
  rw [Evolution.onLeft_evolvePure, (pauliXGate_hasEigenstate_one_qubitPlus).evolvePure_eq]

/-- **`X₂` fixes `|+⟩|+⟩|0⟩`:** `X` on the second qubit leaves the `|+⟩` control alone. -/
theorem pauliXGate_onLeft_onRight_evolvePure_plusplus0 :
    ((pauliXGate.onLeft qubit).onRight qubit).evolvePure (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0))
      = qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0) := by
  rw [Evolution.onRight_evolvePure, Evolution.onLeft_evolvePure,
    (pauliXGate_hasEigenstate_one_qubitPlus).evolvePure_eq]

/-- **`Z₃` fixes `|+⟩|+⟩|0⟩`:** `Z` on the third qubit leaves the `|0⟩` target alone. -/
theorem pauliZGate_onRight_onRight_evolvePure_plusplus0 :
    ((pauliZGate.onRight qubit).onRight qubit).evolvePure (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0))
      = qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0) := by
  rw [Evolution.onRight_evolvePure, Evolution.onRight_evolvePure,
    (pauliZGate_hasEigenstate_one_qubitBasisZero).evolvePure_eq]

/-- **First stabilizer generator** of the Toffoli ancilla, `g₁ = X₁ · CNOT₂₃`
(`X₁ = pauliXGate.onLeft (qubit ⊗ qubit)`, `CNOT₂₃ = cnotGate.onRight qubit`): the Toffoli conjugate
`C²(X)·X₁·C²(X)†` of the `|+⟩|+⟩|0⟩` stabilizer `X₁`, in explicit Pauli × controlled-`X` form
(Exercise 10.67, identity (a)). -/
def toffoliAncillaStabX1 : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (pauliXGate.onLeft (qubit ⊗ qubit)).comp (cnotGate.onRight qubit)

/-- **Second stabilizer generator** of the Toffoli ancilla, `g₂ = X₂ · CNOT₁₃`
(`X₂ = (pauliXGate.onLeft qubit).onRight qubit`, `CNOT₁₃ = cnotFirstThirdGate`): the Toffoli
conjugate `C²(X)·X₂·C²(X)†` of the `|+⟩|+⟩|0⟩` stabilizer `X₂`, the control-1↔control-2 mirror
image of `g₁`. -/
def toffoliAncillaStabX2 : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  ((pauliXGate.onLeft qubit).onRight qubit).comp cnotFirstThirdGate

/-- **Third stabilizer generator** of the Toffoli ancilla, `g₃ = Z₃ · CZ₁₂`
(`Z₃ = (pauliZGate.onRight qubit).onRight qubit`, `CZ₁₂ = controlledZLeftGate`): the Toffoli
conjugate `C²(X)·Z₃·C²(X)†` of the `|+⟩|+⟩|0⟩` stabilizer `Z₃`, in explicit Pauli × controlled-`Z`
form (Exercise 10.67, identity (b)). -/
def toffoliAncillaStabZ3 : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  ((pauliZGate.onRight qubit).onRight qubit).comp controlledZLeftGate

/-- **`g₁ = X₁·CNOT₂₃` stabilizes the Toffoli ancilla:** `g₁|Θ_T⟩ = |Θ_T⟩`. -/
theorem toffoliAncillaStabX1_hasEigenstate_one :
    toffoliAncillaStabX1.HasEigenstate 1 toffoliAncilla :=
  toffoliAncilla_hasEigenstate_one_of_propagates
    toffoliGate_comp_pauliXGate_control_propagates.symm pauliXGate_onLeft_evolvePure_plusplus0

/-- **`g₂ = X₂·CNOT₁₃` stabilizes the Toffoli ancilla:** `g₂|Θ_T⟩ = |Θ_T⟩`. -/
theorem toffoliAncillaStabX2_hasEigenstate_one :
    toffoliAncillaStabX2.HasEigenstate 1 toffoliAncilla :=
  toffoliAncilla_hasEigenstate_one_of_propagates
    toffoliGate_comp_pauliXGate_controlTwo_propagates.symm
    pauliXGate_onLeft_onRight_evolvePure_plusplus0

/-- **`g₃ = Z₃·CZ₁₂` stabilizes the Toffoli ancilla:** `g₃|Θ_T⟩ = |Θ_T⟩`. -/
theorem toffoliAncillaStabZ3_hasEigenstate_one :
    toffoliAncillaStabZ3.HasEigenstate 1 toffoliAncilla :=
  toffoliAncilla_hasEigenstate_one_of_propagates
    toffoliGate_comp_pauliZGate_target_propagates.symm
    pauliZGate_onRight_onRight_evolvePure_plusplus0

/-! ### The stabilizer group structure: commuting Hermitian involutions

The three generators do not merely fix `|Θ_T⟩`; together they form an **abelian group of commuting
Hermitian involutions** — they pairwise commute (so they can be measured jointly, the whole point of
a stabilizer verification) and each is a Hermitian involution (a genuine `±1`-outcome measurement).
Both facts are inherited from the `|+⟩|+⟩|0⟩` stabilizers `X₁, X₂, Z₃` through the Clifford
conjugation by the preparation unitary `C²(X)`: because the Toffoli is its own inverse
(`toffoliGate_comp_toffoliGate`), `gᵢ = C²(X)·Pᵢ·C²(X)`, so `gᵢ·gⱼ = C²(X)·(Pᵢ·Pⱼ)·C²(X)` and
`gᵢ² = C²(X)·Pᵢ²·C²(X)` — commutativity and the involution property transport verbatim from the
disjoint single-qubit Paulis via the general `Evolution`-conjugation engines
`Evolution.comm_of_conj_comm` / `Evolution.comp_self_of_conj_comp_self` (beside
`Evolution.comp_comp_self_of_comm`). The *completeness* of this group — that `|Θ_T⟩` is its unique
common `+1` eigenstate up to phase, which pins the verification to exactly `|Θ_T⟩` — is established
below as `toffoliAncilla_eq_of_stabilized` (see the module docstring). -/

/-- **`g₁` and `g₂` commute:** `g₁·g₂ = g₂·g₁`. The two `X`-type generators are the Toffoli
conjugates of `X₁` and `X₂`, disjoint single-qubit Paulis on the two control wires, which commute
(`Evolution.onLeft_comm_onRight`); the conjugates therefore commute, via the general conjugation
engine `Evolution.comm_of_conj_comm` and the Toffoli self-inverse `toffoliGate_comp_toffoliGate`. -/
theorem toffoliAncillaStabX1_comp_toffoliAncillaStabX2_comm :
    toffoliAncillaStabX1.comp toffoliAncillaStabX2
      = toffoliAncillaStabX2.comp toffoliAncillaStabX1 :=
  Evolution.comm_of_conj_comm toffoliGate_comp_toffoliGate
    toffoliGate_comp_pauliXGate_control_propagates.symm
    toffoliGate_comp_pauliXGate_controlTwo_propagates.symm
    (Evolution.onLeft_comm_onRight pauliXGate (pauliXGate.onLeft qubit))

/-- **`g₁` and `g₃` commute:** `g₁·g₃ = g₃·g₁`. The Toffoli conjugates of `X₁` and `Z₃`, disjoint
Paulis on qubits 1 and 3. -/
theorem toffoliAncillaStabX1_comp_toffoliAncillaStabZ3_comm :
    toffoliAncillaStabX1.comp toffoliAncillaStabZ3
      = toffoliAncillaStabZ3.comp toffoliAncillaStabX1 :=
  Evolution.comm_of_conj_comm toffoliGate_comp_toffoliGate
    toffoliGate_comp_pauliXGate_control_propagates.symm
    toffoliGate_comp_pauliZGate_target_propagates.symm
    (Evolution.onLeft_comm_onRight pauliXGate (pauliZGate.onRight qubit))

/-- **`g₂` and `g₃` commute:** `g₂·g₃ = g₃·g₂`. The Toffoli conjugates of `X₂` and `Z₃`, disjoint
Paulis on qubits 2 and 3. Both sit on the right factor, so their commutation is the single-qubit
`onLeft_comm_onRight` (X on qubit 2, Z on qubit 3) transported across qubit 1 by `onRight_comp`. -/
theorem toffoliAncillaStabX2_comp_toffoliAncillaStabZ3_comm :
    toffoliAncillaStabX2.comp toffoliAncillaStabZ3
      = toffoliAncillaStabZ3.comp toffoliAncillaStabX2 :=
  Evolution.comm_of_conj_comm toffoliGate_comp_toffoliGate
    toffoliGate_comp_pauliXGate_controlTwo_propagates.symm
    toffoliGate_comp_pauliZGate_target_propagates.symm
    (by rw [Evolution.onRight_comp, Evolution.onLeft_comm_onRight, ← Evolution.onRight_comp])

/-- **`g₁` is an involution:** `g₁·g₁ = 1`. The Toffoli conjugate of the involution `X₁`; a
self-inverse unitary, hence a Hermitian `±1` observable — a genuine measurable stabilizer. Via the
general conjugation engine `Evolution.comp_self_of_conj_comp_self`. -/
theorem toffoliAncillaStabX1_comp_self :
    toffoliAncillaStabX1.comp toffoliAncillaStabX1 = Evolution.id :=
  Evolution.comp_self_of_conj_comp_self toffoliGate_comp_toffoliGate
    toffoliGate_comp_pauliXGate_control_propagates.symm
    (by rw [Evolution.onLeft_comp, pauliXGate_comp_pauliXGate, Evolution.id_onLeft])

/-- **`g₂` is an involution:** `g₂·g₂ = 1`. The Toffoli conjugate of the involution `X₂`. -/
theorem toffoliAncillaStabX2_comp_self :
    toffoliAncillaStabX2.comp toffoliAncillaStabX2 = Evolution.id :=
  Evolution.comp_self_of_conj_comp_self toffoliGate_comp_toffoliGate
    toffoliGate_comp_pauliXGate_controlTwo_propagates.symm
    (by rw [Evolution.onRight_comp, Evolution.onLeft_comp, pauliXGate_comp_pauliXGate,
      Evolution.id_onLeft, Evolution.id_onRight])

/-- **`g₃` is an involution:** `g₃·g₃ = 1`. The Toffoli conjugate of the involution `Z₃`. -/
theorem toffoliAncillaStabZ3_comp_self :
    toffoliAncillaStabZ3.comp toffoliAncillaStabZ3 = Evolution.id :=
  Evolution.comp_self_of_conj_comp_self toffoliGate_comp_toffoliGate
    toffoliGate_comp_pauliZGate_target_propagates.symm
    (by rw [Evolution.onRight_comp, Evolution.onRight_comp, pauliZGate_comp_pauliZGate,
      Evolution.id_onRight, Evolution.id_onRight])

/-! ### Completeness: the stabilizer group pins the ancilla

The three generators do not merely fix `|Θ_T⟩`; jointly they **determine** it. Measuring
`g₁, g₂, g₃` and post-selecting the all-`+1` outcome prepares *exactly* `|Θ_T⟩` (up to a global
phase) and nothing else — the *completeness* half of the stabilizer verification, the analogue of
Exercise 10.73's `steaneLogicalZero_eq_of_stabilized_inCode`.

The route is the same Clifford conjugation that produced the generators. Because `C²(X)` is its own
inverse (`toffoliGate_comp_toffoliGate`), any common `+1` eigenstate `ψ` of `gᵢ = C²(X)·Pᵢ·C²(X)`
maps under `C²(X)` to a common `+1` eigenstate `C²(X)ψ` of the disjoint single-qubit Paulis
`X₁, X₂, Z₃`; and the unique such state up to phase is `|+⟩|+⟩|0⟩`, because the joint `+1`
eigenprojector `|+⟩⟨+| ⊗ |+⟩⟨+| ⊗ |0⟩⟨0|` is the rank-one projector `|+⟩|+⟩|0⟩⟨+|⟨+|⟨0|`.
Transporting back through `C²(X)` gives `ψ = C²(X)(|+⟩|+⟩|0⟩) = |Θ_T⟩`, up to a global phase.

The uniqueness of the `|+⟩|+⟩|0⟩` common `+1` eigenstate of `X₁, X₂, Z₃` is the
lemma `qubitPlusPlusZero_eq_of_stabilized` (`AxQM/Postulates/API/PlusPlusZeroStabilizer.lean`); the
bridge below transports it through `C²(X)` to the Toffoli ancilla. -/

/-- **The stabilizer group pins the Toffoli ancilla (completeness).** Any pure state `ψ` fixed by
all three stabilizer generators `g₁ = X₁·CNOT₂₃`, `g₂ = X₂·CNOT₁₃`, `g₃ = Z₃·CZ₁₂` equals the
Toffoli ancilla `|Θ_T⟩` up to a global phase (`ψ.toState = toffoliAncilla.toState`). Together with
`toffoliAncillaStab…_hasEigenstate_one` (soundness — `|Θ_T⟩` *is* stabilized) this is N&C's
guarantee that measuring the three generators and post-selecting the all-`+1` outcome prepares
*exactly*
`|Θ_T⟩`. Proof: `C²(X)` is its own inverse (`toffoliGate_comp_toffoliGate`), so from
`gᵢ·C²(X) = C²(X)·Pᵢ` (Exercise 10.67's `toffoli…_propagates`) each `Pᵢ ∈ {X₁, X₂, Z₃}` fixes
`C²(X)ψ`; by `qubitPlusPlusZero_eq_of_stabilized` that state is `|+⟩|+⟩|0⟩` up to phase, and
`toffoliAncilla = C²(X)(|+⟩|+⟩|0⟩)` (`toffoliAncilla_prep_ketPlus`), so applying `C²(X)` (phase
invisible to the density operator, `toState_evolvePure`) gives `ψ = |Θ_T⟩` up to phase. -/
theorem toffoliAncilla_eq_of_stabilized (ψ : PureState (qubit ⊗ (qubit ⊗ qubit)))
    (h1 : toffoliAncillaStabX1.HasEigenstate 1 ψ)
    (h2 : toffoliAncillaStabX2.HasEigenstate 1 ψ)
    (h3 : toffoliAncillaStabZ3.HasEigenstate 1 ψ) :
    ψ.toState = toffoliAncilla.toState := by
  -- `C²(X)` is its own inverse on pure states.
  have hCinv : ∀ x : PureState (qubit ⊗ (qubit ⊗ qubit)),
      toffoliGate.evolvePure (toffoliGate.evolvePure x) = x := fun x => by
    rw [← Evolution.evolvePure_comp, toffoliGate_comp_toffoliGate, Evolution.id_evolvePure]
  -- Transport a stabilizer condition through `C²(X)`: if `gᵢ` fixes `ψ` and `C²(X)·Pᵢ = gᵢ·C²(X)`,
  -- then `Pᵢ` fixes `C²(X)ψ`.
  have key : ∀ {g P : Evolution (qubit ⊗ (qubit ⊗ qubit))},
      toffoliGate.comp P = g.comp toffoliGate → g.evolvePure ψ = ψ →
      P.HasEigenstate 1 (toffoliGate.evolvePure ψ) := by
    intro g P hprop hg
    apply Evolution.hasEigenstate_one_of_evolvePure_eq
    have step : toffoliGate.evolvePure (P.evolvePure (toffoliGate.evolvePure ψ)) = ψ := by
      rw [← Evolution.evolvePure_comp, hprop, Evolution.evolvePure_comp, hCinv, hg]
    calc P.evolvePure (toffoliGate.evolvePure ψ)
        = toffoliGate.evolvePure
            (toffoliGate.evolvePure (P.evolvePure (toffoliGate.evolvePure ψ))) := (hCinv _).symm
      _ = toffoliGate.evolvePure ψ := by rw [step]
  have hX1φ := key toffoliGate_comp_pauliXGate_control_propagates h1.evolvePure_eq
  have hX2φ := key toffoliGate_comp_pauliXGate_controlTwo_propagates h2.evolvePure_eq
  have hZ3φ := key toffoliGate_comp_pauliZGate_target_propagates h3.evolvePure_eq
  have hφΘ := qubitPlusPlusZero_eq_of_stabilized (toffoliGate.evolvePure ψ) hX1φ hX2φ hZ3φ
  calc ψ.toState
      = (toffoliGate.evolvePure (toffoliGate.evolvePure ψ)).toState := by rw [hCinv]
    _ = toffoliGate.evolve (toffoliGate.evolvePure ψ).toState := toState_evolvePure _ _
    _ = toffoliGate.evolve (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)).toState := by rw [hφΘ]
    _ = (toffoliGate.evolvePure (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0))).toState :=
          (toState_evolvePure _ _).symm
    _ = toffoliAncilla.toState := by rw [toffoliAncilla_prep_ketPlus]

end AxQM
