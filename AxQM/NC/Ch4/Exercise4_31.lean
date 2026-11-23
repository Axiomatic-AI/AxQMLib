/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CnotPauliYPropagation
import AxQM.Postulates.API.CnotRotationCommutation

/-!
# Nielsen & Chuang, Exercise 4.31 (More circuit identities)

*(N&C p. 185.)*

Prove eight CNOT-conjugation circuit identities (CX1C=X1X2, etc.).

`C = CNOT`, the single-qubit Pauli gates, and the single-qubit rotation gates are closed-system
evolutions (Postulate 5 / `Evolution`); each identity is an equality of gates on `qubit ⊗ qubit`,
built from `cnotGate`, `pauliXGate`, `pauliYGate`, `pauliZGate`, `rotZGate`, `rotXGate` and
`Evolution.onLeft`/`onRight`/`comp`.

## The formalisation (all eight identities, eqs 4.32–4.39)

Qubit 1 is the *left* factor and qubit 2 the *right* factor of `qubit ⊗ qubit`, so `P₁ = P.onLeft`
(`= P ⊗ 1`) and `P₂ = P.onRight` (`= 1 ⊗ P`).  `C·P·C` is the gate composition
`cnotGate.comp (P.comp cnotGate)` (operator product `C·P·C`, applied right-to-left).

The six **Pauli conjugations** (eqs 4.32–4.37):

* `cnotGate_conj_pauliXGate_onLeft` — eq. (4.32): `C·X₁·C = X₁·X₂`.
* `cnotGate_conj_pauliYGate_onLeft` — eq. (4.33): `C·Y₁·C = Y₁·X₂`.
* `cnotGate_conj_pauliZGate_onLeft` — eq. (4.34): `C·Z₁·C = Z₁`.
* `cnotGate_conj_pauliXGate_onRight` — eq. (4.35): `C·X₂·C = X₂`.
* `cnotGate_conj_pauliYGate_onRight` — eq. (4.36): `C·Y₂·C = Z₁·Y₂`.
* `cnotGate_conj_pauliZGate_onRight` — eq. (4.37): `C·Z₂·C = Z₁·Z₂`.

The two **rotation commutations** (eqs 4.38–4.39), in N&C's `R·C = C·R` orientation — a rotation on
the axis `CNOT` leaves invariant commutes with `CNOT`:

* `rotZGate_onLeft_comm_cnotGate` — eq. (4.38): `R_{z,1}(θ)·C = C·R_{z,1}(θ)`.
* `rotXGate_onRight_comm_cnotGate` — eq. (4.39): `R_{x,2}(θ)·C = C·R_{x,2}(θ)`.

## Design notes

* **Statement shape (fidelity).**  N&C writes each identity as a genuine *operator equality*
  `CP₁C = Q` (not an action on selected states, not up to phase).  We render it as the corresponding
  equality of `Evolution`s `cnotGate.comp (P.comp cnotGate) = Q`, faithful to the textbook's
  operator product `C·P·C`.
* **Proof route (uniform).**  Each conjugation identity is a single application of the reusable
  `Evolution`-monoid lemma `Evolution.comp_comp_self_of_comm` (conjugation by an involution:
  `C·P = Q·C` and `C·C = 1` give `C·P·C = Q`, since `C·P·C = (Q·C)·C = Q·(C·C) = Q`) to a Clifford
  *commutation* rule `C·P = P'·C` (the propagation rules
  `cnotGate_comp_pauli{X,Y,Z}Gate_on{Left,Right}` of
  `AxQM/Postulates/API/CnotPauli{,Y}Propagation.lean`) and the CNOT involution
  `cnotGate_comp_cnotGate` (`C·C = 1`).  The `X`/`Z` propagation rules are in
  `AxQM/Postulates/API/CnotPauliPropagation.lean` (Problem 4.6); the `Y` propagation rules, the
  involution, and `Evolution.comp_comp_self_of_comm` are in
  `AxQM/Postulates/API/CnotPauliYPropagation.lean`, which also defines `pauliYGate`, the Pauli-`Y`
  gate.  The mathematical content lives in the propagation rules.
* **Rotation commutations (4.38)–(4.39).**  Unlike the six Pauli conjugations, these are plain
  *commutations* `R·C = C·R`: a rotation on the axis `CNOT` leaves invariant slides straight past
  `CNOT`.  Each is the `.symm` of a reusable commutation rule
  `cnotGate_comp_rot{Z,X}Gate_on{Left,Right}` of `AxQM/Postulates/API/CnotRotationCommutation.lean`
  (continuous rotations through `CNOT`, not discrete Paulis being conjugated).  There
  `R_z` on the control commutes because it is diagonal (an eigen-action on each control label), and
  `R_x` on the target commutes with the `X` of `C(X) = CNOT` because it is a function of `X`.
-/

noncomputable section

namespace AxQM

/-- **N&C eq. (4.32):** `C·X₁·C = X₁·X₂`.  Conjugating an `X` on the control by `CNOT` copies it to
an `X` on the target as well (the control bit that `X₁` flips is XORed onto the target).  Derived
from the commutation rule `cnotGate_comp_pauliXGate_onLeft` and the involution
`cnotGate_comp_cnotGate`. -/
theorem cnotGate_conj_pauliXGate_onLeft :
    cnotGate.comp ((pauliXGate.onLeft qubit).comp cnotGate)
      = (pauliXGate.onLeft qubit).comp (pauliXGate.onRight qubit) :=
  Evolution.comp_comp_self_of_comm cnotGate_comp_pauliXGate_onLeft cnotGate_comp_cnotGate

/-- **N&C eq. (4.33):** `C·Y₁·C = Y₁·X₂`.  Conjugating a `Y` on the control by `CNOT` leaves a `Y`
on the control and copies an `X` to the target (`Y₁ = iX₁Z₁`: the `X₁` copies, the `Z₁` commutes).
Derived from `cnotGate_comp_pauliYGate_onLeft` and `cnotGate_comp_cnotGate`. -/
theorem cnotGate_conj_pauliYGate_onLeft :
    cnotGate.comp ((pauliYGate.onLeft qubit).comp cnotGate)
      = (pauliYGate.onLeft qubit).comp (pauliXGate.onRight qubit) :=
  Evolution.comp_comp_self_of_comm cnotGate_comp_pauliYGate_onLeft cnotGate_comp_cnotGate

/-- **N&C eq. (4.34):** `C·Z₁·C = Z₁`.  A `Z` on the control commutes with `CNOT`, so conjugation
leaves it unchanged.  Derived from `cnotGate_comp_pauliZGate_onLeft` and the involution. -/
theorem cnotGate_conj_pauliZGate_onLeft :
    cnotGate.comp ((pauliZGate.onLeft qubit).comp cnotGate) = pauliZGate.onLeft qubit :=
  Evolution.comp_comp_self_of_comm cnotGate_comp_pauliZGate_onLeft cnotGate_comp_cnotGate

/-- **N&C eq. (4.35):** `C·X₂·C = X₂`.  An `X` on the target commutes with `CNOT`, so conjugation
leaves it unchanged.  Derived from `cnotGate_comp_pauliXGate_onRight` and the involution. -/
theorem cnotGate_conj_pauliXGate_onRight :
    cnotGate.comp ((pauliXGate.onRight qubit).comp cnotGate) = pauliXGate.onRight qubit :=
  Evolution.comp_comp_self_of_comm cnotGate_comp_pauliXGate_onRight cnotGate_comp_cnotGate

/-- **N&C eq. (4.36):** `C·Y₂·C = Z₁·Y₂`.  Conjugating a `Y` on the target by `CNOT` leaves a `Y` on
the target and copies a `Z` back to the control (`Y₂ = iX₂Z₂`: the `Z₂` copies back, the `X₂` stays,
the phase rides along).  Derived from `cnotGate_comp_pauliYGate_onRight` and the involution. -/
theorem cnotGate_conj_pauliYGate_onRight :
    cnotGate.comp ((pauliYGate.onRight qubit).comp cnotGate)
      = (pauliZGate.onLeft qubit).comp (pauliYGate.onRight qubit) :=
  Evolution.comp_comp_self_of_comm cnotGate_comp_pauliYGate_onRight cnotGate_comp_cnotGate

/-- **N&C eq. (4.37):** `C·Z₂·C = Z₁·Z₂`.  Conjugating a `Z` on the target by `CNOT` copies it back
to a `Z` on the control as well.  Derived from `cnotGate_comp_pauliZGate_onRight` and
`cnotGate_comp_cnotGate`. -/
theorem cnotGate_conj_pauliZGate_onRight :
    cnotGate.comp ((pauliZGate.onRight qubit).comp cnotGate)
      = (pauliZGate.onLeft qubit).comp (pauliZGate.onRight qubit) :=
  Evolution.comp_comp_self_of_comm cnotGate_comp_pauliZGate_onRight cnotGate_comp_cnotGate

/-- **N&C eq. (4.38):** `R_{z,1}(θ)·C = C·R_{z,1}(θ)`.  A `z`-rotation on the control (qubit 1)
commutes with `CNOT`: `CNOT` reads the control only through its computational-basis label, which
`R_z(θ)` merely rephases, so the two gates slide past each other.  The `.symm` of the reusable
commutation rule `cnotGate_comp_rotZGate_onLeft`. -/
theorem rotZGate_onLeft_comm_cnotGate (θ : ℝ) :
    ((rotZGate θ).onLeft qubit).comp cnotGate
      = cnotGate.comp ((rotZGate θ).onLeft qubit) :=
  (cnotGate_comp_rotZGate_onLeft θ).symm

/-- **N&C eq. (4.39):** `R_{x,2}(θ)·C = C·R_{x,2}(θ)`.  An `x`-rotation on the target (qubit 2)
commutes with `CNOT`: `CNOT = C(X)` acts on the target by `X`, and `R_x(θ)` is a function of `X`, so
the two commute there.  The `.symm` of the reusable commutation rule
`cnotGate_comp_rotXGate_onRight`. -/
theorem rotXGate_onRight_comm_cnotGate (θ : ℝ) :
    ((rotXGate θ).onRight qubit).comp cnotGate
      = cnotGate.comp ((rotXGate θ).onRight qubit) :=
  (cnotGate_comp_rotXGate_onRight θ).symm

end AxQM
