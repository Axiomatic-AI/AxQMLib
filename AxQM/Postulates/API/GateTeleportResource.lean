/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellBasis
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Postulates.API.Associator

/-!
# AxQM.Postulates.API — the gate-teleportation resource state

The **four-qubit entangled resource state** of Nielsen & Chuang **Problem 4.6** ("Universality
with prior entanglement"): the Gottesman–Chuang state obtained by applying a `CNOT` to one half
of each of two Bell pairs.  This is resource #3 of Problem 4.6 — a specific value of "the ability
to prepare arbitrary four-qubit entangled states" — and, together with the Bell-basis measurement
and single-qubit Pauli corrections of `AxQM/Postulates/API/Teleportation.lean`, it implements a
`CNOT` by gate teleportation (see `AxQM/Postulates/API/GateTeleportMeasurement.lean`), so
{single-qubit unitaries, Bell-basis measurement, four-qubit state prep} is a universal set.

## The construction

Label the four qubits `a_in, a_out, b_out, b_in`.  Two Bell pairs `|Φ⁺⟩_{a_in a_out}` and
`|Φ⁺⟩_{b_out b_in}` are prepared — the literal `bellPhiPlus ⊗ bellPhiPlus`, the second pair read
in the order `b_out, b_in` — and a `CNOT` with control `a_out` and target `b_out` (the two
*output* halves, which will carry the teleported result) is applied.  The result is the resource
`|χ⟩ = cnotGateTeleportResource`.

Because the `CNOT` couples one qubit from each pair, its qubits `a_out, b_out` sit in the *middle*
of the register `a_in a_out b_out b_in`: adjacent, but not a tensor factor of the Bell-pair
grouping `(a_in a_out) ⊗ (b_out b_in)`.  We therefore re-associate to `a_in ⊗ ((a_out b_out) ⊗
b_in)` — a pure regrouping of the same four qubits (`gateTeleportReshape`, built from the
associators only) — apply `CNOT` to the now-grouped middle pair via
`Evolution.onRight (Evolution.onLeft cnotGate _) _`, then re-associate back.

**Faithfulness is manifest in the definition** and **normalisation is free**:
`cnotGateTeleportResource` is literally `cnotGate.evolvePure` — the genuine `CNOT` `Evolution`
(Postulate 5) — of `bellPhiPlus ⊗ bellPhiPlus` (transported through the structural regrouping), so
it *is* "`CNOT` applied to two Bell pairs"; and, being a value of `PureState`
(Postulate 1) built by norm-preserving transport (`PureState.congr`) and unitary evolution
(`Evolution.evolvePure`), it is automatically a normalised preparable four-qubit entangled state.

## What is formalised

* `gateTeleportReshape` — the regrouping `(q⊗q)⊗(q⊗q) ≃ₛ q ⊗ ((q⊗q)⊗q)` bringing the two middle
  qubits `(a_out, b_out)` together, built from `QSystem.assoc` and the general
  `QSystem.Iso.tmul` (the `⊗` of the transport backbone, which is in
  `AxQM/Postulates/API/Associator.lean`).
* `cnotMiddleGate` — the placed `CNOT` `1 ⊗ (CNOT ⊗ 1)` on the regrouped register.
* `cnotGateTeleportResource` — the **resource state** `|χ⟩`: `CNOT` applied to the two output
  halves of `bellPhiPlus ⊗ bellPhiPlus`.

The explicit computational-basis form of `|χ⟩` (`½ Σ_{i,j} (|i⟩⊗|i⟩) ⊗ (|i⊕j⟩⊗|j⟩)`, the input
labels copied to the outputs and mapped by the `CNOT` truth table) is
`cnotGateTeleportResource_vec` in `AxQM/Postulates/API/GateTeleportResourceExplicit.lean`.

## Design notes

* **Grouping choice.**  Keeping the two Bell pairs contiguous makes the base the *literal*
  `bellPhiPlus ⊗ bellPhiPlus` (so faithfulness needs no separate proof and normalisation is free);
  the price is the middle-qubit reshape, a pure re-association (no braiding), built from
  `QSystem.assoc` and one `QSystem.Iso.tmul` lift.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-! ### The middle-qubit regrouping and the resource state -/

/-- The structural regrouping `(q⊗q)⊗(q⊗q) ≃ₛ q ⊗ ((q⊗q)⊗q)` of the four-qubit register
`a_in a_out b_out b_in`: re-associate so the two middle qubits `(a_out, b_out)` form a tensor
factor.  Built from the associators only — `(assoc a_in a_out (b_out⊗b_in)).symm`, then the
associator `assoc a_out b_out b_in` lifted into the right factor by a `QSystem.Iso.tmul` with
`refl`. -/
def gateTeleportReshape :
    ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) ≃ₛ (qubit ⊗ ((qubit ⊗ qubit) ⊗ qubit)) :=
  (QSystem.assoc qubit qubit (qubit ⊗ qubit)).symm.trans
    (QSystem.Iso.tmul (QSystem.Iso.refl qubit) (QSystem.assoc qubit qubit qubit))

/-- `CNOT` on the middle two qubits `(a_out, b_out)` of the regrouped register
`a_in ⊗ ((a_out b_out) ⊗ b_in)`: `1 ⊗ (CNOT ⊗ 1)`, i.e. identity on `a_in` and `b_in`, `cnotGate`
on `(a_out, b_out)`. -/
def cnotMiddleGate : Evolution (qubit ⊗ ((qubit ⊗ qubit) ⊗ qubit)) :=
  Evolution.onRight (Evolution.onLeft cnotGate qubit) qubit

/-- The **four-qubit gate-teleportation resource state** `|χ⟩` of Nielsen & Chuang Problem 4.6
(resource #3): `CNOT` applied to the two output halves of two Bell pairs.  Defined as the two Bell
pairs `bellPhiPlus ⊗ bellPhiPlus` regrouped by `gateTeleportReshape`, evolved by `cnotMiddleGate`
(the genuine `CNOT` `Evolution`, Postulate 5, on the middle pair), and regrouped back.  Being a
value of `PureState` (Postulate 1) built by norm-preserving transport and unitary evolution, it is
a normalised preparable four-qubit entangled state; being `cnotGate.evolvePure` of two Bell pairs
it faithfully realises "`CNOT` applied to two Bell pairs". -/
def cnotGateTeleportResource : PureState ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)) :=
  PureState.congr gateTeleportReshape.symm
    (cnotMiddleGate.evolvePure (PureState.congr gateTeleportReshape (bellPhiPlus.tmul bellPhiPlus)))

end AxQM
