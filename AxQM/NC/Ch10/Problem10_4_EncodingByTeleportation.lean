/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EncodingTeleportation

/-!
# Nielsen & Chuang, Problem 10.4 (Encoding by teleportation)

*(N&C p. 496.)*

Construct a circuit encoding an unknown qubit into a stabilizer code by teleportation.

## The reduction, and what is verifiable

Parts (1)–(3) describe the standard §1.3.7 teleportation protocol with **Bob's half of the Bell
pair replaced by the encoder's image in the code**: the resource is the *partially encoded* state
`(|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2 = (I ⊗ E)|Φ⁺⟩` (part (1)), a Bell measurement is performed on `|ψ⟩` and
the unencoded qubit (part (2)), and outcome `(x, y)` leaves the code register in the *encoded*
byproduct-corrected state `E(X^y Z^x |ψ⟩)`, which the logical Pauli byproduct undoes to give
`|ψ_L⟩` (part (3)).  Stripped of the circuit vocabulary, this whole mechanism is one linear-algebra
identity — the **encoding analogue of the teleportation identity** — and that is the
**verifiable mathematical core**, formalised as a complete theorem
(`encodingTeleportation_identity`).

Everything else Problem 10.4 asks for is a claim about a *circuit* and an *error model* the
postulate framework has no vocabulary to express, so it is recorded here as the physics annotation
in addition to the identity (exactly as `NC/Ch4/Problem4_6` records "universal" on top of *its*
teleportation identity):

* **"fault-tolerantly construct … by measuring stabilizer generators" (part 1)** and
  **"fault-tolerantly perform a Bell basis measurement" (part 2)** are *fault-tolerance*
  constructions; the library has no fault-tolerance / stabilizer-generator-measurement framework, so
  the formalisable shadow is that the resource `(|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2` is a genuine normalised
  **`PureState`** (`encoderBellState`) and the Bell measurement is the genuine projective
  `bellMeasurement` (from `Postulates/API/Teleportation`).
* **"Compute the probability of error of this circuit"** needs a physical error model over the
  underlying gates; there is no such model in the postulate framework, so no probability is
  computable, and this request cannot be formalised.
* **"modify the circuit to perform fault-tolerant decoding"** is the same construction run in
  reverse (`E†`), and cannot be formalised for the same fault-tolerance reason.

## The formalisation

The formalisation is in `AxQM/Postulates/API/EncodingTeleportation.lean`, in dependency order
(compare the other teleportation developments, `AxQM/Postulates/API/Teleportation.lean` and
`AxQM/Postulates/API/GateTeleportationIdentity.lean`):

* `AxQM.encoderBellUnnormVec E` / `AxQM.encoderBellVec E` — the unnormalised and
  normalised **partially encoded resource vector** `(|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2` on `qubit ⊗ C`
  (N&C eq. 10.126), for a code encoder `E`.
* `AxQM.encoderBellUnnormVec_inner_self` — its squared norm is `2` for an isometric
  encoder, whence:
* `AxQM.encoderBellState E` — the resource as a genuine **`PureState (qubit ⊗ C)`** for an
  isometric encoder `E : qubit.space →ₗᵢ[ℂ] C.space` (the logical embedding of a stabilizer code);
  `encoderBellState_vec` exposes its state vector.
* `AxQM.encodingTeleportation_identity` — the **encoding-teleportation identity**
  `|ψ⟩ ⊗ (|0⟩⊗|0_L⟩ + |1⟩⊗|1_L⟩)/√2 = ½ Σ_{x,y} |β_xy⟩ ⊗ E(X^y Z^x |ψ⟩)`: a Bell measurement of the
  first pair therefore lands the code register in the encoded corrected state `E(X^y Z^x |ψ⟩)`,
  undone by the logical Pauli byproduct — teleportation directly into the logical qubit.  Setting
  `C = qubit`, `E = id` (resource `|Φ⁺⟩`) recovers exactly `teleportation_identity`.
* `AxQM.encodingTeleportation_identity_qubitBasis` — its specialisation to a
  computational-basis input `|i⟩`.
-/
