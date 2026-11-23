/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TeleportationStabilizer

/-!
# Nielsen & Chuang, Exercise 10.42 (Teleportation in the stabilizer formalism)

*(N&C §10.5.4, p. 464.)*

Use stabilizer formalism to verify the circuit of Fig 1.13 teleports qubits.

## What is verified, and how

The circuit of Fig 1.13 teleports the data qubit (wire `0`) onto Bob's qubit (wire `2`) using the
shared Bell pair `(|00⟩+|11⟩)/√2` on wires `1, 2`.  Its unitary part is the **Clifford**
`U = H₀ · CNOT₀₁`; Alice then measures wires `0, 1` in the computational basis (outcomes
`m₀, m₁`) and Bob applies the byproduct `Z₂^{m₀} X₂^{m₁}`.  As the exercise flags, the stabilizer
formalism only handles a *stabilizer* input state, so it is **not** a description of teleporting a
fully general `|ψ⟩` (that state-vector verification, valid for every `|ψ⟩`, is
`AxQM.teleportation_identity` in `AxQM/Postulates/API/Teleportation.lean`).  What the stabilizer
formalism gives — the "understanding of the dynamics" the exercise asks for — is the **Heisenberg
(operator) picture**, and the verification is carried all the way to a machine-checked conclusion in
`AxQM/Concrete/TeleportationStabilizer.lean` (wires `0,1,2 = ` data, Alice's Bell half,
Bob):

1. **Clifford propagation table** — `U P U† = P'`, sign `+1` (the four
   `teleportStabCircuit_conj_logicalZ` / `_logicalX` / `_bellStabX` / `_bellStabZ`, all in
   `AxQM.Concrete`):
   `Z₀ ↦ X₀`, `X₀ ↦ Z₀X₁`, `X₁X₂ ↦ X₁X₂`, `Z₁Z₂ ↦ X₀Z₁Z₂`, an instance of the Clifford tracking
   backbone `CliffordCircuit.conj_pauliString` for `teleportStabCircuit = [had 0, cnot 0 1]`.

2. **Operator transfer onto Bob's wire** — on the post-Clifford stabilised subspace
   (`Concrete.mem_stabilizedSubspace` of the propagated Bell stabilisers)
   `AxQM.Concrete.logicalZ_acts_as_bellZ` gives `X₀ v = Z₁Z₂ v` and
   `AxQM.Concrete.logicalX_acts_as_bellX` gives `(Z₀X₁) v = (Z₀X₂) v`: the transported
   input logical operators act as operators supported on Bob's wire — the machine-checked sense in
   which the information moves to Bob.

3. **Corrected teleportation conclusion** — `AxQM.Concrete.teleportation_Zbasis` and
   `teleportation_Xbasis`.  For a stabilizer input (a `±1` eigenstate of `Z₀`, resp. `X₀`), the
   post-measurement state `w` is a `±1` eigenstate of the measured `Z` (outcome `(-1)^{m}`) and
   retains one surviving stabiliser (`(-1)^a Z₁Z₂`, resp. `(-1)^b Z₀X₂` — the Part-2 transferred
   operator).  The theorems prove that after the byproduct
   `teleportByproduct m₀ m₁ = Z₂^{m₀} X₂^{m₁}`, Bob's wire is stabilised by `(-1)^a Z₂` (resp.
   `(-1)^b X₂`) — i.e. Bob holds the *input* stabilizer state.  Carrying both logical operators of a
   qubit to Bob's implements the identity channel: the qubit teleports.

The §10.5.3 measurement collapse enters Part 3 as the eigenvalue hypotheses on `w` (the precise
content of "the post-measurement state is a `±1` eigenstate of the measured observable"); that
collapse is itself formalised at
`AxQM/Postulates/API/StabilizerMeasurement.lean` (`Observable.signMeasurement`,
`postMeasPlus_hasEigenstate`, …), whose post-measurement guarantees are exactly those hypotheses.

Compare Theorem 10.7 (`AxQM/NC/Ch10/Theorem10_7_GottesmanKnill.lean`), which uses the same
Clifford stabilizer tracking (`AxQM/Concrete/CliffordStabilizerTracking.lean`).
-/
