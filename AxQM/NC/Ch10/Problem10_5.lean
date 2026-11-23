/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EncodedCnotGateTeleportation

/-!
# Nielsen & Chuang, Problem 10.5 (fault-tolerant logical CNOT by gate teleportation)

*(N&C p. 496.)*

For [n,1] stabilizer code, explain a fault-tolerant CNOT between two logical qubits using FT
prep/measurement/normalizer gates.

## The construction

`CNOT` is a **normalizer (Clifford) gate**, but for a *general* `[n, 1]` stabilizer code it cannot
be applied transversally between two code blocks (transversal `CNOT` implements a logical `CNOT`
only for CSS codes, not for an arbitrary stabilizer code).  N&C's "History and further reading" (p.
499) points to Gottesman's review [Got97] for the construction that solves this Problem, and it is
the **gate-teleportation** protocol of Problem 4.6 (`AxQM/NC/Ch4/Problem4_6.lean`) — the
Gottesman–Chuang scheme that implements a physical `CNOT` from
`{single-qubit gates, Bell measurement, state preparation}`
(`cnotGateTeleportation_identity`) — run at the *logical* level:

1. **Fault-tolerant stabilizer state preparation.**  The four-block gate-teleportation resource
   `|χ_L⟩` (a logical `CNOT` pre-applied to two logical Bell pairs) is a *stabilizer state*, so it
   is prepared fault-tolerantly by measuring its stabilizer generators — no transversal `CNOT`
   between data blocks is ever applied.
2. **Fault-tolerant measurement of elements of the stabilizer.**  Teleporting the two logical qubits
   through `|χ_L⟩` needs two logical Bell measurements — measurements of the commuting logical Pauli
   operators `X_L X_L`, `Z_L Z_L`, elements of a stabilizer — done fault-tolerantly.
3. **Normalizer gates applied transversally.**  The teleportation byproducts are logical Pauli
   operators `X_L^y Z_L^x`; Pauli operators *are* transversal for any stabilizer code, so the
   corrections are normalizer gates applied transversally.

The net effect on the two logical qubits is a logical `CNOT`.

## The formalisation

The one **linear-algebra identity** to which the whole construction reduces is formalised — as a
complete theorem — in `AxQM/Postulates/API/EncodedCnotGateTeleportation.lean`
(imported here).  For a code encoder `E : qubit.space →ₗ[ℂ] C.space` (the logical embedding of one
encoded qubit into an `[n, 1]` stabilizer code):

* `AxQM.encodedCnotGateTeleportation_identity` — the **encoded (logical) CNOT
  gate-teleportation identity**: running the gate teleportation with the two *output* blocks encoded
  (apply `id ⊗ (E ⊗ E)` to the reshaped register `reshape ((q_A ⊗ q_B) ⊗ |χ⟩)`) gives
  `¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩) ⊗ (E ⊗ E)((C_A ⊗ C_B)(CNOT (q_A ⊗ q_B)))`, with
  `C_A = pauliByproduct (p.1+q.1) p.2`, `C_B = pauliByproduct q.1 (p.2+q.2)` the two single-qubit
  teleportation byproducts.  Bell-measuring the two pairs (outcomes `p, q`) therefore leaves the two
  *encoded output blocks* — two logical qubits — holding the encoded, byproduct-corrected `CNOT` of
  the data; the encoded byproducts `(E ∘ C ∘ E†)` are logical Paulis (transversal), and undoing them
  leaves the logical `CNOT` `(E ⊗ E)(CNOT(q_A ⊗ q_B))` on the two logical qubits.
* `AxQM.encodedCnotGateTeleportation_identity_qubitBasis` — its specialization to
  computational-basis input data `|a⟩, |b⟩`.

## Faithfulness

**What is formalised is exactly Problem 10.5's verifiable content, at full generality.** The
conclusion states that the two encoded output blocks hold `(E ⊗ E)(CNOT(q_A ⊗ q_B))` up to logical
Pauli byproducts.  For *any* two logical input states `|ψ_A⟩_L = E ψ_A`, `|ψ_B⟩_L = E ψ_B` in the
code, the gate-teleported logical `CNOT` acts on the encoded data by definition as
`CNOT_L(|ψ_A⟩_L ⊗ |ψ_B⟩_L) = (E ⊗ E)(CNOT(ψ_A ⊗ ψ_B))` — precisely the stated output — and by
linearity this covers every input in the code.  So the theorem's content **is** "a logical `CNOT`
between two logical qubits", with the correction structure (a pair of *logical* Pauli byproducts
fixed by the two measurement outcomes) captured exactly.  Carrying the input data as its physical
pre-image `q_A, q_B` rather than as a pre-encoded block is a modeling choice with no effect on the
stated logical content — not a weakening: the logical `CNOT` and the logical Pauli corrections on
the two output blocks, which are the whole verifiable claim, are present in full.  `E` is left an
arbitrary linear map (isometry — a genuine code embedding — is *stronger* than needed and would only
narrow the statement), so the identity holds for every encoder.

**What is annotation, not formalisation, and why.**  The *fault-tolerance* vocabulary of the
Problem — that the resource `|χ_L⟩` is a stabilizer state prepared by measuring stabilizer
generators, that the two logical Bell measurements are fault-tolerant measurements of stabilizer
elements, and that the Pauli corrections are normalizer gates applied *transversally* — has no
counterpart in the framework (as its siblings Problem 4.6 and Problem 10.4 already establish: the
framework models states, evolutions, measurements and composites, not a
fault-tolerance/transversality layer over a concrete code).  It is therefore recorded here as the
physics annotation rather than faked; building it out would require a transversality/normalizer and
stabilizer-measurement framework that the library does not contain.  The identity above is the
maximal framework-expressible core, and it is proved outright.
-/
