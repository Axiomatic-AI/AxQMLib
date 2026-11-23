/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GateTeleportationIdentity

/-!
# AxQM.Postulates.API — encoded (logical) CNOT gate teleportation

The verifiable mathematical core of **Nielsen & Chuang Problem 10.5**: a fault-tolerant `CNOT`
between two logical qubits of an `[n, 1]` stabilizer code, implemented by **gate teleportation** —
the same Gottesman–Chuang construction that Problem 4.6 uses to implement a *physical* `CNOT`
(`cnotGateTeleportation_identity`), now run so that the two output halves land *encoded in the
code*.  The two output code blocks are then genuine logical qubits carrying the logical `CNOT` of
the input data, up to a pair of **logical Pauli** byproducts — Pauli operators, hence correctable
by normalizer gates applied transversally.

## The construction, and what it reduces to

Gate teleportation implements `CNOT` on two data qubits `q_A, q_B` by teleporting them through the
four-qubit resource state `cnotGateTeleportResource` (`|χ⟩`, a `CNOT` pre-applied to the two
*output* halves of two Bell pairs): Bell-measuring the two pairs `(q_A, a_in)`, `(q_B, b_in)`
leaves the two output halves `a_out, b_out` holding `CNOT(q_A ⊗ q_B)` up to a pair of single-qubit
Pauli byproducts fixed by the two outcomes (`cnotGateTeleportation_identity`, the universality core
of Problem 4.6).  Problem 10.5 runs exactly this construction with the two output halves *encoded in
the code*: applying the encoder `E` to each of the two output blocks turns them into a pair of
logical qubits, and the resource `CNOT` on those blocks into a *logical* `CNOT` — `(E ⊗ E)` carries
`CNOT(q_A ⊗ q_B)` to the encoded two-qubit state, i.e. the logical `CNOT` of the two logical output
qubits.  The teleportation byproducts `E ∘ (X^y Z^x) `, being the encoder applied to Pauli
operators, are the *logical* Pauli byproducts `X_L^y Z_L^x` — normalizer (Pauli) operators, which
are transversal for any stabilizer code and undo the correction outcome-by-outcome.

* `encodedCnotGateTeleportation_identity` — the **encoded CNOT gate-teleportation identity**:
  applying `id ⊗ (E ⊗ E)` (encode the two output blocks, leave the two Bell-measured pairs alone)
  to the reshaped teleportation register `reshape ((q_A ⊗ q_B) ⊗ |χ⟩)` gives
  `¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩) ⊗ (E ⊗ E)((X^{y₁}Z^{x₁+x₂} ⊗ X^{y₁+y₂}Z^{x₂}) (CNOT (q_A ⊗ q_B)))`,
  `p = (x₁,y₁)`, `q = (x₂,y₂)`.  Bell-measuring the two pairs (outcomes `p, q`) therefore leaves the
  two *encoded* output blocks in `(E ⊗ E)((C_A ⊗ C_B)(CNOT(q_A ⊗ q_B)))` — the encoded, byproduct-
  corrected `CNOT` of the input data — which the logical Pauli correction
  `(E ∘ C_A ∘ E†) ⊗ (E ∘ C_B ∘ E†)` (applied transversally) undoes, leaving the logical `CNOT`
  `(E ⊗ E)(CNOT(q_A ⊗ q_B))` on the two logical qubits.
* `encodedCnotGateTeleportation_identity_qubitBasis` — its specialization to computational-basis
  input data `|a⟩, |b⟩`.

## Design notes

* **What is formalised.**  Problem 10.5 is a fault-tolerant *circuit
  construction* question; the library has no fault-tolerance vocabulary, so — exactly as
  for its sibling Problem 10.4 (encoding by teleportation, `encodingTeleportation_identity`) and for
  Problem 4.6 (universality by gate teleportation, `cnotGateTeleportation_identity`) — what is
  formalised is the one linear-algebra identity the whole construction reduces to, and everything
  fault-tolerance-specific is recorded as a comment in `AxQM/NC/Ch10/Problem10_5.lean`.  Genuinely
  outside what is formalised: *"fault-tolerant stabilizer state preparation"* (the
  resource `|χ_L⟩` prepared by measuring stabilizer generators — no stabilizer-measurement
  framework), *"fault-tolerant measurement of elements of the stabilizer"* (the logical Bell
  measurements — no fault-tolerance framework), *"normalizer gates applied transversally"* (the
  transversality of the Pauli corrections — no transversality framework).  These are noted but not
  formalised.  The formalised identity is faithful and fully general: its conclusion holds two
  logical
  qubits — the two encoded output blocks — in `(E ⊗ E)(CNOT(q_A ⊗ q_B))` up to a pair of logical
  Pauli byproducts, and for any logical inputs `|ψ_A⟩_L = E ψ_A`, `|ψ_B⟩_L = E ψ_B` the
  gate-teleported logical `CNOT` acts on the code by definition as
  `CNOT_L(|ψ_A⟩_L ⊗ |ψ_B⟩_L) = (E ⊗ E)(CNOT(ψ_A ⊗ ψ_B))` — precisely the stated output — so the
  claim *is* "a logical `CNOT` between two logical qubits", complete over all code inputs by
  linearity.  Carrying the input data as its physical pre-image `q_A, q_B` rather than a pre-encoded
  block is a modeling choice with no effect on the stated logical content, not a weakening; a
  fully pre-encoded protocol would re-route the whole six-qubit reshape through the code (reshape
  naturality under per-block encoding), part of the fault-tolerant *circuit* construction, which the
  library
  cannot express, and it would not sharpen the logical claim the identity already makes.
* **Why encoding the outputs needs no new machinery.**  The two output halves are the rightmost
  tensor factor of the reshaped register (`gateTeleportProtocolReshape` co-locates them there), so
  encoding them is a single `TensorProduct.map LinearMap.id (TensorProduct.map E E)` applied to the
  established identity `cnotGateTeleportation_identity`; pushing that linear map through the
  `¼ Σ_{p,q}` (`map_smul`, `map_sum`) and each pure tensor (`TensorProduct.map_tmul`, identity on
  the left factor) is the whole proof.  `E` is an arbitrary linear encoder (as in
  `encodingTeleportation_identity`); isometry is needed only to make the encoded blocks orthonormal
  logical qubits, which is noted in `AxQM/NC/Ch10/Problem10_5.lean` but not required by the core
  identity.
* **Related files.**  Compare `AxQM/Postulates/API/GateTeleportationIdentity.lean` and
  `AxQM/Postulates/API/EncodingTeleportation.lean`; the statement of Problem 10.5 is in
  `AxQM/NC/Ch10/Problem10_5.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {C : QSystem}

/-- **The encoded (logical) CNOT gate-teleportation identity** (Nielsen & Chuang Problem 10.5).
Running the Gottesman–Chuang `CNOT` gate teleportation (`cnotGateTeleportation_identity`) with the
two output halves *encoded in the code* — apply `id ⊗ (E ⊗ E)` to the reshaped teleportation
register, encoding the two output blocks and leaving the two Bell-measured pairs untouched — gives
`(id ⊗ (E ⊗ E)) (reshape ((q_A ⊗ q_B) ⊗ |χ⟩))`
`= ¼ Σ_{p,q} (|β_p⟩ ⊗ |β_q⟩) ⊗ (E ⊗ E)((X^{y₁}Z^{x₁+x₂} ⊗ X^{y₁+y₂}Z^{x₂}) (CNOT (q_A ⊗ q_B)))`,
`p = (x₁,y₁)`, `q = (x₂,y₂)`.  Bell-measuring the two pairs (outcomes `p, q`) leaves the two
*encoded* output blocks — two logical qubits — in `(E ⊗ E)((C_A ⊗ C_B)(CNOT(q_A ⊗ q_B)))`, the
encoded byproduct-corrected `CNOT` of the input data, with `C_A = pauliByproduct (p.1+q.1) p.2` and
`C_B = pauliByproduct q.1 (p.2+q.2)` the two teleportation corrections.  Since the byproducts are
Pauli operators, their encoded form `E ∘ C ∘ E†` is a *logical* Pauli (a normalizer gate, applied
transversally), and correcting it leaves the logical `CNOT` `(E ⊗ E)(CNOT(q_A ⊗ q_B))` on the two
logical qubits — the fault-tolerant `CNOT` between two logical qubits of Problem 10.5.

Proof: `id ⊗ (E ⊗ E)` is a linear map, so it distributes over the `¼ Σ_{p,q}`
(`map_smul`/`map_sum`) and over each pure tensor (`TensorProduct.map_tmul`), acting as the identity
on the left (Bell-pair) factor and as `E ⊗ E` on the right (output) factor. -/
theorem encodedCnotGateTeleportation_identity (E : qubit.space →ₗ[ℂ] C.space)
    (qA qB : qubit.space) :
    TensorProduct.map
        (LinearMap.id : ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space →ₗ[ℂ]
          ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space)
        (TensorProduct.map E E)
        (gateTeleportProtocolReshape.toIsometry
          ((qA ⊗ₜ[ℂ] qB) ⊗ₜ[ℂ] cnotGateTeleportResource.vec))
      = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
            TensorProduct.map E E
              ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
                (cnotGate.op (qA ⊗ₜ[ℂ] qB))) := by
  rw [cnotGateTeleportation_identity]
  -- Distribute the output-encoding map `id ⊗ (E ⊗ E)` over the `¼ Σ_{p,q}` and each pure tensor.
  -- `rw` cannot resolve the higher-order summand/hom class, so apply the distributors by
  -- unification (the idiom of `GateTeleportationIdentity.lean`).
  refine (map_smul _ (4 : ℂ)⁻¹ _).trans ?_
  refine congrArg (fun z => (4 : ℂ)⁻¹ • z) ?_
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl (fun p _ => ?_))
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl (fun q _ => ?_))
  -- Each summand: `id ⊗ (E ⊗ E)` on the pure tensor `(|β_p⟩⊗|β_q⟩) ⊗ w` acts as the identity on
  -- the left factor (`LinearMap.id` is defeq to the identity) and `E ⊗ E` on the output factor.
  exact TensorProduct.map_tmul _ _ _ _

/-- **Per-basis encoded CNOT gate-teleportation identity:** the
`encodedCnotGateTeleportation_identity` for computational-basis input data `|a⟩, |b⟩`.  A direct
specialization. -/
theorem encodedCnotGateTeleportation_identity_qubitBasis (E : qubit.space →ₗ[ℂ] C.space)
    (a b : Fin 2) :
    TensorProduct.map
        (LinearMap.id : ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space →ₗ[ℂ]
          ((qubit ⊗ qubit) ⊗ (qubit ⊗ qubit)).space)
        (TensorProduct.map E E)
        (gateTeleportProtocolReshape.toIsometry
          (((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec) ⊗ₜ[ℂ] cnotGateTeleportResource.vec))
      = (4 : ℂ)⁻¹ • ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2,
          (bellBasisVec p.1 p.2 ⊗ₜ[ℂ] bellBasisVec q.1 q.2) ⊗ₜ[ℂ]
            TensorProduct.map E E
              ((pauliByproduct (p.1 + q.1) p.2 ⊗ pauliByproduct q.1 (p.2 + q.2)).op
                (cnotGate.op ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec))) :=
  encodedCnotGateTeleportation_identity E (qubitBasis a).vec (qubitBasis b).vec

end AxQM
