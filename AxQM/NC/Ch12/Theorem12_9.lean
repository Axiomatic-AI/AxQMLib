/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.QuantumFanoInequality

/-!
# Nielsen & Chuang, Theorem 12.9 (Quantum Fano inequality)

*(N&C p. 563.)*

Quantum Fano inequality: S(rho,E) <= H(F)+(1-F)log(d^2-1).

The quantum Fano inequality relates two quantum quantities — the entropy exchange
`S(ρ, E) = S(W) = S(ρ_{R'Q'})` and the entanglement fidelity `F(ρ, E)` — of a trace-preserving
quantum operation. Both quantities are formalised at the operator-algebra /
Hilbert–Schmidt level (a state is a density operator `ρ : H →L[ℂ] H`, an operation is its Kraus
family `E : ι → (H →L[ℂ] H)`).

## The formalisation

The headline theorem is `ContinuousLinearMap.entropyExchange_le_binEntropy_entanglementFidelity_add`
(in `ToMathlib/Analysis/InnerProductSpace/QuantumFanoInequality.lean`):

```
S(ρ, E) = entropyExchange ρ E
        ≤ Real.binEntropy (entanglementFidelity ρ E)
          + (1 - entanglementFidelity ρ E) * Real.log ((finrank ℂ H : ℝ) ^ 2 - 1)
```

for `hρ : ρ.IsDensityOp` and a trace-preserving family `htp : ∑ i, adjoint (E i) * E i = 1`, with
`d = finrank ℂ H`. Entropy is in nats (natural log) rather than N&C's bits; the inequality is
base-independent, so this is a faithful reformalisation of eq. (12.112).

The supporting definitions and lemmas, proved in the files below, are:

**Entropy exchange and the reference-plus-system state** (in
`ToMathlib/Analysis/InnerProductSpace/EntropyExchange.lean`):

* `ContinuousLinearMap.wMatrix` — the `w`-matrix `Wⱼₖ = tr(Eⱼ ρ Eₖ†)` (N&C eqs. (12.109)–(12.110)).
* `ContinuousLinearMap.entropyExchange` — the entropy exchange `S(ρ, E) = S(W)` (eq. (12.110)).
* `ContinuousLinearMap.entropyExchangeState` — the reference-plus-system output density operator
  `ρ_{R'Q'}` (eq. (12.107)), realised on the `d²`-dimensional Hilbert–Schmidt space `H ⊗ H` as the
  frame operator `Σᵢ |vec(√ρ Eᵢ†)⟩⟨vec(√ρ Eᵢ†)|`.
* `ContinuousLinearMap.entropyExchange_eq_vonNeumannEntropy_entropyExchangeState` —
  `S(ρ, E) = S(ρ_{R'Q'})`.
* `ContinuousLinearMap.re_inner_entropyExchangeState_sqrt_eq_entanglementFidelity` —
  `⟨vec √ρ, ρ_{R'Q'} (vec √ρ)⟩ = Σᵢ |tr(ρ Eᵢ)|² = F(ρ, E)` (eqs. (9.135), (12.113)); here `vec √ρ`
  is N&C's initial pure state `|RQ⟩`.
* `ContinuousLinearMap.entropyExchangeState_isDensityOp` — `ρ_{R'Q'}` is a density operator (trace
  `1` from the completeness relation `Σᵢ Eᵢ† Eᵢ = 1`).
* `ContinuousLinearMap.norm_matricize_symm_cfc_sqrt` — `vec √ρ` is a unit vector.
* `ContinuousLinearMap.entanglementFidelity` (in `…/EntanglementFidelity.lean`) — `F(ρ, E)`.

**The density-operator Fano bound** (in
`ToMathlib/Analysis/InnerProductSpace/VonNeumannEntropyFano.lean`), the operator core of N&C's proof
(eqs. (12.113)–(12.115)):

* `ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_le_binEntropy_add` —
  `S(σ) ≤ H(⟨ψ, σ ψ⟩) + (1 - ⟨ψ, σ ψ⟩) · log (D - 1)` for a density operator `σ` on a
  `D`-dimensional space and any unit vector `ψ`: extend `ψ` to an orthonormal basis, bound `S(σ)`
  by the Shannon entropy of the diagonal (`vonNeumannEntropy_le_entropy_diag`, N&C Theorem 11.9 —
  a projective measurement never decreases entropy), then apply the classical grouping inequality
  (eq. (12.114)).

**The Gram / sum-of-rank-ones entropy equality** (in
`ToMathlib/Analysis/InnerProductSpace/VonNeumannEntropyGram.lean`):

* `ContinuousLinearMap.vonNeumannEntropy_sum_rankOne_self_eq_gram` —
  `S(Σᵢ |φᵢ⟩⟨φᵢ|) = S(gram φ)`, which identifies `S(W)` with `S(ρ_{R'Q'})` since `W` is the Gram
  matrix of the vectorized family `vec(√ρ Eᵢ†)`.

**The assembly** (in `ToMathlib/Analysis/InnerProductSpace/QuantumFanoInequality.lean`): applies the
density-operator Fano bound to `σ = ρ_{R'Q'}`, `ψ = vec √ρ`, `D = finrank ℂ (H ⊗ H) = d²`
(`Module.finrank_tensorProduct`), then rewrites `S(ρ_{R'Q'}) = S(ρ, E)` and
`⟨vec √ρ, ρ_{R'Q'} (vec √ρ)⟩ = F(ρ, E)` — exactly N&C's eqs. (12.113)–(12.115).
-/
