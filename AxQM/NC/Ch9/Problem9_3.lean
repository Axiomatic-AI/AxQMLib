/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelitySubspace

/-!
# Nielsen & Chuang, Problem 9.3 (Subspace fidelity controls the entanglement fidelity)

Prove fact (5): subspace fidelity >=1-eta implies entanglement fidelity >=1-(3eta/2).

Here `F(ρ, E) = Σᵢ |tr(ρ Eᵢ)|²` is the **entanglement fidelity** of Section 9.3 (N&C `(9.135)`),
`E` is a trace-preserving quantum operation with operation elements `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†`
(`Σᵢ Eᵢ† Eᵢ = 1`), and the *support* of `ρ` is the span of its positive-eigenvalue eigenvectors.
Fact (5) — established by Knill and Laflamme, with a more detailed proof by Barnum, Knill and
Nielsen — is the quantitative link between the two notions of a quantum information source: a
channel that preserves every state in a subspace to high fidelity automatically preserves the
entanglement of any density operator supported there.

## The mathematics: variance decomposition + phase-diagonal twirl

Write `ρ = Σₐ pₐ |bₐ⟩⟨bₐ|` in a spectral eigenbasis. The proof has two quantitative halves:

* **Twirl reduction `1 − F(ρ, E) ≤ η + S_off`.** Averaging the pure-state fidelities of the
  *phase-twirl states* `ψ_θ = Σₐ √pₐ e^{2πiθₐ/N} |bₐ⟩` over a finite phase group `(ZMod N)^ι`
  (`N ≥ 3`) kills the cross terms and returns exactly the entanglement fidelity plus the
  off-diagonal *coherence* `S_off = Σ_{a≠b} pₐ p_b Σᵢ |⟨bₐ, Eᵢ b_b⟩|²`. Each `ψ_θ` is a unit vector
  in the support of `ρ`, so the hypothesis bounds every average term by `1 − η`.
* **Coherence bound `S_off ≤ η/2`.** In an eigenbasis the per-column budget
  `Σ_{a≠b} Σᵢ |⟨bₐ, Eᵢ b_b⟩|²` is the pure-state variance deficit `≤ η` of the support eigenvector
  `b_b`, and the doubly `p`-weighted off-diagonal sum of a column-budgeted array is `≤ η/2` (the
  extremal `2m(1−m) ≤ 1/2`). The `η/2` — not `η` — is what makes fact (5) tight at `1 − 3η/2`.

Combining, `F(ρ, E) ≥ 1 − η − S_off ≥ 1 − 3η/2`.

The statement is about the operation elements — bounded operators `H →L[ℂ] H` — the entanglement
fidelity, and inner products, as in Problem 9.2.

The formalisation lives in three files under `Mathlib/Analysis/InnerProductSpace/`:

### `EntanglementFidelityBound.lean` — variance decomposition and the coherence bound
* `ContinuousLinearMap.opVariance` and
  `ContinuousLinearMap.one_sub_entanglementFidelity_eq_sum_opVariance` — the infidelity as the total
  operator variance of the Kraus family, `1 − F(ρ, E) = Σᵢ Var_ρ(Eᵢ)`.
* `ContinuousLinearMap.re_inner_krausSumₗ_rankOne_self` — the physical reading of the pure-state
  fidelity, `⟨ψ| E(|ψ⟩⟨ψ|) |ψ⟩ = Σᵢ |⟨ψ, Eᵢ ψ⟩|²`.
* `ContinuousLinearMap.entanglementFidelity_sum_rankOne`, `ContinuousLinearMap.offDiagCoherenceSum`,
  `ContinuousLinearMap.offDiagCoherenceSum_le_of_pos` (and its all-columns corollary
  `ContinuousLinearMap.offDiagCoherenceSum_le`) — the eigenbasis diagonal fidelity and the
  support-aware off-diagonal coherence bound `S_off ≤ η/2` (only positive-weight eigenvectors, which
  lie in `supp ρ`, need a fidelity budget).
* `weighted_offDiag_sum_le_half` — the elementary combinatorial core behind the tight `η/2`.

### `EntanglementFidelityTwirl.lean` — the phase-diagonal twirl
* `ZMod.sum_stdAddChar_sub_add_sub` — finite-Fourier character orthogonality on `(ZMod N)^ι`.
* `ContinuousLinearMap.phaseTwirlState`, `ContinuousLinearMap.sum_phaseTwirl_normSq_inner_eq` — the
  twirl states and the average identity `Σ_θ Σⱼ |⟨ψ_θ, Eⱼ ψ_θ⟩|² = Nᶜ (F(ρ, E) + S_off)`.
* `ContinuousLinearMap.one_sub_entanglementFidelity_le_offDiagCoherenceSum` — the twirl reduction
  `1 − F(ρ, E) ≤ η + S_off`.

### `EntanglementFidelitySubspace.lean` — fact (5)
* `ContinuousLinearMap.norm_phaseTwirlState` — each phase-twirl state is a unit vector.
* `ContinuousLinearMap.entanglementFidelity_ge_one_sub_of_subspace_fidelity` — **Problem 9.3**: for
  `ρ = Σₐ pₐ |bₐ⟩⟨bₐ|` and a trace-preserving `E`, if every unit `ψ` in the support of `ρ` has
  `⟨ψ| E(|ψ⟩⟨ψ|) |ψ⟩ ≥ 1 − η`, then `F(ρ, E) ≥ 1 − 3η/2`.
-/
