/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CondTypicalSubspace
import ToMathlib.InformationTheory.ConditionalTypicalConcentration

/-!
# AxQM.Postulates.API — the random-coding expectation of the conditional atypical
weight (N&C Eq. 12.76)

The random-coding *expectation* estimate for the conditional typical subspace `P_M` of Nielsen &
Chuang's proof of the Holevo–Schumacher–Westmoreland theorem (Theorem 12.8, achievability). The
deterministic core — the projector `State.condTypicalSubspaceProj`, its dimension bound (Eq. 12.77),
and the quantum→classical bridge `tr(σ_M (I − P_M)) = 1 − ∑_{κ ∈ T_M} ∏ᵢ λ_{i,κᵢ}` (Eq. 12.76,
`State.re_trace_one_sub_condTypicalSubspaceProj_comp_piTensor`) — lives in
`Postulates/API/CondTypicalSubspace.lean`. This file supplies the missing *random-coding* half:
averaging that atypical weight over Alice's random codeword.

Alice's codeword for a message is a length-`n` sequence `M : Fin n → α` of letters drawn i.i.d. from
an input ensemble `p : α → ℝ`; letter `a` maps to the channel output `τ a = E(ρ_a) : State S`
(all outputs on the *same* channel-output system `S`). The codeword output is the product state
`σ_M = ⨂ᵢ τ (Mᵢ)`, and its conditional typical subspace projector is
`State.condTypicalSubspaceProj (fun i ↦ τ (Mᵢ)) s ε`. With the threshold `s = S̄ = ∑ₐ pₐ S(τ_a)`
the ensemble-average output entropy, N&C's Eq. 12.76 bounds the ensemble expectation of the atypical
weight.

## Main result

* `State.expectation_re_trace_one_sub_condTypicalSubspaceProj_le` — **N&C Eq. 12.76**: the
  `p`-weighted average over codewords `M` of `tr(σ_M (I − P_M))` is at most `V / (n ε²)`, where
  `V = ∑ₐ pₐ · ∑_b λ_{a,b} · (−log λ_{a,b} − S̄)²` (`λ_a = (τ a).eigenvalueDist`) is the per-letter
  spectral-surprisal variance of the ensemble. A *finite-`n`-explicit* bound; as `n → ∞` (with `ε`
  fixed) the right side tends to `0`, giving the vanishing atypical weight that the random-coding
  error estimate (Eqs. 12.80–12.82) consumes.

The quantum face of the classical `Real.sum_weighted_one_sub_condTypicalSeq_le`: the per-codeword
bridge `State.re_trace_one_sub_condTypicalSubspaceProj_comp_piTensor` turns each `tr(σ_M (I − P_M))`
into the classical conditional-atypical weight `1 − ∑_{κ ∈ T_M} ∏ᵢ λ_{Mᵢ,κᵢ}`, on which the
classical random-coding concentration then acts. The threshold identification `S̄ = ∑ₐ pₐ H(λ_a)`
is `State.vonNeumannEntropy_eq_entropy_eigenvalueDist` letterwise.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace AxQM

variable {S : QSystem} {α : Type*} [Fintype α]

/-- **The random-coding expectation of the conditional atypical weight** (Nielsen & Chuang,
Theorem 12.8, Eq. 12.76). Alice draws a length-`n` codeword `M : Fin n → α` with letters i.i.d. from
the input ensemble `p : α → ℝ`; letter `a` maps to the channel output `τ a : State S`, so the
codeword output is the product state `σ_M = ⨂ᵢ τ (Mᵢ)` with conditional typical subspace projector
`P_M = State.condTypicalSubspaceProj (fun i ↦ τ (Mᵢ)) s ε`. With the threshold `s` equal to the
ensemble-average output entropy `S̄ = ∑ₐ pₐ S(τ_a)`, the `p`-weighted average over codewords of the
atypical weight `tr(σ_M (I − P_M))` is at most `V / (n ε²)`, where

`V = ∑ₐ pₐ · ∑_b λ_{a,b} · (−log λ_{a,b} − S̄)²`,  `λ_a = (τ a).eigenvalueDist`,

is the per-letter spectral-surprisal variance of the ensemble. A *deterministic-in-`ε`*,
finite-`n`-explicit bound: as `n → ∞` (with `ε` fixed) `V / (n ε²) → 0`, so the expected atypical
weight vanishes — the vanishing that the random-coding decoding-error estimate (Eqs. 12.80–12.82)
consumes.

Proof: the per-codeword bridge
`State.re_trace_one_sub_condTypicalSubspaceProj_comp_piTensor` rewrites
each `tr(σ_M (I − P_M))` as the classical conditional-atypical weight
`1 − ∑_{κ ∈ T_M} ∏ᵢ λ_{Mᵢ,κᵢ}`; the classical random-coding concentration
`Real.sum_weighted_one_sub_condTypicalSeq_le` then bounds the ensemble average of that weight, the
threshold matching via `State.vonNeumannEntropy_eq_entropy_eigenvalueDist`
(`S̄ = ∑ₐ pₐ H(λ_a)`). -/
theorem State.expectation_re_trace_one_sub_condTypicalSubspaceProj_le
    (τ : α → State S) (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    {s : ℝ} (hs : s = ∑ a, p a * (τ a).vonNeumannEntropy) :
    ∑ M : Fin n → α, (∏ i, p (M i)) *
        RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor (fun _ : Fin n => S)).space)
          (((1 : (QSystem.piTensor (fun _ : Fin n => S)).space →L[ℂ]
                (QSystem.piTensor (fun _ : Fin n => S)).space)
              - State.condTypicalSubspaceProj (fun i => τ (M i)) s ε).comp
              (State.piTensor (fun i => τ (M i))).op : _ →ₗ[ℂ] _))
      ≤ (∑ a, p a * ∑ b, (τ a).eigenvalueDist b *
            (- Real.log ((τ a).eigenvalueDist b) - s) ^ 2) / (n * ε ^ 2) := by
  -- The threshold `S̄` is the ensemble-average Shannon entropy of the output spectra.
  have hs' : s = ∑ a, p a * Real.entropy (τ a).eigenvalueDist := by
    simp_rw [hs, State.vonNeumannEntropy_eq_entropy_eigenvalueDist]
  -- Each codeword's atypical weight is the classical conditional-atypical mass (Eq. 12.76 bridge).
  simp_rw [State.re_trace_one_sub_condTypicalSubspaceProj_comp_piTensor]
  exact Real.sum_weighted_one_sub_condTypicalSeq_le p hp0 hp1 (fun a => (τ a).eigenvalueDist)
    (fun a b => (τ a).eigenvalueDist_nonneg b) (fun a => (τ a).eigenvalueDist_sum_eq_one) hn hε hs'

end AxQM
