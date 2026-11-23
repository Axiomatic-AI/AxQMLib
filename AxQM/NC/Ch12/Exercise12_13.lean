/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.EntropyExchangeConcave

/-!
# Nielsen & Chuang, Exercise 12.13 (Entropy exchange is concave in the quantum operation)

*(N&C p. 563.)*

Show entropy exchange S(rho,E) is concave in the quantum operation E.

That is, for a state `ρ` and a convex combination `E = p E₁ + (1 − p) E₂` of two trace-preserving
quantum operations (`0 ≤ p ≤ 1`),
`p S(ρ, E₁) + (1 − p) S(ρ, E₂) ≤ S(ρ, E)`.

As for the prerequisite entropy-exchange development (N&C Theorem 12.9, `Theorem12_9.lean`), the
entropy exchange `S(ρ, E)` here is realised at the operator/Hilbert–Schmidt level: a state is a
density operator `ρ : H →L[ℂ] H` and a trace-preserving operation is presented by its family of
operation elements `E : ι → (H →L[ℂ] H)` with `∑ᵢ Eᵢ† Eᵢ = 1`
(`ContinuousLinearMap.entropyExchange`).

## The formalisation

In `ToMathlib/Analysis/InnerProductSpace/EntropyExchangeConcave.lean`:

* `ContinuousLinearMap.channelMix p E₁ E₂` — the operation-element family of the mixture
  `p E₁ + (1 − p) E₂`, over the disjoint union `ι ⊕ κ` of the two index sets, scaling the elements
  of `E₁` by `√p` and those of `E₂` by `√(1 − p)`.
* `ContinuousLinearMap.sum_adjoint_mul_channelMix` — the mixture is trace preserving
  (`∑ₛ (channelMix)ₛ† (channelMix)ₛ = 1`), so it is a genuine trace-preserving quantum operation.
* `ContinuousLinearMap.krausSumₗ_channelMix` — the mixture's action is the convex combination of
  channel actions,
  `Σₛ (channelMix)ₛ ρ (channelMix)ₛ† = p (Σᵢ E₁ᵢ ρ E₁ᵢ†) + (1 − p) (Σⱼ E₂ⱼ ρ E₂ⱼ†)`,
  certifying that `channelMix p E₁ E₂` really is `p E₁ + (1 − p) E₂`.
* `ContinuousLinearMap.entropyExchangeState_channelMix` — the reference-plus-system output state is
  **affine** in the operation,
  `ρ_{R'Q'}(p E₁ + (1 − p) E₂) = p · ρ_{R'Q'}(E₁) + (1 − p) · ρ_{R'Q'}(E₂)`.
* `ContinuousLinearMap.entropyExchange_channelMix_ge` — **the exercise**: concavity of the entropy
  exchange in the operation,
  `p S(ρ, E₁) + (1 − p) S(ρ, E₂) ≤ S(ρ, p E₁ + (1 − p) E₂)`.

## The argument

The entropy exchange is the von Neumann entropy of the reference-plus-system output state,
`S(ρ, E) = S(ρ_{R'Q'})` (`entropyExchange_eq_vonNeumannEntropy_entropyExchangeState`, N&C
eqs. (12.107), (12.110)). The frame operator `ρ_{R'Q'} = Σᵢ |vec(√ρ Eᵢ†)⟩⟨vec(√ρ Eᵢ†)|` is affine
in the operation (`entropyExchangeState_channelMix`) — this is N&C's observation that the `w`-matrix
`Wⱼₖ = tr(Eⱼ ρ Eₖ†)` (equivalently `ρ_{R'Q'}`) is linear in the operation, the operation-side
analogue of its stated linearity in `ρ`. Concavity of the entropy exchange is then concavity of the
von Neumann entropy composed with this affine map, discharged by the faithfulness-free form
of entropy concavity
(`ContinuousLinearMap.IsDensityOp.sum_mul_vonNeumannEntropy_le_of_hasSupportLE`; faithfulness-free
is essential — the mixed output state is generally rank-deficient, e.g. two equal operations give a
pure `ρ_{R'Q'}`).
-/
