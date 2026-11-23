/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Uhlmann
public import ToMathlib.Analysis.InnerProductSpace.Polar

/-!
# Uhlmann's theorem into an arbitrary ancilla (upper-bound direction)

The operator core of Uhlmann's theorem
(`TensorProduct.isGreatest_norm_inner_of_isPurification`, Nielsen–Chuang Theorem 9.4) is stated
for purifications into the *doubled* space `E ⊗ E`. Several results — most notably
the **monotonicity of the fidelity** under a quantum operation (N&C Theorem 9.6) — need to
compare the fidelity trace norm `‖√ρ √σ‖₁` against the overlap of purifications living in a
*larger* ancilla `E ⊗ F` (the reference enlarged by a channel's environment). This file records
the **upper-bound half of Uhlmann's theorem for an arbitrary ancilla**:

  `‖⟪Ψ, Φ⟫‖ ≤ ‖√ρ √σ‖₁`   for any purifications `Ψ` of `ρ`, `Φ` of `σ` into `E ⊗ F`.

The achievement half (that `‖√ρ √σ‖₁` is *attained*) is already available in the doubled space
`E ⊗ E` (`isGreatest_norm_inner_of_isPurification`), which is enough for the applications: one
achieves the bound in `E ⊗ E` and bounds the transported overlap in the larger space.

## Main results

* `ContinuousLinearMap.eq_cfc_sqrt_comp_contraction` — the **rectangular factorization**
  `M M† = ρ ⟹ M = √ρ V` with `V` a *contraction* (`‖V‖ ≤ 1`), for `M : F →L E`. The
  square-ancilla version (`Uhlmann.eq_cfc_sqrt_comp_unitary`) produces a *unitary* `V`; here the
  rectangular polar decomposition (`polar_decomposition`, `polarPart_opNorm_le_one`) gives a
  partial isometry, hence a contraction.
* `ContinuousLinearMap.norm_hsPairing_le_traceNorm_cfc_sqrt_mul` — the operator form of the
  bound: `‖N.hsPairing M‖ ≤ ‖√ρ √σ‖₁` whenever `M M† = ρ` and `N N† = σ` (for `M N : F →L E`).
* `TensorProduct.norm_inner_le_traceNorm_of_isPurification` — the purification form:
  `‖⟪Ψ, Φ⟫‖ ≤ ‖√ρ √σ‖₁` for `Ψ` a purification of `ρ`, `Φ` a purification of `σ` into `E ⊗ F`.

## Proof

Both `M M† = ρ` and `N N† = σ` factor as `M = √ρ V`, `N = √σ W` with `‖V‖, ‖W‖ ≤ 1`; then the
pairing rewrites (via `hsPairing_conj`/`hsPairing_comp_left`/`hsPairing_comp_right`, exactly as in
the `E ⊗ E` proof) to `(√ρ √σ).hsPairing (V W†)`, and `V W†` is a contraction, so the Hölder bound
`norm_hsPairing_le_traceNorm_of_opNorm_le_one` (Lemma 9.5) closes it. The purification form is the
operator form transported through the matricization isomorphism
(`matricize_inner_eq_hsPairing`, `isPurification_iff_matricize_comp_adjoint`).
-/

open scoped InnerProductSpace
open ContinuousLinearMap

@[expose] public section

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] [CompleteSpace F]

/-- **Rectangular factorization of a self-outer-product.** If `M M† = ρ` for `M : F →L E`, then
`M = √ρ V` for a *contraction* `V : F →L E` (`‖V‖ ≤ 1`). This is the rectangular counterpart of
`ContinuousLinearMap.eq_cfc_sqrt_comp_unitary` (which needs `M` square and delivers a unitary):
`|M†| = √(M M†) = √ρ`, and the (rectangular) polar decomposition `M† = U √ρ` with `U` a partial
isometry (`polar_decomposition`) gives `M = √ρ U†`, where `V := U†` is a contraction
(`polarPart_opNorm_le_one`). -/
theorem eq_cfc_sqrt_comp_contraction {ρ : E →L[ℂ] E} {M : F →L[ℂ] E}
    (h : M.comp (adjoint M) = ρ) :
    ∃ V : F →L[ℂ] E, ‖V‖ ≤ 1 ∧ M = (cfc Real.sqrt ρ).comp V := by
  -- `|M†|² = M M† = ρ`, and the positive square root is unique, so `|M†| = √ρ`.
  have hsq : (adjoint M).absoluteValue.comp (adjoint M).absoluteValue = ρ := by
    rw [absoluteValue_sq, adjoint_adjoint]; exact h
  have habs : (adjoint M).absoluteValue = cfc Real.sqrt ρ := by
    rw [← hsq, ← ContinuousLinearMap.mul_def,
      cfc_real_sqrt_mul_self_eq_self_of_nonneg (adjoint M).absoluteValue_nonneg]
  -- Rectangular polar of `M†`: `M† = polarPart(M†) ∘ √ρ`; take adjoints to get `M = √ρ ∘ V`.
  have hpolar : adjoint M = (adjoint M).polarPart.comp (cfc Real.sqrt ρ) := by
    rw [← habs]; exact polar_decomposition (adjoint M)
  refine ⟨adjoint (adjoint M).polarPart, ?_, ?_⟩
  · rw [ContinuousLinearMap.adjoint.norm_map]
    exact polarPart_opNorm_le_one _
  · have hM := congrArg adjoint hpolar
    rw [adjoint_adjoint, adjoint_comp, adjoint_cfc_real_sqrt] at hM
    exact hM

/-- **Uhlmann upper bound, operator form.** For `M N : F →L E` with `M M† = ρ` and `N N† = σ`,
the Hilbert–Schmidt pairing is bounded by the fidelity trace norm:
`‖N.hsPairing M‖ ≤ ‖√ρ √σ‖₁`. Factoring `M = √ρ V`, `N = √σ W` with `V, W` contractions
(`eq_cfc_sqrt_comp_contraction`), the pairing rewrites to `(√ρ √σ).hsPairing (V W†)` with `V W†`
a contraction, whence the Hölder bound `norm_hsPairing_le_traceNorm_of_opNorm_le_one`. -/
theorem norm_hsPairing_le_traceNorm_cfc_sqrt_mul {ρ σ : E →L[ℂ] E} {M N : F →L[ℂ] E}
    (hM : M.comp (adjoint M) = ρ) (hN : N.comp (adjoint N) = σ) :
    ‖N.hsPairing M‖ ≤ (cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm := by
  obtain ⟨V, hV, hMV⟩ := eq_cfc_sqrt_comp_contraction hM
  obtain ⟨W, hW, hNW⟩ := eq_cfc_sqrt_comp_contraction hN
  set p : E →L[ℂ] E := cfc Real.sqrt ρ
  set q : E →L[ℂ] E := cfc Real.sqrt σ
  have hpsa : adjoint p = p := adjoint_cfc_real_sqrt ρ
  have hcontr : ‖V.comp (adjoint W)‖ ≤ 1 := by
    calc ‖V.comp (adjoint W)‖ ≤ ‖V‖ * ‖adjoint W‖ := opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
          rw [ContinuousLinearMap.adjoint.norm_map]; gcongr
      _ = 1 := one_mul 1
  rw [hMV, hNW,
    ← hsPairing_conj (p.comp V) (q.comp W), norm_star, hsPairing_comp_left, hpsa,
    ← comp_assoc, ← hsPairing_conj ((p.comp q).comp W) V, norm_star, hsPairing_comp_right]
  exact norm_hsPairing_le_traceNorm_of_opNorm_le_one _ hcontr

end ContinuousLinearMap

namespace TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] [CompleteSpace F]

/-- **Uhlmann upper bound into an arbitrary ancilla, purification form** (Nielsen–Chuang Theorem
9.4, upper-bound half). For positive operators `ρ, σ` on `E` and *any* ancilla `F`, the overlap
of a purification `Ψ` of `ρ` with a purification `Φ` of `σ` into `E ⊗ F` is at most the fidelity
trace norm:

  `‖⟪Ψ, Φ⟫‖ ≤ ‖√ρ √σ‖₁`.

This generalizes the doubled-space bound in `isGreatest_norm_inner_of_isPurification` from the
canonical ancilla `E ⊗ E` to an arbitrary `E ⊗ F` — the form needed to bound the overlap of
purifications transported into a channel's (system ⊗ environment ⊗ reference) space, in the proof
of the monotonicity of the fidelity (N&C Theorem 9.6). Through the matricization isomorphism it is
`norm_hsPairing_le_traceNorm_cfc_sqrt_mul` applied to `M := matricize b Ψ`, `N := matricize b Φ`,
which satisfy `M M† = ρ`, `N N† = σ` by `isPurification_iff_matricize_comp_adjoint`. -/
theorem norm_inner_le_traceNorm_of_isPurification {ρ σ : E →L[ℂ] E}
    {Ψ Φ : TensorProduct ℂ E F}
    (hΨ : TensorProduct.IsPurification ρ Ψ) (hΦ : TensorProduct.IsPurification σ Φ) :
    ‖(inner ℂ Ψ Φ : ℂ)‖ ≤ (cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm := by
  set b := stdOrthonormalBasis ℂ F
  rw [isPurification_iff_matricize_comp_adjoint b] at hΨ hΦ
  rw [matricize_inner_eq_hsPairing b Ψ Φ]
  exact ContinuousLinearMap.norm_hsPairing_le_traceNorm_cfc_sqrt_mul hΨ hΦ

end TensorProduct
