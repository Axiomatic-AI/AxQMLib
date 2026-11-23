/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PolarUnitary
public import ToMathlib.Analysis.InnerProductSpace.Purification
public import ToMathlib.Analysis.InnerProductSpace.TraceNorm

/-!
# Uhlmann's theorem (Nielsen–Chuang Theorem 9.4), operator form

For positive operators `ρ, σ` on a finite-dimensional complex inner product space `E`, the
**fidelity trace norm** `‖√ρ √σ‖₁` is the *greatest* overlap `‖⟪Ψ, Φ⟫‖` achievable between a
purification `Ψ` of `ρ` and a purification `Φ` of `σ` into the doubled space `E ⊗ E`:

  `IsGreatest {‖⟪Ψ, Φ⟫‖ | IsPurification ρ Ψ ∧ IsPurification σ Φ} ‖√ρ √σ‖₁`.

This is the operator-level core of Nielsen–Chuang Theorem 9.4 (Uhlmann's theorem). The
restatement for states — `F(ρ, σ) = max |⟨ψ|φ⟩|` over purifications, with `F` the
`State.fidelity` — is in `AxQM/NC/Ch9`.

## Proof outline

A purification `Ψ` of `ρ` corresponds, under the matricization isomorphism
`matricize b : E ⊗ E ≃ (E →L E)`, to an operator `M := matricize b Ψ` with `M M† = ρ`
(`isPurification_iff_matricize_comp_adjoint`), and the overlap becomes the Hilbert–Schmidt
pairing `⟪Ψ, Φ⟫ = hsPairing N M` (`matricize_inner_eq_hsPairing`), `N := matricize b Φ`.

* **Factorization** (`eq_cfc_sqrt_comp_unitary`): `M M† = ρ ⟹ M = √ρ V` for a *unitary* `V`.
  Indeed `|M†| = √(M M†) = √ρ`, and the left unitary polar decomposition of `M†`
  (`exists_mem_unitary_eq_comp_absoluteValue`) gives `M† = U √ρ`, hence `M = √ρ U†`.
* **Upper bound.** With `M = √ρ V`, `N = √σ W`, the pairing rewrites (via `hsPairing_comp_*`
  and `hsPairing_conj`) to `(√ρ √σ).hsPairing (V W†)`, and `V W†` is a unitary contraction,
  so `‖⟪Ψ, Φ⟫‖ ≤ ‖√ρ √σ‖₁` by `norm_hsPairing_le_traceNorm_of_opNorm_le_one` (Lemma 9.5).
* **Achievement.** Taking `M = √ρ` and `N = √σ U†` where `√ρ √σ = U |√ρ √σ|` is the polar
  decomposition, both `M M† = ρ` and `N N† = σ` hold, and
  `⟪Ψ, Φ⟫ = tr(√ρ √σ U†) = tr|√ρ √σ| = ‖√ρ √σ‖₁`, attaining the bound.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

@[expose] public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

namespace ContinuousLinearMap

omit [FiniteDimensional ℂ E] in
/-- The **CFC real square root of an operator is self-adjoint**, `(√a)† = √a`: a
real-valued functional-calculus image is self-adjoint (`IsSelfAdjoint.cfc`), spelled through
`star = adjoint`. -/
theorem adjoint_cfc_real_sqrt (a : E →L[ℂ] E) :
    adjoint (cfc Real.sqrt a) = cfc Real.sqrt a := by
  rw [← star_eq_adjoint]; exact IsSelfAdjoint.cfc

omit [FiniteDimensional ℂ E] in
/-- A **unitary operator is a contraction**, `‖U‖ ≤ 1`: from the C⋆-identity
`‖U‖² = ‖U† U‖ = ‖1‖ ≤ 1`. -/
theorem opNorm_le_one_of_mem_unitary {U : E →L[ℂ] E}
    (hU : U ∈ unitary (E →L[ℂ] E)) : ‖U‖ ≤ 1 := by
  have hsq : ‖U‖ * ‖U‖ = ‖(1 : E →L[ℂ] E)‖ := by
    rw [← CStarRing.norm_star_mul_self, (Unitary.mem_iff.mp hU).1]
  have h1 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]; exact norm_id_le
  nlinarith [norm_nonneg U]

/-- **Factorization of a self-outer-product** (the operator core of Uhlmann's theorem): if
`M M† = ρ`, then `M = √ρ V` for some *unitary* `V`. The absolute value of `M†` is
`|M†| = √(M M†) = √ρ`, so the left unitary polar decomposition `M† = U |M†|`
(`exists_mem_unitary_eq_comp_absoluteValue`) reads `M† = U √ρ`; taking adjoints gives
`M = √ρ U†` with `V := U†` unitary. -/
theorem eq_cfc_sqrt_comp_unitary {ρ M : E →L[ℂ] E} (h : M.comp (adjoint M) = ρ) :
    ∃ V ∈ unitary (E →L[ℂ] E), M = (cfc Real.sqrt ρ).comp V := by
  obtain ⟨U, hU, hUeq⟩ := exists_mem_unitary_eq_comp_absoluteValue (adjoint M)
  have habs : (adjoint M).absoluteValue = cfc Real.sqrt ρ := by
    rw [absoluteValue_eq_cfc_sqrt, adjoint_adjoint, h]
  refine ⟨adjoint U, ?_, ?_⟩
  · rw [← star_eq_adjoint]; exact Unitary.star_mem hU
  · have hM := congrArg adjoint hUeq
    rw [adjoint_adjoint, habs, adjoint_comp, adjoint_cfc_real_sqrt] at hM
    exact hM

end ContinuousLinearMap

namespace TensorProduct

/-- **Uhlmann's theorem (operator form), Nielsen–Chuang Theorem 9.4.** For positive operators
`ρ, σ` on a finite-dimensional complex inner product space `E`, the trace norm `‖√ρ √σ‖₁` is the
greatest overlap `‖⟪Ψ, Φ⟫‖` over purifications `Ψ` of `ρ` and `Φ` of `σ` into `E ⊗ E`. -/
theorem isGreatest_norm_inner_of_isPurification {ρ σ : E →L[ℂ] E} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    IsGreatest
      {r : ℝ | ∃ Ψ Φ : TensorProduct ℂ E E,
        TensorProduct.IsPurification ρ Ψ ∧ TensorProduct.IsPurification σ Φ ∧
        r = ‖(inner ℂ Ψ Φ : ℂ)‖}
      (cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm := by
  set b := stdOrthonormalBasis ℂ E
  set p : E →L[ℂ] E := cfc Real.sqrt ρ
  set q : E →L[ℂ] E := cfc Real.sqrt σ
  have hpsa : adjoint p = p := adjoint_cfc_real_sqrt ρ
  have hqsa : adjoint q = q := adjoint_cfc_real_sqrt σ
  have hpp : p * p = ρ := cfc_real_sqrt_mul_self_of_nonneg hρ
  have hqq : q * q = σ := cfc_real_sqrt_mul_self_of_nonneg hσ
  constructor
  · -- Achievement: choose `M = √ρ`, `N = √σ U†` with `√ρ √σ = U |√ρ √σ|`.
    obtain ⟨U, hU, hUeq⟩ := exists_mem_unitary_eq_comp_absoluteValue (p * q)
    have hUU : adjoint U * U = 1 := by rw [← star_eq_adjoint]; exact (Unitary.mem_iff.mp hU).1
    refine ⟨(matricize b).symm p, (matricize b).symm (q.comp (adjoint U)), ?_, ?_, ?_⟩
    · -- `IsPurification ρ Ψ*`: `√ρ (√ρ)† = √ρ √ρ = ρ`.
      rw [isPurification_iff_matricize_comp_adjoint b, LinearEquiv.apply_symm_apply, hpsa]
      exact hpp
    · -- `IsPurification σ Φ*`: `(√σ U†)(√σ U†)† = √σ (U† U) √σ = √σ √σ = σ`.
      rw [isPurification_iff_matricize_comp_adjoint b, LinearEquiv.apply_symm_apply]
      have hadj : adjoint (q.comp (adjoint U)) = U.comp q := by
        rw [adjoint_comp, adjoint_adjoint, hqsa]
      rw [hadj]
      change q * adjoint U * (U * q) = σ
      rw [mul_assoc q (adjoint U) (U * q), ← mul_assoc (adjoint U) U q, hUU, one_mul, hqq]
    · -- Value: `⟪Ψ*, Φ*⟫ = tr(√ρ √σ U†) = tr|√ρ √σ| = ‖√ρ √σ‖₁`.
      rw [matricize_inner_eq_hsPairing b _ _, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, hsPairing_eq, hpsa]
      have hUU' : U.adjoint ∘L U = 1 := hUU
      set A := (p * q).absoluteValue with hA
      have hUeq' : p * q = U * A := hUeq
      have e1 : p.comp (q.comp (adjoint U)) = U ∘L A ∘L U.adjoint := by
        change p * (q * adjoint U) = U * (A * adjoint U)
        rw [← mul_assoc, hUeq', mul_assoc]
      rw [e1, trace_conj_isometry hUU' A, hA, toLinearMap_absoluteValue,
        ← LinearMap.ofReal_traceNorm_eq_trace_absoluteValue, RCLike.norm_ofReal,
        abs_of_nonneg (LinearMap.traceNorm_nonneg _)]
      exact (traceNorm_toLinearMap _).symm
  · -- Upper bound: any overlap is `≤ ‖√ρ √σ‖₁`.
    rintro r ⟨Ψ, Φ, hΨ, hΦ, rfl⟩
    rw [isPurification_iff_matricize_comp_adjoint b] at hΨ hΦ
    obtain ⟨V, hV, hMV⟩ := eq_cfc_sqrt_comp_unitary hΨ
    obtain ⟨W, hW, hNW⟩ := eq_cfc_sqrt_comp_unitary hΦ
    have hcontr : ‖V.comp (adjoint W)‖ ≤ 1 := by
      refine opNorm_le_one_of_mem_unitary ?_
      have hVW : V.comp (adjoint W) = V * star W := by rw [← star_eq_adjoint]; rfl
      rw [hVW]
      exact mul_mem hV (Unitary.star_mem hW)
    rw [matricize_inner_eq_hsPairing b Ψ Φ, hMV, hNW,
      ← hsPairing_conj (p.comp V) (q.comp W), norm_star, hsPairing_comp_left, hpsa,
      ← comp_assoc, ← hsPairing_conj ((p.comp q).comp W) V, norm_star, hsPairing_comp_right]
    exact norm_hsPairing_le_traceNorm_of_opNorm_le_one _ hcontr

end TensorProduct
