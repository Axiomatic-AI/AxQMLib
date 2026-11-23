/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.UhlmannAncilla
public import ToMathlib.Analysis.InnerProductSpace.OperatorSumDilation

/-!
# Monotonicity of the fidelity trace norm under an operator sum (Nielsen–Chuang Theorem 9.6)

The **fidelity** of two positive operators `ρ, σ` is `F(ρ, σ) = ‖√ρ √σ‖₁` (the Schatten-1 form,
`State.fidelity_eq_traceNorm`). Nielsen–Chuang Theorem 9.6 states that a trace-preserving quantum
operation never decreases the fidelity: `F(E(ρ), E(σ)) ≥ F(ρ, σ)`. This file proves the
**operator-level heart** of that statement — the inequality between the two fidelity trace norms —
for the operator-sum (Kraus) form of the channel. The statement of the theorem for
`AxQM.IsChannel` / `State.fidelity` is in `AxQM/NC/Ch9/Theorem9_6.lean`.

## Main results

* `ContinuousLinearMap.traceNorm_cfc_sqrt_mul_le_krausSum` — for a **complete** Kraus family
  `E : ι → (H →L H)` (`∑ₖ Eₖ† Eₖ = 1`) and positive `ρ, σ`,
  `‖√ρ √σ‖₁ ≤ ‖√(∑ₖ Eₖ ρ Eₖ†) √(∑ₖ Eₖ σ Eₖ†)‖₁ = ‖√(E(ρ)) √(E(σ))‖₁`.

## Proof

Uhlmann's theorem (`TensorProduct.isGreatest_norm_inner_of_isPurification`, N&C Thm 9.4) supplies
purifications `Ψ₀, Φ₀ ∈ H ⊗ H` of `ρ, σ` **achieving** `‖√ρ √σ‖₁ = ‖⟪Ψ₀, Φ₀⟫‖`; matricizing them
gives square operators `M₀ = matricize Ψ₀`, `N₀ = matricize Φ₀` with `M₀ M₀† = ρ`, `N₀ N₀† = σ` and
`‖√ρ √σ‖₁ = ‖N₀.hsPairing M₀‖` (`matricize_inner_eq_hsPairing`).

The channel is dilated into the environment `F = ℂ^ι`: `krausDilation` assembles the isometry-shaped
column operators, and we take
`M := (√ρ-side dilation)†`, `N := (√σ-side dilation)† : (H ⊗ F) →L H`, built from the Kraus family
`{(Eₖ M₀)†}` / `{(Eₖ N₀)†}`. Then

* `M M† = ∑ₖ (Eₖ M₀)(Eₖ M₀)† = ∑ₖ Eₖ ρ Eₖ† = krausSumₗ E ρ`, and likewise `N N† = krausSumₗ E σ`,
  from `adjoint_krausDilation_comp_self` and `M₀ M₀† = ρ`;
* `N.hsPairing M = ∑ₖ tr(Eₖ N₀ M₀† Eₖ†) = tr((∑ₖ Eₖ† Eₖ) N₀ M₀†) = tr(N₀ M₀†) = N₀.hsPairing M₀`,
  using `trace_conj_adjoint` (cyclicity) and the **completeness** `∑ₖ Eₖ† Eₖ = 1`.

Feeding `M, N` to the arbitrary-ancilla Uhlmann upper bound
(`norm_hsPairing_le_traceNorm_cfc_sqrt_mul`, the operator form for the enlarged ancilla `H ⊗ F`)
gives `‖N.hsPairing M‖ ≤ ‖√(krausSumₗ E ρ) √(krausSumₗ E σ)‖₁`, and the two hsPairings coincide, so
`‖√ρ √σ‖₁ = ‖N₀.hsPairing M₀‖ = ‖N.hsPairing M‖ ≤ ‖√(E(ρ)) √(E(σ))‖₁`.

-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

@[expose] public section

noncomputable section

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {Hin : Type*} [NormedAddCommGroup Hin] [InnerProductSpace 𝕜 Hin] [FiniteDimensional 𝕜 Hin]
  {Eout : Type*} [NormedAddCommGroup Eout] [InnerProductSpace 𝕜 Eout] [FiniteDimensional 𝕜 Eout]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι]

/-- **Cross-family contraction of two Kraus dilations.** For families `A B : ι → Hin →ₗ Eout`,
`(krausDilation b B)† ∘ₗ (krausDilation b A) = ∑ₖ (B k)† ∘ₗ A k`. Generalises
`adjoint_krausDilation_comp_self` (the `A = B` case): expanding
`(krausDilation b B)† = ∑ₖ (B k)† ∘ₗ restrictRight b k` and
`krausDilation b A = ∑ⱼ embedRight b j ∘ₗ A j` and using the delta-orthogonality
`restrictRight b k ∘ₗ embedRight b j = δₖⱼ` collapses the double sum. -/
theorem adjoint_krausDilation_comp_krausDilation (b : OrthonormalBasis ι 𝕜 F)
    (A B : ι → Hin →ₗ[𝕜] Eout) :
    adjoint (krausDilation b B) ∘ₗ krausDilation b A = ∑ k, adjoint (B k) ∘ₗ A k := by
  classical
  ext x
  simp only [LinearMap.comp_apply, krausDilation_apply, adjoint_krausDilation,
    map_sum, LinearMap.sum_apply, restrictRight_tmul, b.inner_eq_ite]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [ite_eq_left rfl, one_smul]
  · intro j _ hjk
    split_ifs with h
    · simp_all
    · rw [zero_smul, map_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

end LinearMap

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]

/-- **Monotonicity of the fidelity trace norm under an operator sum** (the operator-level core of
Nielsen–Chuang Theorem 9.6). For a complete Kraus family `E : ι → (H →L H)` (`∑ₖ Eₖ† Eₖ = 1`) and
positive operators `ρ, σ`, the fidelity trace norm does not decrease:

  `‖√ρ √σ‖₁ ≤ ‖√(∑ₖ Eₖ ρ Eₖ†) √(∑ₖ Eₖ σ Eₖ†)‖₁`.

See the module docstring for the Uhlmann-plus-dilation argument. -/
theorem traceNorm_cfc_sqrt_mul_le_krausSum {ι : Type*} [Fintype ι]
    (E : ι → H →L[ℂ] H) (hE : ∑ i, (adjoint (E i)).comp (E i) = 1)
    {ρ σ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    (cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm
      ≤ (cfc Real.sqrt (krausSumₗ E ρ) * cfc Real.sqrt (krausSumₗ E σ)).traceNorm := by
  classical
  -- Uhlmann achievement in `H ⊗ H`.
  obtain ⟨Ψ₀, Φ₀, hΨ₀, hΦ₀, hval⟩ :=
    (TensorProduct.isGreatest_norm_inner_of_isPurification hρ hσ).1
  set b := stdOrthonormalBasis ℂ H with hb
  set M₀ : H →L[ℂ] H := TensorProduct.matricize b Ψ₀ with hM₀
  set N₀ : H →L[ℂ] H := TensorProduct.matricize b Φ₀ with hN₀
  rw [TensorProduct.isPurification_iff_matricize_comp_adjoint b, ← hM₀] at hΨ₀
  rw [TensorProduct.isPurification_iff_matricize_comp_adjoint b, ← hN₀] at hΦ₀
  -- Environment `F = ℂ^ι`.
  set c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) := EuclideanSpace.basisFun ι ℂ with hc
  set Am : ι → (H →ₗ[ℂ] H) := fun k => (adjoint ((E k).comp M₀) : H →L[ℂ] H).toLinearMap with hAm
  set An : ι → (H →ₗ[ℂ] H) := fun k => (adjoint ((E k).comp N₀) : H →L[ℂ] H).toLinearMap with hAn
  set Vm : H →ₗ[ℂ] (H ⊗[ℂ] EuclideanSpace ℂ ι) := LinearMap.krausDilation c Am with hVm
  set Vn : H →ₗ[ℂ] (H ⊗[ℂ] EuclideanSpace ℂ ι) := LinearMap.krausDilation c An with hVn
  set M : (H ⊗[ℂ] EuclideanSpace ℂ ι) →L[ℂ] H := (LinearMap.adjoint Vm).toContinuousLinearMap
    with hMdef
  set N : (H ⊗[ℂ] EuclideanSpace ℂ ι) →L[ℂ] H := (LinearMap.adjoint Vn).toContinuousLinearMap
    with hNdef
  -- `adjoint M = Vm`, `adjoint N = Vn` (as CLM).
  have hadjM : adjoint M = Vm.toContinuousLinearMap := by
    rw [hMdef, ← LinearMap.adjoint_toContinuousLinearMap, LinearMap.adjoint_adjoint]
  have hadjN : adjoint N = Vn.toContinuousLinearMap := by
    rw [hNdef, ← LinearMap.adjoint_toContinuousLinearMap, LinearMap.adjoint_adjoint]
  -- The shared linear-map identity `∑ₖ (Eₖ Y)(Eₖ X)† = krausSumₗ E (Y X†)` behind `M M†`, `N N†`,
  -- and the cross term of the pairing below.
  have hgen : ∀ X Y : H →L[ℂ] H,
      (∑ k, LinearMap.adjoint ((adjoint ((E k).comp Y) : H →L[ℂ] H) : H →ₗ[ℂ] H)
          ∘ₗ ((adjoint ((E k).comp X) : H →L[ℂ] H) : H →ₗ[ℂ] H))
        = ((krausSumₗ E (Y.comp (adjoint X)) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    intro X Y
    rw [krausSumₗ_apply, ContinuousLinearMap.toLinearMap_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.adjoint_toLinearMap, ContinuousLinearMap.adjoint_adjoint,
      ← ContinuousLinearMap.toLinearMap_comp]
    congr 1
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
  -- `M M† = krausSumₗ E ρ`, `N N† = krausSumₗ E σ`.
  have hMM : M.comp (adjoint M) = krausSumₗ E ρ := by
    apply ContinuousLinearMap.coe_injective
    rw [ContinuousLinearMap.toLinearMap_comp, hadjM, hMdef]
    simp only [LinearMap.coe_toContinuousLinearMap]
    rw [hVm, LinearMap.adjoint_krausDilation_comp_self, ← hΨ₀]
    exact hgen M₀ M₀
  have hNN : N.comp (adjoint N) = krausSumₗ E σ := by
    apply ContinuousLinearMap.coe_injective
    rw [ContinuousLinearMap.toLinearMap_comp, hadjN, hNdef]
    simp only [LinearMap.coe_toContinuousLinearMap]
    rw [hVn, LinearMap.adjoint_krausDilation_comp_self, ← hΦ₀]
    exact hgen N₀ N₀
  -- `N.hsPairing M = N₀.hsPairing M₀`.
  have hpair : N.hsPairing M = N₀.hsPairing M₀ := by
    -- The cross-term dilation sum is the operator sum of `N₀ M₀†` — collapsed by completeness.
    have hsum : (∑ k, LinearMap.adjoint (An k) ∘ₗ Am k)
        = ((krausSumₗ E (N₀.comp (adjoint M₀)) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      simp only [hAn, hAm]; exact hgen M₀ N₀
    have hLHS : N.hsPairing M
        = LinearMap.trace ℂ H ((N₀.comp (adjoint M₀) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rw [← ContinuousLinearMap.hsPairing_toLinearMap N M, LinearMap.hsPairing_eq, hMdef, hNdef]
      simp only [LinearMap.coe_toContinuousLinearMap, LinearMap.adjoint_adjoint]
      rw [hVm, hVn, LinearMap.trace_comp_comm',
        LinearMap.adjoint_krausDilation_comp_krausDilation, hsum, trace_krausSumₗ, hE,
        ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    have hRHS : N₀.hsPairing M₀
        = LinearMap.trace ℂ H ((N₀.comp (adjoint M₀) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rw [← ContinuousLinearMap.hsPairing_toLinearMap N₀ M₀, LinearMap.hsPairing_eq,
        ContinuousLinearMap.adjoint_toLinearMap, LinearMap.trace_comp_comm',
        ← ContinuousLinearMap.toLinearMap_comp]
    rw [hLHS, hRHS]
  -- Assemble.
  have key := norm_hsPairing_le_traceNorm_cfc_sqrt_mul hMM hNN
  rw [hpair] at key
  calc (cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm
      = ‖(N₀.hsPairing M₀ : ℂ)‖ := by
        rw [hval, TensorProduct.matricize_inner_eq_hsPairing b Ψ₀ Φ₀, ← hM₀, ← hN₀]
    _ ≤ _ := key

end ContinuousLinearMap
