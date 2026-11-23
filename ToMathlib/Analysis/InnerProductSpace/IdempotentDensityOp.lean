/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Density
public import ToMathlib.Analysis.InnerProductSpace.Spectrum

/-!

# Idempotent density operators

A density operator on a finite-dimensional inner product space that is also idempotent
equals a rank-one self-projector `rankOne 𝕜 v v` for some unit vector `v`. This file
proves the biconditional:

`ρ.IsDensityOp → (IsIdempotentElem ρ ↔ ∃ v, ‖v‖ = 1 ∧ ρ = rankOne 𝕜 v v)`

The forward direction uses the spectral expansion of `ρ` (positive ⇒ self-adjoint, so
diagonalizable with real eigenvalues): combined with `ρ² = ρ`, each eigenvalue squares to
itself and is therefore in `{0, 1}`; combined with `trace ρ = 1` and non-negativity, exactly
one eigenvalue is `1` and the rest are `0`; the spectral sum then collapses to a single
`rankOne 𝕜 (b i₀) (b i₀)` term.

The reverse direction is the existing `isIdempotentElem_rankOne_self`.

## Main results

* `ContinuousLinearMap.IsDensityOp.isIdempotentElem_iff`: the biconditional.
* `ContinuousLinearMap.IsDensityOp.exists_eq_rankOne_of_idempotent`: the forward
  direction, unpacked.

The supporting lemmas about eigenvalues of symmetric idempotents
(`IsIdempotentElem.eigenvalues_sq_eq_self`, `IsIdempotentElem.eigenvalues_zero_or_one`)
live in [`Spectrum.lean`](../Mathlib/Analysis/InnerProductSpace/Spectrum.lean) — they
characterize the spectrum of orthogonal projections and have no density-operator
dependency.

-/

@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

open Module InnerProductSpace
open scoped ComplexOrder

namespace ContinuousLinearMap

namespace IsDensityOp

variable {ρ : E →L[𝕜] E}

/-- A density operator that is idempotent equals a rank-one self-projector for some
unit vector. -/
theorem exists_eq_rankOne_of_idempotent (hρ : ρ.IsDensityOp) (hidem : IsIdempotentElem ρ) :
    ∃ v : E, ‖v‖ = 1 ∧ ρ = rankOne 𝕜 v v := by
  have hn : finrank 𝕜 E = finrank 𝕜 E := rfl
  have hsa : IsSelfAdjoint ρ := hρ.isPositive.isSelfAdjoint
  set b := hsa.isSymmetric.eigenvectorBasis hn
  set lam := fun i ↦ hsa.isSymmetric.eigenvalues hn i
  have hbool : ∀ i, lam i = 0 ∨ lam i = 1 :=
    fun i ↦ (ContinuousLinearMap.IsIdempotentElem.toLinearMap hidem).eigenvalues_zero_or_one
      hsa.isSymmetric hn i
  have hsum : ∑ i, lam i = 1 := hρ.eigenvalues_sum_eq_one hn
  have hnn : ∀ i, 0 ≤ lam i := fun i ↦ hρ.eigenvalues_nonneg hn i
  -- Exactly one eigenvalue is 1; the rest are 0.
  obtain ⟨i₀, hi₀, h_others⟩ : ∃ i₀, lam i₀ = 1 ∧ ∀ i, i ≠ i₀ → lam i = 0 := by
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, lam i₀ = 1 := by
      by_contra h; push Not at h
      exact one_ne_zero <| hsum.symm.trans <|
        Finset.sum_eq_zero fun i _ ↦ (hbool i).resolve_right (h i)
    refine ⟨i₀, hi₀, fun i hi ↦ ?_⟩
    have h_zero_sum : ∑ j ∈ Finset.univ.erase i₀, lam j = 0 := by
      have := Finset.add_sum_erase _ lam (Finset.mem_univ i₀); linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hnn j).mp h_zero_sum i
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  -- Spectral expansion collapses to a single rankOne term (cast to 𝕜 for the smul).
  refine ⟨b i₀, b.orthonormal.1 i₀, ?_⟩
  have hi₀' : (hsa.isSymmetric.eigenvalues hn i₀ : 𝕜) = 1 := by exact_mod_cast hi₀
  have h_others' : ∀ j, j ≠ i₀ → (hsa.isSymmetric.eigenvalues hn j : 𝕜) = 0 :=
    fun j hj ↦ by exact_mod_cast h_others j hj
  rw [hsa.spectral_sum hn, Finset.sum_eq_single i₀ (fun j _ hji ↦ ?_) (by simp)]
  · rw [hi₀', one_smul]
  · rw [h_others' j hji, zero_smul]

/-- A density operator is a rank-one self-projector for some unit vector iff it is
idempotent. -/
theorem isIdempotentElem_iff (hρ : ρ.IsDensityOp) :
    IsIdempotentElem ρ ↔ ∃ v : E, ‖v‖ = 1 ∧ ρ = rankOne 𝕜 v v := by
  refine ⟨exists_eq_rankOne_of_idempotent hρ, ?_⟩
  rintro ⟨v, hv, rfl⟩
  exact isIdempotentElem_rankOne_self hv

omit [CompleteSpace E] in
/-- **Purity as a sum of squared eigenvalues.** For a density operator `ρ`, the real part of
`tr(ρ²)` equals the sum of the squares of its eigenvalues. Combines the Hilbert–Schmidt identity
`re (hsPairing T T) = re tr(T ∘ₗ T)` with `re (hsPairing T T) = ∑ ‖T (bᵢ)‖²` over the eigenvector
basis, where `‖ρ (bᵢ)‖² = λᵢ²`. -/
theorem re_trace_mul_self_eq_sum_eigenvalues_sq (hρ : ρ.IsDensityOp) {n : ℕ}
    (hn : finrank 𝕜 E = n) :
    RCLike.re (LinearMap.trace 𝕜 E ((ρ * ρ : E →L[𝕜] E) : E →ₗ[𝕜] E)) =
      ∑ i, (hρ.isSymmetric.eigenvalues hn i) ^ 2 := by
  have hcoe : ((ρ * ρ : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = (ρ : E →ₗ[𝕜] E) ∘ₗ (ρ : E →ₗ[𝕜] E) := rfl
  rw [hcoe, ← LinearMap.re_hsPairing_self_eq_re_trace_comp_self_of_isSymmetric hρ.isSymmetric,
    LinearMap.re_hsPairing_self_eq_sum_norm_sq (ρ : E →ₗ[𝕜] E) (hρ.isSymmetric.eigenvectorBasis hn)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hρ.isSymmetric.apply_eigenvectorBasis hn i, norm_smul, RCLike.norm_ofReal,
    (hρ.isSymmetric.eigenvectorBasis hn).orthonormal.1 i, mul_one, sq_abs]

omit [CompleteSpace E] in
/-- **Purity is at most one** (N&C Exercise 2.71, the bound). For a density operator `ρ`,
`re tr(ρ²) ≤ 1`: writing `tr(ρ²) = ∑ λᵢ²` and using `0 ≤ λᵢ ≤ 1` gives `λᵢ² ≤ λᵢ`, so
`∑ λᵢ² ≤ ∑ λᵢ = 1`. -/
theorem re_trace_mul_self_le_one (hρ : ρ.IsDensityOp) :
    RCLike.re (LinearMap.trace 𝕜 E ((ρ * ρ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ≤ 1 := by
  have hn : finrank 𝕜 E = finrank 𝕜 E := rfl
  rw [re_trace_mul_self_eq_sum_eigenvalues_sq hρ hn]
  refine (Finset.sum_le_sum fun i _ => ?_).trans (le_of_eq (hρ.eigenvalues_sum_eq_one hn))
  nlinarith [hρ.eigenvalues_nonneg hn i, hρ.eigenvalues_le_one hn i]

omit [CompleteSpace E] in
/-- **Purity equals one iff idempotent** (N&C Exercise 2.71, the equality case). For a density
operator `ρ`, `re tr(ρ²) = 1` iff `ρ` is idempotent. Forward: `∑ λᵢ² = 1 = ∑ λᵢ` with `0 ≤ λᵢ ≤ 1`
forces `λᵢ² = λᵢ`, and a self-adjoint operator whose eigenvalues each satisfy `λ² = λ` agrees with
`ρ²` on its eigenbasis, so `ρ² = ρ`. Reverse: `ρ² = ρ` gives `tr(ρ²) = tr ρ = 1`. -/
theorem re_trace_mul_self_eq_one_iff_isIdempotentElem (hρ : ρ.IsDensityOp) :
    RCLike.re (LinearMap.trace 𝕜 E ((ρ * ρ : E →L[𝕜] E) : E →ₗ[𝕜] E)) = 1
      ↔ IsIdempotentElem ρ := by
  have hn : finrank 𝕜 E = finrank 𝕜 E := rfl
  constructor
  · intro h
    rw [re_trace_mul_self_eq_sum_eigenvalues_sq hρ hn] at h
    have hsum : ∑ i, hρ.isSymmetric.eigenvalues hn i = 1 := hρ.eigenvalues_sum_eq_one hn
    have hkey : ∀ i, (hρ.isSymmetric.eigenvalues hn i) ^ 2 = hρ.isSymmetric.eigenvalues hn i := by
      have hnonneg : ∀ i ∈ Finset.univ,
          0 ≤ hρ.isSymmetric.eigenvalues hn i - (hρ.isSymmetric.eigenvalues hn i) ^ 2 :=
        fun i _ => by nlinarith [hρ.eigenvalues_nonneg hn i, hρ.eigenvalues_le_one hn i]
      have hz : ∑ i, (hρ.isSymmetric.eigenvalues hn i
          - (hρ.isSymmetric.eigenvalues hn i) ^ 2) = 0 := by
        rw [Finset.sum_sub_distrib, hsum, h]; ring
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz i (Finset.mem_univ i)
      linarith
    set b := hρ.isSymmetric.eigenvectorBasis hn with hb
    have happ : ∀ i, (ρ : E →ₗ[𝕜] E) (b i) = (hρ.isSymmetric.eigenvalues hn i : 𝕜) • b i :=
      fun i => hρ.isSymmetric.apply_eigenvectorBasis hn i
    change (ρ * ρ : E →L[𝕜] E) = ρ
    apply ContinuousLinearMap.coe_injective
    change (ρ : E →ₗ[𝕜] E) ∘ₗ (ρ : E →ₗ[𝕜] E) = (ρ : E →ₗ[𝕜] E)
    refine b.toBasis.ext fun i => ?_
    simp only [OrthonormalBasis.coe_toBasis]
    rw [LinearMap.comp_apply, happ i, map_smul, happ i, smul_smul, ← RCLike.ofReal_mul,
      ← pow_two, hkey i]
  · intro hidem
    rw [show (ρ * ρ : E →L[𝕜] E) = ρ from hidem, hρ.trace_eq_one, RCLike.one_re]

/-- **Purity criterion for pure states** (N&C Exercise 2.71). For a density operator `ρ`,
`re tr(ρ²) = 1` iff `ρ` is a rank-one self-projector `|v⟩⟨v|` for some unit vector `v` — i.e. a
pure state. Combines `re_trace_mul_self_eq_one_iff_isIdempotentElem` with the idempotent-density
characterization `isIdempotentElem_iff`. -/
theorem re_trace_mul_self_eq_one_iff_exists_rankOne (hρ : ρ.IsDensityOp) :
    RCLike.re (LinearMap.trace 𝕜 E ((ρ * ρ : E →L[𝕜] E) : E →ₗ[𝕜] E)) = 1
      ↔ ∃ v : E, ‖v‖ = 1 ∧ ρ = rankOne 𝕜 v v :=
  (re_trace_mul_self_eq_one_iff_isIdempotentElem hρ).trans hρ.isIdempotentElem_iff

end IsDensityOp

end ContinuousLinearMap
