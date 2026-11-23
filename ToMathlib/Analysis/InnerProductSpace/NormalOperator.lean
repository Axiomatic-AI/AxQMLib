/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.JointEigenspace
public import ToMathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The spectral theorem for normal operators

An operator `T` on a finite-dimensional complex inner product space is *normal* when it commutes
with its adjoint. Mathlib spells this with the `IsStarNormal` predicate (`Commute (star T) T`);
for `T : E →ₗ[ℂ] E` the `star` is `LinearMap.adjoint` (`LinearMap.star_eq_adjoint`), so
`IsStarNormal T` is exactly `Tᴴ * T = T * Tᴴ`. This file proves the **spectral theorem** for
such operators: `T` is normal if and only if it is diagonal with respect to some orthonormal
basis, i.e. there is an orthonormal eigenbasis.

The forward direction is obtained from the simultaneous diagonalisation of the two commuting
self-adjoint operators `A = ℜ T` (`realPart T`, i.e. `½ (T + Tᴴ)`) and `B = ℑ T`
(`imaginaryPart T`, i.e. `½ i (Tᴴ - T)`), for which `T = A + i • B`
(`realPart_add_I_smul_imaginaryPart`). Normality of `T` is exactly `Commute A B`
(`isStarNormal_iff_commute_realPart_imaginaryPart`), so
`LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute` shows that the joint
eigenspaces of `A` and `B` span the whole space. Each such joint eigenspace lies inside an
eigenspace of `T`, and the joint eigenspaces form an orthogonal family, so reindexing along the
(finite) set of eigenvalue pairs and taking a subordinate orthonormal basis produces an
orthonormal eigenbasis for `T`. The converse is a direct computation over any `RCLike` field: a
diagonal operator's adjoint is diagonal (with conjugated entries) in the same basis, and diagonal
operators commute.

Working over `ℂ` (rather than a general `RCLike` field) is essential for the forward direction:
over `ℝ` a normal operator such as a rotation need not be diagonalisable, and the Cartesian
decomposition `T = A + i • B` uses `Complex.I` in an irreducible way. The converse half holds over
any `RCLike` field.

## Main results

* `IsStarNormal.exists_orthonormalBasis_forall_apply_eq_smul`: a normal operator has an
  orthonormal eigenbasis (the existence half).
* `LinearMap.adjoint_apply_of_forall_apply_eq_smul`: the adjoint of an operator diagonal in an
  orthonormal basis is diagonal in the same basis with the conjugated eigenvalues.
* `LinearMap.isStarNormal_of_forall_apply_eq_smul`: an operator that is diagonal in an orthonormal
  basis is normal (the converse half; over any `RCLike` field).
* `LinearMap.isStarNormal_iff_exists_orthonormalBasis`: the spectral theorem, packaging the two
  halves as an equivalence.
-/

public section

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Spectral theorem for normal operators** (existence half): a normal operator `T` on a
finite-dimensional complex inner product space, i.e. one satisfying `IsStarNormal T`
(`Tᴴ * T = T * Tᴴ`), is diagonal with respect to some orthonormal basis. Concretely, there is an
orthonormal basis `b` and scalars `μ` with `T (b i) = μ i • b i` for all `i`. -/
theorem _root_.IsStarNormal.exists_orthonormalBasis_forall_apply_eq_smul
    {T : E →ₗ[ℂ] E} (hT : IsStarNormal T) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (μ : Fin (Module.finrank ℂ E) → ℂ),
      ∀ i, T (b i) = μ i • b i := by
  classical
  -- `A` and `B` are the self-adjoint real and imaginary parts of `T`, with `T = A + i • B`.
  set A : E →ₗ[ℂ] E := ↑(realPart T)
  set B : E →ₗ[ℂ] E := ↑(imaginaryPart T)
  have hAsymm : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint _).2 (realPart T).2
  have hBsymm : B.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint _).2 (imaginaryPart T).2
  -- Normality of `T` is exactly commutativity of its real and imaginary parts.
  have hAB : Commute A B := isStarNormal_iff_commute_realPart_imaginaryPart.1 hT
  have hTAB : T = A + Complex.I • B := (realPart_add_I_smul_imaginaryPart T).symm
  -- Simultaneously diagonalise `A` and `B`; then `T = A + i·B` is diagonal in the same basis.
  obtain ⟨b, μ, ν, h⟩ := hAsymm.exists_orthonormalBasis_forall_apply_eq_smul_of_commute hBsymm hAB
  refine ⟨b, fun i => μ i + Complex.I * ν i, fun i => ?_⟩
  obtain ⟨hA', hB'⟩ := h i
  simp only [hTAB, LinearMap.add_apply, LinearMap.smul_apply, hA', hB', smul_smul, add_smul]

/-- If a linear map `T` is diagonal in an orthonormal basis `b` with eigenvalues `μ`, then its
adjoint is diagonal in the same basis with the conjugated eigenvalues. -/
theorem adjoint_apply_of_forall_apply_eq_smul
    {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] {ι : Type*} [Fintype ι] {T : F →ₗ[𝕜] F}
    (b : OrthonormalBasis ι 𝕜 F) (μ : ι → 𝕜) (h : ∀ i, T (b i) = μ i • b i) (k : ι) :
    adjoint T (b k) = (starRingEnd 𝕜) (μ k) • b k := by
  classical
  refine InnerProductSpace.ext_inner_left_basis b.toBasis (fun i => ?_)
  simp only [OrthonormalBasis.coe_toBasis]
  rw [adjoint_inner_right, h i, inner_smul_left, inner_smul_right]
  rcases eq_or_ne i k with rfl | hik
  · rfl
  · rw [orthonormal_iff_ite.mp b.orthonormal i k, ite_eq_right hik, mul_zero, mul_zero]

/-- **Spectral theorem for normal operators** (converse half): an operator that is diagonal with
respect to some orthonormal basis is normal. If `T (b i) = μ i • b i` for an orthonormal basis
`b`, then `T` commutes with its adjoint, i.e. `IsStarNormal T`. This half holds over any `RCLike`
field (unlike the forward direction, which genuinely requires `ℂ`). -/
theorem isStarNormal_of_forall_apply_eq_smul
    {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] {ι : Type*} [Fintype ι] {T : F →ₗ[𝕜] F}
    (b : OrthonormalBasis ι 𝕜 F) (μ : ι → 𝕜)
    (h : ∀ i, T (b i) = μ i • b i) : IsStarNormal T := by
  classical
  -- Both `adjoint T * T` and `T * adjoint T` act as `|μ i|² • b i`, hence agree.
  have hcomm : Commute (adjoint T) T := by
    refine b.toBasis.ext (fun i => ?_)
    rw [OrthonormalBasis.coe_toBasis, mul_apply_eq_comp, mul_apply_eq_comp, h i, map_smul,
      adjoint_apply_of_forall_apply_eq_smul b μ h i, map_smul, h i, smul_smul, smul_smul, mul_comm]
  exact ⟨hcomm⟩

/-- **Spectral theorem for normal operators.** An operator `T` on a finite-dimensional complex
inner product space is normal (`IsStarNormal T`, i.e. it commutes with its adjoint) if and only if
it is diagonal with respect to some orthonormal basis. -/
theorem isStarNormal_iff_exists_orthonormalBasis {T : E →ₗ[ℂ] E} :
    IsStarNormal T ↔
      ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (μ : Fin (Module.finrank ℂ E) → ℂ),
        ∀ i, T (b i) = μ i • b i :=
  ⟨fun hT => hT.exists_orthonormalBasis_forall_apply_eq_smul,
    fun ⟨b, μ, h⟩ => isStarNormal_of_forall_apply_eq_smul b μ h⟩

end LinearMap

end
