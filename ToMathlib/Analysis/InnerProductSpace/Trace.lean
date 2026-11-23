/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import ToMathlib.Analysis.InnerProductSpace.Positive
public import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Traces in inner product spaces: additional API

This file collects additional facts about `LinearMap.trace` on finite-dimensional inner product
spaces: non-negativity and a basis-sum formula for the trace of `T† ∘ T`, non-degeneracy of the
Hilbert-Schmidt pairing, commutation of the trace with the adjoint (up to conjugation), a
spectral expansion of `trace (M ∘ T)`, continuity of the trace on `E →L[𝕜] E`, and invariance of
the trace under conjugation by a linear isometry (equivalence or otherwise).
-/

@[expose] public section

namespace LinearMap

variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open scoped InnerProductSpace ComplexOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The trace of `T† ∘ T` is non-negative in the order on `𝕜`. -/
theorem trace_adjoint_comp_self_nonneg (T : E →ₗ[𝕜] F) :
    0 ≤ (T.adjoint ∘ₗ T).trace 𝕜 E :=
  T.isPositive_adjoint_comp_self.trace_nonneg

/-- The trace of `T† ∘ T` has a basis-sum form: `re trace (T† ∘ T) = ∑ i, ‖T (b i)‖²`
for any orthonormal basis. -/
theorem re_trace_adjoint_comp_self_eq_sum_norm_sq {ι : Type*} [Fintype ι]
    (T : E →ₗ[𝕜] F) (b : OrthonormalBasis ι 𝕜 E) :
    RCLike.re ((T.adjoint ∘ₗ T).trace 𝕜 E) = ∑ i, ‖T (b i)‖ ^ 2 := by
  rw [trace_eq_sum_inner _ b, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]

/-- The basis-sum form of `re trace (T† ∘ T)` makes it manifestly non-negative. -/
theorem re_trace_adjoint_comp_self_nonneg (T : E →ₗ[𝕜] F) :
    0 ≤ RCLike.re ((T.adjoint ∘ₗ T).trace 𝕜 E) :=
  (RCLike.nonneg_iff.mp T.trace_adjoint_comp_self_nonneg).1

/-- **Non-degeneracy of the HS pairing**: a linear map `T : E →ₗ[𝕜] F` between
finite-dim inner product spaces with `trace (T† ∘ T) = 0` must be zero. Follows from
`re_trace_adjoint_comp_self_eq_sum_norm_sq`: the real part of the trace expands as
`∑ ‖T (b i)‖² = 0` over any orthonormal basis, forcing each term to vanish. -/
theorem eq_zero_of_trace_adjoint_comp_self_eq_zero (T : E →ₗ[𝕜] F)
    (h : (T.adjoint ∘ₗ T).trace 𝕜 E = 0) : T = 0 := by
  set b := stdOrthonormalBasis 𝕜 E
  refine b.toBasis.ext fun i ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, LinearMap.zero_apply, ← norm_eq_zero, ← sq_eq_zero_iff]
  have h_sum := T.re_trace_adjoint_comp_self_eq_sum_norm_sq b
  rw [h, map_zero] at h_sum
  exact (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp h_sum.symm i
    (Finset.mem_univ _)

/-- The trace and the adjoint commute up to conjugation:
`star (trace A) = trace A†` for an endomorphism `A` of a finite-dimensional inner product
space. Proof: expand both sides as `∑ i ⟪b i, A (b i)⟫`-sums over an orthonormal basis,
then conjugate-symmetry of the inner product moves the star across each summand. -/
theorem trace_adjoint (A : E →ₗ[𝕜] E) :
    star ((LinearMap.trace 𝕜 E) A) = (LinearMap.trace 𝕜 E) A.adjoint := by
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E) :=
    ⟨stdOrthonormalBasis 𝕜 E⟩
  rw [LinearMap.trace_eq_sum_inner A b, LinearMap.trace_eq_sum_inner A.adjoint b, star_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← LinearMap.adjoint_inner_left]
  exact inner_conj_symm _ _

/-- *Spectral expansion of `trace (M ∘ T)`*: for a symmetric operator `T` with eigenvalues
`λⱼ` and eigenvector ONB `bⱼ`, and any linear operator `M`, the trace of `M ∘ T` factors as
`∑ j, λⱼ * ⟪bⱼ, M bⱼ⟫`. Foundational for finite-dim quantum information theory (Born rule,
expectation values, density-matrix traces). -/
theorem IsSymmetric.trace_comp_eq_sum_eigenvalues_inner
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (M : E →ₗ[𝕜] E) :
    LinearMap.trace 𝕜 E (M ∘ₗ T) =
      ∑ j, (hT.eigenvalues hn j : 𝕜) *
        inner 𝕜 (hT.eigenvectorBasis hn j) (M (hT.eigenvectorBasis hn j)) := by
  rw [LinearMap.trace_eq_sum_inner _ (hT.eigenvectorBasis hn)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, hT.apply_eigenvectorBasis hn j,
    LinearMap.map_smul, inner_smul_right]

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The trace `(T : E →L[𝕜] E) ↦ LinearMap.trace 𝕜 E T.toLinearMap` is continuous on a
finite-dimensional inner product space. Expanded in an orthonormal basis as
`∑ i, ⟪b i, T (b i)⟫`, then continuity follows from continuity of inner product and
CLM evaluation. -/
@[fun_prop]
theorem continuous_trace :
    Continuous (fun T : E →L[𝕜] E ↦ LinearMap.trace 𝕜 E (T : E →ₗ[𝕜] E)) := by
  set b := stdOrthonormalBasis 𝕜 E
  simp_rw [LinearMap.trace_eq_sum_inner _ b, ContinuousLinearMap.coe_coe]
  exact continuous_finsetSum _ fun i _ ↦
    (continuous_const (y := b i)).inner ((ContinuousLinearMap.apply 𝕜 E (b i)).continuous)

omit [FiniteDimensional 𝕜 E] in
/-- **Trace invariance under conjugation by a linear isometry equivalence.** The trace of
`T : E →L[𝕜] E` and `e.conjStarAlgEquiv T : F →L[𝕜] F` agree. Companion to
`ContinuousLinearMap.traceNorm_conjStarAlgEquiv` (in TraceNorm.lean) at the plain-trace
level. Combines the `conjStarAlgEquiv_toLinearMap` rfl-bridge (Adjoint.lean) with
`LinearMap.trace_conj'`. -/
@[simp]
theorem trace_conjStarAlgEquiv [CompleteSpace E] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    LinearMap.trace 𝕜 F ((e.conjStarAlgEquiv T : F →L[𝕜] F) : F →ₗ[𝕜] F) =
      LinearMap.trace 𝕜 E (T : E →ₗ[𝕜] E) := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap]
  exact LinearMap.trace_conj' _ _

/-- **Trace invariance under conjugation by a (possibly non-surjective) isometry.** For
`V : E →L[𝕜] F` with `V† V = 1`, `tr_F (V A V†) = tr_E A`: trace cyclicity moves `V` past `A V†`
and `V† V = 1` collapses. The non-equiv companion to `trace_conjStarAlgEquiv`. -/
theorem trace_conj_isometry [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [CompleteSpace F]
    {V : E →L[𝕜] F} (hV : V.adjoint ∘L V = 1) (A : E →L[𝕜] E) :
    LinearMap.trace 𝕜 F (V ∘L A ∘L V.adjoint : F →L[𝕜] F).toLinearMap
      = LinearMap.trace 𝕜 E A.toLinearMap := by
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    ← LinearMap.trace_comp_comm', LinearMap.comp_assoc, ← ContinuousLinearMap.toLinearMap_comp, hV]
  congr 1

end ContinuousLinearMap
