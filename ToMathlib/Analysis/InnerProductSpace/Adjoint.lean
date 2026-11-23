/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Additions to `LinearMap.adjoint` / `ContinuousLinearMap.adjoint`

New lemmas about adjoints and star projections: a partial-isometry criterion for
`U† ∘L U` to be a star projection, a self-projection identity for rank-one operators,
a CLM-input form of the `LinearMap.adjoint`/`ContinuousLinearMap.adjoint` bridge, a
scaling law for the Gram operator, the range/kernel-orthogonal-complement dual of
`LinearMap.orthogonal_ker` for symmetric operators, conjugation by a (possibly
non-surjective) isometry as a non-unital star homomorphism, and transport lemmas for
`LinearIsometryEquiv.conjStarAlgEquiv`.
-/

@[expose] public section

noncomputable section

open Module RCLike InnerProductSpace
open scoped ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

/-- The "initial-space projection" of a partial isometry: for `U : E →L[𝕜] F` satisfying
the partial-isometry equation `U U† U = U`, the endomorphism `U† ∘ U : E →L[𝕜] E` is a
star projection (idempotent and self-adjoint). The dual statement (`U U† : F →L[𝕜] F` is a
star projection, the "final-space projection") follows by applying this lemma to `U†`. -/
theorem isStarProjection_adjoint_comp_self_of_partialIsometry
    {U : E →L[𝕜] F} (hU : U ∘L U.adjoint ∘L U = U) :
    IsStarProjection (U.adjoint ∘L U) where
  isIdempotentElem :=
    calc (U.adjoint ∘L U) * (U.adjoint ∘L U)
        = U.adjoint ∘L (U ∘L U.adjoint ∘L U) := by
          simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
      _ = U.adjoint ∘L U := by rw [hU]
  isSelfAdjoint := by
    rw [isSelfAdjoint_iff, star_eq_adjoint, adjoint_comp, adjoint_adjoint]

/-- A rank-one self-projector is its own measurement effect: for a unit vector `x`,
`(rankOne x x)† ∘ (rankOne x x) = rankOne x x`. -/
theorem _root_.InnerProductSpace.adjoint_rankOne_comp_self {x : E} (hx : ‖x‖ = 1) :
    adjoint (rankOne 𝕜 x x) ∘L rankOne 𝕜 x x = rankOne 𝕜 x x := by
  rw [adjoint_rankOne]
  exact (isStarProjection_rankOne_self hx).isIdempotentElem

/-- **Conjugation by an isometry as a non-unital star-algebra homomorphism.** For `V : E →L[𝕜] F`
with `V† ∘L V = 1` (an isometry, possibly non-surjective), the map `A ↦ V ∘L A ∘L V†` is a
non-unital `⋆`-algebra homomorphism `(E →L[𝕜] E) →⋆ₙₐ[𝕜] (F →L[𝕜] F)`. Multiplicativity
`V (A B) V† = (V A V†)(V B V†)` consumes `V† V = 1`; it is *non*-unital precisely because
`V V† ≠ 1` for non-surjective `V`. The non-surjective analogue of
`LinearIsometryEquiv.conjStarAlgEquiv`; the vehicle for transporting the continuous functional
calculus across `V` (`cfc_conj_isometry`). -/
noncomputable def conjIsometryₙ {V : E →L[𝕜] F} (hV : V.adjoint ∘L V = 1) :
    (E →L[𝕜] E) →⋆ₙₐ[𝕜] (F →L[𝕜] F) where
  toFun A := V ∘L A ∘L V.adjoint
  map_add' A B := by simp [comp_add, add_comp]
  map_zero' := by simp
  map_smul' c A := by simp
  map_mul' A B := by
    ext x
    simp only [mul_def, comp_apply]
    rw [← comp_apply V.adjoint V, hV, one_apply_eq_self]
  map_star' A := by
    simp only [star_eq_adjoint, adjoint_comp, adjoint_adjoint, comp_assoc]

@[simp]
theorem conjIsometryₙ_apply {V : E →L[𝕜] F} (hV : V.adjoint ∘L V = 1) (A : E →L[𝕜] E) :
    conjIsometryₙ hV A = V ∘L A ∘L V.adjoint := rfl

end ContinuousLinearMap

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- The CLM-input form of the `LinearMap.adjoint` / `ContinuousLinearMap.adjoint` bridge: the
linear-map coercion of the adjoint of a continuous linear map `T` is the adjoint of its linear-map
coercion. Upstream's `ContinuousLinearMap.adjoint_toLinearMap` states the other orientation and
derives completeness from finite-dimensionality inside the statement; this version takes
`[CompleteSpace E] [CompleteSpace F]` as instance arguments, so it applies with whichever
completeness instances are in scope. -/
theorem _root_.ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace [CompleteSpace E]
    [CompleteSpace F] (T : E →L[𝕜] F) :
    (T.adjoint : F →L[𝕜] E).toLinearMap = LinearMap.adjoint T.toLinearMap :=
  rfl

/-- The Gram operator scales by the squared norm under scalar multiplication of the operator:
`(c • T)† ∘ₗ (c • T) = ‖c‖² • (T† ∘ₗ T)`. The two scalar factors `c` and `conj c` combine to
`‖c‖²` via the C*-identity `conj c * c = ‖c‖²`. -/
theorem adjoint_comp_self_smul (c : 𝕜) (T : E →ₗ[𝕜] F) :
    (c • T).adjoint ∘ₗ (c • T) = ((‖c‖ ^ 2 : ℝ) : 𝕜) • (T.adjoint ∘ₗ T) := by
  ext x
  refine ext_inner_left 𝕜 fun y => ?_
  rw [comp_apply, adjoint_inner_right, LinearMap.smul_apply, LinearMap.smul_apply,
      inner_smul_right, inner_smul_left, LinearMap.smul_apply, comp_apply, inner_smul_right,
      adjoint_inner_right, RCLike.ofReal_pow, ← RCLike.conj_mul]
  ring

/-- For a symmetric operator on a finite-dimensional inner product space, the orthogonal
complement of the kernel equals the range. The companion to `IsSymmetric.orthogonal_range`
(which states `(range T)ᗮ = ker T`); this is the dual statement obtained by applying
`orthogonal_ker` to the symmetric operator. -/
theorem IsSymmetric.range_eq_orthogonal_ker {T : E →ₗ[𝕜] E} (hT : LinearMap.IsSymmetric T) :
    LinearMap.range T = (LinearMap.ker T)ᗮ := by
  rw [LinearMap.orthogonal_ker, hT.adjoint_eq]

end LinearMap

section linearIsometryEquiv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

namespace LinearIsometryEquiv

/-- The LinearMap coercion of `e.conjStarAlgEquiv T` is the `LinearEquiv.conj` form of
the LinearMap coercion of `T`. Definitional bridge from the CLM-level StarAlgEquiv to the
LM-level conjugation. -/
@[simp]
theorem conjStarAlgEquiv_toLinearMap (e : H ≃ₗᵢ[𝕜] K) (T : H →L[𝕜] H) :
    ((e.conjStarAlgEquiv T : K →L[𝕜] K) : K →ₗ[𝕜] K) =
      e.toLinearEquiv.conj (T : H →ₗ[𝕜] H) := rfl

/-- Conjugating a rank-one operator by a linear isometry equivalence is the same as
applying the isometry to both factors: `e.conjStarAlgEquiv (rankOne x y) = rankOne (e x) (e y)`.
The structural transport identity behind moving a rank-one operator between two Hilbert
spaces related by a linear isometry. -/
@[simp] theorem _root_.InnerProductSpace.rankOne_conjStarAlgEquiv (e : H ≃ₗᵢ[𝕜] K)
    (x y : H) : e.conjStarAlgEquiv (InnerProductSpace.rankOne 𝕜 x y) =
      InnerProductSpace.rankOne 𝕜 (e x) (e y) := by
  ext z
  simp [InnerProductSpace.rankOne_apply, ← e.inner_map_map y (e.symm z)]

/-- An operator on `H` is self-adjoint iff its image under conjugation by a linear isometry
equivalence is self-adjoint on `K`. The forward direction follows from the `StarAlgEquiv`
preserving `star`; the reverse from injectivity. -/
@[simp]
theorem conjStarAlgEquiv_isSelfAdjoint_iff (e : H ≃ₗᵢ[𝕜] K) {T : H →L[𝕜] H} :
    IsSelfAdjoint (e.conjStarAlgEquiv T) ↔ IsSelfAdjoint T := by
  simp only [_root_.IsSelfAdjoint, ← map_star e.conjStarAlgEquiv,
    EmbeddingLike.apply_eq_iff_eq]

end LinearIsometryEquiv

end linearIsometryEquiv

end
