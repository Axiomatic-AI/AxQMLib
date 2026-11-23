/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Additions to `EuclideanSpace` and `OrthonormalBasis`

Reindexing isometries `EuclideanSpace 𝕜 (Fin m ⊕ Fin n) ≃ₗᵢ EuclideanSpace 𝕜 (Fin (m + n))` and
`EuclideanSpace 𝕜 (Fin m × Fin n) ≃ₗᵢ EuclideanSpace 𝕜 (Fin (m * n))`, a nonvanishing lemma for
orthonormal basis vectors, a `single`-expansion of a Euclidean-space vector against `basisFun`,
and a cross-space generalization of `LinearIsometry.extend` to isometries landing in a
different (but equidimensional) finite-dimensional inner product space.
-/

@[expose] public section

noncomputable section

open Module

section reindexEuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Reindex `EuclideanSpace 𝕜 (Fin m ⊕ Fin n)` to `EuclideanSpace 𝕜 (Fin (m + n))` as a linear
isometric equivalence, via `finSumFinEquiv`. -/
def EuclideanSpace.reindexFinSumEquiv (m n : ℕ) :
    EuclideanSpace 𝕜 (Fin m ⊕ Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin (m + n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv

@[simp]
theorem EuclideanSpace.reindexFinSumEquiv_apply (m n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin m ⊕ Fin n)) :
    (reindexFinSumEquiv m n x : Fin (m + n) → 𝕜) =
      Equiv.piCongrLeft' (fun _ => 𝕜) finSumFinEquiv x :=
  rfl

theorem EuclideanSpace.reindexFinSumEquiv_symm (m n : ℕ) :
    (reindexFinSumEquiv (𝕜 := 𝕜) m n).symm =
      LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm := by
  simp [reindexFinSumEquiv]

@[simp]
theorem EuclideanSpace.reindexFinSumEquiv_single (m n : ℕ)
    (i : Fin m ⊕ Fin n) (v : 𝕜) :
    reindexFinSumEquiv m n (EuclideanSpace.single i v) =
      EuclideanSpace.single (finSumFinEquiv i) v :=
  EuclideanSpace.piLpCongrLeft_single finSumFinEquiv i v

/-- Reindex `EuclideanSpace 𝕜 (Fin m × Fin n)` to `EuclideanSpace 𝕜 (Fin (m * n))` as a linear
isometric equivalence, via `finProdFinEquiv`. -/
def EuclideanSpace.reindexFinProdEquiv (m n : ℕ) :
    EuclideanSpace 𝕜 (Fin m × Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin (m * n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finProdFinEquiv

@[simp]
theorem EuclideanSpace.reindexFinProdEquiv_apply (m n : ℕ)
    (x : EuclideanSpace 𝕜 (Fin m × Fin n)) :
    (reindexFinProdEquiv m n x : Fin (m * n) → 𝕜) =
      Equiv.piCongrLeft' (fun _ => 𝕜) finProdFinEquiv x :=
  rfl

theorem EuclideanSpace.reindexFinProdEquiv_symm (m n : ℕ) :
    (reindexFinProdEquiv (𝕜 := 𝕜) m n).symm =
      LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finProdFinEquiv.symm := by
  simp [reindexFinProdEquiv]

@[simp]
theorem EuclideanSpace.reindexFinProdEquiv_single (m n : ℕ) (i : Fin m × Fin n) (v : 𝕜) :
    reindexFinProdEquiv m n (EuclideanSpace.single i v) =
      EuclideanSpace.single (finProdFinEquiv i) v :=
  EuclideanSpace.piLpCongrLeft_single finProdFinEquiv i v

end reindexEuclideanSpace

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

lemma OrthonormalBasis.ne_zero [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) : b i ≠ 0 :=
  b.orthonormal.ne_zero i

/-- A Euclidean-space vector is the sum of its coordinates against the standard basis vectors:
`∑ i, x.ofLp i • single i 1 = x`. The `single`-form companion of `OrthonormalBasis.sum_repr`
for `basisFun`, convenient for expanding an operator applied to a basis vector. -/
theorem EuclideanSpace.sum_single_ofLp_eq {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace 𝕜 ι) :
    ∑ i, x.ofLp i • EuclideanSpace.single i (1 : 𝕜) = x := by
  simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
    OrthonormalBasis.sum_repr (EuclideanSpace.basisFun ι 𝕜) x

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V}
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearIsometry

/-- Dimension equality of orthogonal complements when `dim V = dim W` and `L : S →ₗᵢ W` is
an isometric embedding: `dim (range L)ᗮ = dim Sᗮ` (both equal `dim V - dim S`). -/
theorem finrank_orthogonal_range_eq_finrank_orthogonal_of_eq_finrank
    (hdim : finrank 𝕜 V = finrank 𝕜 W) (L : S →ₗᵢ[𝕜] W) :
    finrank 𝕜 (LinearMap.range L.toLinearMap)ᗮ = finrank 𝕜 Sᗮ :=
  Submodule.finrank_add_finrank_orthogonal' <| by
    rw [LinearMap.finrank_range_of_inj L.injective, S.finrank_add_finrank_orthogonal, hdim]

/-- **Canonical orthogonal-complement isometry** `Sᗮ ≃ₗᵢ (range L)ᗮ`, derived from
`stdOrthonormalBasis` on both subspaces and `finCongr` on the matching dimensions. -/
noncomputable def extendCrossOrthogonalIsometry
    (hdim : finrank 𝕜 V = finrank 𝕜 W) (L : S →ₗᵢ[𝕜] W) :
    Sᗮ ≃ₗᵢ[𝕜] (LinearMap.range L.toLinearMap)ᗮ :=
  (stdOrthonormalBasis 𝕜 Sᗮ).repr.trans
    ((stdOrthonormalBasis 𝕜 (LinearMap.range L.toLinearMap)ᗮ).reindex <|
      finCongr (finrank_orthogonal_range_eq_finrank_orthogonal_of_eq_finrank hdim L)).repr.symm

-- See the comment on `extendCross_apply` below for the `set_option` rationale.
set_option backward.isDefEq.respectTransparency false in
/-- **Underlying linear map of `LinearIsometry.extendCross`**: extends `L` to `V →ₗ[𝕜] W`
via the canonical decomposition `V = S ⊕ Sᗮ`, mapping `S` by `L` and `Sᗮ` isometrically
onto `(range L)ᗮ` via `extendCrossOrthogonalIsometry`. -/
noncomputable def extendCrossToLinearMap
    (hdim : finrank 𝕜 V = finrank 𝕜 W) (L : S →ₗᵢ[𝕜] W) : V →ₗ[𝕜] W :=
  haveI : CompleteSpace S := FiniteDimensional.completeSpace 𝕜 S
  haveI : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  L.toLinearMap.comp S.orthogonalProjectionOnto.toLinearMap +
    ((LinearMap.range L.toLinearMap)ᗮ.subtypeₗᵢ.comp
        (extendCrossOrthogonalIsometry hdim L).toLinearIsometry).toLinearMap.comp
      Sᗮ.orthogonalProjectionOnto.toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- Norm-preservation of `extendCrossToLinearMap`: by Pythagoras on the `S ⊕ Sᗮ`
decomposition of `x`, with the `S`-part mapped isometrically by `L` and the `Sᗮ`-part
mapped isometrically into the orthogonal complement of `range L`. -/
theorem norm_extendCrossToLinearMap_apply (hdim : finrank 𝕜 V = finrank 𝕜 W)
    (L : S →ₗᵢ[𝕜] W) (x : V) :
    ‖extendCrossToLinearMap hdim L x‖ = ‖x‖ := by
  have : CompleteSpace S := FiniteDimensional.completeSpace 𝕜 S
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  set p1 : V →ₗ[𝕜] S := S.orthogonalProjectionOnto.toLinearMap
  set p2 : V →ₗ[𝕜] Sᗮ := Sᗮ.orthogonalProjectionOnto.toLinearMap
  set L3 : Sᗮ →ₗᵢ[𝕜] W := ((LinearMap.range L.toLinearMap)ᗮ).subtypeₗᵢ.comp
    (extendCrossOrthogonalIsometry hdim L).toLinearIsometry
  have Mx_decomp : extendCrossToLinearMap hdim L x = L (p1 x) + L3 (p2 x) := by
    simp [extendCrossToLinearMap, p1, p2, L3]
  have Mx_orth : ⟪L (p1 x), L3 (p2 x)⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self L.toLinearMap (p1 x))
      ((extendCrossOrthogonalIsometry hdim L) (p2 x)).property
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), S.norm_sq_eq_add_norm_sq_projection x]
  simp only [sq, Mx_decomp]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
  simp only [p1, p2, L3, LinearIsometry.norm_map,
    ContinuousLinearMap.coe_coe, ← Submodule.norm_coe]

/-- **Cross-space extension**: a linear isometry `L : S →ₗᵢ[𝕜] W` from a subspace of a
finite-dimensional inner product space `V` into a finite-dimensional inner product space
`W` of the same dimension extends to a full isometry `V →ₗᵢ[𝕜] W`.

Cross-space generalization of `LinearIsometry.extend`; the same-space form is the special
case `W = V`, `hdim = rfl`. -/
noncomputable def extendCross (hdim : finrank 𝕜 V = finrank 𝕜 W)
    (L : S →ₗᵢ[𝕜] W) : V →ₗᵢ[𝕜] W where
  toLinearMap := extendCrossToLinearMap hdim L
  norm_map' := norm_extendCrossToLinearMap_apply hdim L

-- The `set_option backward.isDefEq.respectTransparency false in` annotation is needed because
-- `FiniteDimensional.completeSpace 𝕜 S` synthesis triggers an `IsUniformAddGroup ↥S` lookup that
-- defeats the default transparency mode on `Submodule` subtypes. Same workaround as on
-- the surrounding `extendCrossToLinearMap` and `norm_extendCrossToLinearMap_apply`.
set_option backward.isDefEq.respectTransparency false in
theorem extendCross_apply (hdim : finrank 𝕜 V = finrank 𝕜 W) (L : S →ₗᵢ[𝕜] W) (s : S) :
    L.extendCross hdim s = L s := by
  have : CompleteSpace S := FiniteDimensional.completeSpace 𝕜 S
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  simp [extendCross, extendCrossToLinearMap]

end LinearIsometry

end

end
