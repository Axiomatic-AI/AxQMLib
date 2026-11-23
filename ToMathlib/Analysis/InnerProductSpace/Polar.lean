/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFC
public import ToMathlib.Analysis.InnerProductSpace.SingularValues
public import ToMathlib.Analysis.InnerProductSpace.Positive

/-!

# Polar decomposition of a finite-dimensional operator

For `T : E →L[𝕜] F` a continuous linear map between finite-dimensional inner product spaces
(possibly with `E ≠ F`), this file constructs the **polar decomposition** `T = U |T|`, where:

* `T.absoluteValue : E →L[𝕜] E` is the positive operator `|T|` on the source space such
  that `|T|² = T† ∘ T`.
* `T.polarPart : E →L[𝕜] F` is the operator `U` (a partial isometry) satisfying
  `T = U ∘L |T|`.

The construction uses the singular value decomposition `T = ∑ σᵢ • rankOne vᵢ uᵢ`
(`LinearMap.svd_apply`):
* `|T| := ∑ σᵢ • rankOne uᵢ uᵢ` (using only the right singular vectors `uᵢ ∈ E`).
* `U := ∑ rankOne vᵢ uᵢ` (sending each right singular vector `uᵢ ∈ E` to the
  corresponding left singular vector `vᵢ ∈ F`).

## Main results

* `ContinuousLinearMap.polar_decomposition`: `T = T.polarPart ∘L T.absoluteValue`.
* `ContinuousLinearMap.absoluteValue_isPositive`: `T.absoluteValue.IsPositive`.
* `ContinuousLinearMap.absoluteValue_nonneg`: `0 ≤ T.absoluteValue`.
* `ContinuousLinearMap.absoluteValue_sq`: `T.absoluteValue ∘L T.absoluteValue = T† ∘L T`,
  the canonical characterization of `|T|`.
* `ContinuousLinearMap.polarPart_isPartialIsometry`: `polarPart T ∘L (polarPart T)† ∘L
  polarPart T = polarPart T`, the partial-isometry characterization.
* `ContinuousLinearMap.polar_decomposition_unique`: if `T = U' ∘L P'` with `P'` positive,
  `U'` a partial isometry, and `kernel U' = kernel P'`, then `P' = absoluteValue T` and
  `U' = polarPart T`.

The square case `E = F` is the most common in textbook references; the general rectangular
case `E ≠ F` arises in SVD-via-polar applications and operator algebras over inhomogeneous
Hilbert spaces.

-/

@[expose] public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

open Module InnerProductSpace
open scoped InnerProduct

namespace ContinuousLinearMap

variable (T : E →L[𝕜] F)

/-- The **absolute value** `|T|` of an operator `T`, constructed from the singular
value decomposition as `∑ σᵢ • rankOne uᵢ uᵢ` where `uᵢ` are the right singular
vectors. Lives on the source space `E` since `|T| = sqrt(T† ∘ T)`. -/
noncomputable def absoluteValue : E →L[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E), (T.toLinearMap.singularValues i.val : 𝕜) •
    rankOne 𝕜 (T.toLinearMap.svdRight i) (T.toLinearMap.svdRight i)

/-- The **polar part** `U` of an operator `T : E →L[𝕜] F`, constructed from the singular value
decomposition as `∑ rankOne vᵢ uᵢ` sending each right singular vector `uᵢ ∈ E` to the
corresponding left singular vector `vᵢ ∈ F`. -/
noncomputable def polarPart : E →L[𝕜] F :=
  ∑ i : Fin (finrank 𝕜 E),
    rankOne 𝕜 (T.toLinearMap.svdLeft i) (T.toLinearMap.svdRight i)

@[simp] theorem absoluteValue_eq_sum : T.absoluteValue =
    ∑ i : Fin (finrank 𝕜 E), (T.toLinearMap.singularValues i.val : 𝕜) •
      rankOne 𝕜 (T.toLinearMap.svdRight i) (T.toLinearMap.svdRight i) := rfl

@[simp] theorem polarPart_eq_sum : T.polarPart =
    ∑ i : Fin (finrank 𝕜 E),
      rankOne 𝕜 (T.toLinearMap.svdLeft i) (T.toLinearMap.svdRight i) := rfl

/-- `|T|` diagonalizes the right singular vectors with eigenvalue `σᵢ`. -/
@[simp] theorem absoluteValue_apply_svdRight (i : Fin (finrank 𝕜 E)) :
    T.absoluteValue (T.toLinearMap.svdRight i) =
      (T.toLinearMap.singularValues i.val : 𝕜) • T.toLinearMap.svdRight i := by
  classical
  simp only [absoluteValue_eq_sum, sum_apply, _root_.smul_apply, rankOne_apply]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)]
  · rw [orthonormal_iff_ite.mp T.toLinearMap.svdRight.orthonormal i i, ite_eq_left rfl,
      smul_smul, mul_one]
  · rw [orthonormal_iff_ite.mp T.toLinearMap.svdRight.orthonormal j i, ite_eq_right hji,
      zero_smul, smul_zero]

/-- The polar part `U` sends each right singular vector to the corresponding left
singular vector. -/
@[simp] theorem polarPart_apply_svdRight (i : Fin (finrank 𝕜 E)) :
    T.polarPart (T.toLinearMap.svdRight i) = T.toLinearMap.svdLeft i := by
  classical
  simp only [polarPart_eq_sum, sum_apply, rankOne_apply]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)]
  · rw [orthonormal_iff_ite.mp T.toLinearMap.svdRight.orthonormal i i, ite_eq_left rfl, one_smul]
  · rw [orthonormal_iff_ite.mp T.toLinearMap.svdRight.orthonormal j i, ite_eq_right hji, zero_smul]

/-- The polar decomposition: `T = polarPart T ∘L absoluteValue T`. -/
theorem polar_decomposition : T = T.polarPart ∘L T.absoluteValue := by
  ext x
  have hx : x = ∑ i, ⟪T.toLinearMap.svdRight i, x⟫_𝕜 • T.toLinearMap.svdRight i :=
    (T.toLinearMap.svdRight.sum_repr' x).symm
  have hT : T x = T.toLinearMap x := rfl
  conv_rhs => rw [hx]
  simp only [coe_comp, Function.comp_apply, map_sum, map_smul,
    absoluteValue_apply_svdRight, polarPart_apply_svdRight, smul_smul]
  rw [hT, T.toLinearMap.svd_apply x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_smul, mul_comm]

/-- `|T|` is a positive operator. -/
theorem absoluteValue_isPositive : T.absoluteValue.IsPositive := by
  rw [absoluteValue_eq_sum]
  refine isPositive_sum _ fun i _ ↦ ?_
  apply IsPositive.smul_of_nonneg
  · exact isPositive_rankOne_self _
  · exact_mod_cast T.toLinearMap.singularValues_nonneg i.val

/-- `0 ≤ |T|` as a CLM. -/
theorem absoluteValue_nonneg : 0 ≤ T.absoluteValue :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr T.absoluteValue_isPositive

/-- `|T|` is self-adjoint: `|T|† = |T|`. The absolute value is a positive operator
(`absoluteValue_isPositive`), hence self-adjoint. -/
theorem adjoint_absoluteValue [CompleteSpace E] : adjoint T.absoluteValue = T.absoluteValue :=
  T.absoluteValue_isPositive.isSelfAdjoint.adjoint_eq

/-- The canonical characterization of `|T|`: `|T|² = T† ∘L T`. -/
theorem absoluteValue_sq [CompleteSpace E] [CompleteSpace F] :
    T.absoluteValue ∘L T.absoluteValue = T† ∘L T := by
  ext x
  have hx : x = ∑ i, ⟪T.toLinearMap.svdRight i, x⟫_𝕜 • T.toLinearMap.svdRight i :=
    (T.toLinearMap.svdRight.sum_repr' x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [coe_comp, Function.comp_apply, map_sum, map_smul,
    absoluteValue_apply_svdRight, adjoint_comp_self_apply_svdRight, smul_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring_nf

/-- Comp-adjoint sibling of `absoluteValue_sq`: `|T†| ∘L |T†|† = T ∘L T†`. Combines
self-adjointness of the absolute value with `absoluteValue_sq` applied to `T†`. -/
theorem absoluteValue_adjoint_comp_adjoint_eq [CompleteSpace E] [CompleteSpace F] :
    T.adjoint.absoluteValue.comp T.adjoint.absoluteValue.adjoint = T.comp T.adjoint := by
  rw [T.adjoint.absoluteValue_isPositive.isSelfAdjoint.adjoint_eq,
    T.adjoint.absoluteValue_sq, ContinuousLinearMap.adjoint_adjoint]

/-- `|T| = cfc Real.sqrt (T† ∘L T)`, the canonical CFC characterization of the absolute
value: both are the unique positive square root of `T† ∘L T`. -/
theorem absoluteValue_eq_cfc_sqrt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E] (T : E →L[ℂ] E) :
    T.absoluteValue = cfc Real.sqrt (T.adjoint ∘L T) := by
  rw [← T.absoluteValue_sq, ← ContinuousLinearMap.mul_def,
    ContinuousLinearMap.cfc_real_sqrt_mul_self_eq_self_of_nonneg T.absoluteValue_nonneg]

section PartialIsometry

variable [CompleteSpace E] [CompleteSpace F]

/-- The adjoint of `polarPart T` swaps the rank-one factors:
`(polarPart T)† = ∑ rankOne (svdRight i) (svdLeft i)`. -/
theorem polarPart_adjoint_eq_sum : T.polarPart.adjoint =
    ∑ i : Fin (finrank 𝕜 E),
      rankOne 𝕜 (T.toLinearMap.svdRight i) (T.toLinearMap.svdLeft i) := by
  rw [polarPart_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ InnerProductSpace.adjoint_rankOne _ _

/-- The adjoint of the polar part sends each left singular vector back to the corresponding
right singular vector when `σⱼ ≠ 0`, and to zero otherwise (in which case `svdLeft j = 0`
already). This is the per-basis-vector witness that `polarPart T` is a partial isometry
with initial space `span {svdRight i : σᵢ ≠ 0} = closure (range |T|)`. -/
theorem polarPart_adjoint_apply_svdLeft (j : Fin (finrank 𝕜 E)) :
    T.polarPart.adjoint (T.toLinearMap.svdLeft j) =
      if T.toLinearMap.singularValues j.val = 0 then 0 else T.toLinearMap.svdRight j := by
  classical
  rw [polarPart_adjoint_eq_sum, sum_apply]
  by_cases hj : T.toLinearMap.singularValues j.val = 0
  · rw [ite_eq_left hj, T.toLinearMap.svdLeft_eq_zero_of_singularValues_eq_zero j hj]
    simp
  · rw [ite_eq_right hj, Finset.sum_eq_single j ?_ (by simp)]
    · simp only [rankOne_apply]
      rw [T.toLinearMap.inner_svdLeft_svdLeft_full j j, ite_eq_left ⟨rfl, hj⟩, one_smul]
    · intro i _ hij
      rw [rankOne_apply, T.toLinearMap.inner_svdLeft_svdLeft_full i j,
        ite_eq_right (fun ⟨h, _⟩ ↦ hij h), zero_smul]

/-- **`polarPart T` is a partial isometry**: `U U† U = U`. This is the key
characterization that distinguishes the polar decomposition `T = U|T|` from arbitrary
factorizations — `polarPart T` acts as an isometry on the orthogonal complement of its
kernel, and is zero on its kernel. -/
theorem polarPart_isPartialIsometry :
    T.polarPart ∘L T.polarPart.adjoint ∘L T.polarPart = T.polarPart := by
  ext x
  have hx : x = ∑ i, ⟪T.toLinearMap.svdRight i, x⟫_𝕜 • T.toLinearMap.svdRight i :=
    (T.toLinearMap.svdRight.sum_repr' x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [coe_comp, Function.comp_apply, map_sum, map_smul, polarPart_apply_svdRight]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [polarPart_adjoint_apply_svdLeft]
  by_cases hi : T.toLinearMap.singularValues i.val = 0
  · rw [ite_eq_left hi, map_zero, T.toLinearMap.svdLeft_eq_zero_of_singularValues_eq_zero i hi]
  · rw [ite_eq_right hi, polarPart_apply_svdRight]

/-- **The polar part has operator norm ≤ 1**: partial isometries are contractions.
Proof via the `IsStarProjection` route: `polarPart† ∘ polarPart` is a star projection
(by `isStarProjection_adjoint_comp_self_of_partialIsometry` applied to
`polarPart_isPartialIsometry`), so its operator norm is ≤ 1; then the C*-property
`‖A‖² = ‖A† ∘ A‖` gives the bound on `‖polarPart‖`. -/
theorem polarPart_opNorm_le_one (T : E →L[𝕜] F) : ‖T.polarPart‖ ≤ 1 := by
  have hsq : ‖T.polarPart‖ ^ 2 ≤ 1 := by
    rw [sq, ← T.polarPart.norm_adjoint_comp_self]
    exact (isStarProjection_adjoint_comp_self_of_partialIsometry
      T.polarPart_isPartialIsometry).norm_le
  nlinarith [norm_nonneg T.polarPart]

end PartialIsometry

section UniquenessFoundations

variable [CompleteSpace E] [CompleteSpace F]

/-- For a partial isometry `U` (`U ∘ U† ∘ U = U`), the operator `U† ∘ U` acts as the identity
on `(ker U)ᗮ`. This is the fixed-point form of the partial-isometry projection property:
`U† ∘ U` is the orthogonal projection onto `(ker U)ᗮ`. The proof: take adjoint of the partial-
isometry equation to get `U† ∘ U ∘ U† = U†`; in finite-dim, `(ker U)ᗮ = range U†`, so
`y = U† z` for some `z`, and `U† U y = (U† U U†) z = U† z = y`. -/
theorem adjoint_apply_apply_of_partialIsometry_of_mem_orthogonal_ker
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    [CompleteSpace G] {U : E →L[𝕜] G} (hU : U ∘L U.adjoint ∘L U = U) {y : E}
    (hy : y ∈ (LinearMap.ker U.toLinearMap)ᗮ) :
    U.adjoint (U y) = y := by
  have hUd : U.adjoint ∘L U ∘L U.adjoint = U.adjoint := by
    have h := congr_arg ContinuousLinearMap.adjoint hU
    simpa [adjoint_comp, ContinuousLinearMap.comp_assoc] using h
  rw [LinearMap.orthogonal_ker] at hy
  obtain ⟨z, hz⟩ := hy
  -- LinearMap.adjoint U.toLinearMap and ContinuousLinearMap.adjoint U agree on application.
  have hz' : U.adjoint z = y := hz
  rw [← hz']
  have heq : (U.adjoint ∘L U ∘L U.adjoint) z = U.adjoint z := by rw [hUd]
  simpa [coe_comp, Function.comp_apply] using heq

/-- Specialization of the partial-isometry projection property to `polarPart T`:
`(polarPart T)† ((polarPart T) y) = y` for `y ∈ (ker (polarPart T))ᗮ`. -/
theorem polarPart_adjoint_apply_apply_of_mem_orthogonal_ker {y : E}
    (hy : y ∈ (LinearMap.ker T.polarPart.toLinearMap)ᗮ) :
    T.polarPart.adjoint (T.polarPart y) = y :=
  adjoint_apply_apply_of_partialIsometry_of_mem_orthogonal_ker T.polarPart_isPartialIsometry hy

/-- The kernel of the absolute value `|T|` equals the kernel of `T`. Proof chain:
`ker |T| = ker (|T|† ∘ |T|) = ker (|T| ∘ |T|) = ker (T† ∘ T) = ker T`, using self-adjointness
of `|T|`, the existing identity `|T|² = T† ∘ T`, and `ker_adjoint_comp_self`. -/
theorem ker_absoluteValue : T.absoluteValue.ker = T.ker := by
  have hself : T.absoluteValue.adjoint = T.absoluteValue :=
    T.absoluteValue_isPositive.isSelfAdjoint.adjoint_eq
  rw [← T.absoluteValue.ker_adjoint_comp_self, hself, T.absoluteValue_sq, T.ker_adjoint_comp_self]

omit [CompleteSpace E] [CompleteSpace F] in
/-- For `x ∈ ker (absoluteValue T)` and `i` a non-zero-singular-value index,
`⟪svdRight i, x⟫ = 0`. The right singular vectors with non-zero singular values are orthogonal
to the kernel of `|T|`. Proof: `0 = ⟪svdRight i, |T| x⟫ = ⟨|T| (svdRight i), x⟩
= σᵢ ⟨svdRight i, x⟩` via self-adjointness of `|T|` and `absoluteValue_apply_svdRight`;
cancel `σᵢ ≠ 0`. -/
theorem inner_svdRight_eq_zero_of_absoluteValue_apply_eq_zero
    {x : E} (hx : T.absoluteValue x = 0) {i : Fin (finrank 𝕜 E)}
    (hσ : T.toLinearMap.singularValues i.val ≠ 0) :
    ⟪T.toLinearMap.svdRight i, x⟫_𝕜 = 0 := by
  have h0 : ⟪T.toLinearMap.svdRight i, T.absoluteValue x⟫_𝕜 = 0 := by
    rw [hx, inner_zero_right]
  rw [← T.absoluteValue_isPositive.inner_left_eq_inner_right, absoluteValue_apply_svdRight,
    inner_smul_left, RCLike.conj_ofReal] at h0
  rcases mul_eq_zero.mp h0 with hσ' | h
  · exact absurd (by exact_mod_cast hσ' : T.toLinearMap.singularValues i.val = 0) hσ
  · exact h

omit [CompleteSpace E] [CompleteSpace F] in
/-- The polar part vanishes on the kernel of the absolute value: `|T| x = 0 → polarPart T x = 0`.
Per-summand vanishing of `polarPart T x = ∑ ⟪svdRight i, x⟫ • svdLeft i`: for `σᵢ = 0` the left
singular vector is zero; for `σᵢ ≠ 0` the inner product is zero
(`inner_svdRight_eq_zero_of_absoluteValue_apply_eq_zero`). -/
theorem polarPart_apply_eq_zero_of_absoluteValue_apply_eq_zero
    {x : E} (hx : T.absoluteValue x = 0) : T.polarPart x = 0 := by
  rw [polarPart_eq_sum, _root_.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [rankOne_apply]
  by_cases hσ : T.toLinearMap.singularValues i.val = 0
  · rw [T.toLinearMap.svdLeft_eq_zero_of_singularValues_eq_zero i hσ, smul_zero]
  · rw [T.inner_svdRight_eq_zero_of_absoluteValue_apply_eq_zero hx hσ, zero_smul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- For any factorization `T = U ∘L absoluteValue T`, the action on right singular vectors is
`T (svdRight i) = σᵢ • U (svdRight i)`. Routes through `absoluteValue_apply_svdRight`:
`T (svdRight i) = U (|T| (svdRight i)) = U (σᵢ • svdRight i) = σᵢ • U (svdRight i)`. -/
theorem apply_svdRight_of_eq_comp_absoluteValue {U : E →L[𝕜] F}
    (hU : T = U ∘L T.absoluteValue) (i : Fin (finrank 𝕜 E)) :
    T (T.toLinearMap.svdRight i) =
      (T.toLinearMap.singularValues i.val : 𝕜) • U (T.toLinearMap.svdRight i) := by
  have h := DFunLike.congr_fun hU (T.toLinearMap.svdRight i)
  rwa [ContinuousLinearMap.comp_apply, T.absoluteValue_apply_svdRight,
    ContinuousLinearMap.map_smul] at h

/-- **Uniqueness of the positive square root of `T† ∘L T`**: a positive operator `P` with
`P ∘L P = T† ∘L T` equals `|T| = absoluteValue T`. Both `P` and `|T|` are positive with the same
square, so they agree on the right-singular-vector eigenbasis of `|T|` (via
`IsPositive.apply_eq_of_isPositive_sq_apply_eq`), hence coincide. This is the canonical
characterisation used wherever a positive-times-(partial)isometry factorisation is shown to be the
polar decomposition. -/
theorem absoluteValue_eq_of_isPositive_sq {P : E →L[𝕜] E} (hP : P.IsPositive)
    (h : P ∘L P = T.adjoint ∘L T) : P = T.absoluteValue := by
  apply ContinuousLinearMap.coe_injective
  apply Basis.ext T.toLinearMap.svdRight.toBasis
  intro i
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  have h_sq : T.absoluteValue ∘L T.absoluteValue = P ∘L P := T.absoluteValue_sq.trans h.symm
  rw [hP.apply_eq_of_isPositive_sq_apply_eq h_sq (T.toLinearMap.singularValues_nonneg i.val)
      (T.absoluteValue_apply_svdRight i), ← T.absoluteValue_apply_svdRight i]

/-- **Polar decomposition uniqueness**: if `T = U' ∘L P'` with `P'` positive, `U'` a partial
isometry, and `kernel U' = kernel P'`, then `P' = absoluteValue T` and `U' = polarPart T`. The
uniqueness theorem characterizes our construction as canonical: any factorization of `T` into a
positive-times-partial-isometry with matching kernels must be the polar decomposition. -/
theorem polar_decomposition_unique {P' : E →L[𝕜] E} {U' : E →L[𝕜] F}
    (hT : T = U' ∘L P') (hP' : P'.IsPositive)
    (hU' : U' ∘L U'.adjoint ∘L U' = U')
    (hker : LinearMap.ker U'.toLinearMap = LinearMap.ker P'.toLinearMap) :
    P' = T.absoluteValue ∧ U' = T.polarPart := by
  -- Step 1: T† ∘L T = P' ∘L P' (using partial-isometry on range P').
  have hTT : T.adjoint ∘L T = P' ∘L P' := by
    rw [hT, ContinuousLinearMap.adjoint_comp, hP'.isSelfAdjoint.adjoint_eq]
    ext y
    simp only [ContinuousLinearMap.comp_apply]
    have hP'y : P' y ∈ (LinearMap.ker U'.toLinearMap)ᗮ := by
      rw [hker, ← hP'.isSymmetric.range_eq_orthogonal_ker]
      exact ⟨y, rfl⟩
    rw [adjoint_apply_apply_of_partialIsometry_of_mem_orthogonal_ker hU' hP'y]
  -- Step 2: P' = absoluteValue T (uniqueness of the positive square root of `T† ∘L T`).
  have habs : P' = T.absoluteValue := T.absoluteValue_eq_of_isPositive_sq hP' hTT.symm
  -- Step 3: U' = polarPart T (using ker U' = ker P' = ker absoluteValue T = ker polarPart T).
  have hU : U' = T.polarPart := by
    apply ContinuousLinearMap.coe_injective
    apply Basis.ext T.toLinearMap.svdRight.toBasis
    intro i
    simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
    by_cases hσ : T.toLinearMap.singularValues i.val = 0
    · -- σᵢ = 0: both U' and polarPart T vanish on svdRight i (via ker chain).
      have habs_z : T.absoluteValue (T.toLinearMap.svdRight i) = 0 := by
        rw [T.absoluteValue_apply_svdRight i, hσ, RCLike.ofReal_zero, zero_smul]
      -- ker chain: T.absoluteValue → P' (via habs) → U' (via hker).
      have hU'_z : U' (T.toLinearMap.svdRight i) = 0 := by
        have hmem : T.toLinearMap.svdRight i ∈ LinearMap.ker P'.toLinearMap := by
          rw [habs]; exact LinearMap.mem_ker.mpr habs_z
        exact LinearMap.mem_ker.mp (hker ▸ hmem)
      rw [hU'_z, T.polarPart_apply_eq_zero_of_absoluteValue_apply_eq_zero habs_z]
    · -- σᵢ ≠ 0: T u = σᵢ • U' u = σᵢ • polarPart T u via apply_svdRight_of_eq_comp_absoluteValue.
      have hT_apply := T.apply_svdRight_of_eq_comp_absoluteValue (habs ▸ hT) i
      have hT_apply' := T.apply_svdRight_of_eq_comp_absoluteValue T.polar_decomposition i
      have hσ' : (T.toLinearMap.singularValues i.val : 𝕜) ≠ 0 := by exact_mod_cast hσ
      exact smul_right_injective F hσ' (hT_apply.symm.trans hT_apply')
  exact ⟨habs, hU⟩

end UniquenessFoundations

end ContinuousLinearMap

namespace LinearMap

variable (T : E →ₗ[𝕜] F)

/-- **LM-level dual of `ContinuousLinearMap.absoluteValue`**: the absolute value `|T|` of
an LM operator. In finite dimensions, defined as the round-trip
`T.toContinuousLinearMap.absoluteValue.toLinearMap`; the CLM↔LM equivalence
(`coe_toContinuousLinearMap`) makes this the natural LM-side companion to the CLM def. -/
noncomputable def absoluteValue : E →ₗ[𝕜] E :=
  T.toContinuousLinearMap.absoluteValue.toLinearMap

/-- **LM-level dual of `ContinuousLinearMap.polarPart`**: the polar part `U` of an LM
operator `T : E →ₗ[𝕜] F`. -/
noncomputable def polarPart : E →ₗ[𝕜] F :=
  T.toContinuousLinearMap.polarPart.toLinearMap

/-- **LM-level polar decomposition**: `T = T.polarPart ∘ₗ T.absoluteValue`. Dual to the
CLM-level `ContinuousLinearMap.polar_decomposition` via the LM↔CLM round-trip
(`coe_toContinuousLinearMap`). -/
theorem polar_decomposition : T = T.polarPart ∘ₗ T.absoluteValue :=
  congrArg ContinuousLinearMap.toLinearMap T.toContinuousLinearMap.polar_decomposition

end LinearMap

namespace ContinuousLinearMap

variable (T : E →L[𝕜] F)

/-- **CLM ↔ LM bridge** for `absoluteValue`: the `toLinearMap` of the CLM-level
`absoluteValue` equals the LM-level `absoluteValue` of the coerced LM. -/
@[simp]
theorem toLinearMap_absoluteValue :
    T.absoluteValue.toLinearMap = (T : E →ₗ[𝕜] F).absoluteValue := rfl

/-- **CLM ↔ LM bridge** for `polarPart`. -/
@[simp]
theorem toLinearMap_polarPart :
    T.polarPart.toLinearMap = (T : E →ₗ[𝕜] F).polarPart := rfl

end ContinuousLinearMap
