/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import ToMathlib.Analysis.InnerProductSpace.Spectrum
public import ToMathlib.Analysis.InnerProductSpace.Positive
public import ToMathlib.Algebra.BigOperators.Fin

/-!
# Singular values for finite-dimensional linear maps: additional API and the SVD

This file collects additional facts about `LinearMap.singularValues` (invariance under adjoint,
negation, scalar multiplication, and composition with linear isometries) and the singular value
decomposition itself (`LinearMap.svdRight`, `LinearMap.svdLeft`, `LinearMap.svd_apply`), together
with their `ContinuousLinearMap` counterparts.
-/

@[expose] public section

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- If the domain is subsingleton (so `finrank 𝕜 E = 0`), all singular values are zero. -/
theorem singularValues_of_subsingleton [Subsingleton E] (i : ℕ) : T.singularValues i = 0 :=
  T.singularValues_of_finrank_le (by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _)

/-- **Singular values are determined by the adjoint-comp-self operator.** If
`S.adjoint ∘ₗ S = T.adjoint ∘ₗ T`, then `S.singularValues = T.singularValues`. Common
underlying structural fact for `singularValues_neg`, `singularValues_linearIsometry_comp`,
and any future "two operators have same adjoint-comp-self ⟹ same singular values" consumer. -/
theorem singularValues_eq_of_adjoint_comp_self_eq
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {S : E →ₗ[𝕜] G} (h_op : S.adjoint ∘ₗ S = T.adjoint ∘ₗ T) :
    S.singularValues = T.singularValues := by
  have h_eig : S.isSymmetric_adjoint_comp_self.eigenvalues rfl =
      T.isSymmetric_adjoint_comp_self.eigenvalues rfl := by
    rw [IsSymmetric.eigenvalues_eq_eigenvalues_iff, h_op]
  ext i
  by_cases h : i < Module.finrank 𝕜 E
  · rw [singularValues_of_lt _ rfl h, singularValues_of_lt _ rfl h]
    exact congrArg Real.sqrt (congrFun h_eig ⟨i, h⟩)
  · rw [singularValues_of_finrank_le _ (Nat.le_of_not_lt h),
        singularValues_of_finrank_le _ (Nat.le_of_not_lt h)]

/-- **Singular values are invariant under left-composition with a linear isometry.**
For `U : F →ₗᵢ[𝕜] G` and `T : E →ₗ[𝕜] F`, the singular values of `U.toLinearMap ∘ₗ T`
agree pointwise with those of `T`. Follows from `(U ∘ₗ T).adjoint ∘ₗ (U ∘ₗ T) = T.adjoint ∘ₗ T`
(unfolding the adjoint of composition and applying `LinearIsometry.adjoint_comp_self'`)
via `singularValues_eq_of_adjoint_comp_self_eq`. -/
theorem singularValues_linearIsometry_comp
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    (U : F →ₗᵢ[𝕜] G) : (U.toLinearMap ∘ₗ T).singularValues = T.singularValues :=
  singularValues_eq_of_adjoint_comp_self_eq T <| by
    rw [LinearMap.adjoint_comp, LinearMap.comp_assoc,
      ← LinearMap.comp_assoc T U.toLinearMap U.toLinearMap.adjoint,
      U.adjoint_comp_self', LinearMap.id_comp]

/-- Singular values are invariant under negation: `(-T).singularValues = T.singularValues`.
Follows from `(-T).adjoint ∘ₗ (-T) = T.adjoint ∘ₗ T` (the two negations cancel) via
`singularValues_eq_of_adjoint_comp_self_eq`. -/
theorem singularValues_neg : (-T).singularValues = T.singularValues :=
  singularValues_eq_of_adjoint_comp_self_eq T (by simp)

/-- For a positive endomorphism `S : E →ₗ[𝕜] E`, the singular values coincide pointwise with the
eigenvalues. Follows from `sq_singularValues_fin` + `IsPositive.eigenvalues_sq` + `sq_eq_sq₀`
on the common nonneg sign. -/
theorem IsPositive.singularValues_eq_eigenvalues
    {S : E →ₗ[𝕜] E} (hS : S.IsPositive) {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    S.singularValues i = hS.isSymmetric.eigenvalues hn i := by
  refine (sq_eq_sq₀ (S.singularValues_nonneg i.val) (hS.nonneg_eigenvalues hn i)).mp ?_
  have h_op : S.adjoint ∘ₗ S = S * S := by rw [hS.isSymmetric.adjoint_eq]; rfl
  rw [sq_singularValues_fin _ hn, ← Pi.pow_apply,
    ← hS.eigenvalues_sq hn (h_op ▸ S.isSymmetric_adjoint_comp_self)]
  congr 1

/-- A `Fin n`-indexed sum of singular values equals the `Finset.range`-indexed sum over the
support, provided `n` covers the support: `finrank T.range ≤ n`. The truncated entries are zero
by `singularValues_eq_zero_iff_le_finrank_range`. -/
theorem sum_singularValues_eq_sum_range_finrank_range
    (T : E →ₗ[𝕜] F) {n : ℕ} (hr : finrank 𝕜 T.range ≤ n) :
    ∑ i : Fin n, T.singularValues i.val =
    ∑ i ∈ Finset.range (finrank 𝕜 T.range), T.singularValues i := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ T.singularValues i),
      ← Finset.sum_subset (Finset.range_subset_range.mpr hr)]
  intro x _ hnx
  rw [Finset.mem_range, not_lt] at hnx
  exact T.singularValues_eq_zero_iff_le_finrank_range.mpr hnx

/-- Scalar-multiplication scales singular values by the norm of the scalar:
`(c • T).singularValues i = ‖c‖ * T.singularValues i`. The eigenbasis of `T† ∘ T` is
also an eigenbasis of `(c • T)† ∘ (c • T) = ‖c‖² • (T† ∘ T)` with eigenvalues scaled by
`‖c‖²`; the recognition theorem (`eigenvalues_multiset_map_eq_of_eigenbasis`) plus antitone
uniqueness lifts this to pointwise equality of eigenvalues, hence singular values. -/
@[simp]
theorem singularValues_smul (c : 𝕜) (T : E →ₗ[𝕜] F) (i : ℕ) :
    (c • T).singularValues i = ‖c‖ * T.singularValues i := by
  have hSym := T.isSymmetric_adjoint_comp_self
  have hSym' := (c • T).isSymmetric_adjoint_comp_self
  by_cases hi : i < Module.finrank 𝕜 E
  · rw [singularValues_of_lt _ rfl hi, singularValues_of_lt _ rfl hi,
      ← Real.sqrt_sq (norm_nonneg c), ← Real.sqrt_mul (sq_nonneg ‖c‖)]
    refine congrArg Real.sqrt (congrFun (Eq.symm <| antitone_eq_of_multiset_map_eq
      (f := fun j ↦ ‖c‖ ^ 2 * hSym.eigenvalues rfl j)
      (fun _ _ hab ↦ by nlinarith [hSym.eigenvalues_antitone rfl hab, sq_nonneg ‖c‖])
      (hSym'.eigenvalues_antitone rfl)
      (hSym'.eigenvalues_multiset_map_eq_of_eigenbasis rfl
        (hSym.eigenvectorBasis rfl).toBasis fun j ↦ ?_)) ⟨i, hi⟩)
    rw [adjoint_comp_self_smul, LinearMap.smul_apply, OrthonormalBasis.coe_toBasis,
      hSym.apply_eigenvectorBasis rfl j, smul_smul]
    push_cast; ring_nf
  · rw [singularValues_of_finrank_le _ (Nat.le_of_not_lt hi),
      singularValues_of_finrank_le _ (Nat.le_of_not_lt hi), mul_zero]

section AdjointSection

open Polynomial

/-- Rectangular charpoly identity:
`X^(finrank F) * (T† ∘ T).charpoly = X^(finrank E) * (T ∘ T†).charpoly`.
Routes the matrix-level `Matrix.charpoly_mul_comm'` through `LinearMap.charpoly_toMatrix` using
orthonormal bases of `E` and `F`. The trailing `X`-powers absorb the differing zero-eigenvalue
multiplicities arising from the different domain sizes. -/
private lemma charpoly_adjoint_mul_pow (T : E →ₗ[𝕜] F) :
    X ^ (finrank 𝕜 F) * (T.adjoint ∘ₗ T).charpoly =
      X ^ (finrank 𝕜 E) * (T ∘ₗ T.adjoint).charpoly := by
  let bE := stdOrthonormalBasis 𝕜 E
  let bF := stdOrthonormalBasis 𝕜 F
  set A := (LinearMap.toMatrix bE.toBasis bF.toBasis) T
  set B := (LinearMap.toMatrix bF.toBasis bE.toBasis) T.adjoint
  rw [← LinearMap.charpoly_toMatrix _ bE.toBasis, LinearMap.toMatrix_comp _ bF.toBasis,
      ← LinearMap.charpoly_toMatrix _ bF.toBasis, LinearMap.toMatrix_comp _ bE.toBasis]
  simpa [Fintype.card_fin] using (Matrix.charpoly_mul_comm' A B).symm

/-- Lift `charpoly_adjoint_mul_pow` to a multiset-of-eigenvalues identity: the multiset of
eigenvalues of `T† ∘ T` padded with `finrank F` zeros equals the multiset of eigenvalues of
`T ∘ T†` padded with `finrank E` zeros. -/
private lemma eigenvalues_adjoint_multiset_eq (T : E →ₗ[𝕜] F) :
    Multiset.replicate (finrank 𝕜 F) (0 : ℝ) +
      Multiset.map (T.isSymmetric_adjoint_comp_self.eigenvalues rfl) Finset.univ.val =
    Multiset.replicate (finrank 𝕜 E) (0 : ℝ) +
      Multiset.map (T.isSymmetric_self_comp_adjoint.eigenvalues rfl) Finset.univ.val := by
  refine Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜)) ?_
  simp only [Multiset.map_add, Multiset.map_replicate, RCLike.ofReal_zero, Multiset.map_map]
  rw [← T.isSymmetric_adjoint_comp_self.roots_charpoly_eq_eigenvalues
        (rfl : finrank 𝕜 E = finrank 𝕜 E),
      ← T.isSymmetric_self_comp_adjoint.roots_charpoly_eq_eigenvalues
        (rfl : finrank 𝕜 F = finrank 𝕜 F)]
  have hne₁ : (T.adjoint ∘ₗ T).charpoly ≠ 0 := (T.adjoint ∘ₗ T).charpoly_monic.ne_zero
  have hne₂ : (T ∘ₗ T.adjoint).charpoly ≠ 0 := (T ∘ₗ T.adjoint).charpoly_monic.ne_zero
  have := congrArg Polynomial.roots (charpoly_adjoint_mul_pow T)
  rwa [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hne₁),
      Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hne₂),
      Polynomial.roots_X_pow, Polynomial.roots_X_pow,
      Multiset.nsmul_singleton, Multiset.nsmul_singleton] at this

/-- Bridge identifying `(T†.adjoint ∘ₗ T†).eigenvalues` with `(T ∘ₗ T†).eigenvalues`. The
underlying operators are equal (`adjoint_adjoint`), so their charpolys agree and
`IsSymmetric.eigenvalues_eq_eigenvalues_iff` finishes. -/
private lemma eigenvalues_adjoint_adjoint_comp (T : E →ₗ[𝕜] F) :
    T.adjoint.isSymmetric_adjoint_comp_self.eigenvalues (rfl : finrank 𝕜 F = finrank 𝕜 F) =
    T.isSymmetric_self_comp_adjoint.eigenvalues (rfl : finrank 𝕜 F = finrank 𝕜 F) := by
  rw [LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff, LinearMap.adjoint_adjoint]

/-- Multiset of singular values (padded with extra zeros): the multiset of `T.singularValues`
indexed by `Fin (finrank E)`, padded with `finrank F` zeros, equals the corresponding padded
multiset for `T†`. Derived from `eigenvalues_adjoint_multiset_eq` by applying `Real.sqrt`
elementwise. -/
private lemma singularValues_adjoint_multiset_eq (T : E →ₗ[𝕜] F) :
    Multiset.replicate (finrank 𝕜 F) (0 : ℝ) +
      Multiset.map (T.singularValues ∘ Fin.val : Fin (finrank 𝕜 E) → ℝ) Finset.univ.val =
    Multiset.replicate (finrank 𝕜 E) (0 : ℝ) +
      Multiset.map (T.adjoint.singularValues ∘ Fin.val : Fin (finrank 𝕜 F) → ℝ)
        Finset.univ.val := by
  have hsqrt := congrArg (Multiset.map Real.sqrt) (eigenvalues_adjoint_multiset_eq T)
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_replicate, Multiset.map_replicate,
      Real.sqrt_zero, Multiset.map_map, Multiset.map_map,
      ← eigenvalues_adjoint_adjoint_comp T] at hsqrt
  convert hsqrt using 2 <;>
    exact Multiset.map_congr rfl fun i _ ↦ singularValues_fin _ rfl i

/-- Padded singular-value sequence on `Fin n` (for any `n`): the first `finrank V` entries are
`T.singularValues`, the rest are zero. Reparametrized so that `paddedSV T n` and
`paddedSV T.adjoint n` share a domain `Fin n`, with `n` chosen large enough to cover both
(e.g. `n = finrank E + finrank F`). -/
private noncomputable def paddedSV {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) (n : ℕ) : Fin n → ℝ :=
  fun i ↦ if i.val < finrank 𝕜 V then T.singularValues i.val else 0

private lemma paddedSV_antitone {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) (n : ℕ) : Antitone (paddedSV T n) := by
  intro i j (hij : i.val ≤ j.val)
  simp only [paddedSV]
  split_ifs with hj hi hi
  · exact T.singularValues_antitone hij
  · exact (hi (hij.trans_lt hj)).elim
  · exact T.singularValues_nonneg _
  · exact le_refl _

private lemma paddedSV_multiset {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) {n : ℕ} (hn : finrank 𝕜 V ≤ n) :
    Multiset.map (paddedSV T n) Finset.univ.val =
    Multiset.map (T.singularValues ∘ Fin.val : Fin (finrank 𝕜 V) → ℝ) Finset.univ.val +
    Multiset.replicate (n - finrank 𝕜 V) (0 : ℝ) := by
  unfold paddedSV
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, Fin.univ_val_add, Multiset.map_add,
      Multiset.map_map, Multiset.map_map]
  refine congrArg₂ _ ?_ ?_
  · refine Multiset.map_congr rfl fun i _ ↦ ?_
    simp [Fin.castAdd, i.isLt]
  · have h_natAdd_const : ∀ i : Fin m,
        (if (Fin.natAdd (finrank 𝕜 V) i).val < finrank 𝕜 V
          then T.singularValues (Fin.natAdd (finrank 𝕜 V) i).val else 0) = 0 := by
      intro i; simp [Fin.natAdd]
    simp_rw [Function.comp_apply, h_natAdd_const]
    simp

/-- **Singular values are invariant under adjoint**: `T†.singularValues = T.singularValues`.
For rectangular `T`, the two singular-value sequences live in `ℕ →₀ ℝ` with the same support
`Finset.range (finrank T.range)` (using `finrank_range_adjoint`), and the same multiset of
positive values. Proof routes through the rectangular charpoly identity
`X^(finrank F) * (T†∘T).charpoly = X^(finrank E) * (T∘T†).charpoly`
(`Matrix.charpoly_mul_comm'` lifted via `LinearMap.charpoly_toMatrix`), then takes roots to get
a multiset equality of eigenvalues, applies `Real.sqrt` for singular values, and finally uses
`antitone_eq_of_multiset_map_eq` on `paddedSV T (finrank E + finrank F)` and
`paddedSV T.adjoint (finrank E + finrank F)` (both antitone on the same domain) to extract
pointwise equality. -/
@[simp]
theorem singularValues_adjoint (T : E →ₗ[𝕜] F) :
    T.adjoint.singularValues = T.singularValues := by
  ext n
  by_cases hE : n < finrank 𝕜 E
  · have hms : Multiset.map (paddedSV T (finrank 𝕜 E + finrank 𝕜 F)) Finset.univ.val =
        Multiset.map (paddedSV T.adjoint (finrank 𝕜 E + finrank 𝕜 F)) Finset.univ.val := by
      rw [paddedSV_multiset T (Nat.le_add_right _ _),
          paddedSV_multiset T.adjoint (Nat.le_add_left _ _),
          Nat.add_sub_cancel_left, Nat.add_sub_cancel,
          add_comm (Multiset.map _ _ : Multiset ℝ) (Multiset.replicate (finrank 𝕜 F) 0),
          add_comm (Multiset.map _ _ : Multiset ℝ) (Multiset.replicate (finrank 𝕜 E) 0)]
      exact singularValues_adjoint_multiset_eq T
    have h := congrFun (antitone_eq_of_multiset_map_eq (paddedSV_antitone T _)
        (paddedSV_antitone T.adjoint _) hms) ⟨n, hE.trans_le (Nat.le_add_right _ _)⟩
    simp only [paddedSV, hE, ite_true] at h
    by_cases hF : n < finrank 𝕜 F
    · rwa [ite_eq_left hF, eq_comm] at h
    · rw [ite_eq_right hF] at h
      rw [h, T.adjoint.singularValues_of_finrank_le (Nat.le_of_not_lt hF)]
  · rw [T.singularValues_of_finrank_le (Nat.le_of_not_lt hE),
        T.adjoint.singularValues_eq_zero_iff_le_finrank_range, finrank_range_adjoint,
        ← T.singularValues_eq_zero_iff_le_finrank_range]
    exact T.singularValues_of_finrank_le (Nat.le_of_not_lt hE)

end AdjointSection

/-- **Singular values are invariant under right-composition with a linear isometry equivalence.**
For `V : E' ≃ₗᵢ[𝕜] E` and `T : E →ₗ[𝕜] F`, the singular values of `T ∘ₗ V.toLinearMap`
agree pointwise with those of `T`. Routes via `singularValues_adjoint` + `LinearMap.adjoint_comp`
+ `LinearIsometryEquiv.adjoint_toLinearMap_eq_symm` to reduce to the left-isometric case
applied to `T.adjoint` and `V.symm.toLinearIsometry`. -/
theorem singularValues_comp_linearIsometryEquiv
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    (V : E' ≃ₗᵢ[𝕜] E) :
    (T ∘ₗ V.toLinearEquiv.toLinearMap).singularValues = T.singularValues := by
  rw [← (T ∘ₗ V.toLinearEquiv.toLinearMap).singularValues_adjoint, LinearMap.adjoint_comp,
    V.adjoint_toLinearMap_eq_symm]
  exact (T.adjoint.singularValues_linearIsometry_comp V.symm.toLinearIsometry).trans
    T.singularValues_adjoint

/-! ### Singular value decomposition

The orthonormal eigenbasis of `T† ∘ T` provides the right singular vectors of `T`.
The left singular vectors are then defined as `σᵢ⁻¹ • T uᵢ` on the support
`{i | σᵢ ≠ 0}` (and as junk values elsewhere via the inverse-of-zero convention). The
factorization theorem `LinearMap.svd_apply` expresses `T x` as a sum over this
decomposition.
-/

/-- The right singular vectors of `T`: an orthonormal eigenbasis of `T† ∘ T`. -/
noncomputable def svdRight : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

@[simp] theorem svdRight_apply (i : Fin (finrank 𝕜 E)) :
    T.svdRight i = T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i := rfl

/-- The left singular vectors of `T`: `σᵢ⁻¹ • T uᵢ` (junk when `σᵢ = 0`). -/
noncomputable def svdLeft (i : Fin (finrank 𝕜 E)) : F :=
  ((T.singularValues i.val : 𝕜))⁻¹ • T (T.svdRight i)

@[simp] theorem svdLeft_apply (i : Fin (finrank 𝕜 E)) :
    T.svdLeft i = ((T.singularValues i.val : 𝕜))⁻¹ • T (T.svdRight i) := rfl

/-- A right singular vector with zero singular value is in the kernel of `T`. -/
theorem apply_svdRight_eq_zero_of_singularValues_eq_zero (i : Fin (finrank 𝕜 E))
    (hi : T.singularValues i.val = 0) : T (T.svdRight i) = 0 := by
  have hsq : T.singularValues i.val ^ 2 = 0 := by simp [hi]
  rw [T.sq_singularValues_fin rfl] at hsq
  rw [← norm_eq_zero (E := F), ← sq_eq_zero_iff, ← inner_self_eq_norm_sq (𝕜 := 𝕜),
    ← T.adjoint_inner_right, svdRight_apply, ← LinearMap.comp_apply,
    T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i, inner_smul_right,
    hsq, RCLike.ofReal_zero, zero_mul, map_zero]

/-- A left singular vector with zero singular value is itself zero. Follows from
`svdLeft i = σᵢ⁻¹ • T (svdRight i)` and `T (svdRight i) = 0` when `σᵢ = 0`. -/
theorem svdLeft_eq_zero_of_singularValues_eq_zero (i : Fin (finrank 𝕜 E))
    (hi : T.singularValues i.val = 0) : T.svdLeft i = 0 := by
  rw [svdLeft_apply, T.apply_svdRight_eq_zero_of_singularValues_eq_zero i hi, smul_zero]

/-- The fundamental SVD relation: applying `T` to a right singular vector scales the
corresponding left singular vector by the singular value. Holds even for the junk
left vectors when `σᵢ = 0`, since both sides vanish. -/
theorem apply_svdRight (i : Fin (finrank 𝕜 E)) :
    T (T.svdRight i) = (T.singularValues i.val : 𝕜) • T.svdLeft i := by
  rw [svdLeft_apply, smul_smul]
  by_cases hi : T.singularValues i.val = 0
  · rw [T.apply_svdRight_eq_zero_of_singularValues_eq_zero i hi, smul_zero]
  · rw [mul_inv_cancel₀ (by exact_mod_cast hi), one_smul]

/-- **Inner products of left singular vectors** (unconditional form): for any `i, j`,
`⟪svdLeft i, svdLeft j⟫ = 1` iff `i = j ∧ σᵢ ≠ 0`, else `0`. Handles the σᵢ = 0 and
σⱼ = 0 degenerate cases by returning 0 (the corresponding svdLeft is zero). -/
@[simp]
theorem inner_svdLeft_svdLeft_full (i j : Fin (finrank 𝕜 E)) :
    ⟪T.svdLeft i, T.svdLeft j⟫_𝕜 = if (i = j ∧ T.singularValues i.val ≠ 0) then 1 else 0 := by
  by_cases hi : T.singularValues i.val = 0
  · rw [T.svdLeft_eq_zero_of_singularValues_eq_zero i hi, inner_zero_left,
      ite_eq_right (fun ⟨_, h⟩ ↦ h hi)]
  by_cases hj : T.singularValues j.val = 0
  · rw [T.svdLeft_eq_zero_of_singularValues_eq_zero j hj, inner_zero_right,
      ite_eq_right (fun ⟨hij, _⟩ ↦ hi (hij.symm ▸ hj))]
  -- Both σᵢ ≠ 0 and σⱼ ≠ 0: the original conditional argument.
  have hsym := T.isSymmetric_adjoint_comp_self
  simp only [svdLeft_apply, svdRight_apply, inner_smul_left, inner_smul_right]
  rw [← T.adjoint_inner_right, ← LinearMap.comp_apply,
    hsym.apply_eigenvectorBasis rfl j, inner_smul_right]
  have hij_inner : ⟪hsym.eigenvectorBasis rfl i, hsym.eigenvectorBasis rfl j⟫_𝕜 =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · simp [hij, (hsym.eigenvectorBasis rfl).orthonormal.1 j]
    · simp [hij, (hsym.eigenvectorBasis rfl).orthonormal.2 hij]
  rw [hij_inner]
  by_cases hij : i = j
  · subst hij
    have heig : (hsym.eigenvalues rfl i : 𝕜) = ((T.singularValues i.val) ^ 2 : 𝕜) := by
      rw [← T.sq_singularValues_fin rfl]; push_cast; ring
    rw [ite_eq_left rfl, mul_one, heig, map_inv₀, RCLike.conj_ofReal, ite_eq_left ⟨rfl, hi⟩]
    have hne : (T.singularValues i.val : 𝕜) ≠ 0 := by exact_mod_cast hi
    field_simp
  · rw [ite_eq_right hij, ite_eq_right (fun ⟨h, _⟩ ↦ hij h)]
    simp

/-- Left singular vectors have norm at most one: `‖svdLeft i‖ = 1` when `σᵢ ≠ 0` and
`‖svdLeft i‖ = 0` when `σᵢ = 0` (in which case `svdLeft i = 0`). -/
theorem norm_svdLeft_le_one (i : Fin (finrank 𝕜 E)) : ‖T.svdLeft i‖ ≤ 1 := by
  have : ‖T.svdLeft i‖ ^ 2 ≤ 1 := by
    rw [@norm_sq_eq_re_inner 𝕜, T.inner_svdLeft_svdLeft_full]; split_ifs <;> simp
  nlinarith [norm_nonneg (T.svdLeft i)]

/-- The left singular vectors are orthonormal on the support `{i | σᵢ ≠ 0}`. Deprecated
in favor of the unconditional `inner_svdLeft_svdLeft_full`. -/
@[deprecated inner_svdLeft_svdLeft_full +typeChanged (since := "2026-05-10")]
theorem inner_svdLeft_svdLeft (i j : Fin (finrank 𝕜 E))
    (_hi : T.singularValues i.val ≠ 0) (hj : T.singularValues j.val ≠ 0) :
    ⟪T.svdLeft i, T.svdLeft j⟫_𝕜 = if i = j then 1 else 0 := by
  rw [T.inner_svdLeft_svdLeft_full i j]
  by_cases hij : i = j
  · simp [hij, hj]
  · simp [hij]

/-- **Singular value decomposition (vector form)**: any linear map `T : E →ₗ[𝕜] F`
between finite-dimensional inner product spaces admits a factorization
`T x = ∑ σᵢ • ⟨uᵢ, x⟩ • vᵢ` where the `uᵢ` are an orthonormal eigenbasis of
`T† ∘ T` (the right singular vectors) and the `vᵢ = σᵢ⁻¹ • T uᵢ` are orthonormal
on the support `{i | σᵢ ≠ 0}` (the left singular vectors). -/
theorem svd_apply (x : E) : T x =
    ∑ i, (T.singularValues i.val : 𝕜) • ⟪T.svdRight i, x⟫_𝕜 • T.svdLeft i := by
  conv_lhs => rw [← T.svdRight.sum_repr' x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, T.apply_svdRight i, smul_smul, smul_smul, mul_comm]

/-- The largest singular value equals the operator norm:
`‖T.toContinuousLinearMap‖ = T.singularValues 0`. Proof: chain `‖T‖² = ‖T† ∘ T‖`
(the C*-property, `norm_adjoint_comp_self`) with the spectral identity
`‖T†T‖ = (T†T).eigenvalues 0` (positive self-adjoint norm = top eigenvalue,
`IsPositive.norm_eq_eigenvalues_zero`) and `(T†T).eigenvalues 0 = T.singularValues 0 ^ 2`
(`sq_singularValues_fin`). For trivial domain `E`, both sides are `0`. -/
theorem opNorm_eq_singularValues_zero : ‖T.toContinuousLinearMap‖ = T.singularValues 0 := by
  by_cases h : Nontrivial E
  · have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
    have : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
    -- ‖T‖² = (singularValues 0)² via C*-property + spectral radius + sq_singularValues_fin.
    have hadj : (T.adjoint ∘ₗ T).toContinuousLinearMap =
        T.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap := by
      ext x; simp [← LinearMap.adjoint_toContinuousLinearMap]
    have heq : ‖T.toContinuousLinearMap‖ ^ 2 = T.singularValues 0 ^ 2 := by
      rw [sq, ← T.toContinuousLinearMap.norm_adjoint_comp_self, ← hadj,
        T.isPositive_adjoint_comp_self.norm_eq_eigenvalues_zero,
        ← T.sq_singularValues_fin rfl ⟨0, Module.finrank_pos⟩]
    have := congr_arg Real.sqrt heq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (T.singularValues_nonneg 0)] at this
  · -- Subsingleton E: T = 0 and singularValues 0 = 0.
    have : Subsingleton E := not_nontrivial_iff_subsingleton.mp h
    rw [T.singularValues_of_subsingleton, Subsingleton.elim T 0]
    simp

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →L[𝕜] F)

/-! ## CLM-level singular value decomposition

CLM siblings of the LM SVD API (above). Each definition delegates to the underlying LM
form with a separate rfl-bridge `_toLinearMap` lemma. The `svd_apply` theorem at CLM level
lets consumers apply the SVD to a CLM `T : E →L[𝕜] F` directly, without inserting
`.toLinearMap` (or a `change` bridge) at every call site. Matches Mathlib's
`ContinuousLinearMap.adjoint`-vs-`LinearMap.adjoint` convention. -/

/-- The singular values of a CLM, as a finitely supported function `ℕ →₀ ℝ`.
Delegates to `LinearMap.singularValues` via `toLinearMap`. -/
noncomputable def singularValues : ℕ →₀ ℝ := T.toLinearMap.singularValues

theorem singularValues_toLinearMap :
    T.singularValues = T.toLinearMap.singularValues := rfl

/-- The right singular vectors of a CLM, as an orthonormal basis.
Delegates to `LinearMap.svdRight` via `toLinearMap`. -/
noncomputable def svdRight : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E :=
  T.toLinearMap.svdRight

theorem svdRight_toLinearMap :
    T.svdRight = T.toLinearMap.svdRight := rfl

/-- The left singular vectors of a CLM, as a finite family of vectors in the codomain.
Delegates to `LinearMap.svdLeft` via `toLinearMap`. -/
noncomputable def svdLeft (i : Fin (Module.finrank 𝕜 E)) : F :=
  T.toLinearMap.svdLeft i

theorem svdLeft_toLinearMap (i : Fin (Module.finrank 𝕜 E)) :
    T.svdLeft i = T.toLinearMap.svdLeft i := rfl

theorem singularValues_nonneg (i : ℕ) : 0 ≤ T.singularValues i :=
  T.toLinearMap.singularValues_nonneg i

theorem apply_svdRight (i : Fin (Module.finrank 𝕜 E)) :
    T (T.svdRight i) = (T.singularValues i.val : 𝕜) • T.svdLeft i :=
  T.toLinearMap.apply_svdRight i

theorem norm_svdLeft_le_one (i : Fin (Module.finrank 𝕜 E)) : ‖T.svdLeft i‖ ≤ 1 :=
  T.toLinearMap.norm_svdLeft_le_one i

/-- **Singular value decomposition (vector form), CLM level**:
`T x = ∑ i, σᵢ • ⟨svdRight i, x⟩ • svdLeft i`. The CLM-application form of
`LinearMap.svd_apply`. -/
theorem svd_apply (x : E) : T x =
    ∑ i, (T.singularValues i.val : 𝕜) • inner 𝕜 (T.svdRight i) x • T.svdLeft i :=
  T.toLinearMap.svd_apply x

/-- CLM-level apply-form for `T.adjoint ∘L T` on the right singular vectors:
`(T.adjoint ∘L T) (svdRight i) = σᵢ² • svdRight i`. The right singular vectors are eigenvectors
of `T.adjoint ∘L T` with eigenvalue `σᵢ²`. Routes through
`LinearMap.IsSymmetric.apply_eigenvectorBasis` (LM-level) via the `adjoint_toLinearMap` bridge. -/
@[simp]
theorem adjoint_comp_self_apply_svdRight [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F)
    (i : Fin (finrank 𝕜 E)) :
    (T.adjoint ∘L T) (T.toLinearMap.svdRight i) =
      ((T.toLinearMap.singularValues i.val) ^ 2 : 𝕜) • T.toLinearMap.svdRight i := by
  have hsym := T.toLinearMap.isSymmetric_adjoint_comp_self
  have hcomp : (T.adjoint ∘L T) (T.toLinearMap.svdRight i) =
      (T.adjoint.toLinearMap ∘ₗ T.toLinearMap) (T.toLinearMap.svdRight i) := by
    simp [ContinuousLinearMap.comp_apply]
  rw [hcomp, ← T.adjoint_toLinearMap, LinearMap.svdRight_apply,
    hsym.apply_eigenvectorBasis rfl, ← T.toLinearMap.sq_singularValues_fin rfl]
  push_cast
  rfl

/-- **Singular values are invariant under conjugation by a linear isometry equivalence.**
For `e : E ≃ₗᵢ[𝕜] F` and `T : E →L[𝕜] E`, the singular values of the conjugated operator
`e.conjStarAlgEquiv T : F →L[𝕜] F` agree pointwise with those of `T`. Routes through the
CLM-level adjoint–product identity (using the star-algebra structure of `conjStarAlgEquiv`)
+ `LinearEquiv.charpoly_conj` + `IsSymmetric.eigenvalues_eq_eigenvalues_iff`. -/
theorem singularValues_conjStarAlgEquiv [CompleteSpace E] [CompleteSpace F]
    (e : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    (e.conjStarAlgEquiv T).toLinearMap.singularValues = T.toLinearMap.singularValues := by
  set T' := (e.conjStarAlgEquiv T).toLinearMap
  set TL := T.toLinearMap
  have hfinrank : Module.finrank 𝕜 E = Module.finrank 𝕜 F := e.toLinearEquiv.finrank_eq
  -- CLM-level: adjoint and product preserved by the star-algebra equiv
  have h_conj_self_CLM :
      (e.conjStarAlgEquiv T).adjoint ∘L e.conjStarAlgEquiv T =
      e.conjStarAlgEquiv (T.adjoint ∘L T) := by
    have h_adj : (e.conjStarAlgEquiv T).adjoint = e.conjStarAlgEquiv T.adjoint := by
      rw [← ContinuousLinearMap.star_eq_adjoint,
          ← ContinuousLinearMap.star_eq_adjoint, map_star]
    rw [h_adj, ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul]
  -- LM lift: T'.adjoint ∘ T' = e.conj (TL.adjoint ∘ TL)
  have h_conj_self : T'.adjoint ∘ₗ T' = e.toLinearEquiv.conj (TL.adjoint ∘ₗ TL) := by
    have h := congrArg ContinuousLinearMap.toLinearMap h_conj_self_CLM
    simp only [ContinuousLinearMap.toLinearMap_comp] at h
    exact h
  -- Charpoly equality via LinearEquiv.charpoly_conj
  have h_charpoly : (T'.adjoint ∘ₗ T').charpoly = (TL.adjoint ∘ₗ TL).charpoly := by
    rw [h_conj_self]; exact e.toLinearEquiv.charpoly_conj _
  -- Eigenvalues function-level equality at the shared `n := finrank F`
  have h_eig : T'.isSymmetric_adjoint_comp_self.eigenvalues rfl =
      TL.isSymmetric_adjoint_comp_self.eigenvalues hfinrank :=
    (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff _ _ _ _).mpr h_charpoly
  -- Pointwise singular values
  ext i
  by_cases hi : i < Module.finrank 𝕜 F
  · rw [LinearMap.singularValues_of_lt _ rfl hi,
        LinearMap.singularValues_of_lt _ hfinrank hi]
    exact congrArg Real.sqrt (congrFun h_eig ⟨i, hi⟩)
  · rw [LinearMap.singularValues_of_finrank_le _ (Nat.le_of_not_lt hi),
        LinearMap.singularValues_of_finrank_le _ (hfinrank ▸ Nat.le_of_not_lt hi)]

/-- **Singular values are invariant under adjoint, CLM level**:
`T†.singularValues = T.singularValues`. The `ContinuousLinearMap` companion of
`LinearMap.singularValues_adjoint`, routed through it via the `_toLinearMap` /
`adjoint_toLinearMap` bridges. -/
theorem singularValues_adjoint [CompleteSpace E] [CompleteSpace F] :
    (ContinuousLinearMap.adjoint T).singularValues = T.singularValues := by
  rw [ContinuousLinearMap.singularValues_toLinearMap, ← ContinuousLinearMap.adjoint_toLinearMap,
    LinearMap.singularValues_adjoint, ← ContinuousLinearMap.singularValues_toLinearMap]

end ContinuousLinearMap
