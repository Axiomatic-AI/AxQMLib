/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Polar

/-!

# Unitary polar decomposition of a square operator

For a continuous linear operator `A : E →L[𝕜] E` on a finite-dimensional inner product space
(the *square* case `E = E`), this file upgrades the partial-isometry polar decomposition
`ToMathlib.Analysis.InnerProductSpace.Polar` (`A = A.polarPart ∘L A.absoluteValue`, where
`A.polarPart` is only a partial isometry) to the classical **unitary** polar decomposition

`A = U J = K U`,

where `U` is *unitary* (not merely a partial isometry), `J = |A| = √(A† A)` and
`K = √(A A†)` are positive operators, `J` and `K` are the *unique* positive operators
satisfying these equations, and `U` is unique when `A` is invertible. This is the statement
of the polar decomposition found in most textbooks (e.g. Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Theorem 2.3): for a square operator one can always
complete the partial isometry to a genuine unitary.

## Main results

* `ContinuousLinearMap.norm_apply_eq_norm_absoluteValue_apply`: `‖A x‖ = ‖|A| x‖`, i.e. `A`
  and its absolute value `|A|` have the same action on norms. This is the isometry that,
  after extension to the whole space, yields the unitary factor.
* `ContinuousLinearMap.exists_mem_unitary_eq_comp_absoluteValue`: there is a unitary `U`
  with `A = U ∘L |A|`. The construction restricts `A.polarPart` to `range |A|` — where it
  is an isometry — and extends it to a full isometry of `E` via `LinearIsometry.extend`,
  which in the square finite-dimensional case is a unitary.
* `ContinuousLinearMap.exists_unitary_isPositive_polar`: the full two-sided decomposition
  `A = U J = K U` with `U` unitary and `J`, `K` positive satisfying `J² = A† A`,
  `K² = A A†` (so `J = √(A† A)` and `K = √(A A†)` are the unique positive square roots).
* `ContinuousLinearMap.absoluteValue_eq_of_unitary_comp` /
  `ContinuousLinearMap.adjoint_absoluteValue_eq_of_comp_unitary`: **uniqueness of `J`, `K`** —
  any positive operator appearing as the right (resp. left) factor of a unitary factorisation
  of `A` equals `|A|` (resp. `|A†|`).
* `ContinuousLinearMap.unitary_factor_unique_of_isUnit`: **uniqueness of `U`** when `A` is
  invertible.

The right factor is `K = U J U†`; it is positive as a unitary conjugate of the positive
`J`, and `K U = U J U† U = U J = A`.

-/

@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]

open Module InnerProductSpace
open scoped InnerProduct

namespace ContinuousLinearMap

omit [FiniteDimensional 𝕜 E] in
/-- **Adjoint of a factorisation with a self-adjoint right factor**: if `A = U ∘L P` with `P`
self-adjoint, then `A† = P ∘L U†` (writing `U† = star U`). A foundational rewrite for the polar
decomposition, where the right factor `|A|` (or the positive `J`) is self-adjoint. -/
theorem adjoint_eq_comp_star_of_isSelfAdjoint {A U P : E →L[𝕜] E}
    (hP : IsSelfAdjoint P) (h : A = U ∘L P) : A.adjoint = P ∘L star U := by
  rw [h, ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, hP.star_eq]

variable (A : E →L[𝕜] E)

/-- The operator `A` and its absolute value `|A| = √(A† A)` are equinorm on every vector:
`‖A x‖ = ‖|A| x‖`. Indeed `⟪A x, A x⟫ = ⟪x, (A† ∘L A) x⟫ = ⟪x, |A|² x⟫ = ⟪|A| x, |A| x⟫`
using `absoluteValue_sq` and self-adjointness of `|A|`. This equality is exactly what makes
`A.polarPart` an isometry on `range |A|`, the fact used to build the unitary factor. -/
theorem norm_apply_eq_norm_absoluteValue_apply (x : E) : ‖A x‖ = ‖A.absoluteValue x‖ := by
  have hsa : A.absoluteValue.adjoint = A.absoluteValue :=
    A.absoluteValue_isPositive.isSelfAdjoint.adjoint_eq
  have h : ⟪A x, A x⟫_𝕜 = ⟪A.absoluteValue x, A.absoluteValue x⟫_𝕜 := by
    rw [← adjoint_inner_right A x (A x),
      ← adjoint_inner_right A.absoluteValue x (A.absoluteValue x), hsa,
      ← comp_apply, ← comp_apply, A.absoluteValue_sq]
  have hre := congrArg RCLike.re h
  rwa [inner_self_eq_norm_sq, inner_self_eq_norm_sq, sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    at hre

/-- **Left unitary polar decomposition (existence)**: for a square operator `A` there is a
*unitary* `U` with `A = U ∘L |A|`.

The construction: `A.polarPart` restricted to `S := range |A|` is an isometry (its norm-
preservation there is `norm_apply_eq_norm_absoluteValue_apply` composed with
`polar_decomposition`), so it defines `L : ↥S →ₗᵢ[𝕜] E`. Extending `L` to a full isometry
of `E` (`LinearIsometry.extend`) and upgrading to a `LinearIsometryEquiv` (equal dimension,
same space) yields a unitary `U` that agrees with `A.polarPart` on `range |A|`; hence
`U (|A| x) = A.polarPart (|A| x) = A x`. -/
theorem exists_mem_unitary_eq_comp_absoluteValue :
    ∃ U ∈ unitary (E →L[𝕜] E), A = U ∘L A.absoluteValue := by
  classical
  have hpd : ∀ x : E, A.polarPart (A.absoluteValue x) = A x := by
    intro x
    have hd := A.polar_decomposition
    conv_rhs => rw [hd]
    rfl
  set S : Submodule 𝕜 E := LinearMap.range (A.absoluteValue : E →ₗ[𝕜] E) with hS
  have hnm : ∀ s : ↥S, ‖A.polarPart (s : E)‖ = ‖(s : E)‖ := by
    rintro ⟨y, x, hx⟩
    have hyx : y = A.absoluteValue x := hx.symm
    subst hyx
    rw [hpd, A.norm_apply_eq_norm_absoluteValue_apply x]
  let L : ↥S →ₗᵢ[𝕜] E :=
    { toLinearMap := A.polarPart.toLinearMap.domRestrict S
      norm_map' := hnm }
  set W : E ≃ₗᵢ[𝕜] E := (L.extend).toLinearIsometryEquiv rfl with hW
  refine ⟨Unitary.linearIsometryEquiv.symm W, (Unitary.linearIsometryEquiv.symm W).2, ?_⟩
  have hkey : ∀ x : E,
      (Unitary.linearIsometryEquiv.symm W : E →L[𝕜] E) (A.absoluteValue x) = A x := by
    intro x
    rw [Unitary.coe_symm_linearIsometryEquiv_apply]
    have hmem : A.absoluteValue x ∈ S := ⟨x, rfl⟩
    change W (A.absoluteValue x) = A x
    rw [hW, LinearIsometry.coe_toLinearIsometryEquiv,
      show A.absoluteValue x = ((⟨A.absoluteValue x, hmem⟩ : ↥S) : E) from rfl,
      LinearIsometry.extend_apply]
    exact hpd x
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  exact (hkey x).symm

/-- **Polar decomposition — existence** (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Theorem 2.3). For a square operator `A : E →L[𝕜] E` there exist a unitary `U`
and positive operators `J`, `K` with

`A = U ∘L J = K ∘L U`,  `J ∘L J = A† ∘L A`,  `K ∘L K = A ∘L A†`.

The last two identities pin down `J = √(A† A) = |A|` and `K = √(A A†)` as the unique
positive square roots. Here `J = A.absoluteValue` and `K = U ∘L |A| ∘L U†`, positive as a
unitary conjugate of `|A|` (`IsPositive.conj_adjoint`). Uniqueness of `J`, `K`, and of `U`
(for invertible `A`) is `absoluteValue_eq_of_unitary_comp`,
`adjoint_absoluteValue_eq_of_comp_unitary`, and `unitary_factor_unique_of_isUnit`. -/
theorem exists_unitary_isPositive_polar :
    ∃ U ∈ unitary (E →L[𝕜] E), ∃ J K : E →L[𝕜] E,
      J.IsPositive ∧ K.IsPositive ∧ A = U ∘L J ∧ A = K ∘L U ∧
        J ∘L J = A.adjoint ∘L A ∧ K ∘L K = A ∘L A.adjoint := by
  obtain ⟨U, hU, hAU⟩ := A.exists_mem_unitary_eq_comp_absoluteValue
  have hstar_mul : star U * U = 1 := by simpa using Unitary.coe_star_mul_self ⟨U, hU⟩
  have hsa : IsSelfAdjoint A.absoluteValue := A.absoluteValue_isPositive.isSelfAdjoint
  refine ⟨U, hU, A.absoluteValue, U ∘L A.absoluteValue ∘L star U,
    A.absoluteValue_isPositive, ?_, hAU, ?_, A.absoluteValue_sq, ?_⟩
  · -- `K = U |A| U†` is positive: a unitary conjugate of the positive `|A|`
    -- (`star U` is defeq to `U.adjoint`).
    exact A.absoluteValue_isPositive.conj_adjoint U
  · -- `A = K U`: cancel `U† U = 1`.
    have hAU_mul : A = U * A.absoluteValue := hAU
    simp only [← ContinuousLinearMap.mul_def]
    rw [mul_assoc, mul_assoc, hstar_mul, mul_one, ← hAU_mul]
  · -- `K² = A A†`: both sides equal `U |A|² U†`.
    have hAadj : A.adjoint = A.absoluteValue ∘L star U :=
      adjoint_eq_comp_star_of_isSelfAdjoint hsa hAU
    have hLHS : (U ∘L A.absoluteValue ∘L star U) ∘L (U ∘L A.absoluteValue ∘L star U)
        = U * A.absoluteValue * A.absoluteValue * star U := by
      simp only [← ContinuousLinearMap.mul_def]
      rw [show U * (A.absoluteValue * star U) * (U * (A.absoluteValue * star U))
          = U * A.absoluteValue * (star U * U) * A.absoluteValue * star U by noncomm_ring,
        hstar_mul, mul_one]
    have hRHS : A ∘L A.adjoint = U * A.absoluteValue * A.absoluteValue * star U := by
      rw [hAadj]
      nth_rewrite 1 [hAU]
      simp only [← ContinuousLinearMap.mul_def]
      noncomm_ring
    rw [hLHS, hRHS]

/-- **Polar decomposition conjugates `A Aᴴ` to `Aᴴ A`.** There is a unitary `U` with
`A† A = U† (A A†) U`, stated as `star A * A = star U * (A * star A) * U`. From the polar
decomposition `A = U ∘L J` (`U` unitary, `J = |A|` positive with `J ∘L J = A† ∘L A`) one gets
`A A† = U (A† A) U†`, which rearranges to the claimed identity. Together with
`exists_unitary_isPositive_polar` this is the standard fact that `A† A` and `A A†` are unitarily
equivalent. -/
theorem exists_unitary_star_mul_self_eq_conj :
    ∃ U ∈ unitary (E →L[𝕜] E), star A * A = star U * (A * star A) * U := by
  obtain ⟨U, hU, J, -, hJ, -, hAUJ, -, hJ2, -⟩ := A.exists_unitary_isPositive_polar
  refine ⟨U, hU, ?_⟩
  have hstarUU : star U * U = 1 := by simpa using Unitary.coe_star_mul_self ⟨U, hU⟩
  have hJsa : star J = J := by rw [ContinuousLinearMap.star_eq_adjoint]; exact hJ.isSelfAdjoint
  have hAUJ' : A = U * J := by rwa [← ContinuousLinearMap.mul_def] at hAUJ
  have hJ2' : J * J = star A * A := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    simpa only [← ContinuousLinearMap.mul_def] using hJ2
  -- `A A† = U (A† A) U†`.
  have hAAstar : A * star A = U * (star A * A) * star U := by
    rw [← hJ2', hAUJ', star_mul, hJsa]
    simp only [mul_assoc]
  rw [hAAstar]
  -- conjugating back by `U` (unitary) recovers `A† A`.
  have hcollapse : star U * (U * (star A * A) * star U) * U = star A * A := by
    have e : star U * (U * (star A * A) * star U) * U
        = (star U * U) * (star A * A) * (star U * U) := by simp only [mul_assoc]
    rw [e]; simp only [hstarUU, one_mul, mul_one]
  exact hcollapse.symm

/-- **Uniqueness of the positive right factor `J`.** If `A = U' ∘L J'` with `U'` unitary and
`J'` positive, then `J' = |A| = √(A† A)`. Indeed `A† ∘L A = J' ∘L U'† ∘L U' ∘L J' = J' ∘L J'`
(as `U'† ∘L U' = 1`), so `J'` is a positive square root of `A† A`; the shared uniqueness lemma
`absoluteValue_eq_of_isPositive_sq` then gives `J' = |A|`. -/
theorem absoluteValue_eq_of_unitary_comp {U' J' : E →L[𝕜] E}
    (hU' : U' ∈ unitary (E →L[𝕜] E)) (hJ' : J'.IsPositive) (h : A = U' ∘L J') :
    J' = A.absoluteValue := by
  have hstarU' : star U' * U' = 1 := by simpa using Unitary.coe_star_mul_self ⟨U', hU'⟩
  have hJ'sa : IsSelfAdjoint J' := hJ'.isSelfAdjoint
  have hAA : A.adjoint ∘L A = J' ∘L J' := by
    have hAadj : A.adjoint = J' ∘L star U' := adjoint_eq_comp_star_of_isSelfAdjoint hJ'sa h
    rw [hAadj]
    nth_rewrite 1 [h]
    simp only [← ContinuousLinearMap.mul_def]
    rw [show J' * star U' * (U' * J') = J' * (star U' * U') * J' by noncomm_ring, hstarU',
      mul_one]
  exact A.absoluteValue_eq_of_isPositive_sq hJ' hAA.symm

/-- **Uniqueness of the positive left factor `K`.** If `A = K' ∘L U'` with `U'` unitary and
`K'` positive, then `K' = |A†| = √(A A†)`. This is `absoluteValue_eq_of_unitary_comp` applied
to `A†`: from `A = K' ∘L U'` we get `A† = (star U') ∘L K'` with `star U'` unitary, so `K'` is
the unique positive right factor of `A†`, namely `|A†|`. -/
theorem adjoint_absoluteValue_eq_of_comp_unitary {U' K' : E →L[𝕜] E}
    (hU' : U' ∈ unitary (E →L[𝕜] E)) (hK' : K'.IsPositive) (h : A = K' ∘L U') :
    K' = A.adjoint.absoluteValue := by
  have hsU' : star U' ∈ unitary (E →L[𝕜] E) := Unitary.star_mem hU'
  have hAadj : A.adjoint = star U' ∘L K' := by
    rw [h, ContinuousLinearMap.adjoint_comp, hK'.isSelfAdjoint.adjoint_eq,
      ← ContinuousLinearMap.star_eq_adjoint]
  exact A.adjoint.absoluteValue_eq_of_unitary_comp hsU' hK' hAadj

/-- **Uniqueness of the unitary factor `U` for invertible `A`.** If `A` is invertible and
`A = U₁ ∘L J₁ = U₂ ∘L J₂` are two unitary–positive factorisations, then `U₁ = U₂`. By
`absoluteValue_eq_of_unitary_comp` both `J₁` and `J₂` equal `|A|`, and `A` invertible forces
`|A|` invertible (`|A| = U₁† ∘L A`, a product of units), so `U₁ = U₂` by right-cancelling
`|A|` in `U₁ ∘L |A| = A = U₂ ∘L |A|`. -/
theorem unitary_factor_unique_of_isUnit {U₁ U₂ J₁ J₂ : E →L[𝕜] E} (hA : IsUnit A)
    (hU₁ : U₁ ∈ unitary (E →L[𝕜] E)) (hU₂ : U₂ ∈ unitary (E →L[𝕜] E))
    (hJ₁ : J₁.IsPositive) (hJ₂ : J₂.IsPositive)
    (h₁ : A = U₁ ∘L J₁) (h₂ : A = U₂ ∘L J₂) : U₁ = U₂ := by
  obtain rfl : J₁ = A.absoluteValue := A.absoluteValue_eq_of_unitary_comp hU₁ hJ₁ h₁
  obtain rfl : J₂ = A.absoluteValue := A.absoluteValue_eq_of_unitary_comp hU₂ hJ₂ h₂
  have hstarU₁ : IsUnit (star U₁) :=
    ⟨⟨star U₁, U₁, by simpa using Unitary.coe_star_mul_self ⟨U₁, hU₁⟩,
      by simpa using Unitary.coe_mul_star_self ⟨U₁, hU₁⟩⟩, rfl⟩
  have hstar_mul : star U₁ * U₁ = 1 := by simpa using Unitary.coe_star_mul_self ⟨U₁, hU₁⟩
  have habs_eq : A.absoluteValue = star U₁ * A := by
    conv_rhs => rw [h₁]
    simp only [← ContinuousLinearMap.mul_def]
    rw [← mul_assoc, hstar_mul, one_mul]
  have habs_unit : IsUnit A.absoluteValue := habs_eq ▸ hstarU₁.mul hA
  have heq : U₁ * A.absoluteValue = U₂ * A.absoluteValue := by
    simp only [← ContinuousLinearMap.mul_def] at h₁ h₂
    rw [← h₁, ← h₂]
  exact habs_unit.mul_left_injective heq

end ContinuousLinearMap
