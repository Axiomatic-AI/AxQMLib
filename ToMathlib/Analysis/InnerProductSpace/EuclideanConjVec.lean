/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Componentwise conjugation on `EuclideanSpace`

`EuclideanSpace.conjVec`: componentwise complex conjugation on `EuclideanSpace 𝕜 ι`,
antilinear over `𝕜` for `𝕜 = ℂ`, norm-preserving and involutive. Reduces to the identity
for real `𝕜`. Used in the abstract Schmidt decomposition's reconstruction formula to
absorb the antilinearity of `inner` in the SVD identity `T φ = ∑ σᵢ • ⟨svdRight i, φ⟩ •
svdLeft i`.
-/

@[expose] public section

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}

namespace EuclideanSpace

/-- Componentwise complex conjugation on `EuclideanSpace 𝕜 ι`. Antilinear over `𝕜`
(for `𝕜 = ℂ`), norm-preserving, and sesquilinear-conjugate on inner products. For real
`𝕜`, this reduces to the identity.

Used as a building block for the "matrix transpose" of a linear endomorphism on
`EuclideanSpace 𝕜 ι`: for `T : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι`, the
composition `conjVec ∘ T.adjoint ∘ conjVec` is a `𝕜`-linear endomorphism whose matrix
in the canonical basis is the transpose (no conjugation) of `T`'s matrix. -/
def conjVec (v : EuclideanSpace 𝕜 ι) : EuclideanSpace 𝕜 ι :=
  WithLp.toLp 2 (fun j ↦ star (v j))

@[simp]
theorem conjVec_apply (v : EuclideanSpace 𝕜 ι) (j : ι) :
    conjVec v j = star (v j) := by
  simp [conjVec]

/-- Componentwise conjugation on the coordinate track: `(conjVec v).ofLp = star v.ofLp`. -/
@[simp]
theorem ofLp_conjVec (v : EuclideanSpace 𝕜 ι) : (conjVec v).ofLp = star v.ofLp := by
  funext j; rw [conjVec_apply]; rfl

theorem norm_conjVec [Fintype ι] (v : EuclideanSpace 𝕜 ι) : ‖conjVec v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [conjVec_apply, ← RCLike.norm_conj, RCLike.star_def, RCLike.conj_conj]

theorem inner_conjVec [Fintype ι] (u v : EuclideanSpace 𝕜 ι) :
    inner 𝕜 (conjVec u) (conjVec v) = star (inner 𝕜 u v) := by
  simp only [PiLp.inner_apply, conjVec_apply, RCLike.inner_apply', star_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [← RCLike.star_def, star_mul, star_star]
  ring

theorem orthonormal_conjVec_comp [Fintype ι] {ι' : Type*}
    {v : ι' → EuclideanSpace 𝕜 ι} (hv : Orthonormal 𝕜 v) :
    Orthonormal 𝕜 (conjVec ∘ v) := by
  refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · simpa [Function.comp_apply, norm_conjVec] using hv.norm_eq_one i
  · simp only [Function.comp_apply, inner_conjVec]
    rw [hv.inner_eq_zero hij, star_zero]

@[simp] theorem conjVec_conjVec (v : EuclideanSpace 𝕜 ι) : conjVec (conjVec v) = v := by
  ext j; simp

/-- Sliding `conjVec` across an inner product: `⟪conjVec a, b⟫ = (⟪a, conjVec b⟫)⋆`. -/
theorem conjVec_inner [Fintype ι] (a b : EuclideanSpace 𝕜 ι) :
    inner 𝕜 (conjVec a) b = star (inner 𝕜 a (conjVec b)) := by
  conv_lhs => rw [← conjVec_conjVec b]
  rw [inner_conjVec]

@[simp] theorem conjVec_add (u v : EuclideanSpace 𝕜 ι) :
    conjVec (u + v) = conjVec u + conjVec v := by
  ext j; simp

@[simp] theorem conjVec_sub (u v : EuclideanSpace 𝕜 ι) :
    conjVec (u - v) = conjVec u - conjVec v := by
  ext j; simp

/-- Componentwise conjugation is conjugate-linear: `conjVec (c • v) = star c • conjVec v`. -/
@[simp] theorem conjVec_smul (c : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    conjVec (c • v) = star c • conjVec v := by
  ext j; simp

theorem conjVec_sum {ι' : Type*} (s : Finset ι') (g : ι' → EuclideanSpace 𝕜 ι) :
    conjVec (∑ k ∈ s, g k) = ∑ k ∈ s, conjVec (g k) := by
  ext j; simp [conjVec_apply, Finset.sum_apply, star_sum]

end EuclideanSpace
