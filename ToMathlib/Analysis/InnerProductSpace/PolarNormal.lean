/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.LinearMap
public import ToMathlib.Analysis.InnerProductSpace.PolarUnitary
public import ToMathlib.Analysis.InnerProductSpace.NormalOperator

/-!

# Polar decomposition of a normal operator in outer-product form

For a *normal* operator `A` on a finite-dimensional complex inner product space, the spectral
theorem writes `A` diagonally in an orthonormal eigenbasis `{bᵢ}`:

`A = ∑ᵢ μᵢ • |bᵢ⟩⟨bᵢ|`  (`ToMathlib.Analysis.InnerProductSpace.NormalOperator`).

This file expresses the polar decomposition `A = U J = J U` (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Theorem 2.3) of such an `A` in this **outer-product
representation** (N&C Exercise 2.49): both polar factors are diagonal in the *same* eigenbasis,

`J = |A| = ∑ᵢ ‖μᵢ‖ • |bᵢ⟩⟨bᵢ|`,   `U = ∑ᵢ phase(μᵢ) • |bᵢ⟩⟨bᵢ|`,

where each eigenvalue is split into modulus and phase, `μᵢ = ‖μᵢ‖ · phase(μᵢ)`. Because `J`
and `U` share `A`'s eigenbasis they commute, so the left and right polar decompositions
`A = U J` and `A = J U` coincide — the special feature of the normal case.

## The diagonal operator

The reusable vehicle is `OrthonormalBasis.diagonalOperator b w = ∑ᵢ wᵢ • |bᵢ⟩⟨bᵢ|`, the operator
diagonal in an orthonormal basis `b` with prescribed diagonal entries `w`. Its algebra makes the
polar decomposition immediate:

* `OrthonormalBasis.diagonalOperator_comp`: `diag w ∘L diag w' = diag (w * w')` — composition is
  pointwise multiplication of diagonals;
* `OrthonormalBasis.diagonalOperator_adjoint`: `(diag w)† = diag (star w)`;
* `OrthonormalBasis.diagonalOperator_one`: `diag 1 = 1`;
* `OrthonormalBasis.diagonalOperator_mem_unitary`: `diag w` is unitary when `‖wᵢ‖ = 1`;
* `OrthonormalBasis.diagonalOperator_isPositive_of_nonneg`: `diag w` is positive when `0 ≤ wᵢ`;
* `OrthonormalBasis.diagonalOperator_isStarNormal`: every `diag w` is normal.

## Main results (N&C Exercise 2.49)

For `A = b.diagonalOperator μ`:

* `OrthonormalBasis.diagonalOperator_eq_phase_comp_norm`: `A = U ∘L J` (left polar decomposition);
* `OrthonormalBasis.diagonalOperator_eq_norm_comp_phase`: `A = J ∘L U` (right polar decomposition);
* `OrthonormalBasis.diagonalOperator_phase_mem_unitary`: `U` is unitary;
* `OrthonormalBasis.diagonalOperator_norm_isPositive`: `J` is positive;
* `OrthonormalBasis.diagonalOperator_norm_eq_absoluteValue`: `J = |A| = √(A† A)`, identifying the
  positive factor with the canonical one of N&C Theorem 2.3 (via
  `ContinuousLinearMap.absoluteValue_eq_of_unitary_comp`).

`OrthonormalBasis.diagonalOperator_isStarNormal` supplies the converse half — that these
diagonal operators are exactly the normal ones — so the forward spectral theorem
`IsStarNormal.exists_orthonormalBasis_forall_apply_eq_smul` places every normal operator in this
outer-product form.

-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap
open scoped ComplexConjugate ComplexOrder

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **phase** (unit-modulus part) of a scalar: `phase z = z / ‖z‖` for `z ≠ 0`, and
`phase 0 = 1`. It satisfies `‖phase z‖ = 1` (`RCLike.norm_phase`) and recovers `z` from its
modulus, `phase z · ‖z‖ = z` (`RCLike.phase_mul_norm`); together these give the polar form
`z = ‖z‖ · phase z` of a complex number. -/
noncomputable def phase (z : 𝕜) : 𝕜 := if z = 0 then 1 else (‖z‖ : 𝕜)⁻¹ * z

@[simp] theorem phase_zero : phase (0 : 𝕜) = 1 := by simp [phase]

/-- The phase of a scalar has unit modulus. -/
theorem norm_phase (z : 𝕜) : ‖phase z‖ = 1 := by
  rw [phase]
  split_ifs with h
  · simp
  · rw [norm_mul, norm_inv, norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

/-- Recovering a scalar from its modulus and phase: `phase z · ‖z‖ = z`. -/
theorem phase_mul_norm (z : 𝕜) : phase z * (‖z‖ : 𝕜) = z := by
  rw [phase]
  split_ifs with h
  · subst h; simp
  · have hz : (‖z‖ : 𝕜) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
    rw [mul_right_comm, inv_mul_cancel₀ hz, one_mul]

/-- Recovering a scalar from its modulus and phase: `‖z‖ · phase z = z`. -/
theorem norm_mul_phase (z : 𝕜) : (‖z‖ : 𝕜) * phase z = z := by
  rw [mul_comm]; exact phase_mul_norm z

end RCLike

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The operator **diagonal in an orthonormal basis** `b` with diagonal entries `w`:
`diagonalOperator b w = ∑ᵢ wᵢ • |bᵢ⟩⟨bᵢ|`. Conjugating any operator diagonal in `b` reduces to
manipulating its scalar diagonal `w`; the spectral decomposition of a normal operator is exactly
`A = b.diagonalOperator μ` for its eigenvalues `μ`. -/
noncomputable def diagonalOperator (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜) : E →L[𝕜] E :=
  ∑ i, w i • rankOne 𝕜 (b i) (b i)

/-- The diagonal operator with all-ones diagonal is the identity. -/
@[simp] theorem diagonalOperator_one (b : OrthonormalBasis ι 𝕜 E) :
    b.diagonalOperator 1 = 1 := by
  simp only [diagonalOperator, Pi.one_apply, one_smul]
  exact b.sum_rankOne_eq_id

/-- **Composition of diagonal operators is pointwise multiplication of their diagonals**:
`diag w ∘L diag w' = diag (w * w')`. -/
theorem diagonalOperator_comp (b : OrthonormalBasis ι 𝕜 E) (w w' : ι → 𝕜) :
    b.diagonalOperator w ∘L b.diagonalOperator w' = b.diagonalOperator (w * w') := by
  simp only [diagonalOperator]
  rw [ContinuousLinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_finsetSum, Finset.smul_sum,
    Finset.sum_eq_single i]
  · rw [ContinuousLinearMap.comp_smul, rankOne_comp_rankOne, b.inner_eq_one i, one_smul,
      smul_smul, Pi.mul_apply]
  · intro j _ hji
    rw [ContinuousLinearMap.comp_smul, rankOne_comp_rankOne, b.orthonormal.inner_eq_zero
      (Ne.symm hji), zero_smul, smul_zero, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **N&C Exercise 2.49 — left polar decomposition in outer-product form.** For a normal operator
`A = ∑ᵢ μᵢ • |bᵢ⟩⟨bᵢ|`, the left polar decomposition `A = U J` has unitary factor
`U = ∑ᵢ phase(μᵢ) • |bᵢ⟩⟨bᵢ|` and positive factor `J = ∑ᵢ ‖μᵢ‖ • |bᵢ⟩⟨bᵢ|`, both diagonal in
`A`'s eigenbasis. -/
theorem diagonalOperator_eq_phase_comp_norm (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    b.diagonalOperator μ =
      b.diagonalOperator (fun i => RCLike.phase (μ i)) ∘L
        b.diagonalOperator (fun i => (‖μ i‖ : 𝕜)) := by
  rw [diagonalOperator_comp]
  congr 1
  ext i
  rw [Pi.mul_apply, RCLike.phase_mul_norm]

/-- **N&C Exercise 2.49 — right polar decomposition in outer-product form.** Since the two factors
share `A`'s eigenbasis they commute, so `A = J U` also holds with the same `U`, `J`. -/
theorem diagonalOperator_eq_norm_comp_phase (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    b.diagonalOperator μ =
      b.diagonalOperator (fun i => (‖μ i‖ : 𝕜)) ∘L
        b.diagonalOperator (fun i => RCLike.phase (μ i)) := by
  rw [diagonalOperator_comp]
  congr 1
  ext i
  rw [Pi.mul_apply, RCLike.norm_mul_phase]

variable [CompleteSpace E]

/-- The adjoint of a diagonal operator is diagonal with conjugated entries:
`(diag w)† = diag (star w)`. -/
theorem diagonalOperator_adjoint (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜) :
    adjoint (b.diagonalOperator w) = b.diagonalOperator (star w) := by
  simp only [diagonalOperator, map_sum, map_smulₛₗ, InnerProductSpace.adjoint_rankOne,
    Pi.star_apply, RCLike.star_def]

/-- A diagonal operator with unit-modulus diagonal is **unitary**. -/
theorem diagonalOperator_mem_unitary (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜)
    (hw : ∀ i, ‖w i‖ = 1) : b.diagonalOperator w ∈ unitary (E →L[𝕜] E) := by
  have hl : star w * w = 1 := by
    ext i; simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply, RCLike.star_def]
    rw [RCLike.conj_mul, hw i]; norm_num
  have hr : w * star w = 1 := by
    ext i; simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply, RCLike.star_def]
    rw [RCLike.mul_conj, hw i]; norm_num
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint, diagonalOperator_adjoint,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, diagonalOperator_comp,
    diagonalOperator_comp, hl, hr, diagonalOperator_one]
  exact ⟨rfl, rfl⟩

omit [CompleteSpace E] in
/-- A diagonal operator with nonnegative diagonal is **positive**. -/
theorem diagonalOperator_isPositive_of_nonneg (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜)
    (hw : ∀ i, 0 ≤ w i) : (b.diagonalOperator w).IsPositive := by
  rw [diagonalOperator]
  refine isPositive_sum _ fun i _ => ?_
  exact (InnerProductSpace.isPositive_rankOne_self _).smul_of_nonneg (hw i)

/-- Every operator diagonal in an orthonormal basis is **normal**: it commutes with its adjoint. -/
theorem diagonalOperator_isStarNormal (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜) :
    IsStarNormal (b.diagonalOperator w) := by
  refine ⟨?_⟩
  change star (b.diagonalOperator w) * b.diagonalOperator w
    = b.diagonalOperator w * star (b.diagonalOperator w)
  rw [ContinuousLinearMap.star_eq_adjoint, diagonalOperator_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.mul_def, diagonalOperator_comp, diagonalOperator_comp, mul_comm (star w) w]

/-- The phase factor `U = ∑ᵢ phase(μᵢ) • |bᵢ⟩⟨bᵢ|` is unitary. -/
theorem diagonalOperator_phase_mem_unitary (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    b.diagonalOperator (fun i => RCLike.phase (μ i)) ∈ unitary (E →L[𝕜] E) :=
  b.diagonalOperator_mem_unitary _ fun i => RCLike.norm_phase (μ i)

omit [CompleteSpace E] in
/-- The positive factor `J = ∑ᵢ ‖μᵢ‖ • |bᵢ⟩⟨bᵢ|` is positive. -/
theorem diagonalOperator_norm_isPositive (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    (b.diagonalOperator (fun i => (‖μ i‖ : 𝕜))).IsPositive :=
  b.diagonalOperator_isPositive_of_nonneg _ fun i => RCLike.ofReal_nonneg.mpr (norm_nonneg (μ i))

/-- **The positive factor is the canonical one:** `J = |A| = √(A† A)`. This identifies the
outer-product positive factor `∑ᵢ ‖μᵢ‖ • |bᵢ⟩⟨bᵢ|` with the absolute value `|A|` of N&C
Theorem 2.3, via uniqueness of the positive factor
(`ContinuousLinearMap.absoluteValue_eq_of_unitary_comp`). -/
theorem diagonalOperator_norm_eq_absoluteValue [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜) :
    b.diagonalOperator (fun i => (‖μ i‖ : 𝕜)) = (b.diagonalOperator μ).absoluteValue :=
  absoluteValue_eq_of_unitary_comp (b.diagonalOperator μ)
    (b.diagonalOperator_phase_mem_unitary μ) (b.diagonalOperator_norm_isPositive μ)
    (b.diagonalOperator_eq_phase_comp_norm μ)

end OrthonormalBasis

/-- **Normality transfers to the underlying linear map:** a normal continuous linear map on a
complete inner product space coerces to a normal `E →ₗ[𝕜] E`. This bridges the `→L` polar/spectral
API to the `→ₗ`-stated spectral theorem for normal operators. -/
theorem ContinuousLinearMap.isStarNormal_toLinearMap {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    {A : E →L[𝕜] E} (hA : IsStarNormal A) : IsStarNormal (A : E →ₗ[𝕜] E) := by
  refine ⟨?_⟩
  have hstar : star (A : E →ₗ[𝕜] E) = ((star A : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
    rw [LinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_toLinearMap]
  rw [hstar]
  change ((star A : E →L[𝕜] E) : E →ₗ[𝕜] E) * (A : E →ₗ[𝕜] E)
    = (A : E →ₗ[𝕜] E) * ((star A : E →L[𝕜] E) : E →ₗ[𝕜] E)
  rw [← ContinuousLinearMap.toLinearMap_mul, ← ContinuousLinearMap.toLinearMap_mul,
      hA.star_comm_self.eq]

section Normal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

open Module

/-- **Every normal operator is diagonal in an orthonormal eigenbasis, in outer-product form.**
The forward half of the spectral theorem (N&C Theorem 2.1) recast as
`A = ∑ᵢ μᵢ • |bᵢ⟩⟨bᵢ| = b.diagonalOperator μ`. Combined with the `diagonalOperator` polar
decomposition above, this places the polar decomposition of *any* normal operator `A` in the
outer-product representation of N&C Exercise 2.49: `A = U J = J U` with
`U = ∑ᵢ phase(μᵢ) • |bᵢ⟩⟨bᵢ|` and `J = |A| = ∑ᵢ ‖μᵢ‖ • |bᵢ⟩⟨bᵢ|`. -/
theorem IsStarNormal.exists_eq_diagonalOperator {A : E →L[ℂ] E} (hA : IsStarNormal A) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E) (μ : Fin (finrank ℂ E) → ℂ),
      A = b.diagonalOperator μ := by
  obtain ⟨b, μ, hbμ⟩ :=
    (ContinuousLinearMap.isStarNormal_toLinearMap hA).exists_orthonormalBasis_forall_apply_eq_smul
  refine ⟨b, μ, ?_⟩
  conv_lhs => rw [← ContinuousLinearMap.comp_id A, ← b.sum_rankOne_eq_id]
  rw [ContinuousLinearMap.comp_finsetSum, OrthonormalBasis.diagonalOperator]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [comp_rankOne, show A (b i) = μ i • b i from hbμ i, ← smul_rankOne]

end Normal
