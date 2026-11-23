/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFC

/-!
# The generalized inverse square root and the pretty-good-measurement completeness bound

For a positive operator `A ≥ 0` on a finite-dimensional complex inner product space, this file
defines the **generalized inverse square root**

`A⁻¹ᐟ²  :=  cfc (fun x => (√x)⁻¹) A`

— the operator inverting `√A` on the support of `A` and vanishing on its kernel — and records the
completeness bound of the **pretty-good (square-root) measurement**.  The generalized inverse is
built directly through the continuous functional calculus with the (globally discontinuous)
function `x ↦ (√x)⁻¹`; in Lean's convention `(√0)⁻¹ = 0⁻¹ = 0`, so this single formula already
inverts the nonzero eigenvalues and kills the zero eigenvalue, and continuity on the (finite) real
spectrum is automatic (`IsSelfAdjoint.continuousOn_spectrum`).

## What this file provides

* `ContinuousLinearMap.genInvSqrt` — the generalized inverse square root `A⁻¹ᐟ²`.
* `ContinuousLinearMap.genInvSqrt_nonneg`, `ContinuousLinearMap.isSelfAdjoint_genInvSqrt` — it is a
  positive (hence self-adjoint) operator when `A ≥ 0`.
* `ContinuousLinearMap.genInvSqrt_mul_self_mul_genInvSqrt_le_one` — the **support-projection bound**
  `A⁻¹ᐟ² · A · A⁻¹ᐟ² ≤ 1`: the composite is the orthogonal projection onto the range of `A`, so it
  is a sub-identity.
* `ContinuousLinearMap.sum_genInvSqrt_conjugate_le_one` — the **completeness bound of the
  pretty-good measurement**: for a finite family of positive operators `A i` with total
  `S = ∑ i, A i`, the pretty-good effects `E i = S⁻¹ᐟ² · A i · S⁻¹ᐟ²` satisfy `∑ i, E i ≤ 1`, so
  `E₀ = 1 - ∑ i, E i ≥ 0` completes them to a POVM.

This is the operator content that turns the square-root decoder `E_M = (∑ P Pₘ P)⁻¹ᐟ² P Pₘ P
(∑ P Pₘ P)⁻¹ᐟ²` of the **Holevo–Schumacher–Westmoreland theorem** (Nielsen & Chuang, Box 12.5,
eq. (12.78)) into a genuine (sub-)POVM: `∑_M E_M ≤ 1` is exactly `sum_genInvSqrt_conjugate_le_one`
applied to `A_M = P Pₘ P ≥ 0`.

## Proof

`A⁻¹ᐟ² · A · A⁻¹ᐟ²` is a triple product of continuous-functional-calculus images of `A`, so
`cfc_mul` folds it to `cfc h A` with `h x = (√x)⁻¹ · x · (√x)⁻¹`.  On the (nonnegative) spectrum
`h x = x · x⁻¹ ∈ {0, 1}`, whence `cfc h A ≤ 1` by `cfc_le_one`.  The completeness bound distributes
the outer factors over the sum, `∑ i, S⁻¹ᐟ² · A i · S⁻¹ᐟ² = S⁻¹ᐟ² · S · S⁻¹ᐟ²`, and applies the
support-projection bound to the (positive) total `S`.

-/

@[expose] public section

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- **The generalized inverse square root** `A⁻¹ᐟ²` of an operator: the continuous-functional-
calculus image of `x ↦ (√x)⁻¹`.  For a positive operator this inverts `√A` on the support of `A`
and vanishes on its kernel (Lean's `(√0)⁻¹ = 0` supplies the kernel behaviour automatically). -/
def genInvSqrt (A : E →L[ℂ] E) : E →L[ℂ] E := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A

omit [FiniteDimensional ℂ E] in
/-- The generalized inverse square root of a positive operator is positive. -/
theorem genInvSqrt_nonneg {A : E →L[ℂ] E} (hA : 0 ≤ A) : 0 ≤ genInvSqrt A := by
  refine cfc_nonneg (fun x hx => ?_)
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
  positivity

omit [FiniteDimensional ℂ E] in
/-- The generalized inverse square root of a positive operator is self-adjoint. -/
theorem isSelfAdjoint_genInvSqrt {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    IsSelfAdjoint (genInvSqrt A) := by
  have : IsSelfAdjoint A := hA.isSelfAdjoint
  exact cfc_predicate _ _

/-- **The support-projection bound** `A⁻¹ᐟ² · A · A⁻¹ᐟ² ≤ 1` for a positive operator `A ≥ 0`.  The
composite is the orthogonal projection onto the range of `A`, so it is a sub-identity.  This is the
completeness step of the pretty-good (square-root) measurement: with `A = ∑ Aᵢ` the total operator,
`A⁻¹ᐟ² · A · A⁻¹ᐟ²` is the sum of the pretty-good effects.

Folding the triple product of functional-calculus images (`cfc_mul`) to `cfc h A` with
`h x = (√x)⁻¹ · x · (√x)⁻¹`, the pointwise bound `h x ≤ 1` on the nonnegative spectrum (where
`(√x)⁻¹ · x · (√x)⁻¹ = x · x⁻¹ ∈ {0, 1}`) gives `cfc h A ≤ 1` by `cfc_le_one`. -/
theorem genInvSqrt_mul_self_mul_genInvSqrt_le_one {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    genInvSqrt A * A * genInvSqrt A ≤ 1 := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f => hsa.continuousOn_spectrum f
  -- fold the triple product of functional-calculus images into a single `cfc`
  have hfold : genInvSqrt A * A * genInvSqrt A
      = cfc (fun x => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) A := by
    have hmid : genInvSqrt A * A * genInvSqrt A
        = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A * cfc (id : ℝ → ℝ) A
            * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A := by
      rw [cfc_id ℝ A]; rfl
    rw [hmid, ← cfc_mul _ _ A (hc _) (hc _), ← cfc_mul _ _ A (hc _) (hc _)]
    simp only [id_eq]
  rw [hfold]
  refine cfc_le_one _ A (fun x hx => ?_)
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
  rcases eq_or_lt_of_le hx0 with h | h
  · simp [← h]
  · -- on a positive eigenvalue `(√x)⁻¹ · x · (√x)⁻¹ = x⁻¹ · x = 1`
    rw [mul_right_comm, ← mul_inv, Real.mul_self_sqrt hx0, inv_mul_cancel₀ (ne_of_gt h)]

/-- **The completeness bound of the pretty-good (square-root) measurement.**  For a finite family of
positive operators `A : ι → E →L[ℂ] E` with total `S = ∑ i, A i`, the pretty-good effects
`E i = S⁻¹ᐟ² · A i · S⁻¹ᐟ²` sum to a sub-identity:

`∑ i, S⁻¹ᐟ² · A i · S⁻¹ᐟ²  ≤  1`.

Hence `E₀ = 1 - ∑ i, E i ≥ 0` completes `{E i}` to a POVM.  This is the operator core making the
Nielsen–Chuang square-root decoder (Box 12.5, eq. (12.78)) a genuine (sub-)POVM.  The outer factors
distribute over the sum, `∑ i, S⁻¹ᐟ² · A i · S⁻¹ᐟ² = S⁻¹ᐟ² · S · S⁻¹ᐟ²`, and the support-projection
bound `genInvSqrt_mul_self_mul_genInvSqrt_le_one` applies to the positive total `S`. -/
theorem sum_genInvSqrt_conjugate_le_one {ι : Type*} [Fintype ι] (A : ι → E →L[ℂ] E)
    (hA : ∀ i, 0 ≤ A i) :
    ∑ i, genInvSqrt (∑ j, A j) * A i * genInvSqrt (∑ j, A j) ≤ 1 := by
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  exact genInvSqrt_mul_self_mul_genInvSqrt_le_one (Finset.sum_nonneg fun i _ => hA i)

omit [FiniteDimensional ℂ E] in
/-- Each pretty-good effect `S⁻¹ᐟ² · Aᵢ · S⁻¹ᐟ²` is a positive operator (conjugation of the positive
`Aᵢ` by the self-adjoint `S⁻¹ᐟ²`), the second half of the POVM datum. -/
theorem genInvSqrt_conjugate_nonneg {ι : Type*} [Fintype ι] (A : ι → E →L[ℂ] E)
    (hA : ∀ i, 0 ≤ A i) (i : ι) :
    0 ≤ genInvSqrt (∑ j, A j) * A i * genInvSqrt (∑ j, A j) :=
  IsSelfAdjoint.conjugate_nonneg (hA i)
    (isSelfAdjoint_genInvSqrt (Finset.sum_nonneg fun i _ => hA i))

end ContinuousLinearMap
