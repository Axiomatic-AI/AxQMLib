/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.TraceNormUnitary
public import ToMathlib.Analysis.InnerProductSpace.Density
public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import ToMathlib.Analysis.InnerProductSpace.HSPairing
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Alberti's variational characterization of the fidelity

For positive operators `ρ, σ` on a finite-dimensional complex Hilbert space `E` and an
*invertible positive* operator `P` (`IsStrictlyPositive P`, i.e. `0 ≤ P` and `IsUnit P`),
Alberti's theorem expresses the squared fidelity as an infimum:
```
F(ρ, σ)² = inf_P tr(ρ P) tr(σ P⁻¹),
```
where `F(ρ, σ) = ‖√ρ √σ‖₁` is the fidelity (the trace norm of `√ρ √σ`; equal to Nielsen &
Chuang's `tr √(√ρ σ √ρ)`, see `AxQM.State.fidelity_eq_traceNorm`). This is the genuine
form of the identity that Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Problem 9.1 (eq. `(9.145)`) states — the book prints it with an unsquared `F`, which is an
erratum (the right-hand side equals `F²`, strictly below `F` for every non-trivial pair).

This file proves the **lower-bound** direction, which holds for *arbitrary* positive `ρ, σ`
(no commutativity or invertibility assumption on the states):
```
F(ρ, σ)² ≤ tr(ρ P) tr(σ P⁻¹)   for every invertible positive P,
```
and, for *strictly positive* (invertible) `ρ, σ`, that this lower bound is **attained** at an
explicit minimizer, giving the full `IsLeast … F²`. For non-invertible states the infimum is not
attained (the minimizer would need `(√ρ)⁻¹`); the identity there is an infimum rather than a least
element, obtained by a regularization `ρ ↝ ρ + δ•1` as `δ → 0⁺`, giving the general
`IsGLB … F²` for *all* positive `ρ, σ` — the exact form of the book's statement.

## Main definitions

* `ContinuousLinearMap.albertiProduct ρ σ P` — the functional `tr(ρ P) · tr(σ P⁻¹)` (with the
  inverse taken as `Ring.inverse P`, the genuine inverse when `P` is invertible), whose infimum
  over invertible positive `P` is `F(ρ, σ)²`.
* `ContinuousLinearMap.albertiMinimizer ρ σ` — the minimizer `(√ρ)⁻¹ √(√ρ σ √ρ) (√ρ)⁻¹` realising
  the infimum for strictly positive `ρ, σ`.

## Main results

* `ContinuousLinearMap.traceNorm_cfc_sqrt_mul_sq_le_albertiProduct` — the Alberti lower bound
  `‖√ρ √σ‖₁² ≤ albertiProduct ρ σ P` for `0 ≤ ρ`, `0 ≤ σ` and invertible positive `P`.
* `ContinuousLinearMap.traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj` — the operator identity
  `‖√ρ √σ‖₁ = tr √(√ρ σ √ρ)` between the two forms of the fidelity.
* `ContinuousLinearMap.albertiProduct_albertiMinimizer` — the minimizer attains `‖√ρ √σ‖₁²`.
* `ContinuousLinearMap.isLeast_albertiProduct` — **Alberti's theorem** for strictly positive `ρ, σ`:
  `F(ρ, σ)² = ‖√ρ √σ‖₁²` is the least value of `tr(ρ P) tr(σ P⁻¹)` over invertible positive `P`.
* `ContinuousLinearMap.isGLB_albertiProduct` — **Alberti's theorem for all positive `ρ, σ`** (the
  book's `(9.145)`, corrected to `F²`): `F(ρ, σ)²` is the *infimum* of `tr(ρ P) tr(σ P⁻¹)` over
  invertible positive `P`, with no invertibility assumption on the states (approached, but not
  attained, when a state is rank-deficient).
* `ContinuousLinearMap.tendsto_albertiRegularization` / `continuousOn_cfc_real_sqrt` — the
  continuity ingredients: `‖√(ρ+δ) √(σ+δ)‖₁² → F(ρ, σ)²` as `δ → 0⁺`, via continuity of
  `cfc Real.sqrt` on the nonnegative cone (the latter at general `CStarAlgebra` generality).

## Implementation notes

Write `A = √P √ρ` and `B = (√P)⁻¹ √σ` (with `√· = cfc Real.sqrt ·`; `√P` is invertible since `P`
is). Then `tr(ρ P) = re⟨A, A⟩_HS` and `tr(σ P⁻¹) = re⟨B, B⟩_HS` for the Hilbert–Schmidt pairing,
and, choosing the unitary `U` that maximizes `‖tr(√ρ √σ U)‖` (so this maximum is `‖√ρ √σ‖₁`,
`ContinuousLinearMap.isGreatest_norm_trace_mul_unitary`), one has
`‖√ρ √σ‖₁ = ‖tr(√ρ √σ U)‖ = ‖⟨B U, A⟩_HS‖`. Cauchy–Schwarz for the HS pairing
(`ContinuousLinearMap.norm_hsPairing_sq_le`) then gives
`‖√ρ √σ‖₁² ≤ re⟨B U, B U⟩_HS · re⟨A, A⟩_HS = tr(σ P⁻¹) · tr(ρ P)`.

## References

* P. M. Alberti, *A note on the transition probability over C\*-algebras*,
  Lett. Math. Phys. **7** (1983), 25–32.
* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Problem 9.1.
-/

@[expose] public section

/-- The CFC real square root of a **strictly positive** element is strictly positive (in particular
invertible). A sibling of `cfc_real_sqrt_nonneg` / `cfc_real_sqrt_mul_self_of_nonneg`
stated for the `cfc Real.sqrt` idiom these results use; the invertibility is the `IsUnit` half. -/
theorem IsStrictlyPositive.cfc_real_sqrt {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a : A} (ha : IsStrictlyPositive a) :
    IsStrictlyPositive (cfc Real.sqrt a) := by
  refine ⟨cfc_real_sqrt_nonneg a, ?_⟩
  have h : IsUnit (cfc Real.sqrt a * cfc Real.sqrt a) := by
    rw [cfc_real_sqrt_mul_self_of_nonneg ha.1]; exact ha.2
  exact ((Commute.isUnit_mul_iff (Commute.refl _)).mp h).1

/-- `cfc Real.sqrt` is continuous on the cone of nonnegative elements of a C\*-algebra. This bridges
the Mathlib result `CFC.continuousOn_sqrt` (stated for the `CFC.sqrt` idiom) to the `cfc Real.sqrt`
form used throughout this file, via `CFC.sqrt_eq_real_sqrt` and `cfcₙ_eq_cfc` (applicable because
`Real.sqrt 0 = 0`). Stated at general `CStarAlgebra` generality — like its sibling
`IsStrictlyPositive.cfc_real_sqrt`, the proof uses only the C\*-algebra structure — and instantiated
at `A := E →L[ℂ] E` to supply the continuity of the regularization `ρ ↝ √(ρ + δ)` below. -/
theorem continuousOn_cfc_real_sqrt {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : ContinuousOn (cfc Real.sqrt : A → A) {a | 0 ≤ a} := by
  refine (CFC.continuousOn_sqrt (A := A)).congr fun a ha => ?_
  rw [CFC.sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc Real.continuous_sqrt.continuousOn Real.sqrt_zero]

namespace ContinuousLinearMap

open scoped ComplexOrder
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- The **Alberti functional** `P ↦ tr(ρ P) · tr(σ P⁻¹)` appearing on the right-hand side of
Nielsen & Chuang's Problem 9.1. The inverse of `P` is taken as `Ring.inverse P`, which is the
genuine two-sided inverse whenever `P` is invertible (the only `P` over which the infimum is
taken). For positive `ρ, σ` and invertible positive `P` the two traces are real and nonnegative,
so this is a nonnegative real number; its infimum over all invertible positive `P` is the squared
fidelity `F(ρ, σ)²` (Alberti's theorem). -/
noncomputable def albertiProduct (ρ σ P : E →L[ℂ] E) : ℝ :=
  RCLike.re (LinearMap.trace ℂ E (ρ * P)) *
    RCLike.re (LinearMap.trace ℂ E (σ * Ring.inverse P))

/-- **Alberti's lower bound** (the nontrivial direction of Nielsen & Chuang Problem 9.1, in its
corrected `F²` form). For positive operators `ρ, σ` and an *invertible positive* operator `P`
(`IsStrictlyPositive P`), the squared fidelity `‖√ρ √σ‖₁²` is a lower bound for the Alberti
functional `tr(ρ P) · tr(σ P⁻¹)`. No commutativity or invertibility of `ρ, σ` is assumed, so this
holds at the full generality of the book's statement. Combined with the minimizer (a companion
result), it yields `F(ρ, σ)² = inf_P tr(ρ P) tr(σ P⁻¹)`.

The proof factors `ρ = √ρ √ρ`, `σ = √σ √σ`, `P = √P √P` and inserts `√P (√P)⁻¹ = 1` between the
square roots of `√ρ √σ`, turning `tr(√ρ √σ U)` (with `U` the fidelity-maximizing unitary) into a
Hilbert–Schmidt pairing `⟨(√P)⁻¹ √σ U, √P √ρ⟩` whose Cauchy–Schwarz bound is exactly
`tr(ρ P) · tr(σ P⁻¹)`. -/
theorem traceNorm_cfc_sqrt_mul_sq_le_albertiProduct (ρ σ P : E →L[ℂ] E)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hP : IsStrictlyPositive P) :
    (cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm ^ 2 ≤ albertiProduct ρ σ P := by
  rw [albertiProduct]
  have hPnn : (0 : E →L[ℂ] E) ≤ P := hP.1
  set r := cfc Real.sqrt ρ with hr
  set s := cfc Real.sqrt σ with hs
  set S := cfc Real.sqrt P with hSdef
  have hrsa : IsSelfAdjoint r := .cfc
  have hssa : IsSelfAdjoint s := .cfc
  have hSsa : IsSelfAdjoint S := .cfc
  have hSS : S * S = P := cfc_real_sqrt_mul_self_of_nonneg hPnn
  have hss : s * s = σ := cfc_real_sqrt_mul_self_of_nonneg hσ
  have hSunit : IsUnit S := by
    have hP2 : IsUnit (S * S) := by rw [hSS]; exact hP.2
    exact ((Commute.isUnit_mul_iff (Commute.refl S)).mp hP2).1
  set Si := Ring.inverse S with hSi
  have hSSi : S * Si = 1 := Ring.mul_inverse_cancel S hSunit
  have hSisa : IsSelfAdjoint Si := hSsa.ringInverse
  have hSiSi : Si * Si = Ring.inverse P := by
    rw [hSi, ← hSS, Ring.mul_inverse_rev' (Commute.refl S)]
  have hSadj : ContinuousLinearMap.adjoint S = S := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hSsa
  -- `re⟨√P √ρ, √P √ρ⟩_HS = tr(ρ P)`
  have hWW : RCLike.re ((S * r).hsPairing (S * r))
      = RCLike.re (LinearMap.trace ℂ E (ρ * P)) := by
    have h := ContinuousLinearMap.hsPairing_mul_cfc_sqrt_eq_trace hρ S S
    rw [← hr] at h
    rw [h, hSadj, hSS]
    exact congrArg RCLike.re (ContinuousLinearMap.trace_mul_comm P ρ)
  -- the fidelity-maximizing unitary: `‖√ρ √σ‖₁ = ‖tr(√ρ √σ U)‖`
  obtain ⟨U, hUmem, hUeq⟩ := (ContinuousLinearMap.isGreatest_norm_trace_mul_unitary (r * s)).1
  have hUadj : U * ContinuousLinearMap.adjoint U = 1 := by
    have h := Unitary.mul_star_self_of_mem hUmem
    rwa [ContinuousLinearMap.star_eq_adjoint] at h
  -- conjugation by the unitary `U` preserves the trace
  have hconj : ∀ Y : E →L[ℂ] E,
      LinearMap.trace ℂ E ↑(ContinuousLinearMap.adjoint U * Y * U) = LinearMap.trace ℂ E ↑Y := by
    intro Y
    rw [mul_assoc, ContinuousLinearMap.trace_mul_comm, mul_assoc, hUadj, mul_one]
  -- the cross pairing recovers `tr(√ρ √σ U)`
  have hcross : (Si * s * U).hsPairing (S * r) = LinearMap.trace ℂ E ↑(r * s * U) := by
    rw [ContinuousLinearMap.hsPairing_eq]
    have hadjW : ContinuousLinearMap.adjoint (S * r) = r * S := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, hrsa.star_eq, hSsa.star_eq]
    have hopeq : (ContinuousLinearMap.adjoint (S * r)).comp (Si * s * U) = r * s * U := by
      rw [hadjW, ← ContinuousLinearMap.mul_def]
      simp only [mul_assoc]
      rw [← mul_assoc S Si (s * U), hSSi, one_mul]
    rw [hopeq]
  -- `re⟨(√P)⁻¹ √σ U, (√P)⁻¹ √σ U⟩_HS = tr(σ P⁻¹)`
  have hTT : RCLike.re ((Si * s * U).hsPairing (Si * s * U))
      = RCLike.re (LinearMap.trace ℂ E (σ * Ring.inverse P)) := by
    rw [ContinuousLinearMap.hsPairing_eq]
    have hadjT : ContinuousLinearMap.adjoint (Si * s * U)
        = ContinuousLinearMap.adjoint U * (s * Si) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_mul, hssa.star_eq, hSisa.star_eq,
        ContinuousLinearMap.star_eq_adjoint]
    rw [← ContinuousLinearMap.mul_def, hadjT]
    have hprod : ContinuousLinearMap.adjoint U * (s * Si) * (Si * s * U)
        = ContinuousLinearMap.adjoint U * (s * Si * Si * s) * U := by
      simp only [mul_assoc]
    rw [hprod, hconj (s * Si * Si * s), mul_assoc s Si Si, hSiSi]
    have htr : LinearMap.trace ℂ E ↑((s * Ring.inverse P) * s)
        = LinearMap.trace ℂ E ↑(σ * Ring.inverse P) := by
      rw [ContinuousLinearMap.trace_mul_comm (s * Ring.inverse P) s, ← mul_assoc, hss]
    exact congrArg RCLike.re htr
  -- Cauchy–Schwarz for the Hilbert–Schmidt pairing
  have hCS := ContinuousLinearMap.norm_hsPairing_sq_le (Si * s * U) (S * r)
  rw [hcross, ← hUeq, hTT, hWW] at hCS
  exact le_of_le_of_eq hCS (mul_comm _ _)

/-- **The two fidelity formulas agree, at operator level.** For positive `σ` and arbitrary `ρ`,
the trace-norm form `‖√ρ √σ‖₁` of the fidelity equals Nielsen & Chuang's square-root form
`tr √(√ρ σ √ρ)` (eq. `(9.53)`). This is the operator content of
`AxQM.State.fidelity_eq_traceNorm`, stated for operators rather than `State`s so that it can
supply the minimizer value below.

The proof flips `√ρ √σ` to its adjoint `√σ √ρ` (trace norm is adjoint-invariant), whose absolute
value is `√((√σ √ρ)† (√σ √ρ)) = √(√ρ σ √ρ)`; the trace norm of that positive operator is the real
part of its trace. -/
theorem traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj (ρ σ : E →L[ℂ] E) (hσ : 0 ≤ σ) :
    (cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm =
      RCLike.re ((LinearMap.trace ℂ E)
        ↑(cfc Real.sqrt (cfc Real.sqrt ρ * σ * cfc Real.sqrt ρ))) := by
  set r := cfc Real.sqrt ρ with hr
  set s := cfc Real.sqrt σ with hs
  have hrsa : IsSelfAdjoint r := .cfc
  have hssa : IsSelfAdjoint s := .cfc
  have hss : s * s = σ := cfc_real_sqrt_mul_self_of_nonneg hσ
  have hadjrs : ContinuousLinearMap.adjoint (r * s) = s * r := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, hssa.star_eq, hrsa.star_eq]
  have habs : (s * r).absoluteValue = cfc Real.sqrt (r * σ * r) := by
    rw [ContinuousLinearMap.absoluteValue_eq_cfc_sqrt, ← ContinuousLinearMap.mul_def]
    have hadjsr : ContinuousLinearMap.adjoint (s * r) = r * s := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, hrsa.star_eq, hssa.star_eq]
    rw [hadjsr, show r * s * (s * r) = r * (s * s) * r by simp only [mul_assoc], hss]
  rw [← ContinuousLinearMap.traceNorm_adjoint (r * s), hadjrs,
    ← ContinuousLinearMap.traceNorm_absoluteValue (s * r), habs,
    ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive
      (habs ▸ ContinuousLinearMap.absoluteValue_isPositive (s * r))]

/-- The **Alberti minimizer** `P = (√ρ)⁻¹ √(√ρ σ √ρ) (√ρ)⁻¹`, the invertible positive operator
attaining the infimum in Alberti's theorem. Both traces collapse to `tr √(√ρ σ √ρ) = F(ρ, σ)`, so
`tr(ρ P) tr(σ P⁻¹) = F(ρ, σ)²` (see `albertiProduct_albertiMinimizer`). Requires `ρ` invertible for
`(√ρ)⁻¹` and `σ` invertible for the inner square root to be invertible; hence the infimum is
*attained* exactly on strictly positive states. -/
noncomputable def albertiMinimizer (ρ σ : E →L[ℂ] E) : E →L[ℂ] E :=
  Ring.inverse (cfc Real.sqrt ρ) *
    cfc Real.sqrt (cfc Real.sqrt ρ * σ * cfc Real.sqrt ρ) * Ring.inverse (cfc Real.sqrt ρ)

omit [FiniteDimensional ℂ E] in
/-- The shared building blocks for the Alberti minimizer over strictly positive `ρ, σ`: writing
`r = √ρ`, the operator `r` is a self-adjoint unit with `r * r = ρ`, its inverse `r⁻¹` is a unit, and
the conjugate `r σ r = √ρ σ √ρ` is strictly positive. Both minimizer theorems apply this instead of
re-deriving the preamble. -/
theorem albertiMinimizer_blocks (ρ σ : E →L[ℂ] E)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    IsSelfAdjoint (cfc Real.sqrt ρ) ∧ cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ ∧
      IsUnit (cfc Real.sqrt ρ) ∧ Ring.inverse (cfc Real.sqrt ρ) * cfc Real.sqrt ρ = 1 ∧
      cfc Real.sqrt ρ * Ring.inverse (cfc Real.sqrt ρ) = 1 ∧
      IsUnit (Ring.inverse (cfc Real.sqrt ρ)) ∧
      IsStrictlyPositive (cfc Real.sqrt ρ * σ * cfc Real.sqrt ρ) := by
  have hrunit : IsUnit (cfc Real.sqrt ρ) := (hρ.cfc_real_sqrt).2
  have hri_r : Ring.inverse (cfc Real.sqrt ρ) * cfc Real.sqrt ρ = 1 :=
    Ring.inverse_mul_cancel _ hrunit
  have hr_ri : cfc Real.sqrt ρ * Ring.inverse (cfc Real.sqrt ρ) = 1 :=
    Ring.mul_inverse_cancel _ hrunit
  exact ⟨.cfc, cfc_real_sqrt_mul_self_of_nonneg hρ.1, hrunit, hri_r, hr_ri,
    ⟨⟨_, _, hri_r, hr_ri⟩, rfl⟩,
    IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint σ _ hrunit .cfc hσ⟩

omit [FiniteDimensional ℂ E] in
/-- The Alberti minimizer is an invertible positive operator (`IsStrictlyPositive`), hence an
admissible `P` in the infimum, provided both states are strictly positive. It is the conjugate
`(√ρ)⁻¹ · √(√ρ σ √ρ) · (√ρ)⁻¹` of the strictly positive operator `√(√ρ σ √ρ)` by the self-adjoint
unit `(√ρ)⁻¹`. -/
theorem albertiMinimizer_isStrictlyPositive (ρ σ : E →L[ℂ] E)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    IsStrictlyPositive (albertiMinimizer ρ σ) := by
  obtain ⟨hrsa, -, -, -, -, hriunit, hrσr⟩ := albertiMinimizer_blocks ρ σ hρ hσ
  rw [albertiMinimizer]
  exact IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _ hriunit hrsa.ringInverse
    hrσr.cfc_real_sqrt

/-- **The Alberti minimizer attains `F(ρ, σ)²`.** For strictly positive `ρ, σ`, the Alberti
functional at `P = (√ρ)⁻¹ √(√ρ σ √ρ) (√ρ)⁻¹` equals `‖√ρ √σ‖₁² = F(ρ, σ)²`. Both traces reduce to
`tr √(√ρ σ √ρ)` by cyclicity of the trace and the cancellations `(√ρ)⁻¹ √ρ = 1`,
`√(√ρ σ √ρ)² = √ρ σ √ρ`; the value is then rewritten to the trace-norm form via
`traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj`. -/
theorem albertiProduct_albertiMinimizer (ρ σ : E →L[ℂ] E)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    albertiProduct ρ σ (albertiMinimizer ρ σ)
      = (cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm ^ 2 := by
  obtain ⟨-, hrr, hrunit, hri_r, hr_ri, hriunit, hrσr⟩ := albertiMinimizer_blocks ρ σ hρ hσ
  rw [albertiProduct, albertiMinimizer]
  set r := cfc Real.sqrt ρ with hr
  set s := cfc Real.sqrt σ with hs
  set M := cfc Real.sqrt (r * σ * r) with hM
  set ri := Ring.inverse r with hri
  -- `√(√ρ σ √ρ)` is an invertible operator with `M * M = √ρ σ √ρ`
  have hMM : M * M = r * σ * r := hM ▸ cfc_real_sqrt_mul_self_of_nonneg hrσr.1
  have hMunit : IsUnit M := (hrσr.cfc_real_sqrt).2
  have hM_Mi : M * Ring.inverse M = 1 := Ring.mul_inverse_cancel M hMunit
  -- `tr(ρ P) = tr M`
  have hconj1 : ri * ρ * ri = 1 := by
    rw [hri, ← hrr, ← mul_assoc, hri_r, one_mul, hr_ri]
  have htr1 : (LinearMap.trace ℂ E) ↑(ρ * (ri * M * ri)) = (LinearMap.trace ℂ E) ↑M := by
    rw [show ρ * (ri * M * ri) = ρ * ri * M * ri by simp only [mul_assoc],
      ContinuousLinearMap.trace_mul_comm (ρ * ri * M) ri,
      show ri * (ρ * ri * M) = ri * ρ * ri * M by simp only [mul_assoc], hconj1, one_mul]
  -- `Ring.inverse P = √ρ M⁻¹ √ρ`, hence `tr(σ P⁻¹) = tr M`
  have hPinv : Ring.inverse (ri * M * ri) = r * Ring.inverse M * r := by
    rw [Ring.inverse_mul (Or.inr hriunit), Ring.inverse_mul (Or.inl hriunit), hri,
      Ring.inverse_inverse hrunit, ← mul_assoc]
  have htr2 : (LinearMap.trace ℂ E) ↑(σ * Ring.inverse (ri * M * ri))
      = (LinearMap.trace ℂ E) ↑M := by
    rw [hPinv,
      show σ * (r * Ring.inverse M * r) = σ * r * Ring.inverse M * r by simp only [mul_assoc],
      ContinuousLinearMap.trace_mul_comm (σ * r * Ring.inverse M) r,
      show r * (σ * r * Ring.inverse M) = r * σ * r * Ring.inverse M by simp only [mul_assoc],
      ← hMM, mul_assoc, hM_Mi, mul_one]
  -- assemble: `tr(ρ P) tr(σ P⁻¹) = (re tr M)² = ‖√ρ √σ‖₁²`
  have hbridge : (r * s).traceNorm = RCLike.re ((LinearMap.trace ℂ E) ↑M) := by
    rw [hM, hr, hs]; exact traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj ρ σ hσ.1
  rw [← ContinuousLinearMap.toLinearMap_mul, ← ContinuousLinearMap.toLinearMap_mul, htr1, htr2,
      hbridge]
  ring

/-- **Alberti's theorem** (Nielsen & Chuang Problem 9.1, corrected `F²` form) for strictly positive
states. For invertible density operators `ρ, σ`, the squared fidelity `F(ρ, σ)² = ‖√ρ √σ‖₁²` is the
*least* value of the Alberti functional `P ↦ tr(ρ P) tr(σ P⁻¹)` over all invertible positive `P` —
attained at the minimizer `albertiMinimizer ρ σ`. This is the general (non-commuting) form of the
identity garbled by the book's `(9.145)` (which prints an unsquared `F`); the lower-bound half holds
for arbitrary positive `ρ, σ` (`traceNorm_cfc_sqrt_mul_sq_le_albertiProduct`), and strict positivity
is used only to realise the minimizer. -/
theorem isLeast_albertiProduct (ρ σ : E →L[ℂ] E)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    IsLeast {y | ∃ P : E →L[ℂ] E, IsStrictlyPositive P ∧ albertiProduct ρ σ P = y}
      ((cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm ^ 2) := by
  constructor
  · exact ⟨albertiMinimizer ρ σ, albertiMinimizer_isStrictlyPositive ρ σ hρ hσ,
      albertiProduct_albertiMinimizer ρ σ hρ hσ⟩
  · rintro y ⟨P, hP, rfl⟩
    exact traceNorm_cfc_sqrt_mul_sq_le_albertiProduct ρ σ P hρ.1 hσ.1 hP

/-- **The regularized squared fidelity converges to `F(ρ, σ)²`.** For positive `ρ, σ`, the path
`δ ↦ ‖√(ρ + δ) √(σ + δ)‖₁²` tends to `‖√ρ √σ‖₁² = F(ρ, σ)²` as the regularization `δ → 0⁺`. This is
the analytic ingredient that upgrades Alberti's `IsLeast` (valid only for invertible states, where
the minimizer exists) to the `IsGLB` valid for *all* positive `ρ, σ` (`isGLB_albertiProduct`): for a
rank-deficient state the infimum is approached but not attained, along the strictly positive
regularizations `ρ + δ•1`. The proof rewrites the trace norm in the `re tr √(√ρ σ √ρ)` form
(`traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj`) and composes continuity of `cfc Real.sqrt` on
the nonnegative cone with continuity of the trace; the regularizations stay in the cone only for
`δ ≥ 0`, so continuity is taken within `Set.Ici 0`. -/
theorem tendsto_albertiRegularization (ρ σ : E →L[ℂ] E) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    Tendsto (fun δ : ℝ => (cfc Real.sqrt (ρ + δ • 1) * cfc Real.sqrt (σ + δ • 1)).traceNorm ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm ^ 2)) := by
  have hsqrt := continuousOn_cfc_real_sqrt (A := E →L[ℂ] E)
  have haρ : Continuous (fun δ : ℝ => ρ + δ • (1 : E →L[ℂ] E)) := by fun_prop
  have haσ : Continuous (fun δ : ℝ => σ + δ • (1 : E →L[ℂ] E)) := by fun_prop
  have hmapρ : Set.MapsTo (fun δ : ℝ => ρ + δ • (1 : E →L[ℂ] E)) (Set.Ici 0) {a | 0 ≤ a} :=
    fun δ hδ => add_nonneg hρ (smul_nonneg hδ zero_le_one)
  have hmapσ : Set.MapsTo (fun δ : ℝ => σ + δ • (1 : E →L[ℂ] E)) (Set.Ici 0) {a | 0 ≤ a} :=
    fun δ hδ => add_nonneg hσ (smul_nonneg hδ zero_le_one)
  have hrρ : ContinuousOn (fun δ : ℝ => cfc Real.sqrt (ρ + δ • (1 : E →L[ℂ] E))) (Set.Ici 0) :=
    hsqrt.comp haρ.continuousOn hmapρ
  have hM : ContinuousOn
      (fun δ : ℝ => cfc Real.sqrt (ρ + δ • 1) * (σ + δ • 1) * cfc Real.sqrt (ρ + δ • 1))
      (Set.Ici 0) := (hrρ.mul haσ.continuousOn).mul hrρ
  have hmapM : Set.MapsTo
      (fun δ : ℝ => cfc Real.sqrt (ρ + δ • 1) * (σ + δ • 1) * cfc Real.sqrt (ρ + δ • 1))
      (Set.Ici 0) {a | 0 ≤ a} := by
    intro δ hδ
    change 0 ≤ cfc Real.sqrt (ρ + δ • 1) * (σ + δ • 1) * cfc Real.sqrt (ρ + δ • 1)
    exact IsSelfAdjoint.conjugate_nonneg (hmapσ hδ) IsSelfAdjoint.cfc
  have hw : ContinuousOn
      (fun δ : ℝ => cfc Real.sqrt
        (cfc Real.sqrt (ρ + δ • 1) * (σ + δ • 1) * cfc Real.sqrt (ρ + δ • 1))) (Set.Ici 0) :=
    hsqrt.comp hM hmapM
  have hcontRe : Continuous (fun T : E →L[ℂ] E => RCLike.re ((LinearMap.trace ℂ E) ↑T)) :=
    RCLike.continuous_re.comp continuous_trace
  have hΨ : ContinuousOn
      (fun δ : ℝ => (RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt
        (cfc Real.sqrt (ρ + δ • 1) * (σ + δ • 1) * cfc Real.sqrt (ρ + δ • 1)))) : ℝ) ^ 2)
      (Set.Ici 0) := (hcontRe.comp_continuousOn hw).pow 2
  have hEq : Set.EqOn
      (fun δ : ℝ => (cfc Real.sqrt (ρ + δ • 1) * cfc Real.sqrt (σ + δ • 1)).traceNorm ^ 2)
      (fun δ : ℝ => (RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt
        (cfc Real.sqrt (ρ + δ • 1) * (σ + δ • 1) * cfc Real.sqrt (ρ + δ • 1)))) : ℝ) ^ 2)
      (Set.Ici 0) := by
    intro δ hδ
    simp only [traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj (ρ + δ • 1) (σ + δ • 1) (hmapσ hδ)]
  have hΦcont : ContinuousWithinAt
      (fun δ : ℝ => (cfc Real.sqrt (ρ + δ • 1) * cfc Real.sqrt (σ + δ • 1)).traceNorm ^ 2)
      (Set.Ici 0) 0 := (hΨ.congr hEq) 0 Set.self_mem_Ici
  have htend := hΦcont.tendsto
  simp only [zero_smul, add_zero] at htend
  exact htend.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

/-- **Alberti's theorem for arbitrary states** (Nielsen & Chuang Problem 9.1, corrected `F²` form).
For *any* positive operators `ρ, σ` — with **no invertibility assumption**, so covering all density
operators including rank-deficient ones — the squared fidelity `F(ρ, σ)² = ‖√ρ √σ‖₁²` is the
*infimum* of the Alberti functional `P ↦ tr(ρ P) tr(σ P⁻¹)` over invertible positive `P`. This is
the exact form of the book's `(9.145)` ("the infimum is taken over all invertible positive matrices
`P`"), once the printed unsquared `F` is corrected to `F²`.

For strictly positive `ρ, σ` the infimum is a minimum (`isLeast_albertiProduct`); for non-invertible
states the minimizer `(√ρ)⁻¹ √(√ρ σ √ρ) (√ρ)⁻¹` does not exist and the value is only approached, so
the `IsLeast` genuinely weakens to `IsGLB`. The lower bound is
`traceNorm_cfc_sqrt_mul_sq_le_albertiProduct` (valid for all positive `ρ, σ`); that it is the
*greatest* lower bound is witnessed by evaluating the functional at the minimizers of the
regularizations `ρ + δ•1`, `σ + δ•1`, whose value is `≥`-above the original
(`re_trace_mul_mono_left`) yet converges down to `F²` as `δ → 0⁺`
(`tendsto_albertiRegularization`). -/
theorem isGLB_albertiProduct (ρ σ : E →L[ℂ] E) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    IsGLB {y | ∃ P : E →L[ℂ] E, IsStrictlyPositive P ∧ albertiProduct ρ σ P = y}
      ((cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm ^ 2) := by
  constructor
  · rintro y ⟨P, hP, rfl⟩
    exact traceNorm_cfc_sqrt_mul_sq_le_albertiProduct ρ σ P hρ hσ hP
  · intro b hb
    refine ge_of_tendsto (tendsto_albertiRegularization ρ σ hρ hσ) ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    have hρδ : IsStrictlyPositive (ρ + δ • 1) := isStrictlyPositive_add_smul_one hρ hδ0
    have hσδ : IsStrictlyPositive (σ + δ • 1) := isStrictlyPositive_add_smul_one hσ hδ0
    set P := albertiMinimizer (ρ + δ • 1) (σ + δ • 1) with hP
    have hPpos : IsStrictlyPositive P := albertiMinimizer_isStrictlyPositive _ _ hρδ hσδ
    have hb1 : b ≤ albertiProduct ρ σ P := hb ⟨P, hPpos, rfl⟩
    -- The regularized minimizer, evaluated at the *original* states, is `≥`-above the original
    -- functional (`ρ ≤ ρ + δ`, `σ ≤ σ + δ`, both traces nonnegative) yet equals `F(ρ+δ, σ+δ)²`.
    have hmono : albertiProduct ρ σ P ≤ albertiProduct (ρ + δ • 1) (σ + δ • 1) P := by
      have hle_ρ : ρ ≤ ρ + δ • 1 := le_add_of_nonneg_right (smul_nonneg hδ0.le zero_le_one)
      have hle_σ : σ ≤ σ + δ • 1 := le_add_of_nonneg_right (smul_nonneg hδ0.le zero_le_one)
      have hPnn : (0 : E →L[ℂ] E) ≤ P := hPpos.1
      have hPinv : (0 : E →L[ℂ] E) ≤ Ring.inverse P := hPpos.ringInverse.1
      have h1 : 0 ≤ RCLike.re ((LinearMap.trace ℂ E) ↑(ρ * P)) :=
        re_trace_mul_nonneg_of_nonneg hρ hPnn
      have h3 : RCLike.re ((LinearMap.trace ℂ E) ↑(ρ * P))
          ≤ RCLike.re ((LinearMap.trace ℂ E) ↑((ρ + δ • 1) * P)) :=
        re_trace_mul_mono_left hle_ρ hPnn
      have h2 : 0 ≤ RCLike.re ((LinearMap.trace ℂ E) ↑(σ * Ring.inverse P)) :=
        re_trace_mul_nonneg_of_nonneg hσ hPinv
      have h4 : RCLike.re ((LinearMap.trace ℂ E) ↑(σ * Ring.inverse P))
          ≤ RCLike.re ((LinearMap.trace ℂ E) ↑((σ + δ • 1) * Ring.inverse P)) :=
        re_trace_mul_mono_left hle_σ hPinv
      simp only [albertiProduct]
      exact mul_le_mul h3 h4 h2 (le_trans h1 h3)
    have hval : albertiProduct (ρ + δ • 1) (σ + δ • 1) P
        = (cfc Real.sqrt (ρ + δ • 1) * cfc Real.sqrt (σ + δ • 1)).traceNorm ^ 2 :=
      albertiProduct_albertiMinimizer _ _ hρδ hσδ
    calc b ≤ albertiProduct ρ σ P := hb1
      _ ≤ albertiProduct (ρ + δ • 1) (σ + δ • 1) P := hmono
      _ = _ := hval

end ContinuousLinearMap
