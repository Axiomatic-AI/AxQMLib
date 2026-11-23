/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.ResolventSquareIntegral
public import ToMathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# Trace of the operator-logarithm derivative: `tr(ω · d/dp log ω_p) = tr(Δ)`

For a strictly positive operator `W` on a finite-dimensional complex inner product space and any
operator `Δ`, the resolvent "sandwich" integral contracted against `W` under the trace collapses to
the plain trace of `Δ`:

`tr(W · ∫₀^∞ (W + s • 1)⁻¹ Δ (W + s • 1)⁻¹ ds) = tr(Δ)`.

With `W = ω_p = p ρ + (1 − p) σ` the mixing operator and `Δ = ρ − σ`, the integral is exactly the
parametric derivative of the operator logarithm `d/dp cfc Real.log ω_p`
(`hasDerivAt_cfc_log_add_smul`), so this is the trace-derivative identity
`tr(ω_p · d/dp log ω_p) = tr(ρ − σ)` used in the
second-derivative proof of concavity of the von Neumann entropy (Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 11.22).

## Method

Writing `Rₛ = (W + s • 1)⁻¹`, the integrand `Rₛ Δ Rₛ` is integrable on `(0, ∞)`
(`integrableOn_Ioi_ringInverse_mul_mul_ringInverse`, dominated by `‖Δ‖ (m + s)⁻²`). The trace and
the constant left factor `W` are pulled inside the Bochner integral (both are continuous linear, via
`ContinuousLinearMap.integral_comp_comm`), and then, pointwise in `s`:

* cyclicity of the trace (`LinearMap.trace_mul_comm`) moves the factors around;
* `W` commutes with its own resolvent — `W Rₛ = 1 − s Rₛ = Rₛ W` (both from `mul_inverse_cancel`) —
  so `Rₛ W Rₛ = W Rₛ²`.

This turns `tr(W Rₛ Δ Rₛ)` into `tr((Δ W) Rₛ²)`, whose `s`-integral collapses via
`∫₀^∞ Rₛ² ds = W⁻¹` (`integral_Ioi_ringInverse_add_smul_one_sq`) to `tr(Δ W W⁻¹) = tr(Δ)`.

## Main results

* `ContinuousLinearMap.reTraceCLM` — the functional `X ↦ re tr(X)` bundled as a real-linear
  continuous map `(E →L[ℂ] E) →L[ℝ] ℝ` (the real-part sibling of `traceCLM`).
* `integrableOn_Ioi_ringInverse_mul_mul_ringInverse` — integrability of the resolvent sandwich
  `s ↦ (a + s • 1)⁻¹ x (a + s • 1)⁻¹` on `(0, ∞)`, for `a` strictly positive in a C⋆-algebra.
* `LinearMap.trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse` — the trace-derivative
  identity.
* `LinearMap.re_trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse_nonneg` — nonnegativity of
  the *second*-derivative trace integral `re tr(Δ · ∫₀^∞ Rₛ Δ Rₛ ds) ≥ 0` for `Δ` self-adjoint,
  i.e. `f''(p) ≤ 0` for `f(p) = S(ω_p)` (the second-derivative form of concavity of the von Neumann
  entropy, Nielsen & Chuang Exercise 11.22).
-/

@[expose] public section

open MeasureTheory Set

/-- The **trace** on a finite-dimensional complex inner product space, bundled as a continuous
ℂ-linear functional `(E →L[ℂ] E) →L[ℂ] ℂ` (a linear map out of a finite-dimensional space is
automatically continuous). Packaging the trace this way lets it be pushed through a Bochner
integral via `ContinuousLinearMap.integral_comp_comm`, as in the trace-derivative identities
below. -/
noncomputable def ContinuousLinearMap.traceCLM
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] :
    (E →L[ℂ] E) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ E).comp (ContinuousLinearMap.coeLM ℂ))

@[simp]
theorem ContinuousLinearMap.traceCLM_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (X : E →L[ℂ] E) : ContinuousLinearMap.traceCLM E X = (LinearMap.trace ℂ E) ↑X := by
  simp [ContinuousLinearMap.traceCLM, LinearMap.coe_toContinuousLinearMap']

/-- **The entropy functional `re ∘ tr`, bundled as a real-linear continuous functional**
`(E →L[ℂ] E) →L[ℝ] ℝ`, `X ↦ re tr(X)` — the `ℝ`-CLM real-part sibling of
`ContinuousLinearMap.traceCLM`. Packaging `re ∘ tr` this way lets it be pushed through a real
derivative via `HasFDerivAt.comp_hasDerivAt`, as in the entropy-derivative computations
(`ToMathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/EntropyDeriv.lean`). -/
noncomputable def ContinuousLinearMap.reTraceCLM
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] :
    (E →L[ℂ] E) →L[ℝ] ℝ :=
  -- `IsScalarTower ℝ ℂ (E →L[ℂ] E)` is mathematically valid but not a global instance for abstract
  -- `E` (the `rclike_operator_algebra_gap` §3.5); provide it locally as in
  -- `ToMathlib/Analysis/InnerProductSpace/DensityFixedPoint.lean`, so
  -- `RCLike.real_smul_eq_coe_smul` gives `ℝ`-linearity of `X ↦ re tr X`. (Restricting the
  -- ℂ-linear `traceCLM` directly hits a
  -- `Module ℝ (E →L[ℂ] E)` diamond in `CompatibleSMul`; we instead build the `ℝ`-linear map by
  -- hand with an explicit operator-norm bound.)
  letI : IsScalarTower ℝ ℂ (E →L[ℂ] E) := IsScalarTower.restrictScalars ℝ ℂ _
  LinearMap.mkContinuous
    { toFun := fun X => RCLike.re ((LinearMap.trace ℂ E) ↑X)
      map_add' := fun X Y => by simp only [ContinuousLinearMap.toLinearMap_add, map_add]
      map_smul' := fun r X => by
        simp only [RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := ℂ) r X,
          ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, RCLike.re_ofReal_mul] }
    ‖ContinuousLinearMap.traceCLM E‖ fun X => by
      calc ‖RCLike.re ((LinearMap.trace ℂ E) ↑X)‖
          ≤ ‖(LinearMap.trace ℂ E) ↑X‖ := RCLike.norm_re_le_norm _
        _ = ‖ContinuousLinearMap.traceCLM E X‖ := by rw [ContinuousLinearMap.traceCLM_apply]
        _ ≤ ‖ContinuousLinearMap.traceCLM E‖ * ‖X‖ := (ContinuousLinearMap.traceCLM E).le_opNorm X

@[simp]
theorem ContinuousLinearMap.reTraceCLM_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (X : E →L[ℂ] E) :
    ContinuousLinearMap.reTraceCLM E X = RCLike.re ((LinearMap.trace ℂ E) ↑X) :=
  rfl

/-- **Integrability of the resolvent sandwich.** For a strictly positive element `a` of a C⋆-algebra
and any element `x`, the map `s ↦ (a + s • 1)⁻¹ x (a + s • 1)⁻¹` is integrable on `(0, ∞)`. With
`(algebraMap ℝ A) m ≤ a` (a positive spectral lower bound), the resolvent norm bound
`‖(a + s • 1)⁻¹‖ ≤ (m + s)⁻¹` (`CStarAlgebra.norm_ringInverse_le_of_algebraMap_le`) and
submultiplicativity give `‖·‖ ≤ ‖x‖ (m + s)⁻²`, an integrable dominating function
(`integrableOn_Ioi_inv_add_sq`). -/
theorem integrableOn_Ioi_ringInverse_mul_mul_ringInverse
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    {a : A} (ha : IsStrictlyPositive a) (x : A) :
    IntegrableOn
      (fun s : ℝ => Ring.inverse (a + s • 1) * x * Ring.inverse (a + s • 1)) (Ioi 0) := by
  obtain ⟨m, hm, hma⟩ : ∃ m, 0 < m ∧ (algebraMap ℝ A) m ≤ a :=
    (CFC.exists_pos_algebraMap_le_iff (a := a)).mpr
      (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp ha).2
  have hunit : ∀ s : ℝ, 0 ≤ s → IsUnit (a + s • (1 : A)) :=
    fun s hs => (ha.add_nonneg (smul_nonneg hs zero_le_one)).isUnit
  have hnorm : ∀ s : ℝ, 0 ≤ s → ‖Ring.inverse (a + s • (1 : A))‖ ≤ (m + s)⁻¹ := by
    intro s hs
    refine CStarAlgebra.norm_ringInverse_le_of_algebraMap_le (m := m + s) (by linarith) ?_
    rw [map_add, Algebra.algebraMap_eq_smul_one (R := ℝ) (A := A) s]
    gcongr
  have hResCont : ∀ s : ℝ, 0 ≤ s →
      ContinuousAt (fun t : ℝ => Ring.inverse (a + t • (1 : A))) s :=
    fun s hs => (hasDerivAt_ringInverse_add_smul (hunit s hs)).continuousAt
  have hcont : ContinuousOn
      (fun s : ℝ => Ring.inverse (a + s • (1 : A)) * x * Ring.inverse (a + s • 1)) (Ioi 0) :=
    fun s hs =>
      (((hResCont s (le_of_lt hs)).continuousWithinAt.mul continuousWithinAt_const).mul
        ((hResCont s (le_of_lt hs)).continuousWithinAt))
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => Ring.inverse (a + s • (1 : A)) * x * Ring.inverse (a + s • 1))
      (volume.restrict (Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  refine ((integrableOn_Ioi_inv_add_sq hm).const_mul ‖x‖).mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s hs => ?_)
  simp only [mem_Ioi] at hs
  have hr := hnorm s hs.le
  calc ‖Ring.inverse (a + s • (1 : A)) * x * Ring.inverse (a + s • 1)‖
      ≤ ‖Ring.inverse (a + s • (1 : A)) * x‖ * ‖Ring.inverse (a + s • (1 : A))‖ := norm_mul_le _ _
    _ ≤ (‖Ring.inverse (a + s • (1 : A))‖ * ‖x‖) * ‖Ring.inverse (a + s • (1 : A))‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ ((m + s)⁻¹ * ‖x‖) * (m + s)⁻¹ := by gcongr
    _ = ‖x‖ * (m + s)⁻¹ ^ 2 := by ring

/-- **Trace-derivative identity.** For a strictly positive operator `W` on a finite-dimensional
complex inner product space and any operator `Δ`,

`tr(W · ∫₀^∞ (W + s • 1)⁻¹ Δ (W + s • 1)⁻¹ ds) = tr(Δ)`.

The integral is the parametric derivative `d/dp cfc Real.log ω_p` at `ω_p = W`
(`hasDerivAt_cfc_log_add_smul`, direction `Δ`), so this is `tr(W · d/dp log ω_p) = tr(Δ)`. See the
module docstring for the method. -/
theorem LinearMap.trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E] [Nontrivial E] {W : E →L[ℂ] E} (hW : IsStrictlyPositive W) (Δ : E →L[ℂ] E) :
    (LinearMap.trace ℂ E) ↑(W * ∫ s in Ioi (0 : ℝ),
        Ring.inverse (W + s • 1) * Δ * Ring.inverse (W + s • 1))
      = (LinearMap.trace ℂ E) ↑Δ := by
  set R : ℝ → (E →L[ℂ] E) := fun s => Ring.inverse (W + s • 1) with hR
  -- Trace cyclicity through the `ContinuousLinearMap → LinearMap` coercion.
  have trcyc : ∀ B C : E →L[ℂ] E,
      (LinearMap.trace ℂ E) ↑(B * C) = (LinearMap.trace ℂ E) ↑(C * B) := by
    intro B C
    rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
        LinearMap.trace_mul_comm]
  -- The trace, bundled as a continuous linear functional (`ContinuousLinearMap.traceCLM`);
  -- left multiplication by a constant is `ContinuousLinearMap.mul_apply'`.
  let tr : (E →L[ℂ] E) →L[ℂ] ℂ := ContinuousLinearMap.traceCLM E
  have htr : ∀ X : E →L[ℂ] E, tr X = (LinearMap.trace ℂ E) ↑X :=
    fun X => ContinuousLinearMap.traceCLM_apply X
  -- Integrability of the two integrands.
  have hφint : IntegrableOn (fun s => R s * Δ * R s) (Ioi 0) :=
    integrableOn_Ioi_ringInverse_mul_mul_ringInverse hW Δ
  have hR2int : IntegrableOn (fun s => R s ^ 2) (Ioi 0) := by
    have := integrableOn_Ioi_ringInverse_mul_mul_ringInverse hW (1 : E →L[ℂ] E)
    refine this.congr_fun ?_ measurableSet_Ioi
    intro s _; simp [hR, sq, mul_one]
  -- `W` commutes with its resolvent: `R s W R s = W (R s)^2`.
  have hWR : ∀ s : ℝ, 0 < s → R s * W = 1 - s • R s := by
    intro s hs
    have hu : IsUnit (W + s • (1 : E →L[ℂ] E)) :=
      (hW.add_nonneg (smul_nonneg hs.le zero_le_one)).isUnit
    have hiu : Ring.inverse (W + s • (1 : E →L[ℂ] E)) * (W + s • (1 : E →L[ℂ] E)) = 1 :=
      Ring.inverse_mul_cancel _ hu
    have expand : W = (W + s • (1 : E →L[ℂ] E)) - s • (1 : E →L[ℂ] E) := by abel
    calc R s * W = R s * ((W + s • 1) - s • 1) := by rw [hR, ← expand]
      _ = R s * (W + s • 1) - R s * (s • 1) := by rw [mul_sub]
      _ = 1 - s • R s := by rw [hR, hiu, mul_smul_comm, mul_one]
  have hRW : ∀ s : ℝ, 0 < s → W * R s = 1 - s • R s := by
    intro s hs
    have hu : IsUnit (W + s • (1 : E →L[ℂ] E)) :=
      (hW.add_nonneg (smul_nonneg hs.le zero_le_one)).isUnit
    have hiu : (W + s • (1 : E →L[ℂ] E)) * Ring.inverse (W + s • (1 : E →L[ℂ] E)) = 1 :=
      Ring.mul_inverse_cancel _ hu
    have expand : W = (W + s • (1 : E →L[ℂ] E)) - s • (1 : E →L[ℂ] E) := by abel
    calc W * R s = ((W + s • 1) - s • 1) * R s := by rw [hR, ← expand]
      _ = (W + s • 1) * R s - (s • 1) * R s := by rw [sub_mul]
      _ = 1 - s • R s := by rw [hR, hiu, smul_mul_assoc, one_mul]
  have hcomm : ∀ s : ℝ, 0 < s → R s * W * R s = W * R s ^ 2 := by
    intro s hs
    rw [hWR s hs, sq]
    rw [show W * (R s * R s) = (W * R s) * R s by rw [mul_assoc], hRW s hs]
  -- Pointwise: `tr(W · (R s Δ R s)) = tr((Δ W) · (R s)^2)`.
  have hpt : ∀ s : ℝ, s ∈ Ioi (0 : ℝ) →
      (LinearMap.trace ℂ E) ↑(W * (R s * Δ * R s))
        = (LinearMap.trace ℂ E) ↑((Δ * W) * R s ^ 2) := by
    intro s hs
    simp only [mem_Ioi] at hs
    calc (LinearMap.trace ℂ E) ↑(W * (R s * Δ * R s))
        = (LinearMap.trace ℂ E) ↑((W * R s * Δ) * R s) := by rw [show W * (R s * Δ * R s)
            = (W * R s * Δ) * R s by noncomm_ring]
      _ = (LinearMap.trace ℂ E) ↑(R s * (W * R s * Δ)) := trcyc _ _
      _ = (LinearMap.trace ℂ E) ↑((R s * W * R s) * Δ) := by rw [show R s * (W * R s * Δ)
            = (R s * W * R s) * Δ by noncomm_ring]
      _ = (LinearMap.trace ℂ E) ↑((W * R s ^ 2) * Δ) := by rw [hcomm s hs]
      _ = (LinearMap.trace ℂ E) ↑(Δ * (W * R s ^ 2)) := trcyc _ _
      _ = (LinearMap.trace ℂ E) ↑((Δ * W) * R s ^ 2) := by rw [mul_assoc]
  -- Assemble.
  calc (LinearMap.trace ℂ E) ↑(W * ∫ s in Ioi (0 : ℝ), R s * Δ * R s)
      = tr ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E) W) (∫ s in Ioi (0 : ℝ), R s * Δ * R s)) := by
        rw [htr, ContinuousLinearMap.mul_apply']
    _ = tr (∫ s in Ioi (0 : ℝ), (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) W) (R s * Δ * R s)) := by
        rw [ContinuousLinearMap.integral_comp_comm _ hφint]
    _ = ∫ s in Ioi (0 : ℝ), tr ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E) W) (R s * Δ * R s)) := by
        rw [← ContinuousLinearMap.integral_comp_comm]
        exact (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) W).integrable_comp hφint
    _ = ∫ s in Ioi (0 : ℝ), (LinearMap.trace ℂ E) ↑((Δ * W) * R s ^ 2) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
        rw [htr, ContinuousLinearMap.mul_apply', hpt s hs]
    _ = ∫ s in Ioi (0 : ℝ), tr ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (Δ * W)) (R s ^ 2)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
        rw [htr, ContinuousLinearMap.mul_apply']
    _ = tr (∫ s in Ioi (0 : ℝ), (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (Δ * W)) (R s ^ 2)) := by
        rw [← ContinuousLinearMap.integral_comp_comm]
        exact (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (Δ * W)).integrable_comp hR2int
    _ = tr ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E) (Δ * W)) (∫ s in Ioi (0 : ℝ), R s ^ 2)) := by
        rw [ContinuousLinearMap.integral_comp_comm _ hR2int]
    _ = (LinearMap.trace ℂ E) ↑((Δ * W) * Ring.inverse W) := by
        rw [htr, ContinuousLinearMap.mul_apply', hR, integral_Ioi_ringInverse_add_smul_one_sq hW]
    _ = (LinearMap.trace ℂ E) ↑Δ := by
        rw [mul_assoc, Ring.mul_inverse_cancel _ hW.isUnit, mul_one]

/-- **Nonnegativity of the second-derivative trace integral.** For a strictly positive operator `W`
on a finite-dimensional complex inner product space and a *self-adjoint* operator `Δ`,

`0 ≤ re tr(Δ · ∫₀^∞ (W + s • 1)⁻¹ Δ (W + s • 1)⁻¹ ds)`.

With `W = ω_p = p ρ + (1 − p) σ` and `Δ = ρ − σ`, the integral is the parametric derivative
`d/dp cfc Real.log ω_p` (`hasDerivAt_cfc_log_add_smul`), so the left-hand side is `−f''(p)` for
`f(p) = S(ω_p) = −tr(ω_p log ω_p)`. This is therefore the second-derivative form of concavity of the
von Neumann entropy — `f''(p) ≤ 0` — the analytic heart of Nielsen & Chuang's alternate proof of
concavity (*Quantum Computation and Quantum Information*, Exercise 11.22).

## Method

Writing `Rₛ = (W + s • 1)⁻¹`, the constant left factor `Δ` and the trace are pulled inside the
Bochner integral (both continuous linear, via `ContinuousLinearMap.integral_comp_comm`, using
integrability of `Rₛ Δ Rₛ` from `integrableOn_Ioi_ringInverse_mul_mul_ringInverse`), and `re`
commutes with the integral (`RCLike.reCLM`). This reduces the claim to pointwise nonnegativity of
the integrand: for `s > 0`,

`re tr(Δ (Rₛ Δ Rₛ)) = re tr((Δ Rₛ Δ) · Rₛ) ≥ 0`,

because `Rₛ` is positive (`IsStrictlyPositive.ringInverse`, `W + s • 1` being strictly positive),
its self-adjoint conjugate `Δ Rₛ Δ` is positive (`IsSelfAdjoint.conjugate_nonneg`), and the trace of
a product of positive operators has nonnegative real part
(`ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg`) — the Hilbert–Schmidt square
`re tr(Δ Rₛ Δ Rₛ) = ‖Rₛ^{1/2} Δ Rₛ^{1/2}‖₂² ≥ 0`. The `s`-integral of a nonnegative function is
nonnegative (`MeasureTheory.setIntegral_nonneg`). -/
theorem LinearMap.re_trace_mul_integral_Ioi_ringInverse_mul_mul_ringInverse_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E] [Nontrivial E] {W : E →L[ℂ] E} (hW : IsStrictlyPositive W)
    {Δ : E →L[ℂ] E} (hΔ : IsSelfAdjoint Δ) :
    0 ≤ RCLike.re ((LinearMap.trace ℂ E) ↑(Δ * ∫ s in Ioi (0 : ℝ),
        Ring.inverse (W + s • 1) * Δ * Ring.inverse (W + s • 1))) := by
  set R : ℝ → (E →L[ℂ] E) := fun s => Ring.inverse (W + s • 1) with hR
  -- `G X = tr(Δ · X)`, bundled as a continuous linear map (via `ContinuousLinearMap.traceCLM`)
  -- for the integral-commutation lemmas; left multiplication is `ContinuousLinearMap.mul_apply'`.
  set G : (E →L[ℂ] E) →L[ℂ] ℂ :=
    (ContinuousLinearMap.traceCLM E).comp (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) Δ) with hG
  have hGapp : ∀ X : E →L[ℂ] E, G X = (LinearMap.trace ℂ E) ↑(Δ * X) := fun X => by
    rw [hG, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.traceCLM_apply]
  -- Integrability of the resolvent sandwich, and of the scalar integrand `s ↦ tr(Δ (Rₛ Δ Rₛ))`.
  have hφint : IntegrableOn (fun s => R s * Δ * R s) (Ioi 0) :=
    integrableOn_Ioi_ringInverse_mul_mul_ringInverse hW Δ
  have hGint : IntegrableOn (fun s => G (R s * Δ * R s)) (Ioi 0) := G.integrable_comp hφint
  -- Pointwise: `re tr(Δ (Rₛ Δ Rₛ)) = re tr((Δ Rₛ Δ) · Rₛ) ≥ 0`.
  have hpt : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ RCLike.re (G (R s * Δ * R s)) := by
    intro s hs
    simp only [mem_Ioi] at hs
    have hWs : IsStrictlyPositive (W + s • (1 : E →L[ℂ] E)) :=
      hW.add_nonneg (smul_nonneg hs.le zero_le_one)
    have hRpos : (0 : E →L[ℂ] E) ≤ R s := (hWs.ringInverse).nonneg
    have hAr : (0 : E →L[ℂ] E) ≤ Δ * R s * Δ := IsSelfAdjoint.conjugate_nonneg hRpos hΔ
    rw [hGapp, show Δ * (R s * Δ * R s) = (Δ * R s * Δ) * R s by noncomm_ring]
    exact ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg hAr hRpos
  -- Pull `Δ` and the trace inside the integral.
  have hpull : (LinearMap.trace ℂ E) ↑(Δ * ∫ s in Ioi (0 : ℝ), R s * Δ * R s)
      = ∫ s in Ioi (0 : ℝ), G (R s * Δ * R s) := by
    rw [← hGapp]
    exact (ContinuousLinearMap.integral_comp_comm G hφint).symm
  -- `re` commutes with the integral; the integrand is nonnegative.
  rw [hpull]
  have hre : RCLike.re (∫ s in Ioi (0 : ℝ), G (R s * Δ * R s))
      = ∫ s in Ioi (0 : ℝ), RCLike.re (G (R s * Δ * R s)) := (integral_re hGint).symm
  rw [hre]
  exact setIntegral_nonneg measurableSet_Ioi hpt
