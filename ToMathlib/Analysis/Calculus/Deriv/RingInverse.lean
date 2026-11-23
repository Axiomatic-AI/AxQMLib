/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Derivative of `Ring.inverse` composed with a differentiable function

`Mathlib.Analysis.Calculus.FDeriv.Mul` provides `hasFDerivAt_ringInverse`, the Fréchet
derivative of the inversion map `Ring.inverse` at a unit `x` of a Banach algebra `R`
(one with summable geometric series), namely `h ↦ -x⁻¹ * h * x⁻¹`. This file records the
corresponding **chain rules**: the derivative of `y ↦ Ring.inverse (g y)` for a
differentiable `R`-valued map `g` whose value is a unit at the point of interest.

Both the multivariable (`HasFDerivAt.ringInverse`) and one-dimensional
(`HasDerivAt.ringInverse`) forms are provided, in parallel with the existing
`Differentiable.inverse`. The one-dimensional form specialises to the derivative of the
**resolvent along an affine line** `t ↦ (a + t • b)⁻¹` (`hasDerivAt_ringInverse_add_smul`),
with the familiar "sandwich" derivative `-x⁻¹ * b * x⁻¹`; this is the elementary calculus
step underlying the parametric derivative of an operator resolvent, e.g. in the
integral-representation approach to differentiating an operator logarithm along a line.

## Main results

* `HasFDerivAt.ringInverse` — chain rule for `Ring.inverse` (Fréchet form).
* `HasDerivAt.ringInverse` — chain rule for `Ring.inverse` (one real/scalar variable).
* `hasDerivAt_ringInverse_add_smul` — the derivative of the resolvent `t ↦ (a + t • b)⁻¹`
  along an affine line, `-(a + t₀ • b)⁻¹ * b * (a + t₀ • b)⁻¹`.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra 𝕜 R]

/-- **Chain rule for `Ring.inverse`, Fréchet form.** If `g` has Fréchet derivative `g'` at
`x` and `g x` is a unit, then `y ↦ Ring.inverse (g y)` has Fréchet derivative
`h ↦ -(g x)⁻¹ * (g' h) * (g x)⁻¹` at `x`. The derivative is written using the unit inverse
`↑hu.unit⁻¹` (which equals `Ring.inverse (g x)`). -/
theorem HasFDerivAt.ringInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {g : E → R} {g' : E →L[𝕜] R} {x : E} (hg : HasFDerivAt g g' x) (hu : IsUnit (g x)) :
    HasFDerivAt (fun y => Ring.inverse (g y))
      (-((ContinuousLinearMap.mulLeftRight 𝕜 R ↑hu.unit⁻¹ ↑hu.unit⁻¹).comp g')) x := by
  have hL := hasFDerivAt_ringInverse (𝕜 := 𝕜) hu.unit
  rw [hu.unit_spec] at hL
  exact hL.comp x hg

/-- **Chain rule for `Ring.inverse`, one-variable form.** If `g : 𝕜 → R` has derivative `g'`
at `t₀` and `g t₀` is a unit, then `t ↦ Ring.inverse (g t)` has derivative
`-(g t₀)⁻¹ * g' * (g t₀)⁻¹` at `t₀`. -/
theorem HasDerivAt.ringInverse {g : 𝕜 → R} {g' : R} {t₀ : 𝕜}
    (hg : HasDerivAt g g' t₀) (hu : IsUnit (g t₀)) :
    HasDerivAt (fun t => Ring.inverse (g t)) (-(↑hu.unit⁻¹ * g' * ↑hu.unit⁻¹)) t₀ := by
  have hL := hasFDerivAt_ringInverse (𝕜 := 𝕜) hu.unit
  rw [hu.unit_spec] at hL
  have hC := hL.comp_hasDerivAt t₀ hg
  simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply] at hC
  exact hC

/-- **Derivative of the resolvent along an affine line.** For `a b : R` with `a + t₀ • b` a
unit, the resolvent `t ↦ Ring.inverse (a + t • b)` has derivative
`-(a + t₀ • b)⁻¹ * b * (a + t₀ • b)⁻¹` at `t₀` (the "sandwich" formula). -/
theorem hasDerivAt_ringInverse_add_smul {a b : R} {t₀ : 𝕜} (hu : IsUnit (a + t₀ • b)) :
    HasDerivAt (fun t : 𝕜 => Ring.inverse (a + t • b)) (-(↑hu.unit⁻¹ * b * ↑hu.unit⁻¹)) t₀ := by
  simpa using (((hasDerivAt_id t₀).smul_const b).const_add a).ringInverse hu
