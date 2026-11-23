/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DipoleSelectionRules

/-!
# Nielsen & Chuang, Exercise 7.16 (Electric dipole selection rules)

Electric dipole selection rules: show the integral (7.60) is nonzero only for m2−m1=±1 and Δl=±1.

(N&C p. 300.) In the two-level-atom approximation (N&C §7.5.1), the dipolar interaction `d⃗·E⃗`
selects atomic levels via a matrix element `⟨ℓ₁,m₁| r̂ |ℓ₂,m₂⟩` of the position operator between
orbital wavefunctions. Writing `r̂` in the `x̂–ŷ` plane in terms of the dipole spherical harmonics
`Y_{1,±1}` (eq. 7.59), the angular part is the Gaunt-type overlap integral

`∫ Y*_{ℓ₁m₁} Y_{1m} Y_{ℓ₂m₂} dΩ`   (eq. 7.60),   with `m = ±1`.

N&C's two selection rules are: `m₂ − m₁ = ±1` (conservation of the `ẑ`-component of angular
momentum) and `Δℓ = ±1` (parity together with the dipole triangle rule).

## The formalisation

The formalisable content is a statement about an integral of complex-valued functions built from
the spherical harmonics `Y_{ℓm}(θ,φ) = R_{ℓm}(θ)·e^{imφ}` (`Polynomial`/`Real.sin`/`Complex.exp`
data). Compare Exercise 7.9.

In `AxQM/Concrete/DipoleSelectionRules.lean`:

* `sphHarmNorm`, `sphHarmRadial`, `sphHarm` — the spherical harmonic `Y_{ℓm}` in the separated form
  `R_{ℓm}(θ)·e^{imφ}`, N&C (7.63)/(7.64) (associated-Legendre radial factor written in `θ`).
* `dipoleOverlap` — the overlap integral (7.60), as the iterated integral over `θ ∈ [0,π]`,
  `φ ∈ [0,2π]` with the solid-angle weight `sin θ`.
* `integral_exp_int_period` — the reusable heart `∫₀^{2π} e^{ikφ} dφ = 0` for nonzero integer `k`.
* `dipoleOverlap_ne_zero_imp_azimuthal` — the **azimuthal (`m`) selection rule**: a nonvanishing
  overlap forces `m₁ = m + m₂` (conservation of the `ẑ` angular-momentum component).
* `dipoleOverlap_ne_zero_imp_delta_m` — the dipole corollary `m₂ − m₁ = ±1` for `m = ±1`, N&C's
  first stated selection rule.
* `sphHarmRadial_pi_sub`, `sphHarm_pi_sub` — the **reflection** `θ ↦ π − θ` of the harmonics, each
  picking up the parity sign `(−1)^{ℓ+|m|}` (from the parity of `(d/dx)^{ℓ+|m|} (x²−1)^ℓ`).
* `dipoleOverlap_reflect` — the reflection identity `(7.60) = (−1)^{ℓ₁+|m₁|+1+|m|+ℓ₂+|m₂|} (7.60)`.
* `dipoleOverlap_ne_zero_imp_parity` — the **parity selection rule**: a nonvanishing overlap forces
  `ℓ₂ − ℓ₁` to be **odd** (the parity half of `Δℓ = ±1`).
* `dipolePoly`, `dipolePoly_swap`, `dipoleOverlap_eq_dipolePoly_integral` — the **reduction** of the
  overlap (under the azimuthal constraint) to `2π` times a real integral of a single polynomial
  `dipolePoly` over `[-1,1]` (via the `φ`-integral and the substitution `x = cos θ`).
* `dipolePoly_integral_eq_zero_of_lt` — that polynomial integral vanishes when `ℓ₁ ≥ ℓ₂ + 2`, by the
  general Rodrigues integration by parts `Polynomial.integral_iterate_derivative_mul` (in
  `ToMathlib.Analysis.Calculus.Deriv.PolynomialIntegral`); the `ℓ₂ ≥ ℓ₁ + 2` case
  follows by `dipolePoly_swap`.
* `dipoleOverlap_ne_zero_imp_triangle` — the **dipole triangle bound** `|ℓ₂ − ℓ₁| ≤ 1`.
* `dipoleOverlap_ne_zero_imp_delta_l` — the **`Δℓ = ±1` rule**, combining parity (odd) with the
  triangle bound.

## Summary

N&C's two selection rules are the two named theorems
`dipoleOverlap_ne_zero_imp_delta_m` (the **`m` rule** `m₂ − m₁ = ±1`, conservation of angular
momentum) and `dipoleOverlap_ne_zero_imp_delta_l` (the **`Δℓ` rule** `ℓ₂ − ℓ₁ = ±1`), the latter
assembled from the parity rule `Δℓ` odd and the triangle bound `|Δℓ| ≤ 1`.
Together this collection is the formalisation of the exercise.
-/
