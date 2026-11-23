/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.Integrals.SinSqDivSq
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Concrete: the spontaneous emission rate `γ_rad` (Nielsen & Chuang, Exercise 7.29)

Nielsen & Chuang §7.6.3 (p. 316) derives the spontaneous emission rate of an atom coupled to the
electromagnetic vacuum through the Jaynes–Cummings interaction (7.109). To lowest order in the
coupling, an excited atom coupled to a single optical mode of frequency `ω` decays with probability
(N&C 7.110)
`p_decay(ω, t) = g²(ω) · 4 sin²(½(ω-ω₀)t) / (ω-ω₀)²`,
where `ℏω₀` is the atomic transition energy and the (frequency-dependent) coupling is (7.111)
`g²(ω) = ω₀² |⟨0|μ|1⟩|² / (2 ℏ ω ε₀ c²)`.
An atom in free space interacts with *all* optical modes; summing over polarisations and solid
angle (`8π/3`) and the three-dimensional mode density (`ω²/(2πc)³`) and integrating over modes gives
the total decay probability `P(t)` (N&C 7.113). **Exercise 7.29** asks to (1) evaluate this mode
integral and (2) differentiate the result in `t` to obtain the emission rate (N&C 7.112)
`γ_rad = ω₀³ |⟨0|μ|1⟩|² / (3π ℏ ε₀ c⁵)`.

## The resonance/peak approximation, and why the literal integral diverges

The literal integrand `ω² p_decay(ω, t)` behaves like `1/ω` at large `ω` (the `ω²` mode weight and
the `g²(ω) ∝ 1/ω` coupling combine to `∝ ω`, against a `1/(ω-ω₀)²` lineshape whose `sin²` averages
to `½`), so `∫₀^∞ ω² p_decay dω` — and the `-∞`-extended version of N&C's hint — **diverge**
logarithmically. Every textbook derivation (N&C included) treats the lineshape
`4 sin²(½(ω-ω₀)t)/(ω-ω₀)²` as a resonance sharply peaked at `ω = ω₀`: the slowly-varying prefactor
`ω² g²(ω)` is evaluated at the peak `ω = ω₀` and pulled out of the integral, and the lower limit is
extended to `-∞` (N&C's explicit hint). The only genuine analytic ingredient that remains is the
convergent line integral
`∫_ℝ 4 sin²(½(ω-ω₀)t)/(ω-ω₀)² dω = 2π|t|`
(`Real.integral_sin_sq_mul_div_sq`, in
`ToMathlib/Analysis/SpecialFunctions/Integrals/SinSqDivSq.lean`). We formalise this
peak-approximated
mode integral — documenting the approximation explicitly rather than reproducing a divergent object
— since it is the physically honest content and the only reading yielding N&C's finite `γ_rad`.

The whole exercise is a real-analysis computation over `ℝ`: `p_decay`, `g²`, `γ_rad` and the mode
integral are functions of real parameters (`ω₀, ℏ, ε₀, c, |⟨0|μ|1⟩|, ω, t`). The statement of
Exercise 7.29 is in `AxQM/NC/Ch7/Exercise7_29.lean`. Compare Exercise 7.21
(`AxQM/Concrete/KerrTwoPhotonPhase.lean`) and Exercise 7.22
(`AxQM/Concrete/KerrAbsorptionLoss.lean`).

## Contents

* `couplingSq` — the atom–field coupling `g²(ω)` (N&C 7.111).
* `pDecay` — the single-mode decay probability `p_decay` (N&C 7.110), in terms of `g²`.
* `gammaRad` — the target emission rate `γ_rad` (N&C 7.112).
* `spontaneousDecayProb` — the resonance-approximated mode integral `P(t)` (N&C 7.113).
* `spontaneousDecayProb_eq_gammaRad_mul_abs` — the master identity `P(t) = γ_rad · |t|`.
* `spontaneousDecayProb_eq_gammaRad_mul` — **step 1** (physical `t ≥ 0`): `P(t) = γ_rad · t`.
* `deriv_spontaneousDecayProb_eq_gammaRad` — **step 2** (`t > 0`): `dP/dt = γ_rad` (N&C 7.112).
-/

open MeasureTheory Real

namespace SpontaneousEmission

/-- The atom–field coupling strength squared `g²(ω)` (Nielsen & Chuang 7.111):
`g²(ω) = ω₀² |⟨0|μ|1⟩|² / (2 ℏ ω ε₀ c²)`, where `ω₀` is the atomic transition frequency, `ℏ` the
reduced Planck constant, `ε₀` the vacuum permittivity, `c` the speed of light, `μ = |⟨0|μ|1⟩|` the
magnitude of the atomic dipole matrix element, and `ω` the optical-mode frequency. -/
noncomputable def couplingSq (ω₀ ħ ε₀ c μ ω : ℝ) : ℝ :=
  ω₀ ^ 2 * μ ^ 2 / (2 * ħ * ω * ε₀ * c ^ 2)

/-- The single-mode spontaneous decay probability `p_decay` (Nielsen & Chuang 7.110):
`p_decay = g² · 4 sin²(½(ω-ω₀)t) / (ω-ω₀)²`, to lowest order in the coupling, for an atom coupled to
one empty optical mode of frequency `ω`. The first argument is the coupling `g²` of (7.111). -/
noncomputable def pDecay (gSq ω ω₀ t : ℝ) : ℝ :=
  gSq * (4 * Real.sin ((ω - ω₀) * t / 2) ^ 2) / (ω - ω₀) ^ 2

/-- The spontaneous emission rate `γ_rad` (Nielsen & Chuang 7.112):
`γ_rad = ω₀³ |⟨0|μ|1⟩|² / (3π ℏ ε₀ c⁵)`. -/
noncomputable def gammaRad (ω₀ ħ ε₀ c μ : ℝ) : ℝ :=
  ω₀ ^ 3 * μ ^ 2 / (3 * Real.pi * ħ * ε₀ * c ^ 5)

/-- The total spontaneous-decay probability `P(t)` from summing over all optical modes (Nielsen &
Chuang 7.113), in the resonance/peak approximation: the mode-density weight `ω²` and the coupling
`g²(ω)` — slowly varying across the sharp resonance — are evaluated at the peak `ω = ω₀` and pulled
out, and the frequency integral of the sharply-peaked lineshape runs over all of `ℝ` (N&C's hint to
extend the lower limit to `-∞`).  Explicitly,
`P(t) = 1/(2πc)³ · 8π/3 · ∫_ℝ ω₀² · p_decay(g²(ω₀), ω, ω₀, t) dω`.
See the module docstring for why the literal `ω`-dependent integrand diverges. -/
noncomputable def spontaneousDecayProb (ω₀ ħ ε₀ c μ t : ℝ) : ℝ :=
  (1 / (2 * Real.pi * c) ^ 3) * (8 * Real.pi / 3) *
    ∫ ω : ℝ, ω₀ ^ 2 * pDecay (couplingSq ω₀ ħ ε₀ c μ ω₀) ω ω₀ t

/-- The convergent core of the mode integral: the resonance lineshape integrates (over all of `ℝ`,
by translation invariance and `Real.integral_sin_sq_mul_div_sq`) to `π|t/2|`. -/
theorem integral_lineshape (ω₀ t : ℝ) :
    ∫ ω : ℝ, Real.sin ((ω - ω₀) * t / 2) ^ 2 / (ω - ω₀) ^ 2 = Real.pi * |t / 2| := by
  have hfun : (fun ω : ℝ => Real.sin ((ω - ω₀) * t / 2) ^ 2 / (ω - ω₀) ^ 2)
      = (fun ω : ℝ => (fun x => Real.sin (t / 2 * x) ^ 2 / x ^ 2) (ω - ω₀)) := by
    funext ω
    have harg : (ω - ω₀) * t / 2 = t / 2 * (ω - ω₀) := by ring
    rw [harg]
  rw [hfun, MeasureTheory.integral_sub_right_eq_self
        (fun x => Real.sin (t / 2 * x) ^ 2 / x ^ 2) ω₀]
  exact Real.integral_sin_sq_mul_div_sq (t / 2)

/-- **Master identity for Exercise 7.29.** The resonance-approximated mode integral of the decay
probability equals `γ_rad · |t|`:
`P(t) = γ_rad · |t|`  (Nielsen & Chuang, combining 7.110–7.113).  All four physical constants are
nonzero. -/
theorem spontaneousDecayProb_eq_gammaRad_mul_abs (ω₀ ħ ε₀ c μ t : ℝ)
    (hω₀ : ω₀ ≠ 0) (hħ : ħ ≠ 0) (hε₀ : ε₀ ≠ 0) (hc : c ≠ 0) :
    spontaneousDecayProb ω₀ ħ ε₀ c μ t = gammaRad ω₀ ħ ε₀ c μ * |t| := by
  rw [spontaneousDecayProb]
  have hfun : (fun ω : ℝ => ω₀ ^ 2 * pDecay (couplingSq ω₀ ħ ε₀ c μ ω₀) ω ω₀ t)
      = (fun ω : ℝ => (ω₀ ^ 2 * couplingSq ω₀ ħ ε₀ c μ ω₀ * 4) *
          (Real.sin ((ω - ω₀) * t / 2) ^ 2 / (ω - ω₀) ^ 2)) := by
    funext ω
    rw [pDecay]
    ring
  rw [hfun, MeasureTheory.integral_const_mul, integral_lineshape,
    show |t / 2| = |t| / 2 by rw [abs_div]; norm_num]
  rw [couplingSq, gammaRad]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Exercise 7.29, step 1.** For physical (non-negative) time, the resonance-approximated mode
integral is linear in `t` with slope the emission rate:
`P(t) = γ_rad · t`  (Nielsen & Chuang 7.113 → the coefficient of 7.112). -/
theorem spontaneousDecayProb_eq_gammaRad_mul (ω₀ ħ ε₀ c μ t : ℝ)
    (hω₀ : ω₀ ≠ 0) (hħ : ħ ≠ 0) (hε₀ : ε₀ ≠ 0) (hc : c ≠ 0) (ht : 0 ≤ t) :
    spontaneousDecayProb ω₀ ħ ε₀ c μ t = gammaRad ω₀ ħ ε₀ c μ * t := by
  rw [spontaneousDecayProb_eq_gammaRad_mul_abs ω₀ ħ ε₀ c μ t hω₀ hħ hε₀ hc, abs_of_nonneg ht]

/-- **Exercise 7.29, step 2.** Differentiating `P(t) = γ_rad · t` in `t` recovers the spontaneous
emission rate `dP/dt = γ_rad` (Nielsen & Chuang 7.112) — the probability of decay per unit time. -/
theorem deriv_spontaneousDecayProb_eq_gammaRad (ω₀ ħ ε₀ c μ t : ℝ)
    (hω₀ : ω₀ ≠ 0) (hħ : ħ ≠ 0) (hε₀ : ε₀ ≠ 0) (hc : c ≠ 0) (ht : 0 < t) :
    deriv (fun s => spontaneousDecayProb ω₀ ħ ε₀ c μ s) t = gammaRad ω₀ ħ ε₀ c μ := by
  have heq : (fun s => spontaneousDecayProb ω₀ ħ ε₀ c μ s)
      =ᶠ[nhds t] (fun s => gammaRad ω₀ ħ ε₀ c μ * s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact spontaneousDecayProb_eq_gammaRad_mul ω₀ ħ ε₀ c μ s hω₀ hħ hε₀ hc (le_of_lt hs)
  rw [heq.deriv_eq]
  simp

end SpontaneousEmission
