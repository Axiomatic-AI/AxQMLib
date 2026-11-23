/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SpontaneousEmission

/-!
# Nielsen & Chuang, Exercise 7.29 (spontaneous emission)

*(N&C p. 316.)*

Spontaneous emission: derive rate γ_rad (7.112) from (7.110)-(7.111) by integrating over modes and
differentiating.

Here (N&C 7.110) `p_decay(ω, t) = g²(ω) · 4 sin²(½(ω-ω₀)t)/(ω-ω₀)²` is the lowest-order decay
probability of an excited atom coupled to a single empty optical mode of frequency `ω` (from the
Jaynes–Cummings interaction 7.109); (7.111) `g²(ω) = ω₀² |⟨0|μ|1⟩|²/(2ℏω ε₀ c²)` is the coupling;
and (7.112) `γ_rad = ω₀³ |⟨0|μ|1⟩|²/(3π ℏ ε₀ c⁵)` is the target emission rate.

## The resonance/peak approximation

The literal integrand `ω² p_decay` decays only like `1/ω` at large `ω` (`ω² g²(ω) ∝ ω`, against the
`sin²`-lineshape whose average is `½`), so `∫₀^∞ ω² p_decay dω` — and the `-∞`-extended integral of
N&C's hint — **diverge** logarithmically. The textbook derivation (as N&C's hint signals) treats the
lineshape `4 sin²(½(ω-ω₀)t)/(ω-ω₀)²` as a resonance sharply peaked at `ω = ω₀`: the slowly-varying
prefactor `ω² g²(ω)` is taken at the peak `ω = ω₀`, and the remaining line integral over all of `ℝ`
is `∫_ℝ 4 sin²(½(ω-ω₀)t)/(ω-ω₀)² dω = 2π|t|`. This peak-approximated integral is the physically
honest, finite content — the only reading yielding N&C's `γ_rad` — and is what we formalise; see the
module docstring of `AxQM/Concrete/SpontaneousEmission.lean` for the full discussion.

The content is entirely a real-analysis computation over `ℝ`: `p_decay`, `g²`, `γ_rad`
and the mode integral are functions of real parameters (`ω₀, ℏ, ε₀, c, |⟨0|μ|1⟩|, ω, t`).
Compare the Ch. 7 exercises 7.21 (`AxQM/Concrete/KerrTwoPhotonPhase.lean`) and 7.22
(`AxQM/Concrete/KerrAbsorptionLoss.lean`).

## The formalisation

In `AxQM/Concrete/SpontaneousEmission.lean` (the analytic
dependency `Real.integral_sin_sq_mul_div_sq : ∫_ℝ sin²(bx)/x² = π|b|` is in
`ToMathlib/Analysis/SpecialFunctions/Integrals/SinSqDivSq.lean`):

* `SpontaneousEmission.couplingSq` — the coupling `g²(ω)` (N&C 7.111).
* `SpontaneousEmission.pDecay` — the single-mode decay probability `p_decay` (N&C 7.110).
* `SpontaneousEmission.gammaRad` — the emission rate `γ_rad` (N&C 7.112).
* `SpontaneousEmission.spontaneousDecayProb` — the resonance-approximated mode integral `P(t)`
  (N&C 7.113).
* `SpontaneousEmission.spontaneousDecayProb_eq_gammaRad_mul_abs` — the master identity
  `P(t) = γ_rad · |t|`.
* `SpontaneousEmission.spontaneousDecayProb_eq_gammaRad_mul` — **step 1** (`t ≥ 0`):
  `P(t) = γ_rad · t`.
* `SpontaneousEmission.deriv_spontaneousDecayProb_eq_gammaRad` — **step 2** (`t > 0`):
  `dP/dt = γ_rad`, the emission rate (N&C 7.112).
-/
