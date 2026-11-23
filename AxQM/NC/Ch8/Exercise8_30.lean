/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RelaxationRates

/-!
# Nielsen & Chuang, Exercise 8.30 (`T₂ ≤ T₁/2`)

*(N&C p. 386.)*

Show amplitude damping has T2=T1/2, and combined amplitude+phase damping gives T2≤T1/2.

## Content

Reading `T₁`, `T₂` as the exercise's own words demand — *decay rates* — the damping channels of
§8.3.5–8.3.6 multiply a general qubit operator's matrix entries by fixed factors: amplitude damping
(`γ`) sends the excited population by `1-γ` and the coherence by `√(1-γ)`; phase damping (`λ`)
preserves the populations and sends the coherence by `√(1-λ)`. Hence the longitudinal rate is
`Γ₁ = -log(1-γ)` and the transverse rate of the combined channel is
`Γ₂ = -log(√(1-γ)·√(1-λ)) = Γ₁/2 + Γ_φ`, with pure-dephasing rate `Γ_φ = -log√(1-λ) ≥ 0` — the exact
additive-rate identity that *is* the exercise: pure amplitude damping (`λ = 0`) gives `Γ₂ = Γ₁/2`
(N&C's `T₂ = T₁/2`), and adding phase damping gives `Γ₂ ≥ Γ₁/2`.

**On the printed inequality.** N&C's second relation `T₂ ≤ T₁/2` has a *reversed* inequality: adding
phase damping makes the coherence decay faster, so its transverse rate can only *increase*
(`Γ₂ ≥ Γ₁/2`), equivalently `T₂ ≤ 2 T₁` in the relaxation-*time* convention (`T = 1/Γ`) of
eq. (7.144) — the printed `T₁/2` is a slip for `2 T₁`. We formalise the physically correct,
convention-independent content and document the discrepancy; see
the module docstring of `AxQM/Concrete/RelaxationRates.lean` for the full analysis.

Its formal content is linear algebra about channel matrix entries (`LinearMap`, `inner`,
`OrthonormalBasis`, `Real.log`/`Real.sqrt`). Compare Exercises 8.22 and 8.27.

## The formalisation

The formalisation is in `AxQM/Concrete/RelaxationRates.lean`:

* `AxQM.Concrete.phaseDampingChannel_inner_zero_one` (coherence damped by `√(1-λ)`) and
  `…_inner_one_one` (excited population preserved) — matrix entries of the
  `AxQM.Concrete.phaseDampingChannel` (Ex 8.26).
* `AxQM.Concrete.combinedDampChannel` — amplitude then phase damping, with
  `combinedDampChannel_inner_zero_one` (coherence damped by `√(1-γ)·√(1-λ)`) and
  `combinedDampChannel_inner_one_one` (population damped by `1-γ`).
* `AxQM.Concrete.longitudinalRate` / `transverseRate` / `pureDephasingRate` — the `T₁`/`T₂`
  rates read off those factors (`decayRate f = -log f`).
* `AxQM.Concrete.transverseRate_eq` — **the exercise**: `Γ₂ = Γ₁/2 + Γ_φ`.
* `AxQM.Concrete.transverseRate_amplitudeDamping` — **part 1**, `T₂ = T₁/2` (`λ = 0`).
* `AxQM.Concrete.transverseRate_ge_half_longitudinal` — **part 2**, `Γ₁/2 ≤ Γ₂`
  (equivalently `T₂ ≤ 2 T₁`); `transverseRate_gt_half_longitudinal` is the strict form refuting the
  printed `≤`.
-/
