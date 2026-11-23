/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BoltzmannTemperature

/-!
# Nielsen & Chuang, Exercise 8.25 (temperature of the GAD stationary state `ρ∞`)

*(N&C p. 382.)*

Find temperature T describing stationary state ρ∞ of generalized amplitude damping via Boltzmann.

Here `ρ∞ = !![p, 0; 0, 1-p]` is the stationary state of the **generalized amplitude damping**
channel `E_GAD` (N&C §8.3.5, eq. 8.120), the finite-temperature relaxation channel; its `|0⟩` and
`|1⟩`
populations are `p` and `1 - p`. Matching them to the Boltzmann populations `p₀ = p`, `p₁ = 1 - p`
gives `p/(1-p) = e^{(E₁-E₀)/(k_B T)}`, so the temperature describing `ρ∞` is

`T = (E₁ - E₀) / (k_B ln(p/(1-p)))`.

## The formalisation

The formal content of Exercise 8.25 is pure **real analysis**: the Boltzmann occupation
probabilities `p₀, p₁`, the partition function `Z`, and the temperature formula are functions of
the real quantities `E₀, E₁, k_B, T, p`, using only `ℝ`, `Real.exp`, and `Real.log`. Compare
Exercises 8.16, 8.17 and 8.22. The `ρ∞` populations `(p, 1-p)` enter only as the target values the
temperature must reproduce, so the exercise reduces to inverting the Boltzmann relation.

The formalisation is in `AxQM/Concrete/BoltzmannTemperature.lean`:

* `AxQM.Concrete.boltzmannGround`, `AxQM.Concrete.boltzmannExcited` — the
  Boltzmann occupation probabilities `p₀ = e^{-E₀/(k_B T)}/Z`, `p₁ = e^{-E₁/(k_B T)}/Z`.
* `AxQM.Concrete.boltzmann_partition_pos` — the partition function `Z > 0`;
  `AxQM.Concrete.boltzmannGround_add_boltzmannExcited` — normalization `p₀ + p₁ = 1`.
* `AxQM.Concrete.boltzmannTemperature` — **the answer**:
  `T = (E₁ - E₀) / (k_B ln(p/(1-p)))`.
* `AxQM.Concrete.boltzmannGround_boltzmannTemperature`,
  `AxQM.Concrete.boltzmannExcited_boltzmannTemperature` — **Exercise 8.25**: at that
  temperature the populations are exactly `p` and `1 - p`, i.e. the Boltzmann distribution
  reproduces the stationary state `ρ∞ = diag(p, 1-p)`.
* `AxQM.Concrete.boltzmannTemperature_unique` — it is the *unique* nonzero temperature
  that does so, so it genuinely "describes the state `ρ∞`".

See the module docstring of `AxQM/Concrete/BoltzmannTemperature.lean` for the full argument.
-/
