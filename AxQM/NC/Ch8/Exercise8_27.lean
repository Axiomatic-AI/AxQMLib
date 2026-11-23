/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PhaseDampingChannel

/-!
# Nielsen & Chuang, Exercise 8.27 (phase damping = the phase-flip channel)

*(N&C p. 385.)*

Give the unitary relating phase-damping operation elements (8.127)-(8.128) to (8.129)-(8.130).

## The answer

Phase damping (N&C §8.3.6) has the operation elements (eqs. 8.127–8.128)

`E₀ = diag(1, √(1-λ))`,   `E₁ = diag(0, √λ)`,

and, after a unitary recombination (N&C Theorem 8.2, the unitary freedom of quantum operations), the
equivalent phase-flip elements (eqs. 8.129–8.130)

`Ẽ₀ = √α · I`,   `Ẽ₁ = √(1-α) · Z`,   `α = (1 + √(1-λ))/2`.

The unitary demanded by the exercise is the real, symmetric, orthogonal `2 × 2` matrix

`u = !![√α, √(1-α); √(1-α), -√α]`,

for which `Ẽₖ = Σⱼ uₖⱼ Eⱼ` (`k = 0, 1`) and `u` is unitary. Since `u` is unitary, N&C Theorem 8.2
then confirms `{E₀,E₁}` and `{Ẽ₀,Ẽ₁}` are two operator-sum representations of *one* quantum
operation — phase damping is exactly the phase-flip channel.

## The formalisation

The formal content of Exercise 8.27 is pure linear algebra about `2 × 2` operators and an
index-mixing unitary matrix (`LinearMap` on a qubit, `OrthonormalBasis`, `Matrix.unitaryGroup`).
Compare Exercises 8.21 and 8.22, and Theorem 8.2 itself. The phase-damping operation elements are
defined once in `AxQM/Concrete/PhaseDampingChannel.lean` (and also used in Exercises 8.26 and
8.28–8.31).

The formalisation is in `AxQM/Concrete/PhaseDampingChannel.lean`:

* `AxQM.Concrete.phaseDampKrausZero`, `…phaseDampKrausOne` (family
  `…phaseDampKraus`) — the phase-damping operation elements `E₀ = diag(1, √(1-λ))`,
  `E₁ = diag(0, √λ)` (eqs. 8.127–8.128).
* `AxQM.Concrete.phaseFlipProb` — the phase-flip "no-error" probability
  `α = (1 + √(1-λ))/2` (eqs. 8.129–8.130), with `…_nonneg`, `…_le_one`,
  `one_sub_phaseFlipProb_nonneg`.
* `AxQM.Concrete.phaseDampKrausZeroTilde`, `…phaseDampKrausOneTilde` (family
  `…phaseDampKrausTilde`) — the recombined phase-flip elements `Ẽ₀ = √α I`, `Ẽ₁ = √(1-α) Z`
  (eqs. 8.129–8.130).
* `AxQM.Concrete.phaseDampMixingUnitary` — **the answer to Exercise 8.27**: the relating
  matrix `u = !![√α, √(1-α); √(1-α), -√α]`, with `…_isHermitian`, `…_mul_self` (`u² = I`) and
  `…_mem_unitaryGroup` (`u` is unitary).
* `AxQM.Concrete.phaseDamp_unitaryFreedom` — **the exercise**: `Ẽₖ = Σⱼ uₖⱼ Eⱼ` for
  `k = 0, 1` (`0 ≤ λ ≤ 1`).

See the module docstring of `AxQM/Concrete/PhaseDampingChannel.lean` for the full argument.
-/
