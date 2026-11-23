/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Rotation

/-!
# Nielsen & Chuang, Exercise 4.5 (`(n̂·σ)² = I`, and the rotation formula eq. 4.8)

Prove (n.sigma)^2=I and use it to verify the rotation formula R_n(theta).

Here `n̂ = (n₀, n₁, n₂)` is a real *unit* three-vector, `σ⃗ = (X, Y, Z)` is the vector of
Pauli matrices, and `n̂·σ = n₀ X + n₁ Y + n₂ Z`. Equation (4.8) is the definition-with-closed-form
of the rotation about the `n̂` axis,

`R_n̂(θ) ≡ exp(−iθ (n̂·σ)/2) = cos(θ/2) I − i sin(θ/2) (n₀ X + n₁ Y + n₂ Z)`.

Both claims are pure `2 × 2` complex-matrix statements — the involution `(n̂·σ)² = I` and the
exponential/closed-form identity (4.8) — about matrices, the matrix exponential, and the real
trigonometric functions.

## The formalisation

The `n̂·σ` involution is in `AxQM/Concrete/Pauli.lean` and the rotation operators are in
`AxQM/Concrete/Rotation.lean` (the §4.2 rotation-operators development):

**Part 1 — `(n̂·σ)² = I`** (in `AxQM/Concrete/Pauli.lean`):

* `AxQM.Concrete.pauliDot n = n₀ • X + n₁ • Y + n₂ • Z` — the combination `n̂·σ`.
* `AxQM.Concrete.pauliDot_mul_self` — the general form `(n̂·σ)² = ‖n‖² • I` (with
  `‖n‖² = n₀² + n₁² + n₂²`): the Pauli cross-terms anticommute and cancel, and the diagonal terms
  sum the squared components.
* `AxQM.Concrete.pauliDot_mul_self_of_unit` — the exercise's claim, `(n̂·σ)² = I` for a
  unit vector (`n₀² + n₁² + n₂² = 1`), an immediate corollary.

**Part 2 — verify Equation (4.8)** (in `AxQM/Concrete/Rotation.lean`):

* `AxQM.Concrete.rotAxis n θ = exp((−(θ/2)·i) • (n̂·σ))` — the rotation operator, defined
  *literally* as N&C's `exp(−iθ(n̂·σ)/2)` (the left-hand side / `≡` of eq. 4.8).
* `AxQM.Concrete.rotAxis_eq_of_unit` — the closed form (the right-hand side of eq. 4.8) for
  a unit axis: `R_n̂(θ) = cos(θ/2) • I − (sin(θ/2)·i) • (n̂·σ)`.

## "Use this to verify": the dependency chain

The exercise asks to *use* `(n̂·σ)² = I` to establish (4.8), and the Lean proof does exactly that.
`rotAxis_eq_of_unit` is proved by rewriting `rotAxis` through
`AxQM.Concrete.pauliDot_exp_of_unit` (N&C Exercise 2.35, in
`AxQM/Concrete/PauliExponential.lean`), the closed form
`exp(iθ (n̂·σ)) = cos θ • I + i sin θ • (n̂·σ)`, and then carrying the `x = −θ/2` sign through with
`Real.cos_neg` / `Real.sin_neg`. In turn `pauliDot_exp_of_unit` is *definitionally* the application
of the general Euler-formula-for-an-involution `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one`
(the `ToMathlib` contribution of Exercise 4.2) to the involution hypothesis
`pauliDot_mul_self_of_unit`. So `(n̂·σ)² = I` is precisely the fact that makes (4.8) go through, as
the textbook intends.

## N&C ↦ Lean dictionary and fidelity

* **`n̂·σ`** is `pauliDot n` for `n : Fin 3 → ℝ`; N&C's `n̂·σ ≡ Σᵢ nᵢ σᵢ` is the definitional
  `n₀ • X + n₁ • Y + n₂ • Z`.
* **`n̂` a unit vector** is the scalar hypothesis `n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1` (matching how
  `AxQM/Concrete/Pauli.lean` models normalization), used in exactly the same way N&C uses `|n̂| =
  1`.
* **`exp(−iθ(n̂·σ)/2)`** is `NormedSpace.exp` of `(−(θ/2)·i) • pauliDot n`; the `−θ/2` is N&C's, and
  `rotAxis` is defined to be this exponential, so the `≡` of (4.8) is a definitional equality.
* **The closed form** `cos(θ/2) I − i sin(θ/2) (n̂·σ)` is `rotAxis_eq_of_unit` verbatim; the `−`
  (versus the `+` of the Exercise 2.35 form at a positive angle) is produced by `Real.cos_neg` /
  `Real.sin_neg` on `θ/2`, not by an added hypothesis.
* **Generality, not weakening.** The statements fix no extra structure and add no hypothesis beyond
  N&C's own (`n̂` real and unit, `θ` real): `pauliDot_mul_self` even proves the stronger
  unnormalised `(n̂·σ)² = ‖n‖² I`, of which the exercise's `(n̂·σ)² = I` is the unit-vector case.

## Relationship to Exercise 4.2

Exercise 4.2 (`exp(iAx) = cos x · I + i sin x · A` for an involution `A`, used to verify the
*coordinate* rotations `R_x, R_y, R_z`, eqs 4.4–4.6) contributed the general
`NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` in `ToMathlib/`. Exercise 4.5 is its
*general-axis* companion: the same abstract identity, now applied to the Pauli-specific involution
`(n̂·σ)² = I` to verify eq. 4.8 for an arbitrary axis `n̂`. The shared abstract
core is in `Mathlib/`, the Pauli-specific instances in `AxQM/Concrete/`.
-/
