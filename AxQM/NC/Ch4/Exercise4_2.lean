/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution
import AxQM.Concrete.Rotation

/-!
# Nielsen & Chuang, Exercise 4.2 (Euler's formula for an involution; the rotation operators)

For real x and A with A^2=I, show exp(iAx)=cos(x)I+i sin(x)A; verify rotation eqns.

Equations (4.4)–(4.6) are the definitions-with-closed-form of the single-qubit rotation operators
`R_x(θ) = exp(-iθX/2) = cos(θ/2) I - i sin(θ/2) X`, and likewise `R_y`, `R_z` about the `ŷ`, `ẑ`
axes, where `X, Y, Z` are the Pauli matrices (all of which satisfy `P² = I`).

Equation (4.7) is a general fact about the exponential of a scalar multiple of an *involution* —
it holds in any normed `ℂ`-algebra, N&C's "`A` a matrix" being one instance — and the rotation
operators are concrete `2 × 2` complex matrices. The abstract identity is in `ToMathlib/` and the
concrete Pauli rotations in `AxQM/Concrete/`.

## The declarations

**Equation (4.7)**, in `ToMathlib/Analysis/Normed/Algebra/ExponentialInvolution.lean`:

* `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one` — for `a` an involution (`a * a = 1`) in a normed
  `ℂ`-algebra and a real `x`,
  `exp ((x * i) • a) = cos x • 1 + (sin x * i) • a`.
  This is the real-angle trigonometric form of
  `NormedSpace.exp_smul_of_mul_self_eq_one` (`exp (z • a) = cosh z • 1 + sinh z • a`), obtained by
  taking `z = x * i` and applying `Complex.cosh_mul_I` / `Complex.sinh_mul_I`. It is also used by
  `Concrete.pauliDot_exp_of_unit` (N&C Ex 2.35).

**Equations (4.4)–(4.6)** (and the general axis rotation eq. 4.8), in
`AxQM/Concrete/Rotation.lean`:

* `AxQM.Concrete.rotAxis n θ = exp(-iθ (n·σ)/2)` — the general rotation operator (eq. 4.8),
  with `rotAxis_eq_of_unit` its closed form `cos(θ/2) I - i sin(θ/2) (n·σ)` for a unit axis `n`.
* `AxQM.Concrete.rotX`, `rotY`, `rotZ` = `rotAxis` at `x̂ = ![1,0,0]`, `ŷ`, `ẑ` — the
  operators `R_x(θ) = exp(-iθX/2)` etc. (eqs 4.4–4.6).
* `AxQM.Concrete.rotX_eq`, `rotY_eq`, `rotZ_eq` — their explicit `2 × 2` matrices. The
  operator form `R_P(θ) = cos(θ/2) I - i sin(θ/2) P` of eqs (4.4)–(4.6) is the `rotAxis_eq_of_unit`
  instance at the corresponding standard-basis unit axis (e.g. `rotAxis_eq_of_unit (n := ![1,0,0])`,
  whose `pauliDot ![1,0,0] = X`).

## N&C ↦ Lean dictionary and fidelity

* **`exp(iAx)`** is `NormedSpace.exp (((x : ℂ) * Complex.I) • a)`: the Mathlib exponential of
  `i x a = (x·i) • a`. The `i` is `Complex.I`; scalar–matrix multiplication `i x A` is the module
  action `•`.
* **`A² = I`** is `a * a = 1` (`sq`/`pow_two` unfolds `A²` to `a * a`; `1` is the algebra unit,
  which for `Matrix (Fin 2) (Fin 2) ℂ` is the identity matrix `I`).
* **Generality, not weakening.** N&C state (4.7) for "`A` a matrix";
  `exp_smul_mul_I_of_mul_self_eq_one` proves it for *any* involution in a normed `ℂ`-algebra, of
  which `Matrix (Fin 2) (Fin 2) ℂ` — the setting of the Pauli rotations — is an instance. It fixes
  no dimension and adds no hypothesis beyond `A² = I` and `x` real, so it is a faithful
  generalisation of the exercise, never a specialisation of it.
* **The rotation operators** `R_x, R_y, R_z` are `rotAxis` at the standard-basis axes, i.e. the
  `x = -θ/2` instances N&C prescribe (`e^{-iθP/2}`): `rotAxis_eq_of_unit` carries the `+` of (4.7)
  into the `-` of (4.4)–(4.6) via `Real.cos_neg` (`cos(-θ/2) = cos(θ/2)`) and `Real.sin_neg`
  (`sin(-θ/2) = -sin(θ/2)`). The general axis rotation `R_n̂(θ) = exp(-iθ n̂·σ/2)` (eq. 4.8) and its
  closed form are `rotAxis` / `rotAxis_eq_of_unit` — both in `Rotation.lean` — and its
  involution `(n̂·σ)² = I` is `Concrete.pauliDot_mul_self_of_unit`.
-/
