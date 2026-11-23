/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliExponential

/-!
# Nielsen & Chuang, Exercise 2.35 (Exponential of the Pauli matrices)

Prove exp(i theta v.sigma) = cos(theta) I + i sin(theta) v.sigma.

## The declarations

The exercise is `exp (z • a) = …` for the involution `a = v · σ` (`a * a = 1` for a unit vector),
so it splits into a general lemma and its Pauli instantiation.

* General engine, in `ToMathlib/Analysis/Normed/Algebra/ExponentialInvolution.lean`:
  `NormedSpace.exp_smul_of_mul_self_eq_one` — in a normed `ℂ`-algebra, if `a * a = 1` then
  `exp (z • a) = Complex.cosh z • 1 + Complex.sinh z • a`, by the even/odd split of the exponential
  series. This holds for any involution (a Pauli matrix, a reflection, …).

* Pauli instantiation, in `AxQM/Concrete/PauliExponential.lean`:
  `AxQM.Concrete.pauliDot_exp_of_unit` — for a unit vector `n` and real `θ`,
  `exp ((θ * i) • pauliDot n) = cos θ • 1 + (sin θ * i) • pauliDot n`, i.e. exactly N&C's
  `exp(i θ v · σ) = cos θ · I + i sin θ · (v · σ)`. It is obtained from the general lemma with
  `z = θ * i` via the involution `(v · σ)² = I` (`pauliDot_mul_self_of_unit`) and
  `Complex.cosh_mul_I` / `Complex.sinh_mul_I`.

The unit-vector hypothesis is essential: it is precisely what makes `v · σ` an involution, and hence
what makes the exponential collapse to the two-term trigonometric form.
-/
