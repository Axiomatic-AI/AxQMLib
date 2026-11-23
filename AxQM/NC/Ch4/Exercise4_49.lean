/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Normed.Algebra.ExponentialSplitting

/-!
# Nielsen & Chuang, Exercise 4.49 (Baker–Campbell–Hausdorff formula)

*(N&C p. 208.)*

Prove the Baker-Campbell-Hausdorff formula (4.105) and Eqns (4.103)-(4.104).

Equations (4.103)–(4.105) are small-`Δt` (Taylor) error estimates for the exponential in a Banach
algebra — pure analysis of the matrix/operator exponential. They are formalised next to the
Lie–Trotter development (`Theorem4_3`).

The `Asymptotics.IsBigO` predicate `f =O[𝓝 0] (fun Δt => Δtⁿ)` is the faithful rendering of
"`… + O(Δtⁿ)` as `Δt → 0`": it asserts exactly a constant `C` and a neighbourhood of `0` on which
`‖f Δt‖ ≤ C·|Δt|ⁿ`. The statements are stated over the *two-sided* filter `𝓝 0` (not `𝓝[≥] 0`), so
they are the full strength of the textbook claim, not a weakening to positive time steps.

## The `i` and the generality

As with the Lie–Trotter formula (`Theorem4_3`), the general Banach-algebra statement over arbitrary
`x, y : 𝔸` **subsumes** N&C's imaginary-unit Hermitian form: `e^{iAΔt} = exp(Δt • x)` with
`x = i·A`, so `e^{i(A+B)Δt} = e^{iAΔt} e^{iBΔt} + O(Δt²)` is the instance `x = i·A`, `y = i·B` of
the theorem below (the `i` and Hermiticity are absorbed into the arbitrary algebra elements
`x, y`).
Equation (4.105) N&C already state without the `i`, directly as the general form. Proving the
`x, y`-general statement is a faithful generalisation, not a specialisation.

## The formalisation

In `ToMathlib/Analysis/Normed/Algebra/ExponentialSplitting.lean`, for `x y` in a Banach algebra
(`[NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]`), all as
`Asymptotics.IsBigO` estimates over the two-sided filter `𝓝 0`:

* `NormedSpace.isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul` — **equation (4.103)**:
  `exp (t • (x + y)) - exp (t • x) * exp (t • y) =O[𝓝 0] (fun t => t ^ 2)`.
* `NormedSpace.isBigO_exp_smul_add_sub_exp_smul_mul_exp_smul_mul_exp_lie` — **equation (4.105)**,
  the second-order Baker–Campbell–Hausdorff formula:
  `exp (t • (x + y)) - exp (t • x) * exp (t • y) * exp (t ^ 2 • ((-2⁻¹ : ℝ) • ⁅x, y⁆))
  =O[𝓝 0] (fun t => t ^ 3)`, where `⁅x, y⁆ = x * y - y * x`. The exponent `t² • (-½ • ⁅x, y⁆)` is
  N&C's `-½[A, B]Δt²`.
* `NormedSpace.isBigO_exp_smul_add_sub_exp_half_smul_mul_exp_smul_mul_exp_half_smul` — **equation
  (4.104)**, the symmetric (Strang) splitting:
  `exp (t • (x + y)) - exp ((t / 2) • x) * exp (t • y) * exp ((t / 2) • x)
  =O[𝓝 0] (fun t => t ^ 3)`. The symmetric half-step arrangement of the two `x`-factors makes the
  second-order term collapse to `½(x+y)²` directly, so — unlike the ordered form (4.105) — no
  commutator-correction factor appears.

Reusable building blocks in the same file: the first- and second-order single-factor Taylor
remainders `NormedSpace.isBigO_exp_smul_sub_one_sub_smul` and
`NormedSpace.isBigO_exp_smul_sub_taylor2` (the latter resting on the third-order remainder bound
`NormedSpace.norm_exp_sub_one_sub_id_sub_half_sq_le`, imported from the Lie–Trotter development),
and the second- and three-factor product expansions
`NormedSpace.isBigO_exp_smul_mul_exp_smul_sub_taylor2` and
`NormedSpace.isBigO_exp_smul_mul_exp_smul_mul_exp_smul_sub_taylor2`.

## Proof strategy

Each equation reduces to matching second-order Taylor polynomials. (4.103) uses only the
first-order remainder. (4.105) expands `exp(t•x) exp(t•y)` to second order
`1 + t•(x+y) + ½t²•(x² + 2xy + y²) + O(t³)` and multiplies in the commutator factor
`exp(-½t²•⁅x,y⁆) = 1 - ½t²•⁅x,y⁆ + O(t³)`; the key cancellation `x² + 2xy + y² - ⁅x, y⁆ = (x+y)²`
recovers `exp(t•(x+y))`'s polynomial `1 + t•(x+y) + ½t²•(x+y)²`. (4.104), by contrast, needs no
correction factor: the symmetric half-step product `exp(½t•x) exp(t•y) exp(½t•x)` already has the
second-order polynomial `1 + t•(x+y) + ½t²•(x+y)²`, because
`2(½x)² + (½x)y + y(½x) + ½y² = ½(x+y)²`.

## Completeness

All three of N&C's equations (4.103), (4.104), and (4.105) are formalised and proved, as the
`Asymptotics.IsBigO` estimates listed above. Equation (4.104) reuses all of
the second-order machinery of (4.105): it expands the three half-step factors
`exp(½t•x) exp(t•y) exp(½t•x)` via the three-factor product expansion
`NormedSpace.isBigO_exp_smul_mul_exp_smul_mul_exp_smul_sub_taylor2`, and the *symmetric* arrangement
makes the `t²`-coefficient `2(½x)² + (½x)y + y(½x) + ½y² = ½(x+y)²` collapse directly, so no
commutator-correction factor is needed.
-/
