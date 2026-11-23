/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Normed.Algebra.LieTrotter

/-!
# Nielsen & Chuang, Theorem 4.3 (the Trotter formula)

Trotter formula: lim (e^{iAt/n}e^{iBt/n})^n = e^{i(A+B)t} for Hermitian A,B.

The Trotter formula is the **Lie product formula** — a general fact about the exponential in a
Banach algebra: `lim (exp(x/n) exp(y/n))ⁿ = exp(x + y)` for *any* `x, y`, commuting or not. N&C's
`e^{iAt/n}` is the algebra exponential of `x/n` with `x = i·t·A`, so their Hermitian-operator
statement is the instance of the general limit at `x = i·t·A`, `y = i·t·B` (the `i`, the real `t`,
and Hermiticity all being absorbed into arbitrary algebra elements `x`, `y`). It is a statement of
analysis about the matrix/operator exponential.

## The declarations

In `ToMathlib/Analysis/Normed/Algebra/LieTrotter.lean`:

* `NormedSpace.tendsto_pow_exp_smul_mul_exp_smul` — **the Trotter / Lie product formula.** For `x y`
  in a Banach algebra (`[NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]`),
  `Tendsto (fun n : ℕ => (exp (n⁻¹ • x) * exp (n⁻¹ • y)) ^ n) atTop (𝓝 (exp (x + y)))`.
  This is (4.98): taking `x = (t : ℝ) • (Complex.I • A)`, `y = (t : ℝ) • (Complex.I • B)` on
  `Matrix (Fin d) (Fin d) ℂ` (a Banach algebra) recovers `lim (e^{iAt/n} e^{iBt/n})ⁿ = e^{i(A+B)t}`,
  with no commutativity hypothesis on `A, B`.

Supporting general lemmas (the `Complex.*`/`Real.*` versions existed in Mathlib but not the
Banach-algebra ones):

* `norm_pow_sub_pow_le` — the noncommutative telescoping bound `‖xⁿ - yⁿ‖ ≤ n·Mⁿ·‖x - y‖`.
* `NormedSpace.norm_exp_le` — `‖exp z‖ ≤ Real.exp ‖z‖` in a Banach algebra.
* `NormedSpace.norm_exp_sub_one_sub_id_le` — the second-order remainder bound
  `‖exp z - 1 - z‖ ≤ ‖z‖² · Real.exp ‖z‖`.

## Fidelity and generality

N&C state the formula for Hermitian `A, B`; the theorem proves the *stronger* statement for
arbitrary elements of any Banach algebra, of which `Matrix (Fin d) (Fin d) ℂ` — the setting of the
Hermitian operators — is an instance. It fixes no dimension and adds no hypothesis beyond those
making the exponential and the limit meaningful, so it is a faithful generalisation of the theorem,
never a specialisation of it. In particular the emphasised content "true even if `A` and `B` do not
commute" is exactly the general, `Commute`-free statement proved (the noncommutative telescoping
lemma `norm_pow_sub_pow_le` is what makes the non-commuting case go through).
-/
