/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.RingTheory.MvPolynomial.Multilinear

/-!
# Nielsen & Chuang, Exercise 6.18 (uniqueness of the multilinear representation)

*(N&C p. 273.)*

Prove the minimum-degree multilinear polynomial representing a Boolean function F is unique.

## Statement and reading

A polynomial `p : Rᴺ → R` *represents* `F` if `p(X) = F(X)` for all `X ∈ {0, 1}ᴺ` (N&C §6.7). In
the method of polynomials N&C considers only **multilinear** polynomials — every variable to degree
at most one — because `Xₖ² = Xₖ` on `{0, 1}`, so any representative reduces to a multilinear one of
no larger degree. Within multilinear polynomials the representative is unique, and being the unique
one it is automatically the minimum-degree representative; that is the faithful content of the
exercise. (The multilinear restriction is essential: without it the minimum-degree representative is
genuinely non-unique — e.g. `X₀X₁ + X₀²` and `X₀X₁ + X₀` are distinct degree-`2` polynomials
computing the same function on `{0, 1}²`.)

## The formalisation

The statement is pure commutative algebra — multivariate polynomials over a commutative ring, their
evaluation on the Boolean cube `{0, 1} ⊆ R`, and per-variable degree. The formalisation is in
`ToMathlib/RingTheory/MvPolynomial/Multilinear.lean`, for an arbitrary index type `σ` (N&C's
`σ = Fin N`) and commutative ring `R` (N&C's `R = ℝ`):

* `MvPolynomial.IsMultilinear p` — the predicate `∀ i, p.degreeOf i ≤ 1` (every variable to degree
  at most one), with `MvPolynomial.isMultilinear_iff_mem_restrictDegree` identifying it with
  membership in the existing Mathlib submodule `MvPolynomial.restrictDegree σ R 1`.
* `MvPolynomial.IsMultilinear.eq_zero_of_forall_eval_boolean` — a multilinear polynomial vanishing
  at every Boolean point is `0` (proved over any `CommSemiring` by evaluating at a support-minimal
  monomial's own `0/1` indicator, so only that monomial's — nonzero — coefficient survives).
* `MvPolynomial.IsMultilinear.eq_of_forall_eval_boolean` — **Exercise 6.18 itself**: two multilinear
  polynomials agreeing at every point of `{0, 1}ˢ` are equal, obtained by applying the vanishing
  form to their difference (`MvPolynomial.IsMultilinear.sub`).

## Faithfulness

The result is stated for an arbitrary index type `σ` and commutative ring `R` — strictly more
general than N&C's `Fin N`/`ℝ`, not a weakening — with no nontriviality hypothesis on `R`. The
"multilinear" hypothesis is exactly N&C's standing restriction in §6.7 (and, as noted above,
necessary for the claim to hold), so the theorem captures the exercise's content rather than a
narrowed version of it.
-/
