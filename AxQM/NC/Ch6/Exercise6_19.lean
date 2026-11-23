/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.OrPolynomial

/-!
# Nielsen & Chuang, Exercise 6.19 (the OR polynomial represents OR)

*(N&C p. 273.)*

Show P(X)=1-(1-X0)(1-X1)...(1-X_{N-1}) represents the OR function.

## Statement and reading

In the method of polynomials (N&C §6.7) a polynomial `p : Rᴺ → R` *represents* a Boolean function
`F` when `p(X) = F(X)` for all `X ∈ {0, 1}ᴺ`. The OR function is `X₀ ∨ X₁ ∨ ⋯ ∨ X_{N-1}` — it is
`1` iff some coordinate is `1`. Each factor `1 − Xₖ` is `1` when `Xₖ = 0` and `0` when `Xₖ = 1`, so
`∏ₖ (1 − Xₖ)` is `1` exactly when every `Xₖ = 0`; hence `1 − ∏ₖ (1 − Xₖ)` is `0` when all
coordinates vanish and `1` otherwise, which is exactly OR.

## The formalisation

The statement is pure commutative algebra — a named multivariate polynomial over a commutative ring
and its evaluation on the Boolean cube. The formalisation is in `AxQM/Concrete/OrPolynomial.lean`
(namespace `AxQM.Concrete`), for an arbitrary finite index type `σ` (N&C's `σ = Fin N`) and
commutative ring `R` (N&C's `R = ℝ`):

* `Represents p F` — N&C's predicate: `p` evaluated at every Boolean point (`true ↦ 1`, `false ↦ 0`)
  returns the `{0, 1}`-encoded value of `F`.
* `orFun` — the OR Boolean function `b ↦ (∃ k, bₖ = true)`.
* `orPoly` — the polynomial `1 - ∏ᵢ (1 - Xᵢ)`.
* `eval_orPoly` — its value at a Boolean point: `1` if some coordinate is `true`, else `0`.
* `orPoly_represents_orFun` — **Exercise 6.19 itself**: `orPoly` represents `orFun`.
* `isMultilinear_orPoly` — `orPoly` is multilinear, so (with Exercise 6.18) it is *the*
  minimum-degree representative of OR.

## Faithfulness

The result is stated for an arbitrary finite index type `σ` and commutative ring `R` — strictly more
general than N&C's `Fin N`/`ℝ`, not a weakening. The representation identity holds over any
commutative ring; the multilinearity fact additionally assumes `R` nontrivial (vacuous over the zero
ring), which N&C's `ℝ` satisfies.
-/
