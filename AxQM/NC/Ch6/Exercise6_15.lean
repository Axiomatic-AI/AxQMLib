/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.OrthonormalDistanceSum

/-!
# Nielsen & Chuang, Exercise 6.15 (`∑ₓ ‖ψ − x‖² ≥ 2N − 2√N`)

*(N&C p. 270.)*

Via Cauchy-Schwarz show sum_x ||psi - x||^2 >= 2N - 2sqrt(N) for orthonormal basis {|x>}.

This is the missing step in the proof (N&C §6.6) that the quantum search algorithm is optimal: it
supplies the lower bound `Fₖ ≥ 2N − 2√N` (for `Fₖ ≡ ∑ₓ ‖x − ψₖ‖²`) which, combined with the upper
bound `Eₖ ≤ (2 − √2)N`, forces the deviation `Dₖ = Ω(N)` and hence `k = Ω(√N)` oracle queries.

## The formalisation

The statement is pure inner-product-space geometry — a normalized vector, a finite orthonormal
family, the induced norm, and the Cauchy–Schwarz/Bessel inequalities. The formalisation is in
`ToMathlib/Analysis/InnerProductSpace/OrthonormalDistanceSum.lean`, for an inner-product space `E`
over an `RCLike` field `𝕜` (N&C's `𝕜 = ℂ` is the special case), a finite
orthonormal family `v : ι → E` (`Orthonormal 𝕜 v`, `N = Fintype.card ι`) and a vector `ψ`:

* `Orthonormal.sum_re_inner_le_sqrt_card_mul_norm` — the **Cauchy–Schwarz content** the exercise
  asks for: `∑ x, RCLike.re (inner 𝕜 ψ (v x)) ≤ √N · ‖ψ‖`. The proof bounds each real part by the
  norm of the inner product, applies the finite-sum Cauchy–Schwarz inequality
  (`sq_sum_le_card_mul_sum_sq`, `(∑ₓ aₓ)² ≤ N·∑ₓ aₓ²`) against the all-ones vector, and closes with
  Bessel's inequality (`Orthonormal.sum_inner_products_le`, `∑ₓ ‖⟪v x, ψ⟫‖² ≤ ‖ψ‖²`).
* `Orthonormal.two_mul_card_sub_two_mul_sqrt_card_le_sum_norm_sub_sq` — **Exercise 6.15 / eq. (6.53)
  itself**: for a normalized `ψ` (`‖ψ‖ = 1`),
  `2·N − 2·√N ≤ ∑ x, ‖ψ − v x‖²`.
  Expanding `‖ψ − v x‖² = 2 − 2·re ⟪ψ, v x⟫` (both `ψ` and each `v x` are unit vectors) rewrites the
  sum as `2N − 2·∑ x, re ⟪ψ, v x⟫`, and the previous lemma (at `‖ψ‖ = 1`) bounds
  `∑ x, re ⟪ψ, v x⟫ ≤ √N`.

## Faithfulness

The result is stated for an arbitrary finite **orthonormal family** rather than a full orthonormal
basis: Bessel's inequality — the only place orthonormality is used — does not require the family to
span the space, so this is the natural generality and captures (indeed slightly strengthens) N&C's
"set of `N` orthonormal basis vectors", not a weakening. `N&C`'s `‖ψ‖ = 1` (normalized state) is
kept as the hypothesis of the main statement; the underlying Cauchy–Schwarz lemma is stated more
generally with an explicit `‖ψ‖` factor.
-/
