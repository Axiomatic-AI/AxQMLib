/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.GramSchmidtNormedRecursion

/-!
# Nielsen & Chuang, Exercise 2.8 (Gram–Schmidt produces an orthonormal basis)

Prove the Gram-Schmidt procedure produces an orthonormal basis for V.

The *procedure* is the one N&C write on p. 66 (eq. 2.17): given a basis `|w₁⟩, …, |w_d⟩` of an
inner-product space `V`, set `|v₁⟩ ≡ |w₁⟩ / ‖|w₁⟩‖` and, for `1 ≤ k ≤ d-1`, put
`u_{k+1} ≡ |w_{k+1}⟩ - ∑_{i=1}^{k} ⟨v_i|w_{k+1}⟩ |v_i⟩` and `|v_{k+1}⟩ ≡ u_{k+1} / ‖u_{k+1}‖`.
This is the *normalize-at-each-step* form: each new vector is `f`'s residual after removing its
projection onto the previously produced **orthonormal** vectors, then normalised. The claim is that
`|v₁⟩, …, |v_d⟩` are orthonormal and form a basis for `V`.

## The declarations

Mathlib already develops Gram–Schmidt (`InnerProductSpace.gramSchmidt`, and its normalisation
`gramSchmidtNormed 𝕜 f n = ‖gramSchmidt 𝕜 f n‖⁻¹ • gramSchmidt 𝕜 f n`), and already proves the
*conclusion* of the exercise for `gramSchmidtNormed`:

* `InnerProductSpace.gramSchmidtNormed_orthonormal` — orthonormality (for a linearly independent
  input `f`), N&C's `⟨v_i|v_j⟩ = δ_{ij}`;
* `InnerProductSpace.gramSchmidtNormed_linearIndependent` — linear independence.

What was **missing** is that `gramSchmidtNormed` is literally the procedure N&C write down:
Mathlib's recursion `gramSchmidt_def''` subtracts projections onto the *unnormalized*
`gramSchmidt 𝕜 f i` (with the squared-norm denominators), whereas N&C (eq. 2.17) subtracts
projections onto the *normalized* `|v_i⟩` and normalises at each step. The new file
`ToMathlib/Analysis/InnerProductSpace/GramSchmidtNormedRecursion.lean` closes that gap and supplies
the spanning statement:

* `InnerProductSpace.gramSchmidt_eq_sub_sum_gramSchmidtNormed` — the orthonormal-family analogue of
  `gramSchmidt_def''`:
  `gramSchmidt 𝕜 f n = f n - ∑ i < n, ⟪gramSchmidtNormed 𝕜 f i, f n⟫ • gramSchmidtNormed 𝕜 f i`.
* `InnerProductSpace.gramSchmidtNormed_eq_norm_inv_smul_sub_sum` — **eq. (2.17) itself**:
  `gramSchmidtNormed 𝕜 f n = ‖uₙ‖⁻¹ • uₙ` with
  `uₙ = f n - ∑ i < n, ⟪gramSchmidtNormed 𝕜 f i, f n⟫ • gramSchmidtNormed 𝕜 f i`. The empty sum at
  the least index recovers the base case `v₁ = w₁ / ‖w₁‖`, so the one formula covers both clauses.
* `InnerProductSpace.gramSchmidtNormed_span_range` —
  `span 𝕜 (range (gramSchmidtNormed 𝕜 f)) = span 𝕜 (range f)`; and
  `InnerProductSpace.gramSchmidtNormed_span_eq_top` — for a `Basis` `b` the produced vectors span
  the whole space `⊤`, i.e. N&C's "basis for `V`".

Together: `gramSchmidtNormed 𝕜 b` obeys eq. (2.17), is orthonormal, is linearly independent, and
spans `V`, so it is an orthonormal basis — the content of Exercise 2.8.

## N&C ↦ Mathlib dictionary and fidelity

`V` is an inner-product space `E` over `𝕜` (`RCLike 𝕜`, i.e. `ℝ` or `ℂ`; N&C's `ℂ` is the special
case), and Mathlib's sesquilinear convention (conjugate-linear in the first slot, linear in the
second) matches N&C's, so `⟨v_i|w_{k+1}⟩` is `inner 𝕜 (v_i) (w_{k+1})`. Dividing a vector by its
norm is `(‖·‖ : 𝕜)⁻¹ • ·`. The index set is a general well-ordered `ι` (e.g. `Fin d` or `ℕ`); N&C's
finite `1, …, d` is an instance. The statement is a faithful generalisation, not a weakening: the
recursion is proved for *every* input `f` (the degenerate terms vanish), and the orthonormal-basis
conclusion is obtained under N&C's hypothesis that `w` is a basis (hence linearly independent and
spanning).
-/
