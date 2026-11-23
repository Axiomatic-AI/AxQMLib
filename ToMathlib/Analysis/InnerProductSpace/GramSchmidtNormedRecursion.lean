/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! # The normalize-at-each-step recursion for the Gram–Schmidt process

Mathlib's `InnerProductSpace.gramSchmidtNormed` produces the orthonormal system by first running
the *unnormalized* orthogonalisation `gramSchmidt` — whose recursion `gramSchmidt_def''` subtracts
the projections onto the previous *unnormalized* vectors `gramSchmidt 𝕜 f i` — and only normalising
at the very end.

Textbooks usually present Gram–Schmidt in the equivalent *normalize-at-each-step* form, in which
each new vector is produced by subtracting the projections onto the previously produced
*orthonormal* vectors and then normalising. This file records that this is exactly what
`gramSchmidtNormed` computes:

* `gramSchmidt_eq_sub_sum_gramSchmidtNormed`: subtracting from `f n` its projection onto the earlier
  *normalized* vectors `gramSchmidtNormed 𝕜 f i` (`i < n`) recovers the unnormalized
  `gramSchmidt 𝕜 f n`. This is the orthonormal-family analogue of `gramSchmidt_def''`.
* `gramSchmidtNormed_eq_norm_inv_smul_sub_sum`: consequently `gramSchmidtNormed 𝕜 f` obeys the
  self-referential recursion
  `gramSchmidtNormed 𝕜 f n = ‖uₙ‖⁻¹ • uₙ` with
  `uₙ = f n - ∑ i < n, ⟪gramSchmidtNormed 𝕜 f i, f n⟫ • gramSchmidtNormed 𝕜 f i`.
* `gramSchmidtNormed_span_range`: the normalized vectors span the same space as the input family;
  `gramSchmidtNormed_span_eq_top`: applied to a basis they span the whole space.

This is Exercise 2.8 of Nielsen & Chuang, *Quantum Computation and Quantum Information* (eq. 2.17),
which asks one to prove that this normalize-at-each-step procedure produces an orthonormal basis
for `V`. Combined with the existing Mathlib results `gramSchmidtNormed_orthonormal`
(orthonormality) and `gramSchmidtNormed_linearIndependent` (linear independence) — both for a
linearly independent input — the lemmas here supply the remaining ingredient (that
`gramSchmidtNormed` *is* the procedure of eq. 2.17, and that it spans `V`), so the produced family
is an orthonormal basis.
-/

@[expose] public section

open Finset Submodule

namespace InnerProductSpace

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Subtracting from `f n` its orthogonal projection onto the earlier **normalized** Gram–Schmidt
vectors `gramSchmidtNormed 𝕜 f i` (`i < n`) recovers the unnormalized vector `gramSchmidt 𝕜 f n`:
`gramSchmidt 𝕜 f n = f n - ∑ i < n, ⟪gramSchmidtNormed 𝕜 f i, f n⟫ • gramSchmidtNormed 𝕜 f i`.

This is the orthonormal-family analogue of `gramSchmidt_def''` (which uses the unnormalized vectors
and their squared norms): because each `gramSchmidtNormed 𝕜 f i` is `‖gramSchmidt 𝕜 f i‖⁻¹` times
`gramSchmidt 𝕜 f i`, the two projection sums coincide term by term (also when a vector is `0`). -/
theorem gramSchmidt_eq_sub_sum_gramSchmidtNormed (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n =
      f n - ∑ i ∈ Iio n, ⟪gramSchmidtNormed 𝕜 f i, f n⟫ • gramSchmidtNormed 𝕜 f i := by
  rw [eq_sub_iff_add_eq]
  rw [show (∑ i ∈ Iio n, ⟪gramSchmidtNormed 𝕜 f i, f n⟫ • gramSchmidtNormed 𝕜 f i)
        = ∑ i ∈ Iio n,
          (⟪gramSchmidt 𝕜 f i, f n⟫ / ↑‖gramSchmidt 𝕜 f i‖ ^ 2) • gramSchmidt 𝕜 f i from ?_]
  · exact (gramSchmidt_def'' 𝕜 f n).symm
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [gramSchmidtNormed, inner_smul_left, smul_smul]
    congr 1
    rw [map_inv₀, RCLike.conj_ofReal]
    ring

/-- **Gram–Schmidt recursion** (Nielsen & Chuang eq. 2.17). The normalized Gram–Schmidt family
`gramSchmidtNormed 𝕜 f` is obtained, at each index `n`, by subtracting from `f n` its projection
onto the previously produced orthonormal vectors and then normalising:
`gramSchmidtNormed 𝕜 f n = ‖uₙ‖⁻¹ • uₙ`, where
`uₙ = f n - ∑ i < n, ⟪gramSchmidtNormed 𝕜 f i, f n⟫ • gramSchmidtNormed 𝕜 f i`.

For the least index the sum is empty, giving `‖f n‖⁻¹ • f n`, so this single formula also covers the
base case `v₁ = w₁ / ‖w₁‖`. -/
theorem gramSchmidtNormed_eq_norm_inv_smul_sub_sum (f : ι → E) (n : ι) :
    gramSchmidtNormed 𝕜 f n =
      (‖f n - ∑ i ∈ Iio n, ⟪gramSchmidtNormed 𝕜 f i, f n⟫ • gramSchmidtNormed 𝕜 f i‖ : 𝕜)⁻¹ •
        (f n - ∑ i ∈ Iio n, ⟪gramSchmidtNormed 𝕜 f i, f n⟫ • gramSchmidtNormed 𝕜 f i) := by
  rw [← gramSchmidt_eq_sub_sum_gramSchmidtNormed, gramSchmidtNormed]

/-- The normalized Gram–Schmidt vectors span the same submodule as the input family: the procedure
does not change the span, so it produces a spanning set whenever the input does. -/
theorem gramSchmidtNormed_span_range (f : ι → E) :
    span 𝕜 (Set.range (gramSchmidtNormed 𝕜 f)) = span 𝕜 (Set.range f) :=
  (span_gramSchmidtNormed_range f).trans (span_gramSchmidt 𝕜 f)

/-- Applied to a basis `b`, the normalized Gram–Schmidt vectors span the whole space. Together with
`gramSchmidtNormed_orthonormal` this says the Gram–Schmidt procedure turns a basis into an
orthonormal basis (Nielsen & Chuang Exercise 2.8). -/
theorem gramSchmidtNormed_span_eq_top (b : Module.Basis ι 𝕜 E) :
    span 𝕜 (Set.range (gramSchmidtNormed 𝕜 (⇑b))) = ⊤ := by
  rw [gramSchmidtNormed_span_range]
  exact b.span_eq

end InnerProductSpace
