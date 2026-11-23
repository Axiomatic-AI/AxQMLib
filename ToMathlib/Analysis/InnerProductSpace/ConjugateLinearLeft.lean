/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Conjugate-linearity of the inner product in the first argument (finite sums)

Mathlib fixes the sesquilinear convention in which the inner product `⟪·, ·⟫` is
*conjugate-linear* in its first argument and linear in its second. The pointwise instances of
this — additivity `sum_inner` and scalar homogeneity `inner_smul_left`
(`⟪r • x, y⟫ = conj r * ⟪x, y⟫`) — are already in the library, but the combined statement for a
finite linear combination `∑ᵢ λᵢ • wᵢ` in the first slot is not available as a single lemma.

This file records that combined form:

* `sum_smul_inner`: `⟪∑ i ∈ s, l i • w i, v⟫ = ∑ i ∈ s, conj (l i) * ⟪w i, v⟫`.

This is Exercise 2.6 of Nielsen & Chuang, *Quantum Computation and Quantum Information* (eq. 2.15),
which asks one to derive conjugate-linearity in the first argument from the inner-product axioms
(linearity in the second argument together with conjugate symmetry). It is the companion in the
first slot of `inner_sum` (`⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫`), and the general-vector
counterpart of `Orthonormal.inner_sum`, which is restricted to an orthonormal family.
-/

@[expose] public section

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The inner product is **conjugate-linear in its first argument**: for a finite linear
combination `∑ i ∈ s, l i • w i`,
`⟪∑ i ∈ s, l i • w i, v⟫ = ∑ i ∈ s, conj (l i) * ⟪w i, v⟫`.

This is Nielsen & Chuang eq. (2.15) (Exercise 2.6), obtained by combining additivity of the inner
product in the first argument over finite sums (`sum_inner`) with scalar conjugate-homogeneity
(`inner_smul_left`). It complements `inner_sum`, the corresponding linearity in the second
argument. -/
theorem sum_smul_inner (s : Finset ι) (l : ι → 𝕜) (w : ι → E) (v : E) :
    inner 𝕜 (∑ i ∈ s, l i • w i) v = ∑ i ∈ s, (starRingEnd 𝕜) (l i) * inner 𝕜 (w i) v := by
  simp only [sum_inner, inner_smul_left]
