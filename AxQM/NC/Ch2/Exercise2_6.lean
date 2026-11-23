/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.ConjugateLinearLeft

/-!
# Nielsen & Chuang, Exercise 2.6 (Conjugate-linearity in the first argument)

Show any inner product is conjugate-linear in the first argument.

Here `(·, ·)` is *any* inner product in the sense N&C define on p. 66 (the three requirements:
linearity in the second argument (2.13), conjugate symmetry, and positive definiteness). The
exercise is to derive from those axioms that the inner product is *conjugate-linear* — linear up to
complex conjugation of the scalars — in the **first** argument, for a finite linear combination.

## The declaration

The formalisation is `sum_smul_inner` in
`ToMathlib/Analysis/InnerProductSpace/ConjugateLinearLeft.lean`:

* `sum_smul_inner` — **Exercise 2.6 / eq. (2.15) itself**: for an inner-product space `E` over an
  `RCLike` field `𝕜`, a `Finset` `s`, scalars `l : ι → 𝕜`, vectors `w : ι → E` and a vector
  `v : E`,
  `inner 𝕜 (∑ i ∈ s, l i • w i) v = ∑ i ∈ s, (starRingEnd 𝕜) (l i) * inner 𝕜 (w i) v`.
  This is the faithful reading of N&C's `(∑ᵢ λᵢ |wᵢ⟩, |v⟩) = ∑ᵢ λᵢ* (|wᵢ⟩, |v⟩)` — Mathlib's
  sesquilinear convention (conjugate-linear in the first slot, linear in the second) matches N&C's
  exactly, `starRingEnd 𝕜` is the complex conjugation `λ ↦ λ*`, and the `Finset` sum is the finite
  index sum `∑ᵢ`. N&C's `𝕜 = ℂ` is the special case of the `RCLike` statement, so this is a
  faithful generalisation, not a weakening.

## Proof approach

N&C intend the derivation from the axioms: conjugate symmetry turns the first-argument statement
into the second-argument linearity (2.13). In Mathlib the two pointwise ingredients are already
available as `sum_inner` (additivity of the inner product in the first argument over a finite sum)
and `inner_smul_left` (`inner 𝕜 (r • x) y = (starRingEnd 𝕜) r * inner 𝕜 x y`, the scalar
conjugate-homogeneity), both consequences of that same convention; combining them by `simp` gives
(2.15) directly. The combined finite-sum form was missing from the library — only the additive
`sum_inner`, the pointwise `inner_smul_left`, and the orthonormal-family-restricted
`Orthonormal.inner_sum` were present — so `sum_smul_inner` fills that gap as the first-argument
counterpart of the existing second-argument `inner_sum`.
-/
