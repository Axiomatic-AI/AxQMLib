/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.AdjointAntilinear

/-!
# Nielsen & Chuang, Exercise 2.14 (Anti-linearity of the adjoint)

Show the adjoint operation is anti-linear.

**Answer.** The adjoint (Hermitian conjugation) `A ↦ A†` on operators is *anti-linear*
(conjugate-linear): it is additive and pulls a scalar out with complex conjugation. Concretely,
`(∑ᵢ aᵢ Aᵢ)† = ∑ᵢ aᵢ* Aᵢ†`, where `aᵢ*` is the complex conjugate of `aᵢ`. The conjugation on the
scalars is exactly what distinguishes anti-linearity from linearity.

## The declarations

In `ToMathlib/Analysis/InnerProductSpace/AdjointAntilinear.lean`:

* `LinearMap.adjoint_smul` — `adjoint (c • A) = star c • adjoint A`: conjugate-homogeneity, the
  characteristic anti-linear feature (the scalar comes out *conjugated*).
* `LinearMap.adjoint_sum_smul` — the combined finite-sum form, a direct transcription of N&C
  eq. (2.33): `adjoint (∑ i ∈ s, a i • A i) = ∑ i ∈ s, star (a i) • adjoint (A i)`.

## N&C ↦ Mathlib dictionary and fidelity

* The **operators** `Aᵢ` are `LinearMap`s `E →ₗ[𝕜] F` between finite-dimensional inner-product
  spaces over `𝕜` (`RCLike 𝕜`, i.e. `ℝ` or `ℂ`; N&C's `ℂ` is the special case). Sharing the domain
  `E` and codomain `F` across `i` is exactly what lets the sum `∑ᵢ aᵢ Aᵢ` be formed, matching N&C.
* The **adjoint** `A†` is `LinearMap.adjoint`, which Mathlib already bundles as a conjugate-linear
  equivalence `(E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] F →ₗ[𝕜] E`. Anti-linearity is thus present at the bundled level
  via `map_add` / `map_smulₛₗ` / `map_sum`; the lemmas supply the unbundled equational forms
  with the conjugation written as `star` (N&C's `*`).
* The **complex conjugate** `aᵢ*` is `star (a i)` (`= (starRingEnd 𝕜) (a i)`, i.e. `RCLike` complex
  conjugation).

The statement is a faithful transcription of (2.33), not a weakening: it fixes no dimension,
quantifies over an arbitrary finite index set `s : Finset ι` and arbitrary scalars/operators, and
yields the exact conjugated-scalar identity N&C asserts. The additive part
`adjoint (A + B) = adjoint A + adjoint B` is Mathlib's `map_add` for the bundled equivalence, and
the concrete matrix analogue of (2.33) is already Mathlib's `Matrix.conjTranspose_smul` /
`Matrix.conjTranspose_sum`, so neither is re-proved.
-/
