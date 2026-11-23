/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Anti-linearity of the adjoint operation

Let `E`, `F` be finite-dimensional inner product spaces over `𝕜` (`ℝ` or `ℂ`). This file records
that the adjoint operation `A ↦ Aᴴ` on operators `E →ₗ[𝕜] F` is *anti-linear* (conjugate-linear):
it is additive and takes a scalar out with complex conjugation.

Mathlib already packages `LinearMap.adjoint` as a conjugate-linear equivalence
(`(E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] F →ₗ[𝕜] E`), so this anti-linearity is present at the level of the bundled
map via the generic `map_add` / `map_smulₛₗ` / `map_sum`. What is missing, and what this file
supplies, are the unbundled equational forms with the conjugation written as `star`.

## Main results

* `LinearMap.adjoint_smul`: `adjoint (c • A) = star c • adjoint A` — conjugate-homogeneity, the
  characteristic feature that distinguishes an anti-linear map from a linear one.
* `LinearMap.adjoint_sum_smul`: `adjoint (∑ i ∈ s, a i • A i) = ∑ i ∈ s, star (a i) • adjoint (A i)`
  — the combined finite-sum form.

The additive part `adjoint (A + B) = adjoint A + adjoint B` is `map_add` for the bundled
equivalence and is not restated here. The analogous statements for the concrete conjugate transpose
of matrices are already in Mathlib as `Matrix.conjTranspose_smul` and `Matrix.conjTranspose_sum`.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Conjugate-homogeneity of the adjoint.** The adjoint of a scalar multiple `c • A` of an
operator between finite-dimensional inner product spaces is the *conjugate* scalar times the
adjoint: `adjoint (c • A) = star c • adjoint A`. This is the defining anti-linear feature of the
adjoint operation (`star c`, not `c`). -/
theorem adjoint_smul (c : 𝕜) (A : E →ₗ[𝕜] F) :
    adjoint (c • A) = star c • adjoint A := by
  rw [map_smulₛₗ, starRingEnd_apply]

/-- **Nielsen & Chuang, Exercise 2.14 (anti-linearity of the adjoint), eq. (2.33).** The adjoint
operation is anti-linear: for a finite family of scalars `a i` and operators `A i` between
finite-dimensional inner product spaces,
`adjoint (∑ i ∈ s, a i • A i) = ∑ i ∈ s, star (a i) • adjoint (A i)`.

The conjugation `star (a i)` on the right (rather than `a i`) is what makes the operation
anti-linear rather than linear. This combines additivity (`map_sum`) with the
conjugate-homogeneity `adjoint_smul`. -/
theorem adjoint_sum_smul {ι : Type*} (s : Finset ι) (a : ι → 𝕜) (A : ι → (E →ₗ[𝕜] F)) :
    adjoint (∑ i ∈ s, a i • A i) = ∑ i ∈ s, star (a i) • adjoint (A i) := by
  simp only [map_sum, adjoint_smul]

end LinearMap
