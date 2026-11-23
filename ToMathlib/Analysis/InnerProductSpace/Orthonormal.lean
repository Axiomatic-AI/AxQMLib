/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Orthonormal sets: the Pythagorean theorem

Extends `Mathlib.Analysis.InnerProductSpace.Orthonormal` with the smul form of the Pythagorean
theorem for a finite linear combination over an orthonormal family.
-/

@[expose] public section

noncomputable section

open RCLike ComplexConjugate

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Pythagorean theorem (orthonormal-smul form)**: the squared norm of a finite linear
combination over an orthonormal family equals the sum of squared coefficient norms.

The same fact is also available as a specialization of `OrthogonalFamily.norm_sum`
applied to `Orthonormal.orthogonalFamily` (in `InnerProductSpace.Subspace`), but via the
`LinearIsometry.toSpanSingleton` coercion which obscures the natural smul pattern. This
file-local proof goes directly through `Orthonormal.inner_sum`. -/
protected theorem Orthonormal.norm_sum_smul_sq {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜)
    (s : Finset ι) : ‖∑ i ∈ s, l i • v i‖ ^ 2 = ∑ i ∈ s, ‖l i‖ ^ 2 := by
  rw [← @inner_self_eq_norm_sq 𝕜, hv.inner_sum l l, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.conj_mul]
  norm_cast
