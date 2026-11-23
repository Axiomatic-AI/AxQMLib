/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# The partial trace over the left factor is the partial trace over the right factor after a swap

The two partial traces `LinearMap.partialTraceLeft` (over the left factor) and
`LinearMap.partialTraceRight` (over the right factor) are the two faces of one operation, related by
the factor-swap `TensorProduct.comm`. This file records that bridge:

`Tr_E T = Tr_E (comm ∘ T ∘ comm)`  — tracing out the left factor `E` of `E ⊗ F` equals swapping the
factors and tracing out the (now right) factor `E` of `F ⊗ E`.

The point is economy: the naturality API for `partialTraceRight` (invariance under a unitary on the
traced factor, associator commutation, …) then transfers to `partialTraceLeft` for free by
conjugating with `comm`, instead of re-proving each fact from scratch on the left. The reduced-state
generator `State.reducedRight` (which is a `partialTraceLeft`) inherits this in
`AxQM/Postulates/API/ReducedStateComm.lean`.

## Main results

* `LinearMap.restrictRight_comm` / `LinearMap.restrictLeft_comm` — the slot-restriction maps swap:
  `restrictRight b k (comm w) = restrictLeft b k w` and its mirror.
* `LinearMap.partialTraceLeft_eq_partialTraceRight_comm` /
  `LinearMap.partialTraceRight_eq_partialTraceLeft_comm` — the partial-trace bridge, in both
  directions.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {ι₁ : Type*} [Fintype ι₁]

/-- **The slot-restriction maps swap under `comm`.** Restricting the right factor at `b k` after
swapping factors is restricting the left factor at `b k`: for `w : E ⊗ F` and an orthonormal basis
`b` of `E`,

  `restrictRight b k (comm w) = restrictLeft b k w`.

On a simple tensor `x ⊗ₜ y` both sides are `⟪b k, x⟫ • y` (the swap sends `x ⊗ₜ y ↦ y ⊗ₜ x`, whose
right factor is the original left factor `x`); extended linearly. -/
theorem restrictRight_comm (b : OrthonormalBasis ι₁ 𝕜 E) (k : ι₁) (w : E ⊗[𝕜] F) :
    restrictRight b k ((TensorProduct.comm 𝕜 E F) w) = restrictLeft b k w := by
  induction w using TensorProduct.inductionOn with
  | tmul x y => rw [TensorProduct.comm_tmul, restrictRight_tmul, restrictLeft_tmul]
  | add a c ha hc => simp only [map_add, ha, hc]

/-- **Left partial trace = right partial trace after a swap.** For `T : E ⊗ F →ₗ E ⊗ F` and an
orthonormal basis `b` of the traced factor `E`,

  `Tr_E T = Tr_E (comm ∘ T ∘ comm)`,

i.e. tracing out the left factor of `E ⊗ F` equals conjugating by the factor-swap
`comm : E ⊗ F ≃ F ⊗ E` and tracing out the (now right) factor `E` of `F ⊗ E`. This is the bridge
that transfers the `partialTraceRight` naturality API to `partialTraceLeft`. Proved termwise from
the `partialTrace{Left,Right}_apply` sum formulas via `restrictRight_comm`. -/
theorem partialTraceLeft_eq_partialTraceRight_comm (b : OrthonormalBasis ι₁ 𝕜 E)
    (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceLeft b T =
      partialTraceRight b ((TensorProduct.comm 𝕜 E F).toLinearMap ∘ₗ T ∘ₗ
        (TensorProduct.comm 𝕜 F E).toLinearMap) := by
  ext y
  rw [partialTraceLeft_apply, partialTraceRight_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, TensorProduct.comm_tmul,
    restrictRight_comm]

/-- **The slot-restriction maps swap under `comm`** (mirror of `restrictRight_comm`). For a vector
`w : E ⊗ F` and an orthonormal basis `b` of `F`,

  `restrictLeft b k (comm w) = restrictRight b k w`.

On a simple tensor `x ⊗ₜ y` both sides are `⟪b k, y⟫ • x`. -/
theorem restrictLeft_comm {ι₂ : Type*} [Fintype ι₂] (b : OrthonormalBasis ι₂ 𝕜 F) (k : ι₂)
    (w : E ⊗[𝕜] F) :
    restrictLeft b k ((TensorProduct.comm 𝕜 E F) w) = restrictRight b k w := by
  induction w using TensorProduct.inductionOn with
  | tmul x y => rw [TensorProduct.comm_tmul, restrictLeft_tmul, restrictRight_tmul]
  | add a c ha hc => simp only [map_add, ha, hc]

/-- **Right partial trace = left partial trace after a swap** (mirror of
`partialTraceLeft_eq_partialTraceRight_comm`). For `T : E ⊗ F →ₗ E ⊗ F` and an orthonormal basis `b`
of the traced factor `F`,

  `Tr_F T = Tr_F (comm ∘ T ∘ comm)`,

tracing out the right factor of `E ⊗ F` equals swapping and tracing out the (now left) factor `F` of
`F ⊗ E`. Transfers the `partialTraceLeft` naturality API to `partialTraceRight`. -/
theorem partialTraceRight_eq_partialTraceLeft_comm {ι₂ : Type*} [Fintype ι₂]
    (b : OrthonormalBasis ι₂ 𝕜 F) (T : E ⊗[𝕜] F →ₗ[𝕜] E ⊗[𝕜] F) :
    partialTraceRight b T =
      partialTraceLeft b ((TensorProduct.comm 𝕜 E F).toLinearMap ∘ₗ T ∘ₗ
        (TensorProduct.comm 𝕜 F E).toLinearMap) := by
  ext x
  rw [partialTraceRight_apply, partialTraceLeft_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, TensorProduct.comm_tmul,
    restrictLeft_comm]

end LinearMap
