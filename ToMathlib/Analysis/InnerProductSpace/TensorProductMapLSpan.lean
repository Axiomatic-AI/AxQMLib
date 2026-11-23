/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Product operators span the operator algebra of a tensor product

For finite-dimensional inner product spaces `E`, `F` over an `RCLike` field, the product operators
`TensorProduct.mapL A B = A ⊗ B` (`A : E →L E`, `B : F →L F`) span the whole operator space
`E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F`.  Equivalently, an operator identity that is `𝕜`-*bilinear* in a pair of
tensor-factor operators is determined by its values on product operators.

## Main results

* `OrthonormalBasis.sum_rankOne_apply_eq` — rank-one expansion of an arbitrary operator,
  `U = ∑ᵢ |U bᵢ⟩⟨bᵢ|`; the operator generalization of `OrthonormalBasis.sum_rankOne_eq_id`.
* `TensorProduct.rankOne_mem_span_range_mapL` — every rank-one operator `|x⟩⟨y|` on `E ⊗ F` lies in
  the span of the product operators.
* `TensorProduct.span_range_mapL_eq_top` — the product operators span the operator space.

Because product operators span the operator space, an operator identity that is `𝕜`-bilinear in a
pair of tensor-factor operators is determined by its values on product operators — the
`span_range_mapL_eq_top` fact a bilinear-lift argument consumes (e.g. the Nielsen & Chuang Exercise
12.22 driving-unitary linchpin `TensorProduct.noComm_driving_raw_eq`, which reduces to the product
case by a `span_range_mapL_eq_top` induction on each driving operator).

## Implementation notes

The span is obtained from two ingredients.  First, every operator `U` is a finite sum of rank-one
operators, `U = ∑ᵢ |U bᵢ⟩⟨bᵢ|` over an orthonormal basis `b` (via
`OrthonormalBasis.sum_rankOne_eq_id` and `InnerProductSpace.comp_rankOne`).  Second, since pure
tensors span `E ⊗ F` and `|·⟩⟨·|` is additive in each slot, every rank-one operator reduces to
rank-ones of pure tensors, which are product operators by `InnerProductSpace.rankOne_tmul_tmul`.
-/

@[expose] public section

open scoped TensorProduct
open InnerProductSpace

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Every rank-one operator `|x⟩⟨y|` on `E ⊗[𝕜] F` lies in the span of the product operators
`TensorProduct.mapL A B`.  Both slots of `|·⟩⟨·|` are additive and pure tensors span `E ⊗ F`, so the
statement reduces to `|a ⊗ c⟩⟨b ⊗ d| = |a⟩⟨b| ⊗ |c⟩⟨d|` (`InnerProductSpace.rankOne_tmul_tmul`), a
product operator. -/
theorem rankOne_mem_span_range_mapL (x y : E ⊗[𝕜] F) :
    ((InnerProductSpace.rankOne 𝕜) x) y ∈
      Submodule.span 𝕜 (Set.range fun p : (E →L[𝕜] E) × (F →L[𝕜] F) =>
        TensorProduct.mapL p.1 p.2) := by
  induction x using TensorProduct.inductionOn with
  | add x1 x2 ih1 ih2 =>
      rw [map_add, add_apply]
      exact Submodule.add_mem _ ih1 ih2
  | tmul a c =>
      induction y using TensorProduct.inductionOn with
      | add y1 y2 ih1 ih2 =>
          rw [map_add]
          exact Submodule.add_mem _ ih1 ih2
      | tmul b d =>
          rw [InnerProductSpace.rankOne_tmul_tmul]
          exact Submodule.subset_span ⟨(_, _), rfl⟩

omit [FiniteDimensional 𝕜 E] in
/-- **Rank-one expansion of an operator.**  Every operator `U : E →L[𝕜] E` on an inner product space
with a finite orthonormal basis `b` is the sum of the rank-one operators `|U bᵢ⟩⟨bᵢ|` over `b`.
The operator generalization of `OrthonormalBasis.sum_rankOne_eq_id` (the `U = id` case): expand the
identity as `∑ᵢ |bᵢ⟩⟨bᵢ|` and precompose with `U` (`InnerProductSpace.comp_rankOne`). -/
theorem _root_.OrthonormalBasis.sum_rankOne_apply_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] E) :
    U = ∑ i, ((InnerProductSpace.rankOne 𝕜) (U (b i))) (b i) := by
  have hid := OrthonormalBasis.sum_rankOne_eq_id b
  calc U = U.comp (ContinuousLinearMap.id 𝕜 E) := by rw [ContinuousLinearMap.comp_id]
    _ = U.comp (∑ i, ((InnerProductSpace.rankOne 𝕜) (b i)) (b i)) := by rw [hid]
    _ = ∑ i, U.comp (((InnerProductSpace.rankOne 𝕜) (b i)) (b i)) := by
          rw [← ContinuousLinearMap.mul_def, Finset.mul_sum]; rfl
    _ = ∑ i, ((InnerProductSpace.rankOne 𝕜) (U (b i))) (b i) := by
          simp [InnerProductSpace.comp_rankOne]

/-- The product operators `TensorProduct.mapL A B = A ⊗ B` span the operator space
`E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F`.  Every operator `U` expands over an orthonormal basis `b` of `E ⊗ F` as
`U = ∑ᵢ |U bᵢ⟩⟨bᵢ|` (`OrthonormalBasis.sum_rankOne_apply_eq`), a sum of rank-one operators, each of
which lies in the span (`TensorProduct.rankOne_mem_span_range_mapL`). -/
theorem span_range_mapL_eq_top :
    Submodule.span 𝕜
      (Set.range fun p : (E →L[𝕜] E) × (F →L[𝕜] F) => TensorProduct.mapL p.1 p.2) = ⊤ := by
  rw [eq_top_iff]
  intro U _
  rw [OrthonormalBasis.sum_rankOne_apply_eq (stdOrthonormalBasis 𝕜 (E ⊗[𝕜] F)) U]
  exact Submodule.sum_mem _ fun i _ => rankOne_mem_span_range_mapL _ _

end TensorProduct
