/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# Tracing out a composite *left* factor of a tripartite operator

For an operator `T` on `(E ⊗ F) ⊗ G`, tracing out the composite **left** factor `E ⊗ F` equals
re-associating *forward* to `E ⊗ (F ⊗ G)` and tracing out `E` then `F`. These are the left-block
mirror of the `partialTraceRight_tensorProduct_basis` /
`partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv` tower lemmas in
`ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract`, which trace out the composite **right**
factor.

The `G`-marginal of a tripartite state must sometimes be read off from two different groupings of
the three subsystems — directly as `Tr_{E⊗F}`, or iteratively as `Tr_F ∘ Tr_E` after
re-association. These lemmas witness that the two agree; they are the operator-level content behind
the `reducedRight`-analogue of `State.reducedLeft_congr_assoc_symm` (tracing out a composite left
factor of a quantum state).

## Main results

* `LinearMap.partialTraceLeft_tensorProduct_basis` — `Tr_{E⊗F} T = Tr_F (Tr_E (assoc.conj T))`.
* `LinearMap.partialTraceLeft_partialTraceLeft_assocIsometry_conjStarAlgEquiv` — its
  `ContinuousLinearMap` / `conjStarAlgEquiv` reading.
-/

@[expose] public section

open scoped TensorProduct

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  {ιE ιF : Type*} [Fintype ιE] [Fintype ιF]

/-- The forward associator-conjugation `(assoc.conj T)` acts on a pure tensor by re-associating:
`(assoc.conj T) (x ⊗ (y ⊗ z)) = assoc (T ((x ⊗ y) ⊗ z))`. The forward companion of
`LinearMap.conj_assoc_symm_tmul`. -/
theorem conj_assoc_tmul (T : (E ⊗[𝕜] F) ⊗[𝕜] G →ₗ[𝕜] (E ⊗[𝕜] F) ⊗[𝕜] G)
    (x : E) (y : F) (z : G) :
    (TensorProduct.assoc 𝕜 E F G).conj T (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z)) =
      (TensorProduct.assoc 𝕜 E F G) (T ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z)) := by
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul]

/-- `restrictLeft` over the composite factor `E ⊗ F` factors as iterated `restrictLeft`s after
re-association: pairing out the `bE i ⊗ bF j` slot equals pairing out `bE i` then `bF j`. The
left-block companion of `restrictRight_restrictRight_assoc_symm`. -/
private theorem restrictLeft_restrictLeft_assoc (bE : OrthonormalBasis ιE 𝕜 E)
    (bF : OrthonormalBasis ιF 𝕜 F) (i : ιE) (j : ιF) (w : (E ⊗[𝕜] F) ⊗[𝕜] G) :
    restrictLeft bF j (restrictLeft bE i ((TensorProduct.assoc 𝕜 E F G) w)) =
      restrictLeft (bE.tensorProduct bF) (i, j) w := by
  induction w using TensorProduct.inductionOn with
  | tmul u g =>
      induction u using TensorProduct.inductionOn with
      | tmul x y =>
          simp only [TensorProduct.assoc_tmul, restrictLeft_tmul, map_smul,
            OrthonormalBasis.tensorProduct_apply, TensorProduct.inner_tmul, mul_smul]
      | add u₁ u₂ h₁ h₂ => simp [TensorProduct.add_tmul, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp [h₁, h₂]

/-- **Tower (`G`-marginal, left block).** Tracing out the composite factor `E ⊗ F` (over the product
basis `bE.tensorProduct bF`) equals re-associating forward, then tracing out `E`, then `F`:
`Tr_{E⊗F} T = Tr_F (Tr_E (assoc.conj T))`. The left-block mirror of
`partialTraceRight_tensorProduct_basis`. -/
theorem partialTraceLeft_tensorProduct_basis (bE : OrthonormalBasis ιE 𝕜 E)
    (bF : OrthonormalBasis ιF 𝕜 F) (T : (E ⊗[𝕜] F) ⊗[𝕜] G →ₗ[𝕜] (E ⊗[𝕜] F) ⊗[𝕜] G) :
    partialTraceLeft (bE.tensorProduct bF) T =
      partialTraceLeft bF (partialTraceLeft bE ((TensorProduct.assoc 𝕜 E F G).conj T)) := by
  ext z
  rw [partialTraceLeft_apply, Fintype.sum_prod_type, Finset.sum_comm, partialTraceLeft_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [partialTraceLeft_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [OrthonormalBasis.tensorProduct_apply, conj_assoc_tmul]
  exact (restrictLeft_restrictLeft_assoc bE bF i j _).symm

/-- **Tower (`G`-marginal, left block), `conjStarAlgEquiv` form.** The `ContinuousLinearMap`-level
reading of `partialTraceLeft_tensorProduct_basis`: tracing out `E` then `F` from the re-associated
operator `assocIsometry.conjStarAlgEquiv T` recovers the `G`-marginal `Tr_{E⊗F} T`. The left-block
mirror of `partialTraceRight_partialTraceRight_assocIsometry_symm_conjStarAlgEquiv`. -/
theorem partialTraceLeft_partialTraceLeft_assocIsometry_conjStarAlgEquiv
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    (bE : OrthonormalBasis ιE 𝕜 E) (bF : OrthonormalBasis ιF 𝕜 F)
    (T : ((E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜] ((E ⊗[𝕜] F) ⊗[𝕜] G)) :
    partialTraceLeft bF (partialTraceLeft bE
        ((TensorProduct.assocIsometry 𝕜 E F G).conjStarAlgEquiv T).toLinearMap) =
      partialTraceLeft (bE.tensorProduct bF) T.toLinearMap := by
  rw [assocIsometry_conjStarAlgEquiv_toLinearMap, ← partialTraceLeft_tensorProduct_basis]

end LinearMap
