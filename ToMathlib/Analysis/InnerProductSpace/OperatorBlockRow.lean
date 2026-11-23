/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.HSPairing
public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract

/-!
# Block-row operators on a tensor product

Given a finite family of operators `M : ι → (E →L[𝕜] E)` and an orthonormal basis `b` of an
ancilla `F`, the **block-row operator** is the map `E ⊗[𝕜] F →L[𝕜] E`

  `blockRow b M = ∑ j, M j ∘L restrictRightL b j`,   `blockRow b M (x ⊗ b k) = M k x`,

i.e. the operator whose `k`-th "column" (the block `E ⊗ ⟨b k⟩`) acts as `M k`. Here
`restrictRightL b k` is the continuous packaging of `LinearMap.restrictRight b k`
(`x ⊗ y ↦ ⟪b k, y⟫ • x`), automatic in finite dimension.

The two structural identities that make block-rows useful are consequences of the
delta-orthogonality of the columns (`restrictRightL b i ∘L (restrictRightL b j)† = δᵢⱼ`):

* `blockRow_comp_adjoint` — the self-outer-product is the sum of the component outer-products,
  `(blockRow b M)(blockRow b M)† = ∑ j, M j (M j)†` (all cross terms vanish);
* `hsPairing_blockRow` — the Hilbert–Schmidt pairing of two block-rows collapses to the diagonal,
  `(blockRow b N).hsPairing (blockRow b M) = ∑ i, (N i).hsPairing (M i)`.

These package the "stack the `Mⱼ` into orthogonal columns" construction reused, e.g., in the proof
of the strong concavity of the fidelity (Nielsen–Chuang Theorem 9.7), where `M M†` recovers a
probabilistic mixture `∑ⱼ pⱼ ρⱼ` and the pairing recovers a diagonal overlap sum.

## Main definitions

* `ContinuousLinearMap.restrictRightL` — the continuous right-restriction `E ⊗[𝕜] F →L[𝕜] E`.
* `ContinuousLinearMap.blockRow` — the block-row operator assembled from a family and a basis.

## Main results

* `ContinuousLinearMap.restrictRightL_tmul`, `blockRow_apply`, `blockRow_tmul` — the defining
  application formulas.
* `ContinuousLinearMap.adjoint_restrictRightL`, `restrictRightL_comp_adjoint_restrictRightL` — the
  adjoint of a column and the column delta-orthogonality.
* `ContinuousLinearMap.blockRow_comp_adjoint`, `hsPairing_blockRow` — the two structural identities.
-/

open scoped InnerProductSpace TensorProduct

@[expose] public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι]

/-- The **continuous** right-restriction `E ⊗[𝕜] F →L[𝕜] E`, `x ⊗ y ↦ ⟪b k, y⟫ • x`: the
`ContinuousLinearMap` packaging of `LinearMap.restrictRight b k` (automatic in finite dimension). -/
noncomputable def restrictRightL (b : OrthonormalBasis ι 𝕜 F) (k : ι) :
    (E ⊗[𝕜] F) →L[𝕜] E :=
  (LinearMap.restrictRight b k).toContinuousLinearMap

/-- Application of `restrictRightL` on a pure tensor:
`restrictRightL b k (x ⊗ y) = ⟪b k, y⟫ • x`. -/
@[simp]
theorem restrictRightL_tmul (b : OrthonormalBasis ι 𝕜 F) (k : ι) (x : E) (y : F) :
    restrictRightL b k (x ⊗ₜ[𝕜] y) = ⟪b k, y⟫_𝕜 • x := by
  simp only [restrictRightL, LinearMap.coe_toContinuousLinearMap', LinearMap.restrictRight_tmul]

/-- The **block-row operator** assembled from a family `M : ι → (E →L[𝕜] E)` and an orthonormal
basis `b` of the ancilla `F`: `blockRow b M = ∑ j, M j ∘L restrictRightL b j`, the map
`E ⊗[𝕜] F →L[𝕜] E` sending `x ⊗ b k ↦ M k x`. -/
noncomputable def blockRow (b : OrthonormalBasis ι 𝕜 F) (M : ι → E →L[𝕜] E) :
    (E ⊗[𝕜] F) →L[𝕜] E :=
  ∑ j, (M j) ∘L restrictRightL b j

/-- Application of `blockRow` on a general element:
`blockRow b M z = ∑ j, M j (restrictRightL b j z)`. -/
theorem blockRow_apply (b : OrthonormalBasis ι 𝕜 F) (M : ι → E →L[𝕜] E) (z : E ⊗[𝕜] F) :
    blockRow b M z = ∑ j, M j (restrictRightL b j z) := by
  rw [blockRow, _root_.sum_apply]
  simp only [ContinuousLinearMap.comp_apply]

/-- Application of `blockRow` on a pure tensor: `blockRow b M (x ⊗ y) = ∑ j, ⟪b j, y⟫ • M j x`. On a
basis vector `y = b k` this collapses (by orthonormality) to the defining `M k x`. -/
theorem blockRow_tmul (b : OrthonormalBasis ι 𝕜 F) (M : ι → E →L[𝕜] E) (x : E) (y : F) :
    blockRow b M (x ⊗ₜ[𝕜] y) = ∑ j, ⟪b j, y⟫_𝕜 • M j x := by
  rw [blockRow_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [restrictRightL_tmul, map_smul]

section Adjoint

variable [CompleteSpace E] [CompleteSpace (E ⊗[𝕜] F)]

/-- The adjoint of the continuous right-restriction is the continuous right-embedding
`x ↦ x ⊗ b k` (`LinearMap.embedRight b k`), via `LinearMap.adjoint_restrictRight`. -/
theorem adjoint_restrictRightL (b : OrthonormalBasis ι 𝕜 F) (k : ι) :
    adjoint (restrictRightL (E := E) b k) = (LinearMap.embedRight b k).toContinuousLinearMap := by
  rw [restrictRightL, ← LinearMap.adjoint_toContinuousLinearMap, LinearMap.adjoint_restrictRight]

/-- **Delta-orthogonality of the block columns** (continuous form):
`restrictRightL b i ∘L (restrictRightL b j)† = if i = j then 1 else 0`. The two restrictions live
on orthogonal `b`-columns of the ancilla, so the composite is the identity when `i = j` and zero
otherwise (`LinearMap.restrictRight_comp_embedRight`). -/
theorem restrictRightL_comp_adjoint_restrictRightL [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 F) (i j : ι) :
    (restrictRightL (E := E) b i) ∘L adjoint (restrictRightL b j) = if i = j then 1 else 0 := by
  rw [adjoint_restrictRightL, restrictRightL]
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.coe_toContinuousLinearMap,
    LinearMap.coe_toContinuousLinearMap, LinearMap.restrictRight_comp_embedRight]
  split_ifs <;> simp [Module.End.one_eq_id]

/-- **The self-outer-product of a block-row is the sum of the component outer-products:**
`(blockRow b M)(blockRow b M)† = ∑ j, M j (M j)†`. The columns of `blockRow b M` sit on orthogonal
`b`-slots of the ancilla, so all cross terms `i ≠ j` vanish
(`restrictRightL_comp_adjoint_restrictRightL`), leaving the diagonal sum. -/
theorem blockRow_comp_adjoint (b : OrthonormalBasis ι 𝕜 F) (M : ι → E →L[𝕜] E) :
    (blockRow b M) ∘L adjoint (blockRow b M) = ∑ j, (M j) ∘L adjoint (M j) := by
  classical
  have hadj : adjoint (blockRow b M)
      = ∑ j, adjoint (restrictRightL b j) ∘L adjoint (M j) := by
    rw [blockRow, map_sum]
    exact Finset.sum_congr rfl fun j _ => adjoint_comp _ _
  rw [hadj, blockRow, ContinuousLinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Peel the inner sum: only the `j = i` column survives.
  rw [ContinuousLinearMap.comp_finsetSum, Finset.sum_eq_single i]
  · rw [comp_assoc, ← comp_assoc (restrictRightL b i),
      restrictRightL_comp_adjoint_restrictRightL, ite_eq_left rfl, one_def, id_comp]
  · intro j _ hji
    rw [comp_assoc, ← comp_assoc (restrictRightL b i),
      restrictRightL_comp_adjoint_restrictRightL, ite_eq_right (Ne.symm hji), zero_comp, comp_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Scaling each block-row column by `r i` scales the self-outer-product:**
`blockRow b (r · • M ·) (blockRow b (r · • M ·))† = ∑ i, (r i * conj (r i)) • (M i (M i)†)`. The
per-column scalar `r i` factors out of the `i`-th self-outer-product term as `r i * star (r i)`
(`= |r i|²`). Specialised to `r i = √(weight i)` this turns a block-row of scaled columns into a
scaled mixture, the shape used in the strong concavity of the fidelity (N&C Theorem 9.7). -/
theorem blockRow_smul_comp_adjoint (b : OrthonormalBasis ι 𝕜 F) (r : ι → 𝕜)
    (M : ι → E →L[𝕜] E) :
    blockRow b (fun i => r i • M i) ∘L adjoint (blockRow b (fun i => r i • M i))
      = ∑ i, (r i * star (r i)) • (M i ∘L adjoint (M i)) := by
  rw [blockRow_comp_adjoint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← star_eq_adjoint, star_smul, star_eq_adjoint, smul_comp, comp_smul, smul_smul]

/-- **The Hilbert–Schmidt pairing of two block-rows collapses to the diagonal:**
`(blockRow b N).hsPairing (blockRow b M) = ∑ i, (N i).hsPairing (M i)`. Bilinearity expands the
pairing over the two sums; `hsPairing_comp_right` moves each ancilla restriction to the other slot,
where delta-orthogonality (`restrictRightL_comp_adjoint_restrictRightL`) kills the off-diagonal
`i ≠ j` terms. -/
theorem hsPairing_blockRow (b : OrthonormalBasis ι 𝕜 F) (M N : ι → E →L[𝕜] E) :
    (blockRow b N).hsPairing (blockRow b M) = ∑ i, (N i).hsPairing (M i) := by
  classical
  rw [blockRow, blockRow, hsPairing_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsPairing_sum_right, Finset.sum_eq_single j]
  · rw [hsPairing_comp_right, comp_assoc, restrictRightL_comp_adjoint_restrictRightL,
      ite_eq_left rfl, one_def, comp_id]
  · intro i _ hij
    rw [hsPairing_comp_right, comp_assoc, restrictRightL_comp_adjoint_restrictRightL,
      ite_eq_right hij, comp_zero, hsPairing_zero_right]
  · intro h; exact absurd (Finset.mem_univ j) h

end Adjoint

end ContinuousLinearMap
