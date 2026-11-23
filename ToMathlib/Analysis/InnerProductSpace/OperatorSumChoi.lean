/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumCP
-- `TensorProduct` is re-imported LAST on purpose (mirroring `OperatorSumCP`): it re-asserts the
-- inner-product-space normed structure on `E ⊗[𝕜] F` as the resolution-priority module instance
-- over the bare algebraic one, so operators built with `TensorProduct.map`/`homTensorHomEquiv`
-- unify with the normed module that `rankOne`/`IsPositive` require.
public import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The Choi operator and the recovery identity (reverse direction of Theorem 8.1)

This file builds the **Choi–Jamiołkowski** construction used in the reverse direction of the
operator-sum representation theorem (Nielsen–Chuang Theorem 8.1, *Quantum Computation and Quantum
Information*, §8.2.4, Eqs. (8.54)–(8.59)): given a superoperator `Φ`, form the **Choi operator**
`σ = (id_R ⊗ Φ)(|α⟩⟨α|)` on a maximally entangled reference state `|α⟩`, and recover `Φ` on pure
states by contracting `σ` against the conjugate vector `|ψ̃⟩`.

## Main definitions

* `LinearMap.tmulLeftVec ω` — the **left-factor** vector embedding `g ↦ ω ⊗ g` (the left analogue of
  `LinearMap.tmulRightVec`), used together with the pre-existing left-factor contraction
  `TensorProduct.contractFst ω` (`x ⊗ g ↦ ⟪ω, x⟫ • g`, its adjoint) to sandwich an operator on
  `H ⊗ G` against a fixed reference vector on the `H`-factor.
* `OrthonormalBasis.maxEntVec b` — the (unnormalized) **maximally entangled vector**
  `|α⟩ = Σᵢ |i⟩ ⊗ |i⟩` for the basis `b`.
* `OrthonormalBasis.conjVec b ψ` — the **conjugate vector** `|ψ̃⟩ = Σⱼ conj(ψⱼ) |j⟩`, written as
  `Σⱼ ⟪ψ, b j⟫ • b j` (since `⟪ψ, b j⟫ = conj ⟪b j, ψ⟫ = conj(ψⱼ)`).
* `ContinuousLinearMap.choiOp b Φ` — the **Choi operator** `σ = (id_R ⊗ Φ)(|α⟩⟨α|)` on `H ⊗ G`,
  with `R = H` and `|α⟩ = maxEntVec b`, via the ampliation `superopAmpliationₗ`.

## Main results

* `LinearMap.contractFst_comp_map_comp_tmulLeftVec` — the sandwich identity
  `contractFst ω ∘ (B ⊗ N) ∘ tmulLeftVec ω = ⟪ω, B ω⟫ • N`, the computational core of the recovery.
* `ContinuousLinearMap.choiRecovery` — **the recovery identity** (N&C Eqs. (8.54)–(8.59)):
  contracting `σ` against `|ψ̃⟩` on the reference factor recovers `Φ` on the pure state `|ψ⟩⟨ψ|`,
  `contractFst ψ̃ ∘ σ ∘ tmulLeftVec ψ̃ = Φ(|ψ⟩⟨ψ|)`. The rank-one tensor factorisation it uses,
  `|a ⊗ b⟩⟨c ⊗ d| = |a⟩⟨c| ⊗ |b⟩⟨d|`, is the pre-existing `InnerProductSpace.rankOne_tmul_tmul`.

Positivity of the Choi operator when `Φ` is completely positive is not proved here:
`IsCompletelyPositive` quantifies its reference over `Type 0`, so instantiating it at `R = H`
(arbitrary universe) needs a universe transport. The recovery identity here is fully
universe-polymorphic.

## Design notes

The reference system `R` is taken to be the input space `H` itself (identified with it via the
basis `b`), so `σ` lives on `H ⊗ G` with the reference on the **left** factor — matching the
convention of `superopAmpliationₗ R Φ`, which ampliates on the left (`R ⊗ H → R ⊗ G`). This is why
the contraction uses the left-factor `TensorProduct.contractFst` and the embedding `tmulLeftVec`.

`choiOp` is deliberately the Choi **operator** `σ` (not a curried sandwich `⟨v|σ|w⟩`): the PSD
decomposition of the reverse direction spectrally decomposes `σ` itself, so it must be a named
operator. The recovery identity is then stated as an explicit sandwich composition.
-/

open scoped TensorProduct InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

@[expose] public section

namespace LinearMap

section LeftVec

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The **left-factor vector embedding**: tensoring on the left with a fixed vector `ω : E`,
`y ↦ ω ⊗ y`, as a linear map `F →ₗ E ⊗ F`. The left analogue of `LinearMap.tmulRightVec`; it
packages a fixed reference state `ω` on the left factor. Definitionally `TensorProduct.mk 𝕜 E F ω`;
its adjoint contraction is the pre-existing `TensorProduct.contractFst ω`. -/
noncomputable def tmulLeftVec (ω : E) : F →ₗ[𝕜] E ⊗[𝕜] F :=
  TensorProduct.mk 𝕜 E F ω

@[simp]
theorem tmulLeftVec_apply (ω : E) (y : F) : tmulLeftVec ω y = ω ⊗ₜ[𝕜] y := rfl

/-- **Sandwiching a product operator between two left-factor vectors.** For `B` on `E`, `N` on `F`,
`contractFst ω' ∘ (B ⊗ N) ∘ tmulLeftVec ω = ⟪ω', B ω⟫ • N`: the left factor `B` is applied to `ω`
(the vector the right factor is embedded along by `tmulLeftVec`) and contracted against `ω'` (by the
pre-existing `TensorProduct.contractFst`) to the scalar `⟪ω', B ω⟫`, and the right factor `N`
survives. This is the computational heart of the recovery identity (used with `ω' = ω`). -/
theorem contractFst_comp_map_comp_tmulLeftVec (ω' ω : E) (B : E →ₗ[𝕜] E) (N : F →ₗ[𝕜] F) :
    TensorProduct.contractFst ω' ∘ₗ TensorProduct.map B N ∘ₗ tmulLeftVec ω = ⟪ω', B ω⟫_𝕜 • N := by
  ext y
  simp only [LinearMap.comp_apply, tmulLeftVec_apply, TensorProduct.map_tmul,
    TensorProduct.contractFst_tmul, LinearMap.smul_apply]

end LeftVec

end LinearMap

namespace OrthonormalBasis

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {ι : Type*} [Fintype ι]

/-- The (unnormalized) **maximally entangled vector** `|α⟩ = Σᵢ |i⟩ ⊗ |i⟩` of an orthonormal basis
`b`, an element of `E ⊗ E`. -/
noncomputable def maxEntVec (b : OrthonormalBasis ι 𝕜 E) : E ⊗[𝕜] E :=
  ∑ i, b i ⊗ₜ[𝕜] b i

/-- The **conjugate vector** `|ψ̃⟩ = Σⱼ conj(ψⱼ) |j⟩` of `ψ` relative to the basis `b`, written as
`Σⱼ ⟪ψ, b j⟫ • b j` (using `⟪ψ, b j⟫ = conj ⟪b j, ψ⟫`). It is the vector whose coordinates are the
complex conjugates of those of `ψ`; `conjVec` is conjugate-linear in `ψ`. -/
noncomputable def conjVec (b : OrthonormalBasis ι 𝕜 E) (ψ : E) : E :=
  ∑ j, ⟪ψ, b j⟫_𝕜 • b j

omit [FiniteDimensional 𝕜 E] in
/-- `⟪ψ̃, b i⟫ = ⟪b i, ψ⟫`: the conjugate vector pairs with a basis ket to give the (un-conjugated)
coordinate of `ψ`. -/
theorem inner_conjVec_left (b : OrthonormalBasis ι 𝕜 E) (ψ : E) (i : ι) :
    ⟪b.conjVec ψ, b i⟫_𝕜 = ⟪b i, ψ⟫_𝕜 := by
  classical
  simp only [conjVec, sum_inner, inner_smul_left]
  rw [Finset.sum_eq_single i]
  · rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [inner_conj_symm]
  · intro j _ hj
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [FiniteDimensional 𝕜 E] in
/-- `⟪b i, ψ̃⟩ = ⟪ψ, b i⟫`: the conjugate vector paired on the right with a basis ket. -/
theorem inner_conjVec_right (b : OrthonormalBasis ι 𝕜 E) (ψ : E) (i : ι) :
    ⟪b i, b.conjVec ψ⟫_𝕜 = ⟪ψ, b i⟫_𝕜 := by
  classical
  simp only [conjVec, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single i]
  · rw [orthonormal_iff_ite.mp b.orthonormal]
    simp
  · intro j _ hj
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

end OrthonormalBasis

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]
  {ι : Type*} [Fintype ι]

/-- The **Choi operator** `σ = (id_R ⊗ Φ)(|α⟩⟨α|)` of a superoperator
`Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)`, with reference `R = H` and the maximally entangled input
`|α⟩ = maxEntVec b`. An operator on `H ⊗ G`, built via the ampliation `superopAmpliationₗ`. -/
noncomputable def choiOp (b : OrthonormalBasis ι ℂ H) (Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)) :
    (H ⊗[ℂ] G) →ₗ[ℂ] (H ⊗[ℂ] G) :=
  superopAmpliationₗ H (toLMSuperop Φ)
    ((rankOne ℂ b.maxEntVec b.maxEntVec : (H ⊗[ℂ] H) →L[ℂ] (H ⊗[ℂ] H)) :
      (H ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] H))

omit [CompleteSpace G] in
/-- **The recovery identity** (Nielsen–Chuang Eqs. (8.54)–(8.59)). Contracting the Choi operator
`σ = choiOp b Φ` against the conjugate vector `|ψ̃⟩` on the reference (left) factor recovers `Φ` on
the pure state `|ψ⟩⟨ψ|`:
`contractFst ψ̃ ∘ σ ∘ tmulLeftVec ψ̃ = Φ(|ψ⟩⟨ψ|)`.
The proof expands `|α⟩⟨α| = Σᵢⱼ |i⟩⟨j| ⊗ |i⟩⟨j|` over the basis (`rankOne_tmul_tmul`), pushes it
through the ampliation (`superopAmpliationₗ_map`, giving `Σᵢⱼ |i⟩⟨j| ⊗ Φ(|i⟩⟨j|)`), and contracts
each product summand (`contractFst_comp_map_comp_tmulLeftVec`), producing
`Σᵢⱼ ⟪ψ, b j⟫ ⟪b i, ψ⟫ • Φ(|i⟩⟨j|) = Φ(Σᵢⱼ ⟪b i, ψ⟫ conj⟪b j, ψ⟫ • |i⟩⟨j|) = Φ(|ψ⟩⟨ψ|)`. -/
theorem choiRecovery (b : OrthonormalBasis ι ℂ H) (Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)) (ψ : H) :
    TensorProduct.contractFst (b.conjVec ψ) ∘ₗ choiOp b Φ ∘ₗ LinearMap.tmulLeftVec (b.conjVec ψ)
      = (Φ (rankOne ℂ ψ ψ) : G →ₗ[ℂ] G) := by
  -- Sandwiching the ampliation of a *product* operator `M ⊗ N` (N&C 8.51–8.53 at one term).
  have key : ∀ M N : H →ₗ[ℂ] H,
      TensorProduct.contractFst (b.conjVec ψ) ∘ₗ
          superopAmpliationₗ H (toLMSuperop Φ) (TensorProduct.map M N) ∘ₗ
            LinearMap.tmulLeftVec (b.conjVec ψ)
        = ⟪b.conjVec ψ, M (b.conjVec ψ)⟫_ℂ •
            (↑(Φ (LinearMap.toContinuousLinearMap N)) : G →ₗ[ℂ] G) := by
    intro M N
    rw [superopAmpliationₗ_map, LinearMap.contractFst_comp_map_comp_tmulLeftVec,
      toLMSuperop_apply]
  -- The sandwich distributes over a double sum of ampliated operators (linearity of everything).
  have sand : ∀ X : ι → ι → ((H ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] H)),
      TensorProduct.contractFst (b.conjVec ψ) ∘ₗ
          superopAmpliationₗ H (toLMSuperop Φ) (∑ i, ∑ j, X i j) ∘ₗ
            LinearMap.tmulLeftVec (b.conjVec ψ)
        = ∑ i, ∑ j, TensorProduct.contractFst (b.conjVec ψ) ∘ₗ
            superopAmpliationₗ H (toLMSuperop Φ) (X i j) ∘ₗ
              LinearMap.tmulLeftVec (b.conjVec ψ) := by
    intro X
    ext g
    simp only [LinearMap.comp_apply, map_sum, LinearMap.sum_apply]
  -- Expand `|α⟩⟨α|` over the basis into a double sum of product rank-one operators.
  have hα : ((rankOne ℂ b.maxEntVec b.maxEntVec : (H ⊗[ℂ] H) →L[ℂ] (H ⊗[ℂ] H)) :
        (H ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] H))
      = ∑ i, ∑ j, TensorProduct.map (↑(rankOne ℂ (b i) (b j)) : H →ₗ[ℂ] H)
          (↑(rankOne ℂ (b i) (b j)) : H →ₗ[ℂ] H) := by
    rw [OrthonormalBasis.maxEntVec]
    simp only [map_sum, _root_.sum_apply, rankOne_tmul_tmul,
      ContinuousLinearMap.toLinearMap_sum, TensorProduct.toLinearMap_mapL]
    rw [Finset.sum_comm]
  -- Expand `|ψ⟩⟨ψ|` over the basis with the matching coefficients `⟪ψ̃, |i⟩⟨j| ψ̃⟫`.
  have hψ : rankOne ℂ ψ ψ = ∑ i, ∑ j,
      (⟪b.conjVec ψ, (↑(rankOne ℂ (b i) (b j)) : H →ₗ[ℂ] H) (b.conjVec ψ)⟫_ℂ) •
        rankOne ℂ (b i) (b j) := by
    have e : ψ = ∑ i, ⟪b i, ψ⟫_ℂ • b i := by
      conv_lhs => rw [← b.sum_repr ψ]
      simp only [OrthonormalBasis.repr_apply_apply]
    conv_lhs => rw [e]
    simp only [map_sum, _root_.sum_apply, map_smul, _root_.smul_apply,
      map_smulₛₗ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_right,
      OrthonormalBasis.inner_conjVec_right, OrthonormalBasis.inner_conjVec_left, inner_conj_symm,
      mul_comm]
  rw [choiOp, hα, sand]
  simp only [key, toLinearMap_toContinuousLinearMap]
  rw [hψ]
  simp only [map_sum, map_smul, ContinuousLinearMap.toLinearMap_sum,
      ContinuousLinearMap.toLinearMap_smul]

end ContinuousLinearMap
