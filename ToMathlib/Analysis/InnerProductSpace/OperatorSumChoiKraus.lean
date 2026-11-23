/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumChoiPositive
public import ToMathlib.Analysis.InnerProductSpace.RankOneSum
-- `TensorProduct` is re-imported LAST on purpose (mirroring `OperatorSumChoiPositive`): it
-- re-asserts the inner-product-space normed structure on `E ⊗[𝕜] F` as the resolution-priority
-- module instance over the bare algebraic one, so operators built with `TensorProduct.map`,
-- `rankOne` and `contractFst` unify with the normed module the positivity / decomposition API uses.
public import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Kraus operators from the Choi decomposition (reverse direction of Theorem 8.1)

This file performs the third and central step of the reverse direction of the operator-sum
representation theorem (Nielsen–Chuang Theorem 8.1, *Quantum Computation and Quantum Information*,
§8.2.4, Eqs. (8.60)–(8.64)). Its two predecessors have established, for a **completely positive**
superoperator `Φ`, the Choi operator `σ = choiOp b Φ` together with

* the **recovery identity** `contractFst ψ̃ ∘ σ ∘ tmulLeftVec ψ̃ = Φ(|ψ⟩⟨ψ|)`
  (`ContinuousLinearMap.choiRecovery`), and
* **positivity** `σ ≥ 0` (`ContinuousLinearMap.choiOp_isPositive`).

Positivity lets us decompose `σ = Σᵢ |sᵢ⟩⟨sᵢ|` into rank-one self-projectors (N&C Eq. (8.60),
`ContinuousLinearMap.IsPositive.exists_sum_rankOne_fin_finrank`). Feeding this decomposition through
the recovery identity reads off a finite family of **operation elements** `Eᵢ : H →L[ℂ] G` with
`Φ(|ψ⟩⟨ψ|) = Σᵢ Eᵢ |ψ⟩⟨ψ| Eᵢ†` on every pure state (N&C Eqs. (8.61)–(8.64)) — the operator-sum
representation of `Φ` on the pure states, which the assembly of the reverse direction then extends
to all operators by convex-linearity.

## Main definitions

* `LinearMap.adjoint_tmulLeftVec` — the adjoint of the left-factor embedding `tmulLeftVec ω`
  (`g ↦ ω ⊗ g`) is the left-factor contraction `contractFst ω` (`x ⊗ y ↦ ⟪ω, x⟫ • y`); mirrors
  `LinearMap.adjoint_tmulRightVec`.
* `ContinuousLinearMap.krausOfChoi b s` — the **operation element read off a Choi vector**
  `s ∈ H ⊗ G` and orthonormal basis `b` of `H`: `Eₛ ψ = ⟨ψ̃|s⟩` (N&C Eq. (8.60)), the contraction of
  `s` against the conjugate vector `ψ̃` on the reference (`H`) factor. Packaged as the manifestly
  `ℂ`-linear sum `∑ⱼ |contractFst (bⱼ) s⟩⟨bⱼ|`.

## Main results

* `ContinuousLinearMap.krausOfChoi_apply` — `krausOfChoi b s ψ = contractFst ψ̃ s`, connecting the
  bundled definition to N&C's `⟨ψ̃|s⟩`.
* `ContinuousLinearMap.contractFst_rankOne_comp_tmulLeftVec` — sandwiching a rank-one projector
  `|s⟩⟨s|` between `contractFst ω` and `tmulLeftVec ω` contracts it to the rank-one projector
  `|contractFst ω s⟩⟨contractFst ω s|` on the surviving factor.
* `ContinuousLinearMap.IsCompletelyPositive.exists_krausSumₗ_apply_rankOne` — **the main result**
  (N&C Eqs. (8.60)–(8.64)): a completely positive `Φ` admits a finite family of operation elements
  `E : Fin (d²) → (H →L[ℂ] G)` (with `d² = finrank ℂ (H ⊗ G)`) such that
  `Φ(|ψ⟩⟨ψ|) = krausSumₗ E (|ψ⟩⟨ψ|)` for every pure state `|ψ⟩` — the operator-sum representation of
  `Φ` on the pure states.
-/

open scoped TensorProduct InnerProductSpace ComplexConjugate
open ContinuousLinearMap InnerProductSpace

noncomputable section

@[expose] public section

namespace LinearMap

section AdjointLeftVec

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Adjoint of the left-factor embedding** is the left-factor contraction:
`(tmulLeftVec ω)† = contractFst ω`. The left analogue of `LinearMap.adjoint_tmulRightVec`; proved
by the inner-product characterization on pure tensors, `⟪ω ⊗ y, a ⊗ b⟫ = ⟪⟪ω, a⟫ • y, b⟫`. -/
theorem adjoint_tmulLeftVec (ω : E) :
    adjoint (tmulLeftVec ω : F →ₗ[𝕜] E ⊗[𝕜] F) = TensorProduct.contractFst ω := by
  rw [eq_comm, LinearMap.eq_adjoint_iff]
  intro v u
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
    simp [tmulLeftVec_apply, TensorProduct.contractFst_tmul, TensorProduct.inner_tmul,
      inner_smul_left]
  | add a b ha hb =>
    simp [inner_add_left, map_add, ha, hb]

end AdjointLeftVec

end LinearMap

namespace TensorProduct

section ContractSumSmul

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {κ : Type*} [Fintype κ]

/-- **Conjugate-linearity of the left-factor contraction in its reference vector.** Contracting `s`
against a linear combination `∑ₖ cₖ • vₖ` on the left factor scales each term by the *conjugate*
`conj cₖ`: `contractFst (∑ₖ cₖ • vₖ) s = ∑ₖ conj cₖ • contractFst (vₖ) s`. (The contraction pairs
the reference with the left factor via `⟪·, ·⟫`, conjugate-linear in the first slot.) -/
theorem contractFst_sum_smul_left (c : κ → 𝕜) (v : κ → E) (s : E ⊗[𝕜] F) :
    contractFst (∑ k, c k • v k) s = ∑ k, conj (c k) • contractFst (v k) s := by
  induction s using TensorProduct.inductionOn with
  | tmul x y =>
      simp only [contractFst_tmul, sum_inner, inner_smul_left, Finset.sum_smul, smul_smul]
  | add a b ha hb => simp [map_add, ha, hb, Finset.sum_add_distrib]

end ContractSumSmul

end TensorProduct

namespace ContinuousLinearMap

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]
  {ι : Type*} [Fintype ι]

/-- **The operation element read off a Choi vector `s`** relative to an orthonormal basis `b` of the
input space `H`. Nielsen–Chuang Eq. (8.60) defines it by `Eₛ|ψ⟩ = ⟨ψ̃|s⟩`, where `ψ̃` is the
conjugate vector of `ψ` and `⟨ψ̃|` contracts the reference (`H`) factor of `s ∈ H ⊗ G`, leaving a
vector of `G`. We package it as `∑ⱼ |contractFst (bⱼ) s⟩⟨bⱼ|`, a finite sum of rank-one operators,
so that it is **manifestly `ℂ`-linear and continuous**; `krausOfChoi_apply` recovers the `⟨ψ̃|s⟩`
action. -/
noncomputable def krausOfChoi (b : OrthonormalBasis ι ℂ H) (s : H ⊗[ℂ] G) : H →L[ℂ] G :=
  ∑ j, rankOne ℂ (TensorProduct.contractFst (b j) s) (b j)

omit [FiniteDimensional ℂ H] [CompleteSpace H] [FiniteDimensional ℂ G] [CompleteSpace G] in
/-- The operation element `krausOfChoi b s` acts by contracting `s` against the conjugate vector
`ψ̃` on the reference factor: `krausOfChoi b s ψ = contractFst ψ̃ s` (Nielsen–Chuang's `⟨ψ̃|s⟩`, Eq.
(8.60)). Both sides expand to `∑ⱼ ⟪bⱼ, ψ⟫ • contractFst (bⱼ) s`, the rank-one sum directly and the
contraction via conjugate-linearity of `contractFst` in its reference
(`contractFst_sum_smul_left`, using `conj ⟪ψ, bⱼ⟫ = ⟪bⱼ, ψ⟫`). -/
theorem krausOfChoi_apply (b : OrthonormalBasis ι ℂ H) (s : H ⊗[ℂ] G) (ψ : H) :
    krausOfChoi b s ψ = TensorProduct.contractFst (b.conjVec ψ) s := by
  rw [krausOfChoi, _root_.sum_apply, OrthonormalBasis.conjVec,
    TensorProduct.contractFst_sum_smul_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rankOne_apply, inner_conj_symm]

omit [CompleteSpace H] [CompleteSpace G] in
/-- **Sandwiching a rank-one projector by a fixed left-factor reference `ω`.** Between the embedding
`tmulLeftVec ω` and the contraction `contractFst ω`, the rank-one projector `|s⟩⟨s|` on `H ⊗ G`
contracts to the rank-one projector `|contractFst ω s⟩⟨contractFst ω s|` on the surviving factor
`G`: `contractFst ω ∘ |s⟩⟨s| ∘ tmulLeftVec ω = |contractFst ω s⟩⟨contractFst ω s|`. The scalar
bookkeeping is the adjoint relation `⟪contractFst ω s, g⟫ = ⟪s, ω ⊗ g⟫` (`adjoint_tmulLeftVec`).
This is the per-term step that turns the Choi decomposition `σ = Σᵢ |sᵢ⟩⟨sᵢ|` into the operator
sum. -/
theorem contractFst_rankOne_comp_tmulLeftVec (ω : H) (s : H ⊗[ℂ] G) :
    TensorProduct.contractFst ω ∘ₗ (↑(rankOne ℂ s s) : (H ⊗[ℂ] G) →ₗ[ℂ] (H ⊗[ℂ] G)) ∘ₗ
        LinearMap.tmulLeftVec ω
      = (↑(rankOne ℂ (TensorProduct.contractFst ω s) (TensorProduct.contractFst ω s))
          : G →ₗ[ℂ] G) := by
  have inner_key : ∀ g : G,
      ⟪TensorProduct.contractFst ω s, g⟫_ℂ = ⟪s, ω ⊗ₜ[ℂ] g⟫_ℂ := by
    intro g
    rw [← LinearMap.adjoint_tmulLeftVec ω, LinearMap.adjoint_inner_left,
      LinearMap.tmulLeftVec_apply]
  ext g
  simp only [LinearMap.comp_apply, LinearMap.tmulLeftVec_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, map_smul]
  rw [inner_key]

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ G] in
/-- **Conjugating a rank-one self-projector by an operator.** For `f : H →L[ℂ] G`,
`f ∘ |ψ⟩⟨ψ| ∘ f† = |f ψ⟩⟨f ψ|` — the single-summand operator-sum action. This is the composition
of `comp_rankOne`, `rankOne_comp` and `adjoint_adjoint`. -/
theorem comp_rankOne_self_comp_adjoint (f : H →L[ℂ] G) (ψ : H) :
    f ∘L rankOne ℂ ψ ψ ∘L adjoint f = rankOne ℂ (f ψ) (f ψ) := by
  simp only [rankOne_comp, comp_rankOne, adjoint_adjoint]

/-- **Operator-sum representation of a completely positive map on the pure states** (Nielsen–Chuang
Theorem 8.1, reverse direction, Eqs. (8.60)–(8.64)). A completely positive superoperator `Φ` admits
a finite family of operation elements `E : Fin (finrank ℂ (H ⊗ G)) → (H →L[ℂ] G)` — at most `d²`
of them, `d = dim H` (for `G = H`) — with `Φ(|ψ⟩⟨ψ|) = krausSumₗ E (|ψ⟩⟨ψ|) = Σᵢ Eᵢ |ψ⟩⟨ψ| Eᵢ†`
on every pure state `|ψ⟩`.

The elements are read off the Choi operator `σ = choiOp b Φ`: `σ` is positive
(`choiOp_isPositive`), hence decomposes as `σ = Σᵢ |uᵢ⟩⟨uᵢ|`
(`IsPositive.exists_sum_rankOne_fin_finrank`), and `Eᵢ` is the Choi vector `uᵢ` read off by
`krausOfChoi b uᵢ`. Feeding the decomposition through the recovery identity (`choiRecovery`) and
contracting each rank-one term (`contractFst_rankOne_comp_tmulLeftVec`) matches, summand by summand,
the operator sum `krausSumₗ E (|ψ⟩⟨ψ|)` (`comp_rankOne_self_comp_adjoint`). The extension to all
operators by convex-linearity, and the trace condition `Σᵢ Eᵢ† Eᵢ ≤ 1`, are not proved here. -/
theorem IsCompletelyPositive.exists_krausSumₗ_apply_rankOne (b : OrthonormalBasis ι ℂ H)
    {Φ : (H →L[ℂ] H) →ₗ[ℂ] (G →L[ℂ] G)} (hΦ : IsCompletelyPositive Φ) :
    ∃ E : Fin (Module.finrank ℂ (H ⊗[ℂ] G)) → (H →L[ℂ] G),
      ∀ ψ : H, Φ (rankOne ℂ ψ ψ) = krausSumₗ E (rankOne ℂ ψ ψ) := by
  -- The Choi operator `σ = choiOp b Φ` is positive; bridge to a CLM and decompose it.
  have hpos : (choiOp b Φ).IsPositive := choiOp_isPositive b hΦ
  have hposC : (LinearMap.toContinuousLinearMap (choiOp b Φ)).IsPositive := by
    rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, LinearMap.coe_toContinuousLinearMap]
    exact hpos
  obtain ⟨u, hu⟩ := hposC.exists_sum_rankOne_fin_finrank
  -- `σ = Σᵢ |uᵢ⟩⟨uᵢ|` as a linear map (N&C Eq. (8.60)).
  have hσ : (choiOp b Φ)
      = ∑ i, (↑(rankOne ℂ (u i) (u i)) : (H ⊗[ℂ] G) →ₗ[ℂ] (H ⊗[ℂ] G)) := by
    rw [← LinearMap.coe_toContinuousLinearMap (choiOp b Φ), hu, ContinuousLinearMap.toLinearMap_sum]
  refine ⟨fun i => krausOfChoi b (u i), fun ψ => ?_⟩
  apply ContinuousLinearMap.coe_injective
  -- The operator sum, summand by summand: `Eᵢ |ψ⟩⟨ψ| Eᵢ† = |Eᵢ ψ⟩⟨Eᵢ ψ|`.
  have rhs_eq :
      (↑(krausSumₗ (fun i => krausOfChoi b (u i)) (rankOne ℂ ψ ψ)) : G →ₗ[ℂ] G)
      = ∑ i, (↑(rankOne ℂ (krausOfChoi b (u i) ψ) (krausOfChoi b (u i) ψ))
          : G →ₗ[ℂ] G) := by
    rw [krausSumₗ_apply, ContinuousLinearMap.toLinearMap_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [comp_rankOne_self_comp_adjoint]
  -- The recovery side: distribute the Choi decomposition through `contractFst · ∘ tmulLeftVec ·`.
  have lhs_eq : (Φ (rankOne ℂ ψ ψ) : G →ₗ[ℂ] G)
      = ∑ i, (↑(rankOne ℂ (krausOfChoi b (u i) ψ) (krausOfChoi b (u i) ψ))
          : G →ₗ[ℂ] G) := by
    have dist : TensorProduct.contractFst (b.conjVec ψ) ∘ₗ choiOp b Φ ∘ₗ
          LinearMap.tmulLeftVec (b.conjVec ψ)
        = ∑ i, (TensorProduct.contractFst (b.conjVec ψ) ∘ₗ
            (↑(rankOne ℂ (u i) (u i)) : (H ⊗[ℂ] G) →ₗ[ℂ] (H ⊗[ℂ] G)) ∘ₗ
            LinearMap.tmulLeftVec (b.conjVec ψ)) := by
      rw [hσ]
      ext g
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    rw [← choiRecovery b Φ ψ, dist]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [contractFst_rankOne_comp_tmulLeftVec, krausOfChoi_apply]
  exact lhs_eq.trans rhs_eq.symm

end ContinuousLinearMap
