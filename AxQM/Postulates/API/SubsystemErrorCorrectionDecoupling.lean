/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SubsystemErrorCorrectionMarginal

/-!
# AxQM.Postulates.API — the decoupling condition as a block condition on the codewords

Infrastructure for **Nielsen & Chuang, Exercise 12.14** (p. 567). For the maximally-mixed code
purification `|RQ⟩ = (1/√N) ∑ₓ eₓ ⊗ wₓ` (`codePurifyVec`, `N = 2ᵏ` codewords), split the coded
system as `Q = Q₁ ⊗ Q₂` and write `σᵢⱼ := Tr_{Q₂} |wᵢ⟩⟨wⱼ|` for the **codeword reduced operators**
on `Q₁` (obtained by tracing out `Q₂`). N&C's *decoupling condition* is `ρ^{RQ1} = ρ^R ⊗ ρ^{Q1}`.

This file shows the decoupling condition is exactly the statement that the family `σ` is
**scalar-diagonal** — off-diagonal blocks vanish and all diagonal blocks are a single common
operator `ρ₁ = ρ^{Q1}`:

`ρ^{RQ1} = ρ^R ⊗ ρ₁   ⟺   ∀ i j, Tr_{Q₂} |wᵢ⟩⟨wⱼ| = if i = j then ρ₁ else 0`

(`codePurify_decoupledLeftFactor_iff`). The forward direction reads the decoupling off the block
form `ρ^{RQ1} = (1/N) ∑ᵢⱼ |eᵢ⟩⟨eⱼ| ⊗ σᵢⱼ` (`codePurifyVec_partialTraceRight_assoc`) together with
`ρ^R = I/N` (`codePurifyVec_partialTraceRight_ref_eq_id`), via the **block-extraction** lemma
`map_rankOne_blockSum_left_inj` (the family `X ↦ ∑ᵢⱼ |eᵢ⟩⟨eⱼ| ⊗ Xᵢⱼ` is injective, for `e` an
orthonormal basis of the reference `R`); the reverse direction reassembles the blocks. The
scalar-diagonal family is also what `ProtectsLeftFactor P` is characterised by in
`AxQM/Postulates/API/SubsystemErrorCorrectionProtection.lean`, so this file supplies one half of
`ProtectsLeftFactor ⟺ decoupling`.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

variable {R A B : Type*}
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [FiniteDimensional ℂ R]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]
  {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℂ R] [FiniteDimensional ℂ A] in
/-- **Block extraction from a reference orthonormal basis.** Contracting the `(k, l)`-block out of a
"block operator" `∑ᵢⱼ |eᵢ⟩⟨eⱼ| ⊗ Xᵢⱼ` on `R ⊗ A` (for an orthonormal basis `e` of the reference `R`)
recovers `Xₖₗ`: applying it to `eₗ ⊗ v` and contracting the reference leg against `eₖ` gives
`Xₖₗ v`. Each product summand is contracted by
`LinearMap.contractFst_comp_map_comp_tmulLeftVec` (`eₗ ⊗ v = tmulLeftVec eₗ v`), reducing the block
to `⟪eₖ, |eᵢ⟩⟨eⱼ|(eₗ)⟫ • Xᵢⱼ v`; orthonormality then selects `i = k`, `j = l`. This is the
injectivity witness behind `map_rankOne_blockSum_left_inj`. -/
theorem contractFst_map_rankOne_blockSum {ι' : Type*} [Fintype ι']
    (e : OrthonormalBasis ι' ℂ R) (X : ι' → ι' → (A →ₗ[ℂ] A)) (k l : ι') (v : A) :
    TensorProduct.contractFst (e k)
        ((∑ i, ∑ j, TensorProduct.map (rankOne ℂ (e i) (e j)).toLinearMap (X i j))
          (e l ⊗ₜ[ℂ] v))
      = X k l v := by
  classical
  -- Contract each product block via the sandwich lemma (`eₗ ⊗ v = tmulLeftVec eₗ v`).
  have hterm : ∀ (B : R →ₗ[ℂ] R) (N : A →ₗ[ℂ] A),
      TensorProduct.contractFst (e k) ((TensorProduct.map B N) (e l ⊗ₜ[ℂ] v))
        = (⟪e k, B (e l)⟫_ℂ) • N v := fun B N => by
    have h := LinearMap.congr_fun
      (LinearMap.contractFst_comp_map_comp_tmulLeftVec (e k) (e l) B N) v
    simpa only [LinearMap.comp_apply, LinearMap.tmulLeftVec_apply, LinearMap.smul_apply] using h
  simp only [LinearMap.sum_apply, map_sum, hterm, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, inner_smul_right]
  -- goal: `∑ i, ∑ j, (⟪e j, e l⟫ * ⟪e k, e i⟫) • (X i j) v = (X k l) v`
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · rw [orthonormal_iff_ite.mp e.orthonormal l l, orthonormal_iff_ite.mp e.orthonormal k k,
        ite_eq_left rfl, ite_eq_left rfl, mul_one, one_smul]
    · intro j _ hjl
      rw [orthonormal_iff_ite.mp e.orthonormal j l, ite_eq_right hjl, zero_mul, zero_smul]
    · intro h; exact absurd (Finset.mem_univ l) h
  · intro i _ hik
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [orthonormal_iff_ite.mp e.orthonormal k i, ite_eq_right (Ne.symm hik), mul_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ k) h

omit [FiniteDimensional ℂ R] [FiniteDimensional ℂ A] in
/-- **Injectivity of the reference-block assembly.** For an orthonormal basis `e` of the reference
`R`, the assignment `X ↦ ∑ᵢⱼ |eᵢ⟩⟨eⱼ| ⊗ Xᵢⱼ` is injective: if two block operators agree, all their
blocks agree. -/
theorem map_rankOne_blockSum_left_inj {ι' : Type*} [Fintype ι']
    (e : OrthonormalBasis ι' ℂ R) {X Y : ι' → ι' → (A →ₗ[ℂ] A)}
    (h : (∑ i, ∑ j, TensorProduct.map (rankOne ℂ (e i) (e j)).toLinearMap (X i j))
        = ∑ i, ∑ j, TensorProduct.map (rankOne ℂ (e i) (e j)).toLinearMap (Y i j))
    (k l : ι') : X k l = Y k l := by
  ext v
  have hX := contractFst_map_rankOne_blockSum e X k l v
  have hY := contractFst_map_rankOne_blockSum e Y k l v
  rw [← hX, ← hY, h]

omit [FiniteDimensional ℂ R] [FiniteDimensional ℂ A] in
/-- **The scalar-diagonal block operator is `I ⊗ τ`.** For an orthonormal basis `e` of the reference
`R`, assembling the diagonal family `Xᵢⱼ = δᵢⱼ τ` into the block operator `∑ᵢⱼ |eᵢ⟩⟨eⱼ| ⊗ Xᵢⱼ`
gives `id_R ⊗ τ` (using `∑ᵢ |eᵢ⟩⟨eᵢ| = 1`). The right-hand side of the decoupling condition, in
block form. -/
theorem blockSum_diag_eq_map_id {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (e : OrthonormalBasis ι' ℂ R) (τ : A →ₗ[ℂ] A) :
    (∑ i, ∑ j, TensorProduct.map (rankOne ℂ (e i) (e j)).toLinearMap (if i = j then τ else 0))
      = TensorProduct.map LinearMap.id τ := by
  have hite : ∀ i : ι', (∑ j, TensorProduct.map (rankOne ℂ (e i) (e j)).toLinearMap
      (if i = j then τ else 0))
      = TensorProduct.map (rankOne ℂ (e i) (e i)).toLinearMap τ := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
    · intro j _ hj; rw [ite_eq_right (Ne.symm hj)]; simp
    · intro h; exact absurd (Finset.mem_univ i) h
  simp_rw [hite]
  rw [← TensorProduct.map_sum_left]
  congr 1
  have := OrthonormalBasis.sum_rankOne_eq_id e
  simpa [ContinuousLinearMap.toLinearMap_sum] using congrArg (ContinuousLinearMap.toLinearMap) this

/-- **N&C Exercise 12.14, decoupling side: the decoupling condition is a block condition on the
codewords.** For the maximally-mixed code purification `|RQ⟩ = ∑ₓ eₓ ⊗ wₓ` on `R ⊗ (Q₁ ⊗ Q₂)`
(`e` an orthonormal basis of the `N = card ι`-dimensional reference `R`, `w` the orthonormal
codewords), the marginals are the normalised reference-and-`Q₁` state
`ρ^{RQ1} = (1/N) Tr_{Q₂} |RQ⟩⟨RQ|` and the maximally-mixed reference state
`ρ^R = (1/N) Tr_Q |RQ⟩⟨RQ|` (`= I/N`). N&C's **decoupling condition** `ρ^{RQ1} = ρ^R ⊗ ρ₁`
(for a candidate `Q₁`-state `ρ₁`)
holds **iff** the codeword reduced operators `σᵢⱼ = Tr_{Q₂} |wᵢ⟩⟨wⱼ|` are **scalar-diagonal** —
`σᵢⱼ = δᵢⱼ ρ₁`: off-diagonal blocks vanish and every diagonal block is the common operator `ρ₁`.

The proof rewrites `ρ^{RQ1}` into the block form `(1/N) ∑ᵢⱼ |eᵢ⟩⟨eⱼ| ⊗ σᵢⱼ`
(`codePurifyVec_partialTraceRight_assoc`) and `ρ^R` into `I/N`
(`codePurifyVec_partialTraceRight_ref_eq_id`), so `ρ^R ⊗ ρ₁ = (1/N) ∑ᵢⱼ |eᵢ⟩⟨eⱼ| ⊗ (δᵢⱼ ρ₁)`
(`blockSum_diag_eq_map_id`); cancelling the common `1/N ≠ 0` and applying block-extraction
(`map_rankOne_blockSum_left_inj`) turns the operator equation into the blockwise condition. This is
the pivot the companion protection development also characterises `ProtectsLeftFactor P` by. -/
theorem codePurify_decoupledLeftFactor_iff [Nonempty ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℂ R) {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (bB : OrthonormalBasis κ ℂ B) (bAB : OrthonormalBasis κ' ℂ (A ⊗[ℂ] B))
    {w : ι → A ⊗[ℂ] B} (hw : Orthonormal ℂ w) (ρ1 : A →ₗ[ℂ] A) :
    (Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bB
          ((TensorProduct.assoc ℂ R A B).symm.conj
            ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap)
        = TensorProduct.map
            ((Fintype.card ι : ℂ)⁻¹ • LinearMap.partialTraceRight bAB
              ((rankOne ℂ (codePurifyVec (⇑e) w)) (codePurifyVec (⇑e) w)).toLinearMap) ρ1
      ↔ ∀ i j, LinearMap.partialTraceRight bB ((rankOne ℂ (w i) (w j)).toLinearMap)
          = if i = j then ρ1 else 0 := by
  have hN : (Fintype.card ι : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [codePurifyVec_partialTraceRight_assoc, codePurifyVec_partialTraceRight_ref_eq_id bAB e hw,
    TensorProduct.map_smul_left, ← blockSum_diag_eq_map_id e ρ1,
    (smul_right_injective _ hN).eq_iff]
  constructor
  · intro h i j
    exact map_rankOne_blockSum_left_inj e h i j
  · intro h
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [h i j]

end AxQM
