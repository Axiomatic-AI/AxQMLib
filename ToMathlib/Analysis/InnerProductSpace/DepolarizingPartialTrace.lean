/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.DepolarizingTwirl
public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
public import Mathlib.LinearAlgebra.Contraction

/-!
# The depolarizing twirl on the traced factor is `partialTrace ⊗ I/d`

Fix finite-dimensional complex inner product spaces `E`, `F`, an orthonormal basis
`b = {bᵢ}` of `F` of dimension `d = |ι|`, and the depolarizing `1`-design unitaries
`Uⱼ = Pσ Sε` on `F` (`OrthonormalBasis.depolarizingUnitary`). Twirling an operator
`T : E ⊗ F →L[ℂ] E ⊗ F` by the unitaries `I_E ⊗ Uⱼ` — i.e. leaving the `E` factor alone and
running the completely depolarizing channel on the `F` factor — collapses `T` to its `E`-marginal
tensored with the maximally mixed state on `F`:

`(2^d d!)⁻¹ • ∑_{ε, σ} (I ⊗ Uⱼ) T (I ⊗ Uⱼ)† = (Tr_F T) ⊗ (I_F / d)`.

This is the bipartite form of the finite unitary `1`-design of Nielsen & Chuang, *Quantum
Computation and Quantum Information*, Exercise 11.19
(`OrthonormalBasis.sum_conjStarAlgEquiv_depolarizingUnitary`): the completely depolarizing
partial-trace channel `T ↦ (Tr_F T) ⊗ I/d` is a **uniform mixed-unitary average**. Feeding this
into the mixed-unitary monotonicity of the quantum relative entropy
(`ContinuousLinearMap.quantumRelativeEntropy_sum_conjStarAlgEquiv_le`) yields the monotonicity of
the relative entropy under partial trace — the bridge to the strong subadditivity of the von
Neumann entropy (N&C Theorem 11.14).

## Main results

* `OrthonormalBasis.sum_depolarizingUnitary_conj_toLinearMap` — the `LinearMap`-level restatement
  of the single-space depolarizing twirl (Ex 11.19), used in the reduction to product operators.
* `OrthonormalBasis.sum_conjStarAlgEquiv_congrIsometry_depolarizingUnitary` — the headline
  bipartite twirl identity `∑ⱼ pⱼ (I ⊗ Uⱼ) T (I ⊗ Uⱼ)† = (Tr_F T) ⊗ (I_F/d)`.
-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap
open scoped TensorProduct

namespace OrthonormalBasis

-- `[CompleteSpace F]` is mathematically implied by `[FiniteDimensional ℂ F]`, but it is kept
-- explicit deliberately: dropping it forces the `CompleteSpace F` / `CompleteSpace (E ⊗ F)`
-- instances (needed by `conjStarAlgEquiv` / `depolarizingUnitary`) to be re-synthesized
-- non-canonically inside the `homTensorHomEquiv` induction of
-- `sum_conjStarAlgEquiv_congrIsometry_depolarizingUnitary`, which desyncs the `conjStarAlgEquiv`
-- terms (the `hterm` rewrite stops firing) and blows the heartbeat budget (`isDefEq` timeout).
-- The explicit binder pins one canonical instance and keeps the proof fast.
variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- **`LinearMap` form of the single-space depolarizing twirl** (Nielsen & Chuang, Exercise 11.19).
Averaging the conjugations `Uⱼ B Uⱼ⁻¹` of a linear operator `B : F →ₗ[ℂ] F` by the `1`-design
unitaries `Uⱼ = Pσ Sε` gives `(Tr B / d) • id`, where `d = |ι|`. This is
`sum_conjStarAlgEquiv_depolarizingUnitary` transported from continuous linear maps to plain linear
maps, so it can be used inside a reduction to product operators `TensorProduct.map A B`. -/
theorem sum_depolarizingUnitary_conj_toLinearMap [Nonempty ι] (b : OrthonormalBasis ι ℂ F)
    (B : F →ₗ[ℂ] F) :
    ∑ p : (ι → Bool) × Equiv.Perm ι,
        (((2 : ℂ) ^ Fintype.card ι * (Fintype.card ι).factorial)⁻¹) •
          ((b.depolarizingUnitary p).toLinearMap ∘ₗ B ∘ₗ (b.depolarizingUnitary p).symm.toLinearMap)
      = (LinearMap.trace ℂ F B / (Fintype.card ι : ℂ)) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun
    (b.sum_conjStarAlgEquiv_depolarizingUnitary (LinearMap.toContinuousLinearMap B)) x
  simp only [_root_.sum_apply, _root_.smul_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_toContinuousLinearMap, one_apply_eq_self] at h
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.id_apply, LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv]
    using h

/-- **The bipartite depolarizing twirl equals `partialTrace ⊗ I/d`** (Nielsen & Chuang, Exercise
11.19, bipartite form). For an operator `T : E ⊗ F →L[ℂ] E ⊗ F` and an orthonormal basis `b` of `F`
of dimension `d = |ι|`, the uniform average of the conjugations by the depolarizing unitaries
`I_E ⊗ Uⱼ` (twirling only the `F` factor) equals the `E`-marginal of `T` tensored with the
maximally mixed state `I_F / d`:

`(2^d d!)⁻¹ • ∑ⱼ (I ⊗ Uⱼ) T (I ⊗ Uⱼ)† = (Tr_F T) ⊗ (I_F / d)`.

Both sides are `ℂ`-linear in `T`; the operators `TensorProduct.map A B` span `E ⊗ F →ₗ[ℂ] E ⊗ F`
(via `homTensorHomEquiv`), so it suffices to check the identity on product operators, where it
reduces to the single-space twirl on the `F` factor
(`sum_depolarizingUnitary_conj_toLinearMap`) and `partialTraceRight_tensorMap`. This exhibits the
completely depolarizing partial-trace channel as a mixed-unitary average, feeding the mixed-unitary
data-processing inequality for the quantum relative entropy. -/
theorem sum_conjStarAlgEquiv_congrIsometry_depolarizingUnitary [Nonempty ι]
    (b : OrthonormalBasis ι ℂ F) (T : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)) :
    ∑ p : (ι → Bool) × Equiv.Perm ι,
        (((2 : ℂ) ^ Fintype.card ι * (Fintype.card ι).factorial)⁻¹) •
          (TensorProduct.congrIsometry (.refl ℂ E) (b.depolarizingUnitary p)).conjStarAlgEquiv T
      = TensorProduct.mapL
          (LinearMap.toContinuousLinearMap
            (LinearMap.partialTraceRight b (T : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)))
          ((Fintype.card ι : ℂ)⁻¹ • 1) := by
  set w : ℂ := (((2 : ℂ) ^ Fintype.card ι * (Fintype.card ι).factorial)⁻¹) with hw
  -- Rewrite each twirl term's underlying linear map as `(I ⊗ Uⱼ) ∘ S ∘ (I ⊗ Uⱼ⁻¹)`.
  have hterm : ∀ p : (ι → Bool) × Equiv.Perm ι,
      ((TensorProduct.congrIsometry (.refl ℂ E) (b.depolarizingUnitary p)).conjStarAlgEquiv
          T).toLinearMap =
        TensorProduct.map LinearMap.id (b.depolarizingUnitary p).toLinearMap ∘ₗ
          T.toLinearMap ∘ₗ
            TensorProduct.map LinearMap.id (b.depolarizingUnitary p).symm.toLinearMap := by
    intro p
    rw [LinearIsometryEquiv.conjStarAlgEquiv_toLinearMap, LinearEquiv.conj_apply,
      TensorProduct.toLinearEquiv_congrIsometry]
    simp only [TensorProduct.congr_symm, TensorProduct.toLinearMap_congr]
    rfl
  -- Reduce the CLM identity to a LinearMap identity.
  refine ContinuousLinearMap.coe_injective ?_
  rw [ContinuousLinearMap.toLinearMap_sum]
  simp only [ContinuousLinearMap.toLinearMap_smul, hterm, TensorProduct.toLinearMap_mapL,
    LinearMap.coe_toContinuousLinearMap, ContinuousLinearMap.toLinearMap_one]
  -- It suffices to prove the LinearMap identity for an arbitrary operator `S`.
  suffices H : ∀ S : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F,
      (∑ p : (ι → Bool) × Equiv.Perm ι, w •
          (TensorProduct.map LinearMap.id (b.depolarizingUnitary p).toLinearMap ∘ₗ S ∘ₗ
            TensorProduct.map LinearMap.id (b.depolarizingUnitary p).symm.toLinearMap))
        = TensorProduct.map (LinearMap.partialTraceRight b S)
            ((Fintype.card ι : ℂ)⁻¹ • LinearMap.id) by
    exact H _
  intro S
  obtain ⟨X, rfl⟩ := (homTensorHomEquiv ℂ E F E F).surjective S
  induction X using TensorProduct.inductionOn with
  | tmul A B =>
      rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply,
        LinearMap.partialTraceRight_tensorMap]
      -- Product-operator case: the twirl acts only on the `F` factor.
      have hstep : ∀ p : (ι → Bool) × Equiv.Perm ι,
          TensorProduct.map LinearMap.id (b.depolarizingUnitary p).toLinearMap ∘ₗ
              TensorProduct.map A B ∘ₗ
                TensorProduct.map LinearMap.id (b.depolarizingUnitary p).symm.toLinearMap
            = TensorProduct.map A
                ((b.depolarizingUnitary p).toLinearMap ∘ₗ B ∘ₗ
                  (b.depolarizingUnitary p).symm.toLinearMap) := by
        intro p
        rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
        simp
      simp_rw [hstep]
      -- Pull the fixed `map A` factor out of the average, then apply the single-space twirl.
      have hpull : (∑ p : (ι → Bool) × Equiv.Perm ι, w • TensorProduct.map A
            ((b.depolarizingUnitary p).toLinearMap ∘ₗ B ∘ₗ
              (b.depolarizingUnitary p).symm.toLinearMap))
          = TensorProduct.map A (∑ p : (ι → Bool) × Equiv.Perm ι, w •
              ((b.depolarizingUnitary p).toLinearMap ∘ₗ B ∘ₗ
                (b.depolarizingUnitary p).symm.toLinearMap)) := by
        simp only [← TensorProduct.mapBilinear_apply, map_sum, map_smul]
      rw [hpull, hw, b.sum_depolarizingUnitary_conj_toLinearMap B,
        TensorProduct.map_smul_right, TensorProduct.map_smul_left,
        TensorProduct.map_smul_right, smul_smul, div_eq_mul_inv]
  | add X Y ihX ihY =>
      rw [map_add]
      simp only [LinearMap.comp_add, LinearMap.add_comp, smul_add, Finset.sum_add_distrib]
      simp only [ihX, ihY, ← LinearMap.partialTraceRightLM_apply, map_add,
        TensorProduct.map_add_left]

end OrthonormalBasis
