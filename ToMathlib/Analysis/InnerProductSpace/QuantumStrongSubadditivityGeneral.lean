/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumStrongSubadditivity
public import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropyContinuous

/-!
# Strong subadditivity for all density operators (positivity-free)

The strictly-positive strong subadditivity
`ContinuousLinearMap.vonNeumannEntropy_add_partialTrace_le` (Nielsen & Chuang, Theorem 11.14)
carries the faithfulness hypothesis `IsStrictlyPositive ρ` inherited from the relative-entropy
engine. This file removes it, proving strong subadditivity for **every** density operator on a
tripartite space `E ⊗ (F ⊗ G)`:

`S(ρ) + S(ρ_F) ≤ S(ρ_{EF}) + S(ρ_{FG})`.

## Proof route: regularisation and continuity

A general density operator `ρ` is the `t → 0⁺` limit of the strictly positive regularised states

`ρ_t := (1 - t) · ρ + t · (d⁻¹ · 1)`, where `d = finrank ℂ (E ⊗ (F ⊗ G))`,

each a convex combination of `ρ` with the maximally mixed state (`IsDensityOp.convex_combination`),
strictly positive for `t ∈ (0, 1]` because `t · (d⁻¹ · 1)` is (`IsStrictlyPositive.nonneg_add`).
Strong subadditivity holds for each `ρ_t` by the strictly-positive theorem. All four marginals of
`ρ_t` are the corresponding affine combinations of the marginals of `ρ` with the (fixed) marginals
of the maximally mixed state — taken as the actual partial traces, so they never need to be
identified with maximally mixed states — hence stay density operators along the path. The four
entropies therefore converge to those of the marginals of `ρ` as `t → 0⁺`
(`ContinuousLinearMap.IsDensityOp.continuousOn_vonNeumannEntropy`, the continuity keystone), and
since `≤` is a closed condition the inequality passes to the limit (`le_of_tendsto_of_tendsto` over
the punctured neighbourhood `𝓝[Set.Ioc 0 1] 0`).

## Main result

* `ContinuousLinearMap.vonNeumannEntropy_add_partialTrace_le_of_isDensityOp` — strong subadditivity
  `S(ρ) + S(ρ_F) ≤ S(ρ_{EF}) + S(ρ_{FG})` for an arbitrary density operator `ρ`.
-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap Filter Topology
open scoped TensorProduct ComplexOrder

namespace ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

set_option synthInstance.maxHeartbeats 400000 in
-- The nested-tensor operator algebras `(E ⊗ (F ⊗ G)) →L …` force a deep instance search, as in the
-- strictly-positive `vonNeumannEntropy_add_partialTrace_le` this proof invokes.
set_option maxHeartbeats 1000000 in
-- The regularisation threads several such nested-tensor algebras through the limit argument, so the
-- overall elaboration budget must also be raised beyond the default.
/-- **Strong subadditivity of the von Neumann entropy for all density operators** (Nielsen &
Chuang, Theorem 11.14, positivity-free form). For an arbitrary density operator `ρ` on the
tripartite space `E ⊗ (F ⊗ G)`,

`S(ρ) + S(ρ_F) ≤ S(ρ_{EF}) + S(ρ_{FG})`,

with the marginals `ρ_{EF}` (trace out `G` after re-associating to `(E ⊗ F) ⊗ G`),
`ρ_{FG} = Tr_E ρ` and `ρ_F = Tr_G ρ_{FG}` supplied as hypotheses. This drops the faithfulness
hypothesis `IsStrictlyPositive ρ` of `vonNeumannEntropy_add_partialTrace_le` by a
regularisation/limiting argument (see the module docstring), the continuity of the von Neumann
entropy on density operators being the enabling ingredient. -/
theorem vonNeumannEntropy_add_partialTrace_le_of_isDensityOp
    {ιE ιF ιG : Type*} [Fintype ιE] [Fintype ιF] [Fintype ιG]
    [Nonempty ιE] [Nonempty ιF] [Nonempty ιG]
    (bE : OrthonormalBasis ιE ℂ E) (bF : OrthonormalBasis ιF ℂ F) (bG : OrthonormalBasis ιG ℂ G)
    {ρ : (E ⊗[ℂ] (F ⊗[ℂ] G)) →L[ℂ] (E ⊗[ℂ] (F ⊗[ℂ] G))}
    {ρAB : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)} {ρBC : (F ⊗[ℂ] G) →L[ℂ] (F ⊗[ℂ] G)} {ρB : F →L[ℂ] F}
    (hρ : ρ.IsDensityOp)
    (hρAB : LinearMap.partialTraceRight bG
      ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv ρ).toLinearMap = ρAB.toLinearMap)
    (hρBC : LinearMap.partialTraceLeft bE ρ.toLinearMap = ρBC.toLinearMap)
    (hρB : LinearMap.partialTraceRight bG ρBC.toLinearMap = ρB.toLinearMap) :
    ρ.vonNeumannEntropy + ρB.vonNeumannEntropy ≤
      ρAB.vonNeumannEntropy + ρBC.vonNeumannEntropy := by
  classical
  -- The marginals are themselves density operators.
  have hρABd : ρAB.IsDensityOp :=
    ((LinearIsometryEquiv.conjStarAlgEquiv_isDensityOp_iff _).mpr hρ).of_partialTraceRight_eq
      bG hρAB
  have hρBCd : ρBC.IsDensityOp := hρ.of_partialTraceLeft_eq bE hρBC
  have hρBd : ρB.IsDensityOp := hρBCd.of_partialTraceRight_eq bG hρB
  -- The tripartite space is nontrivial (its factors carry nonempty orthonormal bases), so the
  -- maximally mixed state `d⁻¹ • 1` is available as a strictly positive regulariser.
  have : Nontrivial E := nontrivial_of_ne (bE (Classical.arbitrary ιE)) 0
    (bE.orthonormal.ne_zero (Classical.arbitrary ιE))
  have : Nontrivial F := nontrivial_of_ne (bF (Classical.arbitrary ιF)) 0
    (bF.orthonormal.ne_zero (Classical.arbitrary ιF))
  have : Nontrivial G := nontrivial_of_ne (bG (Classical.arbitrary ιG)) 0
    (bG.orthonormal.ne_zero (Classical.arbitrary ιG))
  have : Nontrivial (E ⊗[ℂ] (F ⊗[ℂ] G)) :=
    nontrivial_of_ne ((bE.tensorProduct (bF.tensorProduct bG)) (Classical.arbitrary _)) 0
      ((bE.tensorProduct (bF.tensorProduct bG)).orthonormal.ne_zero _)
  set mm : (E ⊗[ℂ] (F ⊗[ℂ] G)) →L[ℂ] (E ⊗[ℂ] (F ⊗[ℂ] G)) :=
    ((Module.finrank ℂ (E ⊗[ℂ] (F ⊗[ℂ] G)) : ℂ))⁻¹ • 1 with hmm_def
  have hmm_d : mm.IsDensityOp := isDensityOp_finrank_inv_smul_one
  have hmm_s : IsStrictlyPositive mm := isStrictlyPositive_finrank_inv_smul_one
  -- The three marginals of the regulariser, taken as the actual partial traces (hence density
  -- operators via marginalisation); they never need to be identified with maximally mixed states.
  set mmAB : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F) := LinearMap.toContinuousLinearMap
    (LinearMap.partialTraceRight bG
      ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv mm).toLinearMap) with hmmAB_def
  set mmBC : (F ⊗[ℂ] G) →L[ℂ] (F ⊗[ℂ] G) := LinearMap.toContinuousLinearMap
    (LinearMap.partialTraceLeft bE mm.toLinearMap) with hmmBC_def
  set mmB : F →L[ℂ] F := LinearMap.toContinuousLinearMap
    (LinearMap.partialTraceRight bG mmBC.toLinearMap) with hmmB_def
  have hmmAB_d : mmAB.IsDensityOp :=
    ((LinearIsometryEquiv.conjStarAlgEquiv_isDensityOp_iff _).mpr hmm_d).of_partialTraceRight_eq bG
      (LinearMap.coe_toContinuousLinearMap _).symm
  have hmmBC_d : mmBC.IsDensityOp :=
    hmm_d.of_partialTraceLeft_eq bE (LinearMap.coe_toContinuousLinearMap _).symm
  have hmmB_d : mmB.IsDensityOp :=
    hmmBC_d.of_partialTraceRight_eq bG (LinearMap.coe_toContinuousLinearMap _).symm
  -- `0` is a limit point of `(0, 1]`, so the punctured neighbourhood is a nontrivial filter.
  have : (𝓝[Set.Ioc (0 : ℝ) 1] 0).NeBot := left_nhdsWithin_Ioc_neBot (by norm_num)
  -- Strong subadditivity holds for each regularised state `ρ_t = (1-t)ρ + t·mm` (`t ∈ (0,1]`,
  -- strictly positive); the four entropies converge to those of the marginals as `t → 0⁺`, and the
  -- inequality is closed, so it passes to the limit.
  refine le_of_tendsto_of_tendsto
    ((tendsto_vonNeumannEntropy_regularise ρ mm hρ hmm_d).add
      (tendsto_vonNeumannEntropy_regularise ρB mmB hρBd hmmB_d))
    ((tendsto_vonNeumannEntropy_regularise ρAB mmAB hρABd hmmAB_d).add
      (tendsto_vonNeumannEntropy_regularise ρBC mmBC hρBCd hmmBC_d)) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  set σt : (E ⊗[ℂ] (F ⊗[ℂ] G)) →L[ℂ] (E ⊗[ℂ] (F ⊗[ℂ] G)) :=
    ((1 - t : ℝ) : ℂ) • ρ + ((t : ℝ) : ℂ) • mm with hσt_def
  have hσt_d : σt.IsDensityOp :=
    IsDensityOp.convex_combination hρ hmm_d
      (by exact_mod_cast (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)) (by exact_mod_cast ht.1.le)
      (by push_cast; ring)
  have hσt_s : IsStrictlyPositive σt := by
    refine IsStrictlyPositive.nonneg_add ?_ (IsStrictlyPositive.smul (by exact_mod_cast ht.1) hmm_s)
    exact nonneg_iff_isPositive.mpr
      (hρ.isPositive.smul_of_nonneg (by exact_mod_cast (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)))
  -- The marginals of `ρ_t` are the corresponding affine combinations of the marginals, by linearity
  -- of `conjStarAlgEquiv` and of the partial traces.
  have hAB_t : LinearMap.partialTraceRight bG
      ((TensorProduct.assocIsometry ℂ E F G).symm.conjStarAlgEquiv σt).toLinearMap =
      (((1 - t : ℝ) : ℂ) • ρAB + ((t : ℝ) : ℂ) • mmAB).toLinearMap := by
    rw [hσt_def, map_add, map_smul, map_smul, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_smul,
      ← LinearMap.partialTraceRightLM_apply, map_add, map_smul, map_smul,
      LinearMap.partialTraceRightLM_apply, LinearMap.partialTraceRightLM_apply, hρAB, hmmAB_def,
      ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
          ContinuousLinearMap.toLinearMap_smul,
      LinearMap.coe_toContinuousLinearMap]
  -- NB: keep the `key` linearity step + *exhaustive* `simp only`; do NOT collapse into one `rw`.
  -- Unlike the sibling `hAB_t` (whose leading `conjStarAlgEquiv` rewrites reshape the term so a
  -- single `rw`'s fixed coe-lemma counts line up), these partial-trace-only chains have their fixed
  -- coe counts consumed on the wrong side of the equation, so a collapsed `rw` fails with
  -- `did not find … ↑(toContinuousLinearMap ?f)`. The `simp only` rewrites all coe occurrences.
  have hBC_t : LinearMap.partialTraceLeft bE σt.toLinearMap =
      (((1 - t : ℝ) : ℂ) • ρBC + ((t : ℝ) : ℂ) • mmBC).toLinearMap := by
    have key : LinearMap.partialTraceLeft bE σt.toLinearMap =
        ((1 - t : ℝ) : ℂ) • LinearMap.partialTraceLeft bE ρ.toLinearMap +
          ((t : ℝ) : ℂ) • LinearMap.partialTraceLeft bE mm.toLinearMap := by
      rw [hσt_def, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
        ContinuousLinearMap.toLinearMap_smul, ← LinearMap.partialTraceLeftLM_apply, map_add,
            map_smul,
        map_smul, LinearMap.partialTraceLeftLM_apply, LinearMap.partialTraceLeftLM_apply]
    rw [key, hρBC, hmmBC_def]
    simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.coe_toContinuousLinearMap]
  have hB_t : LinearMap.partialTraceRight bG
      (((1 - t : ℝ) : ℂ) • ρBC + ((t : ℝ) : ℂ) • mmBC).toLinearMap =
      (((1 - t : ℝ) : ℂ) • ρB + ((t : ℝ) : ℂ) • mmB).toLinearMap := by
    have key : LinearMap.partialTraceRight bG
        (((1 - t : ℝ) : ℂ) • ρBC + ((t : ℝ) : ℂ) • mmBC).toLinearMap =
        ((1 - t : ℝ) : ℂ) • LinearMap.partialTraceRight bG ρBC.toLinearMap +
          ((t : ℝ) : ℂ) • LinearMap.partialTraceRight bG mmBC.toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
          ContinuousLinearMap.toLinearMap_smul,
        ← LinearMap.partialTraceRightLM_apply, map_add, map_smul, map_smul,
        LinearMap.partialTraceRightLM_apply, LinearMap.partialTraceRightLM_apply]
    rw [key, hρB, hmmB_def]
    simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.coe_toContinuousLinearMap]
  exact vonNeumannEntropy_add_partialTrace_le bE bF bG hσt_d hσt_s hAB_t hBC_t hB_t

end ContinuousLinearMap
