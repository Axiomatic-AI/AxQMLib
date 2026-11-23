/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract
public import ToMathlib.Analysis.InnerProductSpace.Density

/-!
# Reduced states

The **reduced state** of a bipartite density operator `T : E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F` on the
factor `E` is its partial trace over `F`. This file records the basic fact that a reduced
state is again a density operator: tracing out a subsystem of a quantum state yields a
quantum state.

Following the library's reduced-state convention (cf. `traceDistance_le_of_partialTraceRight_eq`,
`TensorProduct.IsPurification`), the reduced operator `ρ` is taken as a given
`ContinuousLinearMap` carrying the `LinearMap`-level hypothesis
`LinearMap.partialTraceRight b T.toLinearMap = ρ.toLinearMap`, rather than re-promoting the
`LinearMap`-valued partial trace to a `ContinuousLinearMap`. This keeps the density-operator
reasoning (CFC, positivity) entirely on the `ContinuousLinearMap` side while the partial trace
stays at its native `LinearMap` level.

## Main results

* `ContinuousLinearMap.IsDensityOp.of_partialTraceRight_eq`,
  `ContinuousLinearMap.IsDensityOp.of_partialTraceLeft_eq`: a reduced state of a density
  operator is a density operator.
-/

@[expose] public section

open scoped TensorProduct

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {ι : Type*} [Fintype ι]

/-- **A reduced state is a density operator** (right factor). If `T` is a density operator on
`E ⊗[𝕜] F` and `ρ : E →L[𝕜] E` is its reduced state on `E` (`partialTraceRight b ↑T = ↑ρ`),
then `ρ` is a density operator: positive (`partialTraceRight` preserves positivity) with
trace `1` (`trace (partialTraceRight b ↑T) = trace ↑T = 1`). -/
theorem IsDensityOp.of_partialTraceRight_eq {T : E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F} {ρ : E →L[𝕜] E}
    (hT : T.IsDensityOp) (b : OrthonormalBasis ι 𝕜 F)
    (hρ : LinearMap.partialTraceRight b T.toLinearMap = ρ.toLinearMap) : ρ.IsDensityOp := by
  refine ⟨?_, ?_⟩
  · rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, ← hρ]
    exact LinearMap.partialTraceRight_isPositive b hT.isPositive.toLinearMap
  · rw [← hρ, LinearMap.trace_partialTraceRight]
    exact hT.trace_eq_one

/-- **A reduced state is a density operator** (left factor). If `T` is a density operator on
`E ⊗[𝕜] F` and `ρ : F →L[𝕜] F` is its reduced state on `F` (`partialTraceLeft b ↑T = ↑ρ`),
then `ρ` is a density operator. -/
theorem IsDensityOp.of_partialTraceLeft_eq {T : E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F} {ρ : F →L[𝕜] F}
    (hT : T.IsDensityOp) (b : OrthonormalBasis ι 𝕜 E)
    (hρ : LinearMap.partialTraceLeft b T.toLinearMap = ρ.toLinearMap) : ρ.IsDensityOp := by
  refine ⟨?_, ?_⟩
  · rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, ← hρ]
    exact LinearMap.partialTraceLeft_isPositive b hT.isPositive.toLinearMap
  · rw [← hρ, LinearMap.trace_partialTraceLeft]
    exact hT.trace_eq_one

section StrictlyPositive

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {ι : Type*} [Fintype ι] [Nonempty ι]

open scoped InnerProductSpace

/-- **A reduced state of a faithful state is faithful** (right factor). If `T` is strictly positive
on `E ⊗[ℂ] F` and `ρ : E →L[ℂ] E` is its reduced state on `E` (`partialTraceRight b ↑T = ↑ρ`), then
`ρ` is strictly positive. The marginal is positive-definite because
`⟪x, ρ x⟫ = ∑ k, ⟪x ⊗ b k, T (x ⊗ b k)⟫` (`inner_partialTraceRight_self`) is a sum of strictly
positive terms (`IsStrictlyPositive.re_inner_self_pos`, as `x ⊗ b k ≠ 0`), so `ρ` is injective,
hence invertible. -/
theorem _root_.IsStrictlyPositive.of_partialTraceRight_eq [CompleteSpace E]
    {T : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)} {ρ : E →L[ℂ] E}
    (hT : IsStrictlyPositive T) (b : OrthonormalBasis ι ℂ F)
    (hρ : LinearMap.partialTraceRight b T.toLinearMap = ρ.toLinearMap) :
    IsStrictlyPositive ρ := by
  refine ContinuousLinearMap.isStrictlyPositive_of_re_inner_self_pos ?_ fun x hx ↦ ?_
  · rw [ContinuousLinearMap.nonneg_iff_isPositive,
      ← ContinuousLinearMap.isPositive_toLinearMap_iff, ← hρ]
    exact LinearMap.partialTraceRight_isPositive b ((ContinuousLinearMap.isPositive_toLinearMap_iff
      T).mp (ContinuousLinearMap.nonneg_iff_isPositive.mp hT.nonneg))
  · rw [← ContinuousLinearMap.coe_coe ρ, ← hρ,
      LinearMap.inner_partialTraceRight_self, map_sum]
    refine Finset.sum_pos (fun k _ ↦ ?_) Finset.univ_nonempty
    have hzne : x ⊗ₜ[ℂ] b k ≠ 0 := by
      rw [← norm_ne_zero_iff, TensorProduct.norm_tmul]; simp [hx]
    rw [← RCLike.conj_re, inner_conj_symm]
    exact hT.re_inner_self_pos hzne

omit [Nonempty ι] in
/-- **The support condition descends to the partial trace.** If `supp T ⊆ supp S` on `E ⊗ F` and
`S` is positive, then the marginals satisfy `supp (Tr_F T) ⊆ supp (Tr_F S)`. For `x ∈ ker (Tr_F S)`,
the slice sum `⟪x, (Tr_F S) x⟫ = ∑ₖ ⟪x ⊗ bₖ, S (x ⊗ bₖ)⟫` vanishes; each term is `≥ 0` (`S`
positive), so each `S (x ⊗ bₖ) = 0`, i.e. `x ⊗ bₖ ∈ ker S ⊆ ker T`; hence
`(Tr_F T) x = ∑ₖ restrictRightₖ (T (x ⊗ bₖ)) = 0`. The support-condition twin of
`IsStrictlyPositive.of_partialTraceRight_eq`; lets the relaxed-DPI marginal support condition be
*derived* from the full one, not assumed. -/
theorem HasSupportLE.of_partialTraceRight
    {T S : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)} {T' S' : E →L[ℂ] E} (hS : 0 ≤ S)
    (hsupp : HasSupportLE T S) (b : OrthonormalBasis ι ℂ F)
    (hred_T : LinearMap.partialTraceRight b T.toLinearMap = T'.toLinearMap)
    (hred_S : LinearMap.partialTraceRight b S.toLinearMap = S'.toLinearMap) :
    HasSupportLE T' S' := by
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  rw [LinearMap.mem_ker, ← hred_T, LinearMap.partialTraceRight_apply]
  have hSpos := (ContinuousLinearMap.isPositive_toLinearMap_iff S).mp
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hS)
  have hsum : (∑ k, RCLike.re ⟪x ⊗ₜ[ℂ] b k, S.toLinearMap (x ⊗ₜ[ℂ] b k)⟫_ℂ) = 0 := by
    rw [← map_sum RCLike.re, ← LinearMap.inner_partialTraceRight_self b S.toLinearMap x, hred_S]
    simp [hx]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hSk : S (x ⊗ₜ[ℂ] b k) = 0 := ContinuousLinearMap.apply_eq_zero_of_re_inner_self_eq_zero hS
    ((Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ hSpos.re_inner_nonneg_right _).mp
      hsum k (Finset.mem_univ k))
  have hTk : T.toLinearMap (x ⊗ₜ[ℂ] b k) = 0 :=
    hsupp (by rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]; exact hSk)
  rw [hTk, map_zero]

/-- **A reduced state of a faithful state is faithful** (left factor). Symmetric to
`IsStrictlyPositive.of_partialTraceRight_eq`: the `F`-marginal of a strictly positive `T` is
strictly positive. -/
theorem _root_.IsStrictlyPositive.of_partialTraceLeft_eq [CompleteSpace F]
    {T : (E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)} {ρ : F →L[ℂ] F}
    (hT : IsStrictlyPositive T) (b : OrthonormalBasis ι ℂ E)
    (hρ : LinearMap.partialTraceLeft b T.toLinearMap = ρ.toLinearMap) :
    IsStrictlyPositive ρ := by
  refine ContinuousLinearMap.isStrictlyPositive_of_re_inner_self_pos ?_ fun y hy ↦ ?_
  · rw [ContinuousLinearMap.nonneg_iff_isPositive,
      ← ContinuousLinearMap.isPositive_toLinearMap_iff, ← hρ]
    exact LinearMap.partialTraceLeft_isPositive b ((ContinuousLinearMap.isPositive_toLinearMap_iff
      T).mp (ContinuousLinearMap.nonneg_iff_isPositive.mp hT.nonneg))
  · rw [← ContinuousLinearMap.coe_coe ρ, ← hρ,
      LinearMap.inner_partialTraceLeft_self, map_sum]
    refine Finset.sum_pos (fun k _ ↦ ?_) Finset.univ_nonempty
    have hzne : b k ⊗ₜ[ℂ] y ≠ 0 := by
      rw [← norm_ne_zero_iff, TensorProduct.norm_tmul]; simp [hy]
    rw [← RCLike.conj_re, inner_conj_symm]
    exact hT.re_inner_self_pos hzne

end StrictlyPositive

end ContinuousLinearMap
