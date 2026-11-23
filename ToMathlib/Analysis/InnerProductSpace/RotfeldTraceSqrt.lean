/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.AlbertiFidelity
public import ToMathlib.Analysis.InnerProductSpace.CommuteSqrtSubadditive
public import ToMathlib.Analysis.InnerProductSpace.CFCSqrtTraceInequality
public import ToMathlib.Analysis.InnerProductSpace.Uhlmann
public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyConvexNonfaithful
public import ToMathlib.Analysis.InnerProductSpace.TraceNormUnitary
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.ResolventBounds

/-!
# Rotfel'd's trace inequality for the operator square root

The operator square root is **not** subadditive (`√(A + B) ≤ √A + √B` fails for non-commuting
positive operators, see `ToMathlib.Analysis.InnerProductSpace.CommuteSqrtSubadditive`). Its
**trace**,
however, *is* subadditive over an arbitrary finite family — this is **Rotfel'd's inequality**:

`tr √(∑ⱼ Bⱼ) ≤ ∑ⱼ tr √Bⱼ`   (for positive operators `Bⱼ` on a finite-dimensional Hilbert space).

`ContinuousLinearMap.re_trace_cfc_sqrt_sum_le_sum_of_nonneg` is the main result (square roots are
`cfc Real.sqrt`, matching the library's operator-square-root API). It is proved first for strictly
positive operators — `√C = C · (√C)⁻¹` with `C = ∑ⱼ Bⱼ`, and `Bⱼ ≤ C` forces
`(√C)⁻¹ ≤ (√Bⱼ)⁻¹` (`CStarAlgebra.ringInverse_le_ringInverse`) — then extended to arbitrary
positive `Bⱼ` by the regularization `Bⱼ ↦ Bⱼ + δ • 1` and continuity of `Y ↦ re tr √Y` as `δ → 0⁺`.

`ContinuousLinearMap.re_trace_cfc_sqrt_sum_mul_le_sum_traceNorm` is the discrimination consequence:
for positive `ρ : ι → E →L[ℂ] E` with `S₀ = ∑ⱼ ρⱼ`,

`re tr(√S₀ · √ρᵢ) ≤ ∑ⱼ ‖√ρᵢ · √ρⱼ‖₁`,

the trace of `√ρᵢ` against the *total* `√S₀` bounded by the sum of pairwise **fidelities**
`‖√ρᵢ √ρⱼ‖₁ = F(ρᵢ, ρⱼ)` — the *unconditional* fidelity-metric counterpart of the (subtle, still
open) affinity paired-trace inequality `re tr(√S₀ · √ρᵢ) ≤ ∑ⱼ re tr(√ρᵢ √ρⱼ)`
(`State.PairedTraceBound`, Nielsen & Chuang Problem 5.5), got by applying Rotfel'd to the conjugated
family `Bⱼ = √ρᵢ ρⱼ √ρᵢ` (`‖√ρᵢ √S₀‖₁ = re tr √(√ρᵢ S₀ √ρᵢ)`).
-/

@[expose] public section

open scoped ComplexOrder Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- The real part of a trace is bounded by the trace norm: `re tr X ≤ ‖X‖₁`. This is
`re tr X ≤ ‖tr X‖ ≤ ‖X‖₁`, the last step being `ContinuousLinearMap.norm_trace_mul_le_traceNorm`
at the identity unitary. -/
theorem re_trace_le_traceNorm (X : E →L[ℂ] E) :
    RCLike.re ((LinearMap.trace ℂ E) ↑X) ≤ X.traceNorm := by
  have h1 : ‖(LinearMap.trace ℂ E) ↑X‖ ≤ X.traceNorm := by
    simpa using ContinuousLinearMap.norm_trace_mul_le_traceNorm X (U := 1) (one_mem _)
  exact (RCLike.re_le_norm _).trans h1

/-- The Rotfel'd per-term step. For a **strictly positive** operator `B` below `C`
(`B ≤ C`), the trace of `B` against the inverse square root of `C` is bounded by the trace of `√B`:

`re tr(B · (√C)⁻¹) ≤ re tr √B`.

Since `√B ≤ √C` and both are strictly positive, `(√C)⁻¹ ≤ (√B)⁻¹`
(`CStarAlgebra.ringInverse_le_ringInverse`); pairing this against the positive `B`
(`re_trace_mul_mono_left`) and cancelling `(√B)⁻¹ · B = √B` closes it. -/
theorem re_trace_mul_ringInverse_cfc_sqrt_le {B C : E →L[ℂ] E}
    (hB : IsStrictlyPositive B) (hBC : B ≤ C) :
    RCLike.re ((LinearMap.trace ℂ E) ↑(B * Ring.inverse (cfc Real.sqrt C)))
      ≤ RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt B)) := by
  have hBnn : (0 : E →L[ℂ] E) ≤ B := hB.1
  have hsqB : IsStrictlyPositive (cfc Real.sqrt B) := hB.cfc_real_sqrt
  have hsqle : cfc Real.sqrt B ≤ cfc Real.sqrt C :=
    ContinuousLinearMap.cfc_real_sqrt_le_cfc_real_sqrt hBnn hBC
  have hinv : Ring.inverse (cfc Real.sqrt C) ≤ Ring.inverse (cfc Real.sqrt B) :=
    CStarAlgebra.ringInverse_le_ringInverse hsqle hsqB
  have hcyc1 : (LinearMap.trace ℂ E) ↑(B * Ring.inverse (cfc Real.sqrt C))
      = (LinearMap.trace ℂ E) ↑(Ring.inverse (cfc Real.sqrt C) * B) := by
    rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
        LinearMap.trace_mul_comm]
  have hmono := ContinuousLinearMap.re_trace_mul_mono_left hinv hBnn
  have hunit : cfc Real.sqrt B * cfc Real.sqrt B = B := cfc_real_sqrt_mul_self_of_nonneg hBnn
  have hstep : Ring.inverse (cfc Real.sqrt B) * B = cfc Real.sqrt B := by
    have h1 : Ring.inverse (cfc Real.sqrt B) * B
        = Ring.inverse (cfc Real.sqrt B) * (cfc Real.sqrt B * cfc Real.sqrt B) := by rw [hunit]
    rw [h1, ← mul_assoc, Ring.inverse_mul_cancel _ hsqB.2, one_mul]
  have hcyc2 : (LinearMap.trace ℂ E) ↑(Ring.inverse (cfc Real.sqrt B) * B)
      = (LinearMap.trace ℂ E) ↑(cfc Real.sqrt B) := by rw [hstep]
  rw [hcyc1]; rw [hcyc2] at hmono; exact hmono

/-- **Rotfel'd's inequality, strictly-positive case.** For a nonempty finite family of **strictly
positive** operators `B : ι → E →L[ℂ] E`,

`re tr √(∑ⱼ Bⱼ) ≤ ∑ⱼ re tr √Bⱼ`.

The total `C = ∑ⱼ Bⱼ` is strictly positive, so `√C = C · (√C)⁻¹`, whence
`re tr √C = ∑ⱼ re tr(Bⱼ · (√C)⁻¹)`; each summand is `≤ re tr √Bⱼ`
(`re_trace_mul_ringInverse_cfc_sqrt_le`, using `Bⱼ ≤ C`). -/
theorem re_trace_cfc_sqrt_sum_le_sum_of_strictlyPositive {ι : Type*} {s : Finset ι}
    {B : ι → E →L[ℂ] E} (hs : s.Nonempty) (hB : ∀ j ∈ s, IsStrictlyPositive (B j)) :
    RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt (∑ j ∈ s, B j)))
      ≤ ∑ j ∈ s, RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt (B j))) := by
  set C := ∑ j ∈ s, B j with hC
  have hBnn : ∀ j ∈ s, (0 : E →L[ℂ] E) ≤ B j := fun j hj => (hB j hj).1
  have hle : ∀ j ∈ s, B j ≤ C := fun j hj => Finset.single_le_sum hBnn hj
  obtain ⟨j0, hj0⟩ := hs
  have hCsp : IsStrictlyPositive C := IsStrictlyPositive.of_le (hB j0 hj0) (hle j0 hj0)
  have hsqrtC : cfc Real.sqrt C = C * Ring.inverse (cfc Real.sqrt C) := by
    have hnn : (0 : E →L[ℂ] E) ≤ C := hCsp.1
    have hunit : cfc Real.sqrt C * cfc Real.sqrt C = C := cfc_real_sqrt_mul_self_of_nonneg hnn
    have hsqC : IsStrictlyPositive (cfc Real.sqrt C) := hCsp.cfc_real_sqrt
    calc cfc Real.sqrt C
        = cfc Real.sqrt C * (cfc Real.sqrt C * Ring.inverse (cfc Real.sqrt C)) := by
            rw [Ring.mul_inverse_cancel _ hsqC.2, mul_one]
      _ = cfc Real.sqrt C * cfc Real.sqrt C * Ring.inverse (cfc Real.sqrt C) := by rw [mul_assoc]
      _ = C * Ring.inverse (cfc Real.sqrt C) := by rw [hunit]
  rw [hsqrtC, hC, Finset.sum_mul, ContinuousLinearMap.toLinearMap_sum, map_sum, map_sum]
  exact Finset.sum_le_sum fun j hj => re_trace_mul_ringInverse_cfc_sqrt_le (hB j hj) (hle j hj)

/-- **Rotfel'd's inequality.** For a finite family of **positive** operators
`B : ι → E →L[ℂ] E` on a finite-dimensional complex Hilbert space, the trace of the operator square
root is subadditive:

`re tr √(∑ⱼ Bⱼ) ≤ ∑ⱼ re tr √Bⱼ`.

(The operator inequality `√(∑ⱼ Bⱼ) ≤ ∑ⱼ √Bⱼ` is *false* without commutativity; only its trace
survives.) Proved from the strictly-positive case
(`re_trace_cfc_sqrt_sum_le_sum_of_strictlyPositive`) by the regularization `Bⱼ ↦ Bⱼ + δ • 1` and
continuity of `Y ↦ re tr √Y` on the positive cone as `δ → 0⁺`. -/
theorem re_trace_cfc_sqrt_sum_le_sum_of_nonneg {ι : Type*} {s : Finset ι}
    {B : ι → E →L[ℂ] E} (hB : ∀ j ∈ s, 0 ≤ B j) :
    RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt (∑ j ∈ s, B j)))
      ≤ ∑ j ∈ s, RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt (B j))) := by
  rcases s.eq_empty_or_nonempty with hemp | hne
  · subst hemp; simp
  have hcont : ContinuousOn
      (fun Y : E →L[ℂ] E => RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt Y))) {Y | 0 ≤ Y} := by
    have htr : Continuous (fun T : E →L[ℂ] E => (LinearMap.trace ℂ E) ↑T) :=
      ((LinearMap.trace ℂ E).comp (ContinuousLinearMap.coeLM ℂ)).continuous_of_finiteDimensional
    exact (Complex.continuous_re.comp htr).comp_continuousOn continuousOn_cfc_real_sqrt
  have hsmulcont : ∀ j : ι, Continuous (fun δ : ℝ => B j + δ • (1 : E →L[ℂ] E)) :=
    fun j => continuous_const.add (continuous_id.smul continuous_const)
  have hsumcont : Continuous (fun δ : ℝ => ∑ j ∈ s, (B j + δ • (1 : E →L[ℂ] E))) :=
    continuous_finsetSum s fun j _ => hsmulcont j
  have hFtend : Filter.Tendsto
      (fun δ : ℝ => RCLike.re ((LinearMap.trace ℂ E)
        ↑(cfc Real.sqrt (∑ j ∈ s, (B j + δ • (1 : E →L[ℂ] E)))))) (𝓝[>] 0)
      (𝓝 (RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt (∑ j ∈ s, B j))))) := by
    have hpath : Filter.Tendsto (fun δ : ℝ => ∑ j ∈ s, (B j + δ • (1 : E →L[ℂ] E)))
        (𝓝[>] 0) (𝓝 (∑ j ∈ s, B j)) := by
      have h0 := (hsumcont.continuousWithinAt (s := Set.Ioi 0) (x := 0)).tendsto
      simpa using h0
    have hcone : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        (∑ j ∈ s, (B j + δ • (1 : E →L[ℂ] E))) ∈ {Y : E →L[ℂ] E | 0 ≤ Y} := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact Finset.sum_nonneg fun j hj =>
        add_nonneg (hB j hj) (smul_nonneg (le_of_lt hδ) zero_le_one)
    exact (hcont.continuousWithinAt (Finset.sum_nonneg hB)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hpath, hcone⟩)
  have hGtend : Filter.Tendsto
      (fun δ : ℝ => ∑ j ∈ s, RCLike.re ((LinearMap.trace ℂ E)
        ↑(cfc Real.sqrt (B j + δ • (1 : E →L[ℂ] E))))) (𝓝[>] 0)
      (𝓝 (∑ j ∈ s, RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt (B j))))) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hpath : Filter.Tendsto (fun δ : ℝ => B j + δ • (1 : E →L[ℂ] E)) (𝓝[>] 0) (𝓝 (B j)) := by
      have h0 := ((hsmulcont j).continuousWithinAt (s := Set.Ioi 0) (x := 0)).tendsto
      simpa using h0
    have hcone : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (B j + δ • (1 : E →L[ℂ] E)) ∈ {Y : E →L[ℂ] E | 0 ≤ Y} := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact add_nonneg (hB j hj) (smul_nonneg (le_of_lt hδ) zero_le_one)
    exact (hcont.continuousWithinAt (hB j hj)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hpath, hcone⟩)
  refine le_of_tendsto_of_tendsto hFtend hGtend ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact re_trace_cfc_sqrt_sum_le_sum_of_strictlyPositive hne
    fun j hj => isStrictlyPositive_add_smul_one (hB j hj) hδ

/-- **Fidelity-sum bound on the total-square-root pairing** (the discrimination consequence of
Rotfel'd's inequality). For a finite family of positive operators `ρ : ι → E →L[ℂ] E` with total
`S₀ = ∑ⱼ ρⱼ`, the trace of `√ρᵢ` against the total square root `√S₀` is bounded by the sum of the
pairwise fidelities `‖√ρᵢ √ρⱼ‖₁`:

`re tr(√S₀ · √ρᵢ) ≤ ∑ⱼ ‖√ρᵢ · √ρⱼ‖₁`.

This holds for **every** family of positive operators — no commutativity, no normalization. It is
the fidelity-metric counterpart of the affinity paired-trace inequality
`re tr(√S₀ · √ρᵢ) ≤ ∑ⱼ re tr(√ρᵢ √ρⱼ)` (the latter subtle and, in general, open): the affinity
`re tr(√ρᵢ √ρⱼ)` is dominated by the fidelity `‖√ρᵢ √ρⱼ‖₁`, and this bound is unconditional.

The proof pairs cyclicity and `re tr X ≤ ‖X‖₁` (`re_trace_le_traceNorm`) with the trace-norm/trace
identity `‖√ρᵢ √S₀‖₁ = re tr √(√ρᵢ S₀ √ρᵢ)`
(`traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj`), then applies Rotfel'd
(`re_trace_cfc_sqrt_sum_le_sum_of_nonneg`) to the conjugated family `√ρᵢ ρⱼ √ρᵢ` and reads each term
back as `‖√ρᵢ √ρⱼ‖₁`. -/
theorem re_trace_cfc_sqrt_sum_mul_le_sum_traceNorm {ι : Type*} [Fintype ι]
    (ρ : ι → E →L[ℂ] E) (hρ : ∀ j, 0 ≤ ρ j) (i : ι) :
    RCLike.re ((LinearMap.trace ℂ E) ↑(cfc Real.sqrt (∑ j, ρ j) * cfc Real.sqrt (ρ i)))
      ≤ ∑ j, (cfc Real.sqrt (ρ i) * cfc Real.sqrt (ρ j)).traceNorm := by
  have hS0 : (0 : E →L[ℂ] E) ≤ ∑ j, ρ j := Finset.sum_nonneg fun j _ => hρ j
  have hsa : IsSelfAdjoint (cfc Real.sqrt (ρ i)) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp (cfc_real_sqrt_nonneg (ρ i))).isSelfAdjoint
  have hcyc : (LinearMap.trace ℂ E) ↑(cfc Real.sqrt (∑ j, ρ j) * cfc Real.sqrt (ρ i))
      = (LinearMap.trace ℂ E) ↑(cfc Real.sqrt (ρ i) * cfc Real.sqrt (∑ j, ρ j)) := by
    rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
        LinearMap.trace_mul_comm]
  rw [hcyc]
  refine (re_trace_le_traceNorm _).trans ?_
  rw [ContinuousLinearMap.traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj _ _ hS0]
  have hdist : cfc Real.sqrt (ρ i) * (∑ j, ρ j) * cfc Real.sqrt (ρ i)
      = ∑ j, cfc Real.sqrt (ρ i) * ρ j * cfc Real.sqrt (ρ i) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hdist]
  refine (re_trace_cfc_sqrt_sum_le_sum_of_nonneg
    (fun j _ => IsSelfAdjoint.conjugate_nonneg (hρ j) hsa)).trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
  rw [ContinuousLinearMap.traceNorm_cfc_sqrt_mul_eq_re_trace_cfc_sqrt_conj _ _ (hρ j)]

end ContinuousLinearMap
