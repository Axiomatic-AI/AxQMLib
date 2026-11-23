/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Density
public import ToMathlib.Analysis.InnerProductSpace.Trace
public import ToMathlib.Analysis.InnerProductSpace.TraceNorm
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Complex.Basic
public import ToMathlib.Dynamics.BirkhoffSum.CompactFixedPoint
public import ToMathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A fixed-point theorem for quantum channels

This file proves that a linear superoperator that maps the (compact, convex) set of density
operators into itself has a **density-operator fixed point**. This is the operator-theoretic
core of Nielsen & Chuang, Exercise 9.9 ("every trace-preserving quantum operation has a fixed
point"): the exercise asks for a proof via Schauder's fixed-point theorem, and in finite
dimensions — the only case relevant here — the set of density operators is a compact convex
subset of the space of operators, so Schauder's theorem reduces to its finite-dimensional
content. Rather than route through Brouwer (not available in Mathlib), we invoke the elementary
**Markov–Kakutani / mean-ergodic** fixed-point lemma
`ContinuousLinearMap.exists_isFixedPt_of_isCompact_of_convex`
(`ToMathlib.Dynamics.BirkhoffSum.CompactFixedPoint`), valid for any *linear* self-map.

## Main results

* `isCompact_setOf_isDensityOp`: the set of density operators on a finite-dimensional inner
  product space is compact (Heine–Borel: closed by `isClosed_setOf_isPositive` and continuity
  of the trace, bounded because `‖ρ‖ ≤ ‖ρ‖₁ = tr ρ = 1`).
* `convex_setOf_isDensityOp`: the set of density operators is convex (from
  `IsDensityOp.convex_combination`).
* `ContinuousLinearMap.exists_isDensityOp_isFixedPt`: a `ℂ`-linear superoperator preserving
  the density set has a density-operator fixed point.
-/

@[expose] public section

noncomputable section

section Density

/-- **The set of density operators is convex.** Immediate from the two-operator convex
combination lemma `ContinuousLinearMap.IsDensityOp.convex_combination`, identifying the real
convex weights with their images in `ℂ`. -/
theorem convex_setOf_isDensityOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Convex ℝ {T : E →L[ℂ] E | T.IsDensityOp} := by
  have : IsScalarTower ℝ ℂ (E →L[ℂ] E) := IsScalarTower.restrictScalars ℝ ℂ _
  rw [convex_iff_forall_pos]
  intro T hT S hS a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hT hS ⊢
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a T, RCLike.real_smul_eq_coe_smul (K := ℂ) b S]
  refine hT.convex_combination hS (RCLike.ofReal_nonneg.mpr ha.le)
    (RCLike.ofReal_nonneg.mpr hb.le) ?_
  rw [← RCLike.ofReal_add, hab, RCLike.ofReal_one]

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **The set of density operators is compact** on a finite-dimensional inner product space
(Heine–Borel). It is closed — the intersection of the closed set of positive operators
(`ContinuousLinearMap.isClosed_setOf_isPositive`) with the closed level set `{tr = 1}`
(continuity of the trace) — and bounded, since a density operator `ρ` satisfies
`‖ρ‖ ≤ ‖ρ‖₁ = re(tr ρ) = 1`. -/
theorem isCompact_setOf_isDensityOp :
    IsCompact {T : E →L[𝕜] E | T.IsDensityOp} := by
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  have : ProperSpace (E →L[𝕜] E) := FiniteDimensional.proper_rclike 𝕜 _
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · -- Closed: positivity ∧ trace = 1.
    have hset : {T : E →L[𝕜] E | T.IsDensityOp}
        = {T : E →L[𝕜] E | T.IsPositive}
          ∩ {T : E →L[𝕜] E | LinearMap.trace 𝕜 E (T : E →ₗ[𝕜] E) = 1} := by
      ext T; simp [ContinuousLinearMap.isDensityOp_iff]
    rw [hset]
    exact ContinuousLinearMap.isClosed_setOf_isPositive.inter
      (isClosed_singleton.preimage (by fun_prop))
  · -- Bounded: `‖T‖ ≤ 1`.
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun T hT => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖T‖
        ≤ T.traceNorm := T.opNorm_le_traceNorm
      _ = RCLike.re (LinearMap.trace 𝕜 E (T : E →ₗ[𝕜] E)) :=
          ContinuousLinearMap.traceNorm_eq_re_trace_of_isPositive hT.isPositive
      _ = 1 := by rw [hT.trace_eq_one, RCLike.one_re]

end Density

namespace ContinuousLinearMap

/-- **A superoperator preserving the density set has a density-operator fixed point.** If a
`ℂ`-linear map `Φ` on the operators of a finite-dimensional complex inner product space `E`
sends every density operator to a density operator, then it fixes some density operator `ρ`:
`Φ ρ = ρ`. This is the operator-theoretic content of Nielsen & Chuang, Exercise 9.9. The proof
applies the Markov–Kakutani fixed-point theorem
(`ContinuousLinearMap.exists_isFixedPt_of_isCompact_of_convex`) to the compact convex set of
density operators, viewing the finite-dimensional linear map `Φ` as a continuous real-linear
self-map of that set. -/
theorem exists_isDensityOp_isFixedPt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (Φ : (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (hmaps : ∀ A : E →L[ℂ] E, A.IsDensityOp → (Φ A).IsDensityOp)
    {ρ₀ : E →L[ℂ] E} (hρ₀ : ρ₀.IsDensityOp) :
    ∃ ρ : E →L[ℂ] E, ρ.IsDensityOp ∧ Φ ρ = ρ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
  have : IsScalarTower ℝ ℂ (E →L[ℂ] E) := IsScalarTower.restrictScalars ℝ ℂ _
  -- View `Φ` as a continuous real-linear endomorphism of the operator space.
  set Φr : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E) :=
    (LinearMap.toContinuousLinearMap Φ).restrictScalars ℝ
  have hmapsTo : Set.MapsTo Φr {A : E →L[ℂ] E | A.IsDensityOp}
      {A : E →L[ℂ] E | A.IsDensityOp} := fun A hA => hmaps A hA
  obtain ⟨ρ, hρ, hfix⟩ :=
    exists_isFixedPt_of_isCompact_of_convex ⟨ρ₀, hρ₀⟩ isCompact_setOf_isDensityOp
      convex_setOf_isDensityOp hmapsTo
  exact ⟨ρ, hρ, hfix⟩

end ContinuousLinearMap
