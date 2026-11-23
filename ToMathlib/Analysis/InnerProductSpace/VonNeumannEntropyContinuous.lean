/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy
public import ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality
public import ToMathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Continuity of the von Neumann entropy

The von Neumann entropy `ContinuousLinearMap.vonNeumannEntropy` is defined eigenvalue-wise
(`Real.entropy` of the spectrum), and the individual eigenvalues of a Hermitian operator do *not*
depend continuously on the operator (they can cross and permute). Nonetheless the entropy — a
symmetric function of the spectrum — *is* continuous, because it is a spectral trace:
`S(ρ) = re tr(negMulLog(ρ))` with `negMulLog x = -x log x` a *globally* continuous function
(`Real.continuous_negMulLog`; the removable singularity `0 · log 0 = 0` is exactly Mathlib's
junk-value convention). Continuity then follows from continuity of the continuous functional
calculus in the operator argument (`ContinuousOn.cfc'`) and continuity of the trace
(`ContinuousLinearMap.continuous_trace`).

## Main results

- `ContinuousLinearMap.vonNeumannEntropy_eq_re_trace_cfc_negMulLog`: the trace formula
  `S(T) = re tr(cfc negMulLog T)` for a self-adjoint operator.
- `ContinuousLinearMap.continuousOn_vonNeumannEntropy_of_spectrum_subset_Icc`: continuity of the
  entropy on the set of self-adjoint operators whose real spectrum lies in `[0, 1]`.
- `ContinuousLinearMap.IsDensityOp.continuousOn_vonNeumannEntropy`: continuity on the set of
  density operators.
- `ContinuousLinearMap.tendsto_vonNeumannEntropy_regularise`: continuity of the entropy along a
  density-operator regularisation `t ↦ (1 - t) • A + t • B`, giving `S → S(A)` as `t → 0⁺` — the
  generic limiting step for extending a strictly-positive entropy inequality to all density
  operators.

The density-operator continuity is the keystone for extending strong subadditivity (and the other
strictly-positive entropy inequalities) to *all* density operators by a
regularisation/limiting argument: a general density operator is a limit of strictly positive ones,
and the entropy inequalities, being closed conditions, pass to the limit by continuity.
-/

@[expose] public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- **Trace formula for the von Neumann entropy.** For a self-adjoint operator `T`,
`S(T) = re tr(cfc negMulLog T)`, where `negMulLog x = -x·log x`. This rewrites the eigenvalue-wise
`Real.entropy` definition as a single spectral trace of a *globally continuous* function, which is
the shape needed for continuity of the entropy. Both sides expand to `∑ᵢ negMulLog(λᵢ)` via
`IsSelfAdjoint.re_trace_cfc_eq_sum`. -/
theorem vonNeumannEntropy_eq_re_trace_cfc_negMulLog {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) :
    T.vonNeumannEntropy =
      RCLike.re (LinearMap.trace ℂ E (cfc Real.negMulLog T).toLinearMap) := by
  rw [vonNeumannEntropy_of_isSymmetric hT.isSymmetric, Real.entropy_eq,
    IsSelfAdjoint.re_trace_cfc_eq_sum hT Real.negMulLog]

/-- The real spectrum of a density operator is contained in `[0, 1]`: its eigenvalues are the
spectral values (`IsSelfAdjoint.spectrum_real_eq_range_eigenvalues`), each of which lies in
`[0, 1]`. -/
theorem IsDensityOp.spectrum_real_subset_Icc {T : E →L[ℂ] E} (h : T.IsDensityOp) :
    spectrum ℝ T ⊆ Set.Icc (0 : ℝ) 1 := by
  rw [h.isPositive.isSelfAdjoint.spectrum_real_eq_range_eigenvalues rfl]
  rintro x ⟨i, rfl⟩
  exact ⟨h.eigenvalues_nonneg rfl i, h.eigenvalues_le_one rfl i⟩

/-- **Continuity of the von Neumann entropy** on the set of self-adjoint operators whose real
spectrum lies in `[0, 1]`. Proved by rewriting `S` as the spectral trace `re tr(cfc negMulLog T)`
(`vonNeumannEntropy_eq_re_trace_cfc_negMulLog`) and composing continuity of the continuous
functional calculus (`ContinuousOn.cfc'`, with the fixed compact spectrum bound `[0, 1]`) with
continuity of the trace and of `re`. -/
theorem continuousOn_vonNeumannEntropy_of_spectrum_subset_Icc :
    ContinuousOn (fun T : E →L[ℂ] E => T.vonNeumannEntropy)
      {T | IsSelfAdjoint T ∧ spectrum ℝ T ⊆ Set.Icc (0 : ℝ) 1} := by
  have hcfc : ContinuousOn (fun T : E →L[ℂ] E => cfc Real.negMulLog T)
      {T | IsSelfAdjoint T ∧ spectrum ℝ T ⊆ Set.Icc (0 : ℝ) 1} :=
    ContinuousOn.cfc' isCompact_Icc Real.negMulLog continuousOn_id
      (fun T hT => hT.2) (fun T hT => hT.1)
  have hcont : ContinuousOn
      (fun T : E →L[ℂ] E =>
        RCLike.re (LinearMap.trace ℂ E (cfc Real.negMulLog T).toLinearMap))
      {T | IsSelfAdjoint T ∧ spectrum ℝ T ⊆ Set.Icc (0 : ℝ) 1} :=
    RCLike.continuous_re.comp_continuousOn
      (ContinuousLinearMap.continuous_trace.comp_continuousOn hcfc)
  exact hcont.congr fun T hT => vonNeumannEntropy_eq_re_trace_cfc_negMulLog hT.1

/-- **Continuity of the von Neumann entropy on density operators.** A corollary of
`continuousOn_vonNeumannEntropy_of_spectrum_subset_Icc`, since every density operator is
self-adjoint with real spectrum in `[0, 1]`. This is the form used to extend the strictly-positive
entropy inequalities to all density operators by a limiting argument. -/
theorem IsDensityOp.continuousOn_vonNeumannEntropy :
    ContinuousOn (fun T : E →L[ℂ] E => T.vonNeumannEntropy) {T | T.IsDensityOp} :=
  continuousOn_vonNeumannEntropy_of_spectrum_subset_Icc.mono fun _T hT =>
    ⟨hT.isPositive.isSelfAdjoint, hT.spectrum_real_subset_Icc⟩

/-- **Continuity of the von Neumann entropy along a density-operator regularisation.** For density
operators `A B` on a finite-dimensional space, the convex path `t ↦ (1 - t) • A + t • B` stays
inside the density operators for `t ∈ [0, 1]` (`IsDensityOp.convex_combination`), so — the entropy
being continuous there (`IsDensityOp.continuousOn_vonNeumannEntropy`) — its von Neumann entropy
converges to `S(A)` as `t → 0⁺`.

This is the generic limiting step behind extending a strictly-positive entropy inequality to *all*
density operators: regularise a general operator towards a faithful reference (e.g. the maximally
mixed `d⁻¹ • 1`), apply the inequality along `(0, 1]`, and pass the closed inequality to the
`t → 0⁺` limit. It is used both to remove faithfulness from strong subadditivity
(`vonNeumannEntropy_add_partialTrace_le_of_isDensityOp`) and to extend the second-derivative
concavity of the entropy (Nielsen & Chuang Exercise 11.22) from invertible states to all states. -/
theorem tendsto_vonNeumannEntropy_regularise (A B : E →L[ℂ] E)
    (hA : A.IsDensityOp) (hB : B.IsDensityOp) :
    Filter.Tendsto (fun t : ℝ => (((1 - t : ℝ) : ℂ) • A + ((t : ℝ) : ℂ) • B).vonNeumannEntropy)
      (nhdsWithin 0 (Set.Ioc (0 : ℝ) 1)) (nhds A.vonNeumannEntropy) := by
  have hcont : Continuous (fun t : ℝ => ((1 - (t : ℝ) : ℝ) : ℂ) • A + ((t : ℝ) : ℂ) • B) := by
    fun_prop
  have hmaps : Set.MapsTo (fun t : ℝ => (((1 - t : ℝ) : ℂ) • A + ((t : ℝ) : ℂ) • B))
      (Set.Icc (0 : ℝ) 1) {T : E →L[ℂ] E | T.IsDensityOp} := fun t ht =>
    IsDensityOp.convex_combination hA hB
      (by exact_mod_cast (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)) (by exact_mod_cast ht.1)
      (by push_cast; ring)
  have h0 := ((IsDensityOp.continuousOn_vonNeumannEntropy).comp hcont.continuousOn
    hmaps).continuousWithinAt (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) |>.mono_left
    (nhdsWithin_mono 0 Set.Ioc_subset_Icc_self)
  simpa [Function.comp_def] using h0

end ContinuousLinearMap
