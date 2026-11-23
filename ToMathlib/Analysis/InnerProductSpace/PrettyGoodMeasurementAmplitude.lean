/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.GramSquareRoot
public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import ToMathlib.Analysis.InnerProductSpace.HSPairing

/-!
# The Barnum–Knill amplitude lower bound for pretty-good (square-root) discrimination

For positive operators `ρ ≤ S` on a finite-dimensional complex inner product space, with
`S⁻¹ᐟ² = S.genInvSqrt` the generalized inverse square root, the **Barnum–Knill success amplitude**
`re tr(√ρ · S⁻¹ᐟ² · ρ)` — the physical trace controlling the pretty-good discrimination error of `ρ`
against a family whose total operator is `S` — is bounded below by

`re tr(√ρ · S⁻¹ᐟ² · ρ)  ≥  2·re tr(ρ) − re tr(√S · √ρ)`.

Its content: as the reduced states become perfectly distinguishable (`S = ρ` on the support of `ρ`)
the amplitude tends to `tr ρ`, so this bounds the discrimination deficit `1 − re tr(√ρ · S⁻¹ᐟ² · ρ)`
by the *affinity-to-total* deficit `re tr(√S · √ρ) − re tr(ρ)`.  Combined with the pretty-good
per-state error reduction (`1 − p ≤ 2(1 − re tr(√ρ · S⁻¹ᐟ² · ρ))`) it reduces the mixed-state
discrimination error to a single closed-form trace against `√S`.

## Proof

The bound is a single Hilbert–Schmidt nonnegativity `0 ≤ tr(M⋆·M)` for the operator
`M = S⁻¹ᐟ⁴·ρ³ᐟ⁴ − S¹ᐟ⁴·ρ¹ᐟ⁴` (all fourth roots realised through `cfc`).  Expanding `M⋆·M` and
tracing:

* the `S⁻¹ᐟ⁴·ρ³ᐟ⁴` diagonal gives `tr(S⁻¹ᐟ² · ρ³ᐟ²) = re tr(√ρ · S⁻¹ᐟ² · ρ)` (the amplitude),
* the `S¹ᐟ⁴·ρ¹ᐟ⁴` diagonal gives `tr(√S · √ρ)`,
* each cross term is `tr(Π_S · ρ)` where `Π_S = S⁻¹ᐟ⁴·S¹ᐟ⁴` is the support projection of `S`; since
  `ρ ≤ S` its range lies in that of `S`, so `tr(Π_S · ρ) = tr ρ`.

Hence `0 ≤ re tr(M⋆·M) = re tr(√ρ · S⁻¹ᐟ² · ρ) + re tr(√S · √ρ) − 2·re tr ρ`, which is the claim.

The statement involves only `cfc`, `ContinuousLinearMap.genInvSqrt`, `LinearMap.trace`, and
operator products. It uses the generalized-inverse-square-root development
(`GeneralizedInverseSqrt` / `GramSquareRoot`) and complements the frame reduction
(`PrettyGoodMeasurementError`).

## References

* [Barnum and Knill, *Reversing quantum dynamics with near-optimal quantum and classical
  fidelity*][barnum_knill_2002]; [Nielsen and Chuang][nielsen_chuang_2010], Problem 5.5.
-/

@[expose] public section

open scoped InnerProductSpace

open ContinuousLinearMap

noncomputable section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

set_option maxHeartbeats 400000 in
-- A single long `cfc`/trace computation over four fourth roots of two operators; the ~20 chained
-- functional-calculus rewrites exceed the default heartbeat budget.
/-- **The Barnum–Knill success-amplitude lower bound** for the pretty-good (square-root)
discrimination measurement.  For positive operators `ρ ≤ S` on a finite-dimensional complex inner
product space, the success amplitude `re tr(√ρ · S⁻¹ᐟ² · ρ)` (`S⁻¹ᐟ² = S.genInvSqrt`) satisfies

`2·re tr(ρ) − re tr(√S · √ρ)  ≤  re tr(√ρ · S⁻¹ᐟ² · ρ)`.

This reduces the pretty-good discrimination deficit `1 − re tr(√ρ · S⁻¹ᐟ² · ρ)` to the affinity
deficit `re tr(√S · √ρ) − re tr(ρ)`.  The proof is the Hilbert–Schmidt nonnegativity
`0 ≤ tr(M⋆·M)` for `M = S⁻¹ᐟ⁴·ρ³ᐟ⁴ − S¹ᐟ⁴·ρ¹ᐟ⁴`. -/
theorem two_mul_re_trace_sub_re_trace_cfc_sqrt_mul_le_re_trace_genInvSqrt
    {ρ S : E →L[ℂ] E} (hρ : 0 ≤ ρ) (hρS : ρ ≤ S) :
    2 * RCLike.re (LinearMap.trace ℂ E (ρ : E →ₗ[ℂ] E))
        - RCLike.re (LinearMap.trace ℂ E
          ((cfc Real.sqrt S * cfc Real.sqrt ρ : E →L[ℂ] E) : E →ₗ[ℂ] E))
      ≤ RCLike.re (LinearMap.trace ℂ E
          ((cfc Real.sqrt ρ * S.genInvSqrt * ρ : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  have hS : 0 ≤ S := hρ.trans hρS
  have hSsa : IsSelfAdjoint S := hS.isSelfAdjoint
  have hρsa : IsSelfAdjoint ρ := hρ.isSelfAdjoint
  have hcS : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ S) := fun f => hSsa.continuousOn_spectrum f
  have hcρ : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ ρ) := fun f => hρsa.continuousOn_spectrum f
  -- Fourth roots, all realised as `cfc` of the base operator (so products fold via `cfc_mul`).
  set a : E →L[ℂ] E := cfc (fun x : ℝ => Real.sqrt (Real.sqrt x)) S with ha  -- `S¹ᐟ⁴`
  set b : E →L[ℂ] E := cfc (fun x : ℝ => (Real.sqrt (Real.sqrt x))⁻¹) S with hb  -- `S⁻¹ᐟ⁴`
  set c : E →L[ℂ] E := cfc (fun x : ℝ => Real.sqrt (Real.sqrt x)) ρ with hc  -- `ρ¹ᐟ⁴`
  set d : E →L[ℂ] E := cfc (fun x : ℝ => Real.sqrt x * Real.sqrt (Real.sqrt x)) ρ with hd  -- `ρ³ᐟ⁴`
  have hasa : IsSelfAdjoint a := by rw [ha]; exact cfc_predicate _ _
  have hbsa : IsSelfAdjoint b := by rw [hb]; exact cfc_predicate _ _
  have hcsa : IsSelfAdjoint c := by rw [hc]; exact cfc_predicate _ _
  have hdsa : IsSelfAdjoint d := by rw [hd]; exact cfc_predicate _ _
  -- Forget the `cfc` values of `a, b, c, d` (keeping only `ha …/hd …`): unfolding them during
  -- `isDefEq` is the dominant cost, and every step below rewrites through the equations instead.
  clear_value a b c d
  -- Product identities (each a `cfc_mul` fold + pointwise `cfc_congr`).
  have hbb : b * b = S.genInvSqrt := by
    rw [hb, ← cfc_mul _ _ S (hcS _) (hcS _)]
    refine cfc_congr fun x hx => ?_
    rw [← mul_inv, Real.mul_self_sqrt (Real.sqrt_nonneg x)]
  have haa : a * a = cfc Real.sqrt S := by
    rw [ha, ← cfc_mul _ _ S (hcS _) (hcS _)]
    exact cfc_congr fun x hx => Real.mul_self_sqrt (Real.sqrt_nonneg x)
  have hcc : c * c = cfc Real.sqrt ρ := by
    rw [hc, ← cfc_mul _ _ ρ (hcρ _) (hcρ _)]
    exact cfc_congr fun x hx => Real.mul_self_sqrt (Real.sqrt_nonneg x)
  have hab : a * b = b * a := by
    rw [ha, hb, ← cfc_mul _ _ S (hcS _) (hcS _), ← cfc_mul _ _ S (hcS _) (hcS _)]
    exact cfc_congr fun x _ => mul_comm _ _
  -- `ρ³ᐟ² = ρ · √ρ` as a single `cfc`; used to identify the amplitude trace.
  have hρ32 : ρ * cfc Real.sqrt ρ = cfc (fun x => x * Real.sqrt x) ρ := by
    have h : cfc (fun x => x * Real.sqrt x) ρ = cfc (fun x => x) ρ * cfc Real.sqrt ρ :=
      cfc_mul (fun x => x) Real.sqrt ρ (hcρ _) (hcρ _)
    rw [h, cfc_id' ℝ ρ]
  have hdd : d * d = cfc (fun x => x * Real.sqrt x) ρ := by
    rw [hd, ← cfc_mul _ _ ρ (hcρ _) (hcρ _)]
    refine cfc_congr fun x hx => ?_
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hρ hx
    have h4 : Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) = Real.sqrt x :=
      Real.mul_self_sqrt (Real.sqrt_nonneg x)
    have h2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    nlinarith [h4, h2, Real.sqrt_nonneg x, Real.sqrt_nonneg (Real.sqrt x)]
  have hcd : c * d = ρ := by
    have h : cfc (fun x => Real.sqrt (Real.sqrt x) * (Real.sqrt x * Real.sqrt (Real.sqrt x))) ρ
        = cfc (id : ℝ → ℝ) ρ := by
      refine cfc_congr fun x hx => ?_
      have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hρ hx
      have h4 : Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) = Real.sqrt x :=
        Real.mul_self_sqrt (Real.sqrt_nonneg x)
      have h2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
      simp only [id_eq]
      nlinarith [h4, h2, Real.sqrt_nonneg x, Real.sqrt_nonneg (Real.sqrt x)]
    rw [hc, hd, ← cfc_mul _ _ ρ (hcρ _) (hcρ _), h, cfc_id ℝ ρ]
  have hdc : d * c = ρ := by
    have hcomm : d * c = c * d := by
      rw [hc, hd, ← cfc_mul _ _ ρ (hcρ _) (hcρ _), ← cfc_mul _ _ ρ (hcρ _) (hcρ _)]
      exact cfc_congr fun x _ => mul_comm _ _
    rw [hcomm, hcd]
  -- The support projection `P = b·a = S⁻¹ᐟ⁴·S¹ᐟ⁴`.
  have hprojcfc :
      b * a = cfc (fun x => (Real.sqrt (Real.sqrt x))⁻¹ * Real.sqrt (Real.sqrt x)) S := by
    rw [hb, ha, ← cfc_mul _ _ S (hcS _) (hcS _)]
  have hprojle : b * a ≤ 1 := by
    rw [hprojcfc]
    refine cfc_le_one _ S fun x hx => ?_
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hS hx
    rcases eq_or_lt_of_le hx0 with h0 | h0
    · simp [← h0]
    · rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr h0)).ne']
  have hprojS : b * a * S = S := by
    rw [hprojcfc]
    nth_rewrite 2 [← cfc_id ℝ S]
    rw [← cfc_mul _ _ S (hcS _) (hcS _)]
    refine (cfc_congr (g := (id : ℝ → ℝ)) fun x hx => ?_).trans (cfc_id ℝ S)
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hS hx
    simp only [id_eq]
    rcases eq_or_lt_of_le hx0 with h0 | h0
    · simp [← h0]
    · rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr h0)).ne', one_mul]
  -- `re tr(P·ρ) = re tr ρ`: the range of `ρ ≤ S` lies in that of `S`.
  have hprojrho : RCLike.re (LinearMap.trace ℂ E ((b * a * ρ : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E (ρ : E →ₗ[ℂ] E)) := by
    have honemproj : (0 : E →L[ℂ] E) ≤ 1 - b * a := by rw [sub_nonneg]; exact hprojle
    have hSρ : (0 : E →L[ℂ] E) ≤ S - ρ := by rw [sub_nonneg]; exact hρS
    have hle : RCLike.re (LinearMap.trace ℂ E (((1 - b * a) * ρ : E →L[ℂ] E) : E →ₗ[ℂ] E))
        ≤ RCLike.re (LinearMap.trace ℂ E (((1 - b * a) * S : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
      have h := re_trace_mul_nonneg_of_nonneg honemproj hSρ
      rw [mul_sub, ContinuousLinearMap.toLinearMap_sub, map_sub, map_sub] at h
      linarith
    have hzero : (1 - b * a) * S = 0 := by rw [sub_mul, one_mul, hprojS, sub_self]
    rw [hzero] at hle
    simp only [ContinuousLinearMap.toLinearMap_zero, map_zero, map_zero] at hle
    have hge : 0 ≤ RCLike.re (LinearMap.trace ℂ E (((1 - b * a) * ρ : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
      re_trace_mul_nonneg_of_nonneg honemproj hρ
    have heq0 : RCLike.re (LinearMap.trace ℂ E (((1 - b * a) * ρ : E →L[ℂ] E) : E →ₗ[ℂ] E)) = 0 :=
      le_antisymm hle hge
    rw [ContinuousLinearMap.re_trace_one_sub_mul] at heq0
    linarith
  -- Assemble via `0 ≤ re tr(M⋆·M)`, `M = b·d − a·c`.
  set M : E →L[ℂ] E := b * d - a * c with hM
  have hstarM : star M = d * b - c * a := by
    rw [hM, star_sub, star_mul, star_mul, hdsa.star_eq, hbsa.star_eq, hcsa.star_eq, hasa.star_eq]
  have hnn : 0 ≤ RCLike.re (LinearMap.trace ℂ E ((star M * M : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
    have hMMnn : (0 : E →L[ℂ] E) ≤ star M * M := by
      rw [star_eq_adjoint, ContinuousLinearMap.mul_def]
      exact (ContinuousLinearMap.nonneg_iff_isPositive).mpr (isPositive_adjoint_comp_self M)
    have := re_trace_mul_nonneg_of_nonneg hMMnn (zero_le_one (α := E →L[ℂ] E))
    simpa using this
  -- Operator identity (associativity + distribution).
  have hop : star M * M
      = d * (b * b) * d - d * (b * a) * c - c * (a * b) * d + c * (a * a) * c := by
    rw [hstarM, hM]; noncomm_ring
  rw [hop, hbb, haa, hab] at hnn
  simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_sub, map_add,
      map_sub] at hnn
  -- Evaluate the four traces by cyclicity.
  have e1 : RCLike.re (LinearMap.trace ℂ E ((d * S.genInvSqrt * d : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E ((cfc Real.sqrt ρ * S.genInvSqrt * ρ : E →L[ℂ] E)
          : E →ₗ[ℂ] E)) := by
    rw [re_trace_mul_comm (d * S.genInvSqrt) d, ← mul_assoc, hdd,
      re_trace_mul_comm (cfc Real.sqrt ρ * S.genInvSqrt) ρ, ← mul_assoc, hρ32]
  have e2 : RCLike.re (LinearMap.trace ℂ E ((d * (b * a) * c : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E (ρ : E →ₗ[ℂ] E)) := by
    rw [re_trace_mul_comm (d * (b * a)) c, ← mul_assoc, hcd, re_trace_mul_comm ρ (b * a), hprojrho]
  have e3 : RCLike.re (LinearMap.trace ℂ E ((c * (b * a) * d : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E (ρ : E →ₗ[ℂ] E)) := by
    rw [re_trace_mul_comm (c * (b * a)) d, ← mul_assoc, hdc, re_trace_mul_comm ρ (b * a), hprojrho]
  have e4 : RCLike.re (LinearMap.trace ℂ E ((c * cfc Real.sqrt S * c : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E ((cfc Real.sqrt S * cfc Real.sqrt ρ : E →L[ℂ] E)
          : E →ₗ[ℂ] E)) := by
    rw [re_trace_mul_comm (c * cfc Real.sqrt S) c, ← mul_assoc, hcc,
      re_trace_mul_comm (cfc Real.sqrt ρ) (cfc Real.sqrt S)]
  rw [e1, e2, e3, e4] at hnn
  linarith

/-- **The affinity-to-total Cauchy–Schwarz bound**, summed form. For a finite family of positive
operators `A : ι → E →L[ℂ] E` with total `S₀ = ∑ⱼ A j`, the trace of `√S₀` against the sum of the
per-operator square roots `T = ∑ⱼ √(A j)` is bounded by the full pairwise-affinity double sum:

`re tr(√S₀ · ∑ⱼ √(A j)) ≤ ∑ᵢ ∑ⱼ re tr(√(A i) · √(A j))`.

This is the operator kernel of the *summed* Barnum–Knill state-discrimination error bound: summing
the per-state amplitude deficit `re tr(√S₀ · √(A i)) − re tr(A i)` over the family, the total
`√S₀`-amplitude collapses onto the pairwise-affinity double sum, and the diagonal `re tr(A i)`'s
peel off leaving the *off-diagonal* affinity sum.

The proof is Hilbert–Schmidt Cauchy–Schwarz on the pairing `⟨T, √S₀⟩_HS = tr(√S₀ · T)` (both
operators self-adjoint):

`re tr(√S₀ · T) = re⟨T, √S₀⟩_HS ≤ ‖⟨T, √S₀⟩_HS‖ ≤ √(re‖T‖²_HS)·√(re‖√S₀‖²_HS)
  = √(re tr(T·T))·√(re tr S₀) ≤ re tr(T·T)`,

the last step using `re tr S₀ ≤ re tr(T·T)` (their difference is `∑_{i≠j} re tr(√Aᵢ·√Aⱼ) ≥ 0`, a
sum of traces of products of positive operators), and `re tr(T·T) = ∑ᵢⱼ re tr(√Aᵢ·√Aⱼ)`.

**Only the trace form holds**: the corresponding *operator* subadditivity `√S₀ ≤ ∑ⱼ √(A j)` is
false in general (the anticommutators `√Aᵢ√Aⱼ + √Aⱼ√Aᵢ` need not be positive), and even the
general weighted trace bound `tr(√S₀ · C) ≤ ∑ⱼ tr(√(A j) · C)` fails for an arbitrary positive
weight `C`; the Cauchy–Schwarz argument above is special to pairing against `√S₀` (equivalently
against `T`), which is exactly the summed pretty-good discrimination setting. -/
theorem re_trace_cfc_sqrt_sum_mul_sum_cfc_sqrt_le
    {ι : Type*} [Fintype ι] (A : ι → E →L[ℂ] E) (hA : ∀ i, 0 ≤ A i) :
    RCLike.re (LinearMap.trace ℂ E
        ((cfc Real.sqrt (∑ j, A j) * ∑ j, cfc Real.sqrt (A j) : E →L[ℂ] E) : E →ₗ[ℂ] E))
      ≤ ∑ i, ∑ j, RCLike.re (LinearMap.trace ℂ E
          ((cfc Real.sqrt (A i) * cfc Real.sqrt (A j) : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  classical
  set T : E →L[ℂ] E := ∑ j, cfc Real.sqrt (A j) with hTdef
  have hS₀nn : 0 ≤ ∑ j, A j := Finset.sum_nonneg fun j _ => hA j
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun j _ => cfc_real_sqrt_nonneg (A j)
  have hTsa : IsSelfAdjoint T :=
    ((ContinuousLinearMap.nonneg_iff_isPositive (f := T)).mp hTnn).isSelfAdjoint
  have hRootsa : IsSelfAdjoint (cfc Real.sqrt (∑ j, A j)) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp (cfc_real_sqrt_nonneg _)).isSelfAdjoint
  -- The RHS double sum is `re tr(T · T)`.
  have hexpand : (T * T : E →L[ℂ] E) = ∑ i, ∑ j, cfc Real.sqrt (A i) * cfc Real.sqrt (A j) := by
    rw [hTdef, Finset.sum_mul_sum]
  have hTT_sum : RCLike.re (LinearMap.trace ℂ E ((T * T : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = ∑ i, ∑ j, RCLike.re (LinearMap.trace ℂ E
          ((cfc Real.sqrt (A i) * cfc Real.sqrt (A j) : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
    rw [hexpand, ContinuousLinearMap.toLinearMap_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.toLinearMap_sum, map_sum, map_sum]
  -- `re tr(A i) = re tr(√Aᵢ · √Aᵢ)`, the diagonal terms.
  have hAdiag : ∀ i, RCLike.re (LinearMap.trace ℂ E ((A i : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = RCLike.re (LinearMap.trace ℂ E
          ((cfc Real.sqrt (A i) * cfc Real.sqrt (A i) : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
    fun i => by rw [cfc_real_sqrt_mul_self_of_nonneg (hA i)]
  -- `re tr S₀ ≤ re tr(T · T)`: the difference is a sum of nonnegative off-diagonal affinities.
  have hle : RCLike.re (LinearMap.trace ℂ E ((∑ j, A j : E →L[ℂ] E) : E →ₗ[ℂ] E))
      ≤ RCLike.re (LinearMap.trace ℂ E ((T * T : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
    rw [hTT_sum, ContinuousLinearMap.toLinearMap_sum, map_sum, map_sum,
      Finset.sum_congr rfl fun i _ => hAdiag i]
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.single_le_sum
      (f := fun j => RCLike.re (LinearMap.trace ℂ E
        ((cfc Real.sqrt (A i) * cfc Real.sqrt (A j) : E →L[ℂ] E) : E →ₗ[ℂ] E)))
      (fun j _ => re_trace_mul_nonneg_of_nonneg
        (cfc_real_sqrt_nonneg (A i)) (cfc_real_sqrt_nonneg (A j)))
      (Finset.mem_univ i)
  -- Hilbert–Schmidt self-pairings: `re‖√S₀‖²_HS = re tr S₀`, `re‖T‖²_HS = re tr(T·T)`.
  have hselfRoot : RCLike.re ((cfc Real.sqrt (∑ j, A j)).hsPairing (cfc Real.sqrt (∑ j, A j)))
      = RCLike.re (LinearMap.trace ℂ E ((∑ j, A j : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
    rw [ContinuousLinearMap.re_hsPairing_self_eq_re_trace_sq_of_isSelfAdjoint hRootsa,
      cfc_real_sqrt_mul_self_of_nonneg hS₀nn]
  have hselfT : RCLike.re (T.hsPairing T)
      = RCLike.re (LinearMap.trace ℂ E ((T * T : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
    ContinuousLinearMap.re_hsPairing_self_eq_re_trace_sq_of_isSelfAdjoint hTsa
  -- `re tr(√S₀ · T) = re⟨T, √S₀⟩_HS` (the adjoint of `√S₀` is itself).
  have hpair : RCLike.re (LinearMap.trace ℂ E
        ((cfc Real.sqrt (∑ j, A j) * T : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = RCLike.re (T.hsPairing (cfc Real.sqrt (∑ j, A j))) := by
    rw [ContinuousLinearMap.hsPairing_eq, hRootsa.adjoint_eq, ContinuousLinearMap.mul_def]
  -- Nonnegativity of the two self-pairings, for the Cauchy–Schwarz arithmetic.
  have hbnn : 0 ≤ RCLike.re (LinearMap.trace ℂ E ((T * T : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
    rw [← hselfT]; exact ContinuousLinearMap.re_hsPairing_self_nonneg T
  have hCS := ContinuousLinearMap.norm_hsPairing_sq_le T (cfc Real.sqrt (∑ j, A j))
  rw [hselfT, hselfRoot] at hCS
  rw [← hTT_sum]
  set b : ℝ := RCLike.re (LinearMap.trace ℂ E ((T * T : E →L[ℂ] E) : E →ₗ[ℂ] E)) with hbdef
  set a : ℝ := RCLike.re (LinearMap.trace ℂ E ((∑ j, A j : E →L[ℂ] E) : E →ₗ[ℂ] E)) with hadef
  calc RCLike.re (LinearMap.trace ℂ E
          ((cfc Real.sqrt (∑ j, A j) * T : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = RCLike.re (T.hsPairing (cfc Real.sqrt (∑ j, A j))) := hpair
    _ ≤ ‖T.hsPairing (cfc Real.sqrt (∑ j, A j))‖ := RCLike.re_le_norm _
    _ ≤ Real.sqrt (b * a) := by
        rw [← Real.sqrt_sq (norm_nonneg (T.hsPairing (cfc Real.sqrt (∑ j, A j))))]
        exact Real.sqrt_le_sqrt hCS
    _ = Real.sqrt b * Real.sqrt a := Real.sqrt_mul hbnn a
    _ ≤ Real.sqrt b * Real.sqrt b :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg b)
    _ = b := Real.mul_self_sqrt hbnn

/-- **The generalized-inverse-square-root support projection fixes any positive operator it
dominates.**  For positive operators `ρ ≤ A` on a finite-dimensional complex inner product space,
the support projection `Π_A = A⁻¹ᐟ² · A · A⁻¹ᐟ²` (`A⁻¹ᐟ² = A.genInvSqrt`) acts as the identity on
`ρ`:

`ρ · (A⁻¹ᐟ² · A · A⁻¹ᐟ²) = ρ`.

`Π_A` is the orthogonal projection onto the range of `A`; since `ρ ≤ A` its range lies in that of
`A`, so `Π_A` fixes `ρ`.  This is the *equality* refining the sub-identity bound
`genInvSqrt_mul_self_mul_genInvSqrt_le_one` (`Π_A ≤ 1`): it is the exact statement that the
pretty-good (square-root) measurement is *complete* on the states of its own family (`ρ ≤ S₀`), so
the inconclusive outcome carries no weight and the identification error decomposes exactly into the
off-diagonal confusion probabilities.

The proof needs no explicit range/kernel projections.  `A · Π_A = A` is the `star`-image of the
companion support-projection lemma `genInvSqrt_mul_self_mul_genInvSqrt_mul_self` (`Π_A · A = A`),
using that `A` and `Π_A` are self-adjoint.  Writing `Q = 1 − Π_A`, this gives `A·Q = 0`, hence
`Q·A = 0` (adjoints), so the conjugate `Q·A·Q = 0`; sandwiching `0 ≤ ρ ≤ A`
(`IsSelfAdjoint.conjugate_nonneg` / `conjugate_le_conjugate`) forces `Q·ρ·Q = 0`.  With
`√ρ = cfc √ ρ` (`√ρ·√ρ = ρ`) that is `star(√ρ·Q)·(√ρ·Q) = 0`, so `√ρ·Q = 0`
(`CStarRing.star_mul_self_eq_zero_iff`) and therefore `ρ·Q = √ρ·(√ρ·Q) = 0`, i.e. `ρ·Π_A = ρ`. -/
theorem mul_genInvSqrt_mul_self_mul_genInvSqrt_of_le {A ρ : E →L[ℂ] E}
    (hρ : 0 ≤ ρ) (hρA : ρ ≤ A) :
    ρ * (A.genInvSqrt * A * A.genInvSqrt) = ρ := by
  have hA : 0 ≤ A := hρ.trans hρA
  have hAsa : IsSelfAdjoint A := hA.isSelfAdjoint
  set P : E →L[ℂ] E := A.genInvSqrt * A * A.genInvSqrt with hPdef
  have hPnn : 0 ≤ P := IsSelfAdjoint.conjugate_nonneg hA (isSelfAdjoint_genInvSqrt hA)
  have hPsa : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg hPnn
  -- `A · Π_A = A`: the `star`-image of the existing support-projection lemma `Π_A · A = A`
  -- (`genInvSqrt_mul_self_mul_genInvSqrt_mul_self`), using `A` and `Π_A` self-adjoint.
  have hAP : A * P = A := by
    have h := congrArg star (genInvSqrt_mul_self_mul_genInvSqrt_mul_self hA)
    rw [← hPdef] at h
    rwa [star_mul, hAsa.star_eq, hPsa.star_eq] at h
  set Q : E →L[ℂ] E := 1 - P with hQdef
  have hQsa : IsSelfAdjoint Q := by
    change star Q = Q
    rw [hQdef, star_sub, star_one, hPsa.star_eq]
  -- `A·Q = 0`, hence `Q·A = 0` (adjoints), hence the conjugate `Q·A·Q = 0`.
  have hAQ : A * Q = 0 := by rw [hQdef, mul_sub, mul_one, hAP, sub_self]
  have hQA : Q * A = 0 := by
    have h := congrArg star hAQ
    rwa [star_mul, star_zero, hQsa.star_eq, hAsa.star_eq] at h
  have hQAQ : Q * A * Q = 0 := by rw [hQA, zero_mul]
  -- Sandwiching `0 ≤ ρ ≤ A` forces `Q·ρ·Q = 0`.
  have hle : Q * ρ * Q ≤ Q * A * Q := IsSelfAdjoint.conjugate_le_conjugate hρA hQsa
  have hQρQ : Q * ρ * Q = 0 :=
    le_antisymm (hQAQ ▸ hle) (IsSelfAdjoint.conjugate_nonneg hρ hQsa)
  -- `√ρ·Q = 0` (`star (√ρ Q) · (√ρ Q) = Q·ρ·Q = 0`), hence `ρ·Q = 0`, i.e. `ρ·Π_A = ρ`.
  set r : E →L[ℂ] E := cfc Real.sqrt ρ with hr
  have hrsa : IsSelfAdjoint r := by rw [hr]; exact cfc_predicate _ _
  have hsqrt : r * r = ρ := cfc_real_sqrt_mul_self_of_nonneg hρ
  have hstar : star (r * Q) * (r * Q) = 0 := by
    rw [star_mul, hrsa.star_eq, hQsa.star_eq]
    simp only [mul_assoc]
    rw [← mul_assoc r r Q, hsqrt, ← mul_assoc]
    exact hQρQ
  have hrQ : r * Q = 0 := star_mul_self_eq_zero.mp hstar
  have hρQ : ρ * Q = 0 := by rw [← hsqrt, mul_assoc, hrQ, mul_zero]
  rw [hQdef, mul_sub, mul_one] at hρQ
  exact (sub_eq_zero.mp hρQ).symm

end ContinuousLinearMap
