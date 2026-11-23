/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Pinching and the relative entropy: the entropy-increase identity

Fix a finite-dimensional complex inner product space `E` and a **complete family of orthogonal
projectors** `P : ι → E →L[ℂ] E` — each `P i` a star projection (`IsStarProjection`, i.e. a
self-adjoint idempotent), the `P i` mutually orthogonal (`P i * P j = 0` for `i ≠ j`), and summing
to the identity (`∑ i, P i = 1`). Applying the operator-sum (Kraus) map `krausSumₗ P` to a density
operator `ρ` gives the **pinching** (the non-selective projective-measurement channel)

`ρ' := krausSumₗ P ρ = Σᵢ Pᵢ ρ Pᵢ`.

The main result is the **entropy-increase identity**

`D(ρ ‖ ρ') = S(ρ') − S(ρ)`:

the relative entropy of the pre- to the post-measurement state equals the entropy gained. This is
the operator core of Nielsen & Chuang's proof of Theorem 11.9 (projective measurements increase
entropy): combined with the non-negativity of `D` it gives `S(ρ') ≥ S(ρ)`, and with the equality
condition of Klein's inequality it gives the case of equality.

The heart is the **trace identity** `tr((cfc log ρ') ρ) = tr((cfc log ρ') ρ')`: each `Pᵢ` commutes
with `ρ'` (orthogonality + idempotence), hence with `log ρ'`; and since `Σᵢ Pᵢ = 1`, cyclicity of
the trace lets one replace `ρ'` by `ρ` inside `tr((log ρ') ·)` without changing the value. The
identity is fully general — no faithfulness hypothesis on `ρ` or `ρ'` is needed.

## Main results

* `ContinuousLinearMap.krausSumₗ_eq_sum_conj_of_isStarProjection` — `krausSumₗ P ρ = Σᵢ Pᵢ ρ Pᵢ`
  for self-adjoint `Pᵢ`.
* `ContinuousLinearMap.commute_krausSumₗ_of_isStarProjection` — each `Pᵢ` commutes with the pinched
  operator `Σⱼ Pⱼ ρ Pⱼ`.
* `ContinuousLinearMap.isDensityOp_krausSumₗ_of_isStarProjection` — the pinching of a density
  operator is again a density operator.
* `ContinuousLinearMap.trace_comp_krausSumₗ_of_commute` — the trace identity
  `tr(L (Σᵢ Pᵢ ρ Pᵢ)) = tr(L ρ)` for any operator `L` commuting with every `Pᵢ`.
* `ContinuousLinearMap.quantumRelativeEntropy_krausSumₗ_eq_vonNeumannEntropy_sub` —
  **`D(ρ ‖ Σᵢ Pᵢ ρ Pᵢ) = S(Σᵢ Pᵢ ρ Pᵢ) − S(ρ)`.**
* `ContinuousLinearMap.vonNeumannEntropy_le_krausSumₗ` — **projective measurements never decrease
  entropy** (the operator form of Nielsen & Chuang Theorem 11.9, eq. (11.66)):
  `S(ρ) ≤ S(Σᵢ Pᵢ ρ Pᵢ)`, from the entropy-increase identity and non-negativity of `D`.
* `ContinuousLinearMap.vonNeumannEntropy_krausSumₗ_eq_iff` — its **equality condition**:
  `S(Σᵢ Pᵢ ρ Pᵢ) = S(ρ) ↔ Σᵢ Pᵢ ρ Pᵢ = ρ`, from the equality case of the (non-faithful) Klein
  inequality.
-/

@[expose] public section

open Module

namespace ContinuousLinearMap

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  {P : ι → E →L[ℂ] E} {ρ : E →L[ℂ] E}

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- Cyclicity of the trace on the operator algebra: `tr(A B) = tr(B A)`. -/
theorem trace_toLinearMap_mul_comm (A B : E →L[ℂ] E) :
    LinearMap.trace ℂ E (A * B : E →L[ℂ] E).toLinearMap =
      LinearMap.trace ℂ E (B * A : E →L[ℂ] E).toLinearMap := by
  rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
      LinearMap.trace_mul_comm]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- The composition `L ∘ₗ X` of the underlying linear maps is the underlying linear map of the
operator product `L * X`. -/
theorem coe_comp_toLinearMap (L X : E →L[ℂ] E) :
    L.toLinearMap ∘ₗ X.toLinearMap = (L * X : E →L[ℂ] E).toLinearMap :=
  (ContinuousLinearMap.toLinearMap_mul L X).symm

omit [FiniteDimensional ℂ E] in
/-- For a family of self-adjoint operators `Pᵢ`, the operator-sum map unfolds to the symmetric
conjugation sum `krausSumₗ P ρ = Σᵢ Pᵢ ρ Pᵢ` (each `Pᵢ† = Pᵢ`). -/
theorem krausSumₗ_eq_sum_conj_of_isStarProjection (hP : ∀ i, IsStarProjection (P i)) (ρ) :
    krausSumₗ P ρ = ∑ i, P i * ρ * P i := by
  rw [krausSumₗ_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hP i).isSelfAdjoint.adjoint_eq]
  rfl

omit [FiniteDimensional ℂ E] in
/-- **Each projector commutes with the pinched operator.** For a family of orthogonal star
projectors `Pᵢ`, every `Pᵢ` commutes with `Σⱼ Pⱼ ρ Pⱼ`: both `Pᵢ (Σⱼ Pⱼ ρ Pⱼ)` and
`(Σⱼ Pⱼ ρ Pⱼ) Pᵢ` collapse to `Pᵢ ρ Pᵢ` by orthogonality and idempotence. -/
theorem commute_krausSumₗ_of_isStarProjection (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (ρ) (i : ι) :
    Commute (P i) (∑ j, P j * ρ * P j) := by
  change P i * (∑ j, P j * ρ * P j) = (∑ j, P j * ρ * P j) * P i
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases eq_or_ne i j with rfl | h
  · rw [← mul_assoc, ← mul_assoc, (hP i).isIdempotentElem, mul_assoc (P i * ρ),
      (hP i).isIdempotentElem]
  · rw [← mul_assoc, ← mul_assoc, horth i j h, zero_mul, zero_mul, mul_assoc (P j * ρ),
      horth j i h.symm, mul_zero]

/-- **The pinching of a density operator is a density operator.** Positivity is
`krausSumₗ_isPositive`; trace one follows from the operator-sum trace identity `tr(Σᵢ Pᵢ ρ Pᵢ) =
tr((Σᵢ Pᵢ) ρ) = tr ρ = 1` (completeness). -/
theorem isDensityOp_krausSumₗ_of_isStarProjection (hP : ∀ i, IsStarProjection (P i))
    (hsum : ∑ i, P i = 1) (hρ : ρ.IsDensityOp) : (krausSumₗ P ρ).IsDensityOp := by
  refine ⟨krausSumₗ_isPositive P hρ.isPositive, ?_⟩
  rw [trace_krausSumₗ]
  have hone : (∑ i, adjoint (P i) ∘L P i) = 1 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hP i).isSelfAdjoint.adjoint_eq, ← ContinuousLinearMap.mul_def, (hP i).isIdempotentElem]
  rw [hone, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  exact hρ.2

omit [FiniteDimensional ℂ E] in
/-- **The pinching trace identity.** For a complete family of orthogonal star projectors `Pᵢ` and
any operator `L` commuting with every `Pᵢ`, `tr(L (Σᵢ Pᵢ ρ Pᵢ)) = tr(L ρ)`. Per summand, cyclicity
of the trace moves the trailing `Pᵢ` to the front, where it merges with `L Pᵢ` into `L Pᵢ`
(commutation + idempotence); summing over `i` and using `Σᵢ Pᵢ = 1` collapses the family. -/
theorem trace_comp_krausSumₗ_of_commute (hP : ∀ i, IsStarProjection (P i)) (hsum : ∑ i, P i = 1)
    {L : E →L[ℂ] E} (hL : ∀ i, Commute (P i) L) :
    LinearMap.trace ℂ E (L.toLinearMap ∘ₗ (krausSumₗ P ρ).toLinearMap) =
      LinearMap.trace ℂ E (L.toLinearMap ∘ₗ ρ.toLinearMap) := by
  rw [krausSumₗ_eq_sum_conj_of_isStarProjection hP, coe_comp_toLinearMap, coe_comp_toLinearMap,
    Finset.mul_sum, ContinuousLinearMap.toLinearMap_sum, map_sum]
  have hterm : ∀ i, LinearMap.trace ℂ E (L * (P i * ρ * P i) : E →L[ℂ] E).toLinearMap =
      LinearMap.trace ℂ E (L * P i * ρ : E →L[ℂ] E).toLinearMap := by
    intro i
    have hEq : P i * (L * P i * ρ) = L * P i * ρ := by
      rw [← mul_assoc, ← mul_assoc, (hL i).eq, mul_assoc L, (hP i).isIdempotentElem]
    rw [show L * (P i * ρ * P i) = (L * P i * ρ) * P i by noncomm_ring,
      trace_toLinearMap_mul_comm (L * P i * ρ) (P i), hEq]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← map_sum, ← ContinuousLinearMap.toLinearMap_sum,
    ← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one]

/-- **The entropy-increase identity** (operator form of the identity behind Nielsen & Chuang
Theorem 11.9). For a complete family of orthogonal star projectors `Pᵢ` and a density operator `ρ`,
the relative entropy of `ρ` to its pinching `Σᵢ Pᵢ ρ Pᵢ` equals the entropy gained:
`D(ρ ‖ Σᵢ Pᵢ ρ Pᵢ) = S(Σᵢ Pᵢ ρ Pᵢ) − S(ρ)`. No faithfulness is required: it rests only on the
trace identity `tr((log ρ') ρ) = tr((log ρ') ρ') = −S(ρ')` and the definition
`D(ρ ‖ σ) = −S(ρ) − re tr((log σ) ρ)`. -/
theorem quantumRelativeEntropy_krausSumₗ_eq_vonNeumannEntropy_sub (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (hsum : ∑ i, P i = 1) (hρ : ρ.IsDensityOp) :
    ρ.quantumRelativeEntropy (krausSumₗ P ρ) =
      (krausSumₗ P ρ).vonNeumannEntropy - ρ.vonNeumannEntropy := by
  have hρ'D : (krausSumₗ P ρ).IsDensityOp := isDensityOp_krausSumₗ_of_isStarProjection hP hsum hρ
  have hcomm : ∀ i, Commute (P i) (cfc Real.log (krausSumₗ P ρ)) := by
    intro i
    have hc : Commute (krausSumₗ P ρ) (P i) := by
      rw [krausSumₗ_eq_sum_conj_of_isStarProjection hP]
      exact (commute_krausSumₗ_of_isStarProjection hP horth ρ i).symm
    exact (hc.cfc_real Real.log).symm
  have htr := (trace_comp_krausSumₗ_of_commute (ρ := ρ) hP hsum hcomm).symm
  have hself : (krausSumₗ P ρ).quantumRelativeEntropy (krausSumₗ P ρ) = 0 :=
    quantumRelativeEntropy_self _
  rw [hρ'D.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub] at hself
  rw [hρ.quantumRelativeEntropy_eq_neg_vonNeumannEntropy_sub, htr]
  linarith [hself]

omit [FiniteDimensional ℂ E] in
/-- **The pinching does not enlarge the support:** `supp ρ ⊆ supp (Σᵢ Pᵢ ρ Pᵢ)`. For a complete
family of orthogonal star projectors `Pᵢ` and a positive operator `ρ`, `ker (Σᵢ Pᵢ ρ Pᵢ) ≤ ker ρ`,
i.e. `HasSupportLE ρ (krausSumₗ P ρ)`.

If `(krausSumₗ P ρ) x = 0`, then the quadratic form of the pinching at `x` splits over the
projectors, `re ⟪x, (krausSumₗ P ρ) x⟫ = Σᵢ re ⟪Pᵢ x, ρ (Pᵢ x)⟫` (each `Pᵢ` self-adjoint), and
equals `0`. Every summand is `≥ 0` by positivity of `ρ`, so each `re ⟪Pᵢ x, ρ (Pᵢ x)⟫ = 0`, hence
`ρ (Pᵢ x) = 0` (`apply_eq_zero_of_re_inner_self_eq_zero`); summing over `i` with `Σᵢ Pᵢ = 1` gives
`ρ x = Σᵢ ρ (Pᵢ x) = 0`. This is the exact support hypothesis under which the non-faithful Klein
inequality applies to `D(ρ ‖ Σᵢ Pᵢ ρ Pᵢ)` even though the pinching is generally rank-deficient. -/
theorem hasSupportLE_krausSumₗ_of_isStarProjection (hP : ∀ i, IsStarProjection (P i))
    (hsum : ∑ i, P i = 1) (hρ : ρ.IsPositive) : HasSupportLE ρ (krausSumₗ P ρ) := by
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
  -- The pinching's quadratic form at `x` splits as a sum of `ρ`-quadratic forms.
  have hsplit : RCLike.re (inner ℂ x ((krausSumₗ P ρ) x)) =
      ∑ i, RCLike.re (inner ℂ (P i x) (ρ (P i x))) := by
    rw [krausSumₗ_eq_sum_conj_of_isStarProjection hP, _root_.sum_apply, inner_sum,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      ← ContinuousLinearMap.adjoint_inner_left (P i) (ρ (P i x)) x, (hP i).isSelfAdjoint.adjoint_eq]
  rw [hx, inner_zero_right, map_zero] at hsplit
  -- Each nonnegative summand vanishes, so `ρ` kills every `Pᵢ x`.
  have hterm : ∀ i, RCLike.re (inner ℂ (P i x) (ρ (P i x))) = 0 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ RCLike.re (inner ℂ (P i x) (ρ (P i x))) := fun i _ => by
      have h := hρ.reApplyInnerSelf_nonneg (P i x)
      rwa [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_re_symm] at h
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsplit.symm i (Finset.mem_univ i)
  have hPx : ∀ i, ρ (P i x) = 0 := fun i =>
    apply_eq_zero_of_re_inner_self_eq_zero (nonneg_iff_isPositive.mpr hρ) (hterm i)
  -- `ρ x = ρ ((Σᵢ Pᵢ) x) = Σᵢ ρ (Pᵢ x) = 0`.
  have hxsum : ∑ i, P i x = x := by
    rw [← _root_.sum_apply, hsum, one_apply_eq_self]
  rw [← hxsum, map_sum, Finset.sum_eq_zero fun i _ => hPx i]

/-- **Projective measurements never decrease entropy** (the operator form of Nielsen & Chuang
Theorem 11.9, eq. (11.66)). For a complete family of orthogonal star projectors `Pᵢ` and a density
operator `ρ`, the pinching `Σᵢ Pᵢ ρ Pᵢ` has entropy at least that of `ρ`:

  `S(ρ) ≤ S(Σᵢ Pᵢ ρ Pᵢ)`.

Immediate from the entropy-increase identity
`D(ρ ‖ Σᵢ Pᵢ ρ Pᵢ) = S(Σᵢ Pᵢ ρ Pᵢ) − S(ρ)` together with non-negativity of the relative entropy
under the support condition `ker (Σᵢ Pᵢ ρ Pᵢ) ≤ ker ρ`, which the pinching always satisfies
(`hasSupportLE_krausSumₗ_of_isStarProjection`). No faithfulness hypothesis on `ρ`. -/
theorem vonNeumannEntropy_le_krausSumₗ (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (hsum : ∑ i, P i = 1) (hρ : ρ.IsDensityOp) :
    ρ.vonNeumannEntropy ≤ (krausSumₗ P ρ).vonNeumannEntropy := by
  have hρ'D : (krausSumₗ P ρ).IsDensityOp := isDensityOp_krausSumₗ_of_isStarProjection hP hsum hρ
  have hsupp : HasSupportLE ρ (krausSumₗ P ρ) :=
    hasSupportLE_krausSumₗ_of_isStarProjection hP hsum hρ.isPositive
  have hident := quantumRelativeEntropy_krausSumₗ_eq_vonNeumannEntropy_sub hP horth hsum hρ
  have hnonneg := hρ.quantumRelativeEntropy_nonneg_of_hasSupportLE hρ'D hsupp
  rw [hident] at hnonneg
  linarith

/-- **Equality condition for the entropy increase under pinching** (the operator form of the
equality case of Nielsen & Chuang Theorem 11.9). For a complete family of orthogonal star
projectors `Pᵢ` and a density operator `ρ`, the pinching `Σᵢ Pᵢ ρ Pᵢ` has the *same* entropy as `ρ`
if and only if the pinching leaves `ρ` unchanged:

  `S(Σᵢ Pᵢ ρ Pᵢ) = S(ρ) ↔ Σᵢ Pᵢ ρ Pᵢ = ρ`.

By the entropy-increase identity `D(ρ ‖ Σᵢ Pᵢ ρ Pᵢ) = S(Σᵢ Pᵢ ρ Pᵢ) − S(ρ)`, equality of the
entropies is `D(ρ ‖ Σᵢ Pᵢ ρ Pᵢ) = 0`, which by the equality case of the (non-faithful, support-
conditioned) Klein inequality `quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE` holds exactly
when `ρ = Σᵢ Pᵢ ρ Pᵢ`. No faithfulness hypothesis on `ρ`. This is the operator-level step behind the
equality condition of the entropy-of-a-mixture bound (N&C Theorem 11.10): applied to the diagonal
pinching of the Gram operator of an ensemble, it reads off orthogonality of the ensemble states. -/
theorem vonNeumannEntropy_krausSumₗ_eq_iff (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (hsum : ∑ i, P i = 1) (hρ : ρ.IsDensityOp) :
    (krausSumₗ P ρ).vonNeumannEntropy = ρ.vonNeumannEntropy ↔ krausSumₗ P ρ = ρ := by
  have hρ'D : (krausSumₗ P ρ).IsDensityOp := isDensityOp_krausSumₗ_of_isStarProjection hP hsum hρ
  have hsupp : HasSupportLE ρ (krausSumₗ P ρ) :=
    hasSupportLE_krausSumₗ_of_isStarProjection hP hsum hρ.isPositive
  have hident := quantumRelativeEntropy_krausSumₗ_eq_vonNeumannEntropy_sub hP horth hsum hρ
  have hklein := hρ.quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE hρ'D hsupp
  constructor
  · intro heq
    have hD0 : ρ.quantumRelativeEntropy (krausSumₗ P ρ) = 0 := by rw [hident]; linarith
    exact (hklein.mp hD0).symm
  · intro heq
    have hD0 := hklein.mpr heq.symm
    rw [hident] at hD0
    linarith

end ContinuousLinearMap
