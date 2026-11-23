/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CascadedMeasurement
import AxQM.Postulates.API.CompositeMeasurement
import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# AxQM — the adaptive cascade of measurements (dependent Exercise 2.57)

The **adaptive cascade** `L.adaptiveCascade M`: given a measurement `L` with outcomes `κ`
and, for *each* outcome `j : κ`, a measurement `M j` with outcomes `μ j` (the second measurement is
allowed to *depend on the first outcome*), the composite that measures `L` and then the
outcome-dependent `M j` is itself a single measurement, with outcome set the sigma type
`Σ j, μ j` and operators

  `N₍ⱼ,ₖ₎ = (M j)ₖ Lⱼ`.

This is the dependent generalization of the fixed cascade `Measurement.cascade`
(`AxQM/Postulates/API/CascadedMeasurement.lean`, Nielsen–Chuang Exercise 2.57): `cascade` uses
one fixed second measurement for every first outcome (`κ × μ`), whereas here the second
measurement — and even its outcome set — varies with `j`, so the joint outcome set is a sigma
type rather than a product.
It is exactly the "combine all of Alice's measurements into one single measurement (Exercise 2.57)"
step of Nielsen–Chuang Proposition 12.14, where the second measurement Alice performs is chosen
conditionally on the result she has already obtained.

Completeness of the composite family chains the given completeness relations exactly as for the
fixed cascade, now summing over the sigma type:
`∑₍ⱼ,ₖ₎ N₍ⱼ,ₖ₎† N₍ⱼ,ₖ₎ = ∑ⱼ Lⱼ† (∑ₖ (M j)ₖ† (M j)ₖ) Lⱼ = ∑ⱼ Lⱼ† Lⱼ = 1`, so `adaptiveCascade`
produces a genuine `Measurement (Σ j, μ j) S`.

Alongside the operator identities (`adaptiveCascade_op`, `postOp_adaptiveCascade`) this file
records the two physical-equivalence laws — the joint Born probability factorizes as
`p(j,k) = p(j)·p(k∣j)` (`adaptiveCascade_bornProb`) and the joint collapse equals the sequential one
(`adaptiveCascade_postMeasurement`). They are stated for `Measurement`, `State`, `bornProb` and
`postMeasurement`, and are the dependent analogues of `cascade_bornProb` /
`cascade_postMeasurement` (`AxQM/NC/Ch2/Exercise2_57.lean`).
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {κ : Type*} [Fintype κ] {μ : κ → Type*} [∀ j, Fintype (μ j)] {S : QSystem}

namespace Measurement

/-- The **adaptive cascade** of a measurement `L` (outcomes `κ`) with an outcome-dependent family of
measurements `M j` (outcomes `μ j`): the single measurement with outcome set `Σ j, μ j` whose
operator for outcome `⟨j, k⟩` is `N₍ⱼ,ₖ₎ = (M j)ₖ Lⱼ`. This is the dependent version of
`Measurement.cascade` (Exercise 2.57), where the second measurement is chosen conditionally on the
first outcome `j`. Completeness `∑₍ⱼ,ₖ₎ N₍ⱼ,ₖ₎† N₍ⱼ,ₖ₎ = 1` chains the completeness relations of the
`M j` and of `L`. -/
def adaptiveCascade (L : Measurement κ S) (M : (j : κ) → Measurement (μ j) S) :
    Measurement (Σ j, μ j) S where
  op p := ((M p.1).op p.2).comp (L.op p.1)
  complete := by
    rw [← L.complete, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsummand : ∀ k : μ j,
        (adjoint (((M j).op k).comp (L.op j))).comp (((M j).op k).comp (L.op j))
          = (adjoint (L.op j)).comp
              (((adjoint ((M j).op k)).comp ((M j).op k)).comp (L.op j)) :=
      fun k => by rw [adjoint_comp, comp_assoc, comp_assoc]
    simp only [hsummand]
    rw [← ContinuousLinearMap.comp_finsetSum, ← ContinuousLinearMap.finsetSum_comp,
      (M j).complete, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

@[simp]
theorem adaptiveCascade_op (L : Measurement κ S) (M : (j : κ) → Measurement (μ j) S)
    (j : κ) (k : μ j) :
    (L.adaptiveCascade M).op ⟨j, k⟩ = ((M j).op k).comp (L.op j) := rfl

/-- The post-measurement operation of the adaptive cascade factors through the two individual
post-measurement operations: `E₍ⱼ,ₖ₎(ρ) = (M j)ₖ Lⱼ ρ Lⱼ† (M j)ₖ† = Eₖ(Eⱼ(ρ))`. The operator
identity underlying both physical-equivalence laws. -/
theorem postOp_adaptiveCascade (L : Measurement κ S) (M : (j : κ) → Measurement (μ j) S)
    (ρ : S →L[ℂ] S) (j : κ) (k : μ j) :
    ContinuousLinearMap.postOp (L.adaptiveCascade M).op ρ ⟨j, k⟩
      = ContinuousLinearMap.postOp (M j).op (ContinuousLinearMap.postOp L.op ρ j) k := by
  simp only [ContinuousLinearMap.postOp, adaptiveCascade_op, adjoint_comp, comp_assoc]

/-- **Adaptive cascade: probabilities chain.** The Born probability of the single adaptive-cascade
measurement `L.adaptiveCascade M` for the joint outcome `⟨j, k⟩` equals the probability `p(j)` of
outcome `j` under `L` times the probability `p(k ∣ j)` of outcome `k` under the conditionally chosen
measurement `M j`, computed in the post-measurement state `L.postMeasurement ρ j` — the chained
probability `p(j, k) = p(j) · p(k ∣ j)`. The dependent analogue of `cascade_bornProb`. -/
theorem adaptiveCascade_bornProb (L : Measurement κ S) (M : (j : κ) → Measurement (μ j) S)
    (ρ : State S) (j : κ) (k : μ j) (hl : L.bornProb ρ j ≠ 0) :
    (L.adaptiveCascade M).bornProb ρ ⟨j, k⟩
      = L.bornProb ρ j * (M j).bornProb (L.postMeasurement ρ j hl) k := by
  have hp : RCLike.re (LinearMap.trace ℂ S
      (ContinuousLinearMap.postOp L.op ρ.op j : S →ₗ[ℂ] S)) ≠ 0 := by
    rw [← Measurement.bornProb_eq_re_trace_postOp]; exact hl
  have key : (M j).bornProb (L.postMeasurement ρ j hl) k
      = (RCLike.re (LinearMap.trace ℂ S (ContinuousLinearMap.postOp L.op ρ.op j : S →ₗ[ℂ] S)))⁻¹
        * RCLike.re (LinearMap.trace ℂ S
            (ContinuousLinearMap.postOp (M j).op (ContinuousLinearMap.postOp L.op ρ.op j) k
              : S →ₗ[ℂ] S)) := by
    rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.postMeasurement_op,
      ContinuousLinearMap.postState, ContinuousLinearMap.postOp_smul,
          ContinuousLinearMap.toLinearMap_smul,
      map_smul, smul_eq_mul]
    simp
  rw [Measurement.bornProb_eq_re_trace_postOp (L.adaptiveCascade M),
    Measurement.postOp_adaptiveCascade, Measurement.bornProb_eq_re_trace_postOp L, key,
    mul_inv_cancel_left₀ hp]

/-- **Adaptive cascade: states chain.** The post-measurement `State` of the single adaptive-cascade
measurement `L.adaptiveCascade M` for the joint outcome `⟨j, k⟩` equals the state obtained by
collapsing first under `L` (outcome `j`) and then under the conditionally chosen measurement `M j`
(outcome `k`). Together with `adaptiveCascade_bornProb` this is the physical equivalence of the
adaptive cascade and the sequential adaptive procedure. The dependent analogue of
`cascade_postMeasurement`. -/
theorem adaptiveCascade_postMeasurement (L : Measurement κ S) (M : (j : κ) → Measurement (μ j) S)
    (ρ : State S) (j : κ) (k : μ j) (hl : L.bornProb ρ j ≠ 0)
    (hm : (M j).bornProb (L.postMeasurement ρ j hl) k ≠ 0) :
    (L.adaptiveCascade M).postMeasurement ρ ⟨j, k⟩
        (by rw [adaptiveCascade_bornProb L M ρ j k hl]; exact mul_ne_zero hl hm)
      = (M j).postMeasurement (L.postMeasurement ρ j hl) k hm := by
  have hp : RCLike.re (LinearMap.trace ℂ S
      (ContinuousLinearMap.postOp L.op ρ.op j : S →ₗ[ℂ] S)) ≠ 0 := by
    rw [← Measurement.bornProb_eq_re_trace_postOp]; exact hl
  apply State.ext
  simp only [Measurement.postMeasurement_op]
  have hLunfold : ContinuousLinearMap.postState L.op ρ.op j
      = ((RCLike.re (LinearMap.trace ℂ S
            (ContinuousLinearMap.postOp L.op ρ.op j : S →ₗ[ℂ] S)))⁻¹ : ℂ)
          • ContinuousLinearMap.postOp L.op ρ.op j := rfl
  rw [hLunfold, ← Complex.ofReal_inv,
    ContinuousLinearMap.postState_smul (M j).op (ContinuousLinearMap.postOp L.op ρ.op j) k
      (inv_ne_zero hp),
    ContinuousLinearMap.postState, ContinuousLinearMap.postState,
    Measurement.postOp_adaptiveCascade]

/-- **Adaptive cascade: states chain, with the joint possibility supplied explicitly.** The variant
of `adaptiveCascade_postMeasurement` taking the joint-outcome possibility `hjoint` as an explicit
hypothesis instead of the `adaptiveCascade_bornProb`-derived proof embedded in its statement.
Interchangeable with `adaptiveCascade_postMeasurement` by proof irrelevance, but keeping `hjoint`
opaque matters when the cascade is instantiated at a large, deeply-composed measurement: with the
derived proof in the statement, the kernel re-verifies it at every use (unfolding the cascade's
operators — a heavy defeq); with `hjoint` opaque it never does. -/
theorem adaptiveCascade_postMeasurement' (L : Measurement κ S) (M : (j : κ) → Measurement (μ j) S)
    (ρ : State S) (j : κ) (k : μ j) (hl : L.bornProb ρ j ≠ 0)
    (hm : (M j).bornProb (L.postMeasurement ρ j hl) k ≠ 0)
    (hjoint : (L.adaptiveCascade M).bornProb ρ ⟨j, k⟩ ≠ 0) :
    (L.adaptiveCascade M).postMeasurement ρ ⟨j, k⟩ hjoint
      = (M j).postMeasurement (L.postMeasurement ρ j hl) k hm :=
  adaptiveCascade_postMeasurement L M ρ j k hl hm

/-- **The adaptive cascade lifted to the left factor.** On `S ⊗ T`, measuring the adaptive cascade
`L.adaptiveCascade M` and then lifting to the left factor (`.onLeft T`) has the same operator at
`⟨j, k⟩` as first lifting each stage and cascading there: both equal
`((M j)ₖ Lⱼ) ⊗ 1 = ((M j)ₖ ⊗ 1)(Lⱼ ⊗ 1)`. This lets the reduction reason about a combined Alice
measurement lifted to the composite `A ⊗ B` by transporting the cascade laws
(`adaptiveCascade_bornProb` / `adaptiveCascade_postMeasurement`) along `bornProb_congr` /
`postMeasurement_congr`. -/
theorem adaptiveCascade_onLeft_op (L : Measurement κ S) (M : (j : κ) → Measurement (μ j) S)
    (T : QSystem) (j : κ) (k : μ j) :
    ((L.adaptiveCascade M).onLeft T).op ⟨j, k⟩
      = ((L.onLeft T).adaptiveCascade (fun j => (M j).onLeft T)).op ⟨j, k⟩ := by
  simp only [Measurement.onLeft_op, adaptiveCascade_op]
  exact TensorProduct.mapL_mul_one ((M j).op k) (L.op j)

/-- **Each measurement effect is bounded by the identity.** For a measurement `N` on `S` and an
outcome `k`, the POVM effect satisfies `Nₖ† Nₖ ≤ 1` in the Loewner order, since it is one
nonnegative summand of the completeness sum `∑ i, Nᵢ† Nᵢ = 1`. -/
theorem op_adjoint_mul_self_le_one {ι : Type*} [Fintype ι] (N : Measurement ι S) (k : ι) :
    ContinuousLinearMap.adjoint (N.op k) * N.op k ≤ 1 := by
  have hApos : ∀ i : ι,
      (0 : S →L[ℂ] S) ≤ (ContinuousLinearMap.adjoint (N.op i)).comp (N.op i) :=
    fun i => (ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self (N.op i))
  have h1 := Finset.single_le_sum
    (f := fun i => (ContinuousLinearMap.adjoint (N.op i)).comp (N.op i))
    (fun i _ => hApos i) (Finset.mem_univ k)
  rwa [N.complete] at h1

/-- **A single measurement outcome is trace non-increasing.** For a measurement `N` on `S`, a
positive operator `X`, and an outcome `k`, the real trace of the post-measurement operation
`Eₖ(X) = Nₖ X Nₖ†` is at most the real trace of `X`:
`re tr(Nₖ X Nₖ†) = re tr(Nₖ† Nₖ X) ≤ re tr(1 · X) = re tr(X)`, using cyclicity of the trace, the
completeness bound `Nₖ† Nₖ ≤ 1`, and monotonicity of the trace pairing against `X ≥ 0`. -/
theorem re_trace_postOp_le {ι : Type*} [Fintype ι] (N : Measurement ι S)
    (X : S →L[ℂ] S) (hX : (0 : S →L[ℂ] S) ≤ X) (k : ι) :
    RCLike.re ((LinearMap.trace ℂ S) (ContinuousLinearMap.postOp N.op X k : S →ₗ[ℂ] S))
      ≤ RCLike.re ((LinearMap.trace ℂ S) (X : S →ₗ[ℂ] S)) := by
  have hcyc : (LinearMap.trace ℂ S) (ContinuousLinearMap.postOp N.op X k : S →ₗ[ℂ] S)
      = (LinearMap.trace ℂ S)
          ((((ContinuousLinearMap.adjoint (N.op k)) * (N.op k)) * X : S →L[ℂ] S) : S →ₗ[ℂ] S) := by
    simp only [ContinuousLinearMap.postOp, ← ContinuousLinearMap.mul_def]
    rw [ContinuousLinearMap.trace_mul_comm (N.op k) (X * ContinuousLinearMap.adjoint (N.op k)),
      mul_assoc, ContinuousLinearMap.trace_mul_comm X
        (ContinuousLinearMap.adjoint (N.op k) * N.op k)]
  rw [hcyc]
  simpa using ContinuousLinearMap.re_trace_mul_mono_left (N.op_adjoint_mul_self_le_one k) hX

/-- **The joint adaptive-cascade probability never exceeds the first-stage probability.** For the
adaptive cascade `L.adaptiveCascade M`, `p(j, k) ≤ p(j)`: measuring the second (conditional)
measurement after the first can only lose probability. This is the marginal bound
`p(j, k) = re tr((M j)ₖ (Lⱼ ρ Lⱼ†) (M j)ₖ†) ≤ re tr(Lⱼ ρ Lⱼ†) = p(j)` from `re_trace_postOp_le`. -/
theorem adaptiveCascade_bornProb_le_fst (L : Measurement κ S)
    (M : (j : κ) → Measurement (μ j) S) (ρ : State S) (j : κ) (k : μ j) :
    (L.adaptiveCascade M).bornProb ρ ⟨j, k⟩ ≤ L.bornProb ρ j := by
  rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.bornProb_eq_re_trace_postOp,
    Measurement.postOp_adaptiveCascade]
  exact (M j).re_trace_postOp_le (ContinuousLinearMap.postOp L.op ρ.op j)
    ((ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.postOp_isPositive L.op ρ.isPositive_op j)) k

/-- **A possible joint outcome forces the first stage to be possible.** If the adaptive cascade's
joint outcome `⟨j, k⟩` has nonzero Born probability, then so does the first-stage outcome `j`
(`p(j, k) ≤ p(j)` with `p(j, k) > 0`). This discharges the zero-probability first-stage branches
when combining Alice's rounds into a single measurement in the Proposition 12.14 reduction. -/
theorem adaptiveCascade_bornProb_fst_ne_zero (L : Measurement κ S)
    (M : (j : κ) → Measurement (μ j) S) (ρ : State S) (j : κ) (k : μ j)
    (h : (L.adaptiveCascade M).bornProb ρ ⟨j, k⟩ ≠ 0) : L.bornProb ρ j ≠ 0 := by
  intro hL
  have hle := adaptiveCascade_bornProb_le_fst L M ρ j k
  rw [hL] at hle
  exact h (le_antisymm hle ((L.adaptiveCascade M).bornProb_nonneg ρ ⟨j, k⟩))

end Measurement

end AxQM
