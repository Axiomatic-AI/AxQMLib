/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CondTypicalSubspaceFrame

/-!
# The HSW cross-message confusion term (N&C Thm 12.8, Box 12.5, eqs. (12.94)→(12.95))

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, achievability) the per-code average error is bounded by the pretty-good-measurement
error estimate of Box 12.5.  Its abstract Gram-family form
(`InnerProductSpace.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le`, eq. (12.94)) has, as one of its
three right-hand frame sums, the **cross-message confusion** double sum

`∑_{K ∈ T_M} λ^M_K ∑_{K' ∈ T_{M'}} |⟪Ẽ^M_K, Ẽ^{M'}_{K'}⟫|²`,   `Ẽ^M_K = P|E^M_K⟩`,

over the typical-subspace-compressed codeword eigenvectors of two *different* messages `M ≠ M'`.
"Calculating the spurs" (eqs. (12.94)→(12.95)) turns this frame sum into the physical confusion
trace `tr(P σ_M P P_{M'})` of eq. (12.95)/(12.79).  This file provides that per-message-pair
evaluation, plus the reusable ordering fact it rests on.

Both codewords live over the same block index `ι` and factor systems `S`, as HSW codewords do (all
outputs live in the single output space `⨂ₚ i, S`); `P` is any projection (a self-adjoint
idempotent), the typical projector in the application.

## Main results

* `AxQM.State.condTypicalSubspaceProj_comp_piTensor_op_le` — the **conditional typical
  compression is dominated by the codeword**: `P_M ∘ σ_M ≤ σ_M` in the Loewner order.  `P_M` is
  spanned by eigenvectors of `σ_M`, so it commutes with `σ_M` and `σ_M − P_M σ_M = (1−P_M) σ_M
  (1−P_M) ≥ 0`.  This is N&C's step of dropping the `P_M` factor when passing from the exact frame
  confusion sum to the over-estimate `tr(P σ_M P P_{M'})`.

* `AxQM.State.sum_eigenvalueDist_mul_sum_normSq_inner_proj_le_re_trace_confusion` — the
  **confusion-term bound** (N&C eqs. (12.94)→(12.95)):
  `∑_{κ} λ^M_κ ∑_{κ'} ‖⟪P E^M_κ, P E^{M'}_{κ'}⟫‖² ≤ re tr(P σ_M P P_{M'})`.
  The frame double sum equals `re tr((P P_{M'} P) ∘ P_M ∘ σ_M)` (the frame operator
  `P P_{M'} P = ∑ |Ẽ'⟩⟨Ẽ'|`, `comp_condTypicalSubspaceProj_comp_adjoint_eq_sum`, read against the
  spur evaluator `re_trace_comp_condTypicalSubspaceProj_comp_piTensor`); dropping the `P_M` via
  `P_M σ_M ≤ σ_M` and trace monotonicity against the positive `P P_{M'} P` gives the physical trace.

These use the frame identities of `CondTypicalSubspaceFrame`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, Box 12.5, eqs. (12.94), (12.95), (12.79).
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → QSystem}

set_option maxHeartbeats 1000000 in
-- Operator algebra on the re-bundled `⨂ₛ` space (adjoint / positivity / Loewner order) is
-- elaboration-heavy, so the default heartbeat budget is raised.
/-- **The conditional typical compression is dominated by the codeword** (Nielsen & Chuang,
Theorem 12.8, Box 12.5).  For a product codeword `σ_M = ⨂ₚ i, σ i` and its conditional typical
subspace projector `P_M = State.condTypicalSubspaceProj σ s ε`,

`P_M ∘ σ_M  ≤  σ_M`

in the Loewner order.  `P_M` is the orthogonal projector onto a set of eigenvectors of `σ_M`, so it
commutes with `σ_M` (both are diagonal in `State.piTensorEigenbasis σ`); hence
`σ_M − P_M σ_M = (1 − P_M) σ_M (1 − P_M)` is a conjugation of the positive `σ_M`, so it is positive.
This is exactly N&C's step of over-estimating the confusion contribution by dropping the leading
`P_M` when passing from the frame confusion sum to `tr(P σ_M P P_{M'})` (eqs. (12.94)→(12.95)). -/
theorem State.condTypicalSubspaceProj_comp_piTensor_op_le (σ : (i : ι) → State (S i)) (s ε : ℝ) :
    (State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op ≤ (State.piTensor σ).op := by
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive]
  have hPsa : IsSelfAdjoint (State.condTypicalSubspaceProj σ s ε) :=
    State.condTypicalSubspaceProj_isSelfAdjoint σ s ε
  have hAsa : IsSelfAdjoint (State.piTensor σ).op := State.isSelfAdjoint_op _
  -- `P_M ∘ σ_M` is self-adjoint: it is the eigenvalue-weighted sum of rank-one self-projectors.
  have hPAsa :
      IsSelfAdjoint ((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op) := by
    have hstar :
        star ((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op)
          = (State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op := by
      rw [State.condTypicalSubspaceProj_comp_piTensor_op_eq_sum, star_sum]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [star_smul, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne, ← starRingEnd_apply,
        Complex.conj_ofReal]
    exact hstar
  -- commutation `σ_M ∘ P_M = P_M ∘ σ_M`: `P_M ∘ σ_M` is self-adjoint, so it equals its own adjoint.
  have hcomm : (State.piTensor σ).op.comp (State.condTypicalSubspaceProj σ s ε)
      = (State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op := by
    rw [← hPAsa.star_eq, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      hAsa.star_eq, hPsa.star_eq]
  set P := State.condTypicalSubspaceProj σ s ε with hPdef
  set A := (State.piTensor σ).op with hAdef
  have hidem : P * P = P := State.condTypicalSubspaceProj_idem σ s ε
  have hc : A * P = P * A := hcomm
  have hdiff : A - P.comp A = (1 - P).comp (A.comp (1 - P)) := by
    have hexp : (1 - P).comp (A.comp (1 - P)) = A - A * P - P * A + P * (A * P) := by
      simp only [← ContinuousLinearMap.mul_def]
      noncomm_ring
    rw [show P.comp A = P * A from rfl, hexp, hc, ← mul_assoc, hidem]
    abel
  rw [hdiff]
  have hApos : A.IsPositive := State.isPositive_op _
  have h1Padj : ContinuousLinearMap.adjoint (1 - P) = 1 - P := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_sub, star_one, hPsa.star_eq]
  have hconj := hApos.conj_adjoint (1 - P)
  rw [h1Padj] at hconj
  exact hconj

set_option maxHeartbeats 1000000 in
-- Operator algebra on the re-bundled `⨂ₛ` space (adjoint / positivity / trace) is
-- elaboration-heavy, so the default heartbeat budget is raised.
/-- **The HSW cross-message confusion-term bound** (Nielsen & Chuang, Theorem 12.8, Box 12.5, the
"calculating the spurs" step, eqs. (12.94)→(12.95)).  For two product codewords `σ_M = ⨂ₚ i, σ i`,
`σ_{M'} = ⨂ₚ i, τ i` over the same block index `ι`, and a projection `P` (self-adjoint idempotent —
the typical projector compressing the codeword eigenvectors to `Ẽ = P|E⟩`),

`∑_{κ ∈ T_M} λ^M_κ ∑_{κ' ∈ T_{M'}} ‖⟪P E^M_κ, P E^{M'}_{κ'}⟫‖²  ≤  re tr(P σ_M P P_{M'})`,

where `T_M`, `T_{M'}` are the conditional typical sets (`Real.condTypicalSeq`),
`λ^M_κ = ∏ᵢ λ_{i,κᵢ}`, `E^M_κ = State.piTensorEigenbasis σ κ`, and
`P_{M'} = State.condTypicalSubspaceProj τ s ε`.

This is one of the three physical traces N&C's spur substitution produces; instantiated at every
pair `M ≠ M'` it supplies the confusion sum `∑_{M'≠M} tr(P σ_M P P_{M'})` of the per-code error
bound (eq. (12.79)).

Proof.  The frame operator `P P_{M'} P = ∑_{κ'} |Ẽ^{M'}_{κ'}⟩⟨Ẽ^{M'}_{κ'}|`
(`State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum` with `A = P`, `adjoint P = P`); its
diagonal matrix element `⟪E^M_κ, (P P_{M'} P) E^M_κ⟫ = ∑_{κ'} ‖⟪P E^M_κ, P E^{M'}_{κ'}⟫‖²`
(rank-one expansion, using `P` self-adjoint idempotent so `⟪E^M_κ, P E'⟫ = ⟪P E^M_κ, P E'⟫`).  The
spur evaluator `State.re_trace_comp_condTypicalSubspaceProj_comp_piTensor` with `B = P P_{M'} P`
then identifies the whole frame sum with `re tr((P P_{M'} P) ∘ P_M ∘ σ_M)`.  Finally `P_M σ_M ≤ σ_M`
(`State.condTypicalSubspaceProj_comp_piTensor_op_le`) and trace monotonicity against the positive
`P P_{M'} P` (`ContinuousLinearMap.re_trace_mul_mono_left`) drop the `P_M`, and trace cyclicity
rearranges `(P P_{M'} P) σ_M` into `P σ_M P P_{M'}`. -/
theorem State.sum_eigenvalueDist_mul_sum_normSq_inner_proj_le_re_trace_confusion
    (σ τ : (i : ι) → State (S i)) (s ε : ℝ)
    (P : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
    (hPsa : IsSelfAdjoint P) (hPidem : P.comp P = P) :
    (∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
        (∏ i, (σ i).eigenvalueDist (κ i)) *
          ∑ κ' ∈ Real.condTypicalSeq (fun i => (τ i).eigenvalueDist) s ε,
            ‖inner ℂ (P (State.piTensorEigenbasis σ κ)) (P (State.piTensorEigenbasis τ κ'))‖ ^ 2)
      ≤ RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
          (↑(P.comp ((State.piTensor σ).op.comp
            (P.comp (State.condTypicalSubspaceProj τ s ε)))) :
            (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space)) := by
  have hadjP : ContinuousLinearMap.adjoint P = P := hPsa.adjoint_eq
  have hfin : ∀ z : ℂ, RCLike.re ((starRingEnd ℂ) z * z) = ‖z‖ ^ 2 := fun z => by
    rw [mul_comm, Complex.mul_conj]
    change Complex.normSq z = ‖z‖ ^ 2
    exact Complex.normSq_eq_norm_sq z
  -- `B := P P_{M'} P` is the frame operator ∑ |Ẽ'⟩⟨Ẽ'|
  have hframe : P.comp ((State.condTypicalSubspaceProj τ s ε).comp P)
      = ∑ κ' ∈ Real.condTypicalSeq (fun i => (τ i).eigenvalueDist) s ε,
          rankOne ℂ (P (State.piTensorEigenbasis τ κ')) (P (State.piTensorEigenbasis τ κ')) := by
    have h := State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum τ s ε P
    rwa [hadjP] at h
  -- Step 1: the frame double sum equals `re tr((P P_{M'} P) ∘ P_M ∘ σ_M)`.
  have hstep1 :
      (∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
          (∏ i, (σ i).eigenvalueDist (κ i)) *
            ∑ κ' ∈ Real.condTypicalSeq (fun i => (τ i).eigenvalueDist) s ε,
              ‖inner ℂ (P (State.piTensorEigenbasis σ κ)) (P (State.piTensorEigenbasis τ κ'))‖ ^ 2)
        = RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
            (↑((P.comp ((State.condTypicalSubspaceProj τ s ε).comp P)).comp
              ((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op)) :
              (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space)) := by
    rw [State.re_trace_comp_condTypicalSubspaceProj_comp_piTensor σ s ε
      (P.comp ((State.condTypicalSubspaceProj τ s ε).comp P))]
    refine Finset.sum_congr rfl fun κ _ => ?_
    congr 1
    rw [hframe, _root_.sum_apply, inner_sum, RCLike.re_sum]
    refine Finset.sum_congr rfl fun κ' _ => ?_
    rw [rankOne_apply, inner_smul_right]
    have hz : inner ℂ (State.piTensorEigenbasis σ κ) (P (State.piTensorEigenbasis τ κ'))
        = inner ℂ (P (State.piTensorEigenbasis σ κ)) (P (State.piTensorEigenbasis τ κ')) := by
      rw [← ContinuousLinearMap.adjoint_inner_right P (State.piTensorEigenbasis σ κ)
          (P (State.piTensorEigenbasis τ κ')), hadjP,
        show P (P (State.piTensorEigenbasis τ κ'))
            = (P.comp P) (State.piTensorEigenbasis τ κ') from rfl, hPidem]
    rw [show inner ℂ (P (State.piTensorEigenbasis τ κ')) (State.piTensorEigenbasis σ κ)
          = (starRingEnd ℂ) (inner ℂ (State.piTensorEigenbasis σ κ)
              (P (State.piTensorEigenbasis τ κ'))) from
        (inner_conj_symm (P (State.piTensorEigenbasis τ κ')) (State.piTensorEigenbasis σ κ)).symm,
      hz, hfin]
  rw [hstep1]
  -- Step 2: drop the `P_M` factor and rearrange to `re tr(P σ_M P P_{M'})`.
  have hBpos : (0 : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
      ≤ P.comp ((State.condTypicalSubspaceProj τ s ε).comp P) := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    have hPτpos : (State.condTypicalSubspaceProj τ s ε).IsPositive := by
      rw [ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
        (State.condTypicalSubspaceProj_idem τ s ε)]
      exact State.condTypicalSubspaceProj_isSelfAdjoint τ s ε
    have hcj := hPτpos.conj_adjoint P
    rwa [hadjP] at hcj
  have hle : (State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op
      ≤ (State.piTensor σ).op :=
    State.condTypicalSubspaceProj_comp_piTensor_op_le σ s ε
  have hmono := ContinuousLinearMap.re_trace_mul_mono_left hle hBpos
  have heq1 : RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑((P.comp ((State.condTypicalSubspaceProj τ s ε).comp P)).comp
          ((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op)) :
          (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
      = RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op)
          * (P.comp ((State.condTypicalSubspaceProj τ s ε).comp P))) :
          (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space)) := by
    rw [show (P.comp ((State.condTypicalSubspaceProj τ s ε).comp P)).comp
          ((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op)
        = (P.comp ((State.condTypicalSubspaceProj τ s ε).comp P))
          * ((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op) from rfl,
      ContinuousLinearMap.trace_mul_comm]
  have hrw2 : (State.piTensor σ).op * (P.comp ((State.condTypicalSubspaceProj τ s ε).comp P))
      = ((State.piTensor σ).op.comp (P.comp (State.condTypicalSubspaceProj τ s ε))) * P := by
    simp only [← ContinuousLinearMap.mul_def]; noncomm_ring
  have heq2 : RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑((State.piTensor σ).op * (P.comp ((State.condTypicalSubspaceProj τ s ε).comp P))) :
          (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
      = RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(P.comp ((State.piTensor σ).op.comp
          (P.comp (State.condTypicalSubspaceProj τ s ε)))) :
          (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space)) := by
    rw [hrw2, ContinuousLinearMap.trace_mul_comm, ContinuousLinearMap.mul_def]
  rw [heq1]
  exact hmono.trans_eq heq2

end AxQM
