/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CondTypicalSubspaceConfusion

/-!
# The HSW same-message diagonal spur (N&C Thm 12.8, Box 12.5, eqs. (12.94)→(12.79))

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, achievability) the per-code average error is bounded by the pretty-good-measurement
error estimate of Box 12.5.  Its abstract Gram-family form
(`InnerProductSpace.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le`, eq. (12.94)) bounds the decoding
deficit `2·∑_c λ_c (1 − α_{cc})` — over the *global* typical index `c = (M, κ)`, `κ ∈ T_M` —
by three right-hand frame sums

`2·∑_c λ_c  −  3·∑_c λ_c ‖ψ_c‖²  +  ∑_c ∑_{c'} λ_c |⟪ψ_c, ψ_{c'}⟫|²`,   `ψ_{(M,κ)} = P|E^M_κ⟩`.

Grouping the global index by the message `M`, the contribution of one message splits into a
**same-message** part (the diagonal `M' = M`) plus the **cross-message** confusion part (`M' ≠ M`,
handled by `State.sum_eigenvalueDist_mul_sum_normSq_inner_proj_le_re_trace_confusion`).  This file
provides the same-message part: its three sums, `2·∑_{κ∈T} λ_κ`, `−3·∑_{κ∈T} λ_κ‖P E_κ‖²`, and the
diagonal frame double sum `∑_{κ∈T} λ_κ ∑_{κ'∈T} |⟪P E_κ, P E_{κ'}⟫|²`, combine into the two physical
error terms of the per-code bound eq. (12.79):

`≤  3·tr(σ_M (1 − P))  +  tr(σ_M (1 − P_M))`.

## Main result

* `AxQM.State.sum_eigenvalueDist_sameMessageSpur_le_re_trace` — the same-message diagonal
  spur bound: for a product codeword `σ_M = ⨂ₚ i, σ i`, its conditional typical subspace projector
  `P_M = State.condTypicalSubspaceProj σ s ε`, and a projection `P` (self-adjoint idempotent — the
  typical projector),

  `2·∑_{κ∈T} λ_κ − 3·∑_{κ∈T} λ_κ‖P E_κ‖² + ∑_{κ∈T} λ_κ ∑_{κ'∈T} ‖⟪P E_κ, P E_{κ'}⟫‖²`
  `  ≤  3·re tr((1 − P) σ_M) + re tr((1 − P_M) σ_M)`,

  where `T = Real.condTypicalSeq (fun i ↦ (σ i).eigenvalueDist) s ε`, `λ_κ = ∏ᵢ λ_{i,κᵢ}`, and
  `E_κ = State.piTensorEigenbasis σ κ`.

## Proof

Abbreviate `A = σ_M`, `P_M`, and write `re tr(X)` for the real trace.  Three trace identities read
the frame sums as physical traces (all via the spur/frame lemmas of `CondTypicalSubspaceFrame`
and the confusion bound of `CondTypicalSubspaceConfusion`):

* `∑_{κ∈T} λ_κ = re tr(P_M A)` (the typical mass, `re_trace_condTypicalSubspaceProj_comp_piTensor`);
* `∑_{κ∈T} λ_κ ‖P E_κ‖² = re tr(P P_M A)` (the spur evaluator at `B = P`, using
  `re⟪E_κ, P E_κ⟫ = ‖P E_κ‖²` for a projection `P`);
* the diagonal frame double sum `≤ re tr(P σ_M P P_M)` (the confusion bound at the *same* codeword
  `σ`).

The remaining step is trace algebra, closed by `linarith`, using that `P` and `P_M` are between `0`
and `1`, that `(1 − P_M) A` is positive (`P_M` is spanned by eigenvectors of `A`, so `P_M A ≤ A`,
`State.condTypicalSubspaceProj_comp_piTensor_op_le`), trace monotonicity
(`ContinuousLinearMap.re_trace_mul_mono_left`), and nonnegativity of the trace of a product of
positive operators (`ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg`).  Concretely, with
`a = re tr(P A)`: the diagonal frame trace is `≤ re tr(P σ_M P P_M) ≤ re tr(P σ_M P) = a` (drop
`P_M ≤ 1`); and `re tr(P P_M A) ≥ a − tr((1 − P_M) A)` (the `P`-weight of the atypical block is
`≤` its full trace).  The two combine to `≤ 3(re tr A − a) + (re tr A − re tr(P_M A))`, the two
physical terms.  No use is made of `tr σ_M = 1`, so the bound holds for any positive `A`.

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
-- Operator algebra on the re-bundled `⨂ₛ` space (adjoint / positivity / trace) is
-- elaboration-heavy, so the default heartbeat budget is raised.
/-- **The HSW same-message diagonal spur bound** (Nielsen & Chuang, Theorem 12.8, Box 12.5, the
same-message part of the "calculating the spurs" step, eqs. (12.94)→(12.79)).  For a product
codeword `σ_M = ⨂ₚ i, σ i` with conditional typical subspace projector
`P_M = State.condTypicalSubspaceProj σ s ε`, and a projection `P` (self-adjoint idempotent — the
typical projector compressing the codeword eigenvectors to `Ẽ = P|E⟩`),

`2·∑_{κ∈T} λ_κ  −  3·∑_{κ∈T} λ_κ‖P E_κ‖²  +  ∑_{κ∈T} λ_κ ∑_{κ'∈T} ‖⟪P E_κ, P E_{κ'}⟫‖²`
`  ≤  3·re tr((1 − P) σ_M)  +  re tr((1 − P_M) σ_M)`,

where `T = Real.condTypicalSeq (fun i ↦ (σ i).eigenvalueDist) s ε`, `λ_κ = ∏ᵢ λ_{i,κᵢ}`, and
`E_κ = State.piTensorEigenbasis σ κ`.

The left-hand side is the same-message (`M' = M`) contribution of the abstract Gram-family bound
(N&C eq. (12.94)) grouped by message; the right-hand side is the corresponding two physical error
terms of the per-code bound eq. (12.79) (`3·tr(σ_M(I−P)) + tr(σ_M(I−P_M))`).  Together with the
cross-message confusion bound
(`State.sum_eigenvalueDist_mul_sum_normSq_inner_proj_le_re_trace_confusion`, summed over `M' ≠ M`)
it supplies the per-message content of the global-index assembly of eq. (12.79).

The three frame sums are read as physical traces via the spur/frame lemmas, and the trace
algebra is closed by `linarith` using `0 ≤ P, P_M ≤ 1`, positivity of `(1 − P_M) σ_M`, and trace
monotonicity/nonnegativity; see the module docstring. -/
theorem State.sum_eigenvalueDist_sameMessageSpur_le_re_trace (σ : (i : ι) → State (S i)) (s ε : ℝ)
    (P : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
    (hPsa : IsSelfAdjoint P) (hPidem : P.comp P = P) :
    2 * (∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
          ∏ i, (σ i).eigenvalueDist (κ i))
      - 3 * (∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
          (∏ i, (σ i).eigenvalueDist (κ i)) * ‖P (State.piTensorEigenbasis σ κ)‖ ^ 2)
      + (∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
          (∏ i, (σ i).eigenvalueDist (κ i)) *
            ∑ κ' ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
              ‖inner ℂ (P (State.piTensorEigenbasis σ κ))
                (P (State.piTensorEigenbasis σ κ'))‖ ^ 2)
      ≤ 3 * RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
            (↑((1 - P) * (State.piTensor σ).op) :
              (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
        + RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
            (↑((1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op) :
              (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space)) := by
  classical
  -- `adjoint P = P` for the self-adjoint projection.
  have hadjP : ContinuousLinearMap.adjoint P = P := hPsa.adjoint_eq
  -- `P` and `P_M` are between `0` and `1` (they are self-adjoint idempotents).
  have hPidemElt : IsIdempotentElem P := hPidem
  have hP_le1 : P ≤ 1 := ContinuousLinearMap.IsIdempotentElem.le_one hPidemElt hPsa
  have h1P_nonneg :
      (0 : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space) ≤ 1 - P :=
    sub_nonneg.mpr hP_le1
  have hPmidemElt : IsIdempotentElem (State.condTypicalSubspaceProj σ s ε) :=
    State.condTypicalSubspaceProj_idem σ s ε
  have hPmsa : IsSelfAdjoint (State.condTypicalSubspaceProj σ s ε) :=
    State.condTypicalSubspaceProj_isSelfAdjoint σ s ε
  have hPm_le1 : State.condTypicalSubspaceProj σ s ε ≤ 1 :=
    ContinuousLinearMap.IsIdempotentElem.le_one hPmidemElt hPmsa
  -- Positivity of the codeword and of the atypical block `(1 − P_M) σ_M`.
  have hA_pos : (0 : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
      ≤ (State.piTensor σ).op :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (State.isPositive_op _)
  have hle : (State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op
      ≤ (State.piTensor σ).op :=
    State.condTypicalSubspaceProj_comp_piTensor_op_le σ s ε
  have h1PmA_nonneg :
      (0 : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
        ≤ (1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op := by
    have hrw : ((1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op)
        = (State.piTensor σ).op
          - (State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op := by
      rw [sub_mul, one_mul]
    rw [hrw]
    have hlt : (State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op
        ≤ (State.piTensor σ).op := by
      rw [ContinuousLinearMap.mul_def]; exact hle
    exact sub_nonneg.mpr hlt
  -- Positivity of `P σ_M P` (conjugation of the positive `σ_M` by the self-adjoint `P`).
  have hPAP_pos : (0 : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
      ≤ P * ((State.piTensor σ).op * P) := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    have hcj := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA_pos).conj_adjoint P
    rw [hadjP] at hcj
    simpa only [← ContinuousLinearMap.mul_def] using hcj
  -- `re⟪E_κ, P E_κ⟫ = ‖P E_κ‖²` for the projection `P`.
  have hnorm : ∀ κ, RCLike.re (inner ℂ (State.piTensorEigenbasis σ κ)
      (P (State.piTensorEigenbasis σ κ))) = ‖P (State.piTensorEigenbasis σ κ)‖ ^ 2 := by
    intro κ
    rw [inner_self_of_isSelfAdjoint_of_isIdempotent hPsa hPidemElt, RCLike.ofReal_re]
  -- Frame sum 1 (typical mass): `∑ λ = re tr(P_M σ_M)`.
  have e1 : (∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
        ∏ i, (σ i).eigenvalueDist (κ i))
      = RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
          (↑((State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op) : _ →ₗ[ℂ] _)) := by
    rw [show ((State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op)
        = (State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op from rfl,
      State.re_trace_condTypicalSubspaceProj_comp_piTensor σ s ε]
  -- Frame sum 2 (`‖P E_κ‖²`-weight): `∑ λ‖P E_κ‖² = re tr(P P_M σ_M)`.
  have e2 : (∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
        (∏ i, (σ i).eigenvalueDist (κ i)) * ‖P (State.piTensorEigenbasis σ κ)‖ ^ 2)
      = RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
          (↑(P * ((State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op)) :
            _ →ₗ[ℂ] _)) := by
    rw [show (P * ((State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op))
        = P.comp ((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op) from rfl,
      State.re_trace_comp_condTypicalSubspaceProj_comp_piTensor σ s ε P]
    exact Finset.sum_congr rfl fun κ _ => by rw [hnorm κ]
  -- Frame sum 3 (diagonal confusion sum): `≤ re tr(P σ_M P P_M)` (confusion bound at `σ = τ`).
  have hC := State.sum_eigenvalueDist_mul_sum_normSq_inner_proj_le_re_trace_confusion σ σ s ε P
    hPsa hPidem
  simp only [← ContinuousLinearMap.mul_def] at hC
  -- Cyclicity/idempotence: `re tr(P σ_M P) = re tr(P σ_M)`.
  have hPmul : P * P = P := hPidem
  have heqPAP : RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(P * ((State.piTensor σ).op * P)) : _ →ₗ[ℂ] _))
      = RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(P * (State.piTensor σ).op) : _ →ₗ[ℂ] _)) := by
    rw [congrArg RCLike.re (ContinuousLinearMap.trace_mul_comm P ((State.piTensor σ).op * P)),
      show (((State.piTensor σ).op * P) * P) = (State.piTensor σ).op * P from by
        rw [mul_assoc, hPmul],
      congrArg RCLike.re (ContinuousLinearMap.trace_mul_comm (State.piTensor σ).op P)]
  -- Drop `P_M ≤ 1`: `re tr(P σ_M P P_M) ≤ re tr(P σ_M)`.
  have hassoc : (P * ((State.piTensor σ).op * P)) * (State.condTypicalSubspaceProj σ s ε)
      = P * ((State.piTensor σ).op * (P * (State.condTypicalSubspaceProj σ s ε))) := by
    rw [mul_assoc, mul_assoc]
  have hCle : RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(P * ((State.piTensor σ).op * (P * (State.condTypicalSubspaceProj σ s ε)))) : _ →ₗ[ℂ] _))
      ≤ RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(P * (State.piTensor σ).op) : _ →ₗ[ℂ] _)) := by
    have hcyc : RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
          (↑(P * ((State.piTensor σ).op * (P * (State.condTypicalSubspaceProj σ s ε))))
            : _ →ₗ[ℂ] _))
        = RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
          (↑((State.condTypicalSubspaceProj σ s ε) * (P * ((State.piTensor σ).op * P)))
            : _ →ₗ[ℂ] _)) := by
      rw [← hassoc]
      exact congrArg RCLike.re (ContinuousLinearMap.trace_mul_comm (P * ((State.piTensor σ).op * P))
        (State.condTypicalSubspaceProj σ s ε))
    have hm := ContinuousLinearMap.re_trace_mul_mono_left hPm_le1 hPAP_pos
    rw [one_mul] at hm
    rw [hcyc]
    exact hm.trans (le_of_eq heqPAP)
  -- `P_M`-split of `re tr(P σ_M) = re tr(P P_M σ_M) + re tr(P (1 − P_M) σ_M)`.
  have hB : RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(P * (State.piTensor σ).op) : _ →ₗ[ℂ] _))
      = RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
          (↑(P * ((State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op)) : _ →ₗ[ℂ] _))
        + RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
          (↑(P * ((1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op))
            : _ →ₗ[ℂ] _)) := by
    have hop : P * ((State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op)
          + P * ((1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op)
        = P * (State.piTensor σ).op := by
      rw [← mul_add, ← add_mul,
        show ((State.condTypicalSubspaceProj σ s ε) + (1 - State.condTypicalSubspaceProj σ s ε))
          = 1 from by abel, one_mul]
    rw [← hop, ContinuousLinearMap.toLinearMap_add, map_add, map_add]
  -- The `P`-weight of the atypical block is `≤` its full trace.
  have hy : RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(P * ((1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op)) : _ →ₗ[ℂ] _))
      ≤ RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑((1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op) : _ →ₗ[ℂ] _)) := by
    have hnn := ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg h1P_nonneg h1PmA_nonneg
    have hsplit : ((1 - P) * ((1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op))
        = (1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op
          - P * ((1 - State.condTypicalSubspaceProj σ s ε) * (State.piTensor σ).op) := by
      rw [sub_mul, one_mul]
    rw [hsplit, ContinuousLinearMap.toLinearMap_sub, map_sub, map_sub] at hnn
    linarith
  -- `re tr(P σ_M) ≤ re tr σ_M`.
  have hx4le5 : RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(P * (State.piTensor σ).op) : _ →ₗ[ℂ] _))
      ≤ RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
        (↑(State.piTensor σ).op : _ →ₗ[ℂ] _)) := by
    have hm := ContinuousLinearMap.re_trace_mul_mono_left hP_le1 hA_pos
    rwa [one_mul] at hm
  -- The two physical terms as trace differences (`re tr((1−X)σ_M) = re tr σ_M − re tr(X σ_M)`).
  have hRHS1 := ContinuousLinearMap.re_trace_one_sub_mul P (State.piTensor σ).op
  have hRHS2 := ContinuousLinearMap.re_trace_one_sub_mul
    (State.condTypicalSubspaceProj σ s ε) (State.piTensor σ).op
  rw [e1, e2, hRHS1, hRHS2]
  linarith [hC, hCle, hB, hy, hx4le5, hRHS2]

end AxQM
