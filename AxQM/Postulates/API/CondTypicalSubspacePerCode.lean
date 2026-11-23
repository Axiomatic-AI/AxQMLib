/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CondTypicalSubspaceDiagonal
import ToMathlib.Analysis.InnerProductSpace.CFCSqrtGramFamilySigma

/-!
# The HSW per-code spur instantiation (N&C Thm 12.8, Box 12.5, eqs. (12.94)→(12.95)/(12.79))

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, achievability) the per-code average error of the pretty-good (square-root) decoder is
bounded by the abstract Gram-family estimate of Box 12.5.  Its *message-grouped* form
(`InnerProductSpace.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le_sigma`, N&C eq. (12.94)) bounds
the total decoding deficit over the **global** typical index `c = (M, κ)`, `κ ∈ T_M`,

`2·∑_c λ_c (1 − α_c)`,   `α_c = re⟪e_c, √Γ e_c⟫`,   `Γ = V⋆·V`,   `V = synthesisMap ψ`,
`ψ_{(M,κ)} = P|E^M_κ⟩`,

by a sum over the message `M` of a **same-message** block (the diagonal `M' = M`) plus a
**cross-message** block (`M' ≠ M`).

This file performs the "calculating the spurs" substitution (N&C eqs. (12.94)→(12.95)):
instantiating that abstract bound at the concrete codebook family `ψ_{(M,κ)} = P|E^M_κ⟩`, over the
global typical index `Σ_M {κ ∈ T_M}`, and evaluating each block's frame sums as the physical error
traces of the per-code bound eq. (12.79).

## Main result

* `AxQM.State.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_codebook_le_re_trace` — the
  **per-code spur bound**.  For a length-`n` codebook `σ : Fin K → (i : ι) → State (S i)` of `K`
  product codewords `σ_M = ⨂ₚ i, σ M i` and a projection `P` (self-adjoint idempotent — the typical
  projector), the total decoding deficit over the global typical index is bounded by the sum over
  messages of the three physical error traces of eq. (12.79):

  `2·∑_{(M,κ) : Σ_M T_M} λ^M_κ (1 − α_{(M,κ)})`
  `  ≤  ∑_M [ 3·re tr((1 − P) σ_M) + re tr((1 − P_M) σ_M) + ∑_{M'≠M} re tr(P σ_M P P_{M'}) ]`,

  where `T_M = Real.condTypicalSeq (fun i ↦ (σ M i).eigenvalueDist) s ε`, `λ^M_κ = ∏ᵢ λ_{i,κᵢ}`,
  `α_{(M,κ)} = re⟪e_{(M,κ)}, √Γ e_{(M,κ)}⟫` is the diagonal of the square root of the Gram operator
  `Γ = (synthesisMap ψ)⋆ ∘ synthesisMap ψ` of the global compressed-eigenvector family
  `ψ_{(M,κ)} = P (State.piTensorEigenbasis (σ M) κ)`, and `P_{M'} = State.condTypicalSubspaceProj
  (σ M') s ε`.

  Combined with the decoder-error → diagonal-α reduction (N&C eqs. (12.84)–(12.88), which identifies
  the per-code error `p_av` with `α`), this is the per-code error bound eq. (12.79).

## Proof

Instantiate `two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le_sigma` at the sigma-indexed family
`ψ_{(M,κ)} = P|E^M_κ⟩` and weight `λ^M_κ = ∏ᵢ λ_{i,κᵢ}` (nonnegative,
`State.eigenvalueDist_nonneg`), the block index `a = M` ranging over `Fin K` and the block
`γ M = {κ // κ ∈ T_M}` the message's
conditional typical set.  Its right-hand side is a sum over `M` of one same-message block and the
cross-message blocks; `Finset.sum_coe_sort` rewrites each subtype block sum as a `Finset` sum over
`T_M`, matching exactly the left-hand sides of the two per-message spur bounds:

* the same-message block is closed by the same-message diagonal spur bound
  `State.sum_eigenvalueDist_sameMessageSpur_le_re_trace`
  (`≤ 3·re tr((1−P)σ_M) + re tr((1−P_M)σ_M)`);
* each cross-message block (fixed `M' ≠ M`) is closed by the confusion bound
  `State.sum_eigenvalueDist_mul_sum_normSq_inner_proj_le_re_trace_confusion`
  (`≤ re tr(P σ_M P P_{M'})`), summed over `M' ≠ M` by `Finset.sum_le_sum`.

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
-- The functional calculus `cfc Real.sqrt` of the Gram operator on the concrete global typical index
-- `Σ M, {κ ∈ T_M}` drives elaboration-heavy operator-algebra instance synthesis, so both heartbeat
-- budgets are raised.
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The HSW per-code spur bound** (Nielsen & Chuang, Theorem 12.8, Box 12.5, "calculating the
spurs", eqs. (12.94)→(12.95)/(12.79)).  For a length-`n` codebook
`σ : Fin K → (i : ι) → State (S i)` of `K` product codewords `σ_M = ⨂ₚ i, σ M i`, and a projection
`P` (self-adjoint idempotent — the
typical projector compressing the codeword eigenvectors to `Ẽ = P|E⟩`), the total decoding deficit
of the pretty-good decoder over the global typical index is bounded by the sum over messages of the
three physical error traces of the per-code bound eq. (12.79):

`2·∑_{(M,κ)} λ^M_κ (1 − α_{(M,κ)})`
`  ≤  ∑_M [ 3·re tr((1 − P) σ_M) + re tr((1 − P_M) σ_M) + ∑_{M'≠M} re tr(P σ_M P P_{M'}) ]`,

where the sum on the left ranges over the sigma index `Σ_M {κ ∈ T_M}`,
`T_M = Real.condTypicalSeq (fun i ↦ (σ M i).eigenvalueDist) s ε`, `λ^M_κ = ∏ᵢ λ_{i,κᵢ}`,
`α_{(M,κ)} = re⟪e_{(M,κ)}, √Γ e_{(M,κ)}⟫` is the diagonal of the operator square root of the Gram
operator `Γ = (synthesisMap ψ)⋆ ∘ synthesisMap ψ` of the global compressed-eigenvector family
`ψ_{(M,κ)} = P (State.piTensorEigenbasis (σ M) κ)`, and `P_{M'} = State.condTypicalSubspaceProj
(σ M') s ε`.

Instantiates the message-grouped Gram-family bound
`InnerProductSpace.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le_sigma` (eq. (12.94)) and evaluates
each block's frame sums as physical traces via the same-message diagonal spur bound
(`State.sum_eigenvalueDist_sameMessageSpur_le_re_trace`) and the cross-message confusion bound
(`State.sum_eigenvalueDist_mul_sum_normSq_inner_proj_le_re_trace_confusion`).

The functional calculus `cfc Real.sqrt` of the Gram operator on the concrete global typical index
`Σ M, {κ ∈ T_M}` drives elaboration-heavy operator-algebra instance synthesis, so both heartbeat
budgets are raised. -/
theorem State.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_codebook_le_re_trace
    {K : ℕ} (σ : Fin K → (i : ι) → State (S i)) (s ε : ℝ)
    (P : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
    (hPsa : IsSelfAdjoint P) (hPidem : P.comp P = P) :
    2 * ∑ p : (Σ M : Fin K,
          {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}),
        (∏ i, (σ p.1 i).eigenvalueDist (p.2.1 i)) *
          (1 - RCLike.re (inner ℂ
            (EuclideanSpace.basisFun (Σ M : Fin K,
              {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) ℂ p)
            ((cfc Real.sqrt ((adjoint (synthesisMap
                (fun p : (Σ M : Fin K,
                  {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) =>
                  P (State.piTensorEigenbasis (σ p.1) p.2.1)))).comp
              (synthesisMap (fun p : (Σ M : Fin K,
                  {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) =>
                  P (State.piTensorEigenbasis (σ p.1) p.2.1)))))
              (EuclideanSpace.basisFun (Σ M : Fin K,
                {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) ℂ p))))
      ≤ ∑ M : Fin K, (3 * RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
            (↑((1 - P) * (State.piTensor (σ M)).op) :
              (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
          + RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
            (↑((1 - State.condTypicalSubspaceProj (σ M) s ε) * (State.piTensor (σ M)).op) :
              (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))
          + ∑ M' ∈ Finset.univ.erase M, RCLike.re (LinearMap.trace ℂ (QSystem.piTensor S).space
            (↑(P.comp ((State.piTensor (σ M)).op.comp
                (P.comp (State.condTypicalSubspaceProj (σ M') s ε)))) :
              (QSystem.piTensor S).space →ₗ[ℂ] (QSystem.piTensor S).space))) := by
  classical
  refine (InnerProductSpace.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le_sigma
    (fun p : (Σ M : Fin K,
        {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) =>
      P (State.piTensorEigenbasis (σ p.1) p.2.1))
    (fun p : (Σ M : Fin K,
        {κ // κ ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε}) =>
      ∏ i, (σ p.1 i).eigenvalueDist (p.2.1 i))
    (fun p => Finset.prod_nonneg fun i _ => State.eigenvalueDist_nonneg _ _)).trans ?_
  refine Finset.sum_le_sum fun M _ => ?_
  -- Convert the inner frame sums over the subtype to `Finset` sums over the typical set.
  -- The function shape is fixed (only the first argument `v` varies), so `simp` can match it under
  -- the outer binders of both the same-message and the cross-message blocks.
  have hcoeInner : ∀ (N : Fin K) (v : (QSystem.piTensor S).space),
      (∑ κ' : {κ // κ ∈ Real.condTypicalSeq (fun i => (σ N i).eigenvalueDist) s ε},
          ‖inner ℂ v (P (State.piTensorEigenbasis (σ N) κ'.1))‖ ^ 2)
        = ∑ κ' ∈ Real.condTypicalSeq (fun i => (σ N i).eigenvalueDist) s ε,
            ‖inner ℂ v (P (State.piTensorEigenbasis (σ N) κ'))‖ ^ 2 :=
    fun N v => Finset.sum_coe_sort _
      (fun κ' => ‖inner ℂ v (P (State.piTensorEigenbasis (σ N) κ'))‖ ^ 2)
  simp only [hcoeInner]
  refine add_le_add ?_ ?_
  · -- same-message diagonal block: convert the three outer sums, then apply the diagonal bound
    rw [Finset.sum_coe_sort (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)
          (fun κ => ∏ i, (σ M i).eigenvalueDist (κ i)),
        Finset.sum_coe_sort (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)
          (fun κ => (∏ i, (σ M i).eigenvalueDist (κ i)) *
            ‖P (State.piTensorEigenbasis (σ M) κ)‖ ^ 2),
        Finset.sum_coe_sort (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)
          (fun κ => (∏ i, (σ M i).eigenvalueDist (κ i)) *
            ∑ κ' ∈ Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε,
              ‖inner ℂ (P (State.piTensorEigenbasis (σ M) κ))
                (P (State.piTensorEigenbasis (σ M) κ'))‖ ^ 2)]
    exact State.sum_eigenvalueDist_sameMessageSpur_le_re_trace (σ M) s ε P hPsa hPidem
  · -- cross-message confusion blocks: convert the outer sum per pair, apply the confusion bound
    refine Finset.sum_le_sum fun M' _ => ?_
    rw [Finset.sum_coe_sort (Real.condTypicalSeq (fun i => (σ M i).eigenvalueDist) s ε)
          (fun κ => (∏ i, (σ M i).eigenvalueDist (κ i)) *
            ∑ κ' ∈ Real.condTypicalSeq (fun i => (σ M' i).eigenvalueDist) s ε,
              ‖inner ℂ (P (State.piTensorEigenbasis (σ M) κ))
                (P (State.piTensorEigenbasis (σ M') κ'))‖ ^ 2)]
    exact State.sum_eigenvalueDist_mul_sum_normSq_inner_proj_le_re_trace_confusion
      (σ M) (σ M') s ε P hPsa hPidem

end AxQM
