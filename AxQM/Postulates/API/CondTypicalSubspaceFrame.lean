/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CondTypicalSubspace
import AxQM.Postulates.API.EntropyMixLine
import ToMathlib.Analysis.InnerProductSpace.CFCSqrtGramFamily

/-!
# AxQM.Postulates.API — codeword-eigenvector frame identities ("calculating the spurs")

The *frame algebra* underlying Nielsen & Chuang's Box 12.5 "calculating the spurs"
step (eqs. (12.94)→(12.95)) in the random-coding achievability half of the
Holevo–Schumacher–Westmoreland theorem (Theorem 12.8, `χ(E) = C⁽¹⁾(E)`).

Box 12.5 bounds the pretty-good (square-root) decoding deficit by the abstract Gram-trace
inequality `InnerProductSpace.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le` (N&C eq. (12.94)),
whose right-hand side is a set of *frame sums* `∑ λ‖ψ‖²`, `∑∑ λ|⟪ψ, ψ⟫|²` over the compressed
codeword eigenvectors `ψ = |Ẽ_κ⟩ = A|E_κ⟩`.  To recover N&C's physical error terms `tr(σ_M(I−P))`,
`tr(P σ_M P P_{M'})`, `tr(σ_M(I−P_M))` (eq. (12.95)/(12.79)) those frame sums must be evaluated as
operator traces built from the codeword output `σ_M = ⨂ₚ i, σ i`, its conditional typical subspace
projector `P_M` (`State.condTypicalSubspaceProj`, N&C eq. (12.75)), and the typical projector `P`.
This file provides the three single-family lemmas that perform that evaluation.

Fix a finite family of output states `σ : (i : ι) → State (S i)` (a codeword's channel-output
factors, `n = |ι|`), with product state `σ_M = ⨂ₚ i, σ i` diagonal in the product eigenbasis
`|E_κ⟩ = State.piTensorEigenbasis σ κ` with eigenvalue `λ_κ = ∏ᵢ λ_{i,κᵢ}`
(`State.piTensor_op_apply_piTensorEigenbasis`), and conditional typical set
`T = Real.condTypicalSeq (fun i ↦ (σ i).eigenvalueDist) s ε` (N&C eq. (12.75)).

## Main results

* `State.condTypicalSubspaceProj_comp_piTensor_op_eq_sum` — the **eigendecomposition of the
  typical-truncated codeword** `P_M ∘ σ_M = ∑_{κ ∈ T} λ_κ |E_κ⟩⟨E_κ|`: composing the conditional
  typical projector with the codeword keeps exactly its typical eigenvalue-weighted rank-one terms.
* `State.re_trace_comp_condTypicalSubspaceProj_comp_piTensor` — the **spur evaluator**: for any
  operator `B`,

  `re tr(B ∘ P_M ∘ σ_M)  =  ∑_{κ ∈ T} λ_κ · re⟪E_κ, B E_κ⟫`,

  the weighted diagonal of `B` over the typical eigenvectors.  Its `B = 1` case is the
  conditional-typical probability `re tr(P_M ∘ σ_M) = ∑_{κ ∈ T} λ_κ`
  (`State.re_trace_condTypicalSubspaceProj_comp_piTensor`, N&C eq. (12.76)); the general form is
  what N&C's spur substitution needs, since eq. (12.94) evaluates traces against the typical
  projector `P` and the cross-message confusion operators `P P_{M'} P`.
* `State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum` — the **compressed-eigenvector frame
  operator** `A ∘ P_M ∘ A⋆ = ∑_{κ ∈ T} |A E_κ⟩⟨A E_κ|`: conjugating `P_M` by an operator `A` yields
  the sum of rank-one projectors onto the compressed eigenvectors `A|E_κ⟩`.  With `A = P` this is
  N&C's `P P_{M'} P = ∑_{κ' ∈ T_{M'}} |Ẽ_{κ'}^{M'}⟩⟨Ẽ_{κ'}^{M'}|`, the frame operator of the
  compressed typical codeword eigenvectors underlying the confusion term `tr(P σ_M P P_{M'})`.
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → QSystem}

/-- **Eigendecomposition of the typical-truncated codeword** (Nielsen & Chuang, Theorem 12.8, the
object of Box 12.5's spur calculation).  Composing the conditional typical subspace projector `P_M`
with the product codeword `σ_M = ⨂ₚ i, σ i` keeps exactly the eigenvalue-weighted rank-one terms of
the *typical* eigenvectors:

`P_M ∘ σ_M  =  ∑_{κ ∈ T} λ_κ |E_κ⟩⟨E_κ|`,   `λ_κ = ∏ᵢ λ_{i,κᵢ}`,

where `T = Real.condTypicalSeq (fun i ↦ (σ i).eigenvalueDist) s ε` (N&C eq. (12.75)) and
`|E_κ⟩ = State.piTensorEigenbasis σ κ`.  The conditional typical projector is the sum of the typical
rank-one projectors `P_M = ∑_{κ ∈ T} |E_κ⟩⟨E_κ|` (`State.condTypicalSubspaceProj`,
`InnerProductSpace.orthonormalProjector`); composing each `|E_κ⟩⟨E_κ|` on the right with the
self-adjoint `σ_M` (`InnerProductSpace.rankOne_comp`, `State.isSelfAdjoint_op`) contracts the second
slot against `σ_M |E_κ⟩ = λ_κ |E_κ⟩` (`State.piTensor_op_apply_piTensorEigenbasis`), and the real
eigenvalue passes out of the conjugate-linear slot. -/
theorem State.condTypicalSubspaceProj_comp_piTensor_op_eq_sum (σ : (i : ι) → State (S i))
    (s ε : ℝ) :
    (State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op
      = ∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
          ((∏ i, (σ i).eigenvalueDist (κ i) : ℝ) : ℂ) •
            rankOne ℂ (State.piTensorEigenbasis σ κ) (State.piTensorEigenbasis σ κ) := by
  rw [State.condTypicalSubspaceProj, InnerProductSpace.orthonormalProjector,
    ContinuousLinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [InnerProductSpace.rankOne_comp, (State.isSelfAdjoint_op (State.piTensor σ)).adjoint_eq,
    State.piTensor_op_apply_piTensorEigenbasis]
  ext z
  simp only [rankOne_apply, FunLike.coe_smul, Pi.smul_apply, inner_smul_left,
    Complex.conj_ofReal, smul_smul]

/-- **The spur evaluator** (Nielsen & Chuang, Theorem 12.8, the trace-evaluation core of Box 12.5's
eqs. (12.94)→(12.95)).  For any operator `B` on the codeword space, the real trace of `B` against
the typical-truncated codeword `P_M ∘ σ_M` is the eigenvalue-weighted diagonal of `B` over the
typical eigenvectors:

`re tr(B ∘ P_M ∘ σ_M)  =  ∑_{κ ∈ T} λ_κ · re⟪E_κ, B E_κ⟫`.

The `B = 1` case recovers the conditional-typical probability
`re tr(P_M ∘ σ_M) = ∑_{κ ∈ T} λ_κ` (`State.re_trace_condTypicalSubspaceProj_comp_piTensor`, N&C
eq. (12.76)).  The general form is exactly what N&C's spur substitution (12.94)→(12.95) needs: with
`B = P` (typical projector) it evaluates `∑ λ_κ ‖P E_κ‖²`, and with `B = P P_{M'} P` the
cross-message confusion sums.  Proof: `P_M ∘ σ_M` is the eigenvalue-weighted rank-one sum
(`State.condTypicalSubspaceProj_comp_piTensor_op_eq_sum`), against which the trace of `B` splits as
`∑_κ λ_κ ⟪E_κ, B E_κ⟫` (`InnerProductSpace.trace_comp_sum_smul_rankOne_self`); the real eigenvalues
factor out of the real part. -/
theorem State.re_trace_comp_condTypicalSubspaceProj_comp_piTensor (σ : (i : ι) → State (S i))
    (s ε : ℝ) (B : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space) :
    RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
        (B.comp ((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op) : _ →ₗ[ℂ] _))
      = ∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
          (∏ i, (σ i).eigenvalueDist (κ i)) *
            RCLike.re (inner ℂ (State.piTensorEigenbasis σ κ)
              (B (State.piTensorEigenbasis σ κ))) := by
  -- The eigenvalue-weighted rank-one sum, traced against `B`, splits termwise by the general
  -- `Finset` form of `InnerProductSpace.trace_comp_sum_smul_rankOne_self`; the real eigenvalues
  -- then factor out of the real part.
  rw [State.condTypicalSubspaceProj_comp_piTensor_op_eq_sum,
    InnerProductSpace.trace_comp_sum_smul_rankOne_self, map_sum]
  exact Finset.sum_congr rfl fun κ _ => Complex.re_ofReal_mul _ _

/-- **The compressed-eigenvector frame operator** (Nielsen & Chuang, Theorem 12.8, Box 12.5).
Conjugating the conditional typical subspace projector `P_M` by an operator `A` yields the sum of
rank-one projectors onto the compressed eigenvectors `A|E_κ⟩`:

`A ∘ P_M ∘ A⋆  =  ∑_{κ ∈ T} |A E_κ⟩⟨A E_κ|`.

With `A = P` the typical projector, the right-hand side is N&C's frame operator of the
compressed codeword eigenvectors `|Ẽ_κ⟩ = P|E_κ⟩`, so the left-hand side is
`P P_{M'} P = ∑_{κ' ∈ T_{M'}} |Ẽ_{κ'}^{M'}⟩⟨Ẽ_{κ'}^{M'}|`, the operator whose weighted diagonal is
the confusion term `tr(P σ_M P P_{M'})` of eq. (12.95).  Proof: `P_M = ∑_{κ ∈ T} |E_κ⟩⟨E_κ|`
(`State.condTypicalSubspaceProj`, `InnerProductSpace.orthonormalProjector`); conjugation distributes
over the sum, and `A |E_κ⟩⟨E_κ| A⋆ = |A E_κ⟩⟨A E_κ|` termwise
(`ContinuousLinearMap.comp_rankOne_self_comp_adjoint`). -/
theorem State.comp_condTypicalSubspaceProj_comp_adjoint_eq_sum (σ : (i : ι) → State (S i)) (s ε : ℝ)
    (A : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space) :
    A.comp ((State.condTypicalSubspaceProj σ s ε).comp (adjoint A))
      = ∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
          rankOne ℂ (A (State.piTensorEigenbasis σ κ)) (A (State.piTensorEigenbasis σ κ)) := by
  rw [State.condTypicalSubspaceProj, InnerProductSpace.orthonormalProjector,
    ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [ContinuousLinearMap.comp_rankOne_self_comp_adjoint]

end AxQM
