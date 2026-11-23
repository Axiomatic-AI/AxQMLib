/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PiTensorEigenbasis
import ToMathlib.InformationTheory.ConditionalTypicalSequence

/-!
# AxQM.Postulates.API — the conditional typical subspace `P_M` (N&C Eqs. 12.74–77)

The infrastructure for the **conditional typical subspace** of a product codeword in
Nielsen & Chuang's proof of the Holevo–Schumacher–Westmoreland theorem (Theorem 12.8, random-coding
achievability). Alice's codeword for a message `M` produces the channel output
`σ_M = σ_{M₁} ⊗ ⋯ ⊗ σ_{Mₙ}` — an `n`-fold product of *different* output states `σ_{Mᵢ} = E(ρ_{Mᵢ})`
drawn from the input ensemble. Its typical subspace therefore cannot be read off the tensor-power
typical subspace `State.typicalSubspaceProj` (`Postulates/API/TypicalSubspace.lean`), which needs a
single repeated state; it must use the **product eigenbasis** of the distinct factors,
`State.piTensorEigenbasis` (`Postulates/API/PiTensorEigenbasis.lean`).

Fix a finite family of quantum states `σ : (i : ι) → State (S i)` (the codeword's output factors,
`n = |ι|`). Each `σ i = ∑ₖ λᵢₖ |eᵢₖ⟩⟨eᵢₖ|` has eigenvalue distribution `λᵢ = (σ i).eigenvalueDist`,
so the product state `⨂ₚ i, σ i` is diagonal in the product eigenbasis `|E_κ⟩ = ⨂ᵢ |e_{i,κᵢ}⟩` with
eigenvalue `λ_κ = ∏ᵢ λ_{i,κᵢ}` (`State.piTensor_op_apply_piTensorEigenbasis`). N&C's *conditional*
typical set `T_M` (Eq. 12.75) — the `κ` with `|(1/n)∑ᵢ -log λ_{i,κᵢ} - S̄| ≤ ε`, `S̄ = ∑ⱼ pⱼ S(σⱼ)`
— is then exactly the classical `Real.condTypicalSeq λ S̄ ε` of the per-factor spectra, and the
conditional typical *subspace* projector is its `orthonormalProjector`.

## Main definitions and results

* `State.condTypicalSubspaceProj σ s ε` — the **conditional typical subspace projector** `P_M`
  (N&C Eq. 12.75): the orthogonal projector onto the span of the product eigenvectors `|E_κ⟩` whose
  index sequence `κ` is `(s, ε)`-typical for the per-factor eigenvalue distributions.
* `State.condTypicalSubspaceDim σ s ε` — the **rank** of `P_M`, a natural number,
  namely the cardinality of the conditional typical set.
* `State.trace_condTypicalSubspaceProj_eq_condTypicalSubspaceDim` — `tr(P_M) = dim` (a projector's
  trace is its rank).
* `State.condTypicalSubspaceDim_le` — **the dimension bound** (N&C Eq. 12.77):
  `dim(P_M) ≤ exp (n (s + ε))`, a *deterministic* bound holding for every codeword `M` (with
  `s = S̄` the ensemble-average entropy, this is N&C's `tr(P_M) ≤ 2^{n(S̄+ε)}`). Immediate from the
  classical
  `Real.card_condTypicalSeq_le`, the per-factor spectra being probability distributions.
* `State.condTypicalSubspaceProj_isSelfAdjoint` / `State.condTypicalSubspaceProj_idem` — `P_M` is a
  self-adjoint idempotent (an orthonormal projector), as the pretty-good decoder `E_M` (Eq. 12.78)
  built from the `P_M` requires.

The distinct-factor generalisation of the tensor-power typical subspace `State.typicalSubspaceProj`
(which is this projector for a constant family `σ i = ρ`). The random-coding *expectation* estimate
`E(tr(σ_M (I − P_M))) ≤ δ` (N&C Eq. 12.76), which needs the law of large numbers over the codeword
distribution, is a separate ingredient and is not part of this deterministic core.

Compare its constant-family sibling `AxQM/Postulates/API/TypicalSubspace.lean`.
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → QSystem}

/-- **The conditional typical subspace projector** `P_M` (Nielsen & Chuang, Theorem 12.8,
Eq. 12.75): the orthogonal projector onto the conditional typical subspace of the product codeword
`σ_M = ⨂ₚ i, σ i`, spanned by the product eigenvectors `|E_κ⟩ = ⨂ᵢ |e_{i,κᵢ}⟩`
(`State.piTensorEigenbasis`) whose index sequence `κ` is `(s, ε)`-typical for the per-factor
eigenvalue distributions `λᵢ = (σ i).eigenvalueDist`. Formally the
`InnerProductSpace.orthonormalProjector` of the product eigenbasis restricted to the classical
conditional typical set `Real.condTypicalSeq (fun i ↦ (σ i).eigenvalueDist) s ε`. The threshold `s`
is N&C's ensemble-average entropy `S̄ = ∑ⱼ pⱼ S(σⱼ)`; kept general here. The distinct-factor
generalisation of `State.typicalSubspaceProj` (this projector for a constant family). -/
def State.condTypicalSubspaceProj (σ : (i : ι) → State (S i)) (s ε : ℝ) :
    (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space :=
  orthonormalProjector ℂ (⇑(State.piTensorEigenbasis σ))
    (Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε)

/-- **The dimension of the conditional typical subspace** (Nielsen & Chuang, Theorem 12.8): the rank
of `P_M`, i.e. the number of `(s, ε)`-typical index sequences `κ`. A natural number, so the
dimension bound (Eq. 12.77) can be stated for it without the trace. Definitionally the
cardinality of the conditional typical set; equal to `tr(P_M)` via
`trace_condTypicalSubspaceProj_eq_condTypicalSubspaceDim`. -/
def State.condTypicalSubspaceDim (σ : (i : ι) → State (S i)) (s ε : ℝ) : ℕ :=
  (Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε).card

/-- **`tr(P_M) = dim(P_M)`**: the trace of the conditional typical subspace projector equals its
rank (the number of typical sequences). Immediate from the general projector-trace identity
`InnerProductSpace.trace_orthonormalProjector` (trace of `∑_{κ ∈ s} |E_κ⟩⟨E_κ|` is `|s|`), applied
to the product eigenbasis and the conditional typical index set. -/
theorem State.trace_condTypicalSubspaceProj_eq_condTypicalSubspaceDim (σ : (i : ι) → State (S i))
    (s ε : ℝ) :
    LinearMap.trace ℂ (QSystem.piTensor S).space
        (State.condTypicalSubspaceProj σ s ε : _ →ₗ[ℂ] _)
      = (State.condTypicalSubspaceDim σ s ε : ℂ) := by
  rw [State.condTypicalSubspaceProj, trace_orthonormalProjector, State.condTypicalSubspaceDim]

/-- **The dimension bound of the conditional typical subspace** (Nielsen & Chuang, Theorem 12.8,
Eq. 12.77): `dim(P_M) ≤ exp (n (s + ε))`, `n = |ι|`. A *deterministic* bound — it holds for every
codeword `M`, needing only that each per-factor spectrum `(σ i).eigenvalueDist` is a probability
distribution (`eigenvalueDist_nonneg`, `eigenvalueDist_sum_eq_one`). With `s = S̄ = ∑ⱼ pⱼ S(σⱼ)`
this is N&C's `tr(P_M) ≤ 2^{n(S̄+ε)}` (natural-log/nats convention). The quantum face of the
classical
`Real.card_condTypicalSeq_le`. -/
theorem State.condTypicalSubspaceDim_le (σ : (i : ι) → State (S i)) (s ε : ℝ) :
    (State.condTypicalSubspaceDim σ s ε : ℝ) ≤ Real.exp ((Fintype.card ι : ℝ) * (s + ε)) := by
  rw [State.condTypicalSubspaceDim]
  exact Real.card_condTypicalSeq_le (fun i b => (σ i).eigenvalueDist_nonneg b)
    (fun i => (σ i).eigenvalueDist_sum_eq_one) s ε

/-- The conditional typical subspace projector `P_M` is **self-adjoint** (it is an orthonormal
projector). -/
theorem State.condTypicalSubspaceProj_isSelfAdjoint (σ : (i : ι) → State (S i)) (s ε : ℝ) :
    IsSelfAdjoint (State.condTypicalSubspaceProj σ s ε) :=
  isSelfAdjoint_orthonormalProjector _ _

/-- The conditional typical subspace projector `P_M` is **idempotent**, `P_M ∘ P_M = P_M` (it is an
orthonormal projector). -/
theorem State.condTypicalSubspaceProj_idem (σ : (i : ι) → State (S i)) (s ε : ℝ) :
    (State.condTypicalSubspaceProj σ s ε).comp (State.condTypicalSubspaceProj σ s ε)
      = State.condTypicalSubspaceProj σ s ε :=
  isIdempotentElem_orthonormalProjector (State.piTensorEigenbasis σ).orthonormal _

/-- The conditional typical subspace projector `P_M` is a **positive** operator (it is a
self-adjoint idempotent, hence `≥ 0` in the Loewner order). -/
theorem State.condTypicalSubspaceProj_isPositive (σ : (i : ι) → State (S i)) (s ε : ℝ) :
    (State.condTypicalSubspaceProj σ s ε).IsPositive :=
  (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
      (State.condTypicalSubspaceProj_idem σ s ε)).mpr
    (State.condTypicalSubspaceProj_isSelfAdjoint σ s ε)

/-- **The conditional-typical probability of a product codeword** (Nielsen & Chuang, Theorem 12.8,
the object of Eq. 12.76): the trace of the product output state `σ_M = ⨂ₚ i, σ i` against its
conditional typical subspace projector `P_M` is the classical probability mass of the conditional
typical set,

`tr(σ_M P_M)  =  ∑_{κ ∈ T_M} ∏ᵢ λ_{i,κᵢ}`,

the total probability that a run of independent draws `κᵢ ∼ (σ i).eigenvalueDist` lands in the
conditional typical set `T_M`. (Written here as `tr(P_M ∘ σ_M)`, equal to `tr(σ_M P_M)` by
cyclicity.) This is the quantum→classical bridge behind the random-coding estimate
`E(tr(σ_M(I − P_M))) ≤ δ` (Eq. 12.76): it reduces the (a)typical-subspace weight of a codeword to
the classical `condTypicalProb`, on which the law of large numbers over the codeword distribution
then acts.

The distinct-factor generalisation of `State.typicalSubspaceMeasurement_bornProb_true`. Proof: the
projector-trace lemma `InnerProductSpace.trace_orthonormalProjector_comp` restricts `tr(P_M σ_M)` to
the conditional-typical diagonal `∑_{κ ∈ T_M} ⟪E_κ, σ_M E_κ⟫`, and `σ_M` is diagonal there with
eigenvalue `∏ᵢ λ_{i,κᵢ}` (`State.piTensor_op_apply_piTensorEigenbasis`). -/
theorem State.re_trace_condTypicalSubspaceProj_comp_piTensor (σ : (i : ι) → State (S i)) (s ε : ℝ) :
    RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
        ((State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op : _ →ₗ[ℂ] _))
      = ∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
          ∏ i, (σ i).eigenvalueDist (κ i) := by
  rw [State.condTypicalSubspaceProj, trace_orthonormalProjector_comp]
  have hterm : ∀ κ, inner ℂ (State.piTensorEigenbasis σ κ)
        ((State.piTensor σ).op (State.piTensorEigenbasis σ κ))
      = ((∏ i, (σ i).eigenvalueDist (κ i) : ℝ) : ℂ) := by
    intro κ
    rw [State.piTensor_op_apply_piTensorEigenbasis, inner_smul_right,
      orthonormal_iff_ite.mp (State.piTensorEigenbasis σ).orthonormal, ite_eq_left rfl, mul_one]
  rw [Finset.sum_congr rfl (fun κ _ => hterm κ), ← Complex.ofReal_sum]
  exact Complex.ofReal_re _

/-- **The atypical weight of a product codeword** (Nielsen & Chuang, Theorem 12.8, the left side of
Eq. 12.76): the weight of the product output state `σ_M` outside its conditional typical subspace is
one minus the conditional-typical probability,

`tr(σ_M (I − P_M))  =  1 − ∑_{κ ∈ T_M} ∏ᵢ λ_{i,κᵢ}`.

Immediate from `State.re_trace_condTypicalSubspaceProj_comp_piTensor` and the unit trace
`State.trace_op_eq_one` (`tr(σ_M) = 1`): the trace is linear over `(I − P_M)`, and `re` of the real
scalar `1` is `1`. This is exactly N&C's `tr(σ_M(I − P_M))`, whose random-coding expectation is
bounded by `δ` (Eq. 12.76) once the law of large numbers is applied to the classical
`1 − condTypicalProb`. -/
theorem State.re_trace_one_sub_condTypicalSubspaceProj_comp_piTensor (σ : (i : ι) → State (S i))
    (s ε : ℝ) :
    RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor S).space)
        (((1 : (QSystem.piTensor S).space →L[ℂ] (QSystem.piTensor S).space)
              - State.condTypicalSubspaceProj σ s ε).comp (State.piTensor σ).op : _ →ₗ[ℂ] _))
      = 1 - ∑ κ ∈ Real.condTypicalSeq (fun i => (σ i).eigenvalueDist) s ε,
          ∏ i, (σ i).eigenvalueDist (κ i) := by
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.toLinearMap_sub, map_sub, State.trace_op_eq_one, map_sub, RCLike.one_re,
    State.re_trace_condTypicalSubspaceProj_comp_piTensor]

end AxQM
