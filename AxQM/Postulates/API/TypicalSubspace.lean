/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TensorPowState
import AxQM.Postulates.API.MeasurementModel
import AxQM.Postulates.API.EntropySpectral
import ToMathlib.InformationTheory.TypicalSequence
import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelityBound

/-!
# AxQM.Postulates.API — the ε-typical subspace projector `P(n, ε)` (N&C Thm 12.5)

This file concerns Nielsen & Chuang's **typical subspace theorem** (Theorem 12.5): the ε-typical
subspace projector `P(n, ε)`, its rank/trace identities, and its realization as a projective
measurement whose Born probability is the classical typicality probability.

Fix a quantum state `ρ : State S` with spectral decomposition `ρ = ∑ₓ λ(x) |eₓ⟩⟨eₓ|` (eigenbasis
`e = ρ.isDensity.isSymmetric.eigenvectorBasis`, eigenvalue distribution `λ = ρ.eigenvalueDist`). The
eigenvalues `λ` are a probability distribution (`eigenvalueDist_nonneg`,
`eigenvalueDist_sum_eq_one`) with `H(λ) = S(ρ)` (`vonNeumannEntropy_eq_entropy_eigenvalueDist`), so
the classical notion of an
ε-typical sequence `κ : Fin n → Fin d` of eigenvalue indices — `κ ∈ Real.typicalSeq λ n ε`
(N&C's `|(1/n) log(1/∏ λ(κᵢ)) − S(ρ)| ≤ ε`, Eq. 12.41) — applies verbatim to the spectrum.

* `State.typicalSubspaceProj ρ n ε` — the **ε-typical subspace projector** `P(n, ε)` (N&C Eq.
  12.42): the orthogonal projector onto the span of the product eigenvectors `|e_κ⟩` whose index
  sequence `κ` is ε-typical, i.e. `InnerProductSpace.orthonormalProjector` of `ρ`'s product
  eigenbasis (`State.tensorPowEigenbasis`) restricted to `Real.typicalSeq λ n ε`.
* `State.trace_typicalSubspaceProj_eq_card` — the **dimension identity** `tr(P(n, ε)) = |T(n, ε)|`
  (N&C's `|T(n, ε)| = tr(P(n, ε))`): the trace of `P` is the number of ε-typical sequences.
* `State.typicalSubspaceMeasurement ρ n ε` — `P(n, ε)` packaged as the **two-outcome projective
  measurement** `{P(n, ε), I − P(n, ε)}` (`Measurement.ofOrthonormalBasisFiber`, outcome `true` =
  "found in the typical subspace"), with `typicalSubspaceMeasurement_op_true` identifying its
  `true`-projector with `P(n, ε)`.
* `State.typicalSubspaceMeasurement_bornProb_true` — the **Born-probability identity** (N&C Eq.
  12.46): the probability of the outcome `true` on `ρ^⊗n` is the classical typicality probability
  `tr(P(n, ε) ρ^⊗n) = ∑_{κ ∈ T(n, ε)} ∏ᵢ λ(κᵢ)`.

Together these are the bridge that reduces the *quantum* typical subspace theorem to the *classical*
theorem of typical sequences (N&C Theorem 12.2, `ToMathlib.InformationTheory.TypicalSequence`)
applied
to the eigenvalue distribution `λ`. Part (1) of Theorem 12.5 (`tr(P ρ^⊗n) ≥ 1 − δ`) is the
`bornProb` identity fed into `Real.exists_le_sum_typicalSeq`; part (2) (the dimension bounds) is the
`trace = card` identity fed into `Real.exists_card_typicalSeq_bounds`. Those consequences are in
`AxQM/NC/Ch12/Theorem12_5.lean`.
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The eigenvalue distribution of a state -/

/-- The **eigenvalue distribution** `λ : Fin d → ℝ` (`d = dim S.space`) of a quantum state `ρ`: the
spectrum of the density operator, indexed by `ρ`'s canonical eigenbasis
(`ρ.isDensity.isSymmetric.eigenvalues`). It is a genuine probability distribution
(`eigenvalueDist_nonneg`, `eigenvalueDist_sum_eq_one`) whose Shannon entropy is the von Neumann
entropy `S(ρ)` (`vonNeumannEntropy_eq_entropy_eigenvalueDist`) — the classical distribution N&C's
typical subspace theorem is reduced to. -/
def State.eigenvalueDist (ρ : State S) : Fin (Module.finrank ℂ S.space) → ℝ :=
  ρ.isDensity.isSymmetric.eigenvalues rfl

/-- The eigenvalues of a state are non-negative (the density operator is positive). -/
theorem State.eigenvalueDist_nonneg (ρ : State S) (i : Fin (Module.finrank ℂ S.space)) :
    0 ≤ ρ.eigenvalueDist i :=
  ρ.isDensity.eigenvalues_nonneg rfl i

/-- The eigenvalues of a state sum to one (the density operator has unit trace). -/
theorem State.eigenvalueDist_sum_eq_one (ρ : State S) : ∑ i, ρ.eigenvalueDist i = 1 :=
  ρ.isDensity.eigenvalues_sum_eq_one rfl

/-- **The entropy bridge** (N&C: `H(p(x)) = S(ρ)`): the Shannon entropy of a state's eigenvalue
distribution is its von Neumann entropy. This is what turns the classical typical-sequences bounds
(stated over `Real.entropy λ`) into the quantum `S(ρ)` bounds of the typical subspace theorem. -/
theorem State.vonNeumannEntropy_eq_entropy_eigenvalueDist (ρ : State S) :
    ρ.vonNeumannEntropy = Real.entropy ρ.eigenvalueDist :=
  ρ.vonNeumannEntropy_eq_entropy_of_isEigenbasis (ρ.isDensity.isSymmetric.eigenvectorBasis rfl)
    (fun i => ρ.op_apply_eigenvectorBasis i)

/-! ### The ε-typical subspace projector -/

/-- **The ε-typical subspace projector** `P(n, ε)` (Nielsen & Chuang, Theorem 12.5, Eq. 12.42): the
orthogonal projector onto the ε-typical subspace `T(n, ε)` of `ρ^⊗n`, spanned by the product
eigenvectors `|e_κ⟩ = ⨂ᵢ |e_{κᵢ}⟩` whose index sequence `κ` is ε-typical for the eigenvalue
distribution `λ = ρ.eigenvalueDist`. Formally the `InnerProductSpace.orthonormalProjector` of `ρ`'s
product eigenbasis (`State.tensorPowEigenbasis`) restricted to the classical ε-typical set
`Real.typicalSeq λ n ε`. -/
def State.typicalSubspaceProj (ρ : State S) (n : ℕ) (ε : ℝ) :
    (S ^⊗ₛ n).space →L[ℂ] (S ^⊗ₛ n).space :=
  orthonormalProjector ℂ (⇑(ρ.tensorPowEigenbasis n)) (Real.typicalSeq ρ.eigenvalueDist n ε)

/-- **The dimension of the typical subspace equals the number of typical sequences** (Nielsen &
Chuang, Theorem 12.5: `|T(n, ε)| = tr(P(n, ε))`): the trace of the ε-typical projector is the
cardinality of the classical ε-typical set. Immediate from the general projector-trace identity
`InnerProductSpace.trace_orthonormalProjector` (trace of `∑_{i ∈ s} |bᵢ⟩⟨bᵢ|` is `|s|`), applied to
the product eigenbasis and the ε-typical index set. -/
theorem State.trace_typicalSubspaceProj_eq_card (ρ : State S) (n : ℕ) (ε : ℝ) :
    LinearMap.trace ℂ (S ^⊗ₛ n).space (ρ.typicalSubspaceProj n ε : _ →ₗ[ℂ] _)
      = ((Real.typicalSeq ρ.eigenvalueDist n ε).card : ℂ) := by
  rw [State.typicalSubspaceProj, trace_orthonormalProjector]

/-- The **dimension of the ε-typical subspace** `|T(n, ε)|` (Nielsen & Chuang, Theorem 12.5, part
(2)): the number of ε-typical index sequences `κ ∈ Real.typicalSeq λ n ε`, equivalently the rank of
`P(n, ε)`. It is an `ℕ`-valued quantity, so the part-(2) dimension bounds can be stated over it
without the `LinearMap.trace`/`OrthonormalBasis` machinery. N&C's identity
`|T(n, ε)| = tr(P(n, ε))` is `trace_typicalSubspaceProj_eq_typicalSubspaceDim`. -/
def State.typicalSubspaceDim (ρ : State S) (n : ℕ) (ε : ℝ) : ℕ :=
  (Real.typicalSeq ρ.eigenvalueDist n ε).card

/-- **`|T(n, ε)| = tr(P(n, ε))`** (Nielsen & Chuang, Theorem 12.5, part (2)): the dimension of the
ε-typical subspace equals the trace of its projector. A restatement of
`trace_typicalSubspaceProj_eq_card` in terms of the dimension `typicalSubspaceDim`
(definitionally its cardinality), N&C's identity `|T(n, ε)| = tr(P(n, ε))`. -/
theorem State.trace_typicalSubspaceProj_eq_typicalSubspaceDim (ρ : State S) (n : ℕ) (ε : ℝ) :
    LinearMap.trace ℂ (S ^⊗ₛ n).space (ρ.typicalSubspaceProj n ε : _ →ₗ[ℂ] _)
      = (ρ.typicalSubspaceDim n ε : ℂ) :=
  ρ.trace_typicalSubspaceProj_eq_card n ε

/-! ### The typical subspace as a projective measurement -/

/-- **The typical/atypical projective measurement** `{P(n, ε), I − P(n, ε)}` (Nielsen & Chuang,
Theorem 12.5): the two-outcome von Neumann measurement asking whether `ρ^⊗n` lies in the ε-typical
subspace. Built as `Measurement.ofOrthonormalBasisFiber` of the product eigenbasis with the Boolean
fibre `κ ↦ (κ ∈ T(n, ε))`; outcome `true` is the ε-typical outcome, with projector `P(n, ε)`
(`typicalSubspaceMeasurement_op_true`). -/
def State.typicalSubspaceMeasurement (ρ : State S) (n : ℕ) (ε : ℝ) :
    Measurement Bool (S ^⊗ₛ n) :=
  Measurement.ofOrthonormalBasisFiber (ρ.tensorPowEigenbasis n)
    (fun κ => decide (κ ∈ Real.typicalSeq ρ.eigenvalueDist n ε))

/-- The `true`-outcome projector of the typical subspace measurement is the ε-typical subspace
projector `P(n, ε)`: the fibre `{κ | (κ ∈ T(n, ε)) = true}` is exactly the typical set `T(n, ε)`. -/
theorem State.typicalSubspaceMeasurement_op_true (ρ : State S) (n : ℕ) (ε : ℝ) :
    (ρ.typicalSubspaceMeasurement n ε).op true = ρ.typicalSubspaceProj n ε := by
  rw [State.typicalSubspaceMeasurement, Measurement.ofOrthonormalBasisFiber_op,
    State.typicalSubspaceProj]
  congr 1
  ext κ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

/-- **The Born probability of the typical subspace equals the classical typicality probability**
(Nielsen & Chuang, Theorem 12.5, Eq. 12.46): the probability of the ε-typical outcome on `ρ^⊗n` is
`tr(P(n, ε) ρ^⊗n) = ∑_{κ ∈ T(n, ε)} ∏ᵢ λ(κᵢ)`, the total probability the classical i.i.d. source
with distribution `λ` emits an ε-typical sequence.

Proof: the Born probability is `re tr(P† P ρ^⊗n)` (`bornProb_eq_re_trace_postOp`,
`trace_postOp`), which collapses to `re tr(P ρ^⊗n)` since `P` is a self-adjoint idempotent. The
projector-trace lemma `InnerProductSpace.trace_orthonormalProjector_comp` restricts `tr(P ρ^⊗n)` to
the ε-typical diagonal `∑_{κ typical} ⟪e_κ, ρ^⊗n e_κ⟫`, and `ρ^⊗n` is diagonal there with eigenvalue
`∏ᵢ λ(κᵢ)` (`tensorPow_op_apply_tensorPowEigenbasis`), giving `∑_{κ typical} ∏ᵢ λ(κᵢ)`. -/
theorem State.typicalSubspaceMeasurement_bornProb_true (ρ : State S) (n : ℕ) (ε : ℝ) :
    (ρ.typicalSubspaceMeasurement n ε).bornProb (ρ.tensorPow n) true
      = ∑ κ ∈ Real.typicalSeq ρ.eigenvalueDist n ε, ∏ i, ρ.eigenvalueDist (κ i) := by
  rw [Measurement.bornProb_eq_re_trace_postOp, ContinuousLinearMap.trace_postOp,
    State.typicalSubspaceMeasurement_op_true, State.typicalSubspaceProj,
    ← ContinuousLinearMap.comp_assoc,
    orthonormalProjector_adjoint_comp_self (ρ.tensorPowEigenbasis n).orthonormal,
    trace_orthonormalProjector_comp]
  -- The remaining sum runs over the typical eigenbasis diagonal `⟪e_κ, ρ^⊗n e_κ⟫ = ∏ᵢ λ(κᵢ)`.
  have hterm : ∀ κ,
      inner ℂ (ρ.tensorPowEigenbasis n κ) ((ρ.tensorPow n).op (ρ.tensorPowEigenbasis n κ))
        = ((∏ i, ρ.eigenvalueDist (κ i) : ℝ) : ℂ) := by
    intro κ
    rw [State.tensorPow_op_apply_tensorPowEigenbasis, inner_smul_right,
      orthonormal_iff_ite.mp (ρ.tensorPowEigenbasis n).orthonormal, ite_eq_left rfl, mul_one]
    rfl
  rw [Finset.sum_congr rfl (fun κ _ => hterm κ), ← Complex.ofReal_sum]
  exact Complex.ofReal_re _

/-- The ε-typical subspace projector `P(n, ε)` is **self-adjoint** (it is an orthonormal
projector). -/
theorem State.typicalSubspaceProj_isSelfAdjoint (ρ : State S) (n : ℕ) (ε : ℝ) :
    IsSelfAdjoint (ρ.typicalSubspaceProj n ε) :=
  isSelfAdjoint_orthonormalProjector _ _

/-- The ε-typical subspace projector `P(n, ε)` is **idempotent**, `P ∘ P = P` (it is an orthonormal
projector). -/
theorem State.typicalSubspaceProj_idem (ρ : State S) (n : ℕ) (ε : ℝ) :
    (ρ.typicalSubspaceProj n ε).comp (ρ.typicalSubspaceProj n ε) = ρ.typicalSubspaceProj n ε :=
  isIdempotentElem_orthonormalProjector (ρ.tensorPowEigenbasis n).orthonormal _

/-- **Born-rule bridge for the typical/atypical measurement**: on *any* state `τ` of `S ^⊗ₛ n`, the
ε-typical outcome probability is `re tr(P(n, ε) τ)`. (Generalizes the `ρ^⊗n`-specialized
`typicalSubspaceMeasurement_bornProb_true` to an arbitrary post-scheme state, as needed to certify
that a compressed output lands in the typical subspace.) Proof: `bornProb = re tr(P† P τ)`
(`bornProb_eq_re_trace_postOp`, `trace_postOp`), and `P† P = P` since `P` is a self-adjoint
idempotent. -/
theorem State.typicalSubspaceMeasurement_bornProb_eq_re_trace (ρ : State S) (n : ℕ) (ε : ℝ)
    (τ : State (S ^⊗ₛ n)) :
    (ρ.typicalSubspaceMeasurement n ε).bornProb τ true
      = RCLike.re ((LinearMap.trace ℂ (S ^⊗ₛ n).space)
          ((ρ.typicalSubspaceProj n ε).comp τ.op)) := by
  rw [Measurement.bornProb_eq_re_trace_postOp, ContinuousLinearMap.trace_postOp,
    State.typicalSubspaceMeasurement_op_true, (ρ.typicalSubspaceProj_isSelfAdjoint n ε).adjoint_eq,
    ← ContinuousLinearMap.comp_assoc, ρ.typicalSubspaceProj_idem n ε]

/-! ### The small-subspace bound: arbitrary bounded-rank projectors -/

/-- The **dimension of the "true"-outcome subspace** of a two-outcome measurement `M` on
`S ^⊗ₛ n`: the rank (`finrank` of the range) of the projector `M.op true`. An `ℕ`-valued
quantity, so the small-subspace bound of the typical subspace theorem (Nielsen & Chuang, Theorem
12.5, part (3)), quantifying over "any subspace of dimension at most `2^{nR}`", can be stated over
it. For a *projective* `M` it equals
the trace of the projector (`Measurement.trace_op_true_eq_trueSubspaceDim`). -/
def Measurement.trueSubspaceDim {n : ℕ} (M : Measurement Bool (S ^⊗ₛ n)) : ℕ :=
  Module.finrank ℂ (LinearMap.range (M.op true : (S ^⊗ₛ n).space →ₗ[ℂ] (S ^⊗ₛ n).space))

/-- For a **projective** two-outcome measurement, the trace of the `true`-outcome projector equals
the dimension of its subspace: `tr(M.op true) = trueSubspaceDim M`. A projector's trace is its rank
(`LinearMap.IsProj.trace`, via the idempotence of the star projection `M.op true`). -/
theorem Measurement.trace_op_true_eq_trueSubspaceDim {n : ℕ} (M : Measurement Bool (S ^⊗ₛ n))
    (hM : M.IsProjective) :
    LinearMap.trace ℂ (S ^⊗ₛ n) (M.op true : (S ^⊗ₛ n).space →ₗ[ℂ] (S ^⊗ₛ n).space)
      = (M.trueSubspaceDim : ℂ) := by
  have hidem : IsIdempotentElem (M.op true : (S ^⊗ₛ n).space →ₗ[ℂ] (S ^⊗ₛ n).space) := by
    rw [IsIdempotentElem, ← ContinuousLinearMap.toLinearMap_mul, (hM true).isIdempotentElem]
  rw [Measurement.trueSubspaceDim,
    LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hidem)]

/-- **Small-subspace reduction** (Nielsen & Chuang, Theorem 12.5, part (3), the operator step). For
a *projective* two-outcome measurement `M` on `S ^⊗ₛ n`, the Born probability of the `true` outcome
on `ρ^⊗n` is a classical *weighted* mass `∑_κ w κ · ∏ᵢ λ(κᵢ)` of the eigenvalue distribution
`λ = ρ.eigenvalueDist`, where the weights `w κ = ‖(M.op true) e_κ‖²` are the eigenbasis-diagonal
matrix elements `⟨e_κ, (M.op true) e_κ⟩` of the projector `M.op true`. They satisfy `0 ≤ w κ ≤ 1`
(the diagonal of a star projection) with total weight `∑_κ w κ = tr(M.op true) = trueSubspaceDim M`.

This is the bridge feeding the classical weighted small-set bound
(`Real.exists_sum_weighted_prod_le_of_sum_le_exp`): `bornProb true = re tr(M.op true · ρ^⊗n)`
(`bornProb_eq_re_trace_postOp`, `trace_postOp`, self-adjoint idempotence), expanded in the `ρ^⊗n`
eigenbasis (`LinearMap.trace_eq_sum_inner`), on which `ρ^⊗n` acts diagonally with eigenvalue
`∏ᵢ λ(κᵢ)` (`tensorPow_op_apply_tensorPowEigenbasis`). -/
theorem State.exists_weights_bornProb_true (ρ : State S) (n : ℕ)
    (M : Measurement Bool (S ^⊗ₛ n)) (hM : M.IsProjective) :
    ∃ w : (Fin n → Fin (Module.finrank ℂ S.space)) → ℝ,
      (∀ κ, 0 ≤ w κ) ∧ (∀ κ, w κ ≤ 1) ∧ (∑ κ, w κ = (M.trueSubspaceDim : ℝ)) ∧
        M.bornProb (ρ.tensorPow n) true = ∑ κ, w κ * ∏ i, ρ.eigenvalueDist (κ i) := by
  -- The complex diagonal element of the star projection `M.op true` is the (real) squared norm,
  -- `⟪e_κ, P e_κ⟫ = ‖P e_κ‖²` (`inner_self_of_isSelfAdjoint_of_isIdempotent`).
  have hpe : ∀ κ, inner ℂ (ρ.tensorPowEigenbasis n κ) ((M.op true) (ρ.tensorPowEigenbasis n κ))
      = ((‖(M.op true) (ρ.tensorPowEigenbasis n κ)‖ ^ 2 : ℝ) : ℂ) :=
    fun κ => inner_self_of_isSelfAdjoint_of_isIdempotent
      (hM true).isSelfAdjoint (hM true).isIdempotentElem (ρ.tensorPowEigenbasis n κ)
  refine ⟨fun κ => ‖(M.op true) (ρ.tensorPowEigenbasis n κ)‖ ^ 2, fun κ => sq_nonneg _, ?_, ?_, ?_⟩
  · -- `w κ ≤ 1`: a star projection is a contraction (`IsStarProjection.norm_le`), and `‖e_κ‖ = 1`.
    intro κ
    have hnx : ‖ρ.tensorPowEigenbasis n κ‖ = 1 := (ρ.tensorPowEigenbasis n).orthonormal.1 κ
    exact pow_le_one₀ (norm_nonneg _)
      (((M.op true).le_opNorm _).trans (by rw [hnx, mul_one]; exact (hM true).norm_le))
  · -- `∑ κ, w κ = tr(M.op true) = trueSubspaceDim`.
    have h1 : ((∑ κ, ‖(M.op true) (ρ.tensorPowEigenbasis n κ)‖ ^ 2 : ℝ) : ℂ)
        = (M.trueSubspaceDim : ℂ) := by
      rw [Complex.ofReal_sum, ← Measurement.trace_op_true_eq_trueSubspaceDim M hM,
        LinearMap.trace_eq_sum_inner _ (ρ.tensorPowEigenbasis n)]
      exact Finset.sum_congr rfl fun κ _ => (hpe κ).symm
    exact_mod_cast h1
  · -- `bornProb true = ∑ κ, w κ · ∏ᵢ λ(κᵢ)`.
    have hPadj : (ContinuousLinearMap.adjoint (M.op true)).comp (M.op true) = M.op true := by
      rw [← ContinuousLinearMap.star_eq_adjoint, (hM true).isSelfAdjoint,
        ← ContinuousLinearMap.mul_def]
      exact (hM true).isIdempotentElem
    rw [Measurement.bornProb_eq_re_trace_postOp, ContinuousLinearMap.trace_postOp,
      ← ContinuousLinearMap.comp_assoc, hPadj,
      LinearMap.trace_eq_sum_inner _ (ρ.tensorPowEigenbasis n)]
    have hterm : ∀ κ, inner ℂ (ρ.tensorPowEigenbasis n κ)
        (((M.op true).comp (ρ.tensorPow n).op : (S ^⊗ₛ n).space →ₗ[ℂ] (S ^⊗ₛ n).space)
          (ρ.tensorPowEigenbasis n κ))
        = ((‖(M.op true) (ρ.tensorPowEigenbasis n κ)‖ ^ 2 * ∏ i, ρ.eigenvalueDist (κ i) : ℝ)
            : ℂ) := by
      intro κ
      simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_coe,
        Function.comp_apply]
      rw [State.tensorPow_op_apply_tensorPowEigenbasis, map_smul, inner_smul_right, hpe κ]
      simp only [State.eigenvalueDist]
      push_cast; ring
    rw [Finset.sum_congr rfl fun κ _ => hterm κ, ← Complex.ofReal_sum]
    exact Complex.ofReal_re _

end AxQM
