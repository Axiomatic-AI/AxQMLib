/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FidelityPure
import AxQM.Postulates.API.QuantumChannel
import AxQM.Postulates.API.Ensemble
import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelityBound

/-!
# AxQM.Postulates.API — the projection–reset compression channel

The Schumacher compression–decompression operation `Dₙ ∘ Cₙ` of Nielsen & Chuang §12.2.2
(eq. (12.50)) acts on a state `σ` by **projecting** onto a code subspace with projector `P`
(the typical subspace) and, on the orthogonal "failure" component, **resetting** to a fixed
codeword `|v₀⟩`:

`ℰ_P(σ) = P σ P + tr((1 − P) σ) · |v₀⟩⟨v₀|`.

This file records that operation for an *arbitrary* orthogonal projector `P` and unit vector `v₀`
— the **projection–reset channel** `projectionResetChannel` — together with the single facts
Exercise 12.8 needs from it:

* it is a genuine quantum channel (`projectionResetChannel_isChannel`), realised by the Kraus
  family `{P} ∪ {|v₀⟩⟨fᵢ|(1 − P)}` over any orthonormal basis `{fᵢ}` of the whole space;
* its **single-shot squared-fidelity lower bound** (`projectionResetChannel_fidelity_sq_ge`): for a
  pure input `|ψ⟩`,
  `‖⟨ψ, P ψ⟩‖² ≤ F(|ψ⟩, ℰ_P(|ψ⟩⟨ψ|))²`,
  i.e. the fidelity between the input and its compressed–decompressed image is at least the squared
  typical-subspace weight `(tr P|ψ⟩⟨ψ|)²`.

The bound is the heart of Schumacher's reliability argument in the *entanglement-fidelity*
sense and — after averaging over an i.i.d. ensemble (`NC/Ch12/Exercise12_8.lean`) — of
**Exercise 12.8**
(reliability in the *ensemble-average-fidelity* sense): the same projector `P` that makes
`tr(P ρ⊗ⁿ)` close to `1` (the typical subspace theorem) makes the average fidelity close to `1`.
Writing `ℰ_P(|ψ⟩⟨ψ|) = ∑ₒ Eₒ |ψ⟩⟨ψ| Eₒ†` as an operator sum, the squared fidelity is
`F² = ⟨ψ|ℰ_P(|ψ⟩⟨ψ|)|ψ⟩ = ∑ₒ ‖⟨ψ, Eₒ ψ⟩‖²`
(`ContinuousLinearMap.re_inner_krausSumₗ_rankOne_self`), and dropping every summand but the
`P`-term (all are `≥ 0`) leaves `‖⟨ψ, P ψ⟩‖²`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2, eq. (12.50); Exercise 12.8.
-/

open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **Kraus family of the projection–reset channel** for an orthogonal projector `P` and unit
codeword `v₀`, indexed by `Option (Fin d)` with `d = dim S.space`. The distinguished element
`none ↦ P` performs the projection onto the code subspace; the elements `some i ↦ |v₀⟩⟨fᵢ|(1 − P)`,
where `{fᵢ}` is the standard orthonormal basis of `S.space`, collapse the failure component
`(1 − P) S.space` onto the fixed codeword `|v₀⟩`. The completeness relation
`∑ₒ Eₒ† Eₒ = P + (1 − P) = 1` (`projectionResetKraus_completeness`) makes the operator sum
`ρ ↦ ∑ₒ Eₒ ρ Eₒ†` trace-preserving; the resulting map is `projectionResetChannel`. -/
def projectionResetKraus (P : S.space →L[ℂ] S.space) (v₀ : PureState S) :
    Option (Fin (Module.finrank ℂ S.space)) → (S.space →L[ℂ] S.space)
  | none => P
  | some i => (rankOne ℂ v₀.vec ((stdOrthonormalBasis ℂ S.space) i)).comp (1 - P)

/-- **The projection–reset Kraus family is trace-preserving:** `∑ₒ Eₒ† Eₒ = 1` for an orthogonal
projector `P` (`IsSelfAdjoint P`, `P ∘ P = P`) and a unit codeword `v₀`. The distinguished element
contributes `P† P = P` (self-adjointness and idempotence); the failure elements contribute
`∑ᵢ (1 − P) |fᵢ⟩⟨v₀|v₀⟩⟨fᵢ| (1 − P) = (1 − P) (∑ᵢ |fᵢ⟩⟨fᵢ|) (1 − P) = (1 − P) · 1 · (1 − P) = 1 − P`
(unit `v₀`, completeness of the orthonormal basis, idempotence of `1 − P`), and the two sum to
`P + (1 − P) = 1`. -/
theorem projectionResetKraus_completeness
    (P : S.space →L[ℂ] S.space) (hsa : IsSelfAdjoint P) (hidem : P.comp P = P)
    (v₀ : PureState S) :
    ∑ o, (adjoint (projectionResetKraus P v₀ o)).comp (projectionResetKraus P v₀ o) = 1 := by
  have hadj : adjoint P = P := hsa.adjoint_eq
  have hadj1 : adjoint (1 - P : S.space →L[ℂ] S.space) = 1 - P :=
    ((IsSelfAdjoint.one (R := S.space →L[ℂ] S.space)).sub hsa).adjoint_eq
  have hidem1 : (1 - P : S.space →L[ℂ] S.space).comp (1 - P) = 1 - P :=
    IsIdempotentElem.one_sub hidem
  have hsome : (∑ i, (adjoint (projectionResetKraus P v₀ (some i))).comp
        (projectionResetKraus P v₀ (some i))) = 1 - P := by
    have hterm : ∀ i, (adjoint (projectionResetKraus P v₀ (some i))).comp
        (projectionResetKraus P v₀ (some i)) =
        (1 - P).comp ((rankOne ℂ ((stdOrthonormalBasis ℂ S.space) i)
          ((stdOrthonormalBasis ℂ S.space) i)).comp (1 - P)) := by
      intro i
      simp only [projectionResetKraus]
      rw [ContinuousLinearMap.adjoint_comp, hadj1, InnerProductSpace.adjoint_rankOne,
        ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc
          (rankOne ℂ ((stdOrthonormalBasis ℂ S.space) i) v₀.vec),
        InnerProductSpace.rankOne_comp_rankOne, inner_self_eq_norm_sq_to_K, v₀.normalized]
      simp
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      ← ContinuousLinearMap.comp_finsetSum, ← ContinuousLinearMap.finsetSum_comp,
      OrthonormalBasis.sum_rankOne_eq_id, ContinuousLinearMap.id_comp, hidem1]
  rw [Fintype.sum_option, hsome]
  have hnone : (adjoint (projectionResetKraus P v₀ none)).comp (projectionResetKraus P v₀ none)
      = P := by
    simp only [projectionResetKraus]; rw [hadj, hidem]
  rw [hnone]
  abel

/-- **The projection–reset (Schumacher compression–decompression) channel** for an orthogonal
projector `P` and unit codeword `v₀`. On a state `σ` it returns
`ℰ_P(σ) = P σ P + tr((1 − P) σ) · |v₀⟩⟨v₀|` — Nielsen & Chuang eq. (12.50), realised here as the
operator sum `∑ₒ Eₒ σ Eₒ†` over the Kraus family `projectionResetKraus`. Trace-preservation of the
family (`projectionResetKraus_completeness`) sends density operators to density operators
(`ContinuousLinearMap.isDensityOp_krausSumₗ`), so the output is a genuine `State`. -/
def projectionResetChannel (P : S.space →L[ℂ] S.space) (hsa : IsSelfAdjoint P)
    (hidem : P.comp P = P) (v₀ : PureState S) (σ : State S) : State S where
  op := krausSumₗ (projectionResetKraus P v₀) σ.op
  isDensity :=
    ContinuousLinearMap.isDensityOp_krausSumₗ (projectionResetKraus P v₀)
      (projectionResetKraus_completeness P hsa hidem v₀) σ.isDensity

/-- The density operator of the projection–reset channel output is the Kraus operator sum
`∑ₒ Eₒ σ Eₒ†`. Definitional (unfolds the `op` field). -/
@[simp]
theorem projectionResetChannel_op (P : S.space →L[ℂ] S.space) (hsa : IsSelfAdjoint P)
    (hidem : P.comp P = P) (v₀ : PureState S) (σ : State S) :
    (projectionResetChannel P hsa hidem v₀ σ).op = krausSumₗ (projectionResetKraus P v₀) σ.op :=
  rfl

/-- **The projection–reset operation is a quantum channel** (CPTP map). The Kraus family
`projectionResetKraus` satisfies the completeness relation (`projectionResetKraus_completeness`),
so the operator sum `ρ ↦ ∑ₒ Eₒ ρ Eₒ†` is completely positive and trace-preserving
(`isChannel_of_kraus`). -/
theorem projectionResetChannel_isChannel (P : S.space →L[ℂ] S.space) (hsa : IsSelfAdjoint P)
    (hidem : P.comp P = P) (v₀ : PureState S) :
    IsChannel (projectionResetChannel P hsa hidem v₀) :=
  isChannel_of_kraus (projectionResetKraus P v₀)
    (projectionResetKraus_completeness P hsa hidem v₀) fun _ => rfl

/-- **Single-shot squared-fidelity lower bound for the projection–reset channel.** For an orthogonal
projector `P` (`IsSelfAdjoint P`, `P ∘ P = P`), a unit codeword `v₀`, and any pure input `|ψ⟩`, the
squared fidelity between the input and its compressed–decompressed image is at least the squared
overlap with the code subspace:

`‖⟨ψ, P ψ⟩‖² ≤ F(|ψ⟩, ℰ_P(|ψ⟩⟨ψ|))²`.

Since `⟨ψ, P ψ⟩ = tr(P |ψ⟩⟨ψ|)` is the weight of `|ψ⟩` inside the code subspace, this says the
scheme recovers a pure state with squared fidelity at least the squared typical-subspace weight —
the pointwise input to Schumacher's reliability argument and to Exercise 12.8.

Proof: `F² = ⟨ψ|ℰ_P(|ψ⟩⟨ψ|)|ψ⟩` (`State.fidelity_toState_sq`); the operator sum reads
`⟨ψ|ℰ_P(|ψ⟩⟨ψ|)|ψ⟩ = ∑ₒ ‖⟨ψ, Eₒ ψ⟩‖²`
(`ContinuousLinearMap.re_inner_krausSumₗ_rankOne_self`); every summand is `≥ 0`, so the total is at
least the distinguished `none ↦ P` term `‖⟨ψ, P ψ⟩‖²` (`Finset.single_le_sum`). -/
theorem projectionResetChannel_fidelity_sq_ge (P : S.space →L[ℂ] S.space) (hsa : IsSelfAdjoint P)
    (hidem : P.comp P = P) (v₀ : PureState S) (ψ : PureState S) :
    ‖inner ℂ ψ.vec (P ψ.vec)‖ ^ 2 ≤
      (ψ.toState.fidelity (projectionResetChannel P hsa hidem v₀ ψ.toState)) ^ 2 := by
  rw [State.fidelity_toState_sq, projectionResetChannel_op, PureState.toState_op,
    ContinuousLinearMap.re_inner_krausSumₗ_rankOne_self]
  have h := Finset.single_le_sum
    (f := fun o => ‖inner ℂ ψ.vec (projectionResetKraus P v₀ o ψ.vec)‖ ^ 2)
    (fun o _ => sq_nonneg _) (Finset.mem_univ none)
  rwa [projectionResetKraus] at h

/-- **Ensemble-average squared-fidelity lower bound for the projection–reset channel.** For an
orthogonal projector `P` (`IsSelfAdjoint P`, `P ∘ P = P`), a unit codeword `v₀`, and an ensemble
of pure states `e = {pᵢ, |ψᵢ⟩}` with density operator `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` (`Ensemble.toState`),
the **ensemble average fidelity** `∑ᵢ pᵢ F(|ψᵢ⟩, ℰ_P(|ψᵢ⟩⟨ψᵢ|))²` between each emitted state and
its compressed–decompressed image is at least the *squared typical-subspace weight of the average*
`(tr P ρ)²`:

`(tr P ρ)² ≤ ∑ᵢ pᵢ F(|ψᵢ⟩, ℰ_P(|ψᵢ⟩⟨ψᵢ|))²`.

The right-hand side is the ensemble average fidelity `F̄` of Nielsen & Chuang eq. (12.61) (single
copy): it is definitionally
`AxQM.ensembleAvgFidelity e.prob (fun i => (e.states i).toState)`
`(projectionResetChannel P hsa hidem v₀)`. This is the ensemble-average (rather than
entanglement-fidelity) form of Schumacher's reliability estimate driving **Exercise 12.8**: the same
projector `P` that makes `tr(P ρ⊗ⁿ)` close to `1` (the typical subspace theorem) makes the average
fidelity close to `1`.

Proof. Write `wᵢ = ⟨ψᵢ, P ψᵢ⟩ = ‖P ψᵢ‖²` (real and non-negative, since `P` is a self-adjoint
idempotent). The single-shot bound `projectionResetChannel_fidelity_sq_ge` gives `wᵢ² ≤ Fᵢ²`
termwise, so `∑ᵢ pᵢ wᵢ² ≤ ∑ᵢ pᵢ Fᵢ²`. Jensen's inequality for the convex square `x ↦ x²` against
the probability weights (`Real.pow_arith_mean_le_arith_mean_pow` at `n = 2`) gives
`(∑ᵢ pᵢ wᵢ)² ≤ ∑ᵢ pᵢ wᵢ²`. Finally the trace is linear (`ContinuousLinearMap.trace_mul_sum_smul`)
and `tr(P |ψᵢ⟩⟨ψᵢ|) = ⟨ψᵢ, P ψᵢ⟩` (`InnerProductSpace.trace_rankOne_self_comp`, trace cyclicity),
so `tr(P ρ) = ∑ᵢ pᵢ wᵢ`. Chaining, `(tr P ρ)² ≤ ∑ᵢ pᵢ Fᵢ²`. -/
theorem projectionResetChannel_avgFidelity_ge (P : S.space →L[ℂ] S.space) (hsa : IsSelfAdjoint P)
    (hidem : P.comp P = P) (v₀ : PureState S) (e : Ensemble S) :
    RCLike.re ((LinearMap.trace ℂ S.space) (P.comp e.toState.op)) ^ 2 ≤
      ∑ i, e.prob i *
        ((e.states i).toState.fidelity
          (projectionResetChannel P hsa hidem v₀ (e.states i).toState)) ^ 2 := by
  -- each pure state's typical-subspace overlap `⟨ψᵢ, P ψᵢ⟩` is the non-negative real `‖P ψᵢ‖²`
  -- (a general self-adjoint-idempotent fact, `inner_self_of_isSelfAdjoint_of_isIdempotent`)
  have hovlp : ∀ i, inner ℂ (e.states i).vec (P (e.states i).vec)
      = ((‖P (e.states i).vec‖ ^ 2 : ℝ) : ℂ) :=
    fun i => inner_self_of_isSelfAdjoint_of_isIdempotent hsa hidem (e.states i).vec
  -- trace bridge: `re tr(P ρ) = ∑ᵢ pᵢ ‖P ψᵢ‖²`
  have htrace : RCLike.re ((LinearMap.trace ℂ S.space) (P.comp e.toState.op))
      = ∑ i, e.prob i * ‖P (e.states i).vec‖ ^ 2 := by
    have hterm : ∀ i, (LinearMap.trace ℂ S.space) (↑(P * (e.states i).toState.op))
        = inner ℂ (e.states i).vec (P (e.states i).vec) := by
      intro i
      rw [PureState.toState_op, ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
        ← ContinuousLinearMap.toLinearMap_mul]
      exact InnerProductSpace.trace_rankOne_self_comp (e.states i).vec P
    have hcomp : (P.comp e.toState.op : S.space →L[ℂ] S.space)
        = P * ∑ i, (e.prob i : ℂ) • (e.states i).toState.op := by
      rw [Ensemble.toState_op]; rfl
    rw [hcomp, ContinuousLinearMap.trace_mul_sum_smul, RCLike.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hterm i, hovlp i, ← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  -- Jensen for the convex square against the probability weights: `(∑ pᵢ wᵢ)² ≤ ∑ pᵢ wᵢ²`
  have hjensen : (∑ i, e.prob i * ‖P (e.states i).vec‖ ^ 2) ^ 2
      ≤ ∑ i, e.prob i * (‖P (e.states i).vec‖ ^ 2) ^ 2 :=
    Real.pow_arith_mean_le_arith_mean_pow Finset.univ e.prob
      (fun i => ‖P (e.states i).vec‖ ^ 2) (fun i _ => e.prob_nonneg i) e.sum_prob
      (fun i _ => sq_nonneg _) 2
  -- termwise single-shot bound `‖⟨ψᵢ, P ψᵢ⟩‖² ≤ Fᵢ²` upgraded through the probability weights
  have hterm : ∑ i, e.prob i * (‖P (e.states i).vec‖ ^ 2) ^ 2 ≤
      ∑ i, e.prob i *
        ((e.states i).toState.fidelity
          (projectionResetChannel P hsa hidem v₀ (e.states i).toState)) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (e.prob_nonneg i)
    have h1 := projectionResetChannel_fidelity_sq_ge P hsa hidem v₀ (e.states i)
    rwa [hovlp i, Complex.norm_of_nonneg (sq_nonneg _)] at h1
  rw [htrace]
  exact hjensen.trans hterm

/-- **The projection–reset output is supported on the code subspace when the reset codeword is.**
If the codeword `v₀` lies in the range of the projector `P` (`P v₀ = v₀`), then the whole output
`ℰ_P(σ)` lies in the range of `P`: `P · ℰ_P(σ) = ℰ_P(σ)`. Indeed every Kraus operator `Eₒ` maps into
`range P` — `P ∘ P = P` for the projection element, and `P ∘ (|v₀⟩⟨fᵢ|(1 − P)) = |P v₀⟩⟨fᵢ|(1 − P) =
|v₀⟩⟨fᵢ|(1 − P)` for the reset elements (`comp_rankOne`, `P v₀ = v₀`) — so `P ∘ (∑ₒ Eₒ σ Eₒ†) =
∑ₒ (P Eₒ) σ Eₒ† = ∑ₒ Eₒ σ Eₒ†`. This is what makes the scheme a genuine rate-limited *compression*:
its output always sits inside the code subspace onto which `P` projects. -/
theorem projectionResetChannel_comp_op (P : S.space →L[ℂ] S.space) (hsa : IsSelfAdjoint P)
    (hidem : P.comp P = P) (v₀ : PureState S) (hv : P v₀.vec = v₀.vec) (σ : State S) :
    P.comp (projectionResetChannel P hsa hidem v₀ σ).op
      = (projectionResetChannel P hsa hidem v₀ σ).op := by
  rw [projectionResetChannel_op, ContinuousLinearMap.krausSumₗ_apply,
    ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← ContinuousLinearMap.comp_assoc]
  congr 1
  cases o with
  | none => simp only [projectionResetKraus]; exact hidem
  | some i =>
      simp only [projectionResetKraus]
      rw [← ContinuousLinearMap.comp_assoc, InnerProductSpace.comp_rankOne, hv]

end AxQM
