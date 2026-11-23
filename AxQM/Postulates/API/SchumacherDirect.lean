/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TypicalSubspace
import ToMathlib.Analysis.InnerProductSpace.SchumacherCompression
import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelityBound
import ToMathlib.InformationTheory.NoiselessCoding

/-!
# AxQM.Postulates.API — the direct part of Schumacher's theorem (N&C Thm 12.6)

The **direct (achievability) half** of Nielsen & Chuang's quantum noiseless channel coding theorem
(Theorem 12.6): for an i.i.d. quantum source `ρ : State S`, if `S(ρ) < R` (in nats,
`ρ.vonNeumannEntropy < R * log 2`, with `R` a qubit rate) then `ρ` is **reliably compressible at
rate `R`** — there is a family of rate-`R` quantum compression schemes whose entanglement fidelity
for `ρ^⊗n` tends to `1` (`ContinuousLinearMap.ReliablyCompressible ρ.op R`).

## The construction (N&C Eqs. 12.50–12.53)

At each block length `n` the scheme is Schumacher's **projection–reset** scheme
(`QuantumCompressionScheme.projectionReset`) built on the ε-typical subspace projector `P(n, ε)`
(`State.typicalSubspaceProj`), for a fixed `ε` with `S(ρ) + ε < R * log 2`:

* the compression `Cₙ` is the projection–reset encoder onto the span of the ε-typical product
  eigenvectors of `ρ^⊗n`, the decompression `Dₙ` is the identity;
* the compressed subspace is the ε-typical subspace `T(n, ε)`, of dimension `|T(n, ε)|`.

Two facts drive reliability, both already established:

* **Rate.** For large `n` the ε-typical set has `|T(n, ε)| ≤ 2^{⌊nR⌋}`
  (`Real.exists_card_typicalSeq_le_two_pow`, the classical theorem of typical sequences applied to
  the eigenvalue distribution `λ = ρ.eigenvalueDist`, whose entropy is `S(ρ)`), so the scheme really
  compresses into `⌊nR⌋` qubits.
* **Fidelity.** The projection–reset fidelity dominates the code overlap,
  `F(ρ^⊗n, Dₙ ∘ Cₙ) ≥ |tr(ρ^⊗n P(n, ε))|²` (`projectionReset_fidelity_ge`, N&C Eq. 12.52), and
  `tr(ρ^⊗n P(n, ε))` is the Born probability of landing in the typical subspace, which tends to `1`
  (`State.typicalSubspaceMeasurement_bornProb_true` + `Real.exists_le_sum_typicalSeq`, part (1)).
  Together with the universal upper bound `F ≤ 1` (`entanglementFidelity_le_one`) a squeeze gives
  `F(ρ^⊗n, Dₙ ∘ Cₙ) → 1`.

For the finitely many small `n` where the ε-typical set is empty or already too large, the family
falls back to a trivial single-vector scheme; the reliability limit only sees the tail, so the
fallback is irrelevant.

## Main results

* `State.bornProb_typicalSubspace_le_norm_trace` — the Born probability of the typical subspace is
  `≤ ‖tr(ρ^⊗n P(n, ε))‖` (the bridge from `re tr(P ρ)` to `‖tr(ρ P)‖`), so squaring turns N&C's
  part (1) probability bound into the fidelity lower bound of Eq. (12.52).
* `State.bornProb_typicalSubspace_tendsto_one` — the typical-subspace Born probability tends to `1`
  (N&C part (1), asymptotic form).
* `State.reliablyCompressible_of_vonNeumannEntropy_lt` — **the direct part of Theorem 12.6**:
  `ρ.vonNeumannEntropy < R * log 2 → ReliablyCompressible ρ.op R`.

The iff `ReliablyCompressible ↔ S(ρ) < R` of Theorem 12.6 is assembled from this direct half and
the converse (`AxQM/Postulates/API/SchumacherConverse.lean`) in `AxQM/NC/Ch12/Theorem12_6.lean`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2 (Theorem 12.6; Eqs. (12.50)–(12.53)).
-/

open scoped InnerProductSpace TensorProduct BigOperators
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The typical-subspace Born probability is bounded by the code-overlap trace norm.** The
probability that `ρ^⊗n` lands in the ε-typical subspace, `tr(P(n, ε) ρ^⊗n)`, is at most
`‖tr(ρ^⊗n P(n, ε))‖` — the quantity squared in Schumacher's fidelity lower bound (N&C Eq. 12.52).

The Born probability is `re tr(P† P ρ^⊗n) = re tr(P ρ^⊗n)` (`bornProb_eq_re_trace_postOp`,
`trace_postOp`, and `orthonormalProjector_adjoint_comp_self` collapsing `P† P = P`); the real
part of a complex number is at most its norm (`RCLike.re_le_norm`), and cyclicity of the trace
(`LinearMap.trace_comp_comm'`) identifies `‖tr(P ρ^⊗n)‖` with `‖tr(ρ^⊗n P)‖`. -/
theorem State.bornProb_typicalSubspace_le_norm_trace (ρ : State S) (n : ℕ) (ε : ℝ) :
    (ρ.typicalSubspaceMeasurement n ε).bornProb (ρ.tensorPow n) true
      ≤ ‖LinearMap.trace ℂ (S ^⊗ₛ n).space
          (((ρ.tensorPow n).op * ρ.typicalSubspaceProj n ε :
              (S ^⊗ₛ n).space →L[ℂ] (S ^⊗ₛ n).space) :
            (S ^⊗ₛ n).space →ₗ[ℂ] (S ^⊗ₛ n).space)‖ := by
  rw [Measurement.bornProb_eq_re_trace_postOp, ContinuousLinearMap.trace_postOp,
    State.typicalSubspaceMeasurement_op_true, State.typicalSubspaceProj,
    ← ContinuousLinearMap.comp_assoc,
    InnerProductSpace.orthonormalProjector_adjoint_comp_self
      (ρ.tensorPowEigenbasis n).orthonormal]
  refine le_trans (RCLike.re_le_norm _) (le_of_eq ?_)
  congr 1
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']

/-- **The typical-subspace Born probability tends to `1`** (Nielsen & Chuang, Theorem 12.5,
part (1), asymptotic form): fix `ε > 0`; then the probability that `ρ^⊗n` lands in the ε-typical
subspace,
`tr(P(n, ε) ρ^⊗n)`, tends to `1` as `n → ∞`. The probability is `≥ 1 − δ` for large `n` for every
`δ` (`Real.exists_le_sum_typicalSeq` applied to `λ = ρ.eigenvalueDist`, rewritten by the Born
identity `typicalSubspaceMeasurement_bornProb_true`) and is always `≤ 1` (`bornProb_le_one`). -/
theorem State.bornProb_typicalSubspace_tendsto_one (ρ : State S) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (ρ.typicalSubspaceMeasurement n ε).bornProb (ρ.tensorPow n) true)
      atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, _, hN⟩ := Real.exists_le_sum_typicalSeq ρ.eigenvalueDist_nonneg
    ρ.eigenvalueDist_sum_eq_one hε (half_pos hη)
  refine ⟨N, fun n hn => ?_⟩
  have hle1 := Measurement.bornProb_le_one (ρ.typicalSubspaceMeasurement n ε) (ρ.tensorPow n) true
  have hge := hN n hn
  rw [← ρ.typicalSubspaceMeasurement_bornProb_true] at hge
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- **The direct part of Schumacher's noiseless channel coding theorem** (Nielsen & Chuang, Theorem
12.6, Eqs. 12.50–12.53). If the von Neumann entropy of the source is below the rate,
`S(ρ) < R` (in nats: `ρ.vonNeumannEntropy < R * log 2`, `R` a qubit rate), then `ρ` is **reliably
compressible at rate `R`**: there is a family of rate-`R` quantum compression schemes whose
entanglement fidelity for `ρ^⊗n` tends to `1`.

The witness is Schumacher's projection–reset scheme on the ε-typical subspace for a fixed `ε` with
`S(ρ) + ε < R * log 2`. For large `n` the ε-typical set is nonempty and has cardinality `≤ 2^{⌊nR⌋}`
(`Real.exists_card_typicalSeq_le_two_pow` / `Real.exists_le_sum_typicalSeq` on `λ =
ρ.eigenvalueDist`), so the projection–reset scheme is well-defined; its fidelity dominates
`|tr(ρ^⊗n P(n, ε))|²` (`projectionReset_fidelity_ge`), the Born probability squared, which tends to
`1` (`bornProb_typicalSubspace_tendsto_one`). Together with `F ≤ 1`
(`entanglementFidelity_le_one`) a squeeze forces `F → 1`. Small `n` outside the good range use a
trivial fallback scheme, invisible to the limit. -/
theorem State.reliablyCompressible_of_vonNeumannEntropy_lt (ρ : State S) {R : ℝ}
    (hR : ρ.vonNeumannEntropy < R * Real.log 2) :
    ContinuousLinearMap.ReliablyCompressible ρ.op R := by
  classical
  -- `S.space` is nonzero (a density operator has trace `1`), so the eigenbasis index type is
  -- nonempty — needed for the fallback scheme's reference vector.
  have hNE : Nonempty (Fin (Module.finrank ℂ S.space)) := by
    have := ρ.nontrivial_space
    exact ⟨⟨0, Module.finrank_pos⟩⟩
  -- Pick `ε > 0` with `S(ρ) + ε < R log 2`.
  obtain ⟨ε, hε, hεR⟩ : ∃ ε, 0 < ε ∧ ρ.vonNeumannEntropy + ε < R * Real.log 2 :=
    ⟨(R * Real.log 2 - ρ.vonNeumannEntropy) / 2, by linarith, by linarith⟩
  have hεR' : Real.entropy ρ.eigenvalueDist + ε < R * Real.log 2 := by
    rw [← ρ.vonNeumannEntropy_eq_entropy_eigenvalueDist]; exact hεR
  -- The "good" range: for large `n` the ε-typical set is nonempty with cardinality `≤ 2^{⌊nR⌋}`.
  obtain ⟨Ncard, hNcard⟩ := Real.exists_card_typicalSeq_le_two_pow ρ.eigenvalueDist
    ρ.eigenvalueDist_nonneg ρ.eigenvalueDist_sum_eq_one hεR'
  obtain ⟨Nne, _, hNne⟩ := Real.exists_le_sum_typicalSeq ρ.eigenvalueDist_nonneg
    ρ.eigenvalueDist_sum_eq_one hε (by norm_num : (0:ℝ) < 1 / 2)
  have hgood : ∀ n ≥ max Ncard Nne,
      (Real.typicalSeq ρ.eigenvalueDist n ε).Nonempty ∧
        (Real.typicalSeq ρ.eigenvalueDist n ε).card ≤ 2 ^ ⌊(n : ℝ) * R⌋₊ := by
    intro n hn
    refine ⟨?_, hNcard n (le_trans (le_max_left _ _) hn)⟩
    rw [← Finset.ne_empty_iff_nonempty]
    intro he
    have := hNne n (le_trans (le_max_right _ _) hn)
    rw [he, Finset.sum_empty] at this
    linarith
  -- The scheme family: the projection–reset scheme on the good range, a trivial fallback otherwise.
  set sch : (n : ℕ) → QuantumCompressionScheme (⨂[ℂ] (_ : Fin n), S.space) ⌊(n : ℝ) * R⌋₊ :=
    fun n =>
      if h : (Real.typicalSeq ρ.eigenvalueDist n ε).Nonempty ∧
          (Real.typicalSeq ρ.eigenvalueDist n ε).card ≤ 2 ^ ⌊(n : ℝ) * R⌋₊ then
        QuantumCompressionScheme.projectionReset (ρ.tensorPowEigenbasis n)
          (Real.typicalSeq ρ.eigenvalueDist n ε) h.1.choose h.1.choose_spec h.2
      else
        QuantumCompressionScheme.projectionReset (ρ.tensorPowEigenbasis n)
          {fun _ => hNE.some} (fun _ => hNE.some) (Finset.mem_singleton_self _)
          (by rw [Finset.card_singleton]; exact Nat.one_le_two_pow) with hsch
  refine ⟨sch, ?_⟩
  -- Upper bound: the entanglement fidelity is always `≤ 1`.
  have hle_one : ∀ n, (sch n).fidelity (PiTensorProduct.mapCLM fun _ : Fin n => ρ.op) ≤ 1 := by
    intro n
    have hop : (PiTensorProduct.mapCLM fun _ : Fin n => ρ.op) = (ρ.tensorPow n).op := rfl
    rw [hop]
    unfold QuantumCompressionScheme.fidelity
    exact ContinuousLinearMap.entanglementFidelity_le_one (ρ.tensorPow n).isDensity _
      (sch n).composite_isTracePreserving
  -- Lower bound (eventually): the fidelity dominates the squared Born probability.
  have hbp : Tendsto
      (fun n => ((ρ.typicalSubspaceMeasurement n ε).bornProb (ρ.tensorPow n) true) ^ 2)
      atTop (nhds 1) := by
    simpa using (ρ.bornProb_typicalSubspace_tendsto_one hε).pow 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hbp tendsto_const_nhds ?_
    (Eventually.of_forall hle_one)
  rw [eventually_atTop]
  refine ⟨max Ncard Nne, fun n hn => ?_⟩
  obtain ⟨hne, hcard⟩ := hgood n hn
  have hsch_n : sch n = QuantumCompressionScheme.projectionReset (ρ.tensorPowEigenbasis n)
      (Real.typicalSeq ρ.eigenvalueDist n ε) hne.choose hne.choose_spec hcard := by
    simp only [hsch]
    exact dite_eq_left ⟨hne, hcard⟩
  have hfge := QuantumCompressionScheme.projectionReset_fidelity_ge (ρ.tensorPowEigenbasis n)
    (Real.typicalSeq ρ.eigenvalueDist n ε) hne.choose hne.choose_spec hcard ((ρ.tensorPow n).op)
  calc ((ρ.typicalSubspaceMeasurement n ε).bornProb (ρ.tensorPow n) true) ^ 2
      ≤ ‖LinearMap.trace ℂ (S ^⊗ₛ n).space
          (((ρ.tensorPow n).op * ρ.typicalSubspaceProj n ε :
              (S ^⊗ₛ n).space →L[ℂ] (S ^⊗ₛ n).space) :
            (S ^⊗ₛ n).space →ₗ[ℂ] (S ^⊗ₛ n).space)‖ ^ 2 :=
        pow_le_pow_left₀ (Measurement.bornProb_nonneg _ _ _)
          (ρ.bornProb_typicalSubspace_le_norm_trace n ε) 2
    _ ≤ (sch n).fidelity (PiTensorProduct.mapCLM fun _ : Fin n => ρ.op) := by
        rw [hsch_n]; exact hfge

end AxQM
