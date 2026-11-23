/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Theorem12_5
import AxQM.Postulates.API.ProjectionResetChannel
import AxQM.Postulates.API.EnsembleIidPow
import AxQM.NC.Ch9.Exercise9_23

/-!
# N&C Exercise 12.8 — compression of an ensemble of quantum states

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 12.8, p. 546.

Instead of defining a quantum source by a single density matrix `ρ` and the *entanglement*
fidelity (as in Schumacher's Theorem 12.6), N&C's Exercise 12.8 adopts the **ensemble definition**:
an i.i.d. source is an ensemble `e = {pⱼ, |ψⱼ⟩}` emitting `|ψⱼ⟩` with probability `pⱼ`, and a
compression–decompression scheme `(Cₙ, Dₙ)` is **reliable** when its *ensemble average fidelity*
tends to `1`:

`F̄ ≡ ∑_J p_{j₁} ⋯ p_{jₙ} · F(ρ_J, (Dₙ ∘ Cₙ)(ρ_J))² → 1` as `n → ∞`   (N&C Eq. 12.61),

where `J = (j₁, …, jₙ)` and `ρ_J = |ψ_{j₁}⟩⟨ψ_{j₁}| ⊗ ⋯ ⊗ |ψ_{jₙ}⟩⟨ψ_{jₙ}|`. Setting
`ρ = ∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|`, the exercise asks to show that **provided `R > S(ρ)` there exists a reliable
compression scheme of rate `R`** in this ensemble-average sense.

## The formalisation

The i.i.d. source model is the product ensemble `e.iidPow n`
(`AxQM/Postulates/API/EnsembleIidPow.lean`),
whose emitted states are `ρ_J = ((e.iidPow n).states J).toState` with weights `p_J`, and whose
density operator is `ρ^⊗n` (`Ensemble.iidPow_toState`). The ensemble average fidelity `F̄` (Eq.
12.61) is `ensembleAvgFidelity (e.iidPow n).prob (fun J ↦ ρ_J) (Cₙ)` (N&C `(9.127)`,
`NC/Ch9/Exercise9_23`).

* **`exists_reliable_ensembleCompression`** is the headline: for `R > S(ρ) = ρ.vonNeumannEntropy`
  there is an `ε > 0` and a family of quantum channels `Cₙ` such that
  * (i) each `Cₙ` is a genuine channel (`IsChannel`);
  * (ii) the code dimension `|T(n, ε)| = ρ.typicalSubspaceDim n ε` is `≤ 2^{nR}` (in nats,
    `≤ exp(nR)`) for all large `n` — the **rate `R`** bound;
  * (iii) **`Cₙ` genuinely compresses into that code**: for all large `n`, every output `Cₙ(σ)`
    lies in the `|T(n, ε)|`-dimensional typical subspace, i.e. the typical/atypical measurement
    accepts it with certainty, `(ρ.typicalSubspaceMeasurement n ε).bornProb (Cₙ σ) true = 1`. This
    conjunct **couples the scheme to its rate**: together with (ii) it forces `Cₙ`'s output into a
    `≤ 2^{nR}`-dimensional subspace, excluding non-compressing families such as the identity;
  * (iv) **reliability**: the ensemble average fidelity of `Cₙ` over `e.iidPow n` tends to `1`.

The witness is Schumacher's projection–reset scheme `Cₙ = ℰ_{P(n,ε)}` onto the `ε`-typical subspace
(`projectionResetChannel`, `AxQM/Postulates/API/ProjectionResetChannel.lean`) with
`ε = (R − S(ρ))/2`, so `S(ρ) + ε < R`; its reset codeword `v₀` is taken *inside* the typical
subspace (a typical eigenvector, which exists for large `n`). The proof chains:

* the **single-copy fidelity reduction** `(tr P(n,ε) ρ^⊗n)² ≤ F̄`
  (`projectionResetChannel_avgFidelity_ge` applied to `e.iidPow n`, with
  `(e.iidPow n).toState = ρ^⊗n`), together with `F̄ ≤ 1` (a convex combination of squared
  fidelities, `State.fidelity_le_one`) — squeezing `F̄` between `(tr P ρ^⊗n)²` and `1`;
* the **typical subspace theorem, part (1)** (`State.typicalSubspace_bornProb_ge`, Theorem 12.5):
  `tr(P(n,ε) ρ^⊗n) = Prob(typical) → 1` (via the projective-measurement Born rule, `bornProb`),
  hence `(tr P ρ^⊗n)² → 1` and so `F̄ → 1` by the squeeze;
* the **typical subspace theorem, part (2)** (`State.typicalSubspaceDim_bounds`, Theorem 12.5):
  `|T(n,ε)| ≤ exp(n(S(ρ)+ε)) ≤ exp(nR)` for large `n` — the rate bound;
* the **output-support fact** `projectionResetChannel_comp_op` (`P v₀ = v₀ ⟹ P·Cₙ(σ) = Cₙ(σ)`) +
  the Born bridge `typicalSubspaceMeasurement_bornProb_eq_re_trace`, giving conjunct (iii): the
  compressed output has all its weight in the typical subspace.

This is the ensemble-average-fidelity counterpart of Theorem 12.6 (the entanglement-fidelity
version): the *same* Schumacher scheme, driven by the same typical-subspace input, is reliable in
both senses.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2, Exercise 12.8, Eq. (12.61); Theorem 12.5; Theorem 12.6.
-/

open scoped InnerProductSpace ComplexOrder Topology BigOperators
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

namespace AxQM

variable {T : QSystem}

/-- **Nielsen & Chuang Exercise 12.8** (compression of an ensemble of quantum states): for an
ensemble source `e = {pⱼ, |ψⱼ⟩}` with average density operator `ρ = e.toState = ∑ⱼ pⱼ |ψⱼ⟩⟨ψⱼ|`,
**provided `R > S(ρ)` there exists a reliable compression scheme of rate `R`** in the
ensemble-average-fidelity sense (Eq. 12.61).

Concretely: for `R > ρ.vonNeumannEntropy` there is an `ε > 0` and a family of maps
`C : ∀ n, State (T ^⊗ₛ n) → State (T ^⊗ₛ n)` such that

* every `C n` is a genuine quantum channel (`IsChannel (C n)`);
* **rate `R`**: the code dimension `|T(n, ε)| = ρ.typicalSubspaceDim n ε` satisfies
  `|T(n, ε)| ≤ exp(n · R)` (nats; N&C's `2^{nR}`) for all sufficiently large `n`;
* **compression into that code**: for all sufficiently large `n`, every output `C n σ` lies in the
  `|T(n, ε)|`-dimensional typical subspace, `(ρ.typicalSubspaceMeasurement n ε).bornProb (C n σ)
  true = 1` — this couples the channel to the rate bound (the non-compressing identity family is
  excluded);
* **reliability**: the ensemble average fidelity
  `∑_J p_J · F(ρ_J, C n (ρ_J))² = ensembleAvgFidelity (e.iidPow n).prob (fun J ↦ ρ_J) (C n)`
  of `C n` over the `n`-fold i.i.d. source `e.iidPow n` tends to `1` as `n → ∞`.

The witnessing scheme is Schumacher's projection–reset channel `ℰ_{P(n,ε)}` onto the `ε`-typical
subspace with `ε = (R − S(ρ))/2` and reset codeword inside the typical subspace; see the module
docstring for the proof outline. -/
theorem exists_reliable_ensembleCompression (e : Ensemble T) {R : ℝ}
    (hR : e.toState.vonNeumannEntropy < R) :
    ∃ (ε : ℝ) (C : (n : ℕ) → State (T ^⊗ₛ n) → State (T ^⊗ₛ n)),
      0 < ε ∧ (∀ n, IsChannel (C n)) ∧
      (∀ᶠ n in atTop, (e.toState.typicalSubspaceDim n ε : ℝ) ≤ Real.exp (n * R)) ∧
      (∀ᶠ n in atTop, ∀ σ, (e.toState.typicalSubspaceMeasurement n ε).bornProb (C n σ) true = 1) ∧
      Tendsto (fun n => ensembleAvgFidelity (e.iidPow n).prob
        (fun J => ((e.iidPow n).states J).toState) (C n)) atTop (𝓝 1) := by
  classical
  set ρ := e.toState with hρ
  set ε : ℝ := (R - ρ.vonNeumannEntropy) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hSε : ρ.vonNeumannEntropy + ε ≤ R := by rw [hεdef]; linarith
  -- a fallback codeword index: the source ensemble is nonempty (its weights sum to `1`)
  obtain ⟨i0, -⟩ := Finset.nonempty_of_sum_ne_zero (s := (Finset.univ : Finset (Fin e.card)))
    (f := e.prob) (by rw [e.sum_prob]; exact one_ne_zero)
  -- the reset codeword: a typical eigenvector when the typical set is nonempty (else the fallback)
  set v : ∀ n, PureState (T ^⊗ₛ n) := fun n =>
    if h : (Real.typicalSeq ρ.eigenvalueDist n ε).Nonempty then
      ⟨ρ.tensorPowEigenbasis n h.choose, (ρ.tensorPowEigenbasis n).orthonormal.norm_eq_one _⟩
    else (e.iidPow n).states (finFunctionFinEquiv (fun _ : Fin n => i0)) with hv
  refine ⟨ε, fun n => projectionResetChannel (ρ.typicalSubspaceProj n ε)
      (ρ.typicalSubspaceProj_isSelfAdjoint n ε) (ρ.typicalSubspaceProj_idem n ε) (v n), hε,
    fun n => projectionResetChannel_isChannel _ _ _ _, ?_, ?_, ?_⟩
  · -- rate: `|T(n,ε)| ≤ exp(n(S+ε)) ≤ exp(nR)` for large `n` (Theorem 12.5, part (2))
    obtain ⟨N, -, hN⟩ := ρ.typicalSubspaceDim_bounds hε (δ := 1 / 2) (by norm_num)
    rw [eventually_atTop]
    exact ⟨N, fun n hn => (hN n hn).2.trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hSε (Nat.cast_nonneg n)))⟩
  · -- compression: `C n σ` is typical with certainty, once the typical set is nonempty
    obtain ⟨N, -, hN⟩ := ρ.typicalSubspace_bornProb_ge hε (δ := 1 / 2) (by norm_num)
    rw [eventually_atTop]
    refine ⟨N, fun n hn σ => ?_⟩
    -- typical set nonempty for `n ≥ N` (its total probability is `≥ 1/2 > 0`)
    have hne : (Real.typicalSeq ρ.eigenvalueDist n ε).Nonempty := by
      refine Finset.nonempty_of_sum_ne_zero (f := fun κ => ∏ i, ρ.eigenvalueDist (κ i)) ?_
      have hb := hN n hn
      rw [ρ.typicalSubspaceMeasurement_bornProb_true] at hb
      intro h0; rw [h0] at hb; linarith
    -- the codeword `v n` is the typical eigenvector `e_{κ₀}`, so `P v₀ = v₀`
    have hvfix : ρ.typicalSubspaceProj n ε (v n).vec = (v n).vec := by
      rw [hv]
      simp only [dite_eq_left hne]
      rw [State.typicalSubspaceProj,
        orthonormalProjector_apply_eq_ite (ρ.tensorPowEigenbasis n).orthonormal,
        ite_eq_left hne.choose_spec]
    rw [ρ.typicalSubspaceMeasurement_bornProb_eq_re_trace,
      projectionResetChannel_comp_op _ _ _ _ hvfix, State.trace_op_eq_one]
    simp
  · -- reliability: squeeze `(tr P ρ^⊗n)² ≤ F̄ ≤ 1` with `(tr P ρ^⊗n)² → 1` (Theorem 12.5, part (1))
    have hbp := ρ.typicalSubspace_bornProb_tendsto_one hε
    have le1 : ∀ n, (ρ.typicalSubspaceMeasurement n ε).bornProb (ρ.tensorPow n) true ^ 2
        ≤ ensembleAvgFidelity (e.iidPow n).prob (fun J => ((e.iidPow n).states J).toState)
          (projectionResetChannel (ρ.typicalSubspaceProj n ε)
            (ρ.typicalSubspaceProj_isSelfAdjoint n ε) (ρ.typicalSubspaceProj_idem n ε) (v n)) := by
      intro n
      rw [ρ.typicalSubspaceMeasurement_bornProb_eq_re_trace, ← e.iidPow_toState n]
      exact projectionResetChannel_avgFidelity_ge _ _ _ _ (e.iidPow n)
    have le2 : ∀ n, ensembleAvgFidelity (e.iidPow n).prob
        (fun J => ((e.iidPow n).states J).toState)
        (projectionResetChannel (ρ.typicalSubspaceProj n ε)
          (ρ.typicalSubspaceProj_isSelfAdjoint n ε) (ρ.typicalSubspaceProj_idem n ε)
          (v n)) ≤ 1 :=
      fun n => ensembleAvgFidelity_le_one _ (fun J => (e.iidPow n).prob_nonneg J)
        (e.iidPow n).sum_prob _ _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hbp.pow 2)
      tendsto_const_nhds le1 le2

end AxQM
