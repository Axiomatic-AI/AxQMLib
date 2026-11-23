/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.Subadditivity
import AxQM.Postulates.API.ControlMeasurementCommute
import AxQM.Postulates.API.ReducedStateOneFactor

/-!
# The head-wire measurement disentangles the register (N&C Problem 5.2)

The measured quantum Fourier transform (Problem 5.2) is assembled by an outer induction over the
tower depth. Its Figure 5.1 head-layer peel measures the **head wire** first
(`controlMeasurement`, the left factor of `qtower (n+1) qubit = qubit ⊗ qtower n qubit`); the
inductive step then plugs the level-`n` measured QFT into the collapsed state's *tail* factor
through the recursion connector `Measurement.postMeasurement_onRight_evolve_tmul`
(`AxQM/Postulates/API/OnRightProductState.lean`), which requires that collapsed state to be
a **product state** `|i⟩⟨i| ⊗ τ` — the head wire disentangled from the tail.

This file supplies exactly that fact, for an **arbitrary (mixed) input state**: measuring the head
wire of `qubit ⊗ S` in the computational basis collapses the register to the product of the pure
head state `|i⟩⟨i|` with the conditional tail state, `postMeas(σ, i) = |i⟩⟨i| ⊗ τ`. A
computational-basis measurement of one factor leaves that factor definite and carries no
correlation into the collapsed state, so the register factorises across the cut.

* `controlMeasurement_postMeasurement_reducedLeft` — the head marginal of the collapsed state is the
  measured basis state: `(postMeas(σ, i)).reducedLeft = |i⟩⟨i|`. From the marginal identity
  `Measurement.reducedLeft_postMeasurement_onLeft_op` (Alice's collapsed marginal is `Nᵢ ρ_A Nᵢ†/p`,
  valid for a mixed input), with `Nᵢ = |i⟩⟨i|` so the sandwich
  `|i⟩⟨i| ρ_A |i⟩⟨i| = ⟪i, ρ_A i⟫ |i⟩⟨i|`; the a-priori-unknown scalar is pinned to `1` by trace-one
  of the collapsed marginal.
* `controlMeasurement_postMeasurement_eq_tmul` — the **disentangling bridge**:
  `postMeas(σ, i) = |i⟩ ⊗ (postMeas(σ, i)).reducedRight`, the product form the outer induction feeds
  to the recursion connector. Immediate from the marginal identity above and the product-factoring
  lemma `State.eq_tmul_of_isPure_reducedLeft` (a state with a pure left marginal is the product of
  its marginals).

The two general `State` facts this development needs are `State.tmul_mix` (the
left-factor companion of `State.mix_tmul`) and `State.eq_tmul_of_isPure_reducedLeft` (the left
companion of `State.eq_tmul_of_isPure_reducedRight`); they are in `AxQM/Postulates/API/Mixture.lean`
and `AxQM/NC/Ch11/Subadditivity.lean`, beside their right/dual siblings. The
mixed-input marginal identity `Measurement.reducedLeft_postMeasurement_onLeft_op` is in
`AxQM/Postulates/API/ReducedStateOneFactor.lean`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The head marginal of the collapsed state is the measured basis state.** Measuring the head
wire of `qubit ⊗ S` in the computational basis (`controlMeasurement S`, operators `Mᵢ = |i⟩⟨i| ⊗ 1`)
and obtaining outcome `i` collapses the head wire to `|i⟩`: the reduced state on the head qubit of
the post-measurement state is `|i⟩⟨i|`, whatever the (mixed) input `σ`.

`controlMeasurement S` is the left-factor computational-basis measurement, so the marginal identity
`Measurement.reducedLeft_postMeasurement_onLeft_op` gives the head marginal as
`p(i)⁻¹ · (Nᵢ ρ_A Nᵢ†)` with `Nᵢ = |i⟩⟨i|` and `ρ_A = σ.reducedLeft`. The rank-one sandwich
`|i⟩⟨i| ρ_A |i⟩⟨i| = ⟪i, ρ_A i⟫ |i⟩⟨i|` reduces it to a scalar multiple of `|i⟩⟨i|`; the collapsed
marginal is a state, so its trace is `1`, forcing the scalar to `1`. -/
theorem controlMeasurement_postMeasurement_reducedLeft (σ : State (qubit ⊗ S)) (i : Fin 2)
    (hp : (controlMeasurement S).bornProb σ i ≠ 0) :
    ((controlMeasurement S).postMeasurement σ i hp).reducedLeft = (qubitBasis i).toState := by
  set v : qubit.space := (qubitBasis i).vec with hv
  set m : Measurement (Fin 2) qubit :=
    Measurement.ofOrthonormalBasis (EuclideanSpace.basisFun (Fin 2) ℂ) with hm
  -- `controlMeasurement S = m.onLeft S`, and `m.op i = |i⟩⟨i|`.
  have hmop : m.op i = InnerProductSpace.rankOne ℂ v v := by
    erw [hm, Measurement.ofOrthonormalBasis_op, hv]
    exact congrArg (fun w => InnerProductSpace.rankOne ℂ w w)
      ((EuclideanSpace.basisFun_apply (Fin 2) ℂ i).trans (qubitBasis_vec i).symm)
  -- the rank-one sandwich `|v⟩⟨v| ρ_A |v⟩⟨v| = ⟪v, ρ_A v⟫ |v⟩⟨v|`
  have hsand : (InnerProductSpace.rankOne ℂ v v).comp
        (σ.reducedLeft.op.comp (adjoint (InnerProductSpace.rankOne ℂ v v)))
      = (inner ℂ v (σ.reducedLeft.op v)) • InnerProductSpace.rankOne ℂ v v := by
    rw [InnerProductSpace.adjoint_rankOne, InnerProductSpace.comp_rankOne,
      InnerProductSpace.rankOne_comp_rankOne]
  -- Alice's collapsed marginal (mixed input), then the sandwich: a scalar multiple of `|v⟩⟨v|`
  have key : ((controlMeasurement S).postMeasurement σ i hp).reducedLeft.op
      = (((controlMeasurement S).bornProb σ i : ℝ) : ℂ)⁻¹ •
          ((m.op i).comp (σ.reducedLeft.op.comp (adjoint (m.op i)))) :=
    Measurement.reducedLeft_postMeasurement_onLeft_op m σ i hp
  have hvv : inner ℂ v v = (1 : ℂ) := inner_self_eq_one_of_norm_eq_one (qubitBasis i).normalized
  have htrace : (LinearMap.trace ℂ qubit.space) ↑(InnerProductSpace.rankOne ℂ v v) = 1 := by
    rw [InnerProductSpace.trace_rankOne, hvv]
  have hred : ((controlMeasurement S).postMeasurement σ i hp).reducedLeft.op
      = ((((controlMeasurement S).bornProb σ i : ℝ) : ℂ)⁻¹ * inner ℂ v (σ.reducedLeft.op v))
          • InnerProductSpace.rankOne ℂ v v := by rw [key, hmop, hsand, smul_smul]
  -- trace-one of the collapsed marginal pins the scalar to `1`
  have hd1 : (((controlMeasurement S).bornProb σ i : ℝ) : ℂ)⁻¹ * inner ℂ v (σ.reducedLeft.op v)
      = 1 := by
    have h1 := State.trace_op_eq_one ((controlMeasurement S).postMeasurement σ i hp).reducedLeft
    rw [hred, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, htrace, mul_one] at h1
    exact h1
  apply State.ext
  rw [hred, hd1, one_smul, PureState.toState_op, hv]

/-- **Problem 5.2 (the head-wire measurement disentangles the register).** Measuring the head wire
of `qubit ⊗ S` in the computational basis and obtaining outcome `i` collapses the register to the
**product state** `|i⟩ ⊗ τ`, the pure head state tensored with the conditional tail state
`τ = (postMeas(σ, i)).reducedRight`:

  `postMeas(σ, i) = |i⟩ ⊗ (postMeas(σ, i)).reducedRight`.

A computational-basis measurement of one factor leaves it definite and carries no correlation into
the collapsed state. This is the product form the measured-QFT outer induction feeds to the
recursion connector `Measurement.postMeasurement_onRight_evolve_tmul`, plugging the
level-`n` measured QFT into the disentangled tail. Immediate from
`State.eq_tmul_of_isPure_reducedLeft` (the head marginal is pure by
`controlMeasurement_postMeasurement_reducedLeft`). -/
theorem controlMeasurement_postMeasurement_eq_tmul (σ : State (qubit ⊗ S)) (i : Fin 2)
    (hp : (controlMeasurement S).bornProb σ i ≠ 0) :
    (controlMeasurement S).postMeasurement σ i hp
      = (qubitBasis i).toState.tmul
          ((controlMeasurement S).postMeasurement σ i hp).reducedRight := by
  have hpure : ((controlMeasurement S).postMeasurement σ i hp).reducedLeft.IsPure := by
    rw [controlMeasurement_postMeasurement_reducedLeft]; exact ⟨qubitBasis i, rfl⟩
  have hprod := State.eq_tmul_of_isPure_reducedLeft
    ((controlMeasurement S).postMeasurement σ i hp) hpure
  rw [controlMeasurement_postMeasurement_reducedLeft] at hprod
  exact hprod

end AxQM
