/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyComposite
import AxQM.Postulates.API.UnreadMeasurement
import AxQM.Postulates.API.ResetMeasurement

/-!
# Nielsen & Chuang, Exercise 11.15 — a generalized measurement can decrease entropy

**Exercise 11.15 (Generalized measurements can decrease entropy), N&C p. 515.** A qubit in the
state `ρ` is measured with the measurement operators `M₀ = |0⟩⟨0|` and `M₁ = |0⟩⟨1|`. If the result
of the measurement is unknown to us, the state of the system afterwards is
`ρ' = M₀ ρ M₀† + M₁ ρ M₁†`. Show that this procedure can decrease the entropy of the qubit.

## Discussion

`M₀, M₁` are valid generalized-measurement operators: the completeness relation (N&C Eq. (2.121))
holds, `M₀† M₀ + M₁† M₁ = |0⟩⟨0| + |1⟩⟨1| = I`, so `{M₀, M₁}` is a `Measurement` (Postulate 3) —
`resetMeasurement` below. Note `M₁ = |0⟩⟨1|` is *not* self-adjoint, so this is a genuine
*generalized* measurement, not a projective one.

The unread (non-selective) post-measurement state is `Measurement.unreadState`,
`ρ' = Σᵢ Mᵢ ρ Mᵢ†`. Here it collapses to a constant, because both operators map onto `|0⟩` and
`tr ρ = 1`:
`M₀ ρ M₀† + M₁ ρ M₁† = ⟨0|ρ|0⟩ · |0⟩⟨0| + ⟨1|ρ|1⟩ · |0⟩⟨0| = (tr ρ) · |0⟩⟨0| = |0⟩⟨0|`.
So this is a **reset channel**: it sends *every* state to the pure state `|0⟩⟨0|`
(`resetMeasurement_unreadState`), whose von Neumann entropy is `0`
(`resetMeasurement_unreadState_vonNeumannEntropy_eq_zero`).

Entropy therefore strictly decreases whenever the input is not already pure. Taking `ρ = I/2` (the
maximally mixed qubit, entropy `log 2 > 0`) exhibits a strict decrease `S(ρ') < S(ρ)`
(`resetMeasurement_can_decrease_entropy`) — the exercise's claim.

## The formalisation

The generalized measurement itself, `resetMeasurement : Measurement (Fin 2) qubit` (the operators
`{|0⟩⟨0|, |0⟩⟨1|}` bundled with their completeness proof), is in
`AxQM/Postulates/API/ResetMeasurement.lean` (like `quditMeasurement`). The statements are:

* `resetMeasurement_unreadState` — `ρ' = |0⟩⟨0|` for every `ρ` (the reset-channel identity).
* `resetMeasurement_unreadState_vonNeumannEntropy_eq_zero` — `S(ρ') = 0` for every `ρ`.
* `resetMeasurement_can_decrease_entropy` — `∃ ρ, S(ρ') < S(ρ)`, witnessed by the maximally mixed
  state.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The reset-channel identity (the heart of Exercise 11.15).** For *every* qubit state `ρ`, the
unread post-measurement state of `resetMeasurement` is the pure state `|0⟩⟨0|`:
`ρ' = Σᵢ Mᵢ ρ Mᵢ† = |0⟩⟨0|`. Indeed each Kraus term is a scalar multiple of `|0⟩⟨0|`,
`Mᵢ ρ Mᵢ† = ⟨i|ρ|i⟩ · |0⟩⟨0|`, and the coefficients sum to `⟨0|ρ|0⟩ + ⟨1|ρ|1⟩ = tr ρ = 1`
(`State.trace_op_eq_one`, `LinearMap.trace_eq_sum_inner`). -/
theorem resetMeasurement_unreadState (ρ : State qubit) :
    resetMeasurement.unreadState ρ = (qubitBasis 0).toState := by
  -- Each Kraus term `Mᵢ ρ Mᵢ†` is `⟨i|ρ|i⟩ · |0⟩⟨0|`.
  have hterm : ∀ i, resetMeasurement.op i * ρ.op * star (resetMeasurement.op i)
      = (inner ℂ (qubitBasis i).vec (ρ.op (qubitBasis i).vec) : ℂ)
          • rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec := by
    intro i
    rw [resetMeasurement_op]
    ext x
    simp only [mul_apply_eq_comp, star_eq_adjoint, adjoint_rankOne, rankOne_apply, map_smul,
      smul_apply, smul_smul]
    rw [mul_comm]
  -- The coefficients sum to the trace, which is one.
  have htr : (inner ℂ (qubitBasis 0).vec (ρ.op (qubitBasis 0).vec) : ℂ)
      + inner ℂ (qubitBasis 1).vec (ρ.op (qubitBasis 1).vec) = 1 := by
    set b : OrthonormalBasis (Fin 2) ℂ qubit.space := EuclideanSpace.basisFun (Fin 2) ℂ with hb
    have hbv : ∀ i, (qubitBasis i).vec = b i := fun i => by
      rw [qubitBasis_vec]; exact (EuclideanSpace.basisFun_apply (Fin 2) ℂ i).symm
    have ht := State.trace_op_eq_one ρ
    rw [LinearMap.trace_eq_sum_inner (↑ρ.op) b, Fin.sum_univ_two] at ht
    simpa only [← hbv, ContinuousLinearMap.coe_coe] using ht
  apply State.ext
  rw [PureState.toState_op, Measurement.unreadState_op,
    ContinuousLinearMap.krausSumₗ_eq_sum_mul_star, Fin.sum_univ_two, hterm, hterm, ← add_smul, htr,
    one_smul]

/-- **The reset channel outputs a pure state, so its entropy is zero.** For every qubit state `ρ`,
the unread post-measurement state has vanishing von Neumann entropy, since it is the pure state
`|0⟩⟨0|` (`resetMeasurement_unreadState`) and pure states have zero entropy. -/
theorem resetMeasurement_unreadState_vonNeumannEntropy_eq_zero (ρ : State qubit) :
    (resetMeasurement.unreadState ρ).vonNeumannEntropy = 0 := by
  rw [resetMeasurement_unreadState]
  exact (qubitBasis 0).vonNeumannEntropy_toState_eq_zero

/-- **N&C Exercise 11.15: the procedure can strictly decrease the entropy of the qubit.** There is
a state whose entropy is strictly greater than that of its unread post-measurement state: take the
maximally mixed state `I/2`, with `S(I/2) = log 2 > 0`, whose image is the pure state `|0⟩⟨0|` with
`S = 0`. -/
theorem resetMeasurement_can_decrease_entropy :
    ∃ ρ : State qubit,
      (resetMeasurement.unreadState ρ).vonNeumannEntropy < ρ.vonNeumannEntropy := by
  refine ⟨maximallyMixedState qubit, ?_⟩
  rw [resetMeasurement_unreadState_vonNeumannEntropy_eq_zero,
    State.vonNeumannEntropy_maximallyMixed, finrank_qubit_space]
  exact Real.log_pos (by norm_num)

end AxQM
