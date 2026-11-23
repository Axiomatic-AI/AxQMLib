/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyComposite
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.Purity
import AxQM.Postulates.PartialTraceTensor

/-!
# N&C Exercise 11.17 — an explicit non-trivial mixed `AB` state with `S(A,B) = S(B) − S(A)`

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.17, p. 516: *find an explicit non-trivial example of a mixed state `ρ` for `AB` such
that `S(A,B) = S(B) − S(A)`.*

The Araki–Lieb *triangle inequality* (N&C eq. (11.73)) is `S(A,B) ≥ |S(A) − S(B)|`, so in
particular `S(A,B) ≥ S(B) − S(A)`. This exercise asks for a state that **saturates** that lower
bound. The *trivial* saturating states are the pure ones: a pure `ρ^{AB}` has `S(A,B) = 0` and
`S(A) = S(B)` (N&C Theorem 11.8), so `S(A,B) = S(B) − S(A) = 0` holds vacuously. The exercise
therefore asks for a genuinely **mixed** witness.

## The witness

We take the product state on two qubits (`A = B = ` qubit)

`ρ = |0⟩⟨0|_A ⊗ (I/2)_B`  (`arakiLiebEqualityState`),

a pure `|0⟩` on `A` tensored with the maximally mixed state on `B`. It is a product state, so its
marginals are read off directly: `ρ^A = |0⟩⟨0|` (pure, `S(A) = 0`) and `ρ^B = I/2`
(`S(B) = log 2`); and additivity over a product (N&C Exercise 11.13) gives
`S(A,B) = S(A) + S(B) = 0 + log 2 = log 2`. Hence

`S(A,B) = log 2 = log 2 − 0 = S(B) − S(A)`,

and `ρ` is mixed (`S(A,B) = log 2 ≠ 0`, so `ρ` is not a pure state). This is the boundary case of
the equality conditions of Exercise 11.16: with `A` pure, `A` is uncorrelated with the purifying
system, so the triangle inequality is tight.

## Main definitions

* `AxQM.arakiLiebEqualityState` — the witness `|0⟩⟨0| ⊗ I/2` on `qubit ⊗ qubit`.

## Main results

* `AxQM.arakiLiebEqualityState_reducedLeft_vonNeumannEntropy` — `S(A) = 0`.
* `AxQM.arakiLiebEqualityState_reducedRight_vonNeumannEntropy` — `S(B) = log 2`.
* `AxQM.arakiLiebEqualityState_vonNeumannEntropy` — `S(A,B) = log 2`.
* `AxQM.arakiLiebEqualityState_vonNeumannEntropy_eq_reducedRight_sub_reducedLeft` — the
  saturation `S(A,B) = S(B) − S(A)`.
* `AxQM.arakiLiebEqualityState_not_isPure` — the witness is genuinely mixed.
* `AxQM.exists_mixed_state_vonNeumannEntropy_eq_reducedRight_sub_reducedLeft` — the
  exercise: there is a non-trivial (mixed) `AB` state with `S(A,B) = S(B) − S(A)`.
-/

noncomputable section

namespace AxQM

/-- **The Exercise 11.17 witness** `ρ = |0⟩⟨0|_A ⊗ (I/2)_B` on `qubit ⊗ qubit`: a pure `|0⟩` on the
left factor `A` tensored with the maximally mixed state on the right factor `B`. A non-trivial
(mixed) state saturating the Araki–Lieb triangle inequality `S(A,B) ≥ S(B) − S(A)`. -/
def arakiLiebEqualityState : State (qubit ⊗ qubit) :=
  qubitKet0.toState.tmul (maximallyMixedState qubit)

/-- The **left marginal** `ρ^A = Tr_B ρ = |0⟩⟨0|` of the witness: the left factor of a product
state is recovered by tracing out the right factor. -/
theorem arakiLiebEqualityState_reducedLeft :
    arakiLiebEqualityState.reducedLeft = qubitKet0.toState := by
  rw [arakiLiebEqualityState, State.reducedLeft_tmul]

/-- The **right marginal** `ρ^B = Tr_A ρ = I/2` of the witness: the right factor of a product state
is recovered by tracing out the left factor. -/
theorem arakiLiebEqualityState_reducedRight :
    arakiLiebEqualityState.reducedRight = maximallyMixedState qubit := by
  rw [arakiLiebEqualityState, State.reducedRight_tmul]

/-- **`S(A) = 0`**: the `A`-marginal `ρ^A = |0⟩⟨0|` is pure, so it has zero von Neumann entropy. -/
theorem arakiLiebEqualityState_reducedLeft_vonNeumannEntropy :
    arakiLiebEqualityState.reducedLeft.vonNeumannEntropy = 0 := by
  rw [arakiLiebEqualityState_reducedLeft, PureState.vonNeumannEntropy_toState_eq_zero]

/-- **`S(B) = log 2`**: the `B`-marginal `ρ^B = I/2` is the maximally mixed qubit, whose entropy is
`log (dim) = log 2`. -/
theorem arakiLiebEqualityState_reducedRight_vonNeumannEntropy :
    arakiLiebEqualityState.reducedRight.vonNeumannEntropy = Real.log 2 := by
  rw [arakiLiebEqualityState_reducedRight, State.vonNeumannEntropy_maximallyMixed,
    finrank_qubit_space, Nat.cast_ofNat]

/-- **`S(A,B) = log 2`**: additivity of the entropy over the product state `|0⟩⟨0| ⊗ I/2` gives
`S(A,B) = S(|0⟩⟨0|) + S(I/2) = 0 + log 2`. In particular `S(A,B) ≠ 0`, so the witness is mixed. -/
theorem arakiLiebEqualityState_vonNeumannEntropy :
    arakiLiebEqualityState.vonNeumannEntropy = Real.log 2 := by
  rw [arakiLiebEqualityState, State.vonNeumannEntropy_tmul,
    PureState.vonNeumannEntropy_toState_eq_zero, zero_add,
    State.vonNeumannEntropy_maximallyMixed, finrank_qubit_space, Nat.cast_ofNat]

/-- **The witness saturates the triangle inequality**: `S(A,B) = S(B) − S(A)`. Both sides equal
`log 2`, since `S(A,B) = log 2`, `S(B) = log 2` and `S(A) = 0`. This is the equation Exercise 11.17
asks for. -/
theorem arakiLiebEqualityState_vonNeumannEntropy_eq_reducedRight_sub_reducedLeft :
    arakiLiebEqualityState.vonNeumannEntropy =
      arakiLiebEqualityState.reducedRight.vonNeumannEntropy -
        arakiLiebEqualityState.reducedLeft.vonNeumannEntropy := by
  rw [arakiLiebEqualityState_vonNeumannEntropy,
    arakiLiebEqualityState_reducedRight_vonNeumannEntropy,
    arakiLiebEqualityState_reducedLeft_vonNeumannEntropy, sub_zero]

/-- **The witness is genuinely mixed** (non-trivial): `arakiLiebEqualityState` is not a pure state.
A pure state has zero von Neumann entropy, but `S(A,B) = log 2 > 0`. -/
theorem arakiLiebEqualityState_not_isPure : ¬ arakiLiebEqualityState.IsPure := by
  rintro ⟨ψ, hψ⟩
  have h0 : arakiLiebEqualityState.vonNeumannEntropy = 0 := by
    rw [hψ, PureState.vonNeumannEntropy_toState_eq_zero]
  rw [arakiLiebEqualityState_vonNeumannEntropy] at h0
  exact (Real.log_pos (by norm_num)).ne' h0

/-- **N&C Exercise 11.17.** There is an explicit non-trivial (mixed) state `ρ` on `AB` saturating
the Araki–Lieb triangle inequality, i.e. with `S(A,B) = S(B) − S(A)`. The witness is
`arakiLiebEqualityState = |0⟩⟨0|_A ⊗ (I/2)_B`: it is not pure
(`arakiLiebEqualityState_not_isPure`) yet `S(A,B) = S(B) − S(A)`
(`arakiLiebEqualityState_vonNeumannEntropy_eq_reducedRight_sub_reducedLeft`). -/
theorem exists_mixed_state_vonNeumannEntropy_eq_reducedRight_sub_reducedLeft :
    ∃ ρ : State (qubit ⊗ qubit), ¬ ρ.IsPure ∧
      ρ.vonNeumannEntropy =
        ρ.reducedRight.vonNeumannEntropy - ρ.reducedLeft.vonNeumannEntropy :=
  ⟨arakiLiebEqualityState, arakiLiebEqualityState_not_isPure,
    arakiLiebEqualityState_vonNeumannEntropy_eq_reducedRight_sub_reducedLeft⟩

end AxQM
