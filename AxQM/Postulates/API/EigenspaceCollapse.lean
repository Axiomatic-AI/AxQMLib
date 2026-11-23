/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasureObservable

/-!
# AxQM.Postulates.API — collapse into the `±1` eigenspaces of an involution observable

The results behind **Nielsen & Chuang, Exercise 5.9**: for a unitary `U`
with eigenvalues `±1` (a self-adjoint involution, `U² = I`), the phase-estimation circuit of
Exercise 4.34 (`measureObservableCircuit U = (H ⊗ 1) · C(U) · (H ⊗ 1)`) collapses an arbitrary input
`|ψ⟩` into one of the two eigenspaces of `U`, with the single ancilla qubit as the classical
indicator of which eigenspace. This file supplies the pieces that Exercise 4.34 did not need — the
`−1`-outcome collapse state, and the fact that *both* collapsed states are genuine `±1` eigenstates
of `U` — used in the statement of the collapse in `AxQM/NC/Ch5/Exercise5_9.lean`.

## What is formalised

The `+1` post-measurement machinery of the sign measurement — `Observable.postMeasPlus`,
`postOp_signMeasurement_zero`, `bornProb_signMeasurement_plus_eq_normSq`,
`postMeasurement_signMeasurement_plus` — is in `AxQM/Postulates/API/PauliMeasurement.lean`
(introduced there for Exercise 2.61's `+1` outcome). This file adds:

* `Observable.postMeasMinus` — the **normalized `−1` post-measurement pure state**
  `P₋|ψ⟩ / ‖P₋|ψ⟩‖`,
  the collapsed target when the `±1` measurement of `A` yields `−1`. The exact `−1` sibling of the
  existing `Observable.postMeasPlus`, with its supporting `postOp_signMeasurement_one`,
  `bornProb_signMeasurement_minus_eq_normSq`, `projMinus_apply_ne_zero_of_bornProb`, and
  `postMeasurement_signMeasurement_minus` (the Postulate-4 collapse to `postMeasMinus`).
* `Observable.postMeasPlus_hasEigenstate` / `Observable.postMeasMinus_hasEigenstate` — **the
  collapse lands in the eigenspace:** the `+1` (resp. `−1`) collapsed state is a genuine `+1`
  (resp. `−1`) eigenstate of `A`, `A |ψ'⟩ = ±|ψ'⟩`. This is the content Exercise 5.9 emphasises
  over 4.34: the post-measurement state is *the corresponding eigenvector*. Proved from
  `Observable.op_mul_projPlus` / `op_mul_projMinus` (`A·P± = ±P±`, so `P±|ψ⟩` is a `±1`
  eigenvector) transported to the
  normalized state via `Observable.hasEigenstate_of_smul`.

Together with `measureObservableCircuit_op_qubitBasisZero_tmul_signMeasurement` (in
`AxQM/Postulates/API/MeasureObservable.lean`, stated over an arbitrary target `S`) — the circuit
sends `|0⟩ ⊗ |ψ⟩` to
`|0⟩ ⊗ M₀|ψ⟩ + |1⟩ ⊗ M₁|ψ⟩` with `M₀ = P₊`, `M₁ = P₋` the operators of `Observable.signMeasurement`
— these say precisely: the circuit realises the sign measurement of `U`; a computational-basis
measurement of the ancilla returns the outcome `i ∈ {0, 1}` (the classical indicator) with Born
probability `‖Mᵢ|ψ⟩‖²`, and collapses the target onto `postMeasPlus`/`postMeasMinus`, a `±1`
eigenstate of `U` — one of the two eigenspaces.

The circuit's deterministic action on a `±1` eigenstate input, with the indicator flagging the
eigenvalue, is stated in `AxQM/NC/Ch5/Exercise5_9.lean`.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Observable

/-! ### The `−1` post-measurement collapse (sibling of the `+1` machinery in `PauliMeasurement`) -/

/-- The post-measurement operation for the `−1` outcome sends `|ψ⟩⟨ψ|` to the rank-one operator
`|P₋ψ⟩⟨P₋ψ|`: `M₁ ρ M₁† = P₋ |ψ⟩⟨ψ| P₋ = |P₋ψ⟩⟨P₋ψ|`, using `adjoint P₋ = P₋` and the rank-one
composition rules. The `−1` sibling of `postOp_signMeasurement_zero`. -/
theorem postOp_signMeasurement_one (A : Observable S) (hinv : A.op * A.op = 1) (ψ : PureState S) :
    ContinuousLinearMap.postOp (A.signMeasurement hinv).op ψ.toState.op 1
      = rankOne ℂ (A.projMinus ψ.vec) (A.projMinus ψ.vec) := by
  simp only [ContinuousLinearMap.postOp, signMeasurement_op_one, PureState.toState_op,
    A.adjoint_projMinus, InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp]

/-- **Born probability of `−1` as a squared norm:** `p(−1) = ‖P₋|ψ⟩‖²`. The `−1` sibling of
`bornProb_signMeasurement_plus_eq_normSq`; certifies that `−1` is a possible outcome (`p ≠ 0`)
exactly when `P₋|ψ⟩ ≠ 0`. -/
theorem bornProb_signMeasurement_minus_eq_normSq (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) :
    (A.signMeasurement hinv).bornProb ψ.toState 1 = ‖A.projMinus ψ.vec‖ ^ 2 := by
  rw [Measurement.bornProb_eq_re_trace_postOp, postOp_signMeasurement_one,
    InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq]

/-- If the `−1` outcome is possible (`p(−1) ≠ 0`), then `P₋|ψ⟩ ≠ 0` — the post-measurement state is
well-defined. Contrapositive of `bornProb_signMeasurement_minus_eq_normSq`. -/
theorem projMinus_apply_ne_zero_of_bornProb (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) (hp : (A.signMeasurement hinv).bornProb ψ.toState 1 ≠ 0) :
    A.projMinus ψ.vec ≠ 0 := by
  intro h0
  apply hp
  rw [bornProb_signMeasurement_minus_eq_normSq, h0, norm_zero]
  norm_num

/-- The **normalized `−1` post-measurement pure state** `P₋|ψ⟩ / ‖P₋|ψ⟩‖` — the collapsed state of
Postulate 4 after the `±1` measurement of `A` yields `−1`, defined when `P₋|ψ⟩ ≠ 0` (i.e. when `−1`
is a possible outcome). It is the `−1` eigenstate of `A`. The `−1` sibling of
`Observable.postMeasPlus`. -/
def postMeasMinus (A : Observable S) (ψ : PureState S) (hne : A.projMinus ψ.vec ≠ 0) :
    PureState S :=
  PureState.normalize (A.projMinus ψ.vec) hne

@[simp]
theorem postMeasMinus_vec (A : Observable S) (ψ : PureState S) (hne : A.projMinus ψ.vec ≠ 0) :
    (A.postMeasMinus ψ hne).vec = ((‖A.projMinus ψ.vec‖ : ℝ) : ℂ)⁻¹ • A.projMinus ψ.vec := rfl

/-- **Postulate 4 (state update), `−1` outcome.** When the `±1` measurement of `A` on `|ψ⟩` yields
`−1`, the system collapses to the normalized state `P₋|ψ⟩ / ‖P₋|ψ⟩‖ = postMeasMinus`. The `−1`
sibling of `postMeasurement_signMeasurement_plus`; stated for
`Measurement.postMeasurement`. -/
theorem postMeasurement_signMeasurement_minus (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) (hne : A.projMinus ψ.vec ≠ 0)
    (hp : (A.signMeasurement hinv).bornProb ψ.toState 1 ≠ 0) :
    (A.signMeasurement hinv).postMeasurement ψ.toState 1 hp = (A.postMeasMinus ψ hne).toState := by
  have htr : RCLike.re (LinearMap.trace ℂ S.space
      ↑(ContinuousLinearMap.postOp (A.signMeasurement hinv).op ψ.toState.op 1))
      = ‖A.projMinus ψ.vec‖ ^ 2 := by
    rw [postOp_signMeasurement_one, InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq]
  apply State.ext
  rw [Measurement.postMeasurement_op, ContinuousLinearMap.postState, htr,
    postOp_signMeasurement_one, PureState.toState_op, postMeasMinus_vec,
    InnerProductSpace.rankOne_smul_smul_self]
  congr 1
  rw [map_inv₀, Complex.conj_ofReal]
  push_cast
  ring

/-! ### The collapse lands in the eigenspace: the collapsed states are `±1` eigenstates -/

/-- **The `+1` collapse is a `+1` eigenstate.** For a `±1` observable `A` (`A² = I`), the
post-measurement state `postMeasPlus = P₊|ψ⟩/‖P₊|ψ⟩‖` is a genuine `+1` eigenstate of `A`:
`A |ψ'⟩ = |ψ'⟩`. From `A·P₊ = P₊` (`op_mul_projPlus`), `P₊|ψ⟩` is a `+1` eigenvector, and rescaling
to the normalized state preserves the eigenvalue (`hasEigenstate_of_smul`). This is Exercise 5.9's
"the post-measurement state is the corresponding eigenvector", `+1` case. -/
theorem postMeasPlus_hasEigenstate (A : Observable S) (hinv : A.op * A.op = 1) (ψ : PureState S)
    (hne : A.projPlus ψ.vec ≠ 0) :
    A.HasEigenstate 1 (A.postMeasPlus ψ hne) := by
  refine A.hasEigenstate_of_smul (A.postMeasPlus_vec ψ hne) ?_
  have h := congrArg (fun T : S.space →L[ℂ] S.space => T ψ.vec) (A.op_mul_projPlus hinv)
  simp only [mul_apply_eq_comp] at h
  rw [h, Complex.ofReal_one, one_smul]

/-- **The `−1` collapse is a `−1` eigenstate.** For a `±1` observable `A` (`A² = I`), the
post-measurement state `postMeasMinus = P₋|ψ⟩/‖P₋|ψ⟩‖` is a genuine `−1` eigenstate of `A`:
`A |ψ'⟩ = −|ψ'⟩`. From `A·P₋ = −P₋` (`op_mul_projMinus`), `P₋|ψ⟩` is a `−1` eigenvector, and
rescaling to the normalized state preserves the eigenvalue. This is Exercise 5.9's "post-measurement
state
is the corresponding eigenvector", `−1` case. -/
theorem postMeasMinus_hasEigenstate (A : Observable S) (hinv : A.op * A.op = 1) (ψ : PureState S)
    (hne : A.projMinus ψ.vec ≠ 0) :
    A.HasEigenstate (-1) (A.postMeasMinus ψ hne) := by
  refine A.hasEigenstate_of_smul (A.postMeasMinus_vec ψ hne) ?_
  have h := congrArg (fun T : S.space →L[ℂ] S.space => T ψ.vec) (A.op_mul_projMinus hinv)
  simp only [mul_apply_eq_comp, _root_.neg_apply] at h
  rw [h]
  push_cast
  module

end Observable

end AxQM
