/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Exercise9_13
import AxQM.Postulates.API.DichotomicOperatorSum
import AxQM.Postulates.API.Mixture
import AxQM.Postulates.API.UnreadMeasurement
import AxQM.Postulates.API.NMRSwap
import AxQM.Postulates.API.NMRGroverOracle
import AxQM.Postulates.API.BlochRotationGate

/-!
# Nielsen & Chuang, Exercise 10.2 (Alternate operator-sum representation of the bit flip channel)

Bit flip channel (1-p)rho+pXrhoX has alternate operator-sum rep (1-2p)rho+2pP+rhoP+ +2pP-rhoP-.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 10.2 (p. 429).

## The formalisation

The bit flip channel with flip probability `p` is the library's `bitFlipChannel` in Nielsen &
Chuang's convention: `bitFlipChannel q` flips with probability `1 − q`, so N&C's `E(ρ) = (1 − p)ρ +
pXρX` is `bitFlipChannel (1 − p)`. The exercise's alternate representation is captured by
`bitFlipMeasurementModel`, N&C's *own reading* of that representation as a physical model:

`bitFlipMeasurementModel p ρ = (1 − 2p) ρ + 2p · (ρ measured in the X-eigenbasis, outcome dropped)`,

built from the **binary mixture** `State.mixPair` and the **unread (non-selective)
measurement** `Measurement.unreadState` of the projective `X`-measurement
`Observable.signMeasurement pauliXObservable` (whose Kraus operators are exactly the eigenprojectors
`P₊, P₋`). Its unread post-measurement operator is `P₊ρP₊ + P₋ρP₋`, so the mixture's operator is
`(1 − 2p)ρ + 2p(P₊ρP₊ + P₋ρP₋)` — precisely N&C's right-hand side.

The two theorems are:

* `bitFlipChannel_eq_measurementModel` — **the exercise's identity**: the bit flip channel equals
  the leave-alone/measure model, `bitFlipChannel (1 − p) = bitFlipMeasurementModel p`, for
  `0 ≤ p ≤ 1/2`. This is the statement that the channel admits the alternate operator-sum
  representation; the physical range `p ≤ 1/2` is exactly what makes `1 − 2p ≥ 0` a genuine mixing
  weight (N&C's "with probability `1 − 2p`").
* `bitFlipMeasurementModel_isChannel` — the alternate representation is a genuine CPTP channel
  (`IsChannel`), inherited from `bitFlipChannel_isChannel` through the equality.

The algebraic core `(1 − p)T + p(XTX) = (1 − 2p)T + 2p(P₊TP₊) + 2p(P₋TP₋)` is the lemma
`Observable.dichotomic_operatorSum` in `AxQM/Postulates/API/DichotomicOperatorSum.lean` (it holds
for *any* observable and *any* operator `T`; no involution or `p ≤ 1/2` hypothesis is needed — the
cross terms cancel).

## Design notes

* **Faithfulness.** The left-hand side is the library's canonical `bitFlipChannel` (not a fresh
  restatement), and the identity is proved for arbitrary input `ρ`, so it is the genuine channel
  equality N&C asks for, not a weakened special case. The alternate representation is presented as
  N&C's own physical model ("measured in the `|±⟩` basis with probability `2p`") via the unread
  measurement — a faithful reformulation of the operator sum `2p(P₊ρP₊ + P₋ρP₋)`, which is
  literally the non-selective `X`-measurement channel scaled by `2p`. Trace preservation of the
  alternate representation is automatic: both `State.mixPair` and `Measurement.unreadState` produce
  genuine density operators, so no separate completeness relation is needed.
* **Why `p ≤ 1/2`.** The operator identity itself holds for every real `p`; the hypothesis
  `p ≤ 1/2` enters only to make `1 − 2p` a legitimate mixing probability (so that
  `bitFlipMeasurementModel` is a convex combination of states), matching N&C's stated model and its
  "with probability `1 − 2p`" reading.
* **Reusing the canonical channel.** `bitFlipChannel = (pauliChannel …).apply` is built from the
  Pauli conjugations `pauliChannelUnitary` (axis `π`-rotations). Extracting its operator in
  `X ρ X` form uses the two helper lemmas `pauliChannelUnitary_zero_evolve` (the identity
  conjugation) and `pauliChannelUnitary_one_evolve` (the `X` conjugation, via the global-phase
  equivalence `R_x(π) = e^{-iπ/2} X`), both characterisations of the Pauli channel's
  building blocks.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The zeroth Pauli-channel unitary acts trivially:** `(pauliChannelUnitary 0).evolve ρ = ρ`.
Index `0` is the `π`-free axis rotation `R_x̂(0) = I` (`Concrete.rotAxis_zero`), so its conjugation
channel is the identity. This characterises the Pauli channel's identity term. -/
theorem pauliChannelUnitary_zero_evolve (ρ : State qubit) :
    (pauliChannelUnitary 0).evolve ρ = ρ := by
  have h0 : pauliChannelUnitary 0 = Evolution.id := by
    apply Evolution.ext
    change (rotAxisGate ![1, 0, 0] (0 : ℝ)).op = Evolution.id.op
    rw [Evolution.id_op, rotAxisGate_op, Concrete.rotAxis_zero]
    exact map_one _
  rw [h0]
  exact Evolution.evolve_id ρ

/-- **The first Pauli-channel unitary is the Pauli-`X` conjugation:**
`(pauliChannelUnitary 1).evolve ρ = pauliXGate.evolve ρ`. Index `1` is `R_x̂(π) = e^{-iπ/2} X`
(`rotXGate_pi_eq_globalPhaseGate_comp_pauliXGate`), which differs from the Pauli-`X` gate only by a
global phase, invisible to the conjugation channel (`GlobalPhaseEquiv.evolve`). This
characterises the Pauli channel's `X` term. -/
theorem pauliChannelUnitary_one_evolve (ρ : State qubit) :
    (pauliChannelUnitary 1).evolve ρ = pauliXGate.evolve ρ := by
  have h1 : pauliChannelUnitary 1 = rotXGate Real.pi := by
    apply Evolution.ext
    rfl
  have hge : GlobalPhaseEquiv (pauliChannelUnitary 1) pauliXGate :=
    ⟨-(Real.pi / 2), by rw [h1]; exact rotXGate_pi_eq_globalPhaseGate_comp_pauliXGate⟩
  exact hge.evolve ρ

/-- **The alternate operator-sum representation of the bit flip channel, as N&C's physical model**
(Nielsen & Chuang, Exercise 10.2): with probability `1 − 2p` the qubit is left alone, and with
probability `2p` it is measured in the `X`-eigenbasis `|±⟩` and the outcome discarded. Formally the
binary mixture `State.mixPair (1 − 2p) ρ (E)` of the input `ρ` (weight `1 − 2p`) with the unread
projective `X`-measurement `E = (signMeasurement pauliXObservable).unreadState ρ` (weight `2p`),
whose operator is `P₊ρP₊ + P₋ρP₋`. Requires `0 ≤ p ≤ 1/2` so that `1 − 2p` is a valid mixing
weight. Its density operator is `(1 − 2p)ρ + 2p(P₊ρP₊ + P₋ρP₋)`, matching the right-hand side of the
exercise; `bitFlipChannel_eq_measurementModel` proves it equals the bit flip channel. -/
noncomputable def bitFlipMeasurementModel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    State qubit → State qubit :=
  fun ρ =>
    State.mixPair (p := 1 - 2 * p) (by linarith) (by linarith) ρ
      ((pauliXObservable.signMeasurement pauliXObservable_op_mul_self).unreadState ρ)

/-- **Nielsen & Chuang, Exercise 10.2 — the bit flip channel's alternate operator-sum
representation.** For `0 ≤ p ≤ 1/2`, the bit flip channel `E(ρ) = (1 − p)ρ + pXρX`
(`bitFlipChannel (1 − p)`) equals the leave-alone/measure model
`bitFlipMeasurementModel p`, whose operator is `(1 − 2p)ρ + 2p P₊ρP₊ + 2p P₋ρP₋`. This is the
identity the exercise asks for: the channel admits the alternate operator-sum representation in the
`X`-eigenbasis. The proof computes both channels' density operators — the bit flip channel via its
Pauli-conjugation building blocks (`pauliChannelUnitary_zero_evolve` / `_one_evolve`), the model via
`State.mixPair` and the unread `X`-measurement — and closes with the algebraic identity
`Observable.dichotomic_operatorSum`. -/
theorem bitFlipChannel_eq_measurementModel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    bitFlipChannel (1 - p) (by linarith) (by linarith) = bitFlipMeasurementModel p hp0 hp1 := by
  funext ρ
  apply State.ext
  have hLHS : (bitFlipChannel (1 - p) (by linarith) (by linarith) ρ).op
      = ((1 - p : ℝ) : ℂ) • ρ.op
        + ((p : ℝ) : ℂ) • (pauliXObservable.op * ρ.op * pauliXObservable.op) := by
    unfold bitFlipChannel
    simp only [pauliChannel, RandomUnitaryChannel.apply_op, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, pauliChannelUnitary_zero_evolve,
      pauliChannelUnitary_one_evolve, Complex.ofReal_zero, zero_smul, add_zero]
    rw [Evolution.evolve_op, pauliXGate_op, ← pauliXObservable_op,
      ← ContinuousLinearMap.star_eq_adjoint, pauliXObservable.selfAdjoint.star_eq,
      ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← mul_assoc, sub_sub_cancel]
  have hRHS : (bitFlipMeasurementModel p hp0 hp1 ρ).op
      = ((1 - 2 * p : ℝ) : ℂ) • ρ.op
        + ((2 * p : ℝ) : ℂ) • (pauliXObservable.projPlus * ρ.op * pauliXObservable.projPlus)
        + ((2 * p : ℝ) : ℂ) • (pauliXObservable.projMinus * ρ.op * pauliXObservable.projMinus) := by
    simp only [bitFlipMeasurementModel, State.mixPair_op, Measurement.unreadState_op,
      ContinuousLinearMap.krausSumₗ_apply, Observable.signMeasurement, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      pauliXObservable.adjoint_projPlus, pauliXObservable.adjoint_projMinus]
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← mul_assoc, ← mul_assoc,
      sub_sub_cancel, smul_add, ← add_assoc]
  rw [hLHS, hRHS]
  exact Observable.dichotomic_operatorSum pauliXObservable p ρ.op

/-- **The alternate operator-sum representation is a genuine CPTP channel** (`IsChannel`). Immediate
from `bitFlipChannel_eq_measurementModel` and `bitFlipChannel_isChannel`: the leave-alone/measure
model equals the bit flip channel, which is completely positive and trace preserving. This certifies
that the alternate representation of Exercise 10.2 is a legitimate quantum operation. -/
theorem bitFlipMeasurementModel_isChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    IsChannel (bitFlipMeasurementModel p hp0 hp1) := by
  rw [← bitFlipChannel_eq_measurementModel p hp0 hp1]
  exact bitFlipChannel_isChannel (1 - p) (by linarith) (by linarith)

end AxQM
