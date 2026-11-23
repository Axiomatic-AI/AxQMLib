/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumChannel
import AxQM.Postulates.API.PeriodShift
import AxQM.Postulates.Composite
import AxQM.Postulates.Measurement
import ToMathlib.Analysis.InnerProductSpace.Polar

/-!
# AxQM.Postulates.API — the Holevo measurement operation `𝓔` (N&C Exercise 12.2)

The construction realizing **Nielsen & Chuang, Exercise 12.2** (p. 533), the construction used in
the proof of the Holevo bound (Theorem 12.1). The quantum operation `𝓔` there acts on the system `Q`
Alice gives Bob together with Bob's measuring apparatus `M`, performing a measurement with POVM
elements `{E_y}` on `Q` and *storing the outcome* in `M`:

  `𝓔(σ ⊗ |0⟩⟨0|) = ∑_y √E_y σ √E_y ⊗ |y⟩⟨y|`   (Nielsen & Chuang, Eq. (12.8)),

where `|0⟩` is the apparatus' standard (reset) state. Exercise 12.2 asks one to exhibit an explicit
operator-sum (Kraus) representation of `𝓔` and verify it is trace-preserving:

Show {sqrt(E_y) tensor U_y} defines a trace-preserving quantum operation matching (12.8).

## The formalisation

The measurement is modelled by `Measurement (Fin r) Q` (Postulate 3): a
family of measurement operators `M_y` with the completeness relation `∑_y M_y† M_y = 1`. Its induced
POVM has effects `E_y = M_y† M_y`, so the positive square root `√E_y = √(M_y† M_y)` is exactly the
**absolute value** `|M_y|` (`ContinuousLinearMap.absoluteValue`) — a self-adjoint positive operator
with `|M_y|² = M_y† M_y = E_y`. Every POVM `{E_y}` arises as `m.toPOVM` for some measurement `m`
(e.g. `M_y = √E_y`), so this loses no generality. The apparatus `M` is the `r`-level system
`qudit r` (`r = n + 1` outcomes), with computational basis `|y⟩` and the cyclic shift
`U_y = periodShift r y` (`U_y|0⟩ = |y⟩`).

* `holevoMeasurementKraus m y` — the **operation element** `√E_y ⊗ U_y` of outcome `y` on `Q ⊗ M`
  (`TensorProduct.mapL |M_y| U_y`).
* `holevoMeasurementKraus_completeness m` — **the trace-preservation / completeness relation**
  `∑_y (√E_y ⊗ U_y)† (√E_y ⊗ U_y) = 1`, the condition that `{√E_y ⊗ U_y}` defines a
  trace-preserving quantum operation. Each summand factors as `(|M_y|† |M_y|) ⊗ (U_y† U_y) =
  E_y ⊗ 1`, and `∑_y E_y = 1` is the measurement's completeness.
* `holevoMeasurementChannel m` — the resulting **quantum operation `𝓔`** as a channel
  `State (Q ⊗ M) → State (Q ⊗ M)`, `ρ ↦ ∑_y (√E_y ⊗ U_y) ρ (√E_y ⊗ U_y)†`, with
  `holevoMeasurementChannel_isChannel` proving it is a genuine CPTP map (`IsChannel`) via the
  operator-sum direction of N&C Theorem 8.1 (`isChannel_of_kraus`).
* `holevoMeasurementChannel_apply_tmul` — **agreement with (12.8):** on a reset apparatus,
  `𝓔(σ ⊗ |0⟩⟨0|) = ∑_y √E_y σ √E_y ⊗ |y⟩⟨y|`. The two identities used per summand are
  `|M_y|† = |M_y|` (self-adjointness of the square root, so `√E_y σ √E_y†` reads `√E_y σ √E_y`) and
  `U_y |0⟩⟨0| U_y† = |y⟩⟨y|` (`periodShift_op_conj_quditBasisZero`).

The statement of Exercise 12.2 is in `AxQM/NC/Ch12/Exercise12_2.lean`.

## Design notes

* **Generality.** N&C introduces the operation elements `√E_y ⊗ U_y` and asks for two
  facts — that they define a *trace-preserving* operation and that its action matches (12.8). The
  formalisation names the elements as their own `def`, states the completeness relation and the
  channel property as their own theorems, and states the (12.8) agreement over an arbitrary system
  `Q`, an arbitrary measurement `m` on it (arbitrary number of outcomes `r = n + 1`), and an
  arbitrary state `σ` of `Q` — no dimension is fixed and no hypothesis is added beyond `NeZero r`
  (the apparatus must have at least one basis state). The right-hand side is stated in N&C's literal
  Eq. (12.8) shape `∑_y √E_y σ √E_y ⊗ |y⟩⟨y|`, with `√E_y = |M_y|` and `|y⟩⟨y| =
  (quditBasis y).toState.op`.
* **Why `|M_y|` for `√E_y`.** The absolute value `|M_y| = √(M_y† M_y)` is the positive square root
  of the effect `E_y = M_y† M_y` (Postulate 3), so it is literally `√E_y`; the purpose-built lemma
  `absoluteValue_sq` (`|M_y| |M_y| = M_y† M_y`) and its positivity/self-adjointness drive the two
  short proofs, and the completeness relation of `{√E_y ⊗ U_y}` reduces directly to the
  measurement's own completeness `∑_y M_y† M_y = 1`.
* **Proof.** Both theorems are per-summand rewrites over the tensor-operator API:
  `TensorProduct.mapL_adjoint_comp_self` (`(f ⊗ g)† (f ⊗ g) = f†f ⊗ g†g`) for completeness, and
  `TensorProduct.mapL_comp_self` (`(f ⊗ g) X (f ⊗ g)† = fXf† ⊗ gXg†` on a product `X`) for the
  action. Two facts they use are elsewhere: the operator-theory
  fact `|T|† = |T|` (`ContinuousLinearMap.adjoint_absoluteValue`) is in
  `ToMathlib/Analysis/InnerProductSpace/Polar.lean`, and the shift conjugation
  `U_y |0⟩⟨0| U_y† = |y⟩⟨y|` (`periodShift_op_conj_quditBasisZero`) is in
  `AxQM/Postulates/API/PeriodShift.lean`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {Q : QSystem} {r : ℕ} [NeZero r]

/-- **The operation element `√E_y ⊗ U_y` of outcome `y`** (Nielsen & Chuang, Exercise 12.2), on the
composite of the measured system `Q` and the apparatus `qudit r`. Here `√E_y = |M_y|` is the
positive square root of the POVM effect `E_y = M_y† M_y` of the measurement `m` (the absolute value
of the measurement operator `M_y`), and `U_y = periodShift r y` is the cyclic shift storing the
outcome, `U_y|0⟩ = |y⟩`. -/
def holevoMeasurementKraus (m : Measurement (Fin r) Q) (y : Fin r) :
    (Q ⊗ qudit r).space →L[ℂ] (Q ⊗ qudit r).space :=
  TensorProduct.mapL (m.op y).absoluteValue (periodShift r y).op

/-- **Nielsen & Chuang, Exercise 12.2 (trace preservation).** The operation elements `{√E_y ⊗ U_y}`
obey the completeness relation `∑_y (√E_y ⊗ U_y)† (√E_y ⊗ U_y) = 1`, so they define a
*trace-preserving* quantum operation. Each summand is `(|M_y|† |M_y|) ⊗ (U_y† U_y) = (M_y† M_y) ⊗ 1`
— the square root is self-adjoint with `|M_y|² = E_y` (`absoluteValue_sq`) and `U_y` is unitary —
and `∑_y M_y† M_y = 1` is the measurement's completeness (Postulate 3). -/
theorem holevoMeasurementKraus_completeness (m : Measurement (Fin r) Q) :
    ∑ y, (adjoint (holevoMeasurementKraus m y)).comp (holevoMeasurementKraus m y) = 1 := by
  have key : ∀ y : Fin r,
      (adjoint (holevoMeasurementKraus m y)).comp (holevoMeasurementKraus m y)
        = TensorProduct.mapL ((adjoint (m.op y)).comp (m.op y))
            (1 : (qudit r).space →L[ℂ] (qudit r).space) := by
    intro y
    have h := TensorProduct.mapL_adjoint_comp_self (m.op y).absoluteValue (periodShift r y).op
    rw [ContinuousLinearMap.adjoint_absoluteValue, ContinuousLinearMap.absoluteValue_sq,
      (periodShift r y).adjoint_comp_self] at h
    rw [holevoMeasurementKraus]
    exact h
  have step1 : ∑ y, (adjoint (holevoMeasurementKraus m y)).comp (holevoMeasurementKraus m y)
      = ∑ y, TensorProduct.mapL ((adjoint (m.op y)).comp (m.op y))
            (1 : (qudit r).space →L[ℂ] (qudit r).space) :=
    Finset.sum_congr rfl (fun y _ => key y)
  have step2 : ∑ y, TensorProduct.mapL ((adjoint (m.op y)).comp (m.op y))
        (1 : (qudit r).space →L[ℂ] (qudit r).space)
      = TensorProduct.mapL (∑ y, (adjoint (m.op y)).comp (m.op y))
        (1 : (qudit r).space →L[ℂ] (qudit r).space) :=
    (TensorProduct.mapL_sum_left (fun y => (adjoint (m.op y)).comp (m.op y))
      (1 : (qudit r).space →L[ℂ] (qudit r).space)).symm
  rw [m.complete] at step2
  exact step1.trans (step2.trans TensorProduct.mapL_one)

/-- **The Holevo measurement operation `𝓔`** (Nielsen & Chuang, Exercise 12.2 / Eq. (12.8)), as a
quantum channel `State (Q ⊗ M) → State (Q ⊗ M)`: `ρ ↦ ∑_y (√E_y ⊗ U_y) ρ (√E_y ⊗ U_y)†`, the
operator sum of the operation elements `holevoMeasurementKraus m`. It sends a state to a state
because the elements satisfy the completeness relation (`holevoMeasurementKraus_completeness`), so
the Kraus map preserves density operators (`isDensityOp_krausSumₗ`). -/
def holevoMeasurementChannel (m : Measurement (Fin r) Q) :
    State (Q ⊗ qudit r) → State (Q ⊗ qudit r) := fun ρ =>
  { op := ContinuousLinearMap.krausSumₗ (holevoMeasurementKraus m) ρ.op
    isDensity := ContinuousLinearMap.isDensityOp_krausSumₗ (holevoMeasurementKraus m)
      (holevoMeasurementKraus_completeness m) ρ.isDensity }

/-- The underlying operator of the Holevo measurement operation is the Kraus sum
`𝓔(ρ) = ∑_y (√E_y ⊗ U_y) ρ (√E_y ⊗ U_y)†`: the `.op`-unfolding lemma of `holevoMeasurementChannel`
(true by `rfl`), completing the def's API. -/
@[simp]
theorem holevoMeasurementChannel_op (m : Measurement (Fin r) Q) (ρ : State (Q ⊗ qudit r)) :
    (holevoMeasurementChannel m ρ).op
      = ContinuousLinearMap.krausSumₗ (holevoMeasurementKraus m) ρ.op := rfl

/-- **Nielsen & Chuang, Exercise 12.2 (a trace-preserving quantum operation).** The Holevo
measurement operation `𝓔` is a genuine quantum channel (completely positive and trace-preserving):
its operation elements `{√E_y ⊗ U_y}` satisfy the completeness relation, so
`isChannel_of_kraus` (the trace-preserving direction of the operator-sum theorem, N&C Theorem 8.1)
exhibits it as a CPTP map. -/
theorem holevoMeasurementChannel_isChannel (m : Measurement (Fin r) Q) :
    IsChannel (holevoMeasurementChannel m) :=
  isChannel_of_kraus (holevoMeasurementKraus m) (holevoMeasurementKraus_completeness m)
    (fun _ => rfl)

/-- **Nielsen & Chuang, Exercise 12.2 (agreement with Eq. (12.8)).** On a state of the form
`σ ⊗ |0⟩⟨0|` — the system `σ` together with the apparatus in its standard state `|0⟩` — the Holevo
measurement operation acts as

  `𝓔(σ ⊗ |0⟩⟨0|) = ∑_y √E_y σ √E_y ⊗ |y⟩⟨y|`,

exactly Eq. (12.8). Per summand, the Kraus action `(√E_y ⊗ U_y)(σ ⊗ |0⟩⟨0|)(√E_y ⊗ U_y)†` factors
(`TensorProduct.mapL_comp_self`) into `(√E_y σ √E_y†) ⊗ (U_y |0⟩⟨0| U_y†)`; the square root is
self-adjoint (`ContinuousLinearMap.adjoint_absoluteValue`, giving `√E_y σ √E_y`) and the shift moves
the reset projector to `|y⟩⟨y|` (`periodShift_op_conj_quditBasisZero`). Here
`√E_y = (m.op y).absoluteValue` and `|y⟩⟨y| = (quditBasis y).toState.op`. -/
theorem holevoMeasurementChannel_apply_tmul (m : Measurement (Fin r) Q) (σ : State Q) :
    (holevoMeasurementChannel m (σ ⊗ (quditBasis (0 : Fin r)).toState)).op
      = ∑ y, TensorProduct.mapL
          ((m.op y).absoluteValue.comp (σ.op.comp (m.op y).absoluteValue))
          ((quditBasis y).toState.op) := by
  have hks := ContinuousLinearMap.krausSumₗ_apply (holevoMeasurementKraus m)
    (TensorProduct.mapL σ.op (quditBasis (0 : Fin r)).toState.op)
  rw [holevoMeasurementChannel_op, State.tmul_op, hks]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have h := TensorProduct.mapL_comp_self (m.op y).absoluteValue (periodShift r y).op σ.op
    ((quditBasis (0 : Fin r)).toState.op)
  rw [ContinuousLinearMap.adjoint_absoluteValue, periodShift_op_conj_quditBasisZero] at h
  rw [holevoMeasurementKraus]
  exact h

end AxQM
