/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.TraceNorm

/-!
# AxQM — the quantum trace distance (Nielsen & Chuang §9.2.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §9.2.1
(equation `(9.11)`, p. 403) define the **trace distance** between two states
`ρ` and `σ` as
```
D(ρ, σ) ≡ ½ tr|ρ − σ| = ½ ‖ρ − σ‖₁,
```
half the trace norm of the difference of their density operators. It is the
quantum generalization of the classical trace distance
`AxQM.Concrete.classicalTraceDist` (N&C `(9.1)`), and — as N&C stress in
§9.2.1 — it is a genuine *metric* on the space of density operators.

`State.traceDistance` takes two states and returns the real number
`½ ‖ρ.op − σ.op‖₁`.

## Main definitions

* `State.traceDistance` — the trace distance `½ ‖ρ − σ‖₁` of N&C `(9.11)`.

## Main statements

The elementary "distance" properties N&C invoke to justify calling `D` a metric
(the metric axioms, less the triangle inequality):

* `State.traceDistance_nonneg` — `0 ≤ D(ρ, σ)`.
* `State.traceDistance_self` — `D(ρ, ρ) = 0`.
* `State.traceDistance_comm` — symmetry, `D(ρ, σ) = D(σ, ρ)`.
* `State.traceDistance_eq` — the defining equation, `D(ρ, σ) = ½ ‖ρ.op − σ.op‖₁`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **quantum trace distance** between two states `ρ` and `σ` of the system `S`,
Nielsen & Chuang `(9.11)`: `D(ρ, σ) ≡ ½ tr|ρ − σ| = ½ ‖ρ − σ‖₁`, half the trace
norm of the difference of their density operators. The quantum generalization of
the classical trace distance `AxQM.Concrete.classicalTraceDist`, and the
trace distance of states, defined through `.op` and `traceNorm`. -/
noncomputable def State.traceDistance (ρ σ : State S) : ℝ :=
  (ρ.op - σ.op).traceNorm / 2

/-- The defining **equation** for the trace distance: `D(ρ, σ) = ½ ‖ρ.op − σ.op‖₁`.
Unfolds the definition to its underlying trace-norm expression, so that `traceDistance` can be
reasoned about through the trace norm. -/
theorem State.traceDistance_eq (ρ σ : State S) :
    ρ.traceDistance σ = (ρ.op - σ.op).traceNorm / 2 := rfl

/-- The trace distance is **nonnegative**, `0 ≤ D(ρ, σ)` (a metric is nonnegative);
immediate from `ContinuousLinearMap.traceNorm_nonneg`. -/
theorem State.traceDistance_nonneg (ρ σ : State S) : 0 ≤ ρ.traceDistance σ :=
  div_nonneg (ContinuousLinearMap.traceNorm_nonneg _) (by norm_num)

/-- The trace distance of a state from **itself is zero**, `D(ρ, ρ) = 0` (a metric
vanishes on the diagonal): `ρ.op − ρ.op = 0` and `‖0‖₁ = 0`. -/
theorem State.traceDistance_self (ρ : State S) : ρ.traceDistance ρ = 0 := by
  rw [State.traceDistance, sub_self, ContinuousLinearMap.traceNorm_zero, zero_div]

/-- The trace distance is **symmetric**, `D(ρ, σ) = D(σ, ρ)` (a metric is symmetric):
`σ.op − ρ.op = −(ρ.op − σ.op)` and `‖−T‖₁ = ‖T‖₁` (`ContinuousLinearMap.traceNorm_neg`). -/
theorem State.traceDistance_comm (ρ σ : State S) : ρ.traceDistance σ = σ.traceDistance ρ := by
  rw [State.traceDistance, State.traceDistance,
    ← ContinuousLinearMap.traceNorm_neg (σ.op - ρ.op), neg_sub]

/-- The trace distance **vanishes exactly on equal states**, `D(ρ, σ) = 0 ↔ ρ = σ`: the
identity-of-indiscernibles axiom of a metric (N&C note in §9.2.1 that `D(ρ, σ) = 0` iff `ρ = σ`).
Since `D(ρ, σ) = ½‖ρ.op − σ.op‖₁`, the trace distance is zero iff the trace norm of the difference
is zero, iff `ρ.op − σ.op = 0` (`ContinuousLinearMap.traceNorm_eq_zero_iff`), iff `ρ.op = σ.op`,
iff `ρ = σ` (`State.ext`). Together with `traceDistance_nonneg`, `traceDistance_self`,
`traceDistance_comm`, and the triangle inequality this is what makes `D` a genuine metric; it turns
`ρ ≠ σ` into `D(ρ, σ) > 0`, as used in the fixed-point arguments of Exercises 9.10–9.13. -/
theorem State.traceDistance_eq_zero_iff (ρ σ : State S) : ρ.traceDistance σ = 0 ↔ ρ = σ := by
  rw [State.traceDistance_eq, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rw [ContinuousLinearMap.traceNorm_eq_zero_iff, sub_eq_zero] at h
      exact State.ext h
    · norm_num at h
  · rintro rfl
    exact Or.inl (by rw [sub_self, ContinuousLinearMap.traceNorm_zero])

end AxQM
