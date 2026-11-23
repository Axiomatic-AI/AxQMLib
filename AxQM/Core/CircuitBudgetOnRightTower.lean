/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.CircuitBudgetOnRight
import AxQM.Core.MultiControlledReduction
import AxQM.Postulates.API.MeasureObservableRegister

/-!
# Adding an idle head *tower* preserves the elementary-gate budget (N&C Problem 4.1)

The single-qubit closure `CircuitBudget.onRight` (`Core/CircuitBudgetOnRight`) prepends **one** idle
head qubit to a budgeted circuit without changing its gate count. Problem 4.1's phase layer `D`,
however, is applied on the *ancilla* of the two-register circuit `qudit (2^m) ⊗ qudit (2^n)` — so to
budget the full phase block `I_A ⊗ D` we must prepend the whole idle **input register** `I_A`, a
tower of `m` qubits, not one. This file supplies that iterated closure.

* `CircuitBudget.onRight_qtower` — the **tower closure**:
  `CircuitBudget E t s → CircuitBudget (E.onRight (qtower k qubit)) t s`. Prepending the idle
  `(k+1)`-qubit control tower `qtower k qubit` (`= qubitᵏ⁺¹`) adds no gates. Proved by induction on
  `k`: the base `qtower 0 qubit = qubit` is the single-qubit closure `CircuitBudget.onRight`, and
  each step peels the head qubit off the tower (`qtower (k+1) qubit = qubit ⊗ qtower k qubit`
  definitionally), applies `CircuitBudget.onRight` to the inductive hypothesis, and re-associates
  the two idle heads with `Evolution.congr_assoc_onRight_onRight` + `CircuitBudget.congr`.

The associator naturality it iterates, `Evolution.congr_assoc_onRight_onRight` (the onRight mirror
of `Evolution.congr_assoc_symm_onLeft_onLeft`), is a general `Evolution.congr`/`onRight` transport
with no budget content; it is in `AxQM/Postulates/API/MeasureObservableRegister.lean` with the rest
of the `congr∘assoc∘{onLeft,onRight}` naturality family.

Its Problem 4.1 use: with `E = D = diagPhase (computablePhaseAngle (n+1))` and the input register
`qudit (2^(m+1)) ≃ qtower m qubit` (`quditPowTower`), this gives
`CircuitBudget (I_A ⊗ D) 0 (n+1)` — the `n` single-qubit phase gates of the `2T + n` count, now on
the *full* input⊗ancilla register, which is then composed with the oracle's `2T`
Toffoli gates (`diagPhase_computablePhaseAngle_onRight_circuitBudget` in
`AxQM/NC/Ch4/Problem4_1.lean`).
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

noncomputable section

/-- **Prepending an idle control tower preserves the elementary-gate budget** (N&C Problem 4.1, the
idle input register of `I_A ⊗ D`). If `E` is built from at most `t` `≤ 2`-control gates and `s`
single-qubit gates, then so is the idle-tower wrap `1_{qtowerᵏ} ⊗ E = E.onRight (qtower k qubit)`:
prepending the untouched `(k+1)`-qubit tower `qtower k qubit` adds no gates,
`CircuitBudget E t s → CircuitBudget (E.onRight (qtower k qubit)) t s`.

Proved by induction on `k`:

* `k = 0`: `qtower 0 qubit = qubit`, so this is the single-qubit closure `CircuitBudget.onRight`.
* `k + 1`: `qtower (k+1) qubit = qubit ⊗ qtower k qubit` (definitionally), so the goal is
  `CircuitBudget (E.onRight (qubit ⊗ qtower k qubit)) t s`. By
  `Evolution.congr_assoc_onRight_onRight`, that circuit is the associator transport of
  `(E.onRight (qtower k qubit)).onRight qubit` — the inductive hypothesis with one further idle head
  qubit (`CircuitBudget.onRight`), whose budget is preserved by `CircuitBudget.congr`. -/
theorem CircuitBudget.onRight_qtower {R : QSystem} {E : Evolution R} {t s : ℕ}
    (h : CircuitBudget E t s) (k : ℕ) :
    CircuitBudget (E.onRight (qtower k qubit)) t s := by
  induction k with
  | zero => exact h.onRight
  | succ k ih =>
      change CircuitBudget (E.onRight (qubit ⊗ qtower k qubit)) t s
      rw [← Evolution.congr_assoc_onRight_onRight E qubit (qtower k qubit)]
      exact CircuitBudget.congr _ ih.onRight

end

end AxQM
