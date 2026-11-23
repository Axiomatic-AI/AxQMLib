/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliTrotterSummand
import AxQM.Core.PauliStringExpCircuitBudget
import AxQM.Core.GlobalPhaseCircuitBudget

/-!
# Problem 4.3(6) gate count: the total per-string Trotter summand costs `O(n)` gates

The total summand `pauliTrotterSummand (n+1) g coeff t` (`Postulates/API/PauliTrotterSummand.lean`)
realises `exp(-i · coeff · t · g)` for *every* Pauli string `g` on the `(n+1)`-qubit register. This
file gives it a uniform `O(n)` elementary-gate `CircuitBudget`, the other half of what the full
Trotter step (product over all `4ⁿ` strings) needs to reach the `O(n · 4ⁿ)` and, ultimately,
`O(n · 16ⁿ / ε)` gate counts of Problem 4.3(6).

* `pauliTrotterSummand_circuitBudget` — for every `g : Fin (n+1) → Fin 4`,
  `CircuitBudget (pauliTrotterSummand (n+1) g coeff t) (2 * n) (2 * n + 3)`: at most `2n` two-qubit
  (`≤ 2`-control) and `2n + 3` single-qubit gates — linear in the qubit number, i.e. `O(n)`, for
  *both* the nonempty-support (Pauli rotation) and identity-string (global phase) cases.

## Where the count comes from

The summand splits on the support of `g`:

* **Nonempty support** — the Figure-4.19 cascade `pauliStringExpCircuit (n+1) g c ts (2 coeff t)`,
  budgeted `(2 · ts.length) (2 n + 3)` by `pauliStringExpCircuit_circuitBudget`. Here `ts` is the
  support minus its least element `c`, so `ts.length = |support| − 1 ≤ (n+1) − 1 = n`
  (`Finset.card_erase_of_mem`, `Finset.card_le_univ`); hence `2 · ts.length ≤ 2 n`, and
  `CircuitBudget.mono` relaxes the two-qubit count to `2 n`.
* **Empty support** — the identity string, whose summand is the global phase
  `globalPhaseGate (-(coeff t))`, budgeted `(0) (1)` by `globalPhaseGate_circuitBudget`; `0 ≤ 2 n`
  and `1 ≤ 2 n + 3`, so `CircuitBudget.mono` lifts it to the common bound.

The uniform bound `(2 n, 2 n + 3)` dominates both branches, so the summand — whichever `g` it is
built for — costs `O(n)` gates.
-/

namespace AxQM

noncomputable section

/-- **Problem 4.3(6): the total per-string Trotter summand costs `O(n)` gates.** For every Pauli
string `g : Fin (n+1) → Fin 4`,
`CircuitBudget (pauliTrotterSummand (n+1) g coeff t) (2 * n) (2 * n + 3)`: at most `2n` two-qubit
(`≤ 2`-control) and `2n + 3` single-qubit gates — linear in the number of qubits, N&C's `O(n)`. The
bound is uniform over both cases of the summand: the Figure-4.19 Pauli-rotation cascade
(`pauliStringExpCircuit_circuitBudget`, whose `2 · ts.length ≤ 2n` since `ts` is the support minus
one wire) and the identity string's global phase (`globalPhaseGate_circuitBudget`, budget `0 1`),
each relaxed to the common bound by `CircuitBudget.mono`. -/
theorem pauliTrotterSummand_circuitBudget {n : ℕ} (g : Fin (n + 1) → Fin 4) (coeff t : ℝ) :
    CircuitBudget (pauliTrotterSummand (n + 1) g coeff t) (2 * n) (2 * n + 3) := by
  unfold pauliTrotterSummand
  by_cases hne : (Concrete.pauliStringSupport g).Nonempty
  · -- Nonempty support: the Figure-4.19 cascade, `2·ts.length ≤ 2n`.
    rw [dite_eq_left hne]
    set S := Concrete.pauliStringSupport g with hSdef
    set c := S.min' hne with hcdef
    have hcmem : c ∈ S := S.min'_mem hne
    have hcnotmem : c ∉ (S.erase c).toList := by
      rw [Finset.mem_toList]; exact Finset.notMem_erase c S
    have hlen : (S.erase c).toList.length ≤ n := by
      have hcard : S.card ≤ n + 1 := by
        have h := Finset.card_le_univ S
        rwa [Fintype.card_fin] at h
      rw [Finset.length_toList, Finset.card_erase_of_mem hcmem]
      omega
    exact (pauliStringExpCircuit_circuitBudget g c ((S.erase c).toList) hcnotmem
      (2 * coeff * t)).mono (by omega) (by omega)
  · -- Empty support: the identity string's global phase, budget `0 1`.
    rw [dite_eq_right hne]
    exact (globalPhaseGate_circuitBudget n (-(coeff * t))).mono (by omega) (by omega)

end

end AxQM
