/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliStringExpCircuit
import AxQM.Core.PauliDiagWireTower
import AxQM.Core.CnotFanEvolutionBudget
import AxQM.Core.CircuitBudgetAdjoint

/-!
# Problem 4.3(3) gate count: the assembled Figure-4.19 circuit is `O(n)` elementary gates

Problem 4.3(3) asks to implement the Trotter summand `exp(-i h_g g Δ)` — a rotation about the Pauli
string `g` — using `O(n)` one- and two-qubit gates. The *operator faithfulness* of the standard
compute–rotate–uncompute cascade `B ∘ V† ∘ R_z ∘ V ∘ B†` (`pauliStringExpCircuit`) was already
proved: `pauliStringExpCircuit_op_eq_propagator` shows its operator is exactly that summand. This
file supplies the other half of Problem 4.3(3) — the **elementary-gate count** — by giving the
assembled `Evolution` a genuine `CircuitBudget`.

* `pauliStringExpCircuit_circuitBudget` — for a collector `c ∉ ts` on the `(n+1)`-qubit register,
  the cascade `pauliStringExpCircuit (n+1) g c ts θ` has budget
  `CircuitBudget (pauliStringExpCircuit (n+1) g c ts θ) (2 * ts.length) (2 * n + 3)`: at most
  `2 · ts.length` two-qubit (`≤ 2`-control) gates and `2n + 3` single-qubit gates. Since the
  string's support is `insert c ts`, `ts.length = |support| − 1 ≤ n`, so both counts are linear in
  the number of qubits — this is exactly the `O(n)` one- and two-qubit gate count of Problem 4.3(3).

## Where the counts come from

The five pieces of `pauliStringExpCircuit (n+1) g c ts θ = B · V† · R_z · V · B†` each carry a
budget established elsewhere:

* `B = pauliDiagLayer (n+1) g` — the basis-change layer: `n+1` single-qubit gates
  (`pauliDiagLayer_circuitBudget`); `B†` its adjoint, another `n+1` single-qubit gates.
* `V = cnotFanIntoEvolution (n+1) c ts` — the parity `CNOT` fan: `ts.length` two-qubit gates
  (`cnotFanIntoEvolution_circuitBudget`); `V†` its uncomputation, another `ts.length`.
* `R_z = rotZWireEvolution (n+1) c θ` — the collector `z`-rotation: one single-qubit gate
  (`rotZWireEvolution_circuitBudget`).

Summing along the composition (`CircuitBudget.comp` adds budgets; `CircuitBudget.adjoint` preserves
a gate count exactly — reversing a circuit neither adds nor removes gates) gives two-qubit total
`ts.length + ts.length = 2 · ts.length` and single-qubit total `(n+1) + 1 + (n+1) = 2n + 3`;
`CircuitBudget.mono` rewrites the raw folded sums into that closed form.

The `Evolution` `pauliStringExpCircuit` is defined in `Postulates/API/PauliStringExpCircuit`.
-/

namespace AxQM

noncomputable section

/-- **Problem 4.3(3): the Figure-4.19 circuit implementing `exp(-i h_g g Δ)` costs `O(n)` gates.**
For a collector wire `c ∉ ts` on the `(n+1)`-qubit register, the assembled compute–rotate–uncompute
cascade `pauliStringExpCircuit (n+1) g c ts θ = B · V† · R_z · V · B†` has budget

  `CircuitBudget (pauliStringExpCircuit (n+1) g c ts θ) (2 * ts.length) (2 * n + 3)`:

at most `2 · ts.length` two-qubit (`≤ 2`-control) gates and `2n + 3` single-qubit gates. When `g`'s
support is `insert c ts` (the case the faithfulness lemma `pauliStringExpCircuit_op_eq_propagator`
covers) `ts.length = |support| − 1 ≤ n`, so this is the linear — `O(n)` — one- and two-qubit gate
count Problem 4.3(3) demands.

The budget is independent of the correctness hypotheses: it holds for any control list `ts` with
`c ∉ ts` (the only condition the fan's budget needs) and any angle `θ`.

Proof: unfold the cascade into its five `Evolution` factors, fold their budgets with
`CircuitBudget.comp` (the two uncomputations `V†`, `B†` reuse the same forward budgets via
`CircuitBudget.adjoint`, which preserves gate counts exactly), and relax the folded sums to the
closed form `(2 * ts.length, 2 * n + 3)` with `CircuitBudget.mono` (both `≤` are equalities, by
`omega`). -/
theorem pauliStringExpCircuit_circuitBudget {n : ℕ} (g : Fin (n + 1) → Fin 4) (c : Fin (n + 1))
    (ts : List (Fin (n + 1))) (hc : c ∉ ts) (θ : ℝ) :
    CircuitBudget (pauliStringExpCircuit (n + 1) g c ts θ) (2 * ts.length) (2 * n + 3) := by
  rw [pauliStringExpCircuit]
  simp only [Evolution.mul_def]
  refine (((((pauliDiagLayer_circuitBudget n g).comp
        (cnotFanIntoEvolution_circuitBudget c ts hc).adjoint).comp
        (rotZWireEvolution_circuitBudget c θ)).comp
        (cnotFanIntoEvolution_circuitBudget c ts hc)).comp
        (pauliDiagLayer_circuitBudget n g).adjoint).mono ?_ ?_ <;> omega

end

end AxQM
