/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.CircuitBudgetSingleWire
import AxQM.Core.PhaseWireTower
import AxQM.Core.QtowerTensorPow

/-!
# The phase layer of Problem 4.1 is `n` single-qubit gates (N&C Problem 4.1, the `n` of `2T + n`)

Problem 4.1's phase layer `D = diagPhase (computablePhaseAngle n)` is, in the textbook construction,
**`n` single-qubit phase gates** — one on each ancilla wire. The elementary-gate budget
`CircuitBudget E t s` (`Core/CircuitBudget`) counts gates on the qubit control tower, where a single
tower-wire gate has budget `0 1` (`qtowerSingleWire_circuitBudget`), and the
phase-gradient layer read on the tower is the ordered product of those wire gates
(`quditPowTower_congr_phaseGradientLayer`). This file assembles those two facts into the
gate-count of the whole phase layer.

* `CircuitBudget.listProd` — the **product fold**: a `List.prod` of gates each costing `0 1` costs
  `0 (length)`. The reusable accountant behind every wire-by-wire layer: `comp` sums the budgets
  down the list, with the empty product discharged by an identity budget on the register (supplied
  as a hypothesis, since a general system carries no elementary-gate budget for `1`).

* `CircuitBudget.id_qtower` — the **tower identity budget** `CircuitBudget (1 : Evolution (qtower n
  qubit)) 0 0`: the identity on the qubit tower is an empty circuit, `0` gates. Proved by the empty
  `block` leaf on `qubit ^⊗ₛ (n+1)` transported back across the tower bridge `qtowerQubitTensorPow`
  (`congr` of `1` is `1`). This is the base the product fold needs on the tower register.

* `phaseGradientLayer_circuitBudget` — **the phase-layer budget**:
  `CircuitBudget (phaseGradientLayer (n+1) φ) 0 (n+1)`. The register `qudit (2ⁿ⁺¹)`'s phase-gradient
  layer — the product of the `n+1` single-wire phase gates `phaseWireEvolution (n+1) t (φ t)` —
  costs at most `n+1` single-qubit gates and no `≤ 2`-control gates, whatever the per-wire angles
  `φ`. Proof: transport the layer onto the tower (`quditPowTower_congr_phaseGradientLayer`), where
  it is the product of `n+1` single-wire gates each budgeted `0 1`
  (`qtowerSingleWire_circuitBudget`); fold with `CircuitBudget.listProd` to get
  `0 (n+1)`; then transport the budget back off the tower (`CircuitBudget.congr` +
  `Evolution.congr_symm_congr`).

The `n+1` here is exactly the ancilla size: the phase layer of an `(n+1)`-qubit ancilla is `n+1`
single-qubit gates, faithful to the exercise's positive integer `n`. Its instance at the computable
phase angle — `D = diagPhase (computablePhaseAngle (n+1))`, via
`phaseGradientLayer_phaseWireAngle_eq_diagPhase` — is `diagPhase_computablePhaseAngle_circuitBudget`
in `AxQM/NC/Ch4/Problem4_1.lean`, the `CircuitBudget D 0 n` ingredient of the `2T + n`
bound.
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

noncomputable section

/-- **A product of single-qubit gates costs one gate per factor.** If every gate in a list `l` has
budget `CircuitBudget · 0 1` (one single-qubit gate, no `≤ 2`-control gates), then their composition
`l.prod` has `CircuitBudget l.prod 0 l.length` — the single-qubit counts add down the list. The
reusable fold behind a wire-by-wire gate layer (Problem 4.1's phase gradient, the QFT rotation
cascades of Problem 5.1/5.2). The empty product `1` needs an identity budget on the register, passed
as `hid` because a general system `S` carries no elementary-gate witness for `1` (its constructors
place gates on qubit registers only); on a qubit tower `hid` is `CircuitBudget.id_qtower`. The
`t₀ = 0, s₀ = 1` specialisation of the general uniform fold `CircuitBudget.listProd_uniform`
(`l.length * 0 = 0`, `l.length * 1 = l.length`). -/
theorem CircuitBudget.listProd {S : QSystem} (hid : CircuitBudget (1 : Evolution S) 0 0)
    (l : List (Evolution S)) (h : ∀ E ∈ l, CircuitBudget E 0 1) :
    CircuitBudget l.prod 0 l.length := by
  simpa using CircuitBudget.listProd_uniform hid l h

/-- **The identity on a qubit tower is a zero-gate circuit.**
`CircuitBudget (1 : Evolution (qtower n qubit)) 0 0` — the identity evolution on the `(n+1)`-qubit
control tower has budget `0 0`, since it is the empty circuit. Proved from the empty-list `block`
leaf `CircuitBudget (1 : Evolution (qubit ^⊗ₛ (n+1))) 0 0` (the classical circuit `[]` realises `1`,
`mcNotDenote_nil`), transported off the tensor power back onto the tower along the bridge
`qtowerQubitTensorPow n` (the transport of `1` is `1`, `Evolution.congr_one`). This is the
register-identity base the product fold `CircuitBudget.listProd` consumes on a tower. -/
theorem CircuitBudget.id_qtower (n : ℕ) : CircuitBudget (1 : Evolution (qtower n qubit)) 0 0 := by
  have hblk : CircuitBudget (1 : Evolution (qubit.tensorPow (n + 1))) 0 0 := by
    have h := CircuitBudget.block ([] : List (Concrete.McNotGate (n + 1)))
      (1 : Evolution (qubit.tensorPow (n + 1))) (by simp) (by
        intro c
        erw [Evolution.one_def, Evolution.id_evolvePure]
        simp only [Concrete.mcNotDenote_nil]
        rfl)
    simpa using h
  rw [← Evolution.congr_one (qtowerQubitTensorPow n).symm]
  exact CircuitBudget.congr (qtowerQubitTensorPow n).symm hblk

/-- **The identity on the `2ⁿ⁺¹`-level qudit register is a zero-gate circuit.**
`CircuitBudget (1 : Evolution (qudit (2ⁿ⁺¹))) 0 0` — the register-identity base the product folds
`CircuitBudget.listProd`/`listProd_uniform` consume on a `qudit (2ⁿ⁺¹)` register, the qudit-side
analogue of `CircuitBudget.id_qtower`. Obtained by transporting the tower identity budget
`id_qtower` back onto the register along the register↔tower bridge `quditPowTower n`
(`CircuitBudget.congr`), the transport of `1` being `1` (`Evolution.congr_one`). This is the base
every wire-by-wire register layer needs on `qudit (2ⁿ⁺¹)` — e.g. the Problem 4.3(6) Trotter step
`pauliTrotterStep_circuitBudget` and its `k`-fold power. -/
theorem CircuitBudget.id_qudit (n : ℕ) :
    CircuitBudget (1 : Evolution (qudit (2 ^ (n + 1)))) 0 0 := by
  rw [← Evolution.congr_one (quditPowTower n).symm]
  exact CircuitBudget.congr (quditPowTower n).symm (CircuitBudget.id_qtower n)

/-- **Problem 4.1's phase layer is `n+1` single-qubit gates.** For any per-wire angles
`φ : Fin (n+1) → ℝ`, the phase-gradient layer `phaseGradientLayer (n+1) φ` on the `(n+1)`-qubit
ancilla register `qudit (2ⁿ⁺¹)` — the product of the `n+1` single-wire phase gates
`phaseWireEvolution (n+1) t (φ t)` — has budget

`CircuitBudget (phaseGradientLayer (n+1) φ) 0 (n+1)`:

at most `n+1` single-qubit gates and **no** `≤ 2`-control gates. This is the `n` (here the ancilla
size `n+1`) of Problem 4.1's `2T + n` gate count, made a genuine `CircuitBudget`.

Proof: transport the layer onto the qubit control tower via
`quditPowTower_congr_phaseGradientLayer`, where it is the ordered product of the `n+1` single-wire
gates
`qtowerSingleWire n t.rev (phaseShiftGate (φ t))`, each budgeted `0 1` by
`qtowerSingleWire_circuitBudget`; fold those with `CircuitBudget.listProd` (base
`CircuitBudget.id_qtower`) to get budget `0 (n+1)` for the tower product; then carry the budget back
off the tower with `CircuitBudget.congr (quditPowTower n).symm` and `Evolution.congr_symm_congr`. -/
theorem phaseGradientLayer_circuitBudget (n : ℕ) (φ : Fin (n + 1) → ℝ) :
    CircuitBudget (phaseGradientLayer (n + 1) φ) 0 (n + 1) := by
  -- Rewrite the goal, via the tower round-trip, to the transported layer — the product of `n+1`
  -- single-wire phase gates — on the tower, then budget that product wire-by-wire.
  rw [← Evolution.congr_symm_congr (quditPowTower n) (phaseGradientLayer (n + 1) φ),
    quditPowTower_congr_phaseGradientLayer]
  refine CircuitBudget.congr (quditPowTower n).symm ?_
  have hbud := CircuitBudget.listProd (CircuitBudget.id_qtower n)
    ((List.finRange (n + 1)).map
      (fun t => Evolution.qtowerSingleWire n t.rev (phaseShiftGate (φ t))))
    (by
      intro E hE
      simp only [List.mem_map] at hE
      obtain ⟨t, -, rfl⟩ := hE
      exact qtowerSingleWire_circuitBudget n t.rev (phaseShiftGate (φ t)))
  rwa [List.length_map, List.length_finRange] at hbud

end

end AxQM
