/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliTrotterStep
import AxQM.Core.PauliTrotterSummandBudget
import AxQM.Core.PhaseLayerBudget

/-!
# Problem 4.3(6) gate count: one full Trotter step costs `O(n·4ⁿ)` gates

The full Trotter step `pauliTrotterStep (n+1) h t` (`Postulates/API/PauliTrotterStep`) is the
ordered product, over all `4ⁿ⁺¹` Pauli strings `g : Fin (n+1) → Fin 4`, of the per-string summands
`exp(-i h_g g t)`. Each summand costs `O(n)` gates uniformly (`pauliTrotterSummand_circuitBudget`,
`Core/PauliTrotterSummandBudget`), so their product — one Trotter step — costs `4ⁿ⁺¹ · O(n) =
O(n·4ⁿ)` gates. This is the per-step count that, taken to the `k = O(4ⁿ/ε)`-th power (part (5)),
gives the `O(n·16ⁿ/ε)` total of Problem 4.3(6).

* `pauliTrotterStep_circuitBudget` — for every `h : (Fin (n+1) → Fin 4) → ℝ` and time `t`,
  `CircuitBudget (pauliTrotterStep (n+1) h t) (4^(n+1) * (2*n)) (4^(n+1) * (2*n+3))`: at most
  `4ⁿ⁺¹ · 2n` two-qubit (`≤ 2`-control) and `4ⁿ⁺¹ · (2n+3)` single-qubit gates — `O(n·4ⁿ)` in the
  qubit number.

## Where the count comes from

The step is a `List.prod` of `4ⁿ⁺¹` factors, one per Pauli string, each budgeted uniformly
`(2n, 2n+3)` by `pauliTrotterSummand_circuitBudget`. The uniform product fold
`CircuitBudget.listProd_uniform` (`Core/CircuitBudget`) turns that into
`CircuitBudget · (l.length · 2n) (l.length · (2n+3))` for the product, where the list length is the
number of Pauli strings `Finset.univ.toList.length = Fintype.card (Fin (n+1) → Fin 4) = 4ⁿ⁺¹`
(`Fintype.card_fun`, `Fintype.card_fin`). The empty-product base the fold needs is the named
register-identity budget `CircuitBudget.id_qudit` (`CircuitBudget (1 : Evolution (qudit (2ⁿ⁺¹)))
0 0`, the qudit-register analogue of `CircuitBudget.id_qtower`).
-/

open scoped InnerProductSpace TensorProduct

namespace AxQM

noncomputable section

/-- **Problem 4.3(6): one full Trotter step costs `O(n·4ⁿ)` gates.** For every coefficient function
`h : (Fin (n+1) → Fin 4) → ℝ` and time `t`,
`CircuitBudget (pauliTrotterStep (n+1) h t) (4^(n+1) * (2*n)) (4^(n+1) * (2*n+3))`: at most
`4ⁿ⁺¹ · 2n` two-qubit (`≤ 2`-control) and `4ⁿ⁺¹ · (2n+3)` single-qubit gates — linear in the qubit
number times the `4ⁿ⁺¹ = O(4ⁿ)` Pauli strings, i.e. N&C's `O(n·4ⁿ)` per Trotter step.

The step is the product over all `4ⁿ⁺¹` Pauli strings of the per-string summands, each budgeted
uniformly `(2n, 2n+3)` by `pauliTrotterSummand_circuitBudget`; the uniform product fold
`CircuitBudget.listProd_uniform` scales that per factor, giving `(l.length · 2n, l.length · (2n+3))`
with `l.length = 4ⁿ⁺¹` the number of Pauli strings (`Fintype.card_fun`). The empty-product base is
the named register-identity budget `CircuitBudget.id_qudit` on `qudit (2ⁿ⁺¹)`. -/
theorem pauliTrotterStep_circuitBudget {n : ℕ} (h : (Fin (n + 1) → Fin 4) → ℝ) (t : ℝ) :
    CircuitBudget (pauliTrotterStep (n + 1) h t)
      (4 ^ (n + 1) * (2 * n)) (4 ^ (n + 1) * (2 * n + 3)) := by
  rw [pauliTrotterStep]
  -- Fold the uniform per-summand budget over the product, over the register-identity base
  -- `CircuitBudget.id_qudit` (the empty-product budget on `qudit (2ⁿ⁺¹)`).
  have hbud := CircuitBudget.listProd_uniform (CircuitBudget.id_qudit n)
    (Finset.univ.toList.map fun g => pauliTrotterSummand (n + 1) g (h g) t)
    (by
      intro E hE
      simp only [List.mem_map] at hE
      obtain ⟨g, -, rfl⟩ := hE
      exact pauliTrotterSummand_circuitBudget g (h g) t)
  -- The number of factors is the number of Pauli strings, `4ⁿ⁺¹`.
  have hlen : (Finset.univ.toList.map fun g => pauliTrotterSummand (n + 1) g (h g) t).length
      = 4 ^ (n + 1) := by
    rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
  rwa [hlen] at hbud

end

end AxQM
