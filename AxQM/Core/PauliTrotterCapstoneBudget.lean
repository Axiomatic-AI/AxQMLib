/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.PauliTrotterStepBudget

/-!
# Problem 4.3(6) gate count: the `k`-fold Trotter circuit costs `O(k·n·4ⁿ)` gates

The Problem 4.3(6) approximation `[∏_g exp(-i h_g g Δ)]ᵏ` is the `k`-fold power of one Trotter step
`pauliTrotterStep (n+1) h t` (`Postulates/API/PauliTrotterStep.lean`), which itself costs `O(n·4ⁿ)`
one- and two-qubit gates (`pauliTrotterStep_circuitBudget`, `Core/PauliTrotterStepBudget.lean`).
Running it `k` times therefore costs `k` times as much — `O(k·n·4ⁿ)` gates. This file records that
`k`-fold count.

* `pauliTrotterStep_pow_circuitBudget` — for every `h : (Fin (n+1) → Fin 4) → ℝ`, time `t`, and
  repetition count `k`,
  `CircuitBudget ((pauliTrotterStep (n+1) h t) ^ k)`
  `(k * (4^(n+1) * (2*n))) (k * (4^(n+1) * (2*n+3)))`: at most `k · 4ⁿ⁺¹ · 2n` two-qubit
  (`≤ 2`-control) and `k · 4ⁿ⁺¹ · (2n+3)` single-qubit gates.

## Where the count comes from

The `k`-fold power `E ^ k` is the product `(List.replicate k E).prod` of `k` copies of `E`
(`List.prod_replicate`). The uniform product fold `CircuitBudget.listProd_uniform`
(`Core/CircuitBudget.lean`) then scales the per-copy budget by the list length `k`
(`List.length_replicate`): every copy is the single Trotter step, budgeted uniformly
`(4^(n+1)·2n, 4^(n+1)·(2n+3))` by `pauliTrotterStep_circuitBudget`, and the empty-product base
is the named register-identity budget `CircuitBudget.id_qudit` on `qudit (2ⁿ⁺¹)`.

## Toward N&C's `O(n·16ⁿ/ε)`

Choosing `k` proportional to `1/ε` (here `k = O(C/ε)` for the first-order Trotter constant `C`,
chosen in `AxQM/NC/Ch4/Problem4_3.lean` so that the part-(5) error `C/k` drops below `ε`)
turns this `O(k·n·4ⁿ)` count into `O(n·4ⁿ·C/ε)`. N&C's `16ⁿ = 4ⁿ · 4ⁿ` is (i) the `4ⁿ⁺¹` gates
*per step* (explicit here) times (ii) the `O(4ⁿ)` *number of steps* `k`. Factor (ii), i.e.
`C = O(4ⁿ)`, is a **rigorous** bound: for a first-order Trotter product of unitaries the error
scales as `O(Λ²)/k`, `Λ = Σ_g |h_g| = O(2ⁿ)` (from `‖H‖ ≤ 2π`), with no exponential prefactor. This
file's budget is uniform in `k`, so it already supplies factor (i) for *any* `k`; pinning
`k = O(4ⁿ/ε)` — i.e. `C = O(4ⁿ)` — needs the unitarity-aware Trotter bound + the coefficient
estimate `Σ_g |h_g| = O(2ⁿ)`, needed for Problem 4.3(6); see `AxQM/NC/Ch4/Problem4_3.lean`.
-/

open scoped InnerProductSpace

namespace AxQM

noncomputable section

/-- **Problem 4.3(6): the `k`-fold Trotter circuit costs `O(k·n·4ⁿ)` gates.** For every coefficient
function `h : (Fin (n+1) → Fin 4) → ℝ`, time `t`, and repetition count `k`,
`CircuitBudget ((pauliTrotterStep (n+1) h t) ^ k)`
`(k * (4^(n+1) * (2*n))) (k * (4^(n+1) * (2*n+3)))`:
at most `k · 4ⁿ⁺¹ · 2n` two-qubit (`≤ 2`-control) and `k · 4ⁿ⁺¹ · (2n+3)` single-qubit gates — the
per-step count `O(n·4ⁿ)` (`pauliTrotterStep_circuitBudget`) multiplied by the `k` repetitions.

The power `E ^ k` is the product of `k` copies of `E` (`List.prod_replicate`); the uniform product
fold `CircuitBudget.listProd_uniform` scales the per-copy Trotter-step budget
`pauliTrotterStep_circuitBudget` by the list length `k` (`List.length_replicate`), over the
register-identity base `CircuitBudget.id_qudit`. Choosing `k = O(C/ε)` (see
`AxQM/NC/Ch4/Problem4_3.lean`) gives an `O(n·4ⁿ·C/ε)` total; N&C's `O(n·16ⁿ/ε)` follows once `C` is
pinned to `O(4ⁿ)` (rigorous; see `AxQM/NC/Ch4/Problem4_3.lean`). -/
theorem pauliTrotterStep_pow_circuitBudget {n : ℕ} (h : (Fin (n + 1) → Fin 4) → ℝ) (t : ℝ)
    (k : ℕ) :
    CircuitBudget ((pauliTrotterStep (n + 1) h t) ^ k)
      (k * (4 ^ (n + 1) * (2 * n))) (k * (4 ^ (n + 1) * (2 * n + 3))) := by
  -- `E ^ k = (List.replicate k E).prod`: fold the per-copy budget over the `k` copies.
  have hbud := CircuitBudget.listProd_uniform (CircuitBudget.id_qudit n)
    (List.replicate k (pauliTrotterStep (n + 1) h t))
    (fun E hE => by
      rw [List.eq_of_mem_replicate hE]; exact pauliTrotterStep_circuitBudget h t)
  rwa [List.length_replicate, List.prod_replicate] at hbud

end

end AxQM
