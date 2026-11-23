/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliTrotterStep
import AxQM.Postulates.API.PauliTrotter

/-!
# The `k`-fold Trotter circuit approximates `U` (N&C Problem 4.3(6), operator form)

Nielsen & Chuang, Problem 4.3(6) approximates an arbitrary `n`-qubit unitary `U` by the `k`-fold
power `[∏_g exp(-i h_g g Δ)]ᵏ` of one Trotter step, with `Δ = 1/k`. Part (5)
(`AxQM/Postulates/API/PauliTrotter.lean`) already proves the underlying **operator** bound
`Evolution.exists_pauliString_trotter_approximation`: for suitable real coefficients `h` and a
constant `C`, `‖(∏_g exp(-i h_g g /k))ᵏ - U‖ ≤ C/k`, phrased over the ordered *operator* product
`∏_g ((pauliStringHamiltonian g (h g)).propagator 1 0 (1/k)).op`.

Part (6) needs the same bound stated over the **circuit** `pauliTrotterStep n h (1/k)` — the single
`Evolution` (`AxQM/Postulates/API/PauliTrotterStep.lean`) whose operator *is* that product
(`pauliTrotterStep_op`) and whose gate count is bounded (`pauliTrotterStep_pow_circuitBudget`,
`AxQM/Core/PauliTrotterCapstoneBudget.lean`) — so that the same object carries both an accuracy
bound and a gate count. This file transfers the part-(5) operator bound onto the circuit's `k`-fold
power.

## What this file provides

* `Evolution.exists_pauliTrotterStep_pow_op_sub_le` — the **circuit-level** part-(5) bound: for
  every `U : Evolution (qudit (2ⁿ))` there are Pauli coefficients `h` and a constant `C ≥ 0` such
  that for every `k ≥ 1`, `‖((pauliTrotterStep n h (1/k))ᵏ).op - U.op‖ ≤ C/k`. Immediate from
  `Evolution.exists_pauliString_trotter_approximation`: `Evolution.op_pow` turns
  `((pauliTrotterStep n h (1/k))ᵏ).op` into `(pauliTrotterStep n h (1/k)).op ^ k`, and
  `pauliTrotterStep_op` rewrites `(pauliTrotterStep n h (1/k)).op` into exactly the ordered
  propagator product that bound already controls.

## Design notes

* **Why restate it over the circuit.** The part-(5) theorem is stated over the operator product
  `∏_g (...).op`, a bare operator with no `Evolution` structure — nothing to count gates on. The
  Trotter *circuit* `pauliTrotterStep` is an `Evolution`, so a `CircuitBudget` (a predicate on
  `Evolution`s) can be attached to its `k`-fold power. `pauliTrotterStep_op` is exactly the bridge
  that identifies the two, and this lemma is the accuracy half of Problem 4.3(6) expressed on the
  countable object. The gate-count half is in `AxQM/Core/PauliTrotterCapstoneBudget.lean`;
  `AxQM/NC/Ch4/Problem4_3.lean` combines the two (accuracy via `Evolution.gateError`, gate count
  via `CircuitBudget`) toward N&C's "approximate `U` within `ε` using `O(n·16ⁿ/ε)` gates".
* **The constant `C`.** `C` is the library's *current* first-order Trotter constant of the Pauli
  decomposition — the general Banach constant of
  `NormedSpace.exists_norm_prod_exp_inv_smul_pow_sub_exp_sum_le`, existential and carrying a crude
  `exp(Σ|h_g|)` factor. N&C's `k = O(4ⁿ/ε)` (i.e. `C = O(4ⁿ)`) is rigorous — the unitary Trotter
  error scales as `O((Σ|h_g|)²)/k` with no exponential prefactor — but pinning `C = O(4ⁿ)` needs the
  unitarity-aware Trotter bound + `Σ|h_g| = O(2ⁿ)`, which
  `AxQM/Postulates/API/PauliTrotterExplicit.lean` supplies. See `AxQM/NC/Ch4/Problem4_3.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- **Nielsen & Chuang, Problem 4.3(6), operator form: the `k`-fold Trotter circuit approximates
`U`.** For every `n`-qubit unitary `U : Evolution (qudit (2ⁿ))` there exist real Pauli-string
coefficients `h : (Fin n → Fin 4) → ℝ` and a constant `C ≥ 0` such that for every number of Trotter
repetitions `k ≥ 1`, the circuit `(pauliTrotterStep n h (1/k))ᵏ` — the `k`-fold power of one Trotter
step `∏_g exp(-i h_g g /k)` — approximates `U` to `O(1/k)`:
`‖((pauliTrotterStep n h (k:ℝ)⁻¹) ^ k).op - U.op‖ ≤ C * (k:ℝ)⁻¹`.

This is the part-(5) theorem `Evolution.exists_pauliString_trotter_approximation` transferred from
the bare operator product `∏_g (...).op` onto the circuit `pauliTrotterStep`: `Evolution.op_pow`
identifies `((pauliTrotterStep n h (1/k))ᵏ).op` with `(pauliTrotterStep n h (1/k)).op ^ k`, and the
faithfulness `pauliTrotterStep_op` rewrites the base into the ordered propagator product that bound
controls. It is the accuracy half of Problem 4.3(6), now stated on the countable `Evolution` whose
gate count `pauliTrotterStep_pow_circuitBudget` bounds. -/
theorem Evolution.exists_pauliTrotterStep_pow_op_sub_le (U : Evolution (qudit (2 ^ n))) :
    ∃ (h : (Fin n → Fin 4) → ℝ) (C : ℝ), 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ‖((pauliTrotterStep n h (k : ℝ)⁻¹) ^ k).op - U.op‖ ≤ C * (k : ℝ)⁻¹ := by
  obtain ⟨h, C, hC0, hC⟩ := U.exists_pauliString_trotter_approximation
  refine ⟨h, C, hC0, fun k hk => ?_⟩
  rw [Evolution.op_pow, pauliTrotterStep_op]
  exact hC k hk

end AxQM
