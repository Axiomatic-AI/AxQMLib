/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliTrotterSummand
import AxQM.Postulates.API.PauliTrotter

/-!
# One full Trotter step `∏_g exp(-i h_g g Δ)` over all `4ⁿ` Pauli strings (N&C Problem 4.3(6))

Nielsen & Chuang, Problem 4.3(6) assembles the universal approximation `U ≈ [∏_g exp(-i h_g g Δ)]ᵏ`
as the `k`-fold power (part (5)) of **one Trotter step** — the ordered product, over *all* `4ⁿ`
Pauli strings `g : Fin n → Fin 4`, of the summands `exp(-i h_g g Δ)`. Parts (2)–(5) of Problem 4.3
already prove that this operator product is `O(Δ²)`-close to `exp(-i H Δ)` and its `k`-fold power
`O(1/k)`-close to `U` (`AxQM/Postulates/API/PauliTrotter.lean`). Those bounds are stated over the
**operator** product `∏_g ((pauliStringHamiltonian g (h g)).propagator 1 0 Δ).op`; part (6)
additionally needs the **circuit** — a single `Evolution` — whose *gate count* can be bounded, and
whose operator *is* that product. This file supplies that circuit. The statement of Problem 4.3 is
in `AxQM/NC/Ch4/Problem4_3.lean`.

## What this file provides

* `pauliTrotterStep n h t` — **one full Trotter step** `∏_g exp(-i h_g g t)`, as one
  `Evolution (qudit (2ⁿ))`: the ordered product `(Finset.univ.toList.map fun g =>
  pauliTrotterSummand n g (h g) t).prod` of the total per-string summands
  (`AxQM/Postulates/API/PauliTrotterSummand.lean`), over the fixed list `Finset.univ.toList` of all
  `4ⁿ` Pauli strings. Each factor — including the identity string's global phase — is a genuine
  register `Evolution` (that is exactly why `pauliTrotterSummand` is a *total* function of `g`), so
  the product is a well-defined circuit.

* `pauliTrotterStep_op` — **faithfulness**: the step's operator is N&C's part-(5) propagator
  product, `(pauliTrotterStep n h t).op = (Finset.univ.toList.map fun g =>
  ((pauliStringHamiltonian g (h g)).propagator 1 0 t).op).prod`. Immediate from the summand
  faithfulness `pauliTrotterSummand_op` (uniform in `g`) pushed through `Evolution.op_prod` (the
  operator of an `Evolution`-monoid product is the product of the operators). This is the bridge
  that transfers N&C's parts (4)/(5) — proved for the operator product — onto the circuit
  `pauliTrotterStep`: substituting `t = 1/k` and taking the `k`-fold power
  `pauliTrotterStep_op ▸ (·^k)`
  turns the base of `Evolution.exists_pauliString_trotter_approximation` into `(pauliTrotterStep n h
  (1/k)).op ^ k`, so the universal `O(1/k)` bound holds for the circuit's operator (see
  `AxQM/Postulates/API/PauliTrotterExplicit.lean`).

## Design notes

* **Why a separate `Evolution`, not just the operator product.** N&C's parts (4)/(5) live at the
  operator level; part (6) is an *implementation* claim — approximate `U` with `O(n·16ⁿ/ε)`
  **gates**. A gate count is a `CircuitBudget`, which is a predicate on an `Evolution`, not on an
  operator. So we must exhibit the actual circuit realising the product and count *it*.
  `pauliTrotterStep` is that
  circuit; `pauliTrotterStep_op` certifies it computes the right operator, and
  `pauliTrotterStep_circuitBudget` (`AxQM/Core/PauliTrotterStepBudget.lean`) counts its `O(n·4ⁿ)`
  gates.
* **The fixed ordering.** The list is `Finset.univ.toList` over `Fin n → Fin 4` — *exactly* the
  ordering N&C's part-(4)/(5) forms use in `AxQM/Postulates/API/PauliTrotter.lean`
  (`Observable.exists_norm_prod_pauliStringHamiltonian_propagator_sub_le` and the theorem
  `Evolution.exists_pauliString_trotter_approximation`). Matching the ordering verbatim is what lets
  `pauliTrotterStep_op` rewrite the base of those existing bounds into this circuit's operator
  without any reindexing; N&C fix "any ordering", and the physical content is order-independent.
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- **One full Trotter step** `∏_g exp(-i h_g g t)` (Nielsen & Chuang, Problem 4.3(6)), as one
`Evolution (qudit (2ⁿ))`: the ordered product over *all* `4ⁿ` Pauli strings `g : Fin n → Fin 4` (the
fixed list `Finset.univ.toList`) of the total per-string summands `pauliTrotterSummand n g (h g) t`.
Each summand — including the identity string `g = I^{⊗n}` (whose summand is a global phase) — is a
genuine register `Evolution`, so the product is a well-defined circuit.

Its operator is N&C's part-(5) propagator product (`pauliTrotterStep_op`) and it costs `O(n·4ⁿ)`
one- and two-qubit gates (`pauliTrotterStep_circuitBudget`). For `t = Δ = 1/k` and `h g = h_g` this
is N&C's `∏_g exp(-i h_g g Δ)`, the single Trotter step whose `k`-fold power approximates `U`. -/
def pauliTrotterStep (n : ℕ) (h : (Fin n → Fin 4) → ℝ) (t : ℝ) : Evolution (qudit (2 ^ n)) :=
  (Finset.univ.toList.map fun g => pauliTrotterSummand n g (h g) t).prod

/-- **Nielsen & Chuang, Problem 4.3(6), faithfulness of the full Trotter step.** The operator of one
Trotter step `pauliTrotterStep n h t` is exactly N&C's part-(5) ordered propagator product,
`(pauliTrotterStep n h t).op = (Finset.univ.toList.map fun g =>
((pauliStringHamiltonian g (h g)).propagator 1 0 t).op).prod`.

The operator of an `Evolution`-monoid product is the product of the operators
(`Evolution.op_prod`), so the step's operator is the product of the summand operators; each summand
operator is the corresponding Pauli-string propagator by the uniform faithfulness
`pauliTrotterSummand_op`. This is the identity that transfers N&C's parts (4)/(5) — stated over this
propagator product in `Postulates/API/PauliTrotter` — onto the circuit `pauliTrotterStep`: at
`t = 1/k`, `(pauliTrotterStep n h (1/k)).op ^ k` is exactly the base (raised to the `k`) of
`Evolution.exists_pauliString_trotter_approximation`, so the universal `O(1/k)` approximation of `U`
holds for the circuit's operator. -/
theorem pauliTrotterStep_op (h : (Fin n → Fin 4) → ℝ) (t : ℝ) :
    (pauliTrotterStep n h t).op
      = (Finset.univ.toList.map fun g =>
          ((pauliStringHamiltonian g (h g)).propagator 1 0 t).op).prod := by
  rw [pauliTrotterStep, Evolution.op_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun g _ => ?_)
  exact pauliTrotterSummand_op g (h g) t

end AxQM
