/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerTensorPow
import AxQM.Postulates.API.WirePermutation
import AxQM.Postulates.API.LeftPairGate

/-!
# Placing a wire permutation on the control tower (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit implementing
`Cⁿ(X)`. The grounded `Cⁿ(X) = mcCtrl n pauliXGate` lives on the **right-nested** control
tower `qtower n qubit` (`AxQM/Core/MultiControlledReduction.lean`); bottoming its
multiply-controlled-`NOT` blocks to genuine two-control gates on the tight `(n+1)`-wire register
requires placing a `Toffoli`/`CNOT` on **non-contiguous** wires — done by conjugating a contiguous
gate by the wire permutation that gathers the chosen wires. The wire-permutation gate
`Evolution.permWires` (`AxQM/Postulates/API/WirePermutation.lean`) lives on the **symmetric** power
`qubit ^⊗ₛ (n+1)`, and the `qtower ↔ tensor-power` bridge `qtowerQubitTensorPow`
(`AxQM/Core/QtowerTensorPow.lean`) connects the two registers. This file assembles them: the wire
permutation transported onto the grounded control tower, with its computational-basis action read
off in the tower's own basis `towerKet`.

## What is formalised

* `Evolution.qtowerPermWires σ` — the **wire-permutation gate on the control tower**
  `qtower n qubit`: the symmetric-register gate `Evolution.permWires σ` transported through the
  bridge `(qtowerQubitTensorPow n).symm` by `Evolution.congr`. It is a genuine closed-system
  `Evolution` on
  exactly the `(n+1)`-wire register — no work qubit — realising an arbitrary relabelling of the
  tower's wires.
* `qtowerPermWires_evolvePure_towerKet` — its **computational-basis action** in the tower's own
  basis: `qtowerPermWires σ (towerKet n b) = towerKet n (b ∘ σ⁻¹)`, i.e. the wire carrying `b j` is
  moved to wire `σ j`. This is exactly the wire-addressed placement dictionary the `Cᵏ(X)`-block
  `Toffoli` reduction consumes — the effect of any wire permutation on a computational-basis tower
  input, computed directly.

## Design notes

* **Why the transport route.** `Evolution.permWires` is defined on the symmetric `PiTensorProduct`
  register `qubit ^⊗ₛ (n+1)`, where a factor relabelling is a clean `reindexₗᵢ` (no associator
  surgery). The grounded gate lives on the right-nested `qtower n qubit`. Rather than redefine the
  permutation gate directly on the awkward right-nested tower, we transport the clean symmetric-side
  gate through the structural bridge `qtowerQubitTensorPow` via `Evolution.congr` — reusing the
  basis dictionary `qtowerQubitTensorPow_congr_towerKet` for the basis action.
* **The basis-action proof.** By the transport law `Evolution.congr_evolvePure_congr`, evolving a
  transported state by the transported gate equals the transport of the original action. Feeding the
  tower basis state `towerKet n b`, the backward bridge dictionary
  `qtowerQubitTensorPow_symm_congr_piTensor` (`AxQM/Core/QtowerTensorPow.lean`) rewrites it as the
  transport of the symmetric product basis `⨂ₚ i, |b i⟩`; the general pure-state action
  `Evolution.permWires_evolvePure_piTensor` (`AxQM/Postulates/API/WirePermutation.lean`) permutes
  the factors to `⨂ₚ i, |b (σ⁻¹ i)⟩`; and the same dictionary (applied forwards) folds this back to
  `towerKet n (b ∘ σ⁻¹)`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- **The wire-permutation gate on the control tower** `qtower n qubit`: given a permutation
`σ : Equiv.Perm (Fin (n+1))` of the `n + 1` wires, the closed-system `Evolution` that relabels them
by `σ`. It is the symmetric-register wire-permutation gate `Evolution.permWires σ` (defined on
`qubit ^⊗ₛ (n+1)`) transported onto the right-nested control tower through the
`qtower ↔ tensor-power` bridge `(qtowerQubitTensorPow n).symm` via `Evolution.congr`. It acts on
exactly the `(n+1)`-wire register — no work qubit — and its computational-basis action is
`qtowerPermWires_evolvePure_towerKet`. -/
def Evolution.qtowerPermWires (σ : Equiv.Perm (Fin (n + 1))) : Evolution (qtower n qubit) :=
  Evolution.congr (qtowerQubitTensorPow n).symm (Evolution.permWires σ)

/-- **Computational-basis action of the tower wire-permutation gate.** Applying
`Evolution.qtowerPermWires σ` to the `(n+1)`-qubit computational tower basis state `towerKet n b`
yields `towerKet n (b ∘ σ⁻¹)`: the wire carrying `b j` is moved to wire `σ j`. This is the
wire-addressed placement dictionary — the effect of an arbitrary wire permutation on a
computational-basis tower input, computed directly on the grounded register. Proved from the
transport law `Evolution.congr_evolvePure_congr`, the backward bridge dictionary
`qtowerQubitTensorPow_symm_congr_piTensor`, and the product-basis action
`Evolution.permWires_evolvePure_piTensor`. -/
theorem qtowerPermWires_evolvePure_towerKet (σ : Equiv.Perm (Fin (n + 1)))
    (b : Fin (n + 1) → Fin 2) :
    (Evolution.qtowerPermWires σ).evolvePure (towerKet n b)
      = towerKet n fun i => b (σ.symm i) := by
  -- Transport `towerKet n b` to the symmetric product basis (backward dictionary), apply the
  -- transport law + the product-basis permutation action, then fold back with the same dictionary.
  rw [Evolution.qtowerPermWires, ← qtowerQubitTensorPow_symm_congr_piTensor n b]
  have h := Evolution.congr_evolvePure_congr (qtowerQubitTensorPow n).symm (Evolution.permWires σ)
    (⨂ₚ (i : Fin (n + 1)), qubitBasis (b i))
  rw [h, Evolution.permWires_evolvePure_piTensor]
  exact qtowerQubitTensorPow_symm_congr_piTensor n _

end AxQM
