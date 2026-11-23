/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QftSwapEvolution
import AxQM.Concrete.MultiControlledNotPermProduct

/-!
# The reversible ≤ 2-control gates on a register wire
(N&C Exercise 4.43, four-gate bridge — register-side ingredient)

The four-gate universality bridge (Exercise 4.43) must exhibit the *abstract* reachable gate set of
`Concrete.exists_phase_smul_mem_closure_reachableCircuits` as circuits of the grounded
`H, S, CNOT, Toffoli` gates. Its **reversible** generator family is the `≤ 2`-control
permutation gates `Concrete.IsToffoliPermGate enc G` — the `Toffoli`/`CNOT`/`NOT` gates
`permGate enc (mcNotPerm S t)` with `|S| ≤ 2`. This file supplies the *register-side* ingredient
that lets the tower re-expression (`AxQM/Core/FourGateReversibleWireTower.lean`) identify such a
matrix gate, placed on the little-endian register `qudit (2ⁿ)`, with the grounded
multiply-controlled `NOT` `Evolution.placedMcNot` — the exact reversible counterpart of the
rotation register-lift's `AxQM/Postulates/API/FourGateReachableWire.lean`.

## What is formalised

* `mcNotWireEvolution n S t ht` — the multiply-controlled `NOT` with controls `S` and target `t`
  placed on the `2ⁿ`-level register, as a named `Evolution (qudit (2ⁿ))`: the `quditGate` promotion
  of the permutation matrix `Concrete.permGate finFunctionFinEquiv (mcNotPerm S ht)` (unitary, so
  `quditGate` applies). It is the reversible analogue of `rotZWireEvolution`.
* `mcNotWireEvolution_evolvePure_quditBasis` — its **computational-basis action**: on
  `|finFunctionFinEquiv f⟩` it is the classical multiply-controlled `NOT` on the bit-string,
  `|finFunctionFinEquiv (mcNot S t f)⟩`. Unlike the rotation register gate (whose column is a
  genuine two-term superposition), a reversible gate sends a basis state to a *basis state*, so it
  is stated purely over `Evolution.evolvePure` / `quditBasis` / `Concrete.mcNot`. The instance of
  `quditGate_permGate_evolvePure_quditBasis` at `σ = mcNotPerm S ht`, `enc = finFunctionFinEquiv`,
  closed by `mcNotPerm_apply`.
-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The multiply-controlled `NOT` on a register wire set.** The reversible gate with controls
`S : Finset (Fin n)` and target `t ∉ S` placed on the `2ⁿ`-level register, as a named
`Evolution (qudit (2ⁿ))`: the `quditGate` promotion of the permutation matrix
`permGate finFunctionFinEquiv (mcNotPerm S ht)` (unitary by `permGate_mem_unitaryGroup`, so
`quditGate` applies). For `|S| ≤ 2` this is the `Toffoli`/`CNOT`/`NOT` addressed to the wires
`(S, t)` — the reversible generator family of `reachableGateSet`. It is used in the tower
re-expression (`AxQM/Core/FourGateReversibleWireTower.lean`); its basis action is
`mcNotWireEvolution_evolvePure_quditBasis`. The reversible analogue of `rotZWireEvolution`. -/
def mcNotWireEvolution (n : ℕ) (S : Finset (Fin n)) (t : Fin n) (ht : t ∉ S) :
    Evolution (qudit (2 ^ n)) :=
  quditGate (permGate_mem_unitaryGroup finFunctionFinEquiv (mcNotPerm S ht))

/-- **The wire-`(S, t)` multiply-controlled `NOT` is the classical `mcNot` on the bit-string.** On
`|finFunctionFinEquiv f⟩` the register gate `mcNotWireEvolution n S t ht` produces
`|finFunctionFinEquiv (mcNot S t f)⟩`: the bit-string `f` addressing the wires has wire `t` flipped
iff every control in `S` is set. A reversible gate maps a computational basis state to a
computational basis state (no superposition), so this is stated purely over `Evolution.evolvePure` /
`quditBasis` / `Concrete.mcNot`. The instance of
`quditGate_permGate_evolvePure_quditBasis` at `σ = mcNotPerm S ht`, closed by `mcNotPerm_apply`. -/
theorem mcNotWireEvolution_evolvePure_quditBasis (n : ℕ) (S : Finset (Fin n)) (t : Fin n)
    (ht : t ∉ S) (f : Fin n → Fin 2) :
    (mcNotWireEvolution n S t ht).evolvePure (quditBasis (finFunctionFinEquiv f))
      = quditBasis (finFunctionFinEquiv (mcNot S t f)) := by
  have : NeZero (2 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  rw [mcNotWireEvolution, quditGate_permGate_evolvePure_quditBasis, mcNotPerm_apply]

end

end AxQM
