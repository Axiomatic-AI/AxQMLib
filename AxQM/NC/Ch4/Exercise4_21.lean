/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary

/-!
# Nielsen & Chuang, Exercise 4.21 (Figure 4.8 implements the `C²(U)` operation)

*(N&C p. 181.)*

Verify Figure 4.8 implements the C^2(U) operation.

Figure 4.8 gives the standard decomposition of the doubly-controlled gate `C²(U)` into one- and
two-qubit gates. One picks a single-qubit unitary `V` with `V² = U` and, on three qubits (two
controls `c₁, c₂` and a target `t`), applies — reading the circuit left to right, so the *leftmost*
gate acts first —

1. `C(V)` with control `c₂` on target `t`;
2. `CNOT` with control `c₁` on `c₂`;
3. `C(V†)` with control `c₂` on target `t`;
4. `CNOT` with control `c₁` on `c₂`;
5. `C(V)` with control `c₁` on target `t`.

Casework on `(c₁, c₂)` shows the net operation is `V^{c₁·c₂}` on the target (`V·V† = 1` cancels for
`c₁ ≠ c₂`; `V·V = U` accumulates for `c₁ = c₂ = 1`), i.e. exactly `C²(U)` with `U = V²`.

## The formalisation

Every gate in Figure 4.8 is a closed-system evolution (Postulate 2 / `Evolution`); the exercise
is a *circuit identity* between them, so the faithful statement is an equality of `Evolution`s,
built from `controlledUnitary`, `Evolution.onLeft`/`onRight`, `pauliXGate`, `Evolution.adjoint`
and the gate-monoid composition.

* `AxQM.ccontrolledUnitaryCircuit V` — **the Figure 4.8 circuit** built from the
  square-root gate `V`, as the ordered composition of the five gates above, all placed on the
  right-associated three-qubit system `qubit ⊗ (qubit ⊗ qubit)` (`c₁ ⊗ (c₂ ⊗ t)`).
* `AxQM.ccontrolledUnitaryCircuit_eq_ccontrolledUnitary` — **the exercise:** for *every*
  single-qubit gate `V`, the circuit equals the doubly-controlled gate on `U = V²`,
  `ccontrolledUnitaryCircuit V = ccontrolledUnitary (V.comp V)`.

The doubly-controlled gate `ccontrolledUnitary` (`= C(C(U))`, the C²(U) target of the verification)
and the three-qubit machinery are in `AxQM/Postulates/API/ControlledControlledUnitary.lean`.

## Design notes

* **Statement shape.** N&C fixes `V` by `V² = U`; here `U` is taken to
  be literally `V.comp V`, so the theorem is the fully general "for any `V`, Figure 4.8 built from
  `V` is `C²(V²)`" — no hypothesis to satisfy, no dimension specialised, and `V†` is the genuine
  adjoint gate `V.adjoint` (which is `V⁻¹` because `V` is unitary). It is a full equality of the
  gate `Evolution`s, holding on every input, not an "on basis states / up to phase" surrogate.
* **Placing all five gates without associators.** Choosing the right-associated system
  `c₁ ⊗ (c₂ ⊗ t)` makes each gate a bare composite: gates 1, 3 are `C(V)`, `C(V†)` on the `(c₂, t)`
  factor with the first qubit idle (`Evolution.onRight … qubit`); the `CNOT` on `(c₁, c₂)` is the
  `c₁`-controlled bit flip on the second qubit with the target idle
  (`controlledUnitary (pauliXGate.onLeft qubit)`); and gate 5 is the `c₁`-controlled `V` on the
  target with the second qubit idle (`controlledUnitary (V.onRight qubit)`). No associator or SWAP
  is needed, and `C²(U) = C(C(U))` is definitional on this same system.
* **Proof.** `threeQubit_evolution_ext` reduces the equality to agreement on the eight computational
  basis inputs `|q₁⟩ ⊗ (|q₂⟩ ⊗ |q₃⟩)`; `evolvePure_comp` unfolds the composition; and casework on
  the two controls `(q₁, q₂)` (`fin_cases`) drives the factor-wise gate actions
  (`controlledUnitary_evolvePure_ket{Zero,One}`, `onLeft`/`onRight_evolvePure`, the bit flip
  `pauliXGate_evolvePure_qubitBasis`). The cancellations `V† V = 1`, `V V† = 1` (from unitarity) and
  the accumulation `V (V ψ) = (V²) ψ` close each branch.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The Figure 4.8 circuit** (Nielsen & Chuang §4.3) implementing `C²(V²)` from a single-qubit
square-root gate `V`, on the right-associated three-qubit system `qubit ⊗ (qubit ⊗ qubit)`
(control₁ ⊗ (control₂ ⊗ target)). Reading the circuit left to right — the leftmost gate acts first,
so it is the *innermost* `Evolution.comp` — the five gates are:
`C(V)` on `(c₂, t)`, `CNOT` on `(c₁, c₂)`, `C(V†)` on `(c₂, t)`, `CNOT` on `(c₁, c₂)`, `C(V)` on
`(c₁, t)`. The `CNOT` on `(c₁, c₂)` is the control-`c₁` bit flip of `c₂` with `t` idle
(`controlledUnitary (pauliXGate.onLeft qubit)`); gate 5 is the control-`c₁` `V` on `t` with `c₂`
idle (`controlledUnitary (V.onRight qubit)`). -/
def ccontrolledUnitaryCircuit (V : Evolution qubit) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (controlledUnitary (V.onRight qubit)).comp
    ((controlledUnitary (pauliXGate.onLeft qubit)).comp
      (((controlledUnitary V.adjoint).onRight qubit).comp
        ((controlledUnitary (pauliXGate.onLeft qubit)).comp
          ((controlledUnitary V).onRight qubit))))

/-- **Nielsen & Chuang, Exercise 4.21: Figure 4.8 implements `C²(U)`.** For every single-qubit gate
`V`, the Figure 4.8 circuit built from `V` equals the doubly-controlled gate on `U = V²`:
`ccontrolledUnitaryCircuit V = ccontrolledUnitary (V.comp V)`.

This is the fully general verification: `V` is arbitrary, `U := V.comp V` is its square,
and `V†` is the adjoint gate `V.adjoint = V⁻¹`. Proved by three-qubit computational-basis
extensionality (`threeQubit_evolution_ext`): unfold the composition on a basis input
`|q₁⟩ ⊗ (|q₂⟩ ⊗ |q₃⟩)`, then case on the two controls `(q₁, q₂)`; the factor-wise gate actions and
the unitarity cancellations `V† V = 1`, `V V† = 1`, `V (V ψ) = (V²) ψ` make each of the four
branches agree with `C²(V²)`. -/
theorem ccontrolledUnitaryCircuit_eq_ccontrolledUnitary (V : Evolution qubit) :
    ccontrolledUnitaryCircuit V = ccontrolledUnitary (V.comp V) := by
  -- Verify on each computational-basis input, unfold the composition, case on the two controls.
  -- The unitarity cancellations `V† V = 1`, `V V† = 1` are the lemmas
  -- `Evolution.evolvePure_adjoint_evolvePure`(`'`).
  apply threeQubit_evolution_ext
  intro q1 q2 q3
  simp only [ccontrolledUnitaryCircuit, ccontrolledUnitary, Evolution.evolvePure_comp]
  fin_cases q1 <;> fin_cases q2 <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue,
      Evolution.onLeft_evolvePure, Evolution.onRight_evolvePure,
      controlledUnitary_evolvePure_ketZero, controlledUnitary_evolvePure_ketOne,
      pauliXGate_evolvePure_qubitBasis, Fin.reduceAdd,
      Evolution.evolvePure_adjoint_evolvePure, Evolution.evolvePure_adjoint_evolvePure',
      Evolution.evolvePure_comp]

end AxQM
