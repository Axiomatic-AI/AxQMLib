/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary

/-!
# AxQM.Postulates.API — commuting gates on disjoint factors

Two reusable gate-algebra facts about when gates on a composite system **commute**, both instances
of the physical principle *gates acting on disjoint sets of wires commute*. They underpin any
circuit verification where a gate has to be slid past a block of gates that touch other qubits (for
example, moving a `Hadamard` on the target wire past the phase/`CNOT` block on the control wires in
Nielsen & Chuang's Figure 4.9, `AxQM/NC/Ch4/Exercise4_24.lean`).

## Main results

* `Evolution.onLeft_comm_onRight` — a left-factor gate `g ⊗ 1` commutes with a right-factor gate
  `1 ⊗ h`: `(g.onLeft T) · (h.onRight S) = (h.onRight S) · (g.onLeft T)`. Both products equal the
  bare tensor `g ⊗ h`, so they agree; this is the base case of "disjoint factors commute".
* `controlledUnitary_comm_onRight` — a controlled gate `C(U)` commutes with a gate `1 ⊗ Z` on the
  *whole* target factor, provided `U` and `Z` commute there: from `U · Z = Z · U` on `S`,
  `C(U) · (Z.onRight qubit) = (Z.onRight qubit) · C(U)`. The `|0⟩` branch is `1 ⊗ Z` on both sides;
  the `|1⟩` branch needs `U · Z = Z · U` (hence the hypothesis).

Compare the gate-algebra lemmas `controlledUnitary_comp` and `Evolution.onRight_comp`. The proofs
go through the underlying `TensorProduct.mapL` operators (`change` at the raw tensor head, as in
`controlledUnitary_comp`) and run the block-diagonal `mapL` composition algebra.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **Gates on disjoint factors commute (base case).** A gate on the left factor, `g ⊗ 1`
(`g.onLeft T`), and a gate on the right factor, `1 ⊗ h` (`h.onRight S`), commute:
`(g.onLeft T).comp (h.onRight S) = (h.onRight S).comp (g.onLeft T)`. Both composites equal the
product unitary `g ⊗ h` (`(g ⊗ 1)(1 ⊗ h) = g ⊗ h = (1 ⊗ h)(g ⊗ 1)`), proved by cracking to the raw
`TensorProduct.mapL` operators and applying `mapL_comp` with `1 ∘ f = f ∘ 1 = f`. -/
theorem Evolution.onLeft_comm_onRight {S T : QSystem} (g : Evolution S) (h : Evolution T) :
    (g.onLeft T).comp (h.onRight S) = (h.onRight S).comp (g.onLeft T) := by
  apply Evolution.ext
  change (TensorProduct.mapL g.op (1 : T.space →L[ℂ] T.space)).comp
      (TensorProduct.mapL (1 : S.space →L[ℂ] S.space) h.op)
    = (TensorProduct.mapL (1 : S.space →L[ℂ] S.space) h.op).comp
      (TensorProduct.mapL g.op (1 : T.space →L[ℂ] T.space))
  rw [← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

/-- **A controlled gate commutes with a gate on the whole target factor, when the targets commute.**
If `U` and `Z` commute on `S` (`U.comp Z = Z.comp U`), then the controlled-`U` gate `C(U)` commutes
with `1 ⊗ Z` (`Z.onRight qubit`):
`(controlledUnitary U).comp (Z.onRight qubit) = (Z.onRight qubit).comp (controlledUnitary U)`.
Both are block-diagonal: `C(U) = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U` and `1 ⊗ Z`, so their product is
`|0⟩⟨0| ⊗ Z + |1⟩⟨1| ⊗ (U ∘ Z)` one way and `|0⟩⟨0| ⊗ Z + |1⟩⟨1| ⊗ (Z ∘ U)` the other; the
hypothesis `U ∘ Z = Z ∘ U` makes them equal. Proved by cracking to operators at the raw tensor head
and running the `TensorProduct.mapL` composition algebra (as in `controlledUnitary_comp`). -/
theorem controlledUnitary_comm_onRight {S : QSystem} (U Z : Evolution S)
    (h : U.comp Z = Z.comp U) :
    (controlledUnitary U).comp (Z.onRight qubit)
      = (Z.onRight qubit).comp (controlledUnitary U) := by
  have hUZ : U.op.comp Z.op = Z.op.comp U.op := by
    rw [← Evolution.comp_op, h, Evolution.comp_op]
  apply Evolution.ext
  set p0 := InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec
  set p1 := InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec
  change (TensorProduct.mapL p0 (1 : S.space →L[ℂ] S.space) + TensorProduct.mapL p1 U.op).comp
      (TensorProduct.mapL 1 Z.op)
    = (TensorProduct.mapL 1 Z.op).comp
      (TensorProduct.mapL p0 (1 : S.space →L[ℂ] S.space) + TensorProduct.mapL p1 U.op)
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp,
    ← TensorProduct.mapL_comp]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp,
    hUZ]

end AxQM
