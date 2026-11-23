/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.LeftPairGate
import AxQM.Postulates.API.ToffoliHadamard

/-!
# AxQM.Postulates.API — arbitrary two-qubit gates on the *control pairs* of three qubits

Infrastructure placing an **arbitrary** two-qubit `Evolution (qubit ⊗ qubit)` on the
two wire pairs of the right-associated three-qubit system `qubit ⊗ (qubit ⊗ qubit)` that involve
the first (control) qubit:

* `leftPairGate U` — `U` on qubits **1, 2** (wires `{0,1}`), qubit 3 idle;
* `outerPairGate U` — `U` on the **outer** qubits **1, 3** (wires `{0,2}`), qubit 2 idle.

The remaining pair (qubits 2, 3, wires `{1,2}`) is already reachable directly as `U.onRight qubit`
(`= 1 ⊗ U`), so together with `onRight` these two placements let one drop an arbitrary two-qubit
gate on *any* of the three wire pairs.

## Why this file exists (Nielsen & Chuang Exercise 4.25, part 4)

Exercise 4.25 part (3) builds the Fredkin gate from **six** two-qubit gates (formalised in
`Core.FredkinTwoQubitCircuit` / `NC/Ch4/Exercise4_25.lean`) and part (4) asks for an even simpler
construction using only **five** two-qubit gates — the Smolin–DiVincenzo result. The five-gate
circuit is *not* expressible in the part-1–3 alphabet `TwoQubitGate3`, whose control-pair gates are
restricted to *controlled single-qubit* gates (`ctrl t g`): with only controlled-unitary gates on
the control pairs and an arbitrary gate on the target pair, the Fredkin gate cannot be reached in
five two-qubit gates even allowing free single-qubit gates — a genuine `√SWAP`-class entangling gate
on a control pair is unavoidable. (Concretely this is the same fact as Problem 3.5, that *classical*
one- and two-bit reversible gates cannot build the Toffoli/Fredkin: the five-gate construction must
use a superposition-creating two-qubit gate on a control pair.)

These two placements supply exactly that missing class of gate — an arbitrary two-qubit gate on a
control pair — and generalise the existing single purpose-built placement `reversedCnotLeftGate`
(which is the `reversedCnotGate` special case of `leftPairGate`, recorded below as
`reversedCnotLeftGate_eq_leftPairGate`).

## What is formalised

* `leftPairGate U` / `outerPairGate U` — the two placements, realised by carrying the left/right
  factor embedding of `U` across the appropriate structural system isomorphism (`QSystem.assoc` for
  the left pair, `QSystem.Iso.leftComm` for the outer pair) with `Evolution.congr`, exactly as
  `reversedCnotLeftGate` does for its special case.
* `leftPairGate_evolvePure` / `outerPairGate_evolvePure` — the **action laws**: how each placement
  acts on a product state `ψ ⊗ (φ ⊗ χ)`, expressed via `U`'s action on the relevant pair (kept
  abstract, so an entangling `U` is handled without expanding it into basis superpositions).
* `leftPairGate_evolvePure_tmul` / `outerPairGate_evolvePure_tmul` — the specialisations for when
  `U`'s action on the pair *is* a product state (the truth-table case), with the associator
  round-trip already discharged.
* `leftPairGate_comp` / `outerPairGate_comp` — the placements are composition homomorphisms.
* `reversedCnotLeftGate_eq_leftPairGate` — the subsumption of the purpose-built gate.
* `leftPairGate_cnotGate` / `leftPairGate_hadamardTmul` — two `leftPairGate` truth-table
  identifications: the forward `CNOT` on the left pair is `cnotLeftGate`, and `H ⊗ H` on the left
  pair splits into the wire-0 and wire-1 Hadamards. The forward-`CNOT` twin of
  `reversedCnotLeftGate_eq_leftPairGate`, and the building blocks a Hadamard-conjugated left-pair
  `CNOT` decomposes into.

## Design notes

* **Construction.** The gates are built from `Evolution.congr`, `QSystem.assoc`,
  `QSystem.Iso.leftComm`, `Evolution.onLeft`/`onRight`, `PureState.congr`, `evolvePure` and `⊗`,
  using the associator / commutation transport API, alongside `reversedCnotLeftGate`, `fredkinGate`
  and the controlled-gate vocabulary.
* **Fidelity / generality.** `U` is an *arbitrary* two-qubit `Evolution`, so the placements are
  fully general (`reversedCnotLeftGate` is one instance); the action laws keep `U`'s action
  abstract, so a genuine entangling square root of `SWAP` can be used
  without ever expanding it into computational-basis coefficients.
* **Proof.** `Evolution.congr_evolvePure_congr` turns each placement's action into `U`'s action on
  the re-bracketed pair, exactly the `reversedCnotLeftGate_evolvePure_qubitBasis` mechanism, and the
  structural transports `pureState_congr_assocSymm` / `pureState_congr_leftCommSymm` re-bracket the
  product state back.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### An arbitrary two-qubit gate on the left pair (qubits 1, 2) -/

/-- **An arbitrary two-qubit gate on qubits 1, 2** (wires `{0,1}`) of the right-associated
three-qubit system, qubit 3 untouched: the two-qubit `U` placed on the left pair of the
left-associated `(qubit ⊗ qubit) ⊗ qubit` via `onLeft` and carried across the associator system
isomorphism `QSystem.assoc`. It generalises `reversedCnotLeftGate` (the `reversedCnotGate` instance,
`reversedCnotLeftGate_eq_leftPairGate`). -/
def leftPairGate (U : Evolution (qubit ⊗ qubit)) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (U.onLeft qubit).congr (QSystem.assoc qubit qubit qubit).symm

/-- **An arbitrary two-qubit gate on the outer qubits 1, 3** (wires `{0,2}`) of the right-associated
three-qubit system, qubit 2 untouched: the two-qubit `U` placed on the *right* factor
`qubit ⊗ qubit` of `qubit ⊗ (qubit ⊗ qubit)` after moving qubit 2 to the front with
`QSystem.Iso.leftComm`, then carried back. Concretely `U` acts on qubits 1 and 3, qubit 2 idle. -/
def outerPairGate (U : Evolution (qubit ⊗ qubit)) : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (U.onRight qubit).congr (QSystem.Iso.leftComm qubit qubit qubit).symm

/-- **`leftPairGate` subsumes `reversedCnotLeftGate`.** The purpose-built reversed-`CNOT` on the
left pair is the `reversedCnotGate` instance of the general placement: both are
`(reversedCnotGate.onLeft qubit).congr (assoc).symm`. -/
theorem reversedCnotLeftGate_eq_leftPairGate :
    reversedCnotLeftGate = leftPairGate reversedCnotGate := rfl

/-! ### Action laws -/

/-- **`leftPairGate` action law.** On a product state `ψ ⊗ (φ ⊗ χ)`, `leftPairGate U` applies `U`
to the front pair `ψ ⊗ φ` (qubits 1, 2) and re-brackets, leaving qubit 3 (`χ`) idle:
`leftPairGate U (ψ ⊗ (φ ⊗ χ)) = ((U (ψ ⊗ φ)) ⊗ χ).congr (assoc).symm`. `U`'s action stays abstract,
so an entangling `U` needs no basis expansion. -/
theorem leftPairGate_evolvePure (U : Evolution (qubit ⊗ qubit)) (ψ φ χ : PureState qubit) :
    (leftPairGate U).evolvePure (ψ ⊗ (φ ⊗ χ))
      = ((U.evolvePure (ψ ⊗ φ)) ⊗ χ).congr (QSystem.assoc qubit qubit qubit).symm := by
  rw [leftPairGate, ← pureState_congr_assocSymm ψ φ χ, Evolution.congr_evolvePure_congr,
    Evolution.onLeft_evolvePure]

/-- **`outerPairGate` action law.** On a product state `ψ ⊗ (φ ⊗ χ)`, `outerPairGate U` applies `U`
to the outer pair `ψ ⊗ χ` (qubits 1, 3) and re-brackets, leaving qubit 2 (`φ`) idle:
`outerPairGate U (ψ ⊗ (φ ⊗ χ)) = (φ ⊗ (U (ψ ⊗ χ))).congr (leftComm).symm`. -/
theorem outerPairGate_evolvePure (U : Evolution (qubit ⊗ qubit)) (ψ φ χ : PureState qubit) :
    (outerPairGate U).evolvePure (ψ ⊗ (φ ⊗ χ))
      = (φ ⊗ (U.evolvePure (ψ ⊗ χ))).congr (QSystem.Iso.leftComm qubit qubit qubit).symm := by
  rw [outerPairGate, ← pureState_congr_leftCommSymm ψ φ χ, Evolution.congr_evolvePure_congr,
    Evolution.onRight_evolvePure]

/-- **`leftPairGate` truth-table specialisation.** When `U` sends `ψ ⊗ φ` to a *product* `ψ' ⊗ φ'`,
`leftPairGate U` sends `ψ ⊗ (φ ⊗ χ)` to `ψ' ⊗ (φ' ⊗ χ)` — the associator round-trip is discharged.
-/
theorem leftPairGate_evolvePure_tmul (U : Evolution (qubit ⊗ qubit))
    (ψ φ χ ψ' φ' : PureState qubit) (h : U.evolvePure (ψ ⊗ φ) = ψ' ⊗ φ') :
    (leftPairGate U).evolvePure (ψ ⊗ (φ ⊗ χ)) = ψ' ⊗ (φ' ⊗ χ) := by
  rw [leftPairGate_evolvePure, h, pureState_congr_assocSymm]

/-- **`outerPairGate` truth-table specialisation.** When `U` sends `ψ ⊗ χ` to a *product* `ψ' ⊗ χ'`,
`outerPairGate U` sends `ψ ⊗ (φ ⊗ χ)` to `ψ' ⊗ (φ ⊗ χ')`. -/
theorem outerPairGate_evolvePure_tmul (U : Evolution (qubit ⊗ qubit))
    (ψ φ χ ψ' χ' : PureState qubit) (h : U.evolvePure (ψ ⊗ χ) = ψ' ⊗ χ') :
    (outerPairGate U).evolvePure (ψ ⊗ (φ ⊗ χ)) = ψ' ⊗ (φ ⊗ χ') := by
  rw [outerPairGate_evolvePure, h, pureState_congr_leftCommSymm]

/-! ### The placements are composition homomorphisms -/

/-- **`leftPairGate` is a composition homomorphism:** placing a product of two-qubit gates on the
left pair composes the placements, `leftPairGate (U · W) = leftPairGate U · leftPairGate W`. Lets
two adjacent left-pair gates merge into one. -/
theorem leftPairGate_comp (U W : Evolution (qubit ⊗ qubit)) :
    leftPairGate (U.comp W) = (leftPairGate U).comp (leftPairGate W) := by
  rw [leftPairGate, leftPairGate, leftPairGate, ← Evolution.onLeft_comp, Evolution.congr_comp]

/-- **`outerPairGate` is a composition homomorphism:**
`outerPairGate (U · W) = outerPairGate U · outerPairGate W`. -/
theorem outerPairGate_comp (U W : Evolution (qubit ⊗ qubit)) :
    outerPairGate (U.comp W) = (outerPairGate U).comp (outerPairGate W) := by
  rw [outerPairGate, outerPairGate, outerPairGate, ← Evolution.onRight_comp, Evolution.congr_comp]

/-! ### `leftPairGate` truth-table identifications -/

/-- **The forward `CNOT` on the left pair is `cnotLeftGate`.**
`leftPairGate cnotGate = cnotLeftGate`: the two-qubit `CNOT` (control first, target second) placed
on qubits 1, 2 of `qubit ⊗ (qubit ⊗ qubit)` is exactly the purpose-built left-pair `CNOT`
`|q₁,q₂,q₃⟩ ↦ |q₁, q₂ ⊕ q₁, q₃⟩`. The forward-`CNOT`
twin of `reversedCnotLeftGate_eq_leftPairGate`. Proved on computational-basis states via
`leftPairGate_evolvePure_tmul` (both `cnotGate` and `cnotLeftGate` are product-preserving). -/
theorem leftPairGate_cnotGate : leftPairGate cnotGate = cnotLeftGate := by
  apply threeQubit_evolution_ext
  intro q1 q2 q3
  rw [leftPairGate_evolvePure_tmul cnotGate (qubitBasis q1) (qubitBasis q2) (qubitBasis q3)
      (qubitBasis q1) (qubitBasis (q2 + q1)) (cnotGate_evolvePure_qubitBasis q1 q2),
    cnotLeftGate_evolvePure_qubitBasis]

/-- **`H ⊗ H` on the left pair splits into the wire-0 and wire-1 Hadamards.**
`leftPairGate (H ⊗ H) = (H ⊗ 1) · (1 ⊗ (H ⊗ 1))`, i.e. the placement of the two-qubit `H ⊗ H` on
qubits 1, 2 of `qubit ⊗ (qubit ⊗ qubit)` is the Hadamard on qubit 1 (`hadamardGate.onLeft (qubit ⊗
qubit)`) composed with the Hadamard on qubit 2 (`(hadamardGate.onLeft qubit).onRight qubit`). Proved
on computational-basis states: `H ⊗ H` sends a product `ψ ⊗ φ` to the product `Hψ ⊗ Hφ`, so
`leftPairGate_evolvePure_tmul` discharges the associator round-trip with no superposition. -/
theorem leftPairGate_hadamardTmul :
    leftPairGate (hadamardGate.tmul hadamardGate)
      = (hadamardGate.onLeft (qubit ⊗ qubit)).comp ((hadamardGate.onLeft qubit).onRight qubit) := by
  apply threeQubit_evolution_ext
  intro q1 q2 q3
  rw [leftPairGate_evolvePure_tmul (hadamardGate.tmul hadamardGate) (qubitBasis q1) (qubitBasis q2)
      (qubitBasis q3) (hadamardGate.evolvePure (qubitBasis q1))
      (hadamardGate.evolvePure (qubitBasis q2)) (Evolution.tmul_evolvePure _ _ _ _)]
  simp only [Evolution.evolvePure_comp, Evolution.onRight_evolvePure, Evolution.onLeft,
    Evolution.tmul_evolvePure, Evolution.id_evolvePure]

end AxQM
