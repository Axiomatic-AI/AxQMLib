/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Swap

/-!
# Nielsen & Chuang, Exercise 4.18 (Controlled-`Z` is symmetric between control and target)

Show controlled-Z is symmetric between control and target qubits.

The controlled-`Z` gate (`controlledZGate`) and the `SWAP` gate (`Evolution.swap`) are both
closed-system evolutions (Postulate 5 / `Evolution`); the exercise is a *circuit identity* between
these gates. Interchanging the control and target qubits of a two-qubit gate is conjugation by
`SWAP`, so the faithful statement is the equality of `Evolution`s `SWAP · CZ · SWAP = CZ` —
equivalently, that controlled-`Z` commutes with the `SWAP` gate.

## The formalisation

* `AxQM.controlledZGate_swap_symm` — **the exercise:**
  `Evolution.swap · controlledZGate · Evolution.swap = controlledZGate`, i.e.
  `SWAP · CZ · SWAP = CZ`.
  Conjugating the controlled-`Z` gate by the `SWAP` gate — the operation that interchanges the two
  qubits — returns the same gate, which is precisely the statement that its control and target roles
  are interchangeable.

It uses the `SWAP` gate `Evolution.swap` and the operator identity
`controlledZGate_swap_conj_op` (both in `AxQM/Postulates/API/Swap.lean`), which in turn rest on the
pure factor-swap algebra `TensorProduct.commIsometry_conj_mapL` in `ToMathlib/`.

## Design notes

* **Why this shape.** N&C states the symmetry as a circuit identity of
  gates. Here that is the exact equality of the `Evolution` gates `SWAP · CZ · SWAP = CZ`, a full
  unitary identity holding on every input — not a weaker "agrees on the computational basis" or "up
  to phase" surrogate. `SWAP` interchanges the two qubits, so `SWAP · CZ · SWAP` is the
  controlled-`Z` gate run with control and target swapped; asserting it equals `CZ` is exactly that
  controlled-`Z` is symmetric between control and target.
* **Proof.** Immediate from the operator identity `controlledZGate_swap_conj_op`
  (`SWAP.op · CZ.op · SWAP.op = CZ.op`), lifted from operators to the gate `Evolution`s by
  `Evolution.ext` and `Evolution.comp_op`. All the tensor/operator work is inside that lemma;
  the theorem only *applies* it.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.18: the controlled-`Z` gate is symmetric between control and
target.** Conjugating `controlledZGate` by the `SWAP` gate — the gate that interchanges the two
qubits — leaves it unchanged: `Evolution.swap · controlledZGate · Evolution.swap = controlledZGate`,
i.e. `SWAP · CZ · SWAP = CZ`. Equivalently, the controlled-`Z` gate commutes with `SWAP`: which
qubit is designated the control and which the target does not affect the gate. Reduces
(`Evolution.ext`,
`Evolution.comp_op`) to the operator identity `controlledZGate_swap_conj_op`. -/
theorem controlledZGate_swap_symm :
    (Evolution.swap (S := qubit)).comp (controlledZGate.comp (Evolution.swap (S := qubit)))
      = controlledZGate := by
  apply Evolution.ext
  rw [Evolution.comp_op, Evolution.comp_op]
  exact controlledZGate_swap_conj_op

end AxQM
