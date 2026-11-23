/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.LeftPairGate
import AxQM.Concrete.PartialCyclicPermutation

/-!
# Nielsen & Chuang, Exercise 4.27 (partial cyclic permutation from CNOTs and Toffoli gates)

*(N&C p. 183.)*

Using CNOTs and Toffoli gates, build a circuit for a partial cyclic permutation.

`CNOT` and Toffoli gates are closed-system evolutions (Postulate 5 / `Evolution`); the answer is a
concrete circuit — a composition of `CNOT` and Toffoli `Evolution`s — together with the theorem
that it performs the transformation (4.31).

## The transformation (4.31)

The matrix (4.31) is the `8 × 8` permutation matrix that, on the computational basis `|q₁ q₂ q₃⟩`
(value `4q₁ + 2q₂ + q₃`), fixes `|000⟩` and cyclically shifts the seven non-zero basis states
`1 → 2 → 3 → 4 → 5 → 6 → 7 → 1` — the *partial cyclic permutation*
`AxQM.Concrete.partialCyclicShift` (`AxQM/Concrete/PartialCyclicPermutation.lean`, where the
column-by-column reading of (4.31) is recorded). Because every `CNOT`/Toffoli gate fixes `|000⟩`
(all controls off leaves the target unchanged), *any* such circuit necessarily fixes `|000⟩`; this
is exactly why (4.31) is a *partial* cyclic permutation (of the seven non-zero states) rather than
a full increment of all eight.

## The formalisation

* `partialCyclicPermCircuit` — the circuit: an eight-gate composition of `CNOT`s and Toffoli gates
  on `qubit ⊗ (qubit ⊗ qubit)`. Reading in application order (right-to-left in the `comp`),
  `CNOT₁→₂ · CNOT₂→₁ · Toffoli₁,₃→₂ · CNOT₂→₁ · CNOT₃→₂ · Toffoli₁,₂→₃ · CNOT₁→₂ · CNOT₂→₃`, where
  `Toffoli₁,₂→₃ = toffoliGate`, `Toffoli₁,₃→₂ = middleToffoliGate`, `CNOT₂→₃ = cnotGate.onRight`,
  `CNOT₃→₂ = reversedCnotGate.onRight`, `CNOT₁→₂ = cnotLeftGate`, `CNOT₂→₁ = reversedCnotLeftGate`.
* `partialCyclicPermCircuit_evolvePure_qubitBasis` — the exercise's statement: the circuit performs
  the transformation (4.31), `circuit|q₁,q₂,q₃⟩ = |partialCyclicShift q₁ q₂ q₃⟩` for every
  computational basis state, i.e. its action is precisely the permutation matrix (4.31).

## Design notes

* **Statement shape (N&C fidelity).** The exercise asks for a *circuit* implementing (4.31); the
  verifiable content is that a concrete `CNOT`/Toffoli circuit realises the permutation. We give
  the circuit as a named `Evolution` (built only from `CNOT`/Toffoli gates) and state its action on
  every computational basis state — a full truth table equal to the matrix (4.31), not a weaker
  "on some inputs" surrogate. `partialCyclicShift` (`AxQM/Concrete/PartialCyclicPermutation.lean`)
  pins down the target permutation exactly as the columns of (4.31).
* **Finding the circuit.** The gate placements available on the right-associated `qubit ⊗ (qubit ⊗
  qubit)` are the two-control gates `toffoliGate` (target qubit 3) and `middleToffoliGate` (target
  qubit 2), the right-pair `CNOT`s `cnotGate.onRight`/`reversedCnotGate.onRight`, and — reaching
  qubit 1 as a target — the left-pair `CNOT`s `cnotLeftGate` (control 1) and `reversedCnotLeftGate`
  (control 2) from `AxQM/Postulates/API/LeftPairGate.lean`. Flipping qubit 1 is unavoidable (the
  permutation changes qubit 1 on, e.g., `|011⟩ ↦ |100⟩`), so at least one qubit-1-targeting gate
  (`reversedCnotLeftGate`) is required. This eight-gate composition over exactly those gates was
  found by breadth-first search over the basis-state permutations and verified here.
* **Proof route.** `threeQubit`-style evaluation: unfold the eight `comp`s
  (`Evolution.evolvePure_comp`) and rewrite each gate's truth table one at a time
  (`Evolution.onRight_evolvePure` first for the two right-pair `CNOT`s), reducing the left side to a
  single basis state whose three qubit values are `Fin 2` polynomials in `q₁, q₂, q₃`. A case split
  on the eight inputs (`fin_cases`) then reduces both sides — and `partialCyclicShift` — to concrete
  basis states, closed by `Fin 2` arithmetic.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

open Concrete (partialCyclicShift)

/-- **The Exercise 4.27 circuit.** A composition of eight `CNOT` and Toffoli gates on
`qubit ⊗ (qubit ⊗ qubit)` implementing the partial cyclic permutation (4.31). In application order
(innermost first): `CNOT₁→₂`, `CNOT₂→₁`, `Toffoli₁,₃→₂`, `CNOT₂→₁`, `CNOT₃→₂`, `Toffoli₁,₂→₃`,
`CNOT₁→₂`, `CNOT₂→₃`. -/
def partialCyclicPermCircuit : Evolution (qubit ⊗ (qubit ⊗ qubit)) :=
  (cnotGate.onRight qubit).comp
    (cnotLeftGate.comp
      (toffoliGate.comp
        ((reversedCnotGate.onRight qubit).comp
          (reversedCnotLeftGate.comp
            (middleToffoliGate.comp
              (reversedCnotLeftGate.comp cnotLeftGate))))))

/-- **Nielsen & Chuang Exercise 4.27.** The circuit `partialCyclicPermCircuit`, built from `CNOT`
and Toffoli gates alone, performs the transformation (4.31): on every computational basis state
`|q₁, q₂, q₃⟩` it acts as the partial cyclic permutation `partialCyclicShift`, fixing `|000⟩` and
cyclically shifting the seven non-zero basis states. This equality of the circuit's action with the
permutation matrix (4.31) is the content of the exercise. Proved by evaluating the eight gates in
turn on a basis state and case-splitting on the eight inputs. -/
theorem partialCyclicPermCircuit_evolvePure_qubitBasis (q1 q2 q3 : Fin 2) :
    partialCyclicPermCircuit.evolvePure ((qubitBasis q1) ⊗ ((qubitBasis q2) ⊗ (qubitBasis q3)))
      = (qubitBasis (partialCyclicShift q1 q2 q3).1)
          ⊗ ((qubitBasis (partialCyclicShift q1 q2 q3).2.1)
              ⊗ (qubitBasis (partialCyclicShift q1 q2 q3).2.2)) := by
  simp only [partialCyclicPermCircuit, Evolution.evolvePure_comp, Evolution.onRight_evolvePure,
    cnotLeftGate_evolvePure_qubitBasis, reversedCnotLeftGate_evolvePure_qubitBasis,
    middleToffoliGate_evolvePure_qubitBasis, reversedCnotGate_evolvePure_qubitBasis,
    toffoliGate_evolvePure_qubitBasis, cnotGate_evolvePure_qubitBasis]
  fin_cases q1 <;> fin_cases q2 <;> fin_cases q3 <;>
    simp only [partialCyclicShift, Fin.mk_zero, Fin.mk_one, Fin.reduceAdd,
      mul_zero, mul_one, zero_add, add_zero]

end AxQM
