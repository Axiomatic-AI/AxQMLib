/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CNOTDensityMatrix

/-!
# Nielsen & Chuang, Exercise 4.19 (CNOT action on density matrices)

*(N&C p. 179.)*

Write out CNOT action on a density matrix explicitly in the computational basis.

`CNOT` acts on a state (density operator) by conjugation, `ρ ↦ CNOT ρ CNOT†` (Postulate 5,
`Evolution.evolve`). Since `CNOT` merely permutes the computational basis (`|c,t⟩ ↦ |c, t ⊕ c⟩`),
conjugating `ρ` by it rearranges the density-matrix elements: each entry is moved by that same
permutation acting on both its row and its column index — the third and fourth rows/columns are
swapped, everything else fixed.

## Where the formalisation is

The `4 × 4` density matrix of the state and the permutation of its entries is the matrix of a
state's operator, whose entries are inner products `⟪|i⟩, ρ|j⟩⟫`. Compare Exercise 4.16, the
two-qubit *gate* matrix.

**Physics, `AxQM/Postulates/API/CNOTDensityMatrix.lean`.** The gate is an `Evolution`
(Postulate 5); its conjugation action `Evolution.evolve` on a `State` (Postulate 2 / density
operator) is the physical content, so the result is the action on a genuine density matrix.

* `AxQM.State.twoQubitStdMatrix` — the computational-basis density matrix of a two-qubit
  state, `(i, j) ↦ ⟨i|ρ|j⟩`; the density-operator analogue of `Evolution.twoQubitStdMatrix`
  (Exercise 4.16).
* `AxQM.cnotBasisPerm` — the `CNOT` computational-basis permutation `(c, t) ↦ (c, t ⊕ c)`
  as an `Equiv.Perm (Fin 2 × Fin 2)` (`CNOT` "is a simple permutation"), shown to be the
  transposition `|10⟩ ↔ |11⟩` by `AxQM.cnotBasisPerm_eq_swap`.
* `AxQM.cnotGate_evolve_twoQubitStdMatrix` — **the exercise:**
  `(CNOT.evolve ρ).twoQubitStdMatrix = ρ.twoQubitStdMatrix.submatrix cnotBasisPerm cnotBasisPerm`,
  i.e. `⟨(c,t)|CNOT ρ CNOT†|(c',t')⟩ = ⟨(c, t⊕c)|ρ|(c', t'⊕c')⟩` — the explicit rearrangement of the
  density-matrix elements in the computational basis.
-/
