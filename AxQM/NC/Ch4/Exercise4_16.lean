/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TwoQubitGateMatrix

/-!
# Nielsen & Chuang, Exercise 4.16 (Matrix representation of multi-qubit gates)

*(N&C p. 178.)*

Find the 4x4 unitary matrix for H on one qubit of a two-qubit register.

Applying a single-qubit gate to one qubit of a two-qubit register is the tensor (Kronecker) product
of that gate with the identity on the untouched qubit. With N&C's big-endian ordering `|x₂ x₁⟩`
(the top wire `x₂` the most significant qubit), the two answers are

* top wire: `H ⊗ I = (1/√2) !![1,0,1,0; 0,1,0,1; 1,0,-1,0; 0,1,0,-1]`;
* bottom wire: `I ⊗ H = (1/√2) !![1,1,0,0; 1,-1,0,0; 0,0,1,1; 0,0,1,-1]`.

Compare Exercise 4.13, the circuit identities for `H` (`AxQM/NC/Ch4/Exercise4_13.lean`).

## Where the formalisation is

The `4 × 4` matrix of the gate is the matrix of an evolution's operator, whose entries are inner
products `⟪|i⟩, U|j⟩⟫`; the explicit numeric arrays are matrix mathematics.

**Physics, `AxQM/Postulates/API/TwoQubitGateMatrix.lean`.** The gate is an `Evolution`
(Postulate 5): "`H` on one qubit of the register
`qubit ⊗ qubit` (Postulate 6)" is the product evolution `hadamardGate.onLeft qubit` (`H ⊗ 1`) resp.
`hadamardGate.onRight qubit` (`1 ⊗ H`), which cannot be formed without discharging unitarity, so its
matrix is automatically N&C's *unitary* matrix.

* `AxQM.Evolution.twoQubitStdMatrix` — the operator→matrix bridge: the matrix of an
  evolution on `qubit ⊗ qubit` in the computational product basis (analogue of
  `Observable.stdMatrix`).
* `AxQM.Evolution.twoQubitStdMatrix_tmul_apply` — the tensor factorization
  `⟨(i₁,i₂)|U⊗V|(j₁,j₂)⟩ = ⟪|i₁⟩,U|j₁⟩⟫ · ⟪|i₂⟩,V|j₂⟩⟫`, the reason a one-qubit gate becomes a
  Kronecker product with the identity.
* `AxQM.hadamardOnLeft_twoQubitStdMatrix` /
  `AxQM.hadamardOnRight_twoQubitStdMatrix` — the matrices are `hadamardC ⊗ₖ pauliI`
  (`H ⊗ I`) and `pauliI ⊗ₖ hadamardC` (`I ⊗ H`).
* `AxQM.hadamardOnLeft_flattenFin4` / `AxQM.hadamardOnRight_flattenFin4` — the
  same, flattened to the explicit `4 × 4` arrays above.

**Mathematics, `AxQM/Concrete/HadamardKronecker.lean`.** The explicit arrays and their
unitarity:

* `AxQM.Concrete.flattenFin4_hadamardC_kronecker_pauliI` / `…_pauliI_kronecker_hadamardC` —
  the two explicit `4 × 4` matrices (in basis order `00, 01, 10, 11`).
* `AxQM.Concrete.hadamardC_kronecker_pauliI_mem_unitaryGroup` /
  `…pauliI_kronecker_hadamardC…` — each answer is unitary (the Kronecker product of unitaries is
  unitary; `H` is unitary by Exercise 2.51).
-/
