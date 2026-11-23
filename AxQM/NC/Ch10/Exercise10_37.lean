/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CnotYConjugation

/-!
# Nielsen & Chuang, Exercise 10.37 — Compute `U Y₁ U†` for the CNOT gate `U`

*(N&C p. 460.)*

This exercise asks to compute the conjugation of the Pauli operator `Y₁ = Y ⊗ I` by the two-qubit
controlled-NOT gate `U` (control = first qubit), continuing the stabilizer-formalism tableau of
§10.5.1 (Exercise 10.36 covers `X₁, X₂, Z₁, Z₂`). The answer is
`U Y₁ U† = Y₁ X₂ = Y ⊗ X`.

The formalization is in
`AxQM/Concrete/CnotYConjugation.lean`:

* `AxQM.Concrete.twoQubitCNOT_conj_pauliY_kron_pauliI` —
  `U Y₁ U† = Y ⊗ X` (closed form).
* `AxQM.Concrete.twoQubitCNOT_conj_pauliY_kron_pauliI_eq_mul` —
  `U Y₁ U† = Y₁ X₂` (Nielsen & Chuang's product form).
* `AxQM.Concrete.pauliY_kron_pauliI_mul_pauliI_kron_pauliX` —
  `Y₁ X₂ = Y ⊗ X`, the bridge between the two forms.
* `AxQM.Concrete.twoQubitCNOT_conjTranspose`,
  `AxQM.Concrete.twoQubitCNOT_mul_self`,
  `AxQM.Concrete.twoQubitCNOT_mem_unitaryGroup` — the gate `U` is Hermitian (`U† = U`),
  an involution (`U² = I`), and unitary, so the conjugation `U Y₁ U†` is a genuine gate conjugation.

The concrete CNOT matrix `AxQM.Concrete.twoQubitCNOT` and the single-qubit Pauli matrices
`pauliX`, `pauliY`, `pauliI` are the definitions used in these statements.
-/
