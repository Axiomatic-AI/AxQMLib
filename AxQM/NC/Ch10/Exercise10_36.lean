/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoQubitCnotConjugation

/-!
# Nielsen & Chuang, Exercise 10.36 (Explicit CNOT conjugation of the Pauli generators)

Explicitly verify CNOT conjugation: UX1U-dag=X1X2, UX2U-dag=X2, UZ1U-dag=Z1, UZ2U-dag=Z1Z2.

Here (Nielsen & Chuang, p. 460) `U = CNOT` is the two-qubit controlled-NOT gate with qubit `1` as
control and qubit `2` as target, and `X₁ = X ⊗ I`, `X₂ = I ⊗ X`, `Z₁ = Z ⊗ I`, `Z₂ = I ⊗ Z` are the
single-Pauli generators of the two-qubit Pauli group. The four relations (summarized in Figure 10.7)
say that an `X` on the control propagates to the target, an `X` on the target and a `Z` on the
control are unchanged, and a `Z` on the target propagates to the control.

Each relation is an identity between concrete `4 × 4` complex matrices (Kronecker products of the
Pauli matrices, conjugated by the CNOT permutation matrix); compare its two-qubit sibling
`totalSpin_lie` of Ex. 7.25.

The formalisation is in `AxQM/Concrete/TwoQubitCnotConjugation.lean`:

* `AxQM.Concrete.pauliX1` / `pauliX2` / `pauliZ1` / `pauliZ2` — the two-qubit generators
  `X ⊗ I`, `I ⊗ X`, `Z ⊗ I`, `I ⊗ Z` as `4 × 4` matrices (with their explicit forms
  `pauliX1_eq`, …).
* `AxQM.Concrete.cnotMatrix_conjTranspose` — the CNOT gate is Hermitian, so the adjoint
  `U†` in the relations is `cnotMatrix` again.
* `AxQM.Concrete.cnotMatrix_conj_pauliX1` — **Exercise 10.36**, first relation:
  `U X₁ U† = X₁X₂` (`cnotMatrix * pauliX1 * cnotMatrixᴴ = pauliX1 * pauliX2`).
* `AxQM.Concrete.cnotMatrix_conj_pauliX2` — second relation: `U X₂ U† = X₂`.
* `AxQM.Concrete.cnotMatrix_conj_pauliZ1` — third relation: `U Z₁ U† = Z₁`.
* `AxQM.Concrete.cnotMatrix_conj_pauliZ2` — fourth relation: `U Z₂ U† = Z₁Z₂`
  (`cnotMatrix * pauliZ2 * cnotMatrixᴴ = pauliZ1 * pauliZ2`).
-/
