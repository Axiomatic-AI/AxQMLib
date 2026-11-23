/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthConjugation
import AxQM.Concrete.ToffoliConjugation

/-!
# Nielsen & Chuang, Exercise 10.41 (π/8 and Toffoli conjugation of the Pauli matrices)

Verify Eqs (10.92)-(10.95): pi/8 and Toffoli gate conjugation of Pauli matrices.

Nielsen & Chuang §10.5.3 observes that "most quantum gates are outside the normalizer" `N(Gₙ)`, and
computes the action *by conjugation* of two such gates — the **π/8 gate** `T = diag(1, e^{iπ/4})`
and the **Toffoli gate** `U` (controls on qubits 1, 2; target 3) — on the Pauli operators:

* (10.92) `T Z T† = Z`,  `T X T† = (X + Y)/√2`;
* (10.93) `U Z₁ U† = Z₁`,  `U X₁ U† = X₁ (I + Z₂ + X₃ − Z₂X₃)/2`;
* (10.94) `U Z₂ U† = Z₂`,  `U X₂ U† = X₂ (I + Z₁ + X₃ − Z₁X₃)/2`;
* (10.95) `U X₃ U† = X₃`,  `U Z₃ U† = Z₃ (I + Z₁ + Z₂ − Z₁Z₂)/2`.

Unlike Hadamard/phase/CNOT, these gates send some Pauli operators to *non-Pauli* combinations, which
is precisely why the stabilizer formalism is inconvenient for circuits containing π/8 or Toffoli
gates.

Every identity is an equality of concrete `2 × 2` (π/8) or `8 × 8` (Toffoli) complex matrices.

## The formalisation

**Equation (10.92) — π/8 gate** (`AxQM/Concrete/PiEighthConjugation.lean`, built on the
π/8-gate matrix `tMatrix` of `Concrete/PiEighthGate.lean`, the Pauli matrices of
`Concrete/Pauli.lean` and the `1/√2` numeric bridges `Concrete.exp_pi_div_four_mul_I` / `invSqrt2`):

* `AxQM.Concrete.tMatrix_conj_pauliZ` — `T Z T† = Z` (first identity of eq. 10.92).
* `AxQM.Concrete.tMatrix_conj_pauliX` — `T X T† = (X + Y)/√2` (second identity of eq.
  10.92), the non-Pauli image witnessing `T ∉ N(Gₙ)`.
* Supporting: `AxQM.Concrete.tMatrix_apply_one_one` (`T₁₁ = e^{iπ/4} = (1 + i)/√2`) and
  `AxQM.Concrete.tMatrix_eq` (`T = !![1, 0; 0, (1 + i)/√2]`).

**Equations (10.93)–(10.95) — Toffoli gate** (`AxQM/Concrete/ToffoliConjugation.lean`,
built on the `Fin 8` Toffoli permutation matrix `toffoliMatrix` (`Concrete/Sqrt2IntegerMatrix.lean`)
and the three-qubit Pauli operators `pauliX1, …, pauliZ3` defined there as `flattenTriQubit` of
triple Kronecker products of the single-qubit Pauli matrices):

* `AxQM.Concrete.ToffoliConj.toffoli_conj_apply` — the structural lemma
  `U A U† i j = A (swap 6 7 i) (swap 6 7 j)`: conjugation by the Toffoli permutation relabels
  entries by the transposition `|110⟩ ↔ |111⟩`.
* `AxQM.Concrete.ToffoliConj.toffoli_conj_pauliZ1` / `toffoli_conj_pauliZ2` /
  `toffoli_conj_pauliX3` — the three fixed generators `U Z₁ U† = Z₁`, `U Z₂ U† = Z₂`,
  `U X₃ U† = X₃` (first identities of eqs. 10.93/10.94/10.95).
* `AxQM.Concrete.ToffoliConj.toffoli_conj_pauliX1` / `toffoli_conj_pauliX2` /
  `toffoli_conj_pauliZ3` — the three non-Pauli images `U X₁ U† = X₁ (I + Z₂ + X₃ − Z₂X₃)/2`,
  `U X₂ U† = X₂ (I + Z₁ + X₃ − Z₁X₃)/2`, `U Z₃ U† = Z₃ (I + Z₁ + Z₂ − Z₁Z₂)/2` (second identities of
  eqs. 10.93/10.94/10.95), witnessing that the Toffoli gate lies outside `N(Gₙ)`.
* Supporting: `AxQM.Concrete.ToffoliConj.pauliX1_eq`, …, `pauliZ3_eq` — the six
  three-qubit Paulis as explicit `8 × 8` matrices.
-/
