/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingStandardForm

/-!
# N&C Problem 10.3 — Encoding stabilizer codes

*(N&C Problem 10.3, p. 495.)*

Find a circuit taking the standard-form check matrix listing to the encoded form (encode stabilizer
codes).

The trivial check matrix `G` (10.124) is `[0 | I]` — the single-qubit generators `Z₁, …, Zₙ` listing
the stabilizer of `|0⟩⊗ⁿ`. The standard form (10.125) is
```
   ┌  I     A₁     A₂  |  B      0     C₂ ┐   ← r      pivot generator rows
   │  0     0      0   |  D      I     E  │   ← n-k-r  middle generator rows
   └  0     0      0   |  A₂ᵀ    0     I  ┘   ← k      encoded-Z rows
```
with `D = A₁ᵀ + E A₂ᵀ`. The wanted circuit is the **Gottesman standard-form encoder**: Hadamards on
the pivot wires, a CNOT network building the `X`-blocks and their coupled transposes, and a
phase / controlled-`Z` network depositing the top `Z`-blocks `B`, `C₂`.

## Formalisation

The encoding circuit and its check-matrix action are combinatorics of the binary symplectic
(check-matrix) representation of the Pauli group and of Clifford circuits. The circuit is a genuine
unitary (`CliffordCircuit.toMatrix`), and its conjugation action on the actual Pauli operators is
recorded by `encodingCircuit_conj_pauliString`, so the physical content — a unitary encoding taking
the `|0⟩⊗ⁿ` stabilizer to the code's standard-form stabilizer — is captured, and the achievability
theorem (below) shows *every* standard-form code is reachable.

The declarations are in `AxQM/Concrete/PauliStringEncodingStandardForm.lean` and its dependencies:

* `AxQM.Concrete.encodingCircuit` — the encoder
  `phaseCZNetwork ws pairs ++ encodingCnotHad D`, parameterized by a standard-form partition
  `D : StdFormData n` (its `tgt` fan targets carrying `A₁, A₂, E`) and phase/`CZ` data `ws`, `pairs`
  (carrying `B`, `C₂`).
* `AxQM.Concrete.checkRow_encodingCircuit_pivot` / `checkRow_encodingCircuit_middle` /
  `checkRow_encodingCircuit_data` — the row-by-row proof that the circuit carries `G` (10.124) to
  the
  standard form (10.125): the top rows `[I A₁ A₂ | B 0 C₂]`, the middle rows `[0 | D I E]` with
  `D = A₁ᵀ + E A₂ᵀ`, and the encoded-`Z` rows `[0 | A₂ᵀ 0 I]`.
* `AxQM.Concrete.phaseCZZ` / `AxQM.Concrete.phaseCZZ_middle_eq_zero` — the
  deposited
  top-row `Z`-block `B`, `C₂` and its vanishing on the middle columns (the `0` of `[B 0 C₂]`).
* `AxQM.Concrete.encodingCircuit_conj_pauliString` — the operator (unitary) reading: the
  encoder conjugates each trivial generator `P_{Zᵢ}` to `± P_{row i}` of the standard form.
* `AxQM.Concrete.phaseCZZ_of_symm` /
  `AxQM.Concrete.encodingCircuit_standardForm_achievable` — the **achievability** (the
  problem's pinnacle claim): the phase/`CZ` deposit realizes every symmetric `𝔽₂`-bilinear form, so
  for **any** standard-form code (`A₁, A₂, E` via `D`; `B, C₂` satisfying the top-row commutation
  relation `B + Bᵀ = A₂C₂ᵀ + C₂A₂ᵀ`) there *exists* a circuit in the family carrying `G` (10.124) to
  **exactly** its (10.125). This discharges the "find a circuit for the given code" reading —
  not just
  the action of one member of the family.

Supporting the assembly: the CNOT + Hadamard core (`Concrete.encodingCnotHad`,
`checkRow_encodingCnotHad_pivot` / `_middle` / `_data`), the layer/network machinery
(`hadLayer`, `cnotNetwork`, `phaseCZNetwork`), and the Clifford-circuit check-matrix backbone
(`CliffordCircuit.conj_pauliString`).
-/
