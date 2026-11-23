/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PhaseFlipCode

/-!
# Nielsen & Chuang, Exercise 10.8 — the three-qubit phase-flip code satisfies the QEC conditions

Verify three qubit phase flip code satisfies QEC conditions for error set {I,Z1,Z2,Z3}.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 10.8 (p. 441).

The three-qubit **phase-flip code** encodes one logical qubit into three physical qubits as
`|0_L⟩ = |+++⟩`, `|1_L⟩ = |−−−⟩`. It is the Hadamard-conjugate of the bit-flip code: in the
`{|+⟩, |−⟩}` basis of each qubit it is *exactly* the bit-flip code in the computational basis, with
the Pauli `Z` (which sends `|+⟩ ↔ |−⟩`) playing the role of the bit-flip `X`. The exercise asks to
check the **quantum error-correction conditions** (Theorem 10.1, eq. (10.16))
`P Eᵢ† Eⱼ P = αᵢⱼ P` for a Hermitian matrix `α`, for the error set `{I, Z₁, Z₂, Z₃}` (the identity
and a single `Z` on each qubit).

The verification is a computation over the `±` basis: the eight error images `Zᵢ|+++⟩` and
`Zᵢ|−−−⟩` (`i = 0` meaning "no error") are mutually orthonormal `±`-basis vectors — each a single
flip of a codeword — so `⟪Eᵢ v_a, Eⱼ v_b⟫ = δᵢⱼ δ_{a,b}`, and the conditions hold with the
**identity** coefficient matrix `α = 1` (Hermitian, as required). This makes `{I, Z₁, Z₂, Z₃}` a
correctable set for the code (Theorem 10.1). Compare Theorem 10.1
(`AxQM/NC/Ch10/Theorem10_1.lean`), which states the conditions for the predicate
`AxQM.SatisfiesQECConditions`.

The formalisation is in `AxQM/Postulates/API/PhaseFlipCode.lean`:

* `AxQM.pmQubit` — the single-qubit `±` orthonormal frame (`pmQubit_orthonormal`), with
  `AxQM.pauliZGate_op_pmQubit` recording that `Z` flips the `±` label.
* `AxQM.pmThreeVec` — the three-qubit `±`-basis vector `|σ₁σ₂σ₃⟩`, orthonormal
  (`pmThreeVec_inner`).
* `AxQM.phaseFlipErrorGate` / `AxQM.phaseFlipErrorOp` — the error set
  `{I, Z₁, Z₂, Z₃}` as gates and as operators; `phaseFlipErrorOp_apply` computes each error's action
  on the `±` basis as a coordinate flip.
* `AxQM.phaseFlipCodeword` — the codewords `|+++⟩`, `|−−−⟩`; and
  `AxQM.phaseFlipCodeProj` — the code projector `P = |+++⟩⟨+++| + |−−−⟩⟨−−−|`.
* `AxQM.phaseFlipCode_satisfiesQECConditions` — **Exercise 10.8**:
  `SatisfiesQECConditions phaseFlipCodeProj phaseFlipErrorOp`, with the identity Hermitian
  coefficient matrix.

The Knill–Laflamme core — the codeword-basis verification — is Hilbert-space mathematics in
`ToMathlib/Analysis/InnerProductSpace/QuantumErrorCorrection.lean`:

* `ContinuousLinearMap.satisfiesKLConditions_of_inner_error_images` — if `⟪Eᵢ v_a, Eⱼ v_b⟫ =
  αᵢⱼ δ_{a,b}` for codewords `v` and errors `E`, then `∑ₐ |v_a⟩⟨v_a|` satisfies the Knill–Laflamme
  conditions with matrix `α` (the shared route for N&C Exercises 10.7–10.10).
-/
