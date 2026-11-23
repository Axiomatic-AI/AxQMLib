/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ThreeQubitBitFlipQEC

/-!
# Nielsen & Chuang, Exercise 10.7 (QEC conditions for the three-qubit bit-flip code)

Verify QEC conditions for three qubit bit flip code with given non-trace-preserving noise operation
elements.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 10.7 (p. 438).

The verification: with the code projector `P` and the four operation elements `Eᵢ`, the
quantum error-correction conditions (N&C Theorem 10.1, whose statement is in
`AxQM/Postulates/API/QuantumErrorCorrection.lean`) `P Eᵢ† Eⱼ P = αᵢⱼ P` hold with the
**diagonal Hermitian** matrix `α = diag((1−p)³, p(1−p)², p(1−p)², p(1−p)²)`. Off the diagonal the
identities vanish because a single bit flip carries the code space `span{|000⟩,|111⟩}` into
single-error strings, and a product of two *distinct* bit flips into two-error strings — both
orthogonal to the code; on the diagonal, `Xₖ² = I` and `P² = P` return the projector, and the
scalar coefficients supply the `α` entries (`√a·√a = a` for `a ≥ 0`, hence `0 ≤ p ≤ 1`).

## The declarations

In `AxQM/Postulates/API/ThreeQubitBitFlipQEC.lean`:

* `AxQM.bitFlipX` — the three single-qubit bit-flip errors `X₁, X₂, X₃` on the register
  `bitFlipReg = qubit ⊗ (qubit ⊗ qubit)`, with `bitFlipX_op_qubitThreeBasis` (each flips its bit)
  and `bitFlipX_op_involution` (`Xₖ² = 1`).
* `AxQM.codeProj_comp_bitFlipX_comp_codeProj` (`P Xₖ P = 0`) and
  `AxQM.codeProj_comp_bitFlipX_comp_bitFlipX_comp_codeProj` (`P Xₖ Xₗ P = 0`, `k ≠ l`) —
  the geometric heart, via the workhorse `codeProj_comp_comp_codeProj_eq_zero`.
* `AxQM.threeBitFlipNoise` / `AxQM.threeBitFlipAlpha` — the four noise operation
  elements `Eᵢ` and the diagonal Hermitian matrix `α`.
* `AxQM.threeBitFlipNoise_satisfiesKLConditions` — the explicit Knill–Laflamme identities
  `P Eᵢ† Eⱼ P = αᵢⱼ P` (N&C Eq. 10.16), the direct "verification".
* `AxQM.threeBitFlipNoise_satisfiesQECConditions` — **Exercise 10.7**: the three-qubit
  bit-flip code satisfies the quantum error-correction conditions for this noise process
  (`SatisfiesQECConditions (bitFlipSyndromeProj 0) (threeBitFlipNoise p)` for `0 ≤ p ≤ 1`).
-/
