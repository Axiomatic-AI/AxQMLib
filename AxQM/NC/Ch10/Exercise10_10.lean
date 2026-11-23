/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorCodeQEC

/-!
# Nielsen & Chuang, Exercise 10.10 — the Shor code satisfies the QEC conditions

Explicitly verify QEC conditions for Shor code with error set I and Xj,Yj,Zj for j=1..9.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 10.10 (p. 441).

The nine-qubit **Shor code** encodes one logical qubit as the two codewords

  `|0_L⟩ = (|000⟩+|111⟩)(|000⟩+|111⟩)(|000⟩+|111⟩) / 2√2`,
  `|1_L⟩ = (|000⟩−|111⟩)(|000⟩−|111⟩)(|000⟩−|111⟩) / 2√2`,

three copies of a three-qubit "cat" block. The exercise asks to check the **quantum error-correction
conditions** (Theorem 10.1, eq. (10.16)) `P Eᵢ† Eⱼ P = αᵢⱼ P` for a Hermitian `α`, against the error
set `{I} ∪ {X_j, Y_j, Z_j : j = 1..9}` — the identity together with all `27` single-qubit Paulis.

## The computation and why the code is *degenerate*

By the shared codeword-basis route, the conditions reduce to the overlaps of the error vectors
`v_{i,s} = Eᵢ |s_L⟩`: one needs `⟪v_{i,a}, v_{j,b}⟫ = αᵢⱼ · δ_{a,b}`. Everything factors over the
three cat blocks (`shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`), and a single-qubit Pauli
touches exactly one block:

* **off-diagonal (`a ≠ b`) vanishes** — two errors touch at most two of the three blocks, so at
  least one block is untouched by both and contributes the vanishing overlap `⟪c_0, c_1⟩ = 0` of the
  two distinct cat blocks; the images of the two codewords stay orthogonal (`fact (B)`);
* **diagonal (`a = b`) is codeword-independent** — each per-block factor is the same for `|0_L⟩` and
  `|1_L⟩`, so `⟪v_{i,1}, v_{j,1}⟫ = ⟪v_{i,0}, v_{j,0}⟫` (`fact (A)`).

Hence the conditions hold with the Hermitian **Gram matrix** `αᵢⱼ = ⟪v_{i,0}, v_{j,0}⟫`. This `α` is
genuinely **non-diagonal**: distinct Paulis in the same cat block (e.g. `X_j` and `Y_j`) send a
codeword to overlapping states, so the Shor code is a **degenerate** code. The faithful reading of
N&C is therefore the general "for *some* Hermitian `α`" condition — not the sharper
orthonormal-image condition (`α = 1`) of the bit-flip / phase-flip codes — and that is exactly what
is proved.

## The declarations

The statement is about the code projector `P` and the error operators `Eᵢ`
(`shorReg.space →L[ℂ] shorReg.space`), through the predicate `AxQM.SatisfiesQECConditions` (N&C
Theorem 10.1), as for the phase-flip-code Exercise 10.8. The Shor code, its single-qubit Pauli
errors, and the verification of Exercise 10.10 are in the `AxQM/Postulates/API/ShorCode*.lean`
files (all in namespace `AxQM`):

* `shorCodeword` / `shorCodeProj` — the logical codewords `|0_L⟩`, `|1_L⟩` and the code projector
  `P = |0_L⟩⟨0_L| + |1_L⟩⟨1_L|` (`ShorCodeProjector.lean`); `shorCodeword_inner` /
  `shorCodeword_orthonormal` record their orthonormality.
* `shorSinglePauli` / `shorPauliError` — the single-qubit Pauli error operators `X_j, Y_j, Z_j` on
  the nine-qubit register, with their self-adjointness and cat-block action (`ShorPauliError.lean`).
* `ShorErrorIndex` / `shorErrorFamily` / `shorErrorVec` — the `28`-element error index
  (`none = I`, `some (t, block, pos)` a Pauli), the error operators `Eᵢ`, and the error vectors
  `v_{i,s} = Eᵢ |s_L⟩` (`ShorErrorInnerProduct.lean`).
* `shorErrorVec_inner_offdiag_eq_zero` — **fact (B)**, off-diagonal-vanishing `⟪v_{i,0}, v_{j,1}⟫ =
  0` (`ShorErrorInnerProduct.lean`); `shorErrorVec_inner_diag_eq` — **fact (A)**, diagonal-equality
  `⟪v_{i,1}, v_{j,1}⟫ = ⟪v_{i,0}, v_{j,0}⟫` (`ShorErrorInnerProductDiag.lean`).
* `shorErrorAlpha` (the Hermitian Gram coefficient matrix, `shorErrorAlpha_isHermitian`) and
  `shorErrorVec_inner_eq` (the combined `⟪v_{i,a}, v_{j,b}⟫ = αᵢⱼ · δ_{a,b}`) — `ShorCodeQEC.lean`.
* `shorCode_satisfiesQECConditions` — **Exercise 10.10**: `SatisfiesQECConditions shorCodeProj
  shorErrorFamily`, the Shor code satisfies the quantum error-correction conditions with the
  Hermitian Gram matrix `α` (`ShorCodeQEC.lean`).

The Knill–Laflamme core — the codeword-basis verification packaged once — is Hilbert-space
mathematics in `ToMathlib/Analysis/InnerProductSpace/QuantumErrorCorrection.lean`:

* `ContinuousLinearMap.satisfiesKLConditions_of_inner_error_images` — if `⟪Eᵢ v_a, Eⱼ v_b⟫ =
  αᵢⱼ δ_{a,b}` for codewords `v` and errors `E`, then `∑ₐ |v_a⟩⟨v_a|` satisfies the Knill–Laflamme
  conditions with matrix `α` (the shared route for N&C Exercises 10.7–10.10).
-/
