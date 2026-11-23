/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ProcessTomographyTwoQubit

/-!
# Nielsen & Chuang, Exercise 8.34

Show two-qubit process χ2=Λ2 ρ̄' Λ2 with the stated block/permutation-matrix construction.

This is the two-qubit lift of Box 8.5's process-reconstruction identity — a pure statement about
`16 × 16` complex matrices (the Kronecker square `Λ₂ = Λ ⊗ Λ`, the operator-sum superoperator `E₂`
and its measured grid, and the perfect-shuffle permutation `P`). Like the single-qubit Box 8.5
identity it builds on, the reconstruction holds for **every** `χ₂` — the physical content
(Hermiticity, trace preservation) lives only in the interpretation.

The formalisation is in `AxQM/Concrete/ProcessTomographyTwoQubit.lean` (building on the
single-qubit Box 8.5 development in `AxQM/Concrete/ProcessTomography.lean`):

* `AxQM.Concrete.chiLambda2` — `Λ₂ = Λ ⊗ Λ`, the Kronecker square of Box 8.5's `Λ`.
* `AxQM.Concrete.tomoBasis2` — the `16`-element two-qubit operator basis
  `Ẽ_M = Ẽ_{m₁} ⊗ Ẽ_{m₂}` (pairwise Kronecker products of the single-qubit basis `{I, X, -iY, Z}`).
* `AxQM.Concrete.chiProcess2` — the two-qubit process `E₂(ρ) = Σ_{MN} χ₂_{MN} Ẽ_M ρ Ẽ_N†`.
* `AxQM.Concrete.chiGrid2` — the measured block matrix, block `(A, B)` = `E₂(|A⟩⟨B|)`,
  i.e. N&C's `[ρ'_{nm}]` from eq. (8.181).
* `AxQM.Concrete.shuffleMatrix` — the permutation matrix `P = I ⊗ SWAP ⊗ I` (the
  perfect shuffle swapping the two middle atomic index slots), with `shuffleMatrix_transpose`
  (`Pᵀ = P`) and `shuffleMatrix_transpose_mul` (`Pᵀ P = 1`) recording that it is a symmetric
  orthogonal permutation matrix.
* `AxQM.Concrete.tomoT` / `AxQM.Concrete.rhoBlock` /
  `AxQM.Concrete.rhoBlock_eq` — the state-preparation operators
  `T_n = (I,X)_{n₁} ⊗ (I,X)_{n₂}` and the measured inputs `ρ_{nm} = T_n |00⟩⟨00| T_m`, with the
  identification `ρ_{nm} = |n⟩⟨m|` (eq. 8.181).
* `AxQM.Concrete.chiLambda2_chiGrid2_chiLambda2` — the exercise's claim, eqs.
  (8.180)–(8.181): `χ₂ = Λ₂ (Pᵀ · chiGrid2 χ₂ · P) Λ₂` for every `χ₂`.
-/
