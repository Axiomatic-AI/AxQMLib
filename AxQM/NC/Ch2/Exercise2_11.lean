/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliEigenvectors

/-!
# Nielsen & Chuang, Exercise 2.11 (Eigendecomposition of the Pauli matrices)

Find eigenvectors, eigenvalues, diagonal representations of X, Y, Z.

Each Pauli matrix is Hermitian with eigenvalues `±1`; its two normalized
eigenvectors are an orthonormal basis of `ℂ²`, and N&C's *diagonal representation*
(eq. (2.29)) writes the operator as `A = (+1)|ψ₊⟩⟨ψ₊| + (-1)|ψ₋⟩⟨ψ₋|` over that
eigenbasis:

* `Z`: `|0⟩, |1⟩` (eigenvalues `+1, -1`); `Z = |0⟩⟨0| - |1⟩⟨1|`.
* `X`: `|±⟩ = (|0⟩ ± |1⟩)/√2` (eigenvalues `+1, -1`); `X = |+⟩⟨+| - |-⟩⟨-|`.
* `Y`: `|±i⟩ = (|0⟩ ± i|1⟩)/√2` (eigenvalues `+1, -1`); `Y = |+i⟩⟨+i| - |-i⟩⟨-i|`.

The formalisation is in `AxQM/Concrete/PauliEigenvectors.lean` (the Pauli
matrices `pauliX/pauliY/pauliZ` and the kets/outer products `ket`, `ketBra`,
`pauliZ_eq_ketBra` are reused from `AxQM/Concrete/Pauli.lean` and
`AxQM/Concrete/PauliOuterProduct.lean`):

* **Eigenvectors.** `AxQM.Concrete.xPlus`, `xMinus` (`X`), `yPlus`,
  `yMinus` (`Y`) — the normalized `|±⟩`, `|±i⟩`; `Z`'s eigenvectors are the reused
  computational-basis kets `ket 0 = |0⟩`, `ket 1 = |1⟩`. Their genuineness is
  recorded by the `_ne_zero` lemmas (`xPlus_ne_zero`, …).
* **Eigenvalues.** `pauliX_mulVec_xPlus`/`pauliX_mulVec_xMinus`,
  `pauliY_mulVec_yPlus`/`pauliY_mulVec_yMinus`,
  `pauliZ_mulVec_ket_zero`/`pauliZ_mulVec_ket_one` — the eigenvalue equations
  `M *ᵥ v = μ • v` with `μ ∈ {+1, -1}` explicit.
* **Diagonal representations.** `pauliX_eq_outerSelf_sub`, `pauliY_eq_outerSelf_sub`,
  `pauliZ_eq_outerSelf_sub` — `M = |ψ₊⟩⟨ψ₊| - |ψ₋⟩⟨ψ₋|`, using the self outer
  product `AxQM.Concrete.outerSelf v = |v⟩⟨v|` (`Z`'s reduces to the
  reused `pauliZ_eq_ketBra`).
* **Orthonormality** (certifying "an orthonormal set of eigenvectors"):
  `xPlus_dotProduct_self`, `xPlus_dotProduct_xMinus`, `yPlus_dotProduct_self`,
  `yPlus_dotProduct_yMinus`, … (Hermitian inner product `star u ⬝ᵥ v`), backed by
  the normalization constant `AxQM.Concrete.invSqrt2 = 1/√2`.
-/
