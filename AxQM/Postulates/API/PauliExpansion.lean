/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qudit
import AxQM.Postulates.Observable
import AxQM.Concrete.PauliString
import ToMathlib.Analysis.InnerProductSpace.Adjoint
import ToMathlib.Algebra.BigOperators.Fin

/-!
# AxQM.Postulates.API — the real Pauli expansion of a Hamiltonian (N&C Problem 4.3(2))

Part (2) of Nielsen & Chuang, Problem 4.3: *the Hamiltonian
`H = i ln(U)` can be written `H = Σ_g h_g g` with real `h_g`, the sum over all `n`-fold tensor
products `g` of the Pauli matrices `{I, X, Y, Z}`.* In this library a Hamiltonian is an
`Observable` — a self-adjoint operator (Postulate 2) — and the `n`-qubit register is the
`2ⁿ`-level system `qudit (2ⁿ)`. The statement here says
that the matrix of *any* Hamiltonian on the `n`-qubit register, written in the computational
basis and reindexed to bit strings, is a **real**-coefficient combination of Pauli strings.

The purely mathematical content — the `n`-fold Pauli strings form a basis of `M₂ₙ(ℂ)` and every
Hermitian matrix has a real Pauli expansion — is proved in `AxQM/Concrete/PauliString.lean`
(`AxQM.Concrete.exists_real_pauliString_expansion`). This file turns an `Observable` (a bundled
self-adjoint operator) into a Hermitian matrix and applies that mathematics, so part (2) is stated
for observables.

## What this file provides

* `Observable.stdMatrix` — the matrix of an observable (Hamiltonian) on `qudit d` in the
  **computational basis** `|0⟩, …, |d-1⟩` (the orthonormal `EuclideanSpace.basisFun`): the
  operator→matrix bridge for an `Observable`. (It represents a self-adjoint operator; the
  Trotter parts (4)/(5) instead need the matrices of the *unitary* evolutions `exp(-iHΔ)`, a
  distinct `Evolution`→matrix bridge, so `stdMatrix` does not serve them directly.)
* `Observable.stdMatrix_apply` — the characterizing entry formula `⟨i|H|j⟩ = ⟪|i⟩, H|j⟩⟫`.
* `Observable.stdMatrix_isHermitian` — that matrix is Hermitian, because the operator is
  self-adjoint (the entries `⟨i|H|j⟩` satisfy `conj ⟨j|H|i⟩ = ⟨i|H|j⟩`).
* `Observable.exists_real_pauliString_expansion` — **Problem 4.3(2)**: for a Hamiltonian
  `H : Observable (qudit (2ⁿ))`, its computational-basis matrix reindexed to bit strings
  (`Fin n → Fin 2`) is `Σ_g (h_g : ℂ) • pauliString g` for real `h_g`.

## Design notes

* **Register model.** N&C's "`n` qubits" is the `2ⁿ`-dimensional register `qudit (2ⁿ)`
  (`EuclideanSpace ℂ (Fin (2ⁿ))`). The Pauli-string mathematics is indexed by bit strings
  `Fin n → Fin 2`, so we reindex the `Fin (2ⁿ)`-indexed matrix along `finFunctionFinEquiv :
  (Fin n → Fin 2) ≃ Fin (2ⁿ)` (via `Matrix.submatrix`), which preserves Hermitianness
  (`Matrix.IsHermitian.submatrix`).
* **Any Hamiltonian, not just `i ln U`.** N&C introduce `H` as `i ln U`, but the expansion uses
  *only* that `H` is Hermitian; the `= i ln U` plays no role in part (2). Stating it for every
  `Observable` is the faithful, reusable form, and specialises to `H = i ln U` by combining with
  the generator existence `Evolution.exists_hamiltonian_generator` (part (1),
  `AxQM/NC/Ch4/Problem4_3.lean`).
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- The **computational-basis matrix** of an observable (Hamiltonian) on the `d`-level register
`qudit d`: the matrix of `H.op` with respect to the orthonormal computational basis
`EuclideanSpace.basisFun`, whose `(i, j)` entry is `⟨i|H|j⟩ = ⟪|i⟩, H|j⟩⟫`. The operator→matrix
bridge for an `Observable` on `qudit d`; its characterizing entry formula is `stdMatrix_apply`. -/
def Observable.stdMatrix (H : Observable (qudit d)) : Matrix (Fin d) (Fin d) ℂ :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin d) ℂ) H.op.toLinearMap

/-- **Entry formula for the computational-basis matrix**: the `(i, j)` entry of `H.stdMatrix` is the
matrix element `⟨i|H|j⟩ = ⟪|i⟩, H|j⟩⟫` of `H.op` between the computational-basis states
`|i⟩ = quditBasis i`. This is `LinearMap.toMatrixOrthonormal_apply_apply` composed with the
identification `EuclideanSpace.basisFun i = EuclideanSpace.single i 1 = (quditBasis i).vec`, so
the bridge can be used without re-deriving its entries. -/
@[simp]
theorem Observable.stdMatrix_apply (H : Observable (qudit d)) (i j : Fin d) :
    H.stdMatrix i j = inner ℂ (quditBasis i).vec (H.op (quditBasis j).vec) := by
  rw [Observable.stdMatrix]
  erw [LinearMap.toMatrixOrthonormal_apply_apply]
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply]
  rfl

/-- The computational-basis matrix of an observable is **Hermitian**: since `H.op` is self-adjoint
(Postulate 2), its underlying map is symmetric
(`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`), and a symmetric operator's matrix in an
orthonormal basis is Hermitian (`LinearMap.isHermitian_toMatrix_iff`, applied to
`H.stdMatrix = toMatrixOrthonormal (basisFun) H.op.toLinearMap`). -/
theorem Observable.stdMatrix_isHermitian (H : Observable (qudit d)) : H.stdMatrix.IsHermitian :=
  (LinearMap.isHermitian_toMatrix_iff (EuclideanSpace.basisFun (Fin d) ℂ)).mpr
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp H.selfAdjoint)

/-- **Nielsen & Chuang, Problem 4.3(2): real Pauli expansion of a Hamiltonian.** For a Hamiltonian
`H : Observable (qudit (2ⁿ))` on the `n`-qubit register, its computational-basis matrix, reindexed
to bit strings `Fin n → Fin 2`, is a **real**-coefficient combination of the `n`-fold Pauli strings:
`H = Σ_g (h_g : ℂ) • pauliString g` with `h_g : ℝ`. This uses that the
Hamiltonian is self-adjoint, hence its matrix is Hermitian (`Observable.stdMatrix_isHermitian`), and
the matrix-level expansion `Concrete.exists_real_pauliString_expansion`. -/
theorem Observable.exists_real_pauliString_expansion {n : ℕ} (H : Observable (qudit (2 ^ n))) :
    ∃ h : (Fin n → Fin 4) → ℝ,
      H.stdMatrix.submatrix finFunctionFinEquiv finFunctionFinEquiv
        = ∑ g, (h g : ℂ) • Concrete.pauliString g :=
  Concrete.exists_real_pauliString_expansion
    (H.stdMatrix_isHermitian.submatrix finFunctionFinEquiv)

end AxQM
