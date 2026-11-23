/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliTrotter
import AxQM.Concrete.PauliTomography
import ToMathlib.Analysis.CStarAlgebra.MatrixToEuclideanCLM

/-!
# AxQM.Postulates.API — the Pauli density matrix of a state and the tomographic bridge

The bridge turning a `State ρ` on the `n`-qubit register `qudit (2ⁿ)` into the
`Matrix (Fin n → Fin 2)`-indexed density matrix on which the Concrete Pauli-trace reconstruction
backbone (`AxQM/Concrete/PauliTomography.lean`) acts, and connecting the postulate expectation value
`State.expectation ρ (pauliStringHamiltonian g 1) = ⟨P_g⟩_ρ` to the trace pairing `tr(P_g ρ)` of
Nielsen & Chuang eq. (7.168). This is the physics half of *state tomography* (§7.7.4, Ex 7.45):
it lets "the state is reconstructed from its Pauli expectation values" be stated for
states, observables and expectation values while being proved by the matrix mathematics.

## What this file provides

* `State.pauliMatrix` — the density matrix `toEuclideanCLM⁻¹ ρ.op` of a state, in the computational
  basis, reindexed from `Fin (2ⁿ)` to bit strings `Fin n → Fin 2` along `finFunctionFinEquiv`.
* `State.pauliMatrix_isHermitian` — it is Hermitian (the density operator is self-adjoint).
* `State.trace_pauliMatrix` — its trace is `1` (a density operator has unit trace).
* `State.expectation_pauliStringHamiltonian` — **the (7.168) bridge**: the postulate expectation
  `ρ.expectation (pauliStringHamiltonian g 1)` equals the real part of the Pauli trace pairing
  `tr(P_g · ρ.pauliMatrix)` — `⟨P_g⟩_ρ = tr(ρ P_g)`.
* `State.eq_of_pauliMatrix_eq` — a state is determined by its Pauli density matrix (`toEuclideanCLM`
  and the reindexing are injective), the bridge from a matrix identity back to a state identity.

## Design

* **Reconstruction.** The reconstruction principle built on this bridge,
  `(∀ g ≠ 0, ⟨P_g⟩_ρ = ⟨P_g⟩_σ) → ρ = σ`, is in `AxQM/Core/PauliTomographyExpectation.lean`.
* **Bridge mechanism.** `Matrix.toEuclideanCLM : Matrix (Fin (2ⁿ)) (Fin (2ⁿ)) ℂ ≃⋆ₐ[ℂ] …` is the
  `⋆`-algebra isomorphism identifying matrices with operators in the computational basis (the same
  one `pauliStringHamiltonian` is built from). Under it, operator composition is matrix product
  (`map_mul`), the operator trace is the matrix trace (`Matrix.trace_toEuclideanCLM`), and the
  adjoint is conjugate transpose (`map_star`), so `State.expectation = Re Tr(ρ A)` is
  matrix pairing `Re tr(P_g ρ)`. The register indexing `Fin (2ⁿ)` is reindexed to bit strings
  `Fin n → Fin 2` (the index type of `Concrete.pauliString`) via `finFunctionFinEquiv`, matching the
  reindexing already used by `pauliStringStd` / `Observable.stdMatrix`.
-/

open Matrix

open scoped BigOperators

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- Reindexing a `Fin (2ⁿ)`-indexed matrix to bit strings `Fin n → Fin 2` along the bijection
`finFunctionFinEquiv` preserves the trace (a bijective relabelling of the diagonal sum). -/
private theorem trace_submatrix_finFunctionFinEquiv
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    (A.submatrix finFunctionFinEquiv finFunctionFinEquiv).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finFunctionFinEquiv fun i => A i i

/-- The **Pauli density matrix** of a state `ρ` on the `n`-qubit register `qudit (2ⁿ)`: the matrix
`toEuclideanCLM⁻¹ ρ.op` of the density operator in the computational basis, reindexed from
`Fin (2ⁿ)` to bit strings `Fin n → Fin 2` along `finFunctionFinEquiv`. This is the concrete matrix
on which the Pauli-trace reconstruction backbone (`Concrete.eq_of_trace_eq_of_trace_pauliString_eq`)
acts; `State.expectation_pauliStringHamiltonian` shows its Pauli trace pairings are the
expectations `⟨P_g⟩_ρ`. -/
def State.pauliMatrix (ρ : State (qudit (2 ^ n))) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm ρ.op).submatrix finFunctionFinEquiv finFunctionFinEquiv

/-- The Pauli density matrix of a state is **Hermitian**, because the density operator `ρ.op` is
self-adjoint (positive), the `⋆`-algebra isomorphism `toEuclideanCLM⁻¹` sends self-adjoint operators
to Hermitian matrices, and reindexing by `finFunctionFinEquiv` preserves Hermitianness. -/
theorem State.pauliMatrix_isHermitian (ρ : State (qudit (2 ^ n))) :
    ρ.pauliMatrix.IsHermitian :=
  (Matrix.isHermitian_iff_isSelfAdjoint.mpr
    (ρ.isPositive_op.isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm)).submatrix
    finFunctionFinEquiv

/-- The Pauli density matrix of a state has **unit trace** (`tr ρ = 1`): the reindexing preserves
the trace, and the matrix trace of `toEuclideanCLM⁻¹ ρ.op` is the operator trace of `ρ.op`, which is
`1`
for a density operator (`State.trace_op_eq_one`). -/
theorem State.trace_pauliMatrix (ρ : State (qudit (2 ^ n))) : ρ.pauliMatrix.trace = 1 := by
  -- `qudit (2 ^ n) := QSystem.ofModel (EuclideanSpace ℂ (Fin (2 ^ n)))`, so `ρ.op`'s bundled
  -- `(qudit _).space` instances and `toEuclideanCLM.symm`'s bare `EuclideanSpace` ones diverge
  -- under `rw`'s syntactic matching even though defeq; `erw` bridges it.
  erw [State.pauliMatrix, trace_submatrix_finFunctionFinEquiv,
    ← Matrix.trace_toEuclideanCLM, StarAlgEquiv.apply_symm_apply]
  exact ρ.trace_op_eq_one

/-- **The (7.168) tomography bridge.** The postulate expectation value of the Pauli-string
observable `P_g = pauliStringHamiltonian g 1` in a state `ρ` is the real part of the Pauli trace
pairing: `⟨P_g⟩_ρ = Re tr(P_g · ρ)`, over the Pauli density matrix `ρ.pauliMatrix`. This is Nielsen
& Chuang's `rₖ = ⟨σₖ⟩ = tr(ρ σₖ)` (eq. 7.168), lifted to the `n`-qubit Pauli strings and grounded in
`State.expectation`. Proof: unfold `expectation` to `Re Tr(ρ.op ∘ P_g.op)`, replace `P_g.op` by
`toEuclideanCLM (pauliStringStd g)` and `ρ.op` by `toEuclideanCLM (toEuclideanCLM⁻¹ ρ.op)`; the
isomorphism turns the composite into `toEuclideanCLM (M_ρ * pauliStringStd g)` whose operator trace
is the matrix trace, which reindexes (cyclically) to `tr(pauliString g · ρ.pauliMatrix)`. -/
theorem State.expectation_pauliStringHamiltonian (ρ : State (qudit (2 ^ n)))
    (g : Fin n → Fin 4) :
    ρ.expectation (pauliStringHamiltonian g 1)
      = ((Concrete.pauliString g * ρ.pauliMatrix).trace).re := by
  set M := (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm ρ.op with hM
  have hρop : ρ.op = Matrix.toEuclideanCLM (𝕜 := ℂ) M :=
    (StarAlgEquiv.apply_symm_apply _ _).symm
  -- `Tr(ρ.op ∘ P_g.op)` as the matrix trace `tr(M * pauliStringStd g)`.
  have hcomp : (LinearMap.trace ℂ (qudit (2 ^ n)).space)
        ↑(ρ.op.comp (pauliStringHamiltonian g 1).op)
      = (M * Concrete.pauliStringStd g).trace := by
    have hopcomp : ρ.op.comp (pauliStringHamiltonian g 1).op
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (M * Concrete.pauliStringStd g) := by
      rw [pauliStringHamiltonian_op, Complex.ofReal_one, one_smul, hρop, map_mul]
      rfl
    rw [hopcomp]
    exact Matrix.trace_toEuclideanCLM _
  -- `(pauliStringStd g).submatrix e e = pauliString g` (the reindexings cancel).
  have hpss : (Concrete.pauliStringStd g).submatrix finFunctionFinEquiv finFunctionFinEquiv
      = Concrete.pauliString g := by
    rw [Concrete.pauliStringStd, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id]
  -- The matrix trace reindexes to the bit-string pairing `tr(pauliString g * ρ.pauliMatrix)`.
  have hreindex : (M * Concrete.pauliStringStd g).trace
      = (Concrete.pauliString g * ρ.pauliMatrix).trace := by
    rw [Matrix.trace_mul_comm,
      ← trace_submatrix_finFunctionFinEquiv (Concrete.pauliStringStd g * M),
      ← Matrix.submatrix_mul_equiv (Concrete.pauliStringStd g) M finFunctionFinEquiv
        finFunctionFinEquiv finFunctionFinEquiv, hpss, State.pauliMatrix, ← hM]
  have hexp : ρ.expectation (pauliStringHamiltonian g 1)
      = ((LinearMap.trace ℂ (qudit (2 ^ n)).space)
          ↑(ρ.op.comp (pauliStringHamiltonian g 1).op)).re := rfl
  rw [hexp, hcomp, hreindex]

/-- A state on the `n`-qubit register is **determined by its Pauli density matrix**: if
`ρ.pauliMatrix = σ.pauliMatrix` then `ρ = σ`. Both `toEuclideanCLM` and the reindexing by the
bijection `finFunctionFinEquiv` are injective, so the density operators — hence the states
(`State.ext`) — coincide. This bridges a matrix reconstruction back to a state identity. -/
theorem State.eq_of_pauliMatrix_eq {ρ σ : State (qudit (2 ^ n))}
    (h : ρ.pauliMatrix = σ.pauliMatrix) : ρ = σ := by
  apply State.ext
  have hM : (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm ρ.op
      = (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm σ.op := by
    have hsub := congrArg
      (fun X : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ =>
        X.submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm) h
    simpa only [State.pauliMatrix, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
      Matrix.submatrix_id_id] using hsub
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm.injective hM

end AxQM
