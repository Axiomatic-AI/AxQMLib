/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PseudoInverse
import AxQM.Postulates.API.TypicalSubspace
import AxQM.Postulates.API.Evolution
import ToMathlib.Analysis.Convex.SameNonzero
import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Postulates.API — the same-non-zero-spectrum relation `ρ ≅ σ`

Nielsen & Chuang, Exercise 12.22, compares the eigenvalue distributions of density operators up to
their *non-zero* entries: writing `λ_ρ` for the spectrum of `ρ` (`State.eigenvalueDist`),
`λ_ρ ≅ λ_σ` means the two vectors have identical non-zero entries (equal up to a permutation and the
insertion/deletion of zeros). This file packages that relation on states as the definition
`State.SameNonzeroSpectrum` and establishes its two structural invariances, which are exactly the
facts the exercise's iff needs:

* **outer product for a product state** — the spectrum of `ρ ⊗ σ` is `≅` the outer product
  `λ_ρ ⊗ λ_σ` (`State.sameNonzero_eigenvalueDist_tmul`);
* **unitary invariance** — the spectrum is unchanged by unitary evolution
  (`State.sameNonzeroSpectrum_evolve`).

The engine is `State.sameNonzero_eigenvalueDist_of_isEigenbasis`: for *any* orthonormal basis
diagonalizing `ρ.op` with real eigenvalues `μ`, the spectrum `λ_ρ` is `≅ μ`. This is the
`SameNonzero` analogue of `State.vonNeumannEntropy_eq_entropy_of_isEigenbasis`; both feed a
task-specific eigenbasis into the eigenvalue-recognition theorem
`eigenvalues_multiset_map_eq_of_eigenbasis` (the multiset of `μ` agrees with the canonical
spectrum), then read the conclusion off the shared multiset.

The `SameNonzero` relation itself is defined in
`ToMathlib/Analysis/Convex/SameNonzero.lean`.

## Main definitions

* `State.SameNonzeroSpectrum ρ σ` : `SameNonzero λ_ρ λ_σ`, the state-level `≅`.

## Main statements

* `State.op_eq_sum_eigenvalueDist_rankOne` : the spectral decomposition `ρ.op = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|`.
* `State.sameNonzero_eigenvalueDist_of_isEigenbasis` : the any-eigenbasis recognition lemma.
* `State.sameNonzero_eigenvalueDist_tmul` : `λ_{ρ⊗σ} ≅ λ_ρ ⊗ λ_σ`.
* `State.sameNonzeroSpectrum_evolve` : `λ_{UρU†} ≅ λ_ρ`.
-/

namespace AxQM

variable {S T : QSystem}

/-- Spectral action of `ρ` on its canonical eigenbasis, phrased with the eigenvalue *distribution*
`ρ.eigenvalueDist` (definitionally `ρ.isDensity.isSymmetric.eigenvalues rfl`): `ρ bⱼ = λⱼ bⱼ`. A
`eigenvalueDist`-typed restatement of `State.op_apply_eigenbasis`. -/
private theorem State.op_apply_eigenbasis_dist (ρ : State S)
    (j : Fin (Module.finrank ℂ S.space)) :
    ρ.op (ρ.eigenbasis j) = (ρ.eigenvalueDist j : ℂ) • ρ.eigenbasis j :=
  ρ.op_apply_eigenbasis j

/-- **Spectral decomposition of a density operator.** Over its canonical eigenbasis,
`ρ.op = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` — the density operator is the eigenvalue-weighted sum of the rank-one
projectors onto its eigenvectors. The foundational spectral identity every rank-one-sum recognition
argument (`State.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum`,
`State.vonNeumannEntropy_eq_entropy_of_orthonormal_rankOne_sum`) wants as an *input*; those lemmas
take `ρ.op = ∑ …` as a hypothesis, and this supplies it for the canonical eigenbasis.

Proof: expand the identity as `∑ᵢ |eᵢ⟩⟨eᵢ|` (`OrthonormalBasis.sum_rankOne_eq_id`), push `ρ.op`
through the sum (`ContinuousLinearMap.comp_finset_sum`), and evaluate each `ρ.op ∘ |eᵢ⟩⟨eᵢ|` via the
eigenvalue equation `ρ eᵢ = λᵢ eᵢ` (`InnerProductSpace.comp_rankOne`, `op_apply_eigenbasis_dist`,
`InnerProductSpace.smul_rankOne`). -/
theorem State.op_eq_sum_eigenvalueDist_rankOne (ρ : State S) :
    ρ.op = ∑ i, (ρ.eigenvalueDist i : ℂ)
      • (InnerProductSpace.rankOne ℂ (ρ.eigenbasis i)) (ρ.eigenbasis i) := by
  calc ρ.op = ρ.op.comp (ContinuousLinearMap.id ℂ S.space) := (ρ.op.comp_id).symm
    _ = ρ.op.comp (∑ i, (InnerProductSpace.rankOne ℂ (ρ.eigenbasis i)) (ρ.eigenbasis i)) := by
          rw [ρ.eigenbasis.sum_rankOne_eq_id]
    _ = ∑ i, ρ.op.comp ((InnerProductSpace.rankOne ℂ (ρ.eigenbasis i)) (ρ.eigenbasis i)) := by
          rw [ContinuousLinearMap.comp_finsetSum]
    _ = _ := Finset.sum_congr rfl fun i _ => by
          rw [InnerProductSpace.comp_rankOne, ρ.op_apply_eigenbasis_dist i,
            ← InnerProductSpace.smul_rankOne]

/-- **Eigenvalue recognition for a state.** For *any* orthonormal basis `b` diagonalizing the
density operator `ρ.op` with real eigenvalues `μ` (`ρ.op (b i) = μ i • b i`), the eigenvalue
distribution `ρ.eigenvalueDist` has the same non-zero entries as `μ`, `μ ≅ λ_ρ`.

The `SameNonzero` companion of `State.vonNeumannEntropy_eq_entropy_of_isEigenbasis`: feed the given
eigenbasis into `LinearMap.IsSymmetric.eigenvalues_multiset_map_eq_of_eigenbasis` (the multiset of
`μ` equals the multiset of `ρ.op`'s canonical eigenvalues `= ρ.eigenvalueDist`), and equal full
multisets have identical non-zero entries (`SameNonzero.of_multiset_map_eq`). -/
theorem State.sameNonzero_eigenvalueDist_of_isEigenbasis {ι : Type*} [Fintype ι] (ρ : State S)
    (b : OrthonormalBasis ι ℂ S.space) {μ : ι → ℝ}
    (h : ∀ i, ρ.op (b i) = (μ i : ℂ) • b i) :
    SameNonzero μ ρ.eigenvalueDist := by
  have heigen : ∀ i, ρ.op.toLinearMap (b.toBasis i) = (μ i : ℂ) • b.toBasis i := by
    intro i; rw [b.coe_toBasis]; exact h i
  exact SameNonzero.of_multiset_map_eq
    (ρ.isDensity.isSymmetric.eigenvalues_multiset_map_eq_of_eigenbasis rfl b.toBasis heigen)

/-- **Same non-zero spectrum** `ρ ≅ σ` (Nielsen & Chuang, Ex. 12.22, the `≅` relation on spectra):
the density operators `ρ` and `σ` — on possibly *different* systems `S` and `T` — have eigenvalue
distributions with identical non-zero entries. Built on the `SameNonzero` relation. -/
def State.SameNonzeroSpectrum (ρ : State S) (σ : State T) : Prop :=
  SameNonzero ρ.eigenvalueDist σ.eigenvalueDist

/-- `SameNonzeroSpectrum` is reflexive. -/
theorem State.SameNonzeroSpectrum.refl (ρ : State S) : ρ.SameNonzeroSpectrum ρ :=
  SameNonzero.refl _

/-- `SameNonzeroSpectrum` is symmetric (across the two systems). -/
theorem State.SameNonzeroSpectrum.symm {ρ : State S} {σ : State T}
    (h : ρ.SameNonzeroSpectrum σ) : σ.SameNonzeroSpectrum ρ :=
  SameNonzero.symm h

/-- `SameNonzeroSpectrum` is transitive (across the three systems). -/
theorem State.SameNonzeroSpectrum.trans {U : QSystem} {ρ : State S} {σ : State T} {τ : State U}
    (h₁ : ρ.SameNonzeroSpectrum σ) (h₂ : σ.SameNonzeroSpectrum τ) : ρ.SameNonzeroSpectrum τ :=
  SameNonzero.trans h₁ h₂

/-- **The spectrum of a product state is the outer product of the spectra.** The eigenvalue
distribution of `ρ ⊗ σ` has the same non-zero entries as the outer product
`(i, j) ↦ λ_ρ i · λ_σ j` — `λ_{ρ⊗σ} ≅ λ_ρ ⊗ λ_σ`. This is the spectral half of Ex. 12.22's
`λ_φ ⊗ x`.

Proof: the tensor products of the two canonical eigenbases form an eigenbasis of
`(ρ ⊗ σ).op = ρ.op ⊗ σ.op` with the product eigenvalues (`TensorProduct.mapL_tmul` +
`op_apply_eigenbasis`), which recognition (`sameNonzero_eigenvalueDist_of_isEigenbasis`) identifies
with the canonical spectrum. -/
theorem State.sameNonzero_eigenvalueDist_tmul (ρ : State S) (σ : State T) :
    SameNonzero (ρ.tmul σ).eigenvalueDist
      (fun ij : Fin (Module.finrank ℂ S.space) × Fin (Module.finrank ℂ T.space) =>
        ρ.eigenvalueDist ij.1 * σ.eigenvalueDist ij.2) := by
  refine (State.sameNonzero_eigenvalueDist_of_isEigenbasis (ρ.tmul σ)
    (ρ.eigenbasis.tensorProduct σ.eigenbasis) ?_).symm
  intro ij
  -- `(ρ ⊗ σ).op` *is* `ρ.op ⊗ σ.op` (structure projection), so re-present the goal at the native
  -- `TensorProduct ℂ S.space T.space` type, where the tensor rewrites match syntactically.
  change (TensorProduct.mapL ρ.op σ.op) ((ρ.eigenbasis.tensorProduct σ.eigenbasis) ij)
      = (↑(ρ.eigenvalueDist ij.1 * σ.eigenvalueDist ij.2) : ℂ)
        • (ρ.eigenbasis.tensorProduct σ.eigenbasis) ij
  rw [OrthonormalBasis.tensorProduct_apply', TensorProduct.mapL_tmul,
    ρ.op_apply_eigenbasis_dist, σ.op_apply_eigenbasis_dist, TensorProduct.smul_tmul_smul,
    ← Complex.ofReal_mul]

/-- **The spectrum is invariant under unitary evolution.** The evolved state `U.evolve ρ = UρU†` has
the same non-zero spectrum as `ρ`: `λ_{UρU†} ≅ λ_ρ`. Unitary conjugation permutes the eigenbasis
without changing the eigenvalues.

Proof: `U` carries `ρ`'s canonical eigenbasis to an eigenbasis of `UρU†` with the *same* eigenvalues
(`evolve_op_conjStarAlgEquiv` + `op_apply_eigenbasis`), which recognition identifies with `λ_ρ`. -/
theorem State.sameNonzeroSpectrum_evolve (U : Evolution S) (ρ : State S) :
    (U.evolve ρ).SameNonzeroSpectrum ρ := by
  refine (State.sameNonzero_eigenvalueDist_of_isEigenbasis (U.evolve ρ)
    (ρ.eigenbasis.map U.toIsometryEquiv) (μ := ρ.eigenvalueDist) ?_).symm
  intro i
  rw [OrthonormalBasis.map_apply, Evolution.evolve_op_conjStarAlgEquiv,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    ρ.op_apply_eigenbasis_dist, map_smul]

end AxQM
