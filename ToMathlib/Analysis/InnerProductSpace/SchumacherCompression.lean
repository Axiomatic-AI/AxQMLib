/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.SchumacherEncoder
public import ToMathlib.Analysis.InnerProductSpace.QuantumDataCompression

/-! # Schumacher's projection–reset compression scheme

The direct (achievability) part of Schumacher's quantum noiseless channel coding theorem
(Nielsen–Chuang, *Quantum Computation and Quantum Information*, §12.2.2, Theorem 12.6, Eqs.
(12.50)–(12.53)) exhibits, at each block length, a concrete rate-`R` compression scheme whose
entanglement fidelity is close to `1`. This file packages that scheme as a bona-fide
`ContinuousLinearMap.QuantumCompressionScheme`.

Given a Hilbert space `K` (standing for `H^⊗n`), an orthonormal basis `b : OrthonormalBasis ι ℂ K`,
a set `s` of "typical" indices, a reference index `i₀ ∈ s`, and a qubit budget `numBits` with
`s.card ≤ 2 ^ numBits`, the **projection–reset compression scheme** `projectionReset b s i₀ hi₀
hcard` has:

* compression operation `Cₙ` = the Schumacher projection–reset encoder
  (`ContinuousLinearMap.schumacherEncoder`, N&C Eq. (12.50)): the code-subspace projector
  `P = ∑_{i ∈ s} |bᵢ⟩⟨bᵢ|` together with the reset operators `Aᵢ = |b i₀⟩⟨bᵢ|` for `i ∉ s`;
* decompression operation `Dₙ` = the identity (a single Kraus operator `1`), per N&C's `Dₙ(σ) = σ`;
* compressed subspace `range P`, of dimension `s.card ≤ 2 ^ numBits`.

Its entanglement fidelity dominates the code-overlap term:

`F(τ, Dₙ ∘ Cₙ) ≥ |tr(τ P)|²`  (N&C Eq. (12.52), `projectionReset_fidelity_ge`),

which is the direct-part inequality: specialised to
`τ = ρ^⊗n` and `P = P(n, ε)` the typical subspace projector, part (1) of the typical subspace
theorem gives `tr(ρ^⊗n P) ≥ 1 − δ`, whence `F ≥ (1 − δ)² → 1`.

## Main definitions and results

* `ContinuousLinearMap.QuantumCompressionScheme.projectionReset` — the projection–reset scheme.
* `ContinuousLinearMap.QuantumCompressionScheme.projectionReset_fidelity_eq` — its entanglement
  fidelity equals that of the bare Schumacher encoder (the identity decoder contributes nothing).
* `ContinuousLinearMap.QuantumCompressionScheme.projectionReset_fidelity_ge` — **N&C Eq. (12.52)**:
  `|tr(τ P)|² ≤ F(τ, Dₙ ∘ Cₙ)`.

The rate bound uses the reusable rank identity
`InnerProductSpace.finrank_range_orthonormalProjector` (rank of `∑_{i ∈ s} |bᵢ⟩⟨bᵢ|` is `s.card`),
which lives upstream beside the rest of the projector API in
`ToMathlib/Analysis/InnerProductSpace/RankOneProjector.lean`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2 (Theorem 12.6; Eqs. (12.50)–(12.53)).
-/

open scoped InnerProductSpace ComplexConjugate

@[expose] public section

namespace ContinuousLinearMap.QuantumCompressionScheme

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
  [CompleteSpace K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Schumacher's projection–reset compression scheme** (Nielsen & Chuang, §12.2.2, Eq. (12.50)):
the rate-`numBits` quantum compression scheme on `K` whose compression operation is the projection–
reset encoder `ContinuousLinearMap.schumacherEncoder b s i₀` and whose decompression operation is
the identity (`Dₙ(σ) = σ`, a single Kraus operator `1`).

The `Option ι`-indexed encoder family is reindexed onto `Fin (Fintype.card (Option ι))`; its
trace-preservation is `schumacherEncoder_isTracePreserving`, and every element factors through the
code projector `P = ∑_{i ∈ s} |bᵢ⟩⟨bᵢ|` because `i₀ ∈ s` fixes `P (b i₀) = b i₀`. The compressed
subspace `range P` has dimension `s.card ≤ 2 ^ numBits`. -/
noncomputable def projectionReset (b : OrthonormalBasis ι ℂ K) (s : Finset ι) (i₀ : ι)
    (hi₀ : i₀ ∈ s) {numBits : ℕ} (hcard : s.card ≤ 2 ^ numBits) :
    QuantumCompressionScheme K numBits where
  encCard := Fintype.card (Option ι)
  decCard := 1
  encode j := schumacherEncoder b s i₀ ((Fintype.equivFin (Option ι)).symm j)
  decode _ := 1
  encode_isTracePreserving := by
    rw [← schumacherEncoder_isTracePreserving b s i₀]
    exact Equiv.sum_comp (Fintype.equivFin (Option ι)).symm
      fun o => adjoint (schumacherEncoder b s i₀ o) * schumacherEncoder b s i₀ o
  decode_isTracePreserving := by simp [← star_eq_adjoint]
  compressedProjection := InnerProductSpace.orthonormalProjector ℂ (⇑b) s
  isStarProjection_compressedProjection :=
    InnerProductSpace.isStarProjection_orthonormalProjector b.orthonormal s
  compressedProjection_mul_encode j :=
    orthonormalProjector_mul_schumacherEncoder b s i₀ hi₀ _
  finrank_range_compressedProjection_le :=
    (InnerProductSpace.finrank_range_orthonormalProjector b s).trans_le hcard

/-- The entanglement fidelity of the projection–reset scheme equals that of the bare Schumacher
encoder: the decompression operation is the identity (a single Kraus operator `1`), so the combined
operation `Dₙ ∘ Cₙ` has the same operation elements as `Cₙ` (up to the reindexing
`Fin 1 × Fin (Fintype.card (Option ι)) ≃ Option ι`), and the entanglement fidelity depends only on
the family of operation elements. -/
theorem projectionReset_fidelity_eq (b : OrthonormalBasis ι ℂ K) (s : Finset ι) (i₀ : ι)
    (hi₀ : i₀ ∈ s) {numBits : ℕ} (hcard : s.card ≤ 2 ^ numBits) (τ : K →L[ℂ] K) :
    (projectionReset b s i₀ hi₀ hcard).fidelity τ
      = entanglementFidelity τ (schumacherEncoder b s i₀) := by
  rw [fidelity, entanglementFidelity, entanglementFidelity]
  refine Fintype.sum_equiv
    ((Equiv.uniqueProd (Fin (Fintype.card (Option ι))) (Fin 1)).trans
      (Fintype.equivFin (Option ι)).symm) _ _ fun p => ?_
  simp only [composite_apply, projectionReset, one_mul, Equiv.trans_apply, Equiv.uniqueProd_apply]

/-- **Nielsen & Chuang, Eq. (12.52).** The entanglement fidelity of the projection–reset scheme is
bounded below by the squared code-overlap `|tr(τ P)|²`, where `P = ∑_{i ∈ s} |bᵢ⟩⟨bᵢ|` is the
compressed-subspace projector: `P` is one of the operation elements and the remaining reset-operator
terms are nonnegative (`entanglementFidelity_schumacherEncoder_ge`). This is the direct
(achievability) inequality of Schumacher's noiseless channel coding theorem. -/
theorem projectionReset_fidelity_ge (b : OrthonormalBasis ι ℂ K) (s : Finset ι) (i₀ : ι)
    (hi₀ : i₀ ∈ s) {numBits : ℕ} (hcard : s.card ≤ 2 ^ numBits) (τ : K →L[ℂ] K) :
    ‖LinearMap.trace ℂ K
        ((τ * InnerProductSpace.orthonormalProjector ℂ (⇑b) s : K →L[ℂ] K) : K →ₗ[ℂ] K)‖ ^ 2
      ≤ (projectionReset b s i₀ hi₀ hcard).fidelity τ := by
  rw [projectionReset_fidelity_eq]
  exact entanglementFidelity_schumacherEncoder_ge b s i₀ τ

end ContinuousLinearMap.QuantumCompressionScheme
