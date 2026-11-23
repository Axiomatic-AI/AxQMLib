/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy
public import ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# Von Neumann entropy of a diagonal density operator

Fix an orthonormal basis `b` of a finite-dimensional inner product space `E` over `𝕜` and a
*real* weight vector `p : ι → ℝ`. The operator diagonal in `b`,
`b.diagonalOperator (fun i ↦ (p i : 𝕜)) = ∑ᵢ pᵢ • |bᵢ⟩⟨bᵢ|`, is self-adjoint, and this file
relates its operator-level data to the classical distribution `p`:

* `OrthonormalBasis.trace_diagonalOperator`: its trace is `∑ᵢ wᵢ`;
* `OrthonormalBasis.diagonalOperator_isDensityOp`: it is a **density operator** when `p` is a
  probability distribution (nonnegative, summing to one);
* `OrthonormalBasis.diagonalOperator_vonNeumannEntropy`: its **von Neumann entropy is the
  Shannon entropy of `p`**, `S(∑ᵢ pᵢ |bᵢ⟩⟨bᵢ|) = H(p)`.

This is the bridge between the operator (quantum) and distribution (classical) notions of
entropy: it realises any classical distribution `p` as the eigenvalue spectrum of a diagonal
density operator, so operator-level entropy facts specialise to the Shannon entropy. In
particular it is the key step in deducing concavity of the Shannon entropy from concavity of the
von Neumann entropy (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.21).

## Main results

* `OrthonormalBasis.trace_diagonalOperator`
* `OrthonormalBasis.diagonalOperator_isDensityOp`
* `OrthonormalBasis.diagonalOperator_vonNeumannEntropy`
-/

@[expose] public section

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Trace of a diagonal operator**: `tr(∑ᵢ wᵢ |bᵢ⟩⟨bᵢ|) = ∑ᵢ wᵢ`. The trace is the sum of the
diagonal inner products `⟪bᵢ, (diag w) bᵢ⟫ = wᵢ` over the orthonormal basis. -/
theorem trace_diagonalOperator (b : OrthonormalBasis ι 𝕜 E) (w : ι → 𝕜) :
    LinearMap.trace 𝕜 E ↑(b.diagonalOperator w) = ∑ i, w i := by
  classical
  rw [LinearMap.trace_eq_sum_inner (↑(b.diagonalOperator w) : E →ₗ[𝕜] E) b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.coe_coe, b.inner_diagonalOperator w i (b i),
    orthonormal_iff_ite.mp b.orthonormal i i, ite_eq_left rfl, mul_one]

/-- A diagonal operator whose (real) diagonal `p` is a **probability distribution** — nonnegative
with `∑ᵢ pᵢ = 1` — is a **density operator**: positive (`diagonalOperator_isPositive_of_nonneg`)
with unit trace (`trace_diagonalOperator`). -/
theorem diagonalOperator_isDensityOp (b : OrthonormalBasis ι 𝕜 E) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (b.diagonalOperator fun i => (p i : 𝕜)).IsDensityOp := by
  rw [ContinuousLinearMap.isDensityOp_iff]
  refine ⟨b.diagonalOperator_isPositive_of_nonneg _ fun i => RCLike.ofReal_nonneg.mpr (hp i), ?_⟩
  rw [trace_diagonalOperator, ← RCLike.ofReal_sum, hsum, RCLike.ofReal_one]

/-- **Von Neumann entropy of a diagonal operator is the Shannon entropy of its diagonal**:
`S(∑ᵢ pᵢ |bᵢ⟩⟨bᵢ|) = H(p)` for a real diagonal `p : ι → ℝ`.

The operator `T = ∑ᵢ pᵢ |bᵢ⟩⟨bᵢ|` is self-adjoint (its adjoint replaces the diagonal by its
`star`, which fixes the real entries), so its underlying linear map is symmetric. Its von Neumann
entropy is therefore the Shannon entropy of its canonical eigenvalue spectrum
(`ContinuousLinearMap.vonNeumannEntropy_of_isSymmetric`); the orthonormal basis `b` is an
eigenbasis with eigenvalues `p` (`diagonalOperator_apply_self`), so the eigenvalue-recognition
theorem identifies the two spectra up to a permutation, and Shannon entropy depends only on the
multiset of values (`Real.entropy_eq_of_multiset_map_eq`). -/
theorem diagonalOperator_vonNeumannEntropy [FiniteDimensional 𝕜 E] [CompleteSpace E]
    (b : OrthonormalBasis ι 𝕜 E) (p : ι → ℝ) :
    (b.diagonalOperator fun i => (p i : 𝕜)).vonNeumannEntropy = Real.entropy p := by
  have hsa : IsSelfAdjoint (b.diagonalOperator fun i => (p i : 𝕜)) := by
    rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, b.diagonalOperator_adjoint]
    congr 1
    funext i
    simp only [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal]
  have hsymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  rw [ContinuousLinearMap.vonNeumannEntropy_of_isSymmetric hsymm]
  refine Real.entropy_eq_of_multiset_map_eq ?_
  refine (LinearMap.IsSymmetric.eigenvalues_multiset_map_eq_of_eigenbasis hsymm rfl b.toBasis
    fun i => ?_).symm
  have h := b.diagonalOperator_apply_self (fun j => (p j : 𝕜)) i
  simpa only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe] using h

end OrthonormalBasis
