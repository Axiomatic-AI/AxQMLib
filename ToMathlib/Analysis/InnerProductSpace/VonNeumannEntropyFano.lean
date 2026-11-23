/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropyPinching
public import ToMathlib.Analysis.InnerProductSpace.DiagonalOperatorEntropy
public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-! # The density-operator Fano bound

For a density operator `ρ` on a finite-dimensional complex inner product space `E` of dimension
`d = finrank ℂ E`, and any unit vector `ψ`, the von Neumann entropy obeys the **density-operator
Fano bound**
`S(ρ) ≤ H(p) + (1 - p) · log (d - 1)`,   `p := ⟨ψ, ρ ψ⟩`,
where `H` is the binary Shannon entropy. This is the operator core of the quantum Fano inequality
(Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 12.9, eqs. (12.113)–
(12.115)): applied to the state `ρ_{R'Q'}` of the reference-plus-system after a quantum operation,
with `ψ` the (pure) initial `|RQ⟩` and `p` the entanglement fidelity, it is the quantum Fano
inequality `S(ρ, E) ≤ H(F) + (1 - F) · log (d² - 1)`.

The proof is the two-step argument of N&C §12.4.1, both steps operator-level:

* **The diagonal bound** (`ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_le_entropy_diag`):
  `S(ρ) ≤ H(diag ρ)`, the Shannon entropy of the diagonal of `ρ` in *any* orthonormal basis `b`.
  This is the operator form of N&C Theorem 11.9 (a projective measurement never decreases entropy):
  the rank-one projectors `Pᵢ = |bᵢ⟩⟨bᵢ|` pinch `ρ` to the diagonal operator
  `Σᵢ ⟨bᵢ, ρ bᵢ⟩ |bᵢ⟩⟨bᵢ|`, whose entropy is `H(diag ρ)`, and pinching never decreases entropy
  (`ContinuousLinearMap.vonNeumannEntropy_le_krausSumₗ`).

* **The grouping step** (`ContinuousLinearMap.IsDensityOp.vonNeumannEntropy_le_binEntropy_add`):
  extend `ψ` to an orthonormal basis and apply the classical grouping inequality
  `Real.entropy_le_qaryEntropy` (N&C eq. (12.114)) to the diagonal distribution `p`, whose
  distinguished entry is `⟨ψ, ρ ψ⟩`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.4.1 (Theorem 12.9), §11.3 (Theorem 11.9).
-/

open scoped InnerProductSpace ComplexConjugate
open InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- For a density operator `ρ`, the diagonal inner product `⟨x, ρ x⟩` equals its own real part
(it is real), since `ρ` is symmetric. -/
theorem IsDensityOp.inner_self_eq_re {ρ : E →L[ℂ] E} (hρ : ρ.IsDensityOp) (x : E) :
    inner ℂ x (ρ x) = ((RCLike.re (inner ℂ x (ρ x)) : ℝ) : ℂ) :=
  (hρ.isSymmetric.coe_re_inner_self_apply x).symm

/-- **The diagonal-entropy bound** (operator form of Nielsen & Chuang Theorem 11.9): for a density
operator `ρ` and any orthonormal basis `b`, the von Neumann entropy is at most the Shannon entropy
of the diagonal `pᵢ = ⟨bᵢ, ρ bᵢ⟩` of `ρ` in that basis:
`S(ρ) ≤ H(diag ρ)`.

The rank-one projectors `Pᵢ = |bᵢ⟩⟨bᵢ|` form a complete family of orthogonal star projections; the
pinching `Σᵢ Pᵢ ρ Pᵢ` is the diagonal operator `Σᵢ ⟨bᵢ, ρ bᵢ⟩ |bᵢ⟩⟨bᵢ|`, whose entropy is
`H(diag ρ)` (`OrthonormalBasis.diagonalOperator_vonNeumannEntropy`), and pinching never decreases
entropy (`ContinuousLinearMap.vonNeumannEntropy_le_krausSumₗ`). -/
theorem IsDensityOp.vonNeumannEntropy_le_entropy_diag {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) {ρ : E →L[ℂ] E} (hρ : ρ.IsDensityOp) :
    ρ.vonNeumannEntropy ≤ Real.entropy (fun i => RCLike.re (inner ℂ (b i) (ρ (b i)))) := by
  classical
  set P : ι → (E →L[ℂ] E) := fun i => rankOne ℂ (b i) (b i) with hP
  have hProj : ∀ i, IsStarProjection (P i) := fun i =>
    InnerProductSpace.isStarProjection_rankOne_self (b.orthonormal.1 i)
  have hOrth : ∀ i j, i ≠ j → P i * P j = 0 := fun i j hij => by
    simp only [hP, ContinuousLinearMap.mul_def, rankOne_comp_rankOne, b.orthonormal.2 hij,
      zero_smul]
  have hSum : ∑ i, P i = 1 := b.sum_rankOne_eq_id
  -- The pinching `Σᵢ Pᵢ ρ Pᵢ` is the diagonal operator with diagonal `⟨bᵢ, ρ bᵢ⟩`.
  have hdiag : krausSumₗ P ρ
      = b.diagonalOperator (fun i => ((RCLike.re (inner ℂ (b i) (ρ (b i))) : ℝ) : ℂ)) := by
    rw [krausSumₗ_eq_sum_conj_of_isStarProjection hProj, OrthonormalBasis.diagonalOperator]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hρ.inner_self_eq_re (b i)]
    ext z
    simp only [hP, mul_apply_eq_comp, InnerProductSpace.rankOne_apply, map_smul,
      _root_.smul_apply, smul_smul, mul_comm]
  -- Assemble: pinching bound + entropy of the diagonal operator.
  calc ρ.vonNeumannEntropy
      ≤ (krausSumₗ P ρ).vonNeumannEntropy := vonNeumannEntropy_le_krausSumₗ hProj hOrth hSum hρ
    _ = Real.entropy (fun i => RCLike.re (inner ℂ (b i) (ρ (b i)))) := by
        rw [hdiag]
        exact b.diagonalOperator_vonNeumannEntropy _

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- For a density operator `ρ` and any orthonormal basis `b`, the real diagonal
`pᵢ = ⟨bᵢ, ρ bᵢ⟩` is normalized: `∑ᵢ pᵢ = tr ρ = 1`. The ONB-diagonal companion of
`ContinuousLinearMap.IsDensityOp.eigenvalues_sum_eq_one`. -/
theorem IsDensityOp.sum_re_inner_orthonormalBasis_eq_one {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) {ρ : E →L[ℂ] E} (hρ : ρ.IsDensityOp) :
    ∑ i, RCLike.re (inner ℂ (b i) (ρ (b i))) = 1 := by
  have key : ∑ i, inner ℂ (b i) (ρ (b i)) = (1 : ℂ) := by
    have h := LinearMap.trace_eq_sum_inner (↑ρ : E →ₗ[ℂ] E) b
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← h]
    exact hρ.trace_eq_one
  refine RCLike.ofReal_injective (K := ℂ) ?_
  push_cast
  rw [← key]
  exact Finset.sum_congr rfl fun i _ => (hρ.inner_self_eq_re (b i)).symm

/-- **The density-operator Fano bound** (operator core of Nielsen & Chuang Theorem 12.9). For a
density operator `ρ` on a `d`-dimensional space and any unit vector `ψ`, writing `p = ⟨ψ, ρ ψ⟩`,
`S(ρ) ≤ H(p) + (1 - p) · log (d - 1)`,
where `H` is the binary Shannon entropy.

Extend `ψ` to an orthonormal basis; the diagonal distribution `pᵢ = ⟨bᵢ, ρ bᵢ⟩` is a probability
distribution (nonnegative, summing to `tr ρ = 1`) whose distinguished entry `p₀ = ⟨ψ, ρ ψ⟩` is the
entanglement fidelity in the intended application. The diagonal bound `S(ρ) ≤ H(p)` combines with
the classical grouping inequality `H(p) ≤ H(1 - p₀) + (1 - p₀) · log (d - 1)`
(`Real.entropy_le_qaryEntropy`) and the symmetry `H(1 - p₀) = H(p₀)` of the binary entropy. -/
theorem IsDensityOp.vonNeumannEntropy_le_binEntropy_add {ρ : E →L[ℂ] E} (hρ : ρ.IsDensityOp)
    {ψ : E} (hψ : ‖ψ‖ = 1) :
    ρ.vonNeumannEntropy ≤ Real.binEntropy (RCLike.re (inner ℂ ψ (ρ ψ)))
      + (1 - RCLike.re (inner ℂ ψ (ρ ψ))) * Real.log ((Module.finrank ℂ E : ℝ) - 1) := by
  classical
  set d := Module.finrank ℂ E with hd
  -- `E` is nontrivial (it has a unit vector), hence `0 < d`.
  have hψ0 : ψ ≠ 0 := by rintro rfl; simp at hψ
  have hNontriv : Nontrivial E := ⟨ψ, 0, hψ0⟩
  have hd0 : 0 < d := Module.finrank_pos
  set i₀ : Fin d := ⟨0, hd0⟩ with hi₀
  -- Extend `ψ` to an orthonormal basis `b : OrthonormalBasis (Fin d) ℂ E` with `b i₀ = ψ`.
  have hcard : Module.finrank ℂ E = Fintype.card (Fin d) := by rw [Fintype.card_fin]
  have horth : Orthonormal ℂ (({i₀} : Set (Fin d)).domRestrict (fun _ => ψ)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    have hvali : ({i₀} : Set (Fin d)).domRestrict (fun _ => ψ) ⟨i₀, hi⟩ = ψ := rfl
    rw [hvali, inner_self_eq_norm_sq_to_K, hψ, ite_eq_left rfl]
    norm_num
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  have hbψ : b i₀ = ψ := hb i₀ rfl
  -- The diagonal distribution `p` is a probability distribution.
  set p : Fin d → ℝ := fun i => RCLike.re (inner ℂ (b i) (ρ (b i))) with hp_def
  have hp_nn : ∀ i, 0 ≤ p i := fun i => hρ.isPositive.re_inner_nonneg_right (b i)
  have hp_sum : ∑ i, p i = 1 := hρ.sum_re_inner_orthonormalBasis_eq_one b
  -- Diagonal bound then classical grouping.
  have hdiag := hρ.vonNeumannEntropy_le_entropy_diag b
  have hgroup := Real.entropy_le_qaryEntropy hp_nn hp_sum i₀
  rw [Real.qaryEntropy_eq_log_add_binEntropy, Real.binEntropy_one_sub, Fintype.card_fin] at hgroup
  have hpi₀ : p i₀ = RCLike.re (inner ℂ ψ (ρ ψ)) := by simp only [hp_def, hbψ]
  rw [hpi₀] at hgroup
  calc ρ.vonNeumannEntropy
      ≤ Real.entropy p := hdiag
    _ ≤ (1 - RCLike.re (inner ℂ ψ (ρ ψ))) * Real.log ((d : ℤ) - 1 : ℤ)
          + Real.binEntropy (RCLike.re (inner ℂ ψ (ρ ψ))) := hgroup
    _ = Real.binEntropy (RCLike.re (inner ℂ ψ (ρ ψ)))
          + (1 - RCLike.re (inner ℂ ψ (ρ ψ))) * Real.log ((d : ℝ) - 1) := by push_cast; ring

end ContinuousLinearMap
