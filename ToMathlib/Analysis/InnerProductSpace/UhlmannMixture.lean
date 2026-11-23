/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.UhlmannAncilla
public import ToMathlib.Analysis.InnerProductSpace.OperatorBlockRow

/-!
# Maximizing factorizations for the fidelity trace norm (Uhlmann achievement, real overlap)

Uhlmann's theorem (`TensorProduct.isGreatest_norm_inner_of_isPurification`, Nielsen–Chuang
Theorem 9.4) asserts that the fidelity trace norm `‖√ρ √σ‖₁` is the *greatest* overlap
`‖⟪Ψ, Φ⟫‖` over purifications `Ψ` of `ρ`, `Φ` of `σ` into `E ⊗ E`; the greatest element is in
particular *attained*. The attained overlap is only known up to a phase (`IsGreatest` records
`‖⟪Ψ, Φ⟫‖`, a norm). This file records the **phase-aligned** achievement: there is a maximizing
pair whose overlap is *real and equal* to `‖√ρ √σ‖₁`.

These are the per-component data from which the joint purification of a probabilistic mixture is
assembled in the proof of the **strong concavity of the fidelity** (N&C Theorem 9.7):
`F(∑ᵢ pᵢ ρᵢ, ∑ᵢ qᵢ σᵢ) ≥ ∑ᵢ √(pᵢ qᵢ) F(ρᵢ, σᵢ)`. The joint purification's overlap is
`∑ᵢ √(pᵢ qᵢ) ⟪ψᵢ, φᵢ⟫`, and for that sum to *equal* `∑ᵢ √(pᵢ qᵢ) ‖√ρᵢ √σᵢ‖₁` (rather than merely
bound it) each term `⟪ψᵢ, φᵢ⟫` must be a nonnegative real — which is exactly what the phase
alignment below secures.

## Main results

* `ContinuousLinearMap.exists_hsPairing_eq_traceNorm_cfc_sqrt_mul` — **operator form.** For positive
  `ρ, σ` on `E` there exist `M, N : E →L E` with `M M† = ρ`, `N N† = σ`, and Hilbert–Schmidt
  pairing `N.hsPairing M = ‖√ρ √σ‖₁` (as a real, i.e. `(· : ℂ)`, value). This is the direct partner
  of `ContinuousLinearMap.norm_hsPairing_le_traceNorm_cfc_sqrt_mul` (the upper bound): together they
  give equality for the maximizing factorization.
* `TensorProduct.exists_isPurification_inner_eq_traceNorm_cfc_sqrt_mul` — **purification form.** The
  same statement phrased with purifications `Ψ, Φ` into `E ⊗ E` and their overlap `⟪Ψ, Φ⟫`.

## Proof

From the achievement half of `isGreatest_norm_inner_of_isPurification` we obtain purifications with
`‖⟪Ψ, Φ⟫‖ = ‖√ρ √σ‖₁`; matricizing (`matricize`, `isPurification_iff_matricize_comp_adjoint`,
`matricize_inner_eq_hsPairing`) turns them into operators `M, N` with `M M† = ρ`, `N N† = σ` and
`‖N.hsPairing M‖ = ‖√ρ √σ‖₁`. Multiplying `N` by the unit-modulus phase `‖z‖ / z`, where
`z := N.hsPairing M` (a no-op when `z = 0`), leaves `N N† = σ` unchanged (`|c|² = 1`) and rotates
the pairing to the nonnegative real `‖z‖ = ‖√ρ √σ‖₁` (`hsPairing_smul_left`). The purification
form is the operator form transported back through the matricization isomorphism.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

@[expose] public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

namespace ContinuousLinearMap

/-- **Maximizing factorization for the fidelity trace norm, operator form.** For positive operators
`ρ, σ` on a finite-dimensional complex inner product space `E`, there are operators `M, N : E →L E`
with `M M† = ρ`, `N N† = σ`, and Hilbert–Schmidt pairing exactly the fidelity trace norm:
`N.hsPairing M = (‖√ρ √σ‖₁ : ℂ)`.

This is the phase-aligned achievement half of Uhlmann's theorem: the upper bound
`norm_hsPairing_le_traceNorm_cfc_sqrt_mul` shows `‖N.hsPairing M‖ ≤ ‖√ρ √σ‖₁` for *every*
factorization, and here the bound is attained with a real, nonnegative pairing. The witnesses are
the matricized maximizing purifications from `isGreatest_norm_inner_of_isPurification`, with `N`
rotated
by a unit phase so that the overlap becomes real. -/
theorem exists_hsPairing_eq_traceNorm_cfc_sqrt_mul {ρ σ : E →L[ℂ] E} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    ∃ M N : E →L[ℂ] E, M.comp (adjoint M) = ρ ∧ N.comp (adjoint N) = σ ∧
      N.hsPairing M = ((cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm : ℂ) := by
  set b := stdOrthonormalBasis ℂ E
  obtain ⟨Ψ, Φ, hΨ, hΦ, htn⟩ :=
    (TensorProduct.isGreatest_norm_inner_of_isPurification hρ hσ).1
  set M := TensorProduct.matricize b Ψ
  set N := TensorProduct.matricize b Φ
  have hM : M.comp (adjoint M) = ρ :=
    (TensorProduct.isPurification_iff_matricize_comp_adjoint b ρ Ψ).mp hΨ
  have hN : N.comp (adjoint N) = σ :=
    (TensorProduct.isPurification_iff_matricize_comp_adjoint b σ Φ).mp hΦ
  have hpair : N.hsPairing M = (inner ℂ Ψ Φ : ℂ) :=
    (TensorProduct.matricize_inner_eq_hsPairing b Ψ Φ).symm
  set tn := (cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm with htndef
  have hz : ‖N.hsPairing M‖ = tn := by rw [hpair, ← htn]
  rcases eq_or_ne (N.hsPairing M) 0 with hzero | hnz
  · -- Degenerate case `‖√ρ √σ‖₁ = 0`: the unrotated factorization already works.
    refine ⟨M, N, hM, hN, ?_⟩
    have htn0 : tn = 0 := by rw [← hz, hzero, norm_zero]
    rw [hzero, htn0, Complex.ofReal_zero]
  · -- Rotate `N` by the unit phase `tn / z`, `z := N.hsPairing M`.
    have htnpos : tn ≠ 0 := by rw [← hz]; exact norm_ne_zero_iff.mpr hnz
    have hc1 : ‖((tn : ℂ) / N.hsPairing M)‖ = 1 := by
      rw [norm_div, Complex.norm_real, hz,
        Real.norm_of_nonneg (ContinuousLinearMap.traceNorm_nonneg _), div_self htnpos]
    refine ⟨M, ((tn : ℂ) / N.hsPairing M) • N, hM, ?_, ?_⟩
    · -- `(cN)(cN)† = |c|² (N N†) = N N† = σ`.
      rw [← star_eq_adjoint, star_smul, star_eq_adjoint,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, hN]
      have hcc : ((tn : ℂ) / N.hsPairing M) * star ((tn : ℂ) / N.hsPairing M) = 1 := by
        rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]; norm_num
      rw [hcc, one_smul]
    · -- `(cN).hsPairing M = c · z = (tn / z) · z = tn`.
      rw [hsPairing_smul_left, div_mul_cancel₀ _ hnz]

end ContinuousLinearMap

namespace TensorProduct

/-- **Maximizing purifications for the fidelity trace norm, purification form.** For positive
operators `ρ, σ` on a finite-dimensional complex inner product space `E`, there are purifications
`Ψ` of `ρ` and `Φ` of `σ` into `E ⊗ E` whose overlap is exactly the fidelity trace norm:
`⟪Ψ, Φ⟫ = (‖√ρ √σ‖₁ : ℂ)` (a nonnegative real).

This is the phase-aligned refinement of the achievement half of
`isGreatest_norm_inner_of_isPurification` (which only records `‖⟪Ψ, Φ⟫‖ = ‖√ρ √σ‖₁`). It is the
operator form `ContinuousLinearMap.exists_hsPairing_eq_traceNorm_cfc_sqrt_mul` transported through
the matricization isomorphism. -/
theorem exists_isPurification_inner_eq_traceNorm_cfc_sqrt_mul {ρ σ : E →L[ℂ] E}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    ∃ Ψ Φ : TensorProduct ℂ E E,
      TensorProduct.IsPurification ρ Ψ ∧ TensorProduct.IsPurification σ Φ ∧
      (inner ℂ Ψ Φ : ℂ) = ((cfc Real.sqrt ρ * cfc Real.sqrt σ).traceNorm : ℂ) := by
  obtain ⟨M, N, hM, hN, hpair⟩ :=
    ContinuousLinearMap.exists_hsPairing_eq_traceNorm_cfc_sqrt_mul hρ hσ
  set b := stdOrthonormalBasis ℂ E
  refine ⟨(matricize b).symm M, (matricize b).symm N, ?_, ?_, ?_⟩
  · rw [isPurification_iff_matricize_comp_adjoint b, LinearEquiv.apply_symm_apply]; exact hM
  · rw [isPurification_iff_matricize_comp_adjoint b, LinearEquiv.apply_symm_apply]; exact hN
  · rw [matricize_inner_eq_hsPairing b, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hpair

end TensorProduct

/-! ## Operator-level strong concavity of the fidelity

The proof of the strong concavity of the fidelity (N&C Theorem 9.7) assembles the per-component
maximizing factorizations `Mᵢ Mᵢ† = ρᵢ`, `Nᵢ Nᵢ† = σᵢ` (from
`exists_hsPairing_eq_traceNorm_cfc_sqrt_mul`) into a **block-row operator**
(`ContinuousLinearMap.blockRow`, `ToMathlib/Analysis/InnerProductSpace/OperatorBlockRow.lean`) on
the
enlarged ancilla `E ⊗ ℂ^ι`: the map `M : E ⊗ ℂ^ι →L E` whose `j`-th column is `√pⱼ Mⱼ`, i.e.
`M (x ⊗ eⱼ) = √pⱼ Mⱼ x`. Its self-outer-product `M M†` is the mixture `∑ⱼ pⱼ ρⱼ`
(`blockRow_comp_adjoint`; the columns are orthogonal, so cross terms vanish), and the
Hilbert–Schmidt pairing of the two block-rows collapses to the diagonal sum
`∑ᵢ √(pᵢ qᵢ) ⟨Nᵢ, Mᵢ⟩_HS` (`hsPairing_blockRow`). Feeding these into the general-ancilla Uhlmann
upper bound `norm_hsPairing_le_traceNorm_cfc_sqrt_mul` yields the operator-level inequality
`∑ᵢ √(pᵢ qᵢ) ‖√ρᵢ √σᵢ‖₁ ≤ ‖√(∑ᵢ pᵢ ρᵢ) √(∑ᵢ qᵢ σᵢ)‖₁`.
-/

namespace ContinuousLinearMap

/-- **Strong concavity of the fidelity trace norm, operator form** (the operator core of
Nielsen–Chuang Theorem 9.7). For finite families of positive operators `ρ, σ : ι → (E →L[ℂ] E)` and
non-negative weights `p, q : ι → ℝ`,
`∑ᵢ √(pᵢ qᵢ) ‖√ρᵢ √σᵢ‖₁ ≤ ‖√(∑ᵢ pᵢ ρᵢ) √(∑ᵢ qᵢ σᵢ)‖₁`.
No normalization `∑ pᵢ = ∑ qᵢ = 1` is needed; the probability hypotheses enter only when this is
lifted to the fidelity of *states* (`State.fidelity`).

Proof (N&C p. 414): for each `i` pick maximizing factorizations `Mᵢ Mᵢ† = ρᵢ`, `Nᵢ Nᵢ† = σᵢ` with
`Nᵢ.hsPairing Mᵢ = ‖√ρᵢ √σᵢ‖₁` a non-negative real (`exists_hsPairing_eq_traceNorm_cfc_sqrt_mul`).
Assemble the block-rows `M = blockRow b (√pᵢ Mᵢ)`, `N = blockRow b (√qᵢ Nᵢ)` on the ancilla
`E ⊗ ℂ^ι`. Then `M M† = ∑ᵢ pᵢ ρᵢ`, `N N† = ∑ᵢ qᵢ σᵢ` (`blockRow_comp_adjoint`), and
`N.hsPairing M = ∑ᵢ √(pᵢ qᵢ) ‖√ρᵢ √σᵢ‖₁` (`hsPairing_blockRow`), a non-negative real. The
general-ancilla Uhlmann upper bound `norm_hsPairing_le_traceNorm_cfc_sqrt_mul` gives
`‖N.hsPairing M‖ ≤ ‖√(∑ pᵢ ρᵢ) √(∑ qᵢ σᵢ)‖₁`, and `‖·‖` of the non-negative real overlap is the
overlap itself. -/
theorem traceNorm_cfc_sqrt_mul_cfc_sqrt_sum_ge {ι : Type*} [Fintype ι]
    (ρ σ : ι → E →L[ℂ] E) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 ≤ σ i)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    ∑ i, Real.sqrt (p i * q i) * (cfc Real.sqrt (ρ i) * cfc Real.sqrt (σ i)).traceNorm
      ≤ (cfc Real.sqrt (∑ i, (p i : ℂ) • ρ i)
          * cfc Real.sqrt (∑ i, (q i : ℂ) • σ i)).traceNorm := by
  classical
  have : CompleteSpace (E ⊗[ℂ] EuclideanSpace ℂ ι) := FiniteDimensional.completeSpace ℂ _
  set b := EuclideanSpace.basisFun ι ℂ with hb
  -- Per-component maximizing factorizations with real overlap.
  choose M N hM hN hpair using fun i =>
    ContinuousLinearMap.exists_hsPairing_eq_traceNorm_cfc_sqrt_mul (hρ i) (hσ i)
  set M' : ι → E →L[ℂ] E := fun i => (Real.sqrt (p i) : ℂ) • M i with hM'
  set N' : ι → E →L[ℂ] E := fun i => (Real.sqrt (q i) : ℂ) • N i with hN'
  -- `M M† = ∑ pᵢ ρᵢ`: block-row of `√pᵢ`-scaled columns is the `pᵢ`-mixture (`|√pᵢ|² = pᵢ`).
  have hMbig : (blockRow b M') ∘L adjoint (blockRow b M') = ∑ i, (p i : ℂ) • ρ i := by
    rw [hM', blockRow_smul_comp_adjoint]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp i),
      hM i]
  -- `N N† = ∑ qᵢ σᵢ`.
  have hNbig : (blockRow b N') ∘L adjoint (blockRow b N') = ∑ i, (q i : ℂ) • σ i := by
    rw [hN', blockRow_smul_comp_adjoint]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hq i),
      hN i]
  -- The joint overlap is the (non-negative real) diagonal sum.
  have hpairbig : (blockRow b N').hsPairing (blockRow b M')
      = ((∑ i, Real.sqrt (p i * q i)
          * (cfc Real.sqrt (ρ i) * cfc Real.sqrt (σ i)).traceNorm : ℝ) : ℂ) := by
    rw [hsPairing_blockRow, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hN', hM', hsPairing_smul_left, hsPairing_smul_right, hpair i, Complex.star_def,
      Complex.conj_ofReal, Real.sqrt_mul (hp i)]
    push_cast
    ring
  -- Feed the block-rows into the general-ancilla Uhlmann upper bound.
  have hub := ContinuousLinearMap.norm_hsPairing_le_traceNorm_cfc_sqrt_mul hMbig hNbig
  rw [hpairbig, Complex.norm_real, Real.norm_of_nonneg] at hub
  · exact hub
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _)
      (ContinuousLinearMap.traceNorm_nonneg _)

end ContinuousLinearMap
