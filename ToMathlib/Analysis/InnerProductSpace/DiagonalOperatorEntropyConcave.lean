/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.DiagonalOperatorEntropy
public import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropyMixture
public import ToMathlib.Analysis.InnerProductSpace.GeneralizedKleinInequality

/-!
# Concavity of the Shannon entropy from concavity of the von Neumann entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 11.21 asks one to
**deduce concavity of the Shannon entropy from concavity of the von Neumann entropy**. This file
carries out that deduction.

The mechanism is the diagonal bridge of
`ToMathlib/Analysis/InnerProductSpace/DiagonalOperatorEntropy.lean`: a classical probability
distribution `p : α → ℝ` is realised as the eigenvalue spectrum of the diagonal density operator
`b.diagonalOperator (fun a ↦ (p a : ℂ))` on `EuclideanSpace ℂ α`, whose von Neumann entropy is the
Shannon entropy `Real.entropy p`. A convex combination of distributions maps to the corresponding
convex combination of diagonal density operators (`OrthonormalBasis.diagonalOperator_sum_smul`), so
the operator concavity specialises to the classical concavity.

The operator concavity used is the **faithfulness-free** form: the mixing (Holevo χ) identity
`ContinuousLinearMap.sum_mul_quantumRelativeEntropy_mix` writes the concavity gap as an average
quantum relative entropy, and every term is nonnegative by the *support-condition* Klein
inequality `ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg_of_hasSupportLE`. Because
that route tolerates a rank-deficient mixture, **no strict-positivity / perturbation argument is
needed**: the general concavity, including distributions with vanishing entries, drops out directly.

## Main results

* `OrthonormalBasis.diagonalOperator_sum_smul`: diagonalisation is linear in the diagonal — the
  diagonal operator of a convex combination `fun i ↦ ∑ⱼ cⱼ wⱼ i` is `∑ⱼ cⱼ • diag wⱼ`.
* `OrthonormalBasis.hasSupportLE_diagonalOperator`: the support condition for two diagonal
  operators reduces to the pointwise support condition on their diagonals.
* `ContinuousLinearMap.IsDensityOp.sum_mul_vonNeumannEntropy_le_of_hasSupportLE`: **concavity of
  the von Neumann entropy, faithfulness-free form** — `∑ᵢ pᵢ S(ρᵢ) ≤ S(σ)` for a mixture
  `σ = ∑ᵢ pᵢ ρᵢ` under the support condition on each component (automatic for a genuine mixture),
  with no positivity hypothesis on `σ`.
* `Real.sum_mul_entropy_le_entropy_convexCombination`: **concavity of the Shannon entropy**
  (Nielsen & Chuang, Exercise 11.21) — `∑ᵢ pᵢ H(qᵢ) ≤ H(∑ᵢ pᵢ qᵢ)` for probability distributions
  `qᵢ` weighted by a probability distribution `p`. The abstract `ConcaveOn` rendering is
  `Real.entropy_concave`; this is the deduction from the von Neumann entropy asked for by the
  exercise.
-/

@[expose] public section

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Diagonalisation is linear in the diagonal.** For weights `c : κ → 𝕜` and diagonals
`w : κ → ι → 𝕜`, the diagonal operator of the pointwise combination `fun i ↦ ∑ⱼ cⱼ · wⱼ i` is the
combination of the diagonal operators, `∑ⱼ cⱼ • b.diagonalOperator wⱼ`. Both sides expand to
`∑ᵢ ∑ⱼ (cⱼ · wⱼ i) • |bᵢ⟩⟨bᵢ|`, matching after commuting the sums. -/
theorem diagonalOperator_sum_smul {κ : Type*} [Fintype κ] (b : OrthonormalBasis ι 𝕜 E)
    (c : κ → 𝕜) (w : κ → ι → 𝕜) :
    b.diagonalOperator (fun i => ∑ j, c j * w j i) = ∑ j, c j • b.diagonalOperator (w j) := by
  simp only [diagonalOperator, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- **Support condition for diagonal operators.** If the diagonal `w` vanishes wherever `v` does
(`v i = 0 → w i = 0`, i.e. `supp w ⊆ supp v`), then `b.diagonalOperator w` has support inside that
of `b.diagonalOperator v` (`HasSupportLE`, the kernel inclusion `ker (diag v) ≤ ker (diag w)`).

Proof: `w = w' * v` pointwise with `w' i := if v i = 0 then 0 else w i / v i` (the missing entries
are handled by the hypothesis), so `diag w = diag w' ∘L diag v` by
`OrthonormalBasis.diagonalOperator_comp`; hence any `x` killed by `diag v` is killed by `diag w`. -/
theorem hasSupportLE_diagonalOperator (b : OrthonormalBasis ι 𝕜 E) {v w : ι → 𝕜}
    (h : ∀ i, v i = 0 → w i = 0) :
    (b.diagonalOperator w).HasSupportLE (b.diagonalOperator v) := by
  classical
  rw [ContinuousLinearMap.hasSupportLE_iff]
  intro x hx
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
  have hfac : b.diagonalOperator w
      = b.diagonalOperator (fun i => if v i = 0 then 0 else w i / v i) ∘L b.diagonalOperator v := by
    rw [b.diagonalOperator_comp]
    congr 1
    funext i
    by_cases hvi : v i = 0
    · simp [Pi.mul_apply, hvi, h i hvi]
    · simp [Pi.mul_apply, hvi, div_mul_cancel₀ _ hvi]
  rw [hfac, ContinuousLinearMap.comp_apply, hx, map_zero]

end OrthonormalBasis

namespace ContinuousLinearMap.IsDensityOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- **Concavity of the von Neumann entropy, faithfulness-free form** (Nielsen & Chuang §11.3.5,
eq. (11.79), in full generality). For a family of density operators `ρ : ι → E →L[ℂ] E`, a mixture
`σ = ∑ᵢ pᵢ ρᵢ` (itself a density operator) with nonnegative weights `pᵢ`, and the support condition
`(ρ i).HasSupportLE σ` for every positive-weight component,
```
∑ᵢ pᵢ S(ρᵢ) ≤ S(σ).
```
There is **no strict-positivity hypothesis** on `σ`: the mixing identity
`ContinuousLinearMap.sum_mul_quantumRelativeEntropy_mix` writes the concavity gap
`S(σ) − ∑ᵢ pᵢ S(ρᵢ)` as the average relative entropy `∑ᵢ pᵢ D(ρᵢ ‖ σ)`, and each summand is
nonnegative — a `pᵢ = 0` term vanishes, while a `pᵢ > 0` term is nonnegative by the
support-condition Klein inequality `quantumRelativeEntropy_nonneg_of_hasSupportLE`, which needs
only `supp ρᵢ ⊆ supp σ` (automatic for a genuine mixture) rather than faithfulness of `σ`. This is
the operator concavity consumed by the Shannon-entropy deduction
`Real.sum_mul_entropy_le_entropy_convexCombination`. -/
theorem sum_mul_vonNeumannEntropy_le_of_hasSupportLE {ι : Type*} [Fintype ι]
    {ρ : ι → E →L[ℂ] E} (hρ : ∀ i, (ρ i).IsDensityOp) {σ : E →L[ℂ] E} (hσ : σ.IsDensityOp)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hσ_eq : σ = ∑ i, (p i : ℂ) • ρ i)
    (hsupp : ∀ i, 0 < p i → (ρ i).HasSupportLE σ) :
    ∑ i, p i * (ρ i).vonNeumannEntropy ≤ σ.vonNeumannEntropy := by
  have hid := ContinuousLinearMap.sum_mul_quantumRelativeEntropy_mix hρ p hσ hσ_eq
  have hnn : 0 ≤ ∑ i, p i * (ρ i).quantumRelativeEntropy σ := by
    refine Finset.sum_nonneg fun i _ => ?_
    rcases eq_or_lt_of_le (hp i) with h0 | hpos
    · rw [← h0]; simp
    · exact mul_nonneg (hp i)
        ((hρ i).quantumRelativeEntropy_nonneg_of_hasSupportLE hσ (hsupp i hpos))
  linarith [hid, hnn]

end ContinuousLinearMap.IsDensityOp

namespace Real

/-- **Concavity of the Shannon entropy** (Nielsen & Chuang, Exercise 11.21). For a probability
distribution `p : ι → ℝ` and a family of probability distributions `q : ι → α → ℝ`,
```
∑ᵢ pᵢ H(qᵢ) ≤ H(∑ᵢ pᵢ qᵢ),
```
the weighted average of the entropies is at most the entropy of the mixture.

This is the deduction from concavity of the von Neumann entropy asked for by the exercise: each
`qᵢ` is realised as the diagonal density operator `diag qᵢ` on `EuclideanSpace ℂ α` — with
`S(diag qᵢ) = H(qᵢ)` (`OrthonormalBasis.diagonalOperator_vonNeumannEntropy`) — the mixture
`∑ᵢ pᵢ qᵢ` maps to `∑ᵢ pᵢ • diag qᵢ = diag (∑ᵢ pᵢ qᵢ)`
(`OrthonormalBasis.diagonalOperator_sum_smul`), and the
operator concavity `ContinuousLinearMap.IsDensityOp.sum_mul_vonNeumannEntropy_le_of_hasSupportLE`
applies (its support condition holds because `diag qᵢ` is supported where the mixture is, by
`OrthonormalBasis.hasSupportLE_diagonalOperator`). The abstract `ConcaveOn` form on the domain of
nonnegative vectors is `Real.entropy_concave`. -/
theorem sum_mul_entropy_le_entropy_convexCombination {ι α : Type*} [Fintype ι] [Fintype α]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    {q : ι → α → ℝ} (hq : ∀ i a, 0 ≤ q i a) (hqsum : ∀ i, ∑ a, q i a = 1) :
    ∑ i, p i * Real.entropy (q i) ≤ Real.entropy (fun a => ∑ i, p i * q i a) := by
  classical
  set b := EuclideanSpace.basisFun α ℂ with hb
  -- The mixture distribution `μ` and its probability-distribution facts.
  have hμnn : ∀ a, 0 ≤ ∑ i, p i * q i a :=
    fun a => Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hq i a)
  have hμsum : ∑ a, ∑ i, p i * q i a = 1 := by
    rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, hqsum, mul_one]; exact hpsum
  -- Diagonal density operators for each component and for the mixture.
  have hρdop : ∀ i, (b.diagonalOperator (fun a => (q i a : ℂ))).IsDensityOp :=
    fun i => b.diagonalOperator_isDensityOp (fun a => hq i a) (hqsum i)
  have hσdop : (b.diagonalOperator (fun a => ((∑ i, p i * q i a : ℝ) : ℂ))).IsDensityOp :=
    b.diagonalOperator_isDensityOp hμnn hμsum
  -- The diagonal of the mixture is the mixture of the diagonals.
  have hσ_eq : b.diagonalOperator (fun a => ((∑ i, p i * q i a : ℝ) : ℂ))
      = ∑ i, (p i : ℂ) • b.diagonalOperator (fun a => (q i a : ℂ)) := by
    rw [← b.diagonalOperator_sum_smul (fun i => (p i : ℂ)) (fun i a => (q i a : ℂ))]
    congr 1
    funext a
    push_cast
    ring
  -- Support condition: each component's diagonal is supported where the mixture's is.
  have hsupp : ∀ i, 0 < p i → (b.diagonalOperator (fun a => (q i a : ℂ))).HasSupportLE
      (b.diagonalOperator (fun a => ((∑ j, p j * q j a : ℝ) : ℂ))) := by
    intro i hpi
    apply b.hasSupportLE_diagonalOperator
    intro a ha
    rw [Complex.ofReal_eq_zero] at ha ⊢
    have hterm : p i * q i a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hp j) (hq j a)).mp ha i
        (Finset.mem_univ i)
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h (ne_of_gt hpi)
    · exact h
  -- Apply operator concavity and translate back through the diagonal bridge
  -- (`S(diag p) = H(p)`). The identities are stated with the same `ℝ → ℂ` coercion as `hconc`,
  -- so they rewrite syntactically; the bridge lemma discharges them up to defeq.
  have e1 : ∀ i, (b.diagonalOperator (fun a => (q i a : ℂ))).vonNeumannEntropy
      = Real.entropy (q i) := fun i => b.diagonalOperator_vonNeumannEntropy (q i)
  have e2 : (b.diagonalOperator (fun a => ((∑ i, p i * q i a : ℝ) : ℂ))).vonNeumannEntropy
      = Real.entropy (fun a => ∑ i, p i * q i a) := b.diagonalOperator_vonNeumannEntropy _
  have hconc := ContinuousLinearMap.IsDensityOp.sum_mul_vonNeumannEntropy_le_of_hasSupportLE
    hρdop hσdop hp hσ_eq hsupp
  rw [e2] at hconc
  simp only [e1] at hconc
  exact hconc

end Real
