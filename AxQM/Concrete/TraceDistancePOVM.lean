/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.POVM
import ToMathlib.Analysis.InnerProductSpace.TraceNorm
import AxQM.Concrete.ClassicalTraceDistance

/-!
# The POVM characterization of the trace distance (Nielsen & Chuang, Theorem 9.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 9.1
(p. 405) relates the (quantum) trace distance `D(ρ, σ) = ½ tr|ρ − σ|` of two
density operators to the classical trace distances of the outcome distributions
produced by measuring them: for a POVM `{Eₘ}` with outcome probabilities
`pₘ = tr(ρ Eₘ)` and `qₘ = tr(σ Eₘ)`,
```
D(ρ, σ) = max_{Eₘ} D(pₘ, qₘ).
```

This file contains the **mathematical core** of the theorem: the two
inequalities that together express the maximum, phrased over operators
`ρ σ : E →L[𝕜] E` and a `POVM ι 𝕜 E`, with the classical distance measured by
`AxQM.Concrete.classicalTraceDist` and the quantum distance by
`½ · traceNorm`. The statement for states and measurements is in
`AxQM/NC/Ch9/Theorem9_1.lean`.

## Main statements

* `classicalTraceDist_toPMF_le` — the **upper bound** `(9.24)–(9.30)`: for *every*
  POVM `M`, `D(pₘ, qₘ) ≤ ½ ‖ρ − σ‖₁`. No hypothesis on `ρ, σ` is needed.
* `classicalTraceDist_toPMF_eigenbasis_eq` — **achievability**: the projective
  measurement in an eigenbasis of the self-adjoint operator `ρ − σ` attains the
  bound, `D(pₘ, qₘ) = ½ ‖ρ − σ‖₁`. This is the converse direction of the theorem.
* `exists_povm_classicalTraceDist_eq` — the resulting **existence** statement
  packaging the maximum: some POVM attains `½ ‖ρ − σ‖₁`.

## Proof outline

*Upper bound.* Writing `dᵢ = pᵢ − qᵢ = re ⟪ρ − σ, Eᵢ⟫_HS`
(`POVM.re_hsPairing_elements_sub_eq_toPMF_sub`) and choosing signs `rᵢ = ±1` with
`|dᵢ| = rᵢ · dᵢ`, the witness `W = ∑ᵢ rᵢ • Eᵢ` has operator norm `≤ 1`
(`POVM.opNorm_sum_real_smul_le_one`), so `∑ᵢ |dᵢ| = re ⟪ρ − σ, W⟫_HS ≤ ‖ρ − σ‖₁`
by the variational bound `ContinuousLinearMap.re_hsPairing_le_traceNorm_of_opNorm_le_one`.

*Achievability.* Measuring in an orthonormal eigenbasis `b` of `ρ − σ`, the outcome
`i` has `pᵢ − qᵢ = re ⟪bᵢ, (ρ − σ) bᵢ⟫ = λᵢ` (the `i`-th eigenvalue), so
`∑ᵢ |pᵢ − qᵢ| = ∑ᵢ |λᵢ| = ‖ρ − σ‖₁` by
`LinearMap.IsSymmetric.traceNorm_eq_sum_abs_eigenvalues`.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum
Information* (10th anniv. ed.). Cambridge University Press. Theorem 9.1, §9.2.1.
-/

namespace AxQM.Concrete

open scoped BigOperators

variable {ι : Type*} [Fintype ι]
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Nielsen & Chuang, Theorem 9.1 (upper bound / measurement monotonicity).**
For any POVM `M` on `E` and any operators `ρ σ : E →L[𝕜] E`, the classical trace
distance of the Born-rule outcome distributions `pₘ = M.toPMF ρ`, `qₘ = M.toPMF σ`
is bounded by half the trace norm of `ρ − σ`:
`D(pₘ, qₘ) ≤ ½ ‖ρ − σ‖₁`.

This is the direction `(9.24)–(9.30)` of the theorem, valid for *all* POVMs and
with no positivity/self-adjointness hypothesis on `ρ, σ`. -/
theorem classicalTraceDist_toPMF_le (M : POVM ι 𝕜 E) (ρ σ : E →L[𝕜] E) :
    classicalTraceDist (M.toPMF ρ) (M.toPMF σ) ≤ (ρ - σ).traceNorm / 2 := by
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  -- The `±1` sign witness realizing `|pᵢ − qᵢ| = rᵢ · (pᵢ − qᵢ)`.
  set r : ι → ℝ := fun i => if 0 ≤ M.toPMF ρ i - M.toPMF σ i then 1 else -1 with hr
  have hr_abs_le : ∀ i, |r i| ≤ 1 := fun i => by simp only [hr]; split <;> simp
  have habs : ∀ i, |M.toPMF ρ i - M.toPMF σ i| = r i * (M.toPMF ρ i - M.toPMF σ i) :=
    fun i => by
      simp only [hr]
      by_cases h : 0 ≤ M.toPMF ρ i - M.toPMF σ i
      · rw [ite_eq_left h, one_mul, abs_of_nonneg h]
      · rw [ite_eq_right h, neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  -- The witness operator `W = ∑ᵢ rᵢ • Eᵢ`, with `‖W‖ ≤ 1`.
  set W : E →L[𝕜] E := ∑ i, (r i : 𝕜) • M.elements i with hW
  have hW_norm : ‖W‖ ≤ 1 := M.opNorm_sum_real_smul_le_one r hr_abs_le
  -- `∑ᵢ |pᵢ − qᵢ| = re ⟪ρ − σ, W⟫_HS`.
  have hsum : (∑ i, |M.toPMF ρ i - M.toPMF σ i|) = RCLike.re ((ρ - σ).hsPairing W) := by
    rw [hW, ContinuousLinearMap.hsPairing_sum_right, RCLike.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.hsPairing_smul_right, ← starRingEnd_apply, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, M.re_hsPairing_elements_sub_eq_toPMF_sub ρ σ i, ← habs i]
  -- Assemble: `D(p,q) = ½ ∑|pᵢ − qᵢ| ≤ ½ ‖ρ − σ‖₁`.
  rw [classicalTraceDist, hsum]
  gcongr
  exact ContinuousLinearMap.re_hsPairing_le_traceNorm_of_opNorm_le_one _ hW_norm

/-- **Nielsen & Chuang, Theorem 9.1 (achievability).** The projective measurement
in an orthonormal *eigenbasis* of the self-adjoint operator `ρ − σ` — the POVM
`POVM.ofOrthonormalBasis (hsymm.eigenvectorBasis rfl)` — realizes the trace
distance exactly:
`D(pₘ, qₘ) = ½ ‖ρ − σ‖₁`.

On the eigenbasis the signed difference of outcome probabilities is the eigenvalue,
`pᵢ − qᵢ = λᵢ`, so `∑ᵢ |pᵢ − qᵢ| = ∑ᵢ |λᵢ| = ‖ρ − σ‖₁`. The hypothesis `hsymm`
records that `ρ − σ` is symmetric (its self-adjointness); for density operators
`ρ, σ` it always holds. -/
theorem classicalTraceDist_toPMF_eigenbasis_eq (ρ σ : E →L[𝕜] E)
    (hsymm : ((ρ - σ : E →L[𝕜] E) : E →ₗ[𝕜] E).IsSymmetric) :
    classicalTraceDist ((POVM.ofOrthonormalBasis (hsymm.eigenvectorBasis rfl)).toPMF ρ)
      ((POVM.ofOrthonormalBasis (hsymm.eigenvectorBasis rfl)).toPMF σ)
      = (ρ - σ).traceNorm / 2 := by
  -- On the eigenbasis, `pᵢ − qᵢ = re ⟪bᵢ, (ρ − σ) bᵢ⟫ = λᵢ`.
  have hdiff : ∀ i, (POVM.ofOrthonormalBasis (hsymm.eigenvectorBasis rfl)).toPMF ρ i
      - (POVM.ofOrthonormalBasis (hsymm.eigenvectorBasis rfl)).toPMF σ i
      = hsymm.eigenvalues (rfl : Module.finrank 𝕜 E = _) i := by
    intro i
    rw [POVM.toPMF_ofOrthonormalBasis, POVM.toPMF_ofOrthonormalBasis, ← map_sub,
      ← inner_sub_right, ← sub_apply, ← ContinuousLinearMap.coe_coe (ρ - σ),
      hsymm.apply_eigenvectorBasis rfl i, inner_smul_right,
      OrthonormalBasis.inner_eq_one _ i, mul_one, RCLike.ofReal_re]
  rw [classicalTraceDist]
  simp_rw [hdiff]
  rw [← hsymm.traceNorm_eq_sum_abs_eigenvalues rfl, ContinuousLinearMap.traceNorm_toLinearMap]

/-- **Nielsen & Chuang, Theorem 9.1 (the maximum is attained).** Combining the
upper bound with achievability: for self-adjoint `ρ − σ`, *some* POVM attains
`D(pₘ, qₘ) = ½ ‖ρ − σ‖₁`. Together with `classicalTraceDist_toPMF_le` (which bounds
every POVM below this value) this says `½ ‖ρ − σ‖₁` is the maximum of `D(pₘ, qₘ)`
over all POVMs. -/
theorem exists_povm_classicalTraceDist_eq (ρ σ : E →L[𝕜] E)
    (hsymm : ((ρ - σ : E →L[𝕜] E) : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (n : ℕ) (M : POVM (Fin n) 𝕜 E),
      classicalTraceDist (M.toPMF ρ) (M.toPMF σ) = (ρ - σ).traceNorm / 2 :=
  ⟨_, _, classicalTraceDist_toPMF_eigenbasis_eq ρ σ hsymm⟩

end AxQM.Concrete
