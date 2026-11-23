/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
public import ToMathlib.Analysis.InnerProductSpace.CFC
public import ToMathlib.Analysis.InnerProductSpace.Trace
public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# The quantum relative entropy of commuting diagonal operators is the classical KL divergence

Fix a finite-dimensional complex inner product space `E` and an orthonormal basis `b` of `E`. If
two self-adjoint operators `A, B` are **simultaneously diagonal** in `b` with real eigenvalue lists
`p, q` — `A (b i) = pᵢ • b i` and `B (b i) = qᵢ • b i` — then their quantum (Umegaki) relative
entropy collapses to the classical relative entropy (Kullback–Leibler divergence) of the eigenvalue
lists:

`D(A ‖ B) = ∑ᵢ pᵢ (log pᵢ − log qᵢ) = Real.relativeEntropy p q`.

This is the operator-level content behind the fact that the quantum relative entropy of two
diagonal (classical) states equals the classical KL divergence of their diagonals — the identity
that turns the classical mutual information appearing in the Holevo bound (Nielsen & Chuang,
Theorem 12.1) into a sum of quantum relative entropies of the measurement-outcome states.

The identity is **unconditional** — no faithfulness/strict-positivity hypothesis — because the
finite real-valued generators handle their boundary cases compatibly: `Real.log 0 = 0` makes the
`pᵢ = 0` / `qᵢ = 0` terms vanish on both sides (`cfc Real.log B` acts as `0` on the kernel of `B`,
matching `Real.log 0 = 0` in the classical sum), and `Real.log` is continuous on the (finite)
spectrum of any self-adjoint operator (`IsSelfAdjoint.continuousOn_log_spectrum`), so the spectral
mapping on eigenvectors (`IsSelfAdjoint.cfc_apply_smul_of_apply_eq_smul`) applies even when `0` lies
in the spectrum.

## Main results

* `ContinuousLinearMap.quantumRelativeEntropy_eq_relativeEntropy_of_isEigenbasis` — the identity
  `D(A ‖ B) = Real.relativeEntropy p q` for `A, B` simultaneously diagonal in an orthonormal basis.
-/

@[expose] public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- **The quantum relative entropy of two commuting diagonal operators is the classical KL
divergence.** If self-adjoint operators `A, B` are simultaneously diagonal in an orthonormal basis
`b` with real eigenvalue lists `p, q` (`A (b i) = pᵢ • b i`, `B (b i) = qᵢ • b i`), then

`D(A ‖ B) = Real.relativeEntropy p q = ∑ᵢ pᵢ (log pᵢ − log qᵢ)`.

Both trace terms of `D(A ‖ B) = re tr((log A) A) − re tr((log B) A)` are evaluated in the shared
eigenbasis `b`: writing `X` for `A` or `B` with eigenvalues `r`, the operator `(cfc log X) ∘ A`
sends `b i ↦ (pᵢ · log rᵢ) • b i` (spectral mapping on eigenvectors, valid since `log` is
continuous on the finite spectrum even where `0` occurs), so `re tr` of it is `∑ᵢ pᵢ log rᵢ`. The
difference `∑ pᵢ log pᵢ − ∑ pᵢ log qᵢ` is the classical relative entropy. No faithfulness is
needed. -/
theorem quantumRelativeEntropy_eq_relativeEntropy_of_isEigenbasis
    (b : OrthonormalBasis ι ℂ E) {A B : E →L[ℂ] E} {p q : ι → ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hpA : ∀ i, A (b i) = (p i : ℂ) • b i) (hqB : ∀ i, B (b i) = (q i : ℂ) • b i) :
    A.quantumRelativeEntropy B = Real.relativeEntropy p q := by
  classical
  -- For a diagonal `X` (eigenvalues `r`), `re tr((log X) ∘ A) = ∑ᵢ pᵢ log rᵢ`.
  have key : ∀ (X : E →L[ℂ] E) (r : ι → ℝ), IsSelfAdjoint X → (∀ i, X (b i) = (r i : ℂ) • b i) →
      RCLike.re ((LinearMap.trace ℂ E) ((cfc Real.log X).toLinearMap ∘ₗ A.toLinearMap))
        = ∑ i, p i * Real.log (r i) := by
    intro X r hX hrX
    have happ : ∀ i, ((cfc Real.log X).toLinearMap ∘ₗ A.toLinearMap) (b i)
        = ((p i * Real.log (r i) : ℝ) : ℂ) • b i := by
      intro i
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hpA i, map_smul,
        hX.cfc_apply_smul_of_apply_eq_smul rfl hX.continuousOn_log_spectrum (hrX i),
        smul_smul, ← Complex.ofReal_mul]
    rw [LinearMap.trace_eq_sum_inner _ b]
    have hin : ∀ i, inner ℂ (b i) (((cfc Real.log X).toLinearMap ∘ₗ A.toLinearMap) (b i))
        = ((p i * Real.log (r i) : ℝ) : ℂ) := by
      intro i
      rw [happ i, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i i]
      simp
    simp_rw [hin]
    rw [← Complex.ofReal_sum]
    simp
  rw [ContinuousLinearMap.quantumRelativeEntropy_def, key A p hA hpA, key B q hB hqB,
    Real.relativeEntropy_eq, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end ContinuousLinearMap
