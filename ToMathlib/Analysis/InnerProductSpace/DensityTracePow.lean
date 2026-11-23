/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFC
public import ToMathlib.Analysis.InnerProductSpace.Density
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Convex.Mul

/-!
# Trace of powers of a density operator, and its monotonicity under depolarizing mixing

For a self-adjoint operator `T` on a finite-dimensional complex inner product space, the trace of
`(cfc g T) ^ k` is the sum of `(g λᵢ) ^ k` over `T`'s eigenvalues
(`IsSelfAdjoint.re_trace_cfc_pow_eq_sum`).

The main result, `ContinuousLinearMap.IsDensityOp.re_trace_depolarize_pow_le`, uses this to prove
that **mixing a density operator `ρ` toward the maximally mixed state never increases `tr(ρ ^ k)`**:
for
`0 ≤ p ≤ 1` and `k ≥ 1`,
`re tr(((p) • (d⁻¹ • 1) + (1 - p) • ρ) ^ k) ≤ re tr(ρ ^ k)`, where `d = finrank ℂ E`.
This is the operator-level content of the fact that the (generalized, `d`-dimensional) depolarizing
channel `E(ρ) = p·I/d + (1 - p)·ρ` does not increase `tr(ρ ^ k)` (Nielsen & Chuang, Exercise 8.18).

## Main statements

* `IsSelfAdjoint.re_trace_cfc_pow_eq_sum` — `re tr((cfc g T) ^ k) = ∑ᵢ (g λᵢ) ^ k`.
* `sum_mix_uniform_pow_le` — the underlying real inequality: for a probability vector `lam` on
  `Fin n`, `∑ᵢ ((1 - p)·lamᵢ + p/n) ^ k ≤ ∑ᵢ lamᵢ ^ k`.
* `ContinuousLinearMap.IsDensityOp.re_trace_depolarize_pow_le` — the density-operator statement.

## Implementation notes

The depolarized operator `(1 - p) • ρ + p • (I/d)` is a *function of* `ρ` — it is `cfc g ρ` for the
affine `g x = (1 - p)·x + p/d` — so it shares `ρ`'s eigenbasis. Expressing both `tr(ρ ^ k)` and
`tr(E(ρ) ^ k)` as sums over `ρ`'s *own* eigenvalues (rather than comparing two operators'
independent spectral orderings) reduces the operator inequality to the real inequality
`sum_mix_uniform_pow_le`,
which follows from convexity of `x ↦ x ^ k` together with the power-mean bound
`pow_sum_div_card_le_sum_pow`.
-/

@[expose] public section

open scoped InnerProductSpace
open Module (finrank)

/-- **Trace of `(cfc g T) ^ k` over the eigenbasis.** For a self-adjoint operator `T` on a
finite-dimensional complex inner product space, `re tr((cfc g T) ^ k) = ∑ᵢ (g λᵢ) ^ k`, the sum of
`(g λᵢ) ^ k` over `T`'s eigenvalues `λᵢ`. Proof: `(cfc g T) ^ k = cfc (·^k ∘ g) T` (`cfc_pow`), then
apply `IsSelfAdjoint.re_trace_cfc_comp_eq_sum` with `M = 1`, using `re ⟪eᵢ, eᵢ⟫ = 1` for the
orthonormal eigenbasis. -/
theorem IsSelfAdjoint.re_trace_cfc_pow_eq_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E] {T : E →L[ℂ] E} {n : ℕ}
    (hT : IsSelfAdjoint T) (hn : finrank ℂ E = n) (g : ℝ → ℝ)
    (hg : ContinuousOn g (spectrum ℝ T)) (k : ℕ) :
    RCLike.re (LinearMap.trace ℂ E ((cfc g T ^ k : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = ∑ i, (g (hT.isSymmetric.eigenvalues hn i)) ^ k := by
  have hgk : ContinuousOn (fun x => g x ^ k) (spectrum ℝ T) := hg.pow k
  rw [← cfc_pow g k T]
  have hsum := hT.re_trace_cfc_comp_eq_sum hn (fun x => g x ^ k) hgk (1 : E →L[ℂ] E)
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id, LinearMap.comp_id,
    ContinuousLinearMap.id_apply] at hsum
  rw [hsum]
  simp [(hT.isSymmetric.eigenvectorBasis hn).orthonormal.1]

/-- **Trace of `T ^ k` over the eigenbasis.** For a self-adjoint operator `T` on a
finite-dimensional complex inner product space, `re tr(T ^ k) = ∑ᵢ λᵢ ^ k`, the sum of the
`k`-th powers of `T`'s eigenvalues (the `g = id` specialization of `re_trace_cfc_pow_eq_sum`; the
`k = 2` case is `ContinuousLinearMap.IsDensityOp.re_trace_mul_self_eq_sum_eigenvalues_sq`). -/
theorem IsSelfAdjoint.re_trace_pow_eq_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E] {T : E →L[ℂ] E} {n : ℕ}
    (hT : IsSelfAdjoint T) (hn : finrank ℂ E = n) (k : ℕ) :
    RCLike.re (LinearMap.trace ℂ E ((T ^ k : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = ∑ i, (hT.isSymmetric.eigenvalues hn i) ^ k := by
  have h := hT.re_trace_cfc_pow_eq_sum hn id continuousOn_id k
  rw [cfc_id ℝ T] at h
  simpa only [id_eq] using h

/-- **Mixing a probability vector toward the uniform distribution does not increase `∑ pᵢ ^ k`.**
For a probability vector `lam : Fin n → ℝ` (`lamᵢ ≥ 0`, `∑ lamᵢ = 1`), `0 ≤ p ≤ 1` and `k ≥ 1`,
`∑ᵢ ((1 - p)·lamᵢ + p/n) ^ k ≤ ∑ᵢ lamᵢ ^ k`. Each term is bounded via convexity of `x ↦ x ^ k`
(`convexOn_pow`), and `n·(1/n) ^ k = 1/n ^ (k-1) ≤ ∑ lamᵢ ^ k` by the power-mean inequality
`pow_sum_div_card_le_sum_pow`. -/
theorem sum_mix_uniform_pow_le {n : ℕ} (lam : Fin n → ℝ) (hlam0 : ∀ i, 0 ≤ lam i)
    (hlam1 : ∑ i, lam i = 1) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    ∑ i, ((1 - p) * lam i + p / (n : ℝ)) ^ k ≤ ∑ i, (lam i) ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hlam1
    · exact_mod_cast h
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hconv := convexOn_pow (𝕜 := ℝ) (m + 1)
  have hterm : ∀ i, ((1 - p) * lam i + p / (n : ℝ)) ^ (m + 1)
      ≤ (1 - p) * (lam i) ^ (m + 1) + p * (1 / (n : ℝ)) ^ (m + 1) := by
    intro i
    have h := hconv.2 (Set.mem_Ici.mpr (hlam0 i))
      (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ)))
      (by linarith : (0 : ℝ) ≤ 1 - p) hp0 (by ring : (1 - p) + p = 1)
    simp only [smul_eq_mul] at h
    rwa [mul_one_div] at h
  have hjensen : (1 : ℝ) / (n : ℝ) ^ m ≤ ∑ i, (lam i) ^ (m + 1) := by
    have hpm := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin n)))
      (f := lam) (fun i _ => hlam0 i) m
    rw [hlam1] at hpm
    simpa [Finset.card_univ, Fintype.card_fin, one_pow] using hpm
  calc ∑ i, ((1 - p) * lam i + p / (n : ℝ)) ^ (m + 1)
      ≤ ∑ i, ((1 - p) * (lam i) ^ (m + 1) + p * (1 / (n : ℝ)) ^ (m + 1)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (1 - p) * (∑ i, (lam i) ^ (m + 1)) + (n : ℝ) * (p * (1 / (n : ℝ)) ^ (m + 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (1 - p) * (∑ i, (lam i) ^ (m + 1)) + p * (∑ i, (lam i) ^ (m + 1)) := by
        have key : (n : ℝ) * (p * (1 / (n : ℝ)) ^ (m + 1)) = p * (1 / (n : ℝ) ^ m) := by
          rw [div_pow, one_pow, pow_succ]; field_simp
        rw [key]
        have := mul_le_mul_of_nonneg_left hjensen hp0
        linarith
    _ = ∑ i, (lam i) ^ (m + 1) := by ring

namespace ContinuousLinearMap.IsDensityOp

/-- **The depolarizing channel does not increase `tr(ρ ^ k)`** (operator form; Nielsen & Chuang,
Exercise 8.18). For a density operator `ρ` on a finite-dimensional complex inner product space of
dimension `d = finrank ℂ E`, `0 ≤ p ≤ 1` and `k ≥ 1`,
`re tr(((p) • (d⁻¹ • 1) + (1 - p) • ρ) ^ k) ≤ re tr(ρ ^ k)`.
The mixed operator equals `cfc g ρ` for the affine `g x = (1 - p)·x + p/d`, so both traces are sums
over `ρ`'s eigenvalues (`IsSelfAdjoint.re_trace_cfc_pow_eq_sum`), and the claim reduces to the real
inequality `sum_mix_uniform_pow_le` applied to `ρ`'s eigenvalues (a probability vector by
`eigenvalues_nonneg` and `eigenvalues_sum_eq_one`). -/
theorem re_trace_depolarize_pow_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E] {ρ : E →L[ℂ] E} (hρ : ρ.IsDensityOp) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    RCLike.re (LinearMap.trace ℂ E ((((p : ℂ) • ((finrank ℂ E : ℂ)⁻¹ • 1)
        + ((1 - p : ℝ) : ℂ) • ρ) ^ k : E →L[ℂ] E) : E →ₗ[ℂ] E))
      ≤ RCLike.re (LinearMap.trace ℂ E ((ρ ^ k : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  have hsa : IsSelfAdjoint ρ := hρ.isPositive.isSelfAdjoint
  have hgcont : ContinuousOn (fun x => (1 - p) * x + p / (finrank ℂ E : ℝ)) (spectrum ℝ ρ) := by
    fun_prop
  have haff : cfc (fun x => (1 - p) * x + p / (finrank ℂ E : ℝ)) ρ
      = ((p : ℂ) • ((finrank ℂ E : ℂ)⁻¹ • 1) + ((1 - p : ℝ) : ℂ) • ρ : E →L[ℂ] E) := by
    rw [cfc_add ρ (fun x => (1 - p) * x) (fun _ => p / (finrank ℂ E : ℝ)),
      cfc_const_mul (1 - p) (fun x => x) ρ, cfc_id' ℝ ρ,
      cfc_const (p / (finrank ℂ E : ℝ)) ρ, Algebra.algebraMap_eq_smul_one,
      ← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module
  rw [← haff, hsa.re_trace_cfc_pow_eq_sum rfl _ hgcont k, hsa.re_trace_pow_eq_sum rfl k]
  exact sum_mix_uniform_pow_le (fun i => hsa.isSymmetric.eigenvalues rfl i)
    (fun i => hρ.eigenvalues_nonneg rfl i) (hρ.eigenvalues_sum_eq_one rfl) hp0 hp1 hk

end ContinuousLinearMap.IsDensityOp
