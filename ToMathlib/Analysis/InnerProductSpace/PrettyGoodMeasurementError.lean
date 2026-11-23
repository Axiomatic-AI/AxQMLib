/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFCSqrtGramFamily

/-!
# The decoder-error reduction of the pretty-good measurement (N&C Box 12.5, eqs. (12.86)→(12.88))

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, achievability), the average error of the pretty-good (square-root) decoder is
reduced, message by message, to a sum over the codeword's diagonal *decoding overlaps* before the
"calculating the spurs" step evaluates those overlaps as physical traces.  Concretely (Box 12.5,
eqs. (12.84)–(12.88)), for the true message `M` with codeword `σ_M = ∑_κ λ^M_κ |E^M_κ⟩⟨E^M_κ|` and
pretty-good effect `E_M = S⁻¹ᐟ² · (∑_{κ∈T_M} |Ẽ^M_κ⟩⟨Ẽ^M_κ|) · S⁻¹ᐟ²`
(`Ẽ^M_κ = P|E^M_κ⟩`, `S = ∑_{M',κ'∈T_{M'}} |Ẽ^{M'}_{κ'}⟩⟨Ẽ^{M'}_{κ'}|`), the deficit is

`1 − tr(σ_M E_M)
   = 1 − ∑_κ ∑_{κ'∈T_M} λ^M_κ |α_{(M,κ),(M,κ')}|²`   (eq. (12.86))
`  ≤ 2·∑_{κ∈T_M} λ^M_κ (1 − α_{(M,κ),(M,κ)}) + ∑_{κ∉T_M} λ^M_κ`   (eq. (12.88)),

where `α_{(M,κ),(M,κ')} = ⟨Ẽ^M_κ, S⁻¹ᐟ² Ẽ^M_{κ'}⟩` is the decoding overlap (the entries of `√Γ`,
`Γ = V⋆·V` the Gram operator).

This file provides that reduction in **operator form**, decoupled from the physical
apparatus: the codeword eigenbasis is an arbitrary spectral family `φ`, the compressed frame vectors
an arbitrary family `ψ`, the generalized inverse square root an arbitrary self-adjoint operator `T`,
and the typical set an arbitrary `Finset`.  The instantiation `T = S⁻¹ᐟ²`, `φ = ` codeword
eigenbasis, `ψ = P ∘ φ`, `T_M = ` conditional typical set (which identifies the overlap
`re⟨ψ_κ, T φ_κ⟩` with the `√Γ` diagonal `re⟨e_κ, √Γ e_κ⟩` of `two_mul_sum_one_sub_re_inner_cfc_sqrt`
`_gram_le` via `P`-absorption) is carried out in
`AxQM/Postulates/API/CondTypicalSubspaceDecoder.lean`.

## Main result

* `InnerProductSpace.one_sub_re_trace_selfAdjoint_conj_frame_le` — for a self-adjoint `T`, a
  spectral family `φ` with nonnegative weights `λ` summing to `1`, a frame family `ψ`, and a
  typical `Finset J`,

  `1 − re tr((∑_k λ_k |φ_k⟩⟨φ_k|) · T · (∑_{j∈J} |ψ_j⟩⟨ψ_j|) · T)
     ≤ 2·∑_{k∈J} λ_k (1 − re⟨ψ_k, T φ_k⟩) + ∑_{k∉J} λ_k`.

## Proof

Writing `α_k = re⟨ψ_k, T φ_k⟩` (the decoding overlap) and `β_k = ∑_{j∈J} ‖⟨ψ_j, T φ_k⟩‖²` (the
per-eigenvector kept overlap mass), the trace evaluates to `∑_k λ_k β_k`: trace cyclicity
(`LinearMap.trace_mul_comm`) plus `trace_comp_sum_smul_rankOne_self` turn it into
`∑_k λ_k ⟨φ_k, T (∑_{j∈J}|ψ_j⟩⟨ψ_j|) T φ_k⟩`, and self-adjointness of `T`
(`adjoint_inner_left`) with the frame expansion gives `⟨φ_k, T B T φ_k⟩ = β_k`.  Since
`∑_k λ_k = 1`, the deficit is `∑_k λ_k (1 − β_k)`.  Splitting `univ = J ∪ Jᶜ`: for `k ∈ Jᶜ` the
diagonal drops non-positively, `1 − β_k ≤ 1` (`0 ≤ β_k`); for `k ∈ J` the diagonal `j = k` term
gives `β_k ≥ α_k²`, whence `1 − β_k ≤ 1 − α_k² ≤ 2(1 − α_k)` (the last step is `0 ≤ (α_k − 1)²`, so
**no** bound on `α_k` is needed — N&C's `0 ≤ α ≤ 1` from the diagonal Cauchy–Schwarz estimate is not
required for the reduction itself).

The statement involves only `rankOne`, `LinearMap.trace`, `ContinuousLinearMap.adjoint` (via
`IsSelfAdjoint`), `inner`, and `Finset.sum`. Its trace-side companion is
`two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le` (`CFCSqrtGramFamily`), which bounds the
`2·∑ λ(1−α)` term it produces.
-/

@[expose] public section

open scoped InnerProductSpace

open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The decoder-error reduction of the pretty-good measurement** (Nielsen & Chuang, Theorem 12.8,
Box 12.5, eqs. (12.86)→(12.88)).  For a self-adjoint operator `T` (the generalized inverse square
root `S⁻¹ᐟ²`), a spectral family `φ` (the codeword eigenbasis) with nonnegative weights `λ` summing
to `1` (the eigenvalue distribution), a frame family `ψ` (the compressed typical eigenvectors
`Ẽ = P E`), and a typical index set `J` (the conditional typical set `T_M`), the deficit of the
square-root ("pretty-good") decoding overlap satisfies

`1 − re tr((∑_k λ_k |φ_k⟩⟨φ_k|) · T · (∑_{j∈J} |ψ_j⟩⟨ψ_j|) · T)
   ≤ 2·∑_{k∈J} λ_k (1 − re⟨ψ_k, T φ_k⟩) + ∑_{k∉J} λ_k`,

where the operator `T · (∑_{j∈J} |ψ_j⟩⟨ψ_j|) · T = S⁻¹ᐟ² · (∑_{κ∈T_M} |Ẽ_κ⟩⟨Ẽ_κ|) · S⁻¹ᐟ²` is the
pretty-good decoder effect for the true message, and `α_k = re⟨ψ_k, T φ_k⟩` is Nielsen & Chuang's
diagonal decoding overlap `α_{(M,κ),(M,κ)}`.

The trace evaluates to `∑_k λ_k β_k` with `β_k = ∑_{j∈J} ‖⟨ψ_j, T φ_k⟩‖²` (trace cyclicity
`LinearMap.trace_mul_comm`, `trace_comp_sum_smul_rankOne_self`, self-adjointness of `T`, and the
frame expansion), so the deficit is `∑_k λ_k (1 − β_k)`; on the typical set `β_k ≥ α_k²` (its
`j = k` diagonal term) gives `1 − β_k ≤ 1 − α_k² ≤ 2(1 − α_k)` via `0 ≤ (α_k − 1)²`, and off it
`1 − β_k ≤ 1` via `0 ≤ β_k`.  No bound on `α_k` is needed for the reduction. -/
theorem one_sub_re_trace_selfAdjoint_conj_frame_le
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (φ ψ : κ → E) (lam : κ → ℝ) (J : Finset κ)
    (hlam : ∀ k, 0 ≤ lam k) (hsum : ∑ k, lam k = 1) :
    1 - RCLike.re (LinearMap.trace ℂ E
        (((∑ k, (lam k : ℂ) • rankOne ℂ (φ k) (φ k)).comp
          (T.comp ((∑ j ∈ J, rankOne ℂ (ψ j) (ψ j)).comp T))) : E →ₗ[ℂ] E))
      ≤ 2 * ∑ k ∈ J, lam k * (1 - RCLike.re (inner ℂ (ψ k) (T (φ k)))) + ∑ k ∈ Jᶜ, lam k := by
  classical
  set B : E →L[ℂ] E := ∑ j ∈ J, rankOne ℂ (ψ j) (ψ j) with hBdef
  set α : κ → ℝ := fun k => RCLike.re (inner ℂ (ψ k) (T (φ k))) with hαdef
  set β : κ → ℝ := fun k => ∑ j ∈ J, ‖inner ℂ (ψ j) (T (φ k))‖ ^ 2 with hβdef
  have hadj : ContinuousLinearMap.adjoint T = T := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hT
  -- The eigenvector-diagonal identity `⟨φ_k, T B T φ_k⟩ = β_k`.
  have hkey : ∀ k, inner ℂ (φ k) ((T.comp (B.comp T)) (φ k)) = ((β k : ℝ) : ℂ) := by
    intro k
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left T (B (T (φ k))) (φ k), hadj, hBdef, hβdef,
      _root_.sum_apply, inner_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rankOne_apply, inner_smul_right, ← inner_conj_symm (T (φ k)) (ψ j), RCLike.mul_conj]
    norm_cast
  -- The decoding overlap trace is `∑_k λ_k β_k`.
  have htr : RCLike.re (LinearMap.trace ℂ E
        (((∑ k, (lam k : ℂ) • rankOne ℂ (φ k) (φ k)).comp (T.comp (B.comp T))) : E →ₗ[ℂ] E))
      = ∑ k, lam k * β k := by
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
      ← ContinuousLinearMap.toLinearMap_comp, trace_comp_sum_smul_rankOne_self]
    simp_rw [hkey, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    exact Complex.ofReal_re _
  rw [htr]
  have hβnn : ∀ k, 0 ≤ β k := fun k => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- On the typical set, the diagonal `j = k` term forces `β_k ≥ α_k²`.
  have hdiag : ∀ k ∈ J, α k ^ 2 ≤ β k := by
    intro k hk
    have hle : α k ^ 2 ≤ ‖inner ℂ (ψ k) (T (φ k))‖ ^ 2 := by
      rw [hαdef, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (RCLike.abs_re_le_norm _) 2
    exact hle.trans (Finset.single_le_sum
      (f := fun j => ‖inner ℂ (ψ j) (T (φ k))‖ ^ 2) (fun j _ => sq_nonneg _) hk)
  have hrw : ∑ k, lam k * (1 - β k) = 1 - ∑ k, lam k * β k := by
    simp_rw [mul_one_sub]; rw [Finset.sum_sub_distrib, hsum]
  rw [← hrw, ← Finset.sum_add_sum_compl J]
  gcongr ?_ + ?_
  · -- typical block: `λ_k (1 − β_k) ≤ 2 λ_k (1 − α_k)` since `1 − α² ≤ 2(1 − α)`.
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have h1 : 1 - β k ≤ 2 * (1 - α k) := by nlinarith [hdiag k hk, sq_nonneg (α k - 1)]
    calc lam k * (1 - β k) ≤ lam k * (2 * (1 - α k)) :=
          mul_le_mul_of_nonneg_left h1 (hlam k)
      _ = 2 * (lam k * (1 - α k)) := by ring
  · -- atypical block: `λ_k (1 − β_k) ≤ λ_k` since `0 ≤ β_k`.
    refine Finset.sum_le_sum fun k _ => ?_
    have h2 : (1 : ℝ) - β k ≤ 1 := by linarith [hβnn k]
    calc lam k * (1 - β k) ≤ lam k * 1 := mul_le_mul_of_nonneg_left h2 (hlam k)
      _ = lam k := mul_one _

end InnerProductSpace
