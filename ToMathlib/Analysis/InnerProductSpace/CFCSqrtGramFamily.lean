/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFCSqrtGramTrace
public import ToMathlib.Analysis.InnerProductSpace.OperatorSumChoiKraus
public import ToMathlib.Analysis.InnerProductSpace.Trace

/-!
# The codeword-family form of the pretty-good-measurement error estimate

Nielsen & Chuang's Box 12.5 "calculating the spurs" step (eqs. (12.92)–(12.94)) evaluates the
right-hand side of the trace form of the square-root operator inequality at the concrete
apparatus of the achievability proof: the (typical-subspace–compressed) codeword eigenvectors
`|Ẽ_c⟩` assembled columnwise into an operator `V = synthesisMap ψ`, with **total operator**
`S = V ∘ V⋆ = ∑ c, |ψ_c⟩⟨ψ_c|` and **Gram operator** `Γ = V⋆ ∘ V` (entries `⟪ψ_c, ψ_{c'}⟫`),
and the diagonal weight `Λ = ∑ c, λ_c |e_c⟩⟨e_c|` of the eigenvalues `λ_c`.

Feeding this instantiation into the abstract Gram-trace bound
`ContinuousLinearMap.two_mul_re_trace_one_sub_cfc_sqrt_gram_le` (N&C eq. (12.94)) turns each of the
three physical traces into a concrete sum over the family `ψ`, giving the decoding-deficit bound in
Nielsen & Chuang's own "sum over codewords" form:

`2·∑_c λ_c (1 − re⟪e_c, √Γ e_c⟫)  ≤  2·∑_c λ_c − 3·∑_c λ_c‖ψ_c‖² + ∑_c ∑_{c'} λ_c |⟪ψ_c, ψ_{c'}⟫|²`,

where `√Γ = cfc Real.sqrt Γ` and `α_c = re⟪e_c, √Γ e_c⟫` is exactly Nielsen & Chuang's diagonal
decoding overlap `α_{(M,K),(M,K)}` (Box 12.5, `Γ^{1/2} = [α]`).  This is the achievability half of
the **Holevo–Schumacher–Westmoreland theorem** (`χ(E) = C⁽¹⁾(E)`, N&C Theorem 12.8): once `ψ` is the
codeword-eigenvector family and `λ` the eigenvalues, the left side is the `2·∑ λ(1−α)` term of
eq. (12.88) and the three right-hand sums are the physical error terms `tr(σ_M(I−P))`,
`tr(P σ_M P P_{M'})`, `tr(σ_M(I−P_M))` of the random-coding error estimate (12.79).

## What this file provides

* `InnerProductSpace.trace_sum_smul_rankOne_self` /
  `InnerProductSpace.trace_comp_sum_smul_rankOne_self` — the reusable trace-evaluation core:
  `tr(∑_c c_c |v_c⟩⟨v_c|) = ∑_c c_c ⟪v_c, v_c⟫` and, against a further operator `A`,
  `tr(A · ∑_c c_c |v_c⟩⟨v_c|) = ∑_c c_c ⟪v_c, A v_c⟫`.
* `InnerProductSpace.synthesisMap_comp_diagWeight_comp_adjoint` — the conjugation identity
  `V · (∑_c c_c |e_c⟩⟨e_c|) · V⋆ = ∑_c c_c |ψ_c⟩⟨ψ_c|`: the synthesis operator carries the
  coordinate-space diagonal weight to the eigenvalue-weighted frame operator on the ambient space.
* `InnerProductSpace.two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le` — the **headline** codeword-sum
  bound (N&C eq. (12.94)), the abstract Gram-trace inequality with all three spurs evaluated as
  concrete sums over the family `ψ` and the diagonal eigenvalue weight `λ`.

The abstract Gram-trace bound used here is in
`ToMathlib.Analysis.InnerProductSpace.CFCSqrtGramTrace`.
-/

@[expose] public section

open scoped InnerProductSpace

open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace InnerProductSpace

section Trace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- **Trace of an operator against a weighted family of rank-one self-projectors.**  For an operator
`A : E →L[𝕜] E`, a family `v : ι → E`, scalar weights `c : ι → 𝕜`, and a finite index set
`s : Finset ι`,

`tr(A · ∑_{i ∈ s} c_i |v_i⟩⟨v_i|) = ∑_{i ∈ s} c_i ⟪v_i, A v_i⟫`.

Distributing the composition over the sum and each scalar, `A · |v_i⟩⟨v_i| = |A v_i⟩⟨v_i|`
(`comp_rankOne`) and `tr(|A v_i⟩⟨v_i|) = ⟪v_i, A v_i⟫` (`trace_rankOne`).  Stated over an arbitrary
`Finset` (the whole-`Fintype` case is `s = Finset.univ`), so it evaluates traces against partial
rank-one sums such as an eigenbasis restricted to a typical index set. -/
theorem trace_comp_sum_smul_rankOne_self (A : E →L[𝕜] E) (v : ι → E) (c : ι → 𝕜) (s : Finset ι) :
    LinearMap.trace 𝕜 E
        ((A.comp (∑ i ∈ s, c i • rankOne 𝕜 (v i) (v i)) : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = ∑ i ∈ s, c i * inner 𝕜 (v i) (A (v i)) := by
  rw [ContinuousLinearMap.comp_finsetSum]
  simp_rw [ContinuousLinearMap.comp_smul, comp_rankOne]
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
  simp_rw [ContinuousLinearMap.toLinearMap_smul, map_smul, trace_rankOne, smul_eq_mul]

/-- **Trace of a weighted family of rank-one self-projectors.**  For a family `v : ι → E` and
scalar weights `c : ι → 𝕜`,

`tr(∑_i c_i |v_i⟩⟨v_i|) = ∑_i c_i ⟪v_i, v_i⟫`.

The `A = 1` case of `trace_comp_sum_smul_rankOne_self`. -/
theorem trace_sum_smul_rankOne_self (v : ι → E) (c : ι → 𝕜) :
    LinearMap.trace 𝕜 E ((∑ i, c i • rankOne 𝕜 (v i) (v i) : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = ∑ i, c i * inner 𝕜 (v i) (v i) := by
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
  simp_rw [ContinuousLinearMap.toLinearMap_smul, map_smul, trace_rankOne, smul_eq_mul]

end Trace

section Family

variable {ι : Type*} [Fintype ι] {G : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

omit [FiniteDimensional ℂ G] in
/-- **The synthesis operator carries the coordinate diagonal weight to the family frame weight.**
For a family `ψ : ι → G` with synthesis operator `V = synthesisMap ψ` and scalar weights
`c : ι → ℂ`,

`V · (∑_i c_i |e_i⟩⟨e_i|) · V⋆ = ∑_i c_i |ψ_i⟩⟨ψ_i|`,

where `e_i` are the standard basis vectors of `EuclideanSpace ℂ ι`.  Termwise
`V · |e_i⟩⟨e_i| · V⋆ = |V e_i⟩⟨V e_i| = |ψ_i⟩⟨ψ_i|` (`comp_rankOne_self_comp_adjoint`,
`synthesisMap_basisFun`). -/
theorem synthesisMap_comp_diagWeight_comp_adjoint (ψ : ι → G) (c : ι → ℂ) :
    (synthesisMap ψ).comp
        ((∑ i, c i • rankOne ℂ (EuclideanSpace.basisFun ι ℂ i) (EuclideanSpace.basisFun ι ℂ i)).comp
          (adjoint (synthesisMap ψ)))
      = ∑ i, c i • rankOne ℂ (ψ i) (ψ i) := by
  rw [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    comp_rankOne_self_comp_adjoint]
  simp only [synthesisMap_basisFun]

/-- **The codeword-family form of the pretty-good-measurement error estimate**
(Nielsen & Chuang, Box 12.5, eq. (12.94)).  For a finite family `ψ : ι → G` with synthesis operator
`V = synthesisMap ψ`, Gram operator `Γ = V⋆ · V`, and nonnegative real weights `λ : ι → ℝ`,

`2 · ∑_i λ_i (1 − re⟪e_i, √Γ e_i⟫)  ≤  2·∑_i λ_i  −  3·∑_i λ_i‖ψ_i‖²  +  ∑_i ∑_j λ_i |⟪ψ_i, ψ_j⟫|²`,

where `e_i` are the standard basis vectors of `EuclideanSpace ℂ ι` and `√Γ = cfc Real.sqrt Γ`.  The
diagonal `α_i = re⟪e_i, √Γ e_i⟫` is Nielsen & Chuang's decoding overlap `α_{(M,K),(M,K)}`
(Box 12.5, `Γ^{1/2} = [α]`).

This is the abstract Gram-trace bound
`ContinuousLinearMap.two_mul_re_trace_one_sub_cfc_sqrt_gram_le` at `V = synthesisMap ψ` and the
diagonal eigenvalue weight `Λ = ∑_i λ_i |e_i⟩⟨e_i|`, with each of its three physical traces
`tr Λ`, `tr(V Λ V⋆)`, `tr(S · V Λ V⋆)` evaluated into concrete sums over `ψ` and `λ`
(`trace_sum_smul_rankOne_self`, `trace_comp_sum_smul_rankOne_self`,
`synthesisMap_comp_diagWeight_comp_adjoint`, `sum_rankOne_self_eq_synthesisMap_comp_adjoint`).  Once
`ψ` is the codeword-eigenvector family and `λ` the eigenvalues, the left side is the `2·∑ λ(1−α)`
term of N&C eq. (12.88) and the three right-hand sums are the error terms of the random-coding
estimate (12.79). -/
theorem two_mul_sum_one_sub_re_inner_cfc_sqrt_gram_le (ψ : ι → G) (lam : ι → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) :
    2 * ∑ i, lam i * (1 - RCLike.re (inner ℂ (EuclideanSpace.basisFun ι ℂ i)
        ((cfc Real.sqrt ((adjoint (synthesisMap ψ)).comp (synthesisMap ψ)))
          (EuclideanSpace.basisFun ι ℂ i))))
      ≤ 2 * ∑ i, lam i
        - 3 * ∑ i, lam i * ‖ψ i‖ ^ 2
        + ∑ i, ∑ j, lam i * ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 := by
  classical
  set Λ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
    ∑ i, (lam i : ℂ) • rankOne ℂ (EuclideanSpace.basisFun ι ℂ i) (EuclideanSpace.basisFun ι ℂ i)
    with hΛdef
  -- `⟪e_i, e_i⟫ = 1` for the standard basis vectors.
  have hbb : ∀ i, (inner ℂ (EuclideanSpace.basisFun ι ℂ i)
      (EuclideanSpace.basisFun ι ℂ i) : ℂ) = 1 := fun i => by
    rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      ite_eq_left rfl]
  -- The diagonal weight is positive.
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    refine Finset.sum_nonneg fun i _ => ?_
    exact nonneg_iff_isPositive.mpr
      ((isPositive_rankOne_self (EuclideanSpace.basisFun ι ℂ i)).smul_of_nonneg
        (by exact_mod_cast hlam i))
  have h := ContinuousLinearMap.two_mul_re_trace_one_sub_cfc_sqrt_gram_le (synthesisMap ψ) hΛ
  -- Evaluate `tr Λ = ∑ λ_i`.
  have htrΛ : LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (Λ : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
      = ∑ i, (lam i : ℂ) := by
    rw [hΛdef, trace_sum_smul_rankOne_self]
    exact Finset.sum_congr rfl fun i _ => by rw [hbb i, mul_one]
  -- Evaluate `tr(V Λ V⋆) = ∑ λ_i ‖ψ_i‖²`.
  have htrT : LinearMap.trace ℂ G
        ((( synthesisMap ψ).comp (Λ.comp (adjoint (synthesisMap ψ))) : G →L[ℂ] G) : G →ₗ[ℂ] G)
      = ∑ i, (lam i : ℂ) * (‖ψ i‖ ^ 2 : ℝ) := by
    rw [hΛdef, synthesisMap_comp_diagWeight_comp_adjoint, trace_sum_smul_rankOne_self]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K]; simp
  -- Evaluate `tr(S · V Λ V⋆) = ∑_i ∑_j λ_i |⟪ψ_i, ψ_j⟫|²`.
  have htrS : LinearMap.trace ℂ G
        ((((synthesisMap ψ).comp (adjoint (synthesisMap ψ))).comp
            ((synthesisMap ψ).comp (Λ.comp (adjoint (synthesisMap ψ)))) : G →L[ℂ] G) : G →ₗ[ℂ] G)
      = ∑ i, ∑ j, (lam i : ℂ) * (‖inner ℂ (ψ i) (ψ j)‖ ^ 2 : ℝ) := by
    rw [hΛdef, synthesisMap_comp_diagWeight_comp_adjoint, trace_comp_sum_smul_rankOne_self]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_rankOne_self_eq_synthesisMap_comp_adjoint, _root_.sum_apply, inner_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rankOne_apply, inner_smul_right, ← inner_conj_symm (ψ j) (ψ i), RCLike.conj_mul]; simp
  -- Evaluate `re tr((1 - √Γ) Λ) = ∑ λ_i (1 - re⟪e_i, √Γ e_i⟫)`.
  have htrLHS : RCLike.re (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
        (((1 - cfc Real.sqrt ((adjoint (synthesisMap ψ)).comp (synthesisMap ψ))) * Λ :
            EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
              EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι))
      = ∑ i, lam i * (1 - RCLike.re (inner ℂ (EuclideanSpace.basisFun ι ℂ i)
          ((cfc Real.sqrt ((adjoint (synthesisMap ψ)).comp (synthesisMap ψ)))
            (EuclideanSpace.basisFun ι ℂ i)))) := by
    rw [ContinuousLinearMap.mul_def, hΛdef, trace_comp_sum_smul_rankOne_self, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.sub_apply, one_apply_eq_self, inner_sub_right, hbb i]
    simp [mul_sub]
  -- Real parts of the codeword sums.
  have hre1 : RCLike.re (∑ i, (lam i : ℂ)) = ∑ i, lam i := by
    rw [map_sum]; exact Finset.sum_congr rfl fun x _ => RCLike.ofReal_re _
  have hre2 : RCLike.re (∑ i, (lam i : ℂ) * (‖ψ i‖ ^ 2 : ℝ)) = ∑ i, lam i * ‖ψ i‖ ^ 2 := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [← Complex.ofReal_mul]; exact RCLike.ofReal_re _
  have hre3 : RCLike.re (∑ i, ∑ j, (lam i : ℂ) * (‖inner ℂ (ψ i) (ψ j)‖ ^ 2 : ℝ))
      = ∑ i, ∑ j, lam i * ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [← Complex.ofReal_mul]; exact RCLike.ofReal_re _
  rw [htrΛ, htrT, htrS, hre1, hre2, hre3, htrLHS] at h
  exact h

end Family

end InnerProductSpace
