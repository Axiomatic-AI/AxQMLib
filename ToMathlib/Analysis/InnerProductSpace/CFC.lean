/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import ToMathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import ToMathlib.Analysis.InnerProductSpace.Trace

/-!
# Closed-form continuous functional calculus on a finite-dimensional inner product space

For a self-adjoint continuous linear operator `T : E →L[ℂ] E` on a finite-dimensional complex
inner product space, the continuous functional calculus has a closed-form expansion in terms
of the rank-one operators along the orthonormal eigenbasis of `T`:

`cfc f T = ∑ i, (f (λᵢ) : ℂ) • rankOne ℂ eᵢ eᵢ`

where `λᵢ` and `eᵢ` are the (real) eigenvalues and orthonormal eigenvectors of `T`.

The proof proceeds by extensionality: we show both sides agree on each eigenvector `eⱼ`. For the
right-hand side, orthonormality collapses the sum to a single term `f(λⱼ) • eⱼ`. For the
left-hand side, `cfc_apply_of_polynomial` plus density (via the closed embedding of `cfcHom`)
gives the same result.

## Main results

- `IsSelfAdjoint.eigenvalues_mem_spectrum_real`: eigenvalues are in the real spectrum (⊇).
- `IsSelfAdjoint.spectrum_real_eq_range_eigenvalues`: real spectrum = range of eigenvalues
  (CLM-level analog of `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`).
- `IsSelfAdjoint.zero_notMem_spectrum_real_of_eigenvalues_pos`: corollary used to discharge
  continuity premises like `ContinuousOn Real.log (spectrum ℝ T)` from positivity assumptions
  on the eigenvalues.
- `IsSelfAdjoint.cfc_eq_sum_rankOne`: `cfc f T = ∑ i, (f λᵢ : ℂ) • rankOne ℂ eᵢ eᵢ`.
- `IsSelfAdjoint.cfc_sqrt_eq_sum_rankOne`, `cfc_exp_eq_sum_rankOne`,
  `cfc_log_eq_sum_rankOne`: closed forms for `Real.sqrt`, `Real.exp`, and
  (for `T` whose spectrum avoids `0`) `Real.log`.
- `IsSelfAdjoint.cfc_inner_self_eq_sum`: quadratic-form expansion
  `⟨x, cfc f T x⟩ = ∑ i, f(λᵢ) * ‖⟨eᵢ, x⟩‖²`.
- `IsSelfAdjoint.trace_comp_cfc_eq_double_sum`: trace double-sum expansion
  `tr((cfc f U) ∘ T) = ∑ᵢ λᵢ * ∑ⱼ f(μⱼ) * ‖⟨fⱼ, eᵢ⟩‖²` for symmetric `T, U`. Foundational
  for operator Klein's inequality (Nielsen–Chuang Theorem 11.7).
-/

@[expose] public section

open InnerProductSpace ContinuousFunctionalCalculus Module.End

namespace IsSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] {T : E →L[ℂ] E} {n : ℕ}

/-- The eigenvalues of a self-adjoint operator are in its real spectrum. -/
theorem eigenvalues_mem_spectrum_real (hT : IsSelfAdjoint T) (hn : Module.finrank ℂ E = n)
    (i : Fin n) : (hT.isSymmetric.eigenvalues hn i : ℝ) ∈ spectrum ℝ T := by
  rw [← IsSelfAdjoint.coe_mem_spectrum_complex hT, ContinuousLinearMap.spectrum_eq]
  exact (hT.isSymmetric.hasEigenvalue_eigenvalues hn i).mem_spectrum

/-- The real spectrum of a self-adjoint operator on a finite-dimensional inner product space
equals the range of its eigenvalue function. CLM-level analog of
`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`; the `⊇` direction is
`eigenvalues_mem_spectrum_real`, the `⊆` direction uses `IsSelfAdjoint.coe_mem_spectrum_complex`
to lift to the ℂ-spectrum + `Module.End.HasEigenvalue.of_mem_spectrum` to extract an
eigenvalue + `LinearMap.IsSymmetric.exists_eigenvalues_eq` to identify the index. -/
theorem spectrum_real_eq_range_eigenvalues (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℂ E = n) :
    spectrum ℝ T = Set.range (hT.isSymmetric.eigenvalues hn) := by
  refine Set.Subset.antisymm (fun μ hμ ↦ ?_) ?_
  · have hμℂ : (μ : ℂ) ∈ spectrum ℂ T := (IsSelfAdjoint.coe_mem_spectrum_complex hT).mpr hμ
    rw [ContinuousLinearMap.spectrum_eq] at hμℂ
    obtain ⟨i, hi⟩ := hT.isSymmetric.exists_eigenvalues_eq hn
      (Module.End.HasEigenvalue.of_mem_spectrum hμℂ)
    exact ⟨i, Complex.ofReal_inj.mp hi⟩
  · rintro _ ⟨i, rfl⟩
    exact hT.eigenvalues_mem_spectrum_real hn i

/-- For a self-adjoint operator on a finite-dimensional inner product space whose eigenvalues
are all strictly positive, zero is not in the real spectrum. Corollary of
`spectrum_real_eq_range_eigenvalues`; foundational for establishing continuity premises like
`ContinuousOn Real.log (spectrum ℝ T)` (since `Real.log` is continuous on `{0}ᶜ`). -/
theorem zero_notMem_spectrum_real_of_eigenvalues_pos (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℂ E = n) (h_pos : ∀ i, 0 < hT.isSymmetric.eigenvalues hn i) :
    (0 : ℝ) ∉ spectrum ℝ T := fun h ↦ by
  obtain ⟨i, hi⟩ := (hT.spectrum_real_eq_range_eigenvalues hn).symm ▸ h
  exact (h_pos i).ne' hi

/-- For a self-adjoint operator with strictly positive eigenvalues, `Real.log` is continuous on
its spectrum. Direct continuity composition with the absent-zero-spectrum bridge. -/
theorem continuousOn_log_spectrum_of_eigenvalues_pos (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℂ E = n) (h_pos : ∀ i, 0 < hT.isSymmetric.eigenvalues hn i) :
    ContinuousOn Real.log (spectrum ℝ T) :=
  Real.continuousOn_log.mono fun _ hx h ↦
    hT.zero_notMem_spectrum_real_of_eigenvalues_pos hn h_pos (h ▸ hx)

/-- **Any** real function is continuous on the spectrum of a self-adjoint operator on a
finite-dimensional inner product space: the real spectrum is the (finite) range of the eigenvalue
function (`spectrum_real_eq_range_eigenvalues`), hence discrete, so every function is continuous on
it. The discharge for the `cfc` continuity premise regardless of the function (`Real.log`,
`Set.indicator {0} 1`, …). -/
theorem continuousOn_spectrum (hT : IsSelfAdjoint T) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ T) := by
  rw [hT.spectrum_real_eq_range_eigenvalues rfl]
  exact (Set.finite_range _).continuousOn f

/-- **Any** real function is continuous on the *quasi*spectrum of a self-adjoint operator on a
finite-dimensional inner product space. The quasispectrum is `spectrum ∪ {0}`
(`quasispectrum_eq_spectrum_union_zero`), still a finite set, hence discrete. The discharge for the
`cfcₙ` (non-unital CFC) continuity premise — the non-unital analogue of `continuousOn_spectrum`. -/
theorem continuousOn_quasispectrum (hT : IsSelfAdjoint T) (f : ℝ → ℝ) :
    ContinuousOn f (quasispectrum ℝ T) := by
  rw [quasispectrum_eq_spectrum_union_zero ℝ T, hT.spectrum_real_eq_range_eigenvalues rfl]
  exact ((Set.finite_range _).union (Set.finite_singleton 0)).continuousOn f

/-- `Real.log` is continuous on the spectrum of **any** self-adjoint operator on a
finite-dimensional inner product space — no positivity needed. Specialization of
`continuousOn_spectrum`; `0` may lie in the spectrum, where `Real.log 0 = 0` is harmless. -/
theorem continuousOn_log_spectrum (hT : IsSelfAdjoint T) :
    ContinuousOn Real.log (spectrum ℝ T) :=
  hT.continuousOn_spectrum Real.log

/-- For a self-adjoint operator with strictly positive eigenvalues, the real power function
`· ^ y` is continuous on its spectrum for any exponent `y : ℝ`. Direct continuity composition
with the absent-zero-spectrum bridge. -/
theorem continuousOn_rpow_const_spectrum_of_eigenvalues_pos (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℂ E = n) (h_pos : ∀ i, 0 < hT.isSymmetric.eigenvalues hn i) (y : ℝ) :
    ContinuousOn (fun x : ℝ ↦ x ^ y) (spectrum ℝ T) :=
  fun x hx ↦ (Real.continuousAt_rpow_const x y <| Or.inl fun h ↦
    hT.zero_notMem_spectrum_real_of_eigenvalues_pos hn h_pos (h ▸ hx)).continuousWithinAt

/-- CLM-cast of `LinearMap.IsSymmetric.apply_eigenvectorBasis`: the action of a self-adjoint
operator on its eigenbasis vector with the ℝ → ℂ coercion applied to the eigenvalue. -/
theorem apply_eigenvectorBasis_cast (hT : IsSelfAdjoint T) (hn : Module.finrank ℂ E = n)
    (i : Fin n) :
    T (hT.isSymmetric.eigenvectorBasis hn i) =
      ((hT.isSymmetric.eigenvalues hn i : ℝ) : ℂ) • hT.isSymmetric.eigenvectorBasis hn i := by
  exact_mod_cast hT.isSymmetric.apply_eigenvectorBasis hn i

omit [FiniteDimensional ℂ E] in
/-- **Eigenvectors of a self-adjoint operator with nonzero overlap must have equal eigenvalues**:
the contrapositive of `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` in the per-vector
form. If `T x = μ • x` and `T e = λ • e` and `⟪e, x⟫ ≠ 0`, then `λ = μ`. -/
theorem eigenvalue_eq_of_inner_ne_zero (hT : IsSelfAdjoint T)
    {x e : E} {μ lam : ℝ} (hμ : T x = (μ : ℂ) • x) (hlam : T e = (lam : ℂ) • e)
    (h_inner : ⟪e, x⟫_ℂ ≠ 0) : lam = μ := by
  have h_eq : (μ : ℂ) * ⟪e, x⟫_ℂ = (lam : ℂ) * ⟪e, x⟫_ℂ := calc
    _ = ⟪e, T x⟫_ℂ := by rw [hμ, inner_smul_right]
    _ = ⟪T e, x⟫_ℂ := (hT.isSymmetric e x).symm
    _ = _ := by rw [hlam, inner_smul_left, Complex.conj_ofReal]
  exact_mod_cast (mul_right_cancel₀ h_inner h_eq).symm

section cfcAuxOp

variable (hT : IsSelfAdjoint T) (hn : Module.finrank ℂ E = n)

/-- Abbreviation for the rank-one projector along the `i`-th eigenvector. -/
noncomputable abbrev P (i : Fin n) : E →L[ℂ] E :=
  InnerProductSpace.rankOne ℂ (hT.isSymmetric.eigenvectorBasis hn i)
    (hT.isSymmetric.eigenvectorBasis hn i)

@[simp] private lemma P_apply (i : Fin n) :
    hT.P hn i = InnerProductSpace.rankOne ℂ (hT.isSymmetric.eigenvectorBasis hn i)
      (hT.isSymmetric.eigenvectorBasis hn i) := rfl

private lemma P_mul_P_of_ne {i j : Fin n} (hij : i ≠ j) : hT.P hn i * hT.P hn j = 0 := by
  simp only [P_apply, ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne,
    (hT.isSymmetric.eigenvectorBasis hn).orthonormal.2 hij, zero_smul]

private lemma P_mul_P_self (i : Fin n) : hT.P hn i * hT.P hn i = hT.P hn i := by
  simp only [P_apply, ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne,
    inner_self_eq_norm_sq_to_K, (hT.isSymmetric.eigenvectorBasis hn).orthonormal.1 i]
  norm_num

private lemma star_P (i : Fin n) : star (hT.P hn i) = hT.P hn i := by
  simp only [P_apply, ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]

private lemma sum_P_eq_one : ∑ i, hT.P hn i = 1 :=
  (hT.isSymmetric.eigenvectorBasis hn).sum_rankOne_eq_id

/-- The auxiliary star-algebra hom whose closed-form image is shown to equal `cfc f T`.
Sends `g : C(spectrum ℝ T, ℝ)` to the rank-one expansion
`∑ i, (g(λᵢ) : ℂ) • rankOne ℂ eᵢ eᵢ`. -/
noncomputable def cfcAuxOp : C(spectrum ℝ T, ℝ) →⋆ₐ[ℝ] (E →L[ℂ] E) where
  toFun g := ∑ i, (g ⟨hT.isSymmetric.eigenvalues hn i,
      IsSelfAdjoint.eigenvalues_mem_spectrum_real hT hn i⟩ : ℂ) •
    IsSelfAdjoint.P hT hn i
  map_zero' := by simp
  map_one' := by
    simp only [ContinuousMap.one_apply, Complex.ofReal_one, one_smul]
    exact hT.sum_P_eq_one hn
  map_add' f g := by
    simp only [ContinuousMap.coe_add, Pi.add_apply, Complex.ofReal_add, add_smul,
      Finset.sum_add_distrib]
  map_mul' f g := by
    simp only [ContinuousMap.coe_mul, Pi.mul_apply, Complex.ofReal_mul]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(Finset.sum_eq_single i (fun j _ hj ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ _) h))]
    · rw [smul_mul_smul_comm, hT.P_mul_P_self hn]
    · rw [smul_mul_smul_comm, hT.P_mul_P_of_ne hn (Ne.symm hj), smul_zero]
  map_star' f := by
    simp only [star_trivial]
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [star_smul, hT.star_P, RCLike.star_def, Complex.conj_ofReal]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, ContinuousMap.coe_smul, Pi.smul_apply,
      ContinuousMap.coe_one, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← Finset.smul_sum, hT.sum_P_eq_one hn, Complex.coe_smul]

@[simp] lemma cfcAuxOp_apply (g : C(spectrum ℝ T, ℝ)) :
    hT.cfcAuxOp hn g = ∑ i, (g ⟨hT.isSymmetric.eigenvalues hn i,
        hT.eigenvalues_mem_spectrum_real hn i⟩ : ℂ) • hT.P hn i := rfl

/-- `cfcAuxOp` sends the spectrum's identity function to `T`, by spectral expansion. -/
lemma cfcAuxOp_id : hT.cfcAuxOp hn
    ((ContinuousMap.id ℝ).restrict (spectrum ℝ T)) = T := by
  simp only [cfcAuxOp_apply]
  exact (hT.spectral_sum hn).symm

/-- `cfcAuxOp` is continuous: it is a finite sum of pointwise-evaluation-then-smul terms,
each of which is continuous. -/
lemma continuous_cfcAuxOp : Continuous (hT.cfcAuxOp hn) :=
  (continuous_finsetSum _ fun _ _ ↦
    (Complex.continuous_ofReal.comp (ContinuousMap.evalCLM ℝ _).continuous).smul
      continuous_const).congr fun g ↦ (cfcAuxOp_apply hT hn g).symm

/-- **Closed-form continuous functional calculus**: for a self-adjoint operator `T` on a
finite-dimensional complex inner product space, the continuous functional calculus has
closed-form expansion in terms of the rank-one projectors along the orthonormal eigenbasis. -/
theorem cfc_eq_sum_rankOne (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ T)) :
    cfc f T = ∑ i, ((f (hT.isSymmetric.eigenvalues hn i) : ℝ) : ℂ) •
      InnerProductSpace.rankOne ℂ (hT.isSymmetric.eigenvectorBasis hn i)
        (hT.isSymmetric.eigenvectorBasis hn i) := by
  simp [cfc_apply f T hT hf,
    cfcHom_eq_of_continuous_of_map_id hT (hT.cfcAuxOp hn) (hT.continuous_cfcAuxOp hn)
      (hT.cfcAuxOp_id hn)]

/-- **Trace of `(cfc f T) ∘ M` as a single sum over `T`'s eigenbasis** (the basic,
complex-valued form): `tr((cfc f T) ∘ M) = ∑ᵢ f(λᵢ) · ⟪eᵢ, M eᵢ⟫`. Expanding
`cfc f T = ∑ᵢ f(λᵢ) • rankOne eᵢ eᵢ` keeps everything in `T`'s *fixed* eigenbasis (the `eᵢ` are
`T`'s eigenvectors, not `M`'s), with `M` an arbitrary operator — the form needed to take an `ε → 0`
limit where `M = ρ_ε` varies but `T = σ` is fixed. The `re`-version `re_trace_cfc_comp_eq_sum` is an
immediate corollary. (The double-sum `trace_comp_cfc_eq_double_sum` is a *different* expansion — cfc
on `U`, basis on a second operator `T` — so it routes through the general
`trace_comp_eq_sum_eigenvalues_inner`, not this lemma.) -/
theorem trace_cfc_comp_eq_sum (hT : IsSelfAdjoint T) (hn : Module.finrank ℂ E = n)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ T)) (M : E →L[ℂ] E) :
    LinearMap.trace ℂ E ((cfc f T).toLinearMap ∘ₗ M.toLinearMap)
      = ∑ i, (f (hT.isSymmetric.eigenvalues hn i) : ℂ)
          * ⟪hT.isSymmetric.eigenvectorBasis hn i,
              M (hT.isSymmetric.eigenvectorBasis hn i)⟫_ℂ := by
  set v := hT.isSymmetric.eigenvectorBasis hn
  rw [hT.cfc_eq_sum_rankOne hn f hf]
  have hdist : (↑(∑ i, (↑(f (hT.isSymmetric.eigenvalues hn i)) : ℂ) • rankOne ℂ (v i) (v i)) :
        E →ₗ[ℂ] E) ∘ₗ M.toLinearMap
      = ∑ i, (((↑(f (hT.isSymmetric.eigenvalues hn i)) : ℂ) • rankOne ℂ (v i) (v i)) :
        E →L[ℂ] E).toLinearMap ∘ₗ M.toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_sum]; ext x; simp [LinearMap.sum_apply]
  rw [hdist, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_comp, map_smul, smul_eq_mul,
    LinearMap.trace_comp_comm', ← ContinuousLinearMap.toLinearMap_comp,
    InnerProductSpace.comp_rankOne, InnerProductSpace.trace_rankOne]

/-- **Trace of `(cfc f T) ∘ M`, real part** (`re`-corollary of `trace_cfc_comp_eq_sum`):
`re tr((cfc f T) ∘ M) = ∑ᵢ f(λᵢ) · re ⟪eᵢ, M eᵢ⟫`, using that `f λᵢ` is real. -/
theorem re_trace_cfc_comp_eq_sum (hT : IsSelfAdjoint T) (hn : Module.finrank ℂ E = n)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ T)) (M : E →L[ℂ] E) :
    RCLike.re (LinearMap.trace ℂ E ((cfc f T).toLinearMap ∘ₗ M.toLinearMap))
      = ∑ i, f (hT.isSymmetric.eigenvalues hn i)
          * RCLike.re ⟪hT.isSymmetric.eigenvectorBasis hn i,
              M (hT.isSymmetric.eigenvectorBasis hn i)⟫_ℂ := by
  rw [hT.trace_cfc_comp_eq_sum hn f hf M, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ RCLike.re_ofReal_mul _ _

/-- Closed-form `cfc Real.sqrt T` for any self-adjoint `T`. (Junk on negative eigenvalues
since `Real.sqrt` is `0` outside `[0, ∞)`.) -/
theorem cfc_sqrt_eq_sum_rankOne :
    cfc Real.sqrt T = ∑ i, ((Real.sqrt (hT.isSymmetric.eigenvalues hn i) : ℝ) : ℂ) •
      InnerProductSpace.rankOne ℂ (hT.isSymmetric.eigenvectorBasis hn i)
        (hT.isSymmetric.eigenvectorBasis hn i) :=
  hT.cfc_eq_sum_rankOne hn Real.sqrt Real.continuous_sqrt.continuousOn

/-- Closed-form `cfc Real.exp T` for any self-adjoint `T`. -/
theorem cfc_exp_eq_sum_rankOne :
    cfc Real.exp T = ∑ i, ((Real.exp (hT.isSymmetric.eigenvalues hn i) : ℝ) : ℂ) •
      InnerProductSpace.rankOne ℂ (hT.isSymmetric.eigenvectorBasis hn i)
        (hT.isSymmetric.eigenvectorBasis hn i) :=
  hT.cfc_eq_sum_rankOne hn Real.exp Real.continuous_exp.continuousOn

/-- Closed-form `cfc Real.log T` for a self-adjoint `T` whose spectrum avoids `0`. -/
theorem cfc_log_eq_sum_rankOne (h0 : (0 : ℝ) ∉ spectrum ℝ T) :
    cfc Real.log T = ∑ i, ((Real.log (hT.isSymmetric.eigenvalues hn i) : ℝ) : ℂ) •
      InnerProductSpace.rankOne ℂ (hT.isSymmetric.eigenvectorBasis hn i)
        (hT.isSymmetric.eigenvectorBasis hn i) :=
  hT.cfc_eq_sum_rankOne hn Real.log <|
    Real.continuousOn_log.mono fun _ hx h ↦ h0 (h ▸ hx)

/-- **Spectral quadratic-form expansion**: for self-adjoint `T` with eigenvalues `λᵢ` and
orthonormal eigenbasis `eᵢ`, and continuous `f` on `spectrum ℝ T`, the inner-product
`⟨x, cfc f T x⟩` decomposes pointwise as `∑ i, f(λᵢ) * ‖⟨eᵢ, x⟩‖²` for any vector `x`. The
quadratic-form sibling of `IsSelfAdjoint.cfc_eq_sum_rankOne`. -/
theorem cfc_inner_self_eq_sum (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ T)) (x : E) :
    ⟪x, (cfc f T) x⟫_ℂ = ∑ i, ((f (hT.isSymmetric.eigenvalues hn i) : ℝ) : ℂ) *
      ((‖⟪hT.isSymmetric.eigenvectorBasis hn i, x⟫_ℂ‖ : ℂ) ^ 2) := by
  rw [hT.cfc_eq_sum_rankOne hn f hf, _root_.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [_root_.smul_apply, inner_smul_right,
    InnerProductSpace.rankOne_apply, inner_smul_right]
  -- Goal: (f λᵢ) * (⟨eᵢ, x⟩ * ⟨x, eᵢ⟩) = (f λᵢ) * ‖⟨eᵢ, x⟩‖²
  congr 1
  rw [← inner_conj_symm x (hT.isSymmetric.eigenvectorBasis hn i), RCLike.mul_conj]
  norm_cast

end cfcAuxOp

/-- **Trace double-sum expansion of `tr((cfc f U) ∘ T)`**: for self-adjoint `T, U` with
respective eigenvalues `λᵢ, μⱼ` and orthonormal eigenbases `eᵢ, fⱼ`, and continuous `f` on
`spectrum ℝ U`, the trace factors as
`∑ᵢ λᵢ * ∑ⱼ f(μⱼ) * ‖⟨fⱼ, eᵢ⟩‖²`.

Foundational for operator Klein's inequality (Nielsen–Chuang Theorem 11.7): when `T := ρ`
(density) and `U := σ` (positive density), the formula expresses `tr(ρ log σ)` as a double
sum that Jensen's inequality on `log` then bounds by the classical Gibbs/Klein expression. -/
theorem trace_comp_cfc_eq_double_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {T U : E →L[ℂ] E} (hT : IsSelfAdjoint T) (hU : IsSelfAdjoint U)
    {n : ℕ} (hn : Module.finrank ℂ E = n)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ U)) :
    LinearMap.trace ℂ E ((cfc f U).toLinearMap ∘ₗ T.toLinearMap) =
      ∑ i, (hT.isSymmetric.eigenvalues hn i : ℂ) *
        ∑ j, ((f (hU.isSymmetric.eigenvalues hn j) : ℝ) : ℂ) *
          ((‖⟪hU.isSymmetric.eigenvectorBasis hn j,
              hT.isSymmetric.eigenvectorBasis hn i⟫_ℂ‖ : ℂ) ^ 2) := by
  rw [LinearMap.IsSymmetric.trace_comp_eq_sum_eigenvalues_inner hT.isSymmetric hn]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact hU.cfc_inner_self_eq_sum hn f hf _

/-- **Spectral mapping on eigenvectors**: for a self-adjoint operator `T` on a finite-dimensional
complex inner product space, if `x` is an eigenvector of `T` with real eigenvalue `μ` and `f` is
continuous on the spectrum of `T`, then `cfc f T x = (f μ : ℂ) • x`.

Proof: expand `cfc f T x = ∑ i (f λᵢ : ℂ) • ⟨eᵢ, x⟩ • eᵢ` via `cfc_eq_sum_rankOne`. For each `i`,
either `⟨eᵢ, x⟩ = 0` (term vanishes) or `λᵢ = μ` (so `f λᵢ = f μ`) — both follow from comparing
`⟪eᵢ, T x⟫` computed via `hμ` and via the eigenvector equation for `eᵢ`. Pull `(f μ : ℂ)` out
and apply Parseval (`OrthonormalBasis.sum_repr'`). -/
theorem cfc_apply_smul_of_apply_eq_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {n : ℕ}
    (hn : Module.finrank ℂ E = n) {f : ℝ → ℝ} (hf : ContinuousOn f (spectrum ℝ T))
    {x : E} {μ : ℝ} (hμ : T x = (μ : ℂ) • x) :
    cfc f T x = (f μ : ℂ) • x := by
  set e := hT.isSymmetric.eigenvectorBasis hn
  set lams := hT.isSymmetric.eigenvalues hn with hlams_def
  -- Each term either vanishes (`⟪eᵢ, x⟫ = 0`) or has matching scalar (`λᵢ = μ`, so `f λᵢ = f μ`).
  have hterm : ∀ i, ((f (lams i) : ℝ) : ℂ) • ⟪e i, x⟫_ℂ • e i =
      ((f μ : ℝ) : ℂ) • ⟪e i, x⟫_ℂ • e i := fun i ↦ by
    by_cases h_inner : ⟪e i, x⟫_ℂ = 0
    · simp [h_inner]
    · rw [hlams_def, hT.eigenvalue_eq_of_inner_ne_zero hμ
        (hT.apply_eigenvectorBasis_cast hn i) h_inner]
  rw [hT.cfc_eq_sum_rankOne hn f hf]
  simp only [_root_.sum_apply, _root_.smul_apply,
    InnerProductSpace.rankOne_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.smul_sum, e.sum_repr' x]

/-- **Trace of `(cfc f T) ∘ M` in an arbitrary eigenbasis of `T`** — the arbitrary-basis
generalization of `re_trace_cfc_comp_eq_sum`, which pins the basis to the canonical
`hT.isSymmetric.eigenvectorBasis`. For *any* orthonormal basis `b` of eigenvectors of a self-adjoint
`T` (`T (b i) = μ i • b i`) and `f` continuous on the spectrum of `T`,
`re tr((cfc f T) ∘ M) = ∑ᵢ f(μ i) · re⟨b i, M (b i)⟩` for any operator `M`.

The freedom to pick `b` is essential when two self-adjoint operators must be diagonalized in a
*shared* basis — e.g. `T` and an identity shift `T + ε • 1`, which have the same eigenvectors but
distinct canonical eigenbases. Trace cyclicity (`LinearMap.trace_mul_comm`) moves `cfc f T` to the
right of `M`; in the eigenbasis of `T` it acts diagonally as `f(μ i)`
(`cfc_apply_smul_of_apply_eq_smul`), reducing the trace to the eigenvalue-weighted sum of the
diagonal matrix elements `⟨b i, M (b i)⟩` of `M`. No positivity or self-adjointness of `M` is
needed. -/
theorem re_trace_cfc_comp_eq_sum_of_apply_eq_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) {μ : ι → ℝ} (hTb : ∀ i, T (b i) = (μ i : ℂ) • b i)
    {f : ℝ → ℝ} (hf : ContinuousOn f (spectrum ℝ T)) (M : E →L[ℂ] E) :
    RCLike.re (LinearMap.trace ℂ E ((cfc f T).toLinearMap ∘ₗ M.toLinearMap))
      = ∑ i, f (μ i) * RCLike.re (inner ℂ (b i) (M (b i))) := by
  classical
  have hdiag : ∀ i, (cfc f T) (b i) = (f (μ i) : ℂ) • b i := fun i =>
    hT.cfc_apply_smul_of_apply_eq_smul rfl hf (hTb i)
  have hcomm : (LinearMap.trace ℂ E) ((cfc f T).toLinearMap ∘ₗ M.toLinearMap)
      = (LinearMap.trace ℂ E) (M.toLinearMap ∘ₗ (cfc f T).toLinearMap) :=
    LinearMap.trace_mul_comm ℂ _ _
  rw [hcomm, LinearMap.trace_eq_sum_inner _ b, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, hdiag i,
    map_smul, inner_smul_right]
  simp

/-- **Spectral mapping for `Real.log` on eigenvectors of a positive-spectrum self-adjoint
operator**: combines `cfc_apply_smul_of_apply_eq_smul` (the generic spectral mapping) with
`continuousOn_log_spectrum_of_eigenvalues_pos` (the continuity-of-log discharge). -/
theorem cfc_log_apply_smul_of_apply_eq_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {n : ℕ}
    (hn : Module.finrank ℂ E = n) (hpos : ∀ i, 0 < hT.isSymmetric.eigenvalues hn i)
    {x : E} {μ : ℝ} (hμ : T x = (μ : ℂ) • x) :
    cfc Real.log T x = ((Real.log μ : ℝ) : ℂ) • x :=
  hT.cfc_apply_smul_of_apply_eq_smul hn (hT.continuousOn_log_spectrum_of_eigenvalues_pos hn hpos) hμ

/-- **`cfc Real.log` on a basis eigenvector** of a positive-spectrum self-adjoint operator:
the result is the log of the eigenvalue times the eigenvector. -/
theorem cfc_log_apply_eigenvectorBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {n : ℕ}
    (hn : Module.finrank ℂ E = n) (hpos : ∀ i, 0 < hT.isSymmetric.eigenvalues hn i) (i : Fin n) :
    cfc Real.log T (hT.isSymmetric.eigenvectorBasis hn i) =
      ((Real.log (hT.isSymmetric.eigenvalues hn i) : ℝ) : ℂ) •
        hT.isSymmetric.eigenvectorBasis hn i :=
  hT.cfc_log_apply_smul_of_apply_eq_smul hn hpos (hT.apply_eigenvectorBasis_cast hn i)

/-- **Spectral mapping for `· ^ y` (real rpow with constant exponent) on eigenvectors of a
positive-spectrum self-adjoint operator**: sibling of `cfc_log_apply_smul_of_apply_eq_smul`,
combining `cfc_apply_smul_of_apply_eq_smul` with
`continuousOn_rpow_const_spectrum_of_eigenvalues_pos`. -/
theorem cfc_rpow_const_apply_smul_of_apply_eq_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {n : ℕ}
    (hn : Module.finrank ℂ E = n) (hpos : ∀ i, 0 < hT.isSymmetric.eigenvalues hn i) (y : ℝ)
    {x : E} {μ : ℝ} (hμ : T x = (μ : ℂ) • x) :
    cfc (fun x : ℝ ↦ x ^ y) T x = ((μ ^ y : ℝ) : ℂ) • x :=
  hT.cfc_apply_smul_of_apply_eq_smul hn
    (hT.continuousOn_rpow_const_spectrum_of_eigenvalues_pos hn hpos y) hμ

/-- **`cfc (· ^ y)` on a basis eigenvector** of a positive-spectrum self-adjoint operator: the
result is the `y`-th power of the eigenvalue times the eigenvector. Sibling of
`cfc_log_apply_eigenvectorBasis`. -/
theorem cfc_rpow_const_apply_eigenvectorBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {n : ℕ}
    (hn : Module.finrank ℂ E = n) (hpos : ∀ i, 0 < hT.isSymmetric.eigenvalues hn i) (y : ℝ)
    (i : Fin n) :
    cfc (fun x : ℝ ↦ x ^ y) T (hT.isSymmetric.eigenvectorBasis hn i) =
      (((hT.isSymmetric.eigenvalues hn i) ^ y : ℝ) : ℂ) •
        hT.isSymmetric.eigenvectorBasis hn i :=
  hT.cfc_rpow_const_apply_smul_of_apply_eq_smul hn hpos y (hT.apply_eigenvectorBasis_cast hn i)

/-- `(cfc f T) · T = cfc (t ↦ f t · t) T`: the product of `cfc f T` with `T` collapses to a single
`cfc`, recombining via `cfc_mul` and `cfc_id` (continuity of `f` on the finite spectrum is free,
via `continuousOn_spectrum`). Captures the shared "rewrite `T` as `cfc id T`, recombine" move. Pure
functional calculus — a candidate for upstream Mathlib. -/
theorem cfc_mul_id (hT : IsSelfAdjoint T) (f : ℝ → ℝ) :
    cfc f T * T = cfc (fun t : ℝ ↦ f t * t) T := by
  nth_rw 2 [← cfc_id ℝ T]
  rw [← cfc_mul _ _ _ (hT.continuousOn_spectrum _) (hT.continuousOn_spectrum _)]
  rfl

/-- `T · (cfc g T) = cfc (t ↦ t · g t) T`: the left-product mirror of `cfc_mul_id`. -/
theorem cfc_id_mul (hT : IsSelfAdjoint T) (g : ℝ → ℝ) :
    T * cfc g T = cfc (fun t : ℝ ↦ t * g t) T := by
  nth_rw 1 [← cfc_id ℝ T]
  rw [← cfc_mul _ _ _ (hT.continuousOn_spectrum _) (hT.continuousOn_spectrum _)]
  rfl

/-- A self-adjoint operator annihilates the spectral projection onto its zero-eigenspace
`cfc 1_{{0}} T` (the projection onto `ker T`): `T * cfc 1_{{0}} T = 0`, since `t · 1_{{0}}(t) = 0`
for every `t` (at `t = 0` the first factor vanishes, elsewhere the indicator does). Foundational for
the `ker σ`-block of the relative-entropy continuity limit. -/
theorem self_mul_cfc_indicator_zero (hT : IsSelfAdjoint T) :
    T * cfc (Set.indicator {0} (1 : ℝ → ℝ)) T = 0 := by
  have hfun : (fun t : ℝ ↦ t * Set.indicator {0} (1 : ℝ → ℝ) t) = 0 := by
    ext t; by_cases ht : t = 0 <;> simp [ht]
  rw [hT.cfc_id_mul, hfun, cfc_zero]

/-- **Entropy-term reduction**: `(cfc log T) · T = cfc (t ↦ t log t) T`. The product `cfc log T · T`
becomes a single `cfc` of the continuous function `t ↦ t log t` (removable singularity at `0`,
`Real.continuous_mul_log`), which — unlike `cfc log T` alone — is continuous in `T`. The reduction
that makes the entropy term `tr((cfc log ρ) · ρ)` continuous in `ρ` across the kernel. -/
theorem cfc_log_mul_self (hT : IsSelfAdjoint T) :
    cfc Real.log T * T = cfc (fun t : ℝ ↦ t * Real.log t) T :=
  (hT.cfc_mul_id Real.log).trans (cfc_congr fun _ _ ↦ mul_comm _ _)

end IsSelfAdjoint

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open scoped ComplexOrder in
/-- **Uniqueness of the positive square root**: for a positive operator `x`, the CFC sqrt of
`x * x` recovers `x`. Equivalently, two positive operators with equal squares are equal —
applying this lemma to both sides of `A * A = B * B` (`0 ≤ A`, `0 ≤ B`) gives
`A = cfc Real.sqrt (A * A) = cfc Real.sqrt (B * B) = B`. Proved via `cfc_comp_pow` +
`cfc_id` + `Real.sqrt_sq` on the spectrum. -/
theorem cfc_real_sqrt_mul_self_eq_self_of_nonneg
    {x : E →L[ℂ] E} (hx : 0 ≤ x) :
    cfc Real.sqrt (x * x) = x := by
  conv_rhs => rw [← cfc_id ℝ x]
  rw [← sq, ← cfc_comp_pow (R := ℝ) Real.sqrt 2 x]
  exact cfc_congr fun y hy ↦ Real.sqrt_sq (spectrum_nonneg_of_nonneg hx hy)

/-- **CFC commutes with conjugation by an isometry**, for functions vanishing at `0`. For
`V : E →L[ℂ] H` an isometry (`V† V = 1`), self-adjoint `ρ`, and `f` with `f 0 = 0`,
`cfc f (V ρ V†) = V (cfc f ρ) V†`. The `f 0 = 0` hypothesis is essential: it kills the contribution
of the zero eigenspace `(ran V)ᗮ` of `V ρ V†`, on which the unital `cfc` would otherwise place
`f 0`. Routes through the non-unital `cfcₙ` (which builds in `f 0 = 0`) and its naturality under the
non-unital `⋆`-hom `conjIsometryₙ` (`NonUnitalStarAlgHom.map_cfcₙ`). The non-equiv companion to
`LinearIsometryEquiv.conjStarAlgEquiv_cfc_real_log`. -/
theorem cfc_conj_isometry [FiniteDimensional ℂ E] [IsScalarTower ℝ ℂ (E →L[ℂ] E)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [CompleteSpace H] [IsScalarTower ℝ ℂ (H →L[ℂ] H)]
    {V : E →L[ℂ] H} (hV : V.adjoint ∘L V = 1) {ρ : E →L[ℂ] E}
    (hρ : IsSelfAdjoint ρ) {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    cfc f (V ∘L ρ ∘L V.adjoint) = V ∘L (cfc f ρ) ∘L V.adjoint := by
  have hVρ : IsSelfAdjoint (conjIsometryₙ hV ρ) := by
    change star (conjIsometryₙ hV ρ) = conjIsometryₙ hV ρ
    rw [← map_star, hρ.star_eq]
  have hφ : Continuous ⇑(conjIsometryₙ hV) := by
    change Continuous fun A : E →L[ℂ] E ↦ V ∘L A ∘L V.adjoint
    fun_prop
  have hqρ := IsSelfAdjoint.continuousOn_quasispectrum hρ f
  rw [← conjIsometryₙ_apply hV ρ, ← conjIsometryₙ_apply hV (cfc f ρ),
    ← cfcₙ_eq_cfc (hf := IsSelfAdjoint.continuousOn_quasispectrum hVρ f) (hf0 := hf0),
    ← cfcₙ_eq_cfc (a := ρ) (hf := hqρ) (hf0 := hf0)]
  exact ((conjIsometryₙ hV).map_cfcₙ f ρ hqρ hf0 hφ hρ hVρ).symm

end ContinuousLinearMap
