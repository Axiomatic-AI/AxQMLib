/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
public import ToMathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Complex.Order

/-!
# Joint convexity of the quantum relative entropy on the finite branch (no faithfulness)

Lindblad's theorem (`ContinuousLinearMap.convexOn_quantumRelativeEntropy`) establishes the joint
convexity of the quantum relative entropy `D(ρ ‖ σ) = re tr(ρ log ρ) − re tr(ρ log σ)` only on the
open cone of **strictly positive** operators. The goal of this development is to remove the
strict-positivity hypothesis, extending joint convexity to N&C's own **finite branch** — the
**support condition** `supp ρ ⊆ supp σ` (`HasSupportLE ρ σ`, i.e. `ker σ ≤ ker ρ`), on which the
real-valued `cfc`-based `D` equals the true relative entropy — as the faithful form of Nielsen &
Chuang Theorem 11.12 (the strict-positivity form, which excludes rank-deficient `ρ, σ`, becomes a
corollary).

This file establishes the analytic **engine** for that removal: the identity-shift continuity of the
relative entropy on the finite branch. The joint convexity itself is assembled from it
separately, by the perturbation-and-limit argument that removes faithfulness from strong
subadditivity (N&C Thm 11.14): shift each operator by `ε • 1` (strictly positive for `ε > 0`, since
`A + ε • 1 ≥ ε • 1` for `A ≥ 0`), apply the strict-positivity joint convexity to the shifted family,
and pass to the limit `ε → 0⁺` through

* `ContinuousLinearMap.tendsto_quantumRelativeEntropy_add_smul_one` —
  `D(ρ + ε•1 ‖ σ + ε•1) → D(ρ ‖ σ)` as `ε → 0⁺`, for positive `ρ, σ` with `HasSupportLE ρ σ`.

Because `ε • 1` commutes with every operator, the shift `Y ↦ Y + ε • 1` stays inside `Y`'s
functional calculus: in the eigenbasis of `Y` the cross trace term
`re tr((log(Y + ε•1)) ∘ (X + ε•1))` is the finite sum `∑ⱼ log(μⱼ + ε)(aⱼ + ε)` with
`aⱼ = re⟨bⱼ, X bⱼ⟩`, and the support condition forces `aⱼ = 0` on the kernel of `Y` (`μⱼ = 0`), so
those terms are the harmless `ε log ε → 0` (`Real.continuous_negMulLog`). Each surviving term
converges by continuity of `log` away from `0`.

The trace-in-an-arbitrary-eigenbasis identity these build on,
`IsSelfAdjoint.re_trace_cfc_comp_eq_sum_of_apply_eq_smul`
(`re tr((cfc f Y) ∘ X) = ∑ⱼ f(μⱼ) · re⟨bⱼ, X bⱼ⟩`), is a general CFC/trace fact and lives with its
siblings in `ToMathlib.Analysis.InnerProductSpace.CFC`.

## Main results

* `ContinuousLinearMap.tendsto_re_trace_cfc_log_add_smul_one` — the identity-shift continuity of the
  cross trace term under the support condition.
* `ContinuousLinearMap.tendsto_quantumRelativeEntropy_add_smul_one` — identity-shift continuity of
  `D` on the finite branch, the engine that removes strict positivity from joint convexity.
* `ContinuousLinearMap.hasSupportLE_sum_smul` — a convex mixture inherits the support condition of
  its components: if each `ρₖ` is supported in `σₖ` (positive) with weight `wₖ ≥ 0`, then
  `∑ₖ wₖ ρₖ` is supported in `∑ₖ wₖ σₖ`.
* `ContinuousLinearMap.quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE` — joint convexity
  of `D` on the finite branch (`n`-ary), **without** strict positivity: only positivity and the
  support condition on each component. This is the faithful form of N&C Theorem 11.12.
* `ContinuousLinearMap.quantumRelativeEntropy_jointly_convex_of_hasSupportLE` — its two-point
  specialization, N&C's literal statement.
-/

@[expose] public section

open scoped Topology InnerProductSpace ComplexOrder
open Filter

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]

/-- **Identity-shift continuity of the relative-entropy cross term on the finite branch.** For a
self-adjoint operator `Y` with an eigenbasis `b` and real eigenvalues `μ` (`Y (b i) = μ i • b i`),
and any `X` with the support condition `HasSupportLE X Y` (`ker Y ≤ ker X`), the cross trace term of
shifted operators converges,
`re tr((log(Y + ε•1)) ∘ (X + ε•1)) → re tr((log Y) ∘ X)` as `ε → 0⁺`.

In the eigenbasis of `Y`, `IsSelfAdjoint.re_trace_cfc_comp_eq_sum_of_apply_eq_smul` turns the
shifted cross term into the finite sum `∑ᵢ log(μ i + ε)(aᵢ + ε)` with `aᵢ = re⟨b i, X (b i)⟩` (the
shift adds `ε` to each eigenvalue and each diagonal element). The limit is termwise: where `μ i ≠ 0`
the term is continuous at `ε = 0` (`Real.log` is continuous away from `0`); where `μ i = 0` the
support condition forces `X (b i) = 0` (so `aᵢ = 0`), leaving the harmless `ε log ε → 0`
(`Real.negMulLog` is continuous, with `Real.negMulLog 0 = 0`). -/
theorem tendsto_re_trace_cfc_log_add_smul_one {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) {X Y : E →L[ℂ] E} {μ : ι → ℝ}
    (hY : IsSelfAdjoint Y) (hYb : ∀ i, Y (b i) = (μ i : ℂ) • b i)
    (h : X.HasSupportLE Y) :
    Tendsto (fun ε : ℝ => RCLike.re (LinearMap.trace ℂ E
        ((cfc Real.log (Y + (ε : ℂ) • 1)).toLinearMap ∘ₗ (X + (ε : ℂ) • 1).toLinearMap)))
      (𝓝[>] 0) (𝓝 (RCLike.re (LinearMap.trace ℂ E
        ((cfc Real.log Y).toLinearMap ∘ₗ X.toLinearMap)))) := by
  classical
  have hsa1 : ∀ ε : ℝ, IsSelfAdjoint ((ε : ℂ) • (1 : E →L[ℂ] E)) := fun ε => by
    rw [isSelfAdjoint_iff, star_smul, star_one, RCLike.star_def, Complex.conj_ofReal]
  have hYε : ∀ ε : ℝ, IsSelfAdjoint (Y + (ε : ℂ) • 1) := fun ε => hY.add (hsa1 ε)
  have hYεb : ∀ (ε : ℝ) (i : ι), (Y + (ε : ℂ) • 1) (b i) = ((μ i + ε : ℝ) : ℂ) • b i := by
    intro ε i
    rw [_root_.add_apply, hYb i, _root_.smul_apply,
      one_apply_eq_self, ← add_smul, Complex.ofReal_add]
  -- rewrite the RHS limit point in the eigenbasis of `Y`
  rw [hY.re_trace_cfc_comp_eq_sum_of_apply_eq_smul b hYb hY.continuousOn_log_spectrum X]
  -- rewrite the ε-dependent cross term in the (shared) eigenbasis of `Y + ε•1`
  have hfun : ∀ ε : ℝ, RCLike.re (LinearMap.trace ℂ E
      ((cfc Real.log (Y + (ε : ℂ) • 1)).toLinearMap ∘ₗ (X + (ε : ℂ) • 1).toLinearMap))
      = ∑ i, Real.log (μ i + ε) * RCLike.re (inner ℂ (b i) ((X + (ε : ℂ) • 1) (b i))) := fun ε =>
    (hYε ε).re_trace_cfc_comp_eq_sum_of_apply_eq_smul b (hYεb ε)
      (hYε ε).continuousOn_log_spectrum (X + (ε : ℂ) • 1)
  simp_rw [hfun]
  -- the diagonal element of `X + ε•1` is that of `X` plus `ε`
  have hinner : ∀ (ε : ℝ) (i : ι), RCLike.re (inner ℂ (b i) ((X + (ε : ℂ) • 1) (b i)))
      = RCLike.re (inner ℂ (b i) (X (b i))) + ε := by
    intro ε i
    rw [_root_.add_apply, inner_add_right, _root_.smul_apply,
      one_apply_eq_self, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal i i]
    simp
  simp_rw [hinner]
  refine tendsto_finsetSum _ fun i _ => ?_
  set a : ℝ := RCLike.re (inner ℂ (b i) (X (b i))) with ha_def
  by_cases hμi : μ i = 0
  · -- kernel term: the support condition kills `aᵢ`, leaving `ε log ε → 0`
    have hXbi : X (b i) = 0 := by
      have hker : b i ∈ LinearMap.ker (Y : E →ₗ[ℂ] E) := by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hYb i, hμi]; simp
      have hmem := h hker
      rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hmem
    have ha0 : a = 0 := by rw [ha_def, hXbi]; simp
    have htarget : Real.log (μ i) * a = 0 := by rw [hμi, ha0]; simp
    rw [htarget]
    have hcongr : (fun ε : ℝ => Real.log (μ i + ε) * (a + ε)) = fun ε => -Real.negMulLog ε := by
      funext ε; rw [hμi, ha0]; simp only [zero_add, Real.negMulLog_eq_neg]; ring
    rw [hcongr]
    have hlim : Tendsto (fun ε : ℝ => -Real.negMulLog ε) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have := (Real.continuous_negMulLog.tendsto 0).neg
      rwa [Real.negMulLog_zero, neg_zero] at this
    exact hlim.mono_left nhdsWithin_le_nhds
  · -- interior term (`μ i ≠ 0`): continuous at `ε = 0`
    have hcont : ContinuousAt (fun ε : ℝ => Real.log (μ i + ε) * (a + ε)) 0 :=
      ((continuousAt_const.add continuousAt_id).log (by simpa using hμi)).mul
        (continuousAt_const.add continuousAt_id)
    have := hcont.tendsto
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds

/-- **Identity-shift continuity of the quantum relative entropy on the finite branch.** For
self-adjoint `X, Y` with the support condition `HasSupportLE X Y`,
`D(X + ε•1 ‖ Y + ε•1) → D(X ‖ Y)` as `ε → 0⁺`.

The relative entropy `D(A ‖ B) = re tr((log A) ∘ A) − re tr((log B) ∘ A)` splits into two cross
terms handled by `tendsto_re_trace_cfc_log_add_smul_one`: the self term (`B = A = X`, with the
trivial support condition `HasSupportLE X X`) and the cross term (`B = Y`, the given support
condition). Each converges, so `D` does by `Tendsto.sub`. -/
theorem tendsto_quantumRelativeEntropy_add_smul_one {X Y : E →L[ℂ] E}
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) (h : X.HasSupportLE Y) :
    Tendsto (fun ε : ℝ => quantumRelativeEntropy (X + (ε : ℂ) • 1) (Y + (ε : ℂ) • 1)) (𝓝[>] 0)
      (𝓝 (quantumRelativeEntropy X Y)) := by
  simp_rw [quantumRelativeEntropy_def]
  refine Tendsto.sub ?_ ?_
  · exact tendsto_re_trace_cfc_log_add_smul_one (X := X) (Y := X)
      (hX.isSymmetric.eigenvectorBasis rfl) hX
      (fun i => hX.apply_eigenvectorBasis_cast rfl i) le_rfl
  · exact tendsto_re_trace_cfc_log_add_smul_one (X := X) (Y := Y)
      (hY.isSymmetric.eigenvectorBasis rfl) hY
      (fun i => hY.apply_eigenvectorBasis_cast rfl i) h

omit [FiniteDimensional ℂ E] in
/-- **A convex mixture inherits the support condition of its components.** If each `σ k` is a
positive operator, `ρ k` is supported in `σ k` (`HasSupportLE`), and the weights `w k` are
nonnegative, then the mixture `∑ₖ wₖ ρₖ` is supported in the mixture `∑ₖ wₖ σₖ`:
`ker (∑ₖ wₖ σₖ) ≤ ker (∑ₖ wₖ ρₖ)`.

A vector `x` in `ker (∑ₖ wₖ σₖ)` gives `0 = ⟨x, (∑ₖ wₖ σₖ) x⟩ = ∑ₖ wₖ ⟨x, σₖ x⟩`, a sum of
nonnegative terms; so each vanishes, and for a positive-weight component `wₖ > 0` we get
`⟨x, σₖ x⟩ = 0`, whence `σₖ x = 0` by positivity, `x ∈ ker σₖ ≤ ker ρₖ` by the support condition,
and `ρₖ x = 0`. A zero-weight component contributes `wₖ • ρₖ x = 0` regardless, so the mixture
`(∑ₖ wₖ ρₖ) x = 0`. This makes the left-hand limit of the joint-convexity regularization
well-defined. -/
theorem hasSupportLE_sum_smul {κ : Type*} (t : Finset κ)
    {ρ σ : κ → E →L[ℂ] E} {w : κ → ℝ}
    (hσ : ∀ k ∈ t, (σ k).IsPositive) (hsupp : ∀ k ∈ t, (ρ k).HasSupportLE (σ k))
    (hw : ∀ k ∈ t, 0 ≤ w k) :
    (∑ k ∈ t, w k • ρ k).HasSupportLE (∑ k ∈ t, w k • σ k) := by
  -- Rewrite both mixtures with complex-scalar weights, matching `inner_smul_right`.
  have hρc : (∑ k ∈ t, w k • ρ k) = ∑ k ∈ t, (↑(w k) : ℂ) • ρ k :=
    Finset.sum_congr rfl fun k _ => (Complex.coe_smul (w k) (ρ k)).symm
  have hσc : (∑ k ∈ t, w k • σ k) = ∑ k ∈ t, (↑(w k) : ℂ) • σ k :=
    Finset.sum_congr rfl fun k _ => (Complex.coe_smul (w k) (σ k)).symm
  rw [hρc, hσc, hasSupportLE_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [ContinuousLinearMap.coe_coe] at hx ⊢
  -- `0 = ⟨x, (∑ₖ wₖ σₖ) x⟩ = ∑ₖ wₖ ⟨x, σₖ x⟩`, a sum of nonnegative terms.
  have hzsum : ∑ k ∈ t, (w k : ℂ) * inner ℂ x ((σ k) x) = 0 := by
    have h0 : inner ℂ x ((∑ k ∈ t, (↑(w k) : ℂ) • σ k) x) = 0 := by rw [hx]; simp
    rw [_root_.sum_apply, inner_sum] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun k _ => by
      rw [_root_.smul_apply, inner_smul_right]
  have hznn : ∀ k ∈ t, (0 : ℂ) ≤ (w k : ℂ) * inner ℂ x ((σ k) x) := fun k hk =>
    mul_nonneg (by exact_mod_cast hw k hk) ((hσ k hk).inner_nonneg_right x)
  have hterm : ∀ k ∈ t, (w k : ℂ) * inner ℂ x ((σ k) x) = 0 := fun k hk =>
    (Finset.sum_eq_zero_iff_of_nonneg hznn).mp hzsum k hk
  rw [_root_.sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [_root_.smul_apply]
  rcases (hw k hk).eq_or_lt with hwk | hwk
  · rw [← hwk]; simp
  · have hwk' : (w k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hwk
    have hinner : inner ℂ x ((σ k) x) = 0 := (mul_eq_zero.mp (hterm k hk)).resolve_left hwk'
    have hσx : (σ k) x = 0 := apply_eq_zero_of_re_inner_self_eq_zero
      (nonneg_iff_isPositive.mpr (hσ k hk)) (by rw [hinner]; simp)
    have hρx : (ρ k) x = 0 := by
      have hmem := hsupp k hk (by rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]; exact hσx)
      rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hmem
    rw [hρx, smul_zero]

omit [FiniteDimensional ℂ E] in
/-- **A binary sum inherits the support condition.** For positive operators `σ₁, σ₂` and support
conditions `ρ₁ ⊆ σ₁`, `ρ₂ ⊆ σ₂` (`HasSupportLE`), the sums satisfy `(ρ₁ + ρ₂) ⊆ (σ₁ + σ₂)`, i.e.
`(ρ₁ + ρ₂).HasSupportLE (σ₁ + σ₂)`. A vector `x ∈ ker (σ₁ + σ₂)` gives
`0 = re⟨x, (σ₁ + σ₂) x⟩ = re⟨x, σ₁ x⟩ + re⟨x, σ₂ x⟩`, a sum of nonnegative terms, so each vanishes;
positivity then forces `σ₁ x = σ₂ x = 0`, the support conditions give `ρ₁ x = ρ₂ x = 0`, and hence
`(ρ₁ + ρ₂) x = 0`. The binary (`Finset (Fin 2)`, weights `1`) special case of
`hasSupportLE_sum_smul`, proved directly; the support-condition input to the binary subadditivity of
the generalized relative entropy. -/
theorem hasSupportLE_add {ρ₁ ρ₂ σ₁ σ₂ : E →L[ℂ] E}
    (hσ₁ : σ₁.IsPositive) (hσ₂ : σ₂.IsPositive)
    (h₁ : ρ₁.HasSupportLE σ₁) (h₂ : ρ₂.HasSupportLE σ₂) :
    (ρ₁ + ρ₂).HasSupportLE (σ₁ + σ₂) := by
  rw [hasSupportLE_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [ContinuousLinearMap.coe_coe] at hx ⊢
  rw [_root_.add_apply] at hx
  have hre : RCLike.re (inner ℂ x (σ₁ x)) + RCLike.re (inner ℂ x (σ₂ x)) = 0 := by
    have h0 : RCLike.re (inner ℂ x (σ₁ x + σ₂ x)) = RCLike.re (inner ℂ x (0 : E)) := by rw [hx]
    rwa [inner_add_right, map_add, inner_zero_right, map_zero] at h0
  have hn₁ : 0 ≤ RCLike.re (inner ℂ x (σ₁ x)) := hσ₁.re_inner_nonneg_right x
  have hn₂ : 0 ≤ RCLike.re (inner ℂ x (σ₂ x)) := hσ₂.re_inner_nonneg_right x
  have hσ₁x : σ₁ x = 0 :=
    apply_eq_zero_of_re_inner_self_eq_zero (nonneg_iff_isPositive.mpr hσ₁) (by linarith)
  have hσ₂x : σ₂ x = 0 :=
    apply_eq_zero_of_re_inner_self_eq_zero (nonneg_iff_isPositive.mpr hσ₂) (by linarith)
  have hρ₁x : ρ₁ x = 0 := h₁.apply_eq_zero hσ₁x
  have hρ₂x : ρ₂ x = 0 := h₂.apply_eq_zero hσ₂x
  rw [_root_.add_apply, hρ₁x, hρ₂x, add_zero]

omit [FiniteDimensional ℂ E] in
omit [CompleteSpace E] in
/-- **Nonzero scaling of both operators preserves the support condition.** For `c ≠ 0`, scaling both
operators by the real scalar `c` leaves both kernels unchanged (`ker (c • τ) = ker τ`, since `ℂ` is
a semifield and `(c : ℂ) ≠ 0`), so `ρ.HasSupportLE σ` upgrades to `(c • ρ).HasSupportLE (c • σ)`.
Transports a per-pair support condition on `rᵢ, sᵢ` to the scaled `t • rᵢ, t • sᵢ`, as used by the
converse (subadditivity ⟹ joint convexity) argument for the generalized relative entropy. -/
theorem hasSupportLE_smul {ρ σ : E →L[ℂ] E} {c : ℝ} (hc : c ≠ 0)
    (h : ρ.HasSupportLE σ) : (c • ρ).HasSupportLE (c • σ) := by
  have hker : ∀ τ : E →L[ℂ] E,
      (↑(c • τ) : E →ₗ[ℂ] E).ker = (↑τ : E →ₗ[ℂ] E).ker := fun τ => by
    rw [← Complex.coe_smul c τ, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.ker_smul _ _ (by exact_mod_cast hc : (c : ℂ) ≠ 0)]
  unfold ContinuousLinearMap.HasSupportLE at h ⊢
  rwa [hker ρ, hker σ]

/-- **Joint convexity of the quantum relative entropy on the finite branch, `n`-ary form**
(Nielsen & Chuang Theorem 11.12, faithful form). For families of positive operators
`ρ, σ : κ → E →L[ℂ] E` with the support condition `(ρ k).HasSupportLE (σ k)` on every component and
convex weights `w` (`w k ≥ 0`, `∑ w k = 1`),
`D(∑ₖ wₖ ρₖ ‖ ∑ₖ wₖ σₖ) ≤ ∑ₖ wₖ D(ρₖ ‖ σₖ)`.

There is **no strict-positivity hypothesis**: this is the faithful form of the theorem on N&C's own
finite branch (the support condition), of which the strict-positivity form
`quantumRelativeEntropy_jointly_convex_sum` is a corollary. The proof is the regularization argument
that removes faithfulness from strong subadditivity: for `ε > 0` shift every operator by `ε • 1`
(strictly positive by `isStrictlyPositive_add_smul_one`, since each `ρ k, σ k ≥ 0`), apply the
strict-positivity joint convexity to the shifted family, and pass to the limit `ε → 0⁺` via
`tendsto_quantumRelativeEntropy_add_smul_one` on both sides — the left-hand limit is well-defined
because the mixture inherits the support condition (`hasSupportLE_sum_smul`). The shift factors
through the sum because `ε • 1` is constant and `∑ₖ wₖ = 1`. -/
theorem quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE {κ : Type*} (t : Finset κ)
    {ρ σ : κ → E →L[ℂ] E} {w : κ → ℝ}
    (hρ : ∀ k ∈ t, (ρ k).IsPositive) (hσ : ∀ k ∈ t, (σ k).IsPositive)
    (hsupp : ∀ k ∈ t, (ρ k).HasSupportLE (σ k))
    (hw : ∀ k ∈ t, 0 ≤ w k) (hsum : ∑ k ∈ t, w k = 1) :
    quantumRelativeEntropy (∑ k ∈ t, w k • ρ k) (∑ k ∈ t, w k • σ k) ≤
      ∑ k ∈ t, w k * quantumRelativeEntropy (ρ k) (σ k) := by
  have : IsScalarTower ℝ ℂ (E →L[ℂ] E) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- The two mixtures are self-adjoint: nonnegative combinations of positive operators.
  have hRc : (∑ k ∈ t, w k • ρ k) = ∑ k ∈ t, (↑(w k) : ℂ) • ρ k :=
    Finset.sum_congr rfl fun k _ => (Complex.coe_smul (w k) (ρ k)).symm
  have hSc : (∑ k ∈ t, w k • σ k) = ∑ k ∈ t, (↑(w k) : ℂ) • σ k :=
    Finset.sum_congr rfl fun k _ => (Complex.coe_smul (w k) (σ k)).symm
  have hcnn : ∀ k ∈ t, (0 : ℂ) ≤ (↑(w k) : ℂ) := fun k hk =>
    RCLike.nonneg_iff_exists_ofReal.mpr ⟨w k, hw k hk, rfl⟩
  have hRsa : IsSelfAdjoint (∑ k ∈ t, w k • ρ k) := by
    rw [hRc]
    exact (isPositive_sum t fun k hk => (hρ k hk).smul_of_nonneg (hcnn k hk)).isSelfAdjoint
  have hSsa : IsSelfAdjoint (∑ k ∈ t, w k • σ k) := by
    rw [hSc]
    exact (isPositive_sum t fun k hk => (hσ k hk).smul_of_nonneg (hcnn k hk)).isSelfAdjoint
  -- The shift `+ ε • 1` factors through the finite mixture (uses `∑ wₖ = 1`).
  have hshift : ∀ (A : κ → E →L[ℂ] E) (ε : ℝ),
      (∑ k ∈ t, w k • A k) + (ε : ℂ) • 1 = ∑ k ∈ t, w k • (A k + (ε : ℂ) • 1) := fun A ε => by
    simp_rw [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul]
  -- Both sides converge as `ε → 0⁺`.
  have hf : Tendsto (fun ε : ℝ => quantumRelativeEntropy
      ((∑ k ∈ t, w k • ρ k) + (ε : ℂ) • 1) ((∑ k ∈ t, w k • σ k) + (ε : ℂ) • 1)) (𝓝[>] 0)
      (𝓝 (quantumRelativeEntropy (∑ k ∈ t, w k • ρ k) (∑ k ∈ t, w k • σ k))) :=
    tendsto_quantumRelativeEntropy_add_smul_one hRsa hSsa (hasSupportLE_sum_smul t hσ hsupp hw)
  have hg : Tendsto (fun ε : ℝ => ∑ k ∈ t, w k * quantumRelativeEntropy
      ((ρ k) + (ε : ℂ) • 1) ((σ k) + (ε : ℂ) • 1)) (𝓝[>] 0)
      (𝓝 (∑ k ∈ t, w k * quantumRelativeEntropy (ρ k) (σ k))) :=
    tendsto_finsetSum t fun k hk =>
      (tendsto_quantumRelativeEntropy_add_smul_one (hρ k hk).isSelfAdjoint (hσ k hk).isSelfAdjoint
        (hsupp k hk)).const_mul (w k)
  -- For every `ε > 0` the strict-positivity convexity applies to the shifted family.
  refine le_of_tendsto_of_tendsto hf hg ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  rw [hshift ρ ε, hshift σ ε]
  exact quantumRelativeEntropy_jointly_convex_sum t
    (fun k hk => by
      rw [Complex.coe_smul]
      exact isStrictlyPositive_add_smul_one (nonneg_iff_isPositive.mpr (hρ k hk)) hεpos)
    (fun k hk => by
      rw [Complex.coe_smul]
      exact isStrictlyPositive_add_smul_one (nonneg_iff_isPositive.mpr (hσ k hk)) hεpos)
    hw hsum

/-- **Joint convexity of the quantum relative entropy on the finite branch, two-point form**
(Nielsen & Chuang Theorem 11.12, N&C's literal statement). For positive operators `ρ₁, ρ₂, σ₁, σ₂`
with the support conditions `ρ₁ ⊆ σ₁`, `ρ₂ ⊆ σ₂` (`HasSupportLE`) and probabilities `t, s ≥ 0`,
`t + s = 1`,
`D(t ρ₁ + s ρ₂ ‖ t σ₁ + s σ₂) ≤ t · D(ρ₁ ‖ σ₁) + s · D(ρ₂ ‖ σ₂)`.

The two-point specialization of `quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE` over a
`Fin 2` index. No strict positivity is required — only the support condition, which for a genuine
mixture is automatic. -/
theorem quantumRelativeEntropy_jointly_convex_of_hasSupportLE
    {ρ₁ ρ₂ σ₁ σ₂ : E →L[ℂ] E}
    (hρ₁ : ρ₁.IsPositive) (hρ₂ : ρ₂.IsPositive) (hσ₁ : σ₁.IsPositive) (hσ₂ : σ₂.IsPositive)
    (hs₁ : ρ₁.HasSupportLE σ₁) (hs₂ : ρ₂.HasSupportLE σ₂)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    quantumRelativeEntropy (t • ρ₁ + s • ρ₂) (t • σ₁ + s • σ₂) ≤
      t * quantumRelativeEntropy ρ₁ σ₁ + s * quantumRelativeEntropy ρ₂ σ₂ := by
  have key := quantumRelativeEntropy_jointly_convex_sum_of_hasSupportLE
    (Finset.univ : Finset (Fin 2)) (ρ := ![ρ₁, ρ₂]) (σ := ![σ₁, σ₂]) (w := ![t, s])
    (by intro k _; fin_cases k <;> simpa)
    (by intro k _; fin_cases k <;> simpa)
    (by intro k _; fin_cases k <;> simpa)
    (by intro k _; fin_cases k <;> simpa)
    (by simp [Fin.sum_univ_two, hts])
  simpa [Fin.sum_univ_two] using key

end ContinuousLinearMap
