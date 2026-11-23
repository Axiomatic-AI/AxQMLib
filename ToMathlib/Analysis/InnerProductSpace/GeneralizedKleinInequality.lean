/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
public import Mathlib.Analysis.Convex.Deriv
public import ToMathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Generalized Klein's inequality

For self-adjoint operators `A, B : E →L[ℂ] E` on a finite-dimensional complex inner product
space and a function `f : ℝ → ℝ` convex on a set `S` containing the spectra of `A` and `B`,
with derivative `f'` at each eigenvalue of `B`, the **generalized Klein inequality**
(Nielsen–Chuang, *Quantum Computation and Quantum Information*, Problem 11.1) states

`tr(f(A) - f(B)) ≥ tr((A - B) f'(B))`,

where `f(A)`, `f(B)`, `f'(B)` are the continuous functional calculi. In the trace-real,
`cfc`-on-the-left convention used throughout this file (matching
`ContinuousLinearMap.quantumRelativeEntropy`), and using that trace is cyclic, this reads

`re tr((cfc f' B) ∘ (A - B)) ≤ re tr(cfc f A) - re tr(cfc f B)`.

## Proof outline

Diagonalising `A` and `B` with orthonormal eigenbases `eᴬ`, `eᴮ` and eigenvalues `a`, `b`, the
matrix `Wᵢⱼ := ‖⟪eᴬᵢ, eᴮⱼ⟫‖²` is doubly stochastic (Parseval). Expanding the four traces via
`IsSelfAdjoint.re_trace_cfc_comp_eq_sum` reduces the inequality to the scalar bound

`∑ⱼ f(bⱼ) + ∑ⱼ f'(bⱼ)·((∑ᵢ Wᵢⱼ aᵢ) - bⱼ) ≤ ∑ᵢ f(aᵢ)`,

which follows term-by-term from the tangent-line inequality
`f(bⱼ) + f'(bⱼ)·(aᵢ - bⱼ) ≤ f(aᵢ)` (convexity of `f`) weighted by `Wᵢⱼ ≥ 0`.

## Main results

- `ConvexOn.add_deriv_mul_sub_le`: tangent-line inequality — a convex function lies above its
  tangent line at a point of differentiability.
- `ConvexOn.sum_deriv_doublyStochastic_le`: the scalar generalized-Klein (doubly-stochastic
  convex) bound, the general-`f` analogue of
  `Real.sum_mul_sum_mul_log_le_neg_entropy_of_doubly_stochastic`.
- `IsSelfAdjoint.re_trace_cfc_eq_sum`: `re tr(cfc f T) = ∑ᵢ f(λᵢ)` for self-adjoint `T`.
- `generalized_klein_inequality`: the operator inequality above.
- `ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg_of_generalizedKlein`:
  **Problem 11.1's deduction** — non-negativity of the quantum relative entropy obtained from
  the generalized Klein inequality with `f = x·log x` (cf.
  `ContinuousLinearMap.IsDensityOp.quantumRelativeEntropy_nonneg`, the direct log-route proof).
-/

@[expose] public section

open scoped InnerProductSpace

/-- **Tangent-line inequality**: a convex function lies above its tangent line. If `f` is convex
on `S` and differentiable at `y ∈ S` with derivative `d`, then `f y + d·(x - y) ≤ f x` for every
`x ∈ S`. -/
theorem ConvexOn.add_deriv_mul_sub_le {S : Set ℝ} {f : ℝ → ℝ} {y d : ℝ}
    (hf : ConvexOn ℝ S f) {x : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hd : HasDerivAt f d y) : f y + d * (x - y) ≤ f x := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have h := hf.slope_le_of_hasDerivAt hx hy hlt hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h; linarith
  · subst heq; simp
  · have h := hf.le_slope_of_hasDerivAt hy hx hgt hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h; linarith

/-- **Strict tangent-line inequality**: a strictly convex function lies *strictly* above its
tangent line away from the point of tangency. If `f` is strictly convex on `S` and differentiable
at `y ∈ S` with derivative `d`, then `f y + d·(x - y) < f x` for every `x ∈ S` with `x ≠ y`. The
strict-convexity companion of `ConvexOn.add_deriv_mul_sub_le`. -/
theorem StrictConvexOn.add_deriv_mul_sub_lt {S : Set ℝ} {f : ℝ → ℝ} {y d : ℝ}
    (hf : StrictConvexOn ℝ S f) {x : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y)
    (hd : HasDerivAt f d y) : f y + d * (x - y) < f x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := hf.slope_lt_of_hasDerivAt hx hy hlt hd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at h
    have key : d * (x - y) = -(d * (y - x)) := by ring
    linarith [key, h]
  · have h := hf.lt_slope_of_hasDerivAt hy hx hgt hd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at h
    linarith [h]

/-- **Equality case of the strict tangent-line inequality**: for a strictly convex `f`
differentiable at `y ∈ S`, the tangent line at `y` meets the graph only at `y`. Hence if
`f y + d·(x - y) = f x` for `x ∈ S`, then `x = y`. The engine of the equality condition of
Klein's inequality. -/
theorem StrictConvexOn.eq_of_add_deriv_mul_sub_eq {S : Set ℝ} {f : ℝ → ℝ} {y d : ℝ}
    (hf : StrictConvexOn ℝ S f) {x : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hd : HasDerivAt f d y) (heq : f y + d * (x - y) = f x) : x = y := by
  by_contra hne
  exact absurd heq (ne_of_lt (hf.add_deriv_mul_sub_lt hx hy hne hd))

/-- **Doubly-stochastic residual identity**: the slack in the generalized-Klein bound
`ConvexOn.sum_deriv_doublyStochastic_le` is exactly the doubly-stochastic average of the
tangent-line gaps. For values `a : ι → ℝ`, `b : κ → ℝ`, a doubly-stochastic matrix `W`, and *any*
`f, f' : ℝ → ℝ`,

`(∑ᵢ f(aᵢ)) − ((∑ⱼ f(bⱼ)) + ∑ⱼ f'(bⱼ)·((∑ᵢ Wᵢⱼ aᵢ) − bⱼ))
    = ∑ᵢ ∑ⱼ Wᵢⱼ·(f(aᵢ) − f(bⱼ) − f'(bⱼ)·(aᵢ − bⱼ))`.

A pure algebraic identity (no convexity is used). It is the single source of truth for both the
generalized-Klein bound (`ConvexOn.sum_deriv_doublyStochastic_le`, whose slack is this nonnegative
average when `f` is convex) and — combined with the strict tangent-line inequality — the equality
condition of Klein's inequality. -/
theorem sum_deriv_doublyStochastic_residual_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f f' : ℝ → ℝ} {a : ι → ℝ} {b : κ → ℝ} {W : ι → κ → ℝ}
    (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, W i j = 1) :
    (∑ i, f (a i)) - ((∑ j, f (b j)) + ∑ j, f' (b j) * ((∑ i, W i j * a i) - b j))
      = ∑ i, ∑ j, W i j * (f (a i) - f (b j) - f' (b j) * (a i - b j)) := by
  have hR : ∑ i, ∑ j, W i j * f (a i) = ∑ i, f (a i) :=
    Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hrow i, one_mul]
  have hL : ∑ i, ∑ j, W i j * (f (b j) + f' (b j) * (a i - b j)) =
      (∑ j, f (b j)) + ∑ j, f' (b j) * ((∑ i, W i j * a i) - b j) := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have step : ∀ i, W i j * (f (b j) + f' (b j) * (a i - b j))
        = W i j * f (b j) + (f' (b j) * (W i j * a i) - f' (b j) * b j * W i j) := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hcol j]
    ring
  have expand : ∑ i, ∑ j, W i j * (f (a i) - f (b j) - f' (b j) * (a i - b j))
      = (∑ i, ∑ j, W i j * f (a i)) - ∑ i, ∑ j, W i j * (f (b j) + f' (b j) * (a i - b j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [expand, hR, hL]

/-- **Doubly-stochastic convex (generalized Klein) bound**, scalar form. For a convex `f` with
derivative `f'`, values `a : ι → ℝ` and `b : κ → ℝ` in `S`, and a doubly-stochastic matrix
`W : ι → κ → ℝ` (nonnegative entries, all row sums and column sums equal to `1`),

`(∑ⱼ f(bⱼ)) + ∑ⱼ f'(bⱼ)·((∑ᵢ Wᵢⱼ aᵢ) - bⱼ) ≤ ∑ᵢ f(aᵢ)`.

This is the general-`f` sibling of `Real.sum_mul_sum_mul_log_le_neg_entropy_of_doubly_stochastic`,
and the classical input to the operator generalized Klein inequality via spectral decomposition.
It is the `sum_deriv_doublyStochastic_residual_eq` identity read as an inequality: the residual
`∑ᵢⱼ Wᵢⱼ·(f(aᵢ) − f(bⱼ) − f'(bⱼ)(aᵢ − bⱼ))` is a nonnegative combination of tangent-line gaps
(each `≥ 0` by convexity, each `Wᵢⱼ ≥ 0`). -/
theorem ConvexOn.sum_deriv_doublyStochastic_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {S : Set ℝ} {f f' : ℝ → ℝ} {a : ι → ℝ} {b : κ → ℝ} {W : ι → κ → ℝ}
    (hf : ConvexOn ℝ S f) (haS : ∀ i, a i ∈ S) (hbS : ∀ j, b j ∈ S)
    (hderiv : ∀ j, HasDerivAt f (f' (b j)) (b j))
    (hW : ∀ i j, 0 ≤ W i j) (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, W i j = 1) :
    (∑ j, f (b j)) + ∑ j, f' (b j) * ((∑ i, W i j * a i) - b j) ≤ ∑ i, f (a i) := by
  have hres := sum_deriv_doublyStochastic_residual_eq (f := f) (f' := f') (a := a) (b := b)
    (W := W) hrow hcol
  have hnn : 0 ≤ ∑ i, ∑ j, W i j * (f (a i) - f (b j) - f' (b j) * (a i - b j)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hW i j) (by linarith [hf.add_deriv_mul_sub_le (haS i) (hbS j) (hderiv j)])
  linarith [hres, hnn]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]

/-- **Trace of `cfc f T`, real part**: for self-adjoint `T` with eigenvalues `λᵢ`,
`re tr(cfc f T) = ∑ᵢ f(λᵢ)`. The single-operator specialization of
`IsSelfAdjoint.re_trace_cfc_comp_eq_sum` (composition with the identity, whose diagonal entries
in `T`'s orthonormal eigenbasis are all `1`). -/
theorem IsSelfAdjoint.re_trace_cfc_eq_sum {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (f : ℝ → ℝ) :
    RCLike.re (LinearMap.trace ℂ E (cfc f A).toLinearMap) =
      ∑ i, f (hA.isSymmetric.eigenvalues rfl i) := by
  set eA := hA.isSymmetric.eigenvectorBasis rfl with heA
  have h := hA.re_trace_cfc_comp_eq_sum rfl f (hA.continuousOn_spectrum f) 1
  simp only [ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, LinearMap.comp_id,
    one_apply_eq_self, ← heA] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : inner ℂ (eA i) (eA i) = (1 : ℂ) := by
    rw [(orthonormal_iff_ite (𝕜 := ℂ)).mp eA.orthonormal, ite_eq_left rfl]
  rw [h1]; simp

/-- **Generalized-Klein residual identity** (operator form). For self-adjoint `A, B` and *any*
`f, f' : ℝ → ℝ`, the slack in the generalized Klein inequality equals the doubly-stochastic
average of the tangent-line gaps of `f`:

`re tr(cfc f A) − re tr(cfc f B) − re tr((cfc f' B) ∘ (A − B))
    = ∑ᵢ ∑ⱼ Wᵢⱼ·(f(aᵢ) − f(bⱼ) − f'(bⱼ)·(aᵢ − bⱼ))`,

where `aᵢ`, `bⱼ` are the eigenvalues of `A`, `B` and `Wᵢⱼ = ‖⟪eᴬᵢ, eᴮⱼ⟫‖²` is the doubly-stochastic
overlap matrix of their orthonormal eigenbases (Parseval). This is the single source of truth for
the operator generalized Klein inequality: `generalized_klein_inequality` reads it as a lower
bound (each gap `≥ 0` by convexity), while the equality case of Klein's inequality reads it as an
exact residual — every gap with a nonzero overlap must vanish. No convexity or differentiability of
`f`/`f'` is required here; it is the spectral expansion of the four traces followed by the
algebraic `sum_deriv_doublyStochastic_residual_eq`. -/
theorem generalized_klein_residual_eq {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) (f f' : ℝ → ℝ) :
    RCLike.re (LinearMap.trace ℂ E (cfc f A).toLinearMap) -
        RCLike.re (LinearMap.trace ℂ E (cfc f B).toLinearMap) -
        RCLike.re (LinearMap.trace ℂ E ((cfc f' B).toLinearMap ∘ₗ (A - B).toLinearMap)) =
      ∑ i, ∑ j, ‖inner ℂ (hA.isSymmetric.eigenvectorBasis rfl i)
            (hB.isSymmetric.eigenvectorBasis rfl j)‖ ^ 2 *
          (f (hA.isSymmetric.eigenvalues rfl i) - f (hB.isSymmetric.eigenvalues rfl j) -
            f' (hB.isSymmetric.eigenvalues rfl j) *
              (hA.isSymmetric.eigenvalues rfl i - hB.isSymmetric.eigenvalues rfl j)) := by
  set eA := hA.isSymmetric.eigenvectorBasis rfl with heA
  set eB := hB.isSymmetric.eigenvectorBasis rfl with heB
  have hT3 := hB.re_trace_cfc_comp_eq_sum rfl f' (hB.continuousOn_spectrum f') (A - B)
  rw [← heB] at hT3
  -- diagonal of `A - B` in `B`'s eigenbasis, weighted by the doubly-stochastic overlaps
  have hAB : ∀ j, RCLike.re (inner ℂ (eB j) ((A - B) (eB j))) =
      (∑ i, ‖inner ℂ (eA i) (eB j)‖ ^ 2 * hA.isSymmetric.eigenvalues rfl i)
        - hB.isSymmetric.eigenvalues rfl j := by
    intro j
    rw [sub_apply, inner_sub_right, map_sub]
    congr 1
    · have hsum := hA.cfc_inner_self_eq_sum rfl (id : ℝ → ℝ) (hA.continuousOn_spectrum id) (eB j)
      rw [cfc_id ℝ A] at hsum
      rw [hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [id_eq, ← Complex.ofReal_pow, mul_comm, ← Complex.ofReal_mul]
      exact Complex.ofReal_re _
    · rw [hB.apply_eigenvectorBasis_cast rfl j, inner_smul_right]
      have h1 : inner ℂ (eB j) (eB j) = (1 : ℂ) := by
        rw [(orthonormal_iff_ite (𝕜 := ℂ)).mp eB.orthonormal, ite_eq_left rfl]
      rw [h1, mul_one]; exact Complex.ofReal_re _
  rw [hA.re_trace_cfc_eq_sum f, hB.re_trace_cfc_eq_sum f, hT3]
  simp_rw [hAB]
  rw [sub_sub]
  exact sum_deriv_doublyStochastic_residual_eq
    (fun i => by rw [eB.sum_sq_norm_inner_left (eA i), eA.orthonormal.1 i, one_pow])
    (fun j => by rw [eA.sum_sq_norm_inner_right (eB j), eB.orthonormal.1 j, one_pow])

/-- **Generalized Klein's inequality** (Nielsen–Chuang, Problem 11.1). For self-adjoint
`A, B : E →L[ℂ] E`, a function `f` convex on a set `S` containing the real spectra of `A` and
`B`, with derivative `f'` at each eigenvalue of `B`,

`re tr((cfc f' B) ∘ (A - B)) ≤ re tr(cfc f A) - re tr(cfc f B)`,

i.e. `tr(f(A) - f(B)) ≥ tr((A - B) f'(B))` in N&C's notation (the left-hand trace `tr((cfc f' B)
∘ (A - B))` equals `tr((A - B) f'(B))` by cyclicity of the trace).

Requiring `f` convex only on `S ⊇ spectrum A ∪ spectrum B` (rather than on all of `ℝ`) is the
faithful generality: it accommodates functions such as `x ↦ x·log x`, convex only on `[0, ∞)`,
that drive the entropy corollary below. It is `generalized_klein_residual_eq` read as a lower
bound: the residual is a sum of tangent-line gaps, each `≥ 0` by convexity, weighted by the
nonnegative overlaps `Wᵢⱼ ≥ 0`. -/
theorem generalized_klein_inequality {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {S : Set ℝ} {f f' : ℝ → ℝ} (hf : ConvexOn ℝ S f)
    (hAS : spectrum ℝ A ⊆ S) (hBS : spectrum ℝ B ⊆ S)
    (hderiv : ∀ b ∈ spectrum ℝ B, HasDerivAt f (f' b) b) :
    RCLike.re (LinearMap.trace ℂ E ((cfc f' B).toLinearMap ∘ₗ (A - B).toLinearMap)) ≤
      RCLike.re (LinearMap.trace ℂ E (cfc f A).toLinearMap) -
        RCLike.re (LinearMap.trace ℂ E (cfc f B).toLinearMap) := by
  have hnn : 0 ≤ RCLike.re (LinearMap.trace ℂ E (cfc f A).toLinearMap) -
      RCLike.re (LinearMap.trace ℂ E (cfc f B).toLinearMap) -
      RCLike.re (LinearMap.trace ℂ E ((cfc f' B).toLinearMap ∘ₗ (A - B).toLinearMap)) := by
    rw [generalized_klein_residual_eq hA hB f f']
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (sq_nonneg _)
        (by linarith [hf.add_deriv_mul_sub_le (hAS (hA.eigenvalues_mem_spectrum_real rfl i))
              (hBS (hB.eigenvalues_mem_spectrum_real rfl j))
              (hderiv _ (hB.eigenvalues_mem_spectrum_real rfl j))])
  linarith [hnn]

namespace ContinuousLinearMap.IsDensityOp

/-- **The generalized-Klein slack at `f = x·log x` is the quantum relative entropy.** For density
operators `ρ, σ`,

`re tr(cfc (x·log x) ρ) − re tr(cfc (x·log x) σ) − re tr((cfc (fun x => log x + 1) σ) ∘ (ρ − σ))
    = D(ρ ‖ σ)`.

The shared slack→`D` reduction consumed by both the non-negativity route
(`quantumRelativeEntropy_nonneg_of_generalizedKlein`) and the equality condition
(`quantumRelativeEntropy_eq_zero_iff`): `cfc_log_mul_self` turns each `x·log x` entropy trace into a
`(cfc log ·) ∘ ·` trace, and the `+1` in `f' = log · + 1` contributes `tr(ρ − σ) = 0` (both states
have unit trace), leaving `re tr((cfc log ρ)∘ρ) − re tr((cfc log σ)∘ρ)`, which is
`quantumRelativeEntropy` by definition. Needs only that `ρ, σ` are density operators (no
faithfulness). -/
private theorem quantumRelativeEntropy_eq_generalizedKlein_slack {ρ σ : E →L[ℂ] E}
    (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp) :
    RCLike.re (LinearMap.trace ℂ E (cfc (fun x => x * Real.log x) ρ).toLinearMap) -
        RCLike.re (LinearMap.trace ℂ E (cfc (fun x => x * Real.log x) σ).toLinearMap) -
        RCLike.re (LinearMap.trace ℂ E
          ((cfc (fun x => Real.log x + 1) σ).toLinearMap ∘ₗ (ρ - σ).toLinearMap)) =
      ρ.quantumRelativeEntropy σ := by
  have hBsa := hσ.isPositive.isSelfAdjoint
  -- `tr(cfc (x·log x) T) = tr((cfc log T) ∘ T)`, the entropy-term reduction.
  have hEred : ∀ (T : E →L[ℂ] E), IsSelfAdjoint T →
      RCLike.re (LinearMap.trace ℂ E (cfc (fun x => x * Real.log x) T).toLinearMap) =
        RCLike.re (LinearMap.trace ℂ E ((cfc Real.log T).toLinearMap ∘ₗ T.toLinearMap)) := by
    intro T hT; rw [← hT.cfc_log_mul_self, ContinuousLinearMap.toLinearMap_mul]; rfl
  -- `f'(σ) = log σ + 1`.
  have hf'cfc : cfc (fun x => Real.log x + 1) σ = cfc Real.log σ + 1 := by
    rw [cfc_add σ Real.log (fun _ => 1) (hBsa.continuousOn_spectrum _)
      (hBsa.continuousOn_spectrum _), cfc_const_one ℝ σ]
  have hρtr : RCLike.re (LinearMap.trace ℂ E ρ.toLinearMap) = 1 := by rw [hρ.trace_eq_one]; simp
  have hσtr : RCLike.re (LinearMap.trace ℂ E σ.toLinearMap) = 1 := by rw [hσ.trace_eq_one]; simp
  have op_eq : (cfc (fun x => Real.log x + 1) σ).toLinearMap ∘ₗ (ρ - σ).toLinearMap =
      ((cfc Real.log σ).toLinearMap ∘ₗ ρ.toLinearMap
        - (cfc Real.log σ).toLinearMap ∘ₗ σ.toLinearMap) + (ρ.toLinearMap - σ.toLinearMap) := by
    rw [hf'cfc, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_one,
      ContinuousLinearMap.toLinearMap_sub, LinearMap.add_comp, Module.End.one_eq_id,
          LinearMap.id_comp,
      LinearMap.comp_sub]
  -- The `+1` contributes `tr(ρ − σ) = 0`.
  have E3 : RCLike.re (LinearMap.trace ℂ E
        ((cfc (fun x => Real.log x + 1) σ).toLinearMap ∘ₗ (ρ - σ).toLinearMap)) =
      RCLike.re (LinearMap.trace ℂ E ((cfc Real.log σ).toLinearMap ∘ₗ ρ.toLinearMap))
        - RCLike.re (LinearMap.trace ℂ E ((cfc Real.log σ).toLinearMap ∘ₗ σ.toLinearMap)) := by
    rw [op_eq]; simp only [map_add, map_sub]; rw [hρtr, hσtr]; ring
  rw [hEred ρ hρ.isPositive.isSelfAdjoint, hEred σ hBsa, E3,
    ContinuousLinearMap.quantumRelativeEntropy_def]
  ring

/-! ### Non-faithful Klein's inequality under the support condition

Klein's inequality `D(ρ ‖ σ) ≥ 0` (and its equality condition `= 0 ↔ ρ = σ`) needs only the
**support condition** `supp ρ ⊆ supp σ` (`HasSupportLE ρ σ`, i.e. `ker σ ≤ ker ρ`) on `σ`, *not*
full faithfulness (`IsStrictlyPositive σ`). Faithfulness (`hσ_pos`) is used in exactly one place: to
get the tangent-line inequality of `x ↦ x·log x` at each eigenvalue `bⱼ` of `σ` (`x·log x` is not
differentiable at `0`). So we prove the support-condition versions here and recover the faithful
`quantumRelativeEntropy_nonneg_of_generalizedKlein` / `quantumRelativeEntropy_eq_zero_iff` (N&C
Problem 11.1 / Theorem 11.7) below as one-line corollaries. The residual identity
`generalized_klein_residual_eq`
holds with no faithfulness at all, writing `D(ρ ‖ σ) = Σᵢⱼ Wᵢⱼ·gapᵢⱼ` for the tangent-line gaps
`gapᵢⱼ`. The support condition kills exactly the ill-defined `bⱼ = 0` terms: if `bⱼ = 0` and the
overlap `⟪eᵨᵢ, eₛⱼ⟫ ≠ 0`, then `eₛⱼ ∈ ker σ ⊆ ker ρ`, so `ρ (eₛⱼ) = 0` forces `aᵢ = 0 = bⱼ` and the
gap vanishes; elsewhere (`bⱼ > 0`) the tangent-line inequality applies as before. This is the exact
generality Nielsen & Chuang need for Theorem 11.9, whose pinched state `Σᵢ Pᵢ ρ Pᵢ` is generally
rank-deficient but always satisfies the support condition. -/

/-- **The support condition kills the zero-eigenvalue block.** If `HasSupportLE ρ σ` and `bⱼ = 0`
is a zero eigenvalue of `σ` whose eigenvector `eₛⱼ` overlaps `ρ`'s eigenvector `eᵨᵢ`
(`⟪eᵨᵢ, eₛⱼ⟫ ≠ 0`), then the corresponding eigenvalue `aᵢ` of `ρ` vanishes. Since `bⱼ = 0` means
`eₛⱼ ∈ ker σ ⊆ ker ρ`, we have `ρ (eₛⱼ) = 0`; pairing with `eᵨᵢ` (using `ρ (eᵨᵢ) = aᵢ eᵨᵢ` and
self-adjointness) gives `aᵢ ⟪eᵨᵢ, eₛⱼ⟫ = 0`, so `aᵢ = 0`. -/
private theorem eigenvalue_eq_zero_of_hasSupportLE {ρ σ : E →L[ℂ] E}
    (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp) (hsupp : HasSupportLE ρ σ)
    {i j : Fin (Module.finrank ℂ E)}
    (hbj : hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl j = 0)
    (hij : inner ℂ (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl i)
      (hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl j) ≠ 0) :
    hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl i = 0 := by
  -- `eₛⱼ ∈ ker σ ⊆ ker ρ`, so `ρ (eₛⱼ) = 0`.
  have hker : hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl j
      ∈ LinearMap.ker (σ : E →ₗ[ℂ] E) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      hσ.isPositive.isSelfAdjoint.apply_eigenvectorBasis_cast rfl j, hbj]
    simp
  have hρ0 : ρ (hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl j) = 0 := by
    have h := hsupp hker
    rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at h
  -- `aᵢ · ⟪eᵨᵢ, eₛⱼ⟫ = ⟪eᵨᵢ, ρ (eₛⱼ)⟫ = 0`.
  have hcoef : (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl i : ℂ) *
      inner ℂ (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl i)
        (hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl j) = 0 := by
    have h1 := ContinuousLinearMap.adjoint_inner_left ρ
      (hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl j)
      (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl i)
    rw [hρ.isPositive.isSelfAdjoint.adjoint_eq,
      hρ.isPositive.isSelfAdjoint.apply_eigenvectorBasis_cast rfl i, inner_smul_left,
      Complex.conj_ofReal, hρ0, inner_zero_right] at h1
    exact h1
  rcases mul_eq_zero.mp hcoef with h | h
  · exact_mod_cast h
  · exact absurd h hij

/-- **Each generalized-Klein term is nonnegative under the support condition.** For density
operators `ρ, σ` with `HasSupportLE ρ σ`, every summand `Wᵢⱼ·gapᵢⱼ` of the residual sum
`generalized_klein_residual_eq` (at `f = x·log x`, `f' = log x + 1`) is `≥ 0`: where `bⱼ > 0` the
tangent-line inequality gives `gapᵢⱼ ≥ 0` (`ConvexOn.add_deriv_mul_sub_le`); where `bⱼ = 0` the
support condition forces the term to vanish (`eigenvalue_eq_zero_of_hasSupportLE`). -/
private theorem gap_term_nonneg {ρ σ : E →L[ℂ] E}
    (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp) (hsupp : HasSupportLE ρ σ)
    (i j : Fin (Module.finrank ℂ E)) :
    0 ≤ ‖inner ℂ (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl i)
          (hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl j)‖ ^ 2 *
        (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl i *
            Real.log (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl i) -
          hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl j *
            Real.log (hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl j) -
          (Real.log (hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl j) + 1) *
            (hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl i -
              hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl j)) := by
  set a := hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl with ha
  set b := hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvalues rfl with hb
  set eA := hρ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl with heA
  set eB := hσ.isPositive.isSelfAdjoint.isSymmetric.eigenvectorBasis rfl with heB
  have hbnn : (0 : ℝ) ≤ b j := hσ.eigenvalues_nonneg rfl j
  rcases eq_or_lt_of_le hbnn with hb0 | hbpos
  · -- `bⱼ = 0`: either the overlap vanishes, or `aᵢ = 0` and the whole gap collapses.
    rcases eq_or_ne (inner ℂ (eA i) (eB j)) 0 with hw | hw
    · rw [hw]; simp
    · have hai : a i = 0 := eigenvalue_eq_zero_of_hasSupportLE hρ hσ hsupp hb0.symm hw
      rw [hai, ← hb0]; simp
  · -- `bⱼ > 0`: the tangent-line inequality of `x·log x` at `bⱼ`.
    refine mul_nonneg (sq_nonneg _) ?_
    have hann : (0 : ℝ) ≤ a i := hρ.eigenvalues_nonneg rfl i
    have htan := Real.strictConvexOn_mul_log.convexOn.add_deriv_mul_sub_le
      (Set.mem_Ici.mpr hann) (Set.mem_Ici.mpr hbpos.le) (Real.hasDerivAt_mul_log hbpos.ne')
    beta_reduce at htan
    linarith [htan]

/-- **Klein's inequality under the support condition** (non-faithful `σ`). For density operators
`ρ, σ : E →L[ℂ] E` with the support condition `supp ρ ⊆ supp σ` (`HasSupportLE ρ σ`, i.e.
`ker σ ≤ ker ρ`), the quantum relative entropy is non-negative:

`0 ≤ D(ρ ‖ σ)`,

even when `σ` is rank-deficient. This is the exact generality behind Nielsen & Chuang's Theorem 11.9
(projective measurements increase entropy), where `σ = Σᵢ Pᵢ ρ Pᵢ` is generally not faithful.

The full-faithfulness version `quantumRelativeEntropy_nonneg_of_generalizedKlein` is the special
case `ker σ = ⊥`. The proof is the residual identity `generalized_klein_residual_eq` (via the shared
slack reduction `quantumRelativeEntropy_eq_generalizedKlein_slack`) with every term nonnegative
(`gap_term_nonneg`); the support condition, rather than faithfulness, discharges the zero-eigenvalue
block. -/
theorem quantumRelativeEntropy_nonneg_of_hasSupportLE {ρ σ : E →L[ℂ] E}
    (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp) (hsupp : HasSupportLE ρ σ) :
    0 ≤ ρ.quantumRelativeEntropy σ := by
  rw [← quantumRelativeEntropy_eq_generalizedKlein_slack hρ hσ,
    generalized_klein_residual_eq hρ.isPositive.isSelfAdjoint hσ.isPositive.isSelfAdjoint
      (fun x => x * Real.log x) (fun x => Real.log x + 1)]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => gap_term_nonneg hρ hσ hsupp i j

/-- **Klein's inequality, equality condition, under the support condition** (non-faithful `σ`;
Nielsen & Chuang Theorem 11.7 relaxed as needed for Theorem 11.9). For density operators `ρ, σ` with
`supp ρ ⊆ supp σ` (`HasSupportLE ρ σ`),

`D(ρ ‖ σ) = 0 ↔ ρ = σ`.

The full-faithfulness version `quantumRelativeEntropy_eq_zero_iff` is the special case `ker σ = ⊥`;
this replaces faithfulness of `σ` by the support condition. The reverse direction is
`quantumRelativeEntropy_self`. Forward: the residual identity writes `D(ρ ‖ σ)` as the
doubly-stochastic average `Σᵢⱼ Wᵢⱼ·gapᵢⱼ ≥ 0` of the tangent-line gaps; `D = 0` with the nonnegative
terms (`gap_term_nonneg`) forces each `Wᵢⱼ·gapᵢⱼ = 0`. Where the overlap `⟪eᵨᵢ, eₛⱼ⟫ ≠ 0`: if
`bⱼ > 0` the strict tangent-line inequality gives `aᵢ = bⱼ`, and if `bⱼ = 0` the support condition
gives `aᵢ = 0 = bⱼ` (`eigenvalue_eq_zero_of_hasSupportLE`). Either way `aᵢ = bⱼ` on the nonzero
overlaps, so `ρ` and `σ` agree on `σ`'s eigenbasis, hence `ρ = σ`. -/
theorem quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE {ρ σ : E →L[ℂ] E}
    (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp) (hsupp : HasSupportLE ρ σ) :
    ρ.quantumRelativeEntropy σ = 0 ↔ ρ = σ := by
  refine ⟨fun hzero => ?_, fun h => h ▸ ContinuousLinearMap.quantumRelativeEntropy_self ρ⟩
  have hAsa := hρ.isPositive.isSelfAdjoint
  have hBsa := hσ.isPositive.isSelfAdjoint
  -- The residual sum vanishes (`D = 0` via the shared slack reduction + residual identity).
  have hZ : ∑ i, ∑ j, ‖inner ℂ (hAsa.isSymmetric.eigenvectorBasis rfl i)
        (hBsa.isSymmetric.eigenvectorBasis rfl j)‖ ^ 2 *
        (hAsa.isSymmetric.eigenvalues rfl i * Real.log (hAsa.isSymmetric.eigenvalues rfl i) -
          hBsa.isSymmetric.eigenvalues rfl j * Real.log (hBsa.isSymmetric.eigenvalues rfl j) -
          (Real.log (hBsa.isSymmetric.eigenvalues rfl j) + 1) *
            (hAsa.isSymmetric.eigenvalues rfl i - hBsa.isSymmetric.eigenvalues rfl j)) = 0 := by
    have hres := generalized_klein_residual_eq hAsa hBsa
      (fun x => x * Real.log x) (fun x => Real.log x + 1)
    have hSL0 := (quantumRelativeEntropy_eq_generalizedKlein_slack hρ hσ).trans hzero
    rw [hres] at hSL0
    exact hSL0
  set eA := hAsa.isSymmetric.eigenvectorBasis rfl with heA
  set eB := hBsa.isSymmetric.eigenvectorBasis rfl with heB
  set a := hAsa.isSymmetric.eigenvalues rfl with ha
  set b := hBsa.isSymmetric.eigenvalues rfl with hb
  -- Each term of the nonnegative residual sum vanishes.
  have hterms : ∀ i j, ‖inner ℂ (eA i) (eB j)‖ ^ 2 *
      (a i * Real.log (a i) - b j * Real.log (b j) - (Real.log (b j) + 1) * (a i - b j)) = 0 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ ∑ j, ‖inner ℂ (eA i) (eB j)‖ ^ 2 *
        (a i * Real.log (a i) - b j * Real.log (b j) - (Real.log (b j) + 1) * (a i - b j)) :=
      fun i _ => Finset.sum_nonneg fun j _ => gap_term_nonneg hρ hσ hsupp i j
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hZ i (Finset.mem_univ i)
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => gap_term_nonneg hρ hσ hsupp i j)).mp h1 j (Finset.mem_univ j)
  -- Where the overlap is nonzero the eigenvalues coincide (strict convexity or support condition).
  have heq_val : ∀ i j, inner ℂ (eA i) (eB j) ≠ (0 : ℂ) → a i = b j := by
    intro i j hij
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ b j from hσ.eigenvalues_nonneg rfl j) with hb0 | hbpos
    · rw [← hb0]
      exact eigenvalue_eq_zero_of_hasSupportLE hρ hσ hsupp hb0.symm hij
    · have hW : ‖inner ℂ (eA i) (eB j)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hij)
      have hgap0 : a i * Real.log (a i) - b j * Real.log (b j)
          - (Real.log (b j) + 1) * (a i - b j) = 0 :=
        (mul_eq_zero.mp (hterms i j)).resolve_left hW
      exact Real.strictConvexOn_mul_log.eq_of_add_deriv_mul_sub_eq
        (Set.mem_Ici.mpr (show (0 : ℝ) ≤ a i from hρ.eigenvalues_nonneg rfl i))
        (Set.mem_Ici.mpr hbpos.le) (Real.hasDerivAt_mul_log hbpos.ne')
        (by linear_combination -hgap0)
  -- `ρ` and `σ` agree on the eigenbasis `eB`, hence coincide.
  have hagree : ∀ j, ρ (eB j) = σ (eB j) := by
    intro j
    have hσj : σ (eB j) = (b j : ℂ) • eB j := hBsa.apply_eigenvectorBasis_cast rfl j
    have hρj : (ρ : E →ₗ[ℂ] E) (eB j) = ∑ i, (a i : ℂ) • inner ℂ (eA i) (eB j) • eA i :=
      hAsa.isSymmetric.spectral_sum_apply rfl (eB j)
    have hterm : ∀ i, (a i : ℂ) • inner ℂ (eA i) (eB j) • eA i
        = (b j : ℂ) • inner ℂ (eA i) (eB j) • eA i := by
      intro i
      by_cases hz : inner ℂ (eA i) (eB j) = (0 : ℂ)
      · rw [hz]; simp
      · rw [heq_val i j hz]
    calc ρ (eB j) = (ρ : E →ₗ[ℂ] E) (eB j) := rfl
      _ = ∑ i, (a i : ℂ) • inner ℂ (eA i) (eB j) • eA i := hρj
      _ = ∑ i, (b j : ℂ) • inner ℂ (eA i) (eB j) • eA i := Finset.sum_congr rfl fun i _ => hterm i
      _ = (b j : ℂ) • ∑ i, inner ℂ (eA i) (eB j) • eA i := by rw [Finset.smul_sum]
      _ = (b j : ℂ) • eB j := by
          congr 1
          simp_rw [← OrthonormalBasis.repr_apply_apply]
          exact eA.sum_repr (eB j)
      _ = σ (eB j) := hσj.symm
  exact ContinuousLinearMap.coe_injective
    (Module.Basis.ext eB.toBasis fun j => by simpa using hagree j)

/-- The support condition holds unconditionally for a faithful `σ`: full-rank (`hσ_pos`) means
`σ` is invertible (`0 ∉ spectrum ℝ σ`), hence strictly positive, hence `ker σ = ⊥ ≤ ker ρ`. The
bridge specializing the support-condition Klein lemmas to the faithful case. -/
private theorem hasSupportLE_of_eigenvalues_pos {ρ σ : E →L[ℂ] E} (hσ : σ.IsDensityOp)
    (hσ_pos : ∀ j, 0 < hσ.isSymmetric.eigenvalues rfl j) : HasSupportLE ρ σ :=
  HasSupportLE.of_isStrictlyPositive (hσ.isStrictlyPositive
    ((spectrum.zero_notMem_iff ℝ).mp
      (hσ.isPositive.isSelfAdjoint.zero_notMem_spectrum_real_of_eigenvalues_pos rfl hσ_pos)))

/-- **Non-negativity of the quantum relative entropy, via the generalized Klein inequality**
(Nielsen–Chuang, Problem 11.1: *"use this result to show that the relative entropy is
non-negative"*). For density operators `ρ, σ` with `σ`'s eigenvalues all positive, `0 ≤ D(ρ ‖ σ)`.

The faithful special case of `quantumRelativeEntropy_nonneg_of_hasSupportLE`: a faithful `σ` has
trivial kernel, so the support condition holds unconditionally (`hasSupportLE_of_eigenvalues_pos`).
Statement-identical to the direct log-route `quantumRelativeEntropy_nonneg`; kept as the explicit
generalized-Klein derivation (Problem 11.1). -/
theorem quantumRelativeEntropy_nonneg_of_generalizedKlein {ρ σ : E →L[ℂ] E}
    (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp)
    (hσ_pos : ∀ j, 0 < hσ.isSymmetric.eigenvalues rfl j) :
    0 ≤ ρ.quantumRelativeEntropy σ :=
  quantumRelativeEntropy_nonneg_of_hasSupportLE hρ hσ (hasSupportLE_of_eigenvalues_pos hσ hσ_pos)

/-- **Klein's inequality, equality condition** (Nielsen–Chuang, Theorem 11.7). For density
operators `ρ, σ` with `σ` faithful (all eigenvalues of `σ` strictly positive), the quantum relative
entropy vanishes iff the states coincide:

`D(ρ ‖ σ) = 0 ↔ ρ = σ`.

Together with `quantumRelativeEntropy_nonneg` this is the full content of Klein's inequality:
`D(ρ ‖ σ) ≥ 0`, with equality iff `ρ = σ`.

The faithful special case of `quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE`: a faithful `σ`
has trivial kernel, so the support condition holds unconditionally
(`hasSupportLE_of_eigenvalues_pos`). Only `σ` need be faithful; `ρ` may be rank-deficient. -/
theorem quantumRelativeEntropy_eq_zero_iff {ρ σ : E →L[ℂ] E}
    (hρ : ρ.IsDensityOp) (hσ : σ.IsDensityOp)
    (hσ_pos : ∀ j, 0 < hσ.isSymmetric.eigenvalues rfl j) :
    ρ.quantumRelativeEntropy σ = 0 ↔ ρ = σ :=
  quantumRelativeEntropy_eq_zero_iff_of_hasSupportLE hρ hσ
    (hasSupportLE_of_eigenvalues_pos hσ hσ_pos)

end ContinuousLinearMap.IsDensityOp
