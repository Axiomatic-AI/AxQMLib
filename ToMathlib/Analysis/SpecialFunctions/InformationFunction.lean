/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Axiomatic characterization of the information function

An *information function* `I : ℝ → ℝ` assigns to an event of probability `p` a number `I p`
measuring "how much information" the event's occurrence conveys. Following the intuitive
requirements one might impose on such a measure (Nielsen & Chuang, *Quantum Computation and
Quantum Information*, Exercise 11.2, p. 501), we ask that

* `I p` depends only on the probability `p` (built into the type `I : ℝ → ℝ`);
* `I` is smooth (here weakened to differentiability, giving a stronger conclusion);
* `I (p * q) = I p + I q` for `p, q > 0` (the information of two independent events adds).

The multiplicative-to-additive functional equation, together with any regularity, forces `I` to
be a constant multiple of the logarithm. This is Cauchy's logarithmic functional equation: the
logarithm is, up to a scalar, the unique differentiable solution.

## Main results

* `Real.exists_const_mul_log_of_map_mul_eq_add`: a differentiable function on the positive reals
  satisfying `I (p * q) = I p + I q` equals `k * Real.log` for some constant `k`.
* `Real.sum_mul_eq_neg_mul_entropy_of_eq_const_mul_log`: consequently the average information gain
  `∑ i, p i * I (p i)` over a distribution `p` with `I p = k * Real.log p` equals `-k` times the
  Shannon entropy `Real.entropy p`, exhibiting the Shannon entropy as the essentially unique such
  average measure of information.

## Implementation notes

The functional equation is imposed for all `p, q > 0`, exactly as Nielsen & Chuang state axiom (3)
("`I (p q) = I p + I q` when `p, q > 0`"), and the conclusion is drawn on all of `(0, ∞)`; the
restriction to probabilities `p ∈ (0, 1]` — the physically meaningful domain — is a special case.
Smoothness is weakened to differentiability: assuming less regularity yields a strictly more
general theorem that still covers the smooth case of the exercise.

The proof differentiates `q ↦ I (p * q) = I p + I q` at `q = 1` to get `p * I' p = I' 1`, so
`I' p = k / p` with `k := deriv I 1`; then `x ↦ I x - k * Real.log x` has vanishing derivative on
the connected open set `(0, ∞)` and is therefore constant, its value pinned to `I 1 = 0`.
-/

open Set Filter Topology

namespace Real

public section

/-- **Cauchy's logarithmic functional equation.** A function `I : ℝ → ℝ` that is differentiable at
every positive real and satisfies `I (p * q) = I p + I q` for all `p, q > 0` is a constant multiple
of the logarithm: there is a constant `k` with `I p = k * Real.log p` for every `p > 0`.

This is the axiomatic justification (Nielsen & Chuang, Exercise 11.2) for defining information as a
logarithm of probability; the constant `k` is `deriv I 1`. -/
theorem exists_const_mul_log_of_map_mul_eq_add {I : ℝ → ℝ}
    (hdiff : ∀ x, 0 < x → DifferentiableAt ℝ I x)
    (hmul : ∀ p q, 0 < p → 0 < q → I (p * q) = I p + I q) :
    ∃ k, ∀ p, 0 < p → I p = k * Real.log p := by
  -- Evaluating the functional equation at `p = q = 1` pins `I 1 = 0`.
  have hI1 : I 1 = 0 := by
    have h := hmul 1 1 one_pos one_pos
    simp only [mul_one] at h
    linarith
  set k := deriv I 1 with hk
  -- Step 1: differentiating `q ↦ I (p * q) = I p + I q` at `q = 1` gives `deriv I p = k / p`.
  have hderiv : ∀ p, 0 < p → HasDerivAt I (k / p) p := by
    intro p hp
    have hIp : HasDerivAt I (deriv I p) p := (hdiff p hp).hasDerivAt
    have hL : HasDerivAt (fun q => I (p * q)) (deriv I p * p) 1 := by
      have h1 : HasDerivAt (fun q => p * q) p 1 := by
        simpa using (hasDerivAt_id (1 : ℝ)).const_mul p
      have h2 : HasDerivAt I (deriv I p) (p * 1) := by rw [mul_one]; exact hIp
      simpa [Function.comp_def] using HasDerivAt.comp 1 h2 h1
    have hEq : (fun q => I (p * q)) =ᶠ[𝓝 (1 : ℝ)] (fun q => I p + I q) := by
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with q hq
      exact hmul p q hp hq
    have hL' : HasDerivAt (fun q => I p + I q) (deriv I p * p) 1 :=
      hL.congr_of_eventuallyEq hEq.symm
    have hR : HasDerivAt (fun q => I p + I q) (deriv I 1) 1 :=
      ((hdiff 1 one_pos).hasDerivAt).const_add (I p)
    have hpp : deriv I p * p = k := hL'.unique hR
    have hval : deriv I p = k / p := by
      rw [eq_div_iff (ne_of_gt hp)]; exact hpp
    rw [← hval]; exact hIp
  -- Step 2: `g x = I x - k * log x` has zero derivative on `(0, ∞)`, hence is constant there.
  set g := fun x => I x - k * Real.log x with hg_def
  have hg : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g 0 x := by
    intro x hx
    have h1 : HasDerivAt I (k / x) x := hderiv x hx
    have h2 : HasDerivAt (fun y => k * Real.log y) (k * x⁻¹) x :=
      (Real.hasDerivAt_log (ne_of_gt hx)).const_mul k
    have hs := h1.fun_sub h2
    simpa [hg_def, div_eq_mul_inv] using hs
  obtain ⟨a, ha⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun x hx => (hg x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hg x hx).deriv)
  -- The constant value is `g 1 = I 1 - k * log 1 = 0`.
  refine ⟨k, fun p hp => ?_⟩
  have hpe : g p = g 1 := by rw [ha p hp, ha 1 (by norm_num)]
  simp only [hg_def, hI1, Real.log_one, mul_zero, sub_zero] at hpe
  linarith [hpe]

/-- Given an information function of the form `I p = k * Real.log p` on the positive reals, the
average information gained from a distribution `p` — the expectation `∑ i, p i * I (p i)` — equals
`-k` times the Shannon entropy `Real.entropy p`. Combined with
`Real.exists_const_mul_log_of_map_mul_eq_add`, this exhibits the Shannon entropy as the essentially
unique average measure of information (Nielsen & Chuang, Exercise 11.2). -/
theorem sum_mul_eq_neg_mul_entropy_of_eq_const_mul_log {ι : Type*} [Fintype ι]
    {I : ℝ → ℝ} {k : ℝ} (hI : ∀ p, 0 < p → I p = k * Real.log p)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    ∑ i, p i * I (p i) = -k * Real.entropy p := by
  calc ∑ i, p i * I (p i)
      = ∑ i, k * (p i * Real.log (p i)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hI (p i) (hp i)]; ring
    _ = k * ∑ i, p i * Real.log (p i) := by rw [Finset.mul_sum]
    _ = -k * Real.entropy p := by rw [Real.entropy_eq_neg_sum_mul_log]; ring

end

end Real
