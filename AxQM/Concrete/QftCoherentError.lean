/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Concrete: coherent phase accumulation and the product-state distance bound

Toward the faithful `Ω(n²/p(n))` lower bound of Nielsen & Chuang, Exercise 5.6, this file supplies
the **analytic heart** of the argument, isolated from the gate-level circuit: the distance between
two *product states* that differ, wire-by-wire, only by a phase.

The Figure 5.1 QFT circuit maps a computational-basis input to the product state
`(1/√2ⁿ) ∏ₛ (φₛ)^{kₛ}` (the block-phase state `qftPartialState n a n`); perturbing every
controlled-`Rₖ` gate by a common `+Δ` leaves the circuit's output a product state of the *same*
shape but with each wire phase `φₛ` multiplied by an extra `e^{iεₛ}` (`εₛ` = the accumulated phase
error on wire `s`). Because the individual errors all share the sign of `Δ`, they **add
coherently**: the two product states pick up a *relative* global phase `θ = (∑ₛ εₛ)/2` that is
`Θ(n²·Δ)`, and this coherent phase — not the (higher-order) per-wire dephasing — sets the distance.
That is the mechanism separating the QFT's `Θ(n²/p(n))` from the naive per-gate `Θ(Δ)`.

## What is formalised

* `phaseProdVec n φ` — the (unnormalised) **phase-product vector** `i ↦ ∏ₛ (φₛ)^{kₛ}`,
  `k = enc.symm i` the little-endian bits of `i` (the `2ⁿ` amplitudes of `⊗ₛ (|0⟩ + φₛ|1⟩)`).
* `phaseProdVec_dotProduct` — the **factorised inner product**
  `∑ᵢ conj(pv φ i)·pv ψ i = ∏ₛ (1 + conj(φₛ)·ψₛ)`: summing over all `2ⁿ` basis strings distributes
  into a product over wires (the tensor-product overlap). This is the one combinatorial input.
* `phaseProdVec_sq_sum` — for unit phases, `∑ᵢ ‖pv φ i‖² = 2ⁿ` (so `(1/√2ⁿ)·pv φ` is a unit vector).
* `phaseProdVec_scaled_dist_ge` — the **coherent-accumulation lower bound**: for unit phases `φ`
  and real per-wire errors `ε`, in the small-error regime `0 ≤ ∑ₛ εₛ ≤ π`, the normalised product
  states `(1/√2ⁿ)·pv φ` and `(1/√2ⁿ)·pv (φ·e^{iε})` are separated by

  `‖·‖ = √(∑ᵢ ‖…‖²) ≥ (∑ₛ εₛ)/π`.

  The proof: the squared distance is `2(1 − P·cos θ)` with `θ = (∑εₛ)/2` and `P = ∏ₛ cos(εₛ/2)`;
  since `P ≤ 1` and `cos θ ≥ 0` in the regime, this is `≥ 2(1 − cos θ) = 4 sin²(θ/2)`, and Jordan's
  inequality `sin x ≥ (2/π)x` (`Real.mul_le_sin`) turns `2 sin(θ/2)` into the linear `(∑εₛ)/π`.

The `(∑ₛ εₛ)/π` shape is exactly what the perturbed QFT circuit feeds: with `εₛ = (n−1−s)·Δ` on the
all-ones input, `∑ₛ εₛ = Δ·n(n−1)/2`, so the distance is `≥ n(n−1)Δ/(2π) = Ω(n²Δ)` — the faithful
lower bound of Exercise 5.6. The regime `∑εₛ ≤ π` is the exercise's small-error regime
(`E ≤ 2` always, so a `Θ(n²Δ)` scaling can only hold where `n²Δ` stays bounded).

## Setting

Every statement is about complex vectors `Fin (2ⁿ) → ℂ`, with the little-endian encoding
`finFunctionFinEquiv`, and real/complex analysis. It is used in Exercise 5.6.
-/

namespace AxQM.Concrete

open scoped BigOperators
open Complex

/-- **Half-angle identity** `1 + e^{ix} = 2·cos(x/2)·e^{ix/2}`. Writing `e^{ix} = e^{ix/2}·e^{ix/2}`
and expanding `e^{ix/2} = cos(x/2) + i·sin(x/2)` (`Complex.exp_mul_I`), the `1 + …` collapses via
the Pythagorean identity `sin²(x/2) + cos²(x/2) = 1`. The factor `2·cos(x/2)·e^{ix/2}` is the
standard polar form of `1 + e^{ix}`, used to read the modulus and argument of `∏ₛ(1 + e^{iεₛ})`. -/
theorem one_add_exp_mul_I (x : ℝ) :
    (1 : ℂ) + Complex.exp (↑x * I) = 2 * (Real.cos (x / 2) : ℂ) * Complex.exp (↑(x / 2) * I) := by
  have h2 : (↑x * I) = (↑(x / 2) * I) + (↑(x / 2) * I) := by push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_mul_I, Complex.ofReal_cos]
  push_cast
  have hp := Complex.sin_sq_add_cos_sq ((x : ℂ) / 2)
  have hI := Complex.I_sq
  linear_combination (-(1 : ℂ)) * hp + (Complex.sin ((x : ℂ) / 2)) ^ 2 * hI

/-- **The phase-product (tensor) vector.** For per-wire phases `φ : Fin n → ℂ`, `phaseProdVec n φ`
is the `2ⁿ`-dimensional vector whose `i`-th amplitude is `∏ₛ (φₛ)^{kₛ}`, where `k = enc.symm i` are
the little-endian bits of the basis index `i` (`finFunctionFinEquiv`). These are the amplitudes of
the unnormalised product state `⊗ₛ (|0⟩ + φₛ|1⟩)`; the QFT circuit's output on a basis input is
`(1/√2ⁿ)` times such a vector. -/
noncomputable def phaseProdVec (n : ℕ) (φ : Fin n → ℂ) : Fin (2 ^ n) → ℂ :=
  fun i => ∏ s : Fin n, φ s ^ (finFunctionFinEquiv.symm i s : ℕ)

/-- The amplitude of `phaseProdVec n φ` at the encoded basis index `enc k` is the wire product
`∏ₛ (φₛ)^{kₛ}` (unfolding the encoding round-trip `enc.symm (enc k) = k`). -/
theorem phaseProdVec_apply_encode (n : ℕ) (φ : Fin n → ℂ) (k : Fin n → Fin 2) :
    phaseProdVec n φ (finFunctionFinEquiv k) = ∏ s, φ s ^ (k s : ℕ) := by
  simp only [phaseProdVec, Equiv.symm_apply_apply]

/-- **The factorised inner product of two phase-product vectors.** Summing the pointwise product
`conj(pv φ i)·pv ψ i` over all `2ⁿ` basis strings distributes into a product over the `n` wires:

`∑ᵢ conj(pv φ i)·pv ψ i = ∏ₛ (1 + conj(φₛ)·ψₛ)`.

This is the tensor-product overlap `⟨⊗ₛ(|0⟩+φₛ|1⟩), ⊗ₛ(|0⟩+ψₛ|1⟩)⟩`. Proved by reindexing the sum
over `Fin (2ⁿ)` to a sum over bit strings `Fin n → Fin 2` and applying `Finset.prod_univ_sum`
(`∏ₛ ∑_b xₛ^b = ∑_k ∏ₛ xₛ^{kₛ}`) with `xₛ = conj(φₛ)ψₛ` and `∑_{b:Fin 2} xₛ^b = 1 + xₛ`. -/
theorem phaseProdVec_dotProduct (n : ℕ) (φ ψ : Fin n → ℂ) :
    ∑ i, (starRingEnd ℂ) (phaseProdVec n φ i) * phaseProdVec n ψ i
      = ∏ s, (1 + (starRingEnd ℂ) (φ s) * ψ s) := by
  rw [← Equiv.sum_comp finFunctionFinEquiv
        (fun i => (starRingEnd ℂ) (phaseProdVec n φ i) * phaseProdVec n ψ i)]
  have step : ∀ k : Fin n → Fin 2,
      (starRingEnd ℂ) (phaseProdVec n φ (finFunctionFinEquiv k))
          * phaseProdVec n ψ (finFunctionFinEquiv k)
        = ∏ s, ((starRingEnd ℂ) (φ s) * ψ s) ^ (k s : ℕ) := by
    intro k
    rw [phaseProdVec_apply_encode, phaseProdVec_apply_encode, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← mul_pow]
  have hprod : ∏ s, (1 + (starRingEnd ℂ) (φ s) * ψ s)
      = ∑ k : Fin n → Fin 2, ∏ s, ((starRingEnd ℂ) (φ s) * ψ s) ^ (k s : ℕ) := by
    have hfac : ∀ s : Fin n, (1 + (starRingEnd ℂ) (φ s) * ψ s)
        = ∑ b : Fin 2, ((starRingEnd ℂ) (φ s) * ψ s) ^ (b : ℕ) := by
      intro s; rw [Fin.sum_univ_two]; simp
    rw [Finset.prod_congr rfl (fun s _ => hfac s), Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [step]
  rw [hprod]

/-- **The squared norm of a unit-phase product-state vector is `2ⁿ`.** When every `φₛ` has modulus
`1`, `∑ᵢ ‖pv φ i‖² = 2ⁿ`, so `(1/√2ⁿ)·pv φ` is a unit vector (the QFT circuit's normalised output).
Obtained from `phaseProdVec_dotProduct` at `ψ = φ`: each factor `1 + conj(φₛ)φₛ = 1 + ‖φₛ‖² = 2`. -/
theorem phaseProdVec_sq_sum (n : ℕ) (φ : Fin n → ℂ) (hφ : ∀ s, ‖φ s‖ = 1) :
    ∑ i, ‖phaseProdVec n φ i‖ ^ 2 = 2 ^ n := by
  have hreal : ∀ i, (starRingEnd ℂ) (phaseProdVec n φ i) * phaseProdVec n φ i
      = ((‖phaseProdVec n φ i‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key : ((∑ i, ‖phaseProdVec n φ i‖ ^ 2 : ℝ) : ℂ) = (2 : ℂ) ^ n := by
    rw [Complex.ofReal_sum,
      show (∑ i, ((‖phaseProdVec n φ i‖ ^ 2 : ℝ) : ℂ))
          = ∑ i, (starRingEnd ℂ) (phaseProdVec n φ i) * phaseProdVec n φ i from
        Finset.sum_congr rfl fun i _ => (hreal i).symm,
      phaseProdVec_dotProduct,
      show (∏ s, (1 + (starRingEnd ℂ) (φ s) * φ s)) = ∏ _s : Fin n, (2 : ℂ) from
        Finset.prod_congr rfl fun s _ => by
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hφ s]; norm_num,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact_mod_cast key

/-- **Coherent-accumulation lower bound** (Nielsen & Chuang, Exercise 5.6, `Ω` half). For unit
phases `φ` and real per-wire errors `ε`, in the small-error regime `0 ≤ ∑ₛ εₛ ≤ π`, the normalised
product states `(1/√2ⁿ)·pv φ` and `(1/√2ⁿ)·pv (φ·e^{iε})` are separated by at least `(∑ₛ εₛ)/π`:

`(∑ₛ εₛ)/π ≤ √(∑ᵢ ‖(1/√2ⁿ)·pv φ i − (1/√2ⁿ)·pv ψ i‖²)`,  `ψₛ = φₛ·e^{iεₛ}`.

The squared distance evaluates to `2(1 − P·cos θ)` with `θ = (∑εₛ)/2` and `P = ∏ₛ cos(εₛ/2)`; since
`P ≤ 1` (a product of cosines) and `cos θ ≥ 0` (as `θ ≤ π/2`), it is `≥ 2(1 − cos θ) = 4 sin²(θ/2)`,
and Jordan's inequality `Real.mul_le_sin` (`(2/π)x ≤ sin x`) bounds `2 sin(θ/2) ≥ (2/π)θ = (∑εₛ)/π`.
The coherent phase `θ = Θ(∑εₛ)` — the *sum* of the errors, from their shared sign — is what makes
the bound linear in `∑εₛ` rather than in a single error. -/
theorem phaseProdVec_scaled_dist_ge (n : ℕ) (φ : Fin n → ℂ) (ε : Fin n → ℝ)
    (hφ : ∀ s, ‖φ s‖ = 1) (hε0 : 0 ≤ ∑ s, ε s) (hεπ : ∑ s, ε s ≤ Real.pi) :
    (∑ s, ε s) / Real.pi
      ≤ Real.sqrt (∑ i, ‖((Real.sqrt 2)⁻¹ : ℂ) ^ n * phaseProdVec n φ i
          - ((Real.sqrt 2)⁻¹ : ℂ) ^ n
              * phaseProdVec n (fun s => φ s * Complex.exp (↑(ε s) * I)) i‖ ^ 2) := by
  set ψ : Fin n → ℂ := fun s => φ s * Complex.exp (↑(ε s) * I) with hψ
  set θ : ℝ := (∑ s, ε s) / 2 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθπ : θ ≤ Real.pi / 2 := by rw [hθ]; linarith
  have hsumhalf : ∑ s : Fin n, ε s / 2 = θ := by
    rw [hθ]; simp only [div_eq_mul_inv]; rw [← Finset.sum_mul]
  -- ψ has unit phases too
  have hψnorm : ∀ s, ‖ψ s‖ = 1 := by
    intro s
    rw [hψ, norm_mul, hφ s, Complex.norm_exp, one_mul, show (↑(ε s) * I).re = 0 from by simp]
    exact Real.exp_zero
  -- the per-wire overlap  conj(φₛ)·ψₛ = e^{iεₛ}
  have hoverlap : ∀ s, (starRingEnd ℂ) (φ s) * ψ s = Complex.exp (↑(ε s) * I) := by
    intro s
    rw [hψ, ← mul_assoc, mul_comm ((starRingEnd ℂ) (φ s)) (φ s), Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hφ s]
    norm_num
  -- the factorised overlap product  ∏ₛ(1 + e^{iεₛ}) = (2ⁿ·P)·e^{iθ}
  set P : ℝ := ∏ s, Real.cos (ε s / 2) with hP
  have hprodval : (∏ s, (1 + (starRingEnd ℂ) (φ s) * ψ s))
      = (↑((2 : ℝ) ^ n * P) : ℂ) * Complex.exp (↑θ * I) := by
    have h1 : (∏ s, (1 + (starRingEnd ℂ) (φ s) * ψ s))
        = ∏ s, (2 * (Real.cos (ε s / 2) : ℂ)) * Complex.exp (↑(ε s / 2) * I) := by
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [hoverlap s]; exact one_add_exp_mul_I (ε s)
    rw [h1, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hP]
      push_cast; ring
    · rw [← Complex.exp_sum]
      congr 1
      rw [← Finset.sum_mul,
        show (∑ s : Fin n, (↑(ε s / 2) : ℂ)) = ↑θ from by rw [← Complex.ofReal_sum, hsumhalf]]
  -- the exact squared distance of the *unnormalised* vectors:  2^{n+1} − 2·2ⁿ·P·cos θ
  have hdistUnscaled : (∑ i, ‖phaseProdVec n φ i - phaseProdVec n ψ i‖ ^ 2)
      = 2 ^ (n + 1) - 2 * (2 ^ n * P * Real.cos θ) := by
    have hterm : ∀ z w : ℂ, ‖z - w‖ ^ 2
        = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * ((starRingEnd ℂ) z * w).re := by
      intro z w
      simp only [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.conj_re, Complex.conj_im]
      ring
    calc ∑ i, ‖phaseProdVec n φ i - phaseProdVec n ψ i‖ ^ 2
        = ∑ i, (‖phaseProdVec n φ i‖ ^ 2 + ‖phaseProdVec n ψ i‖ ^ 2
            - 2 * ((starRingEnd ℂ) (phaseProdVec n φ i) * phaseProdVec n ψ i).re) :=
          Finset.sum_congr rfl fun i _ => hterm _ _
      _ = (∑ i, ‖phaseProdVec n φ i‖ ^ 2) + (∑ i, ‖phaseProdVec n ψ i‖ ^ 2)
            - 2 * (∑ i, (starRingEnd ℂ) (phaseProdVec n φ i) * phaseProdVec n ψ i).re := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.re_sum]
      _ = 2 ^ n + 2 ^ n - 2 * (2 ^ n * P * Real.cos θ) := by
          rw [phaseProdVec_sq_sum n φ hφ, phaseProdVec_sq_sum n ψ hψnorm, phaseProdVec_dotProduct,
            hprodval, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      _ = 2 ^ (n + 1) - 2 * (2 ^ n * P * Real.cos θ) := by rw [pow_succ]; ring
  -- scale by (1/√2ⁿ)² = 2⁻ⁿ
  have hc0 : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  have hc : ‖((Real.sqrt 2)⁻¹ : ℂ) ^ n‖ ^ 2 = (2 : ℝ)⁻¹ ^ n := by
    rw [norm_pow, hc0, ← pow_mul, mul_comm n 2, pow_mul,
      show ((Real.sqrt 2)⁻¹) ^ 2 = (2 : ℝ)⁻¹ from by
        rw [← Real.sqrt_inv, Real.sq_sqrt (by positivity)]]
  have hscale : (∑ i, ‖((Real.sqrt 2)⁻¹ : ℂ) ^ n * phaseProdVec n φ i
          - ((Real.sqrt 2)⁻¹ : ℂ) ^ n * phaseProdVec n ψ i‖ ^ 2)
      = (2 : ℝ)⁻¹ ^ n * (∑ i, ‖phaseProdVec n φ i - phaseProdVec n ψ i‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, norm_mul, mul_pow, hc]
  have h2n : (2 : ℝ)⁻¹ ^ n * 2 ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
  have hPle : P ≤ 1 := by
    rw [hP]
    calc ∏ s, Real.cos (ε s / 2) ≤ |∏ s, Real.cos (ε s / 2)| := le_abs_self _
      _ = ∏ s, |Real.cos (ε s / 2)| := Finset.abs_prod _ _
      _ ≤ 1 := Finset.prod_le_one₀ (fun s _ => abs_nonneg _) (fun s _ => Real.abs_cos_le_one _)
  have hcosθ : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθπ⟩
  -- the core inequality:  4 sin²(θ/2) ≤ scaled squared distance
  have hcore : 4 * Real.sin (θ / 2) ^ 2
      ≤ ∑ i, ‖((Real.sqrt 2)⁻¹ : ℂ) ^ n * phaseProdVec n φ i
          - ((Real.sqrt 2)⁻¹ : ℂ) ^ n * phaseProdVec n ψ i‖ ^ 2 := by
    rw [hscale, hdistUnscaled]
    have hsin : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
      have h1 := Real.abs_sin_half θ
      rw [← sq_abs (Real.sin (θ / 2)), h1, Real.sq_sqrt (by have := Real.cos_le_one θ; linarith)]
    have hrhs : (2 : ℝ)⁻¹ ^ n * (2 ^ (n + 1) - 2 * (2 ^ n * P * Real.cos θ))
        = 2 - 2 * (P * Real.cos θ) := by
      rw [mul_sub, pow_succ,
        show (2 : ℝ)⁻¹ ^ n * (2 ^ n * 2) = ((2 : ℝ)⁻¹ ^ n * 2 ^ n) * 2 from by ring, h2n, one_mul,
        show (2 : ℝ)⁻¹ ^ n * (2 * (2 ^ n * P * Real.cos θ))
            = ((2 : ℝ)⁻¹ ^ n * 2 ^ n) * (2 * (P * Real.cos θ)) from by ring, h2n, one_mul]
    rw [hsin, hrhs]
    have hPcos : P * Real.cos θ ≤ Real.cos θ := by nlinarith [hcosθ, hPle]
    nlinarith [hPcos]
  -- Jordan's inequality turns the coherent phase into the linear bound
  have hsnn : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  calc (∑ s, ε s) / Real.pi = 2 * (2 / Real.pi * (θ / 2)) := by rw [hθ]; ring
    _ ≤ 2 * Real.sin (θ / 2) := by
        have hj := Real.mul_le_sin (x := θ / 2) (by linarith) (by linarith)
        linarith [hj]
    _ = Real.sqrt ((2 * Real.sin (θ / 2)) ^ 2) := by rw [Real.sqrt_sq (by positivity)]
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [hcore])

end AxQM.Concrete
