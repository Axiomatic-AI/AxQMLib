/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SearchSimulationLanding
import AxQM.Concrete.BlochPureState
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Concrete: exact-landing timing of the search-simulation step (Nielsen & Chuang, Exercise 6.10)

Nielsen & Chuang, Exercise 6.10 asks to choose the simulation time-step `Δt` so that the
continuous-time (Hamiltonian-simulation) quantum search lands **exactly** on the solution `|x⟩`
(probability `1`) in `O(√N)` queries, improving on the small-probability `Δt = π` special case.

The geometric core is already in place: `searchStepReduced_pow_conj_blochMatrix_land`
(Exercise 6.10) shows that, for a unit Bloch vector `⃗ψ` and `ẑ = (0,0,1)`, the `j`-th power of
the reduced search step conjugates the Bloch matrix of `⃗ψ` to that of `ẑ`,
`U(Δt)^j |ψ⟩⟨ψ| (U(Δt)^j)† = |x⟩⟨x|`, **whenever** the rotation angle
`θ = rotComposeAngle Δt ẑ Δt ⃗ψ` satisfies the exact-landing condition `(2j+1)·θ = 2π`. This file
supplies the missing analytic ingredient — a step size `Δt` realising that condition — and the
`O(√N)` step count.

## Tuning `Δt` (Eq. 6.28)

The rotation angle obeys N&C's eq. (6.27)/(6.28): `cos(θ/2) = rotComposeCos Δt ẑ Δt ⃗ψ =
cos²(Δt/2) − sin²(Δt/2)·(⃗ψ·ẑ)`. For the effective search qubit `⃗ψ = (sin θψ, 0, cos θψ)`
(`= blochSphereVector θψ 0`, so `⃗ψ·ẑ = cos θψ`), hitting the exact-landing angle
`θ = 2π/(2j+1)` — i.e. `cos(θ/2) = cos(π/(2j+1))` — amounts to
`sin²(Δt/2) = (1 − cos(π/(2j+1)))/(1 + cos θψ)`. Rather than invoking an intermediate-value
argument, we **construct** `Δt` explicitly by `arcsin`:

`Δt = 2·arcsin(√((1 − cos(π/(2j+1)))/(1 + cos θψ)))`,

which lands in `(0, π]` and realises exactly that half-angle sine, so the angle condition holds by
`arccos_cos`. The non-degeneracy hypotheses of the geometric landing are discharged concretely:
`sin(Δt/2) ≠ 0` from the construction, and `searchStepAxis Δt ⃗ψ ẑ ≠ 0` from
`‖searchStepAxis‖² = sin²θψ/4 + cos²(Δt/2)(cos θψ + 1)²/4 > 0`, which needs only `sin θψ ≠ 0`.

## `O(√N)` queries

For the uniform search state `|ψ⟩ = α|x⟩ + β|y⟩` with `α² = 1/N` the polar angle has
`cos θψ = α² − β² = 2/N − 1`. The exact-landing angle `2π/(2j+1)` is achievable (`≤ θ_max`) iff
`1 − 2/N = −cos θψ ≤ cos(π/(2j+1))`. Using the elementary bound `cos y ≥ 1 − y²/2`
(`Real.one_sub_sq_div_two_le_cos`), this holds as soon as `(π/(2j+1))² ≤ 4/N`, i.e.
`2j+1 ≥ (π/2)√N`. Taking `j = ⌈(π/4)√N⌉` meets this and gives the query bound
`j ≤ (π/4 + 1)√N = O(√N)` (each `U(Δt)` step costs `O(1)` oracle calls, Figures 6.4/6.5). The
headline `searchStepReduced_pow_conj_blochMatrix_exactSearch` packages both: for every `N ≥ 2` there
are `j = O(√N)` and `Δt ∈ (0, π]` with `U(Δt)^j |ψ⟩⟨ψ| (U(Δt)^j)† = |x⟩⟨x|` exactly.

The physics assembly (final state `= |x⟩`, probability `1`) is carried out in
`AxQM/NC/Ch6/Exercise6_10.lean`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- **The eq.-6.25 composed axis of the search step is nonzero for the effective search qubit.** For
the search Bloch vector `⃗ψ = blochSphereVector θ 0 = (sin θ, 0, cos θ)` (a genuine superposition,
`sin θ ≠ 0`) and target `ẑ = (0,0,1)`, the composed axis-vector `searchStepAxis Δt ⃗ψ ẑ` (N&C's
`c(⃗ψ+ẑ)/2 + s(⃗ψ×ẑ)/2`, `c = cos(Δt/2)`, `s = sin(Δt/2)`) has strictly positive squared norm:
`‖searchStepAxis Δt ⃗ψ ẑ‖² = sin²θ/4 + cos²(Δt/2)(cos θ + 1)²/4 > 0`.
The first summand is already positive (`sin θ ≠ 0`), so the composite `U(Δt)` is never `± I`; this
is the `hax` non-degeneracy hypothesis of `searchStepReduced_pow_conj_blochMatrix_land`. -/
theorem searchStepAxis_blochSphereVector_normSq_pos (θ : ℝ) (hsθ : Real.sin θ ≠ 0) (Δt : ℝ) :
    0 < (searchStepAxis Δt (blochSphereVector θ 0) ![0, 0, 1]) 0 ^ 2
      + (searchStepAxis Δt (blochSphereVector θ 0) ![0, 0, 1]) 1 ^ 2
      + (searchStepAxis Δt (blochSphereVector θ 0) ![0, 0, 1]) 2 ^ 2 := by
  have hbsv : blochSphereVector θ 0 = ![Real.sin θ, 0, Real.cos θ] := by
    simp only [blochSphereVector, Real.cos_zero, Real.sin_zero, mul_one, mul_zero]
  rw [hbsv]
  have hsθ2 : 0 < Real.sin θ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsθ))
  have hcs : Real.cos (Δt / 2) ^ 2 + Real.sin (Δt / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hsum : (searchStepAxis Δt ![Real.sin θ, 0, Real.cos θ] ![0, 0, 1]) 0 ^ 2
      + (searchStepAxis Δt ![Real.sin θ, 0, Real.cos θ] ![0, 0, 1]) 1 ^ 2
      + (searchStepAxis Δt ![Real.sin θ, 0, Real.cos θ] ![0, 0, 1]) 2 ^ 2
      = Real.sin θ ^ 2 / 4 + (Real.cos (Δt / 2) * (Real.cos θ + 1)) ^ 2 / 4 := by
    simp only [searchStepAxis, cross_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linear_combination (Real.sin θ ^ 2 / 4) * hcs
  rw [hsum]
  nlinarith [hsθ2, sq_nonneg (Real.cos (Δt / 2) * (Real.cos θ + 1))]

/-- **Exercise 6.10 exact-landing timing (general effective qubit).** For an effective search qubit
`⃗ψ = blochSphereVector θ 0 = (sin θ, 0, cos θ)` that is a genuine superposition (`sin θ ≠ 0`) and a
step count `j` for which the exact-landing angle `2π/(2j+1)` is achievable — i.e.
`−cos θ ≤ cos(π/(2j+1))`, N&C's condition `2π/(2j+1) ≤ θ_max` — there is a simulation time-step
`Δt ∈ (0, π]` under which the `j`-th power of the reduced search step lands `|ψ⟩⟨ψ|` exactly on the
solution `|x⟩⟨x| = blochMatrix ẑ`:
`(searchStepReduced Δt ⃗ψ ẑ)^j · blochMatrix ⃗ψ · ((searchStepReduced Δt ⃗ψ ẑ)^j)† = blochMatrix ẑ`.
Proof: set `Δt = 2·arcsin(√((1 − cos(π/(2j+1)))/(1 + cos θ)))`, so `sin²(Δt/2) =
(1 − cos(π/(2j+1)))/(1 + cos θ)`; then `rotComposeCos Δt ẑ Δt ⃗ψ = cos²(Δt/2) − sin²(Δt/2)·cos θ =
cos(π/(2j+1))` (Eq. 6.28), whence `rotComposeAngle Δt ẑ Δt ⃗ψ = 2π/(2j+1)` by `arccos_cos` and
`(2j+1)·θ = 2π`. Feed this, together with `sin(Δt/2) ≠ 0` and the composed-axis non-degeneracy
`searchStepAxis_blochSphereVector_normSq_pos`, into the geometric landing
`searchStepReduced_pow_conj_blochMatrix_land`. -/
theorem searchStepReduced_pow_conj_blochMatrix_tuned (θ : ℝ) (hsθ : Real.sin θ ≠ 0) (j : ℕ)
    (hadm : -Real.cos θ ≤ Real.cos (Real.pi / (2 * (j : ℝ) + 1))) :
    ∃ Δt : ℝ, 0 < Δt ∧ Δt ≤ Real.pi ∧
      (searchStepReduced Δt (blochSphereVector θ 0) ![0, 0, 1]) ^ j
          * blochMatrix (blochSphereVector θ 0)
          * ((searchStepReduced Δt (blochSphereVector θ 0) ![0, 0, 1]) ^ j)ᴴ
        = blochMatrix ![0, 0, 1] := by
  have hmpos : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
  have hm1 : (1 : ℝ) ≤ 2 * (j : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hy0 : 0 < Real.pi / (2 * (j : ℝ) + 1) := div_pos Real.pi_pos hmpos
  have hyle : Real.pi / (2 * (j : ℝ) + 1) ≤ Real.pi := div_le_self Real.pi_pos.le hm1
  set c₀ := Real.cos (Real.pi / (2 * (j : ℝ) + 1)) with hc0
  have hc0le1 : c₀ ≤ 1 := Real.cos_le_one _
  have hc0lt1 : c₀ < 1 := by
    refine lt_of_le_of_ne hc0le1 ?_
    rw [hc0]
    intro h
    rw [Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [Real.pi_pos, hy0])
      (by nlinarith [Real.pi_pos, hyle])] at h
    exact (ne_of_gt hy0) h
  -- overlap bounds from `sin θ ≠ 0`
  have hsθ2 : 0 < Real.sin θ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsθ))
  have h1q : 0 < 1 + Real.cos θ := by
    nlinarith [hsθ2, Real.cos_le_one θ, Real.sin_sq_add_cos_sq θ]
  -- the tuned half-angle sine squared
  set s0sq := (1 - c₀) / (1 + Real.cos θ) with hs0sq
  have hs0sq_pos : 0 < s0sq := div_pos (by linarith) h1q
  have hs0sq_le1 : s0sq ≤ 1 := by rw [hs0sq, div_le_one h1q]; linarith [hadm]
  set s0 := Real.sqrt s0sq with hs0
  have hs0_pos : 0 < s0 := Real.sqrt_pos.mpr hs0sq_pos
  have hs0_le1 : s0 ≤ 1 := by
    rw [hs0, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hs0sq_le1
  set Δt := 2 * Real.arcsin s0 with hΔt
  have hhalf : Δt / 2 = Real.arcsin s0 := by rw [hΔt]; ring
  have hsinhalf : Real.sin (Δt / 2) = s0 := by
    rw [hhalf, Real.sin_arcsin (by linarith [hs0_pos]) hs0_le1]
  have hsin_ne : Real.sin (Δt / 2) ≠ 0 := by rw [hsinhalf]; exact ne_of_gt hs0_pos
  have hsinsq : Real.sin (Δt / 2) ^ 2 = s0sq := by
    rw [hsinhalf, hs0, Real.sq_sqrt hs0sq_pos.le]
  refine ⟨Δt, ?_, ?_, ?_⟩
  · rw [hΔt]; have := Real.arcsin_pos.mpr hs0_pos; linarith
  · rw [hΔt]; have := Real.arcsin_le_pi_div_two s0; linarith
  · have hdot : (![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ blochSphereVector θ 0 = Real.cos θ := by
      simp [dotProduct, Fin.sum_univ_three, blochSphereVector]
    have hcossq : Real.cos (Δt / 2) ^ 2 = 1 - s0sq := by
      have h := Real.sin_sq_add_cos_sq (Δt / 2); rw [hsinsq] at h; linarith
    have hrcc : rotComposeCos Δt ![0, 0, 1] Δt (blochSphereVector θ 0) = c₀ := by
      rw [rotComposeCos, hdot, ← pow_two, ← pow_two, hcossq, hsinsq, hs0sq]
      field_simp
      ring
    have hangle : rotComposeAngle Δt ![0, 0, 1] Δt (blochSphereVector θ 0)
        = 2 * (Real.pi / (2 * (j : ℝ) + 1)) := by
      rw [rotComposeAngle, hrcc, hc0, Real.arccos_cos hy0.le hyle]
    have hj_final : (2 * (j : ℝ) + 1) * rotComposeAngle Δt ![0, 0, 1] Δt (blochSphereVector θ 0)
        = 2 * Real.pi := by
      rw [hangle]
      field_simp
    exact searchStepReduced_pow_conj_blochMatrix_land (blochSphereVector_normSq θ 0) Δt hsin_ne
      (searchStepAxis_blochSphereVector_normSq_pos θ hsθ Δt).ne' j hj_final

/-- **Nielsen & Chuang, Exercise 6.10 (Bloch-matrix level): a tuned `O(√N)`-query search that lands
on `|x⟩` exactly.** For a search space of size `N ≥ 2`, with the uniform search state
`|ψ⟩ = α|x⟩ + β|y⟩` (`α² = 1/N`, effective-qubit polar angle `θ` fixed by `cos θ = ⃗ψ·ẑ = α² − β² =
2/N − 1`), there are a step count `j` and a simulation time-step `Δt ∈ (0, π]` such that:

* `j ≤ (π/4 + 1)·√N` — the number of `U(Δt)` steps is `O(√N)`, hence so is the number of oracle
  calls (each step is `O(1)` oracle calls, Figures 6.4/6.5); and
* `(searchStepReduced Δt ⃗ψ ẑ)^j · blochMatrix ⃗ψ · (…)† = blochMatrix ẑ`, i.e.
  `U(Δt)^j |ψ⟩⟨ψ| (U(Δt)^j)† = |x⟩⟨x|` **exactly** (probability `1`).

Proof: take `j = ⌈(π/4)√N⌉`. Then `2j + 1 ≥ (π/2)√N`, so with `cos y ≥ 1 − y²/2`
(`Real.one_sub_sq_div_two_le_cos`) and `(π/(2j+1))² ≤ 4/N`,
`cos(π/(2j+1)) ≥ 1 − 2/N = −cos θ`, the achievability condition of
`searchStepReduced_pow_conj_blochMatrix_tuned`, which then supplies the tuned `Δt` and the exact
landing. The bound `j = ⌈(π/4)√N⌉ ≤ (π/4)√N + 1 ≤ (π/4 + 1)√N` is the `O(√N)` claim. -/
theorem searchStepReduced_pow_conj_blochMatrix_exactSearch (N : ℕ) (hN : 2 ≤ N) (θ : ℝ)
    (hθcos : Real.cos θ = 2 / (N : ℝ) - 1) :
    ∃ (j : ℕ) (Δt : ℝ), 0 < Δt ∧ Δt ≤ Real.pi ∧ 1 ≤ j ∧
      (j : ℝ) ≤ (Real.pi / 4 + 1) * Real.sqrt N ∧
      (searchStepReduced Δt (blochSphereVector θ 0) ![0, 0, 1]) ^ j
          * blochMatrix (blochSphereVector θ 0)
          * ((searchStepReduced Δt (blochSphereVector θ 0) ![0, 0, 1]) ^ j)ᴴ
        = blochMatrix ![0, 0, 1] := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hsqrtN_sq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  have hsqrtN_ge1 : (1 : ℝ) ≤ Real.sqrt N := by nlinarith [hsqrtN_sq, hsqrtN, hNr]
  -- `sin θ ≠ 0` from `cos θ = 2/N − 1 ∈ (−1, 1)`
  have hcos_lt1 : Real.cos θ < 1 := by
    rw [hθcos]
    have h2N : (2 : ℝ) / N ≤ 1 := (div_le_one hNpos).mpr hNr
    linarith
  have hcos_gtm1 : -1 < Real.cos θ := by
    rw [hθcos]
    have : (0 : ℝ) < 2 / (N : ℝ) := by positivity
    linarith
  have hsθ : Real.sin θ ≠ 0 := by
    intro h
    have hpy := Real.sin_sq_add_cos_sq θ
    rw [h] at hpy
    nlinarith [hpy, hcos_lt1, hcos_gtm1]
  -- choose `j = ⌈(π/4)√N⌉`
  have hquot_pos : 0 < Real.pi * Real.sqrt N / 4 :=
    div_pos (mul_pos Real.pi_pos hsqrtN) (by norm_num)
  set j : ℕ := ⌈Real.pi * Real.sqrt N / 4⌉₊ with hj_def
  have hj1 : 1 ≤ j := by rw [hj_def]; exact Nat.one_le_ceil_iff.mpr hquot_pos
  have hj_lb : Real.pi * Real.sqrt N / 4 ≤ (j : ℝ) := by rw [hj_def]; exact Nat.le_ceil _
  have hj_ub : (j : ℝ) < Real.pi * Real.sqrt N / 4 + 1 := by
    rw [hj_def]; exact Nat.ceil_lt_add_one hquot_pos.le
  -- achievability of the exact-landing angle `2π/(2j+1)`
  have hmpos : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
  have hympos : 0 < Real.pi / (2 * (j : ℝ) + 1) := div_pos Real.pi_pos hmpos
  have hym_ub : Real.pi / (2 * (j : ℝ) + 1) ≤ 2 / Real.sqrt N := by
    rw [div_le_div_iff₀ hmpos hsqrtN]; nlinarith [hj_lb]
  have hsq : (Real.pi / (2 * (j : ℝ) + 1)) ^ 2 ≤ 4 / (N : ℝ) := by
    have hle : (Real.pi / (2 * (j : ℝ) + 1)) ^ 2 ≤ (2 / Real.sqrt N) ^ 2 :=
      pow_le_pow_left₀ hympos.le hym_ub 2
    have h4 : (2 / Real.sqrt N) ^ 2 = 4 / (N : ℝ) := by rw [div_pow, hsqrtN_sq]; norm_num
    linarith [hle, h4]
  have hadm : -Real.cos θ ≤ Real.cos (Real.pi / (2 * (j : ℝ) + 1)) := by
    have hb := Real.one_sub_sq_div_two_le_cos (x := Real.pi / (2 * (j : ℝ) + 1))
    have h2N : (2 : ℝ) / N = (4 / (N : ℝ)) / 2 := by ring
    rw [hθcos]
    linarith [hb, hsq, h2N]
  obtain ⟨Δt, hΔt0, hΔtπ, hland⟩ := searchStepReduced_pow_conj_blochMatrix_tuned θ hsθ j hadm
  refine ⟨j, Δt, hΔt0, hΔtπ, hj1, ?_, hland⟩
  have hexpand : (Real.pi / 4 + 1) * Real.sqrt N = Real.pi * Real.sqrt N / 4 + Real.sqrt N := by
    ring
  linarith [hj_ub, hsqrtN_ge1, hexpand]

end AxQM.Concrete
