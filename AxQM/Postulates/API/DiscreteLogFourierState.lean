/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.OrderFindingEigenstate
import ToMathlib.Analysis.SpecialFunctions.Complex.PeriodicDFT

/-!
# AxQM.Postulates.API — the discrete-log Fourier state `|f̂(ℓ₁,ℓ₂)⟩` (N&C Ex 5.22)

The development behind **Nielsen & Chuang Exercise 5.22** (§5.4.2, discrete
logarithms, p. 239). Fix a modulus `N`, a unit `a` of `ZMod N` (the base `a` of `b = aˢ`) of
multiplicative order `r = orderOf a`, and the discrete logarithm `s`. The discrete-log function is

  `f(x₁, x₂) = bˣ¹ aˣ² = a^{s·x₁ + x₂}  (mod N)`,

so its computational-basis label is `orbitIndex a (s·x₁ + x₂)` and `f(0, j) = aʲ mod N`. Exercise
5.22 asks one to show that the two-dimensional Fourier transform of `f` collapses to a
one-dimensional transform over the coset representatives `f(0, j)` — N&C eq. (5.72):

  `|f̂(ℓ₁,ℓ₂)⟩ = ∑_{x₁,x₂<r} e^{-2πi(ℓ₁x₁+ℓ₂x₂)/r} |f(x₁,x₂)⟩`
             `= (1/√r) ∑_{j<r} e^{-2πiℓ₂j/r} |f(0,j)⟩`,

as printed on p.239: the double sum carries **no** prefactor, only the single sum carries `1/√r`
(contrast the visible `1/r` on the inverse transform (5.73)). It is non-zero only when
`ℓ₁ ≡ s·ℓ₂ (mod r)`; otherwise the double sum vanishes.

## What is formalised

* `dlogBasisState a s x₁ x₂` — the function-value state `|f(x₁,x₂)⟩ = |a^{s·x₁+x₂} mod N⟩` as a
  `PureState (qudit N)`; `dlogBasisState_zero_left` is `|f(0,j)⟩ = |aʲ mod N⟩`.
* `dlogFourierDoubleSum a s ℓ₁ ℓ₂` — the (un-normalized) double sum
  `∑_{x₁,x₂<r} e^{-2πi(ℓ₁x₁+ℓ₂x₂)/r} |f(x₁,x₂)⟩`, the left-hand side of (5.72).
* `dlogFourierSingleSum a ℓ₂` — the (un-normalized) single sum
  `∑_{j<r} e^{-2πiℓ₂j/r} |f(0,j)⟩`, N&C's `√r·|f̂(ℓ₂)⟩` of eq. (5.70).
* `dlogFourierDoubleSum_factor` — **the "phase form"**: the double sum factors as a geometric phase
  sum over `x₁` times the single sum, `DoubleSum = (∑_{x₁<r} e^{2πi(sℓ₂-ℓ₁)x₁/r}) • SingleSum`.
* `dlogFourierDoubleSum_of_modEq` — **eq. (5.72), on support**: if `ℓ₁ ≡ s·ℓ₂ (mod r)` then
  `DoubleSum = r • SingleSum`.
* `dlogFourierDoubleSum_eq_zero_of_not_modEq` — **the constraint**: otherwise `DoubleSum = 0`.
* `dlogFourierSingleSum_eq_orderEigenstate` — the single sum is `√r` times the normalized Fourier
  state `|f̂(ℓ₂)⟩ = orderEigenstate a ℓ₂` of eq. (5.70), grounding the collapse in Exercise 5.13's
  eigenstate.

## Design notes

* **Statement.** The statement of Exercise 5.22 is in `AxQM/NC/Ch5/Exercise5_22.lean`; it builds on
  the Exercise 5.13 `orderEigenstate` development.

* **On the printed normalization of (5.72).** As printed, the double sum carries **no** prefactor
  and the single sum carries `1/√r` — the printed double sum omits the natural unitary 2D-DFT
  normalization `1/r` (the factor that *is* present on the inverse transform (5.73)). So (5.72) is
  not a literal equality. Write `DoubleSum` for the printed (un-normalized) double sum and
  `SingleSum := ∑_{j<r} e^{-2πiℓ₂j/r}|f(0,j)⟩`. On support the proved relation is
  `DoubleSum = r • SingleSum` (`dlogFourierDoubleSum_of_modEq`), while `SingleSum = √r·|f̂(ℓ₂)⟩`
  with `|f̂(ℓ₂)⟩` the *unit* eq.-(5.70) state (`dlogFourierSingleSum_eq_orderEigenstate`). Hence
  the printed left side equals `r·SingleSum = r^{3/2}·|f̂(ℓ₂)⟩` while the printed right side
  `(1/√r)·SingleSum` equals `|f̂(ℓ₂)⟩`: as literally printed the two sides differ by a factor
  `r^{3/2}`. Supplying the omitted `1/r` makes the two *sum* forms agree,
  `(1/r)·DoubleSum = SingleSum`; the printed `1/√r` then normalizes `SingleSum` to the unit state.
  The formalisation carries the correct scalar throughout (`DoubleSum = r • SingleSum`), so the
  Lean statements need no adjustment; only this printed normalization is glossed here.

* **The constraint.** The exact non-vanishing condition — the one the `x₁`-geometric sum produces —
  is `ℓ₁ ≡ s·ℓ₂ (mod r)` (in the algorithm the surviving state has `ℓ₁ = s·ℓ₂` exactly), and this is
  what the theorems use. N&C phrase it informally as "`ℓ₁/s − ℓ₂` an integer multiple of `r`"; read
  literally (with `ℓ₁/s` an integer) that presupposes `s ∣ ℓ₁` and is *strictly stronger* than
  `ℓ₁ ≡ s·ℓ₂ (mod r)` — so the formalisation states the mathematically exact condition rather than
  the printed one. It is expressed here as `Nat.ModEq` and reduced, via the geometric sum
  `sum_range_exp_two_pi_mul_I_div` (Exercise 5.20), to divisibility of `s·ℓ₂ − ℓ₁` by `r`.

* **Faithful generality.** `ℓ₁, ℓ₂, s : ℕ` are arbitrary; the identity is proved for all of them,
  the double sum ranging over the fundamental domain `x₁, x₂ < r` as in (5.72).
-/

noncomputable section

namespace AxQM

open Finset Complex
open scoped Real
open AxQM.Concrete (orbitIndex orbitIndex_mod)

variable {N : ℕ} [NeZero N] (a : (ZMod N)ˣ)

/-- **The discrete-log function-value state** `|f(x₁,x₂)⟩ = |a^{s·x₁+x₂} mod N⟩` of N&C §5.4.2, as a
computational-basis `PureState` of `qudit N`. Its label is the order-finding orbit index of the
combined exponent `s·x₁ + x₂` (`b = aˢ`, so `f(x₁,x₂) = bˣ¹aˣ² = a^{s·x₁+x₂}`). -/
def dlogBasisState (s x₁ x₂ : ℕ) : PureState (qudit N) :=
  quditBasis (orbitIndex a (s * x₁ + x₂))

@[simp]
theorem dlogBasisState_vec (s x₁ x₂ : ℕ) :
    (dlogBasisState a s x₁ x₂).vec = (quditBasis (orbitIndex a (s * x₁ + x₂))).vec := rfl

/-- The coset representatives `|f(0,j)⟩ = |aʲ mod N⟩`. -/
theorem dlogBasisState_zero_left (s j : ℕ) :
    dlogBasisState a s 0 j = quditBasis (orbitIndex a j) := by
  simp [dlogBasisState]

/-- **The double sum of N&C eq. (5.72)** (un-normalized): the two-dimensional Fourier transform
`∑_{x₁,x₂<r} e^{-2πi(ℓ₁x₁+ℓ₂x₂)/r} |f(x₁,x₂)⟩` over the fundamental domain, `r = orderOf a`. -/
def dlogFourierDoubleSum (s ℓ₁ ℓ₂ : ℕ) : (qudit N).space :=
  ∑ x₁ ∈ range (orderOf a), ∑ x₂ ∈ range (orderOf a),
    exp (-(2 * (π : ℂ) * I * ((ℓ₁ : ℂ) * (x₁ : ℂ) + (ℓ₂ : ℂ) * (x₂ : ℂ)) / (orderOf a : ℂ)))
      • (dlogBasisState a s x₁ x₂).vec

/-- **The single sum of N&C eq. (5.70)** (un-normalized): the one-dimensional Fourier transform
`∑_{j<r} e^{-2πiℓ₂j/r} |f(0,j)⟩` over the coset representatives; equals `√r·|f̂(ℓ₂)⟩`. -/
def dlogFourierSingleSum (ℓ₂ : ℕ) : (qudit N).space :=
  ∑ j ∈ range (orderOf a),
    exp (-(2 * (π : ℂ) * I * (ℓ₂ : ℂ) * (j : ℂ) / (orderOf a : ℂ)))
      • (quditBasis (orbitIndex a j)).vec

/-- Summing an `r`-periodic function over any length-`r` window `[c, c+r)` gives the same value as
over `[0, r)`. Proved by induction on the window offset `c`: shifting the window by one drops the
term at `c` and re-adds `g(c+r) = g(c)`. -/
private theorem sum_range_shift_of_periodic {E : Type*} [AddCommGroup E]
    (g : ℕ → E) (r : ℕ) (hper : ∀ k, g (k + r) = g k) :
    ∀ c, ∑ x ∈ range r, g (c + x) = ∑ x ∈ range r, g x := by
  intro c
  induction c with
  | zero => simp
  | succ c ih =>
    rw [← ih]
    have e1 := Finset.sum_range_succ' (fun x => g (c + x)) r
    have e2 := Finset.sum_range_succ (fun x => g (c + x)) r
    have hend : g (c + r) = g (c + 0) := by rw [Nat.add_zero, hper c]
    have hcomm : (∑ x ∈ range r, g (c + (x + 1))) + g (c + 0)
        = (∑ x ∈ range r, g (c + x)) + g (c + r) := e1.symm.trans e2
    rw [hend] at hcomm
    have hcancel : ∑ x ∈ range r, g (c + (x + 1)) = ∑ x ∈ range r, g (c + x) :=
      add_right_cancel hcomm
    rw [← hcancel]
    exact Finset.sum_congr rfl (fun x _ => by congr 1; omega)

/-- The inner `x₂`-sum of the double sum, at a fixed `x₁`: it equals a global phase
`e^{2πi·s·ℓ₂·x₁/r}` times the single sum. Reindexing `x₂ ↦ s·x₁ + x₂` (a length-`r` window of the
`r`-periodic summand `g(k) = e^{-2πiℓ₂k/r}|aᵏ⟩`, `sum_range_shift_of_periodic`) turns
`e^{-2πiℓ₂x₂/r}|f(x₁,x₂)⟩ = e^{-2πiℓ₂x₂/r}|a^{sx₁+x₂}⟩` into `e^{2πisℓ₂x₁/r}·g(sx₁+x₂)`. -/
private theorem dlogFourier_inner_sum (s ℓ₂ x₁ : ℕ) :
    ∑ x₂ ∈ range (orderOf a),
        exp (-(2 * (π : ℂ) * I * (ℓ₂ : ℂ) * (x₂ : ℂ) / (orderOf a : ℂ)))
          • (dlogBasisState a s x₁ x₂).vec
      = exp (2 * (π : ℂ) * I * (ℓ₂ : ℂ) * ((s : ℂ) * (x₁ : ℂ)) / (orderOf a : ℂ))
          • dlogFourierSingleSum a ℓ₂ := by
  have hr : 0 < orderOf a := orderOf_pos a
  have hrne : (orderOf a : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set g : ℕ → (qudit N).space := fun k =>
    exp (-(2 * (π : ℂ) * I * (ℓ₂ : ℂ) * (k : ℂ) / (orderOf a : ℂ)))
      • (quditBasis (orbitIndex a k)).vec with hg
  have hper : ∀ k, g (k + orderOf a) = g k := by
    intro k
    have hidx : orbitIndex a (k + orderOf a) = orbitIndex a k := by
      rw [← orbitIndex_mod a (k + orderOf a), Nat.add_mod_right, orbitIndex_mod a k]
    simp only [hg, hidx]
    refine congrArg (· • _) ?_
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-(ℓ₂ : ℤ), by push_cast; field_simp; ring⟩
  have hterm : ∀ x₂ ∈ range (orderOf a),
      exp (-(2 * (π : ℂ) * I * (ℓ₂ : ℂ) * (x₂ : ℂ) / (orderOf a : ℂ)))
          • (dlogBasisState a s x₁ x₂).vec
        = exp (2 * (π : ℂ) * I * (ℓ₂ : ℂ) * ((s : ℂ) * (x₁ : ℂ)) / (orderOf a : ℂ))
            • g (s * x₁ + x₂) := by
    intro x₂ _
    simp only [hg, dlogBasisState_vec, smul_smul]
    congr 1
    rw [← exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum,
    sum_range_shift_of_periodic g (orderOf a) hper (s * x₁)]
  simp only [hg, dlogFourierSingleSum]

/-- **N&C Exercise 5.22, the phase form.** The discrete-log double sum (5.72) factors as a geometric
phase sum over `x₁` times the single sum (5.70):

  `∑_{x₁,x₂<r} e^{-2πi(ℓ₁x₁+ℓ₂x₂)/r} |f(x₁,x₂)⟩`
    `= (∑_{x₁<r} e^{2πi(sℓ₂-ℓ₁)x₁/r}) · ∑_{j<r} e^{-2πiℓ₂j/r} |f(0,j)⟩`.

The inner `x₂`-sum collapses to `e^{2πisℓ₂x₁/r}·SingleSum` (`dlogFourier_inner_sum`); combining with
the `e^{-2πiℓ₁x₁/r}` factor leaves the geometric sum `∑_{x₁<r} e^{2πi(sℓ₂-ℓ₁)x₁/r}` scaling the
single sum. -/
theorem dlogFourierDoubleSum_factor (s ℓ₁ ℓ₂ : ℕ) :
    dlogFourierDoubleSum a s ℓ₁ ℓ₂
      = (∑ x₁ ∈ range (orderOf a),
          exp (2 * (π : ℂ) * I * ((((s * ℓ₂ : ℕ) : ℤ) - (ℓ₁ : ℤ) : ℤ) : ℂ) * (x₁ : ℂ) /
            (orderOf a : ℂ))) • dlogFourierSingleSum a ℓ₂ := by
  rw [dlogFourierDoubleSum, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun x₁ _ => ?_)
  have hsplit : ∀ x₂ : ℕ,
      exp (-(2 * (π : ℂ) * I * ((ℓ₁ : ℂ) * (x₁ : ℂ) + (ℓ₂ : ℂ) * (x₂ : ℂ)) / (orderOf a : ℂ)))
        = exp (-(2 * (π : ℂ) * I * (ℓ₁ : ℂ) * (x₁ : ℂ) / (orderOf a : ℂ)))
          * exp (-(2 * (π : ℂ) * I * (ℓ₂ : ℂ) * (x₂ : ℂ) / (orderOf a : ℂ))) := by
    intro x₂
    rw [← exp_add]
    congr 1
    field_simp
    ring
  have hpull : ∑ x₂ ∈ range (orderOf a),
        exp (-(2 * (π : ℂ) * I * ((ℓ₁ : ℂ) * (x₁ : ℂ) + (ℓ₂ : ℂ) * (x₂ : ℂ)) / (orderOf a : ℂ)))
          • (dlogBasisState a s x₁ x₂).vec
      = exp (-(2 * (π : ℂ) * I * (ℓ₁ : ℂ) * (x₁ : ℂ) / (orderOf a : ℂ)))
          • ∑ x₂ ∈ range (orderOf a),
              exp (-(2 * (π : ℂ) * I * (ℓ₂ : ℂ) * (x₂ : ℂ) / (orderOf a : ℂ)))
                • (dlogBasisState a s x₁ x₂).vec := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun x₂ _ => by rw [hsplit x₂, mul_smul])
  rw [hpull, dlogFourier_inner_sum, smul_smul, ← exp_add]
  congr 2
  push_cast
  field_simp
  ring

/-- **N&C Exercise 5.22, eq. (5.72) on support.** When the constraint `ℓ₁ ≡ s·ℓ₂ (mod r)` holds, the
double sum collapses to `r` times the single sum over the coset representatives:

  `∑_{x₁,x₂<r} e^{-2πi(ℓ₁x₁+ℓ₂x₂)/r} |f(x₁,x₂)⟩ = r · ∑_{j<r} e^{-2πiℓ₂j/r} |f(0,j)⟩`.

The geometric sum over `x₁` (`sum_range_exp_two_pi_mul_I_div`) is `r` exactly when `r ∣ (s·ℓ₂−ℓ₁)`,
i.e. `ℓ₁ ≡ s·ℓ₂ (mod r)`. Dividing by `r` gives `(1/r)·DoubleSum = SingleSum`, the corrected form of
the printed (5.72) (see the module docstring on its `1/√r` misprint). -/
theorem dlogFourierDoubleSum_of_modEq (s ℓ₁ ℓ₂ : ℕ)
    (h : ℓ₁ ≡ s * ℓ₂ [MOD orderOf a]) :
    dlogFourierDoubleSum a s ℓ₁ ℓ₂ = (orderOf a : ℂ) • dlogFourierSingleSum a ℓ₂ := by
  have hr : 0 < orderOf a := orderOf_pos a
  have hdvd : (orderOf a : ℤ) ∣ ((s * ℓ₂ : ℕ) : ℤ) - (ℓ₁ : ℤ) := (Nat.modEq_iff_dvd).mp h
  rw [dlogFourierDoubleSum_factor,
    sum_range_exp_two_pi_mul_I_div (orderOf a) hr (((s * ℓ₂ : ℕ) : ℤ) - (ℓ₁ : ℤ)), ite_eq_left hdvd]

/-- **N&C Exercise 5.22, the constraint.** When `ℓ₁ ≢ s·ℓ₂ (mod r)` the amplitude of the double sum
is zero. The geometric sum over `x₁` (`sum_range_exp_two_pi_mul_I_div`) vanishes unless
`r ∣ (s·ℓ₂−ℓ₁)`. -/
theorem dlogFourierDoubleSum_eq_zero_of_not_modEq (s ℓ₁ ℓ₂ : ℕ)
    (h : ¬ ℓ₁ ≡ s * ℓ₂ [MOD orderOf a]) :
    dlogFourierDoubleSum a s ℓ₁ ℓ₂ = 0 := by
  have hr : 0 < orderOf a := orderOf_pos a
  have hdvd : ¬ (orderOf a : ℤ) ∣ ((s * ℓ₂ : ℕ) : ℤ) - (ℓ₁ : ℤ) := by
    rw [← Nat.modEq_iff_dvd]; exact h
  rw [dlogFourierDoubleSum_factor,
    sum_range_exp_two_pi_mul_I_div (orderOf a) hr (((s * ℓ₂ : ℕ) : ℤ) - (ℓ₁ :
        ℤ)), ite_eq_right hdvd,
    zero_smul]

/-- The single sum (5.70) is `√r` times the normalized Fourier state `|f̂(ℓ₂)⟩ = orderEigenstate a
ℓ₂` of Exercise 5.13/eq. (5.70). The `orderEigenstate` amplitudes carry the `1/√r` normalization,
which `√r` cancels; the `Fin r`-sum and the `range r`-sum agree (`Fin.sum_univ_eq_sum_range`). This
exhibits the `√r` factor implicit in the printed (5.72). -/
theorem dlogFourierSingleSum_eq_orderEigenstate (ℓ₂ : Fin (orderOf a)) :
    dlogFourierSingleSum a (ℓ₂ : ℕ)
      = (Real.sqrt (orderOf a) : ℂ) • (orderEigenstate a ℓ₂).vec := by
  have hr : 0 < orderOf a := orderOf_pos a
  have hne : (Real.sqrt (orderOf a) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
  rw [orderEigenstate_vec, Finset.smul_sum, dlogFourierSingleSum,
    ← Fin.sum_univ_eq_sum_range
      (fun j => exp (-(2 * (π : ℂ) * I * ((ℓ₂ : ℕ) : ℂ) * (j : ℂ) / (orderOf a : ℂ)))
        • (quditBasis (orbitIndex a j)).vec) (orderOf a)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  congr 2
  ring

end AxQM
