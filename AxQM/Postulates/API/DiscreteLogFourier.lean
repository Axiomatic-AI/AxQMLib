/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DiscreteLogFourierState

/-!
# AxQM.Postulates.API — inverting the discrete-log Fourier double sum (N&C Ex 5.23)

The development behind **Nielsen & Chuang Exercise 5.23** (§5.4.2, the discrete
logarithm problem, p. 239). It builds directly on the Exercise 5.22 development
(`AxQM/Postulates/API/DiscreteLogFourierState.lean`): fix a modulus `N`, a unit `a` of `ZMod N` (the
base, `b = aˢ`) of
multiplicative order `r = orderOf a`, and the discrete logarithm `s`. The discrete-log function is

  `f(x₁, x₂) = bˣ¹ aˣ² = a^{s·x₁ + x₂}  (mod N)`,

whose value states `|f(x₁,x₂)⟩ = |a^{s·x₁+x₂} mod N⟩` are the computational-basis states
`dlogBasisState a s x₁ x₂ = quditBasis (orbitIndex a (s·x₁+x₂))` of the value register `qudit N`
(the `r` distinct orthonormal values `|f(0,j)⟩ = |aʲ⟩`, `j < r`).

## What N&C's Fourier state `|f̂(ℓ₁,ℓ₂)⟩` actually is (eq. 5.70 **with** 5.71)

N&C eq. (5.70) writes `|f̂(ℓ₁,ℓ₂)⟩ = (1/√r) ∑_j e^{−2πiℓ₂j/r} |f(0,j)⟩`, and **immediately**
constrains it (eq. 5.71): "the values of `ℓ₁` and `ℓ₂` must satisfy [`∑_k e^{2πik(ℓ₁/s−ℓ₂)/r} = r`].
Otherwise, the amplitude of `|f̂(ℓ₁,ℓ₂)⟩` is nearly zero." Exercise 5.22 makes this exact: the
genuine two-dimensional Fourier transform (`dlogFourierDoubleSum`) **vanishes** unless
`ℓ₁ ≡ s·ℓ₂ (mod r)`, and on that support equals `r` times the single sum over the coset
representatives, i.e. `r·√r` times the *normalized* eq.-(5.70) state `orderEigenstate a ℓ₂`
(`dlogFourierDoubleSum_of_modEq`,
`dlogFourierSingleSum_eq_orderEigenstate`). So the honest normalized `|f̂(ℓ₁,ℓ₂)⟩` is

  `dlogFourierState a s ℓ₁ ℓ₂ = if ℓ₁ ≡ s·ℓ₂ (mod r) then orderEigenstate a ℓ₂ else 0`,

`ℓ₁`-degenerate on its support but **zero off it** — *not* an `ℓ₁`-independent state that is nonzero
for every `ℓ₁` (`dlogFourierDoubleSum_eq_smul_dlogFourierState` records the exact
`DoubleSum = r√r · dlogFourierState` bridge to Exercise 5.22, pinning this reading).

## Computing (5.73) and reconstructing `f(x₁,x₂)`

With the constraint in force, the inverse-Fourier double sum (5.73) collapses: for each `ℓ₂` only
the single `ℓ₁ ≡ s·ℓ₂` term survives, and the `ℓ₁`-phase `e^{2πiℓ₁x₁/r}` becomes `e^{2πi·s·ℓ₂·x₁/r}`
(`dlogInverseFourierSum_collapse` — "compute (5.73) using (5.70)"). The surviving single-`ℓ₂` sum is
the eq.-(5.45) inverse discrete Fourier transform `orderEigenstate_reconstruct` at the value index
`s·x₁+x₂`, so

  `(1/r) ∑_{ℓ₁,ℓ₂} e^{2πi(ℓ₁x₁+ℓ₂x₂)/r} |f̂(ℓ₁,ℓ₂)⟩ = (1/√r) |f(x₁,x₂)⟩`

(`dlogInverseFourierSum_eq_smul_dlogBasisState`): **the result is `f(x₁,x₂)`**, up to the section's
schematic `1/√r` normalization. This is the faithful content of Exercise 5.23: the constrained
Fourier states (5.70)/(5.71) invert back to the value states, exactly as the algorithm's step-4
"inverse
Fourier transform" requires. (Contrast the *false* reading in which `|f̂(ℓ₁,ℓ₂)⟩` is taken
`ℓ₁`-independent and nonzero for every `ℓ₁`: then the redundant `ℓ₁`-sum kills the double sum to `0`
for `x₁ ≠ 0` — but that discards the constraint N&C states in the same breath as (5.70), and
contradicts Exercise 5.22's `dlogFourierDoubleSum_eq_zero_of_not_modEq`.)

## Two printed imprecisions of this schematic section, made honest

The section is explicitly "more schematic … the reader … will have to work much harder"; (5.73)
carries two such imprecisions, both accounted for here rather than glossed:

* **Normalization.** The literal `1/r` prefactor leaves the result `(1/√r)|f(x₁,x₂)⟩`, a nonzero
  scalar multiple of the value state (the same quantum ray), not the unit state — exactly the `1/√r`
  slop already flagged for eq. (5.72) in the Exercise 5.22 module. The exact scalar is carried
  throughout (`… = (√r)⁻¹ • |f(x₁,x₂)⟩`), never dropped.
* **Sign.** As printed (5.73) shows `e^{−2πi(…)}`, the *forward* sign; the book's own inverse
  transform (eq. 5.64, `quditBasis_eq_sum_qftInverseFourierImage`) and step 4's "apply inverse
  Fourier transform" use `e^{+2πi(…)}`. With the printed `−` the sum reconstructs the *reflected*
  value state `|a^{−(s·x₁+x₂)}⟩ = |f(−x₁,−x₂)⟩`, not `|f(x₁,x₂)⟩`
  (`dlogForwardFourierSum_eq_smul_reflected`); the inverse-transform sign `+` is the one that yields
  the claimed `f(x₁,x₂)`. So `dlogInverseFourierSum` uses `+` (faithful to the inverse-transform
  *operation* N&C names), and the printed `−` form is proved separately to exhibit the misprint
  rather than silently correct it.

## What is formalised

* `dlogFourierState a s ℓ₁ ℓ₂` — the eq.-(5.70)+(5.71) normalized Fourier state `|f̂(ℓ₁,ℓ₂)⟩`
  (`orderEigenstate a ℓ₂` on the support `ℓ₁ ≡ s·ℓ₂ (mod r)`, else `0`).
* `dlogFourierDoubleSum_eq_smul_dlogFourierState` — the bridge `DoubleSum = r√r · dlogFourierState`
  identifying it as the normalized Exercise-5.22 two-dimensional Fourier transform.
* `dlogInverseFourierSum a s x₁ x₂` — the inverse-Fourier double sum (5.73).
* `dlogInverseFourierSum_collapse` — computing (5.73) using (5.70): the `ℓ₁`-sum collapses via the
  constraint to the single-`ℓ₂` inverse transform.
* `dlogInverseFourierSum_eq_smul_dlogBasisState` — **the reconstruction:** the double sum is
  `(1/√r)·|f(x₁,x₂)⟩`.
* `dlogForwardFourierSum a s x₁ x₂`, `dlogForwardFourierSum_eq_smul_reflected` — the literal
  printed-`−` sum and its honest value, the reflected state, exhibiting the sign misprint.

## Design notes

The statement of Exercise 5.23 is in `AxQM/NC/Ch5/Exercise5_23.lean`. The analytic engine is the
order-finding inverse DFT `orderEigenstate_reconstruct`
(Exercise 5.13, eq. 5.45) and the root-of-unity mod arithmetic behind Exercise 5.22.
-/

noncomputable section

namespace AxQM

open Finset Complex
open scoped Real
open AxQM.Concrete (orbitIndex orbitIndex_mod)

variable {N : ℕ} [NeZero N] (a : (ZMod N)ˣ)

/-- Rescaled Exercise-5.13 reconstruction (eq. 5.45): summing `e^{2πiℓ₂k/r}|f̂(ℓ₂)⟩` over `ℓ₂ < r`
recovers `√r` times the value state `|aᵏ mod N⟩`. Obtained from `orderEigenstate_reconstruct`
(whose amplitudes carry the `1/√r`) by cancelling `√r·(1/√r) = 1` in each term. -/
private theorem sum_orderEigenstate_phase (k : ℕ) :
    ∑ ℓ₂ : Fin (orderOf a),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((ℓ₂ : ℕ) * (k : ℕ)) / (orderOf a : ℂ))
          • (orderEigenstate a ℓ₂).vec
      = (Real.sqrt (orderOf a) : ℂ) • (quditBasis (orbitIndex a k)).vec := by
  have hr : 0 < orderOf a := orderOf_pos a
  have hsq : (Real.sqrt (orderOf a) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
  rw [← orderEigenstate_reconstruct a k, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun ℓ₂ _ => ?_)
  rw [smul_smul, mul_inv_cancel_left₀ hsq]

/-- The scalar cancellation `(1/r)·√r = 1/√r` behind both reconstruction theorems: it turns the
`(orderOf a)⁻¹` prefactor of (5.73) times the `√r` from `sum_orderEigenstate_phase` into the `1/√r`
normalization of the value state. -/
private theorem inv_natCast_orderOf_mul_ofReal_sqrt :
    (orderOf a : ℂ)⁻¹ * (Real.sqrt (orderOf a) : ℂ) = (Real.sqrt (orderOf a) : ℂ)⁻¹ := by
  have hr : 0 < orderOf a := orderOf_pos a
  have hsqsq : (Real.sqrt (orderOf a) : ℂ) * (Real.sqrt (orderOf a) : ℂ) = (orderOf a : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]
  have hsqne : (Real.sqrt (orderOf a) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
  rw [← hsqsq, mul_inv, mul_assoc, inv_mul_cancel₀ hsqne, mul_one]

/-- **The discrete-log Fourier state `|f̂(ℓ₁,ℓ₂)⟩` of N&C eq. (5.70)+(5.71).** In the value register
`qudit N` it is the normalized single-`ℓ₂` Fourier state `orderEigenstate a ℓ₂ =
(1/√r) ∑_j e^{−2πiℓ₂j/r}|f(0,j)⟩` **on its support** `ℓ₁ ≡ s·ℓ₂ (mod r)`, and `0` off it (eq. 5.71:
"otherwise the amplitude … is nearly zero"; Exercise 5.22's
`dlogFourierDoubleSum_eq_zero_of_not_modEq`). The condition is written as the residue equality
`(ℓ₁ : ℕ) % r = (s·ℓ₂) % r`, i.e. `ℓ₁ ≡ s·ℓ₂ (mod r)`. -/
def dlogFourierState (s : ℕ) (ℓ₁ ℓ₂ : Fin (orderOf a)) : (qudit N).space :=
  if (ℓ₁ : ℕ) % orderOf a = (s * (ℓ₂ : ℕ)) % orderOf a then (orderEigenstate a ℓ₂).vec else 0

/-- The support condition of `dlogFourierState` as a `Fin`-equality: `ℓ₁ ≡ s·ℓ₂ (mod r)` iff `ℓ₁` is
the unique residue `⟨(s·ℓ₂) % r, _⟩`. -/
theorem dlogFourierState_eq_ite (s : ℕ) (ℓ₁ ℓ₂ : Fin (orderOf a)) :
    dlogFourierState a s ℓ₁ ℓ₂
      = if ℓ₁ = ⟨(s * (ℓ₂ : ℕ)) % orderOf a, Nat.mod_lt _ (orderOf_pos a)⟩
          then (orderEigenstate a ℓ₂).vec else 0 := by
  have hcond : ((ℓ₁ : ℕ) % orderOf a = (s * (ℓ₂ : ℕ)) % orderOf a)
      ↔ ℓ₁ = (⟨(s * (ℓ₂ : ℕ)) % orderOf a, Nat.mod_lt _ (orderOf_pos a)⟩ : Fin (orderOf a)) := by
    rw [Fin.ext_iff, Nat.mod_eq_of_lt ℓ₁.isLt]
  rw [dlogFourierState]
  simp only [hcond]

/-- **Bridge to Exercise 5.22.** The (un-normalized) two-dimensional Fourier transform of `f`
(`dlogFourierDoubleSum`) is `r·√r` times the normalized Fourier state `dlogFourierState`: on the
support `ℓ₁ ≡ s·ℓ₂ (mod r)` it is `r·(√r·|f̂(ℓ₂)⟩)` (`dlogFourierDoubleSum_of_modEq` composed with
`dlogFourierSingleSum_eq_orderEigenstate`), and off it both sides vanish
(`dlogFourierDoubleSum_eq_zero_of_not_modEq`). This pins `dlogFourierState` as the genuine
normalized eq.-(5.70) state, not an `ℓ₁`-independent surrogate. -/
theorem dlogFourierDoubleSum_eq_smul_dlogFourierState (s : ℕ) (ℓ₁ ℓ₂ : Fin (orderOf a)) :
    dlogFourierDoubleSum a s (ℓ₁ : ℕ) (ℓ₂ : ℕ)
      = ((orderOf a : ℂ) * (Real.sqrt (orderOf a) : ℂ)) • dlogFourierState a s ℓ₁ ℓ₂ := by
  by_cases h : (ℓ₁ : ℕ) % orderOf a = (s * (ℓ₂ : ℕ)) % orderOf a
  · have hstate : dlogFourierState a s ℓ₁ ℓ₂ = (orderEigenstate a ℓ₂).vec := by
      rw [dlogFourierState, ite_eq_left h]
    rw [hstate, dlogFourierDoubleSum_of_modEq a s (ℓ₁ : ℕ) (ℓ₂ : ℕ) h,
      dlogFourierSingleSum_eq_orderEigenstate a ℓ₂, smul_smul]
  · have hstate : dlogFourierState a s ℓ₁ ℓ₂ = 0 := by rw [dlogFourierState, ite_eq_right h]
    rw [hstate, smul_zero, dlogFourierDoubleSum_eq_zero_of_not_modEq a s (ℓ₁ : ℕ) (ℓ₂ : ℕ) h]

/-- The `ℓ₁`-sum of a coefficient times `dlogFourierState a s ℓ₁ ℓ₂` collapses to the single
surviving term `ℓ₁ = ⟨(s·ℓ₂) % r, _⟩`: every other `ℓ₁` is off the support
(`dlogFourierState = 0`). -/
private theorem inner_ell1_pick (s : ℕ) (ℓ₂ : Fin (orderOf a)) (c : Fin (orderOf a) → ℂ) :
    ∑ ℓ₁ : Fin (orderOf a), c ℓ₁ • dlogFourierState a s ℓ₁ ℓ₂
      = c ⟨(s * (ℓ₂ : ℕ)) % orderOf a, Nat.mod_lt _ (orderOf_pos a)⟩
          • (orderEigenstate a ℓ₂).vec := by
  simp only [dlogFourierState_eq_ite, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq' Finset.univ
    (⟨(s * (ℓ₂ : ℕ)) % orderOf a, Nat.mod_lt _ (orderOf_pos a)⟩ : Fin (orderOf a))
    (fun ℓ₁ => c ℓ₁ • (orderEigenstate a ℓ₂).vec), ite_eq_left (Finset.mem_univ _)]

/-- **The inverse-Fourier double sum (5.73)** of Nielsen & Chuang Exercise 5.23,
`(1/r) ∑_{ℓ₁,ℓ₂<r} e^{2πi(ℓ₁x₁+ℓ₂x₂)/r} |f̂(ℓ₁,ℓ₂)⟩`, as a vector of the value register
`(qudit N).space`. The sign is the inverse-Fourier-transform sign `+` of eq. (5.64) and step 4 of
the algorithm (the printed (5.73) shows the forward `−`; see `dlogForwardFourierSum` and the module
docstring). -/
def dlogInverseFourierSum (s x₁ x₂ : ℕ) : (qudit N).space :=
  (orderOf a : ℂ)⁻¹ • ∑ ℓ₁ : Fin (orderOf a), ∑ ℓ₂ : Fin (orderOf a),
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((ℓ₁ : ℕ) * (x₁ : ℂ) + (ℓ₂ : ℕ) * (x₂ : ℂ)) / (orderOf a : ℂ))
      • dlogFourierState a s ℓ₁ ℓ₂

/-- **Computing (5.73) using (5.70).** The `ℓ₁`-sum collapses via the constraint `ℓ₁ ≡ s·ℓ₂ (mod r)`
to the single-`ℓ₂` inverse transform, the `ℓ₁`-phase `e^{2πiℓ₁x₁/r}` becoming `e^{2πi·s·ℓ₂·x₁/r}`:

  `(1/r) ∑_{ℓ₁,ℓ₂} e^{2πi(ℓ₁x₁+ℓ₂x₂)/r} |f̂(ℓ₁,ℓ₂)⟩`
    `= (1/r) ∑_{ℓ₂} e^{2πiℓ₂(s·x₁+x₂)/r} |f̂(ℓ₂)⟩`. -/
theorem dlogInverseFourierSum_collapse (s x₁ x₂ : ℕ) :
    dlogInverseFourierSum a s x₁ x₂
      = (orderOf a : ℂ)⁻¹ • ∑ ℓ₂ : Fin (orderOf a),
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((ℓ₂ : ℕ) * (s * x₁ + x₂ : ℕ)) /
              (orderOf a : ℂ))
            • (orderEigenstate a ℓ₂).vec := by
  rw [dlogInverseFourierSum, Finset.sum_comm]
  refine congrArg (_ • ·) ?_
  refine Finset.sum_congr rfl (fun ℓ₂ _ => ?_)
  rw [inner_ell1_pick a s ℓ₂
    (fun ℓ₁ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((ℓ₁ : ℕ) * (x₁ : ℂ) + (ℓ₂ : ℕ) * (x₂ : ℂ)) / (orderOf a : ℂ)))]
  refine congrArg (· • _) ?_
  -- phase: e^{2πi((s·ℓ₂ % r)·x₁ + ℓ₂·x₂)/r} = e^{2πi·ℓ₂·(s·x₁+x₂)/r}, as (s·ℓ₂ % r) ≡ s·ℓ₂ (mod r)
  obtain ⟨q, hq⟩ : ∃ q, s * (ℓ₂ : ℕ) = (s * (ℓ₂ : ℕ)) % orderOf a + orderOf a * q :=
    ⟨s * (ℓ₂ : ℕ) / orderOf a, (Nat.mod_add_div _ _).symm⟩
  have hcast : (((s * (ℓ₂ : ℕ)) % orderOf a : ℕ) : ℂ)
      = ((s * (ℓ₂ : ℕ) : ℕ) : ℂ) - (orderOf a : ℂ) * (q : ℂ) :=
    eq_sub_of_add_eq (by exact_mod_cast hq.symm)
  have hrne : (orderOf a : ℂ) ≠ 0 := by exact_mod_cast (orderOf_pos a).ne'
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((q * x₁ : ℕ) : ℤ), ?_⟩
  rw [hcast]
  push_cast
  field_simp
  ring

/-- **Nielsen & Chuang Exercise 5.23 — the reconstruction.** Computing the inverse-Fourier double
sum (5.73) using (5.70), the result is the value state `f(x₁,x₂)`, up to the section's `1/√r`
normalization:

  `(1/r) ∑_{ℓ₁,ℓ₂<r} e^{2πi(ℓ₁x₁+ℓ₂x₂)/r} |f̂(ℓ₁,ℓ₂)⟩ = (1/√r) |f(x₁,x₂)⟩`.

The `ℓ₁`-sum collapses (`dlogInverseFourierSum_collapse`) to the single-`ℓ₂` inverse discrete
Fourier transform `orderEigenstate_reconstruct` (eq. 5.45) at value index `s·x₁+x₂`; the leftover
`(1/r)·√r` is `1/√r`. -/
theorem dlogInverseFourierSum_eq_smul_dlogBasisState (s x₁ x₂ : ℕ) :
    dlogInverseFourierSum a s x₁ x₂
      = (Real.sqrt (orderOf a) : ℂ)⁻¹ • (dlogBasisState a s x₁ x₂).vec := by
  rw [dlogInverseFourierSum_collapse, sum_orderEigenstate_phase a (s * x₁ + x₂), dlogBasisState_vec,
    smul_smul, inv_natCast_orderOf_mul_ofReal_sqrt]

/-- **The literal printed inverse-Fourier double sum (5.73)**, with the forward sign `e^{−2πi(…)}`
exactly as printed on p. 239. -/
def dlogForwardFourierSum (s x₁ x₂ : ℕ) : (qudit N).space :=
  (orderOf a : ℂ)⁻¹ • ∑ ℓ₁ : Fin (orderOf a), ∑ ℓ₂ : Fin (orderOf a),
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
        ((ℓ₁ : ℕ) * (x₁ : ℂ) + (ℓ₂ : ℕ) * (x₂ : ℂ)) / (orderOf a : ℂ)))
      • dlogFourierState a s ℓ₁ ℓ₂

/-- **Computing the printed (5.73) using (5.70)** — the forward-sign twin of
`dlogInverseFourierSum_collapse`. The `ℓ₁`-sum collapses via the constraint to the single-`ℓ₂` sum,
carrying the printed `−` sign, so the surviving phase is `e^{−2πiℓ₂(s·x₁+x₂)/r}`, written as the
equal `e^{2πiℓ₂·(r−1)(s·x₁+x₂)/r}` to match the inverse-DFT reconstruction. -/
theorem dlogForwardFourierSum_collapse (s x₁ x₂ : ℕ) :
    dlogForwardFourierSum a s x₁ x₂
      = (orderOf a : ℂ)⁻¹ • ∑ ℓ₂ : Fin (orderOf a),
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
              ((ℓ₂ : ℕ) * ((orderOf a - 1) * (s * x₁ + x₂) : ℕ)) / (orderOf a : ℂ))
            • (orderEigenstate a ℓ₂).vec := by
  have hr : 0 < orderOf a := orderOf_pos a
  have hrne : (orderOf a : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [dlogForwardFourierSum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun ℓ₂ _ => ?_)
  rw [inner_ell1_pick a s ℓ₂
    (fun ℓ₁ => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
        ((ℓ₁ : ℕ) * (x₁ : ℂ) + (ℓ₂ : ℕ) * (x₂ : ℂ)) / (orderOf a : ℂ))))]
  congr 1
  obtain ⟨q, hq⟩ : ∃ q, s * (ℓ₂ : ℕ) = (s * (ℓ₂ : ℕ)) % orderOf a + orderOf a * q :=
    ⟨s * (ℓ₂ : ℕ) / orderOf a, (Nat.mod_add_div _ _).symm⟩
  have hcast : (((s * (ℓ₂ : ℕ)) % orderOf a : ℕ) : ℂ)
      = ((s * (ℓ₂ : ℕ) : ℕ) : ℂ) - (orderOf a : ℂ) * (q : ℂ) :=
    eq_sub_of_add_eq (by exact_mod_cast hq.symm)
  have hsub : ((orderOf a - 1 : ℕ) : ℂ) = (orderOf a : ℂ) - 1 := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨((q * x₁ : ℕ) : ℤ) - ((ℓ₂ : ℕ) * (s * x₁ + x₂) : ℕ), ?_⟩
  rw [hcast]
  push_cast [hsub]
  field_simp
  ring

/-- **The printed sign gives the reflected state.** With N&C's printed `e^{−2πi(…)}` (the *forward*
sign, not the inverse transform's `+` of eq. 5.64), the double sum reconstructs the reflected value
state `|a^{−(s·x₁+x₂)}⟩ = |f(−x₁,−x₂)⟩` (the `|a^{(r−1)m}⟩` of the collapse), up to `1/√r` —
**not** `|f(x₁,x₂)⟩`. This is why the inverse-transform sign `+` (`dlogInverseFourierSum`) is the
faithful one; the printed `−` is a sign misprint, exhibited here rather than silently corrected. -/
theorem dlogForwardFourierSum_eq_smul_reflected (s x₁ x₂ : ℕ) :
    dlogForwardFourierSum a s x₁ x₂
      = (Real.sqrt (orderOf a) : ℂ)⁻¹
          • (quditBasis (orbitIndex a ((orderOf a - 1) * (s * x₁ + x₂)))).vec := by
  rw [dlogForwardFourierSum_collapse, sum_orderEigenstate_phase a ((orderOf a - 1) * (s * x₁ + x₂)),
    smul_smul, inv_natCast_orderOf_mul_ofReal_sqrt]

end AxQM
