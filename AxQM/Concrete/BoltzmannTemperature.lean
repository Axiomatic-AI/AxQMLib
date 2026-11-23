/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Concrete: the two-level Boltzmann distribution and its temperature (N&C Exercise 8.25)

This file is real analysis about the
**Boltzmann (Gibbs) occupation probabilities** of a two-level system and the temperature they
encode, using only `ℝ`, `Real.exp`, and `Real.log`. Compare the density-matrix computations of
Exercises 8.16/8.17/8.22.

## The exercise

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §8.3.5 introduces **generalized
amplitude damping** `E_GAD` (eqs. 8.116–8.119), the finite-temperature relaxation channel. Its
stationary state (eq. 8.120) is the diagonal single-qubit density matrix

`ρ∞ = !![p, 0; 0, 1 - p]`,   `E_GAD(ρ∞) = ρ∞`,

whose ground-state (`|0⟩`) and excited-state (`|1⟩`) populations are `p` and `1 - p`.

Find temperature T describing stationary state ρ∞ of generalized amplitude damping via Boltzmann.

Matching the Boltzmann populations to the stationary populations, `p₀ = p` and `p₁ = 1 - p`, gives
`p/(1-p) = p₀/p₁ = e^{(E₁-E₀)/(k_B T)}`, hence the answer

`T = (E₁ - E₀) / (k_B ln(p/(1-p)))`.

## Contents

* `boltzmannGround`, `boltzmannExcited` — the occupation probabilities `p₀`, `p₁` (the Boltzmann
  distribution of the exercise).
* `boltzmann_partition_pos` — the partition function `Z` is strictly positive (so the probabilities
  are always well defined).
* `boltzmannGround_add_boltzmannExcited` — normalization `p₀ + p₁ = 1`, for *every* `T`.
* `boltzmannTemperature` — **the answer**: the temperature `T = (E₁-E₀)/(k_B ln(p/(1-p)))`.
* `boltzmann_log_ratio_ne_zero` — the log-ratio `ln(p/(1-p))` (that temperature's denominator) is
  nonzero for `0 < p < 1`, `p ≠ 1/2`; shared by the two theorems below.
* `boltzmannGround_boltzmannTemperature`, `boltzmannExcited_boltzmannTemperature` — at that
  temperature the populations are exactly `p` and `1 - p`, i.e. it reproduces the stationary state
  `ρ∞ = diag(p, 1-p)`.
* `boltzmannTemperature_unique` — and it is the *unique* (nonzero) temperature that does so, so
  `boltzmannTemperature` genuinely "describes the state `ρ∞`".

## Hypotheses

The formula needs `0 < p < 1` (both populations positive, so `ln(p/(1-p))` is defined) and `p ≠ 1/2`
(else the populations are equal, `ln(1) = 0`, and the equilibrium is at infinite temperature — no
finite `T` exists). A nonzero energy gap `E₀ ≠ E₁` and `k_B ≠ 0` make the temperature finite and
nonzero. These are exactly the conditions under which the qubit has a genuine finite Boltzmann
temperature; `p > 1/2` (with `E₁ > E₀`) is the physical regime `T > 0`, `p < 1/2` the population
inversion / negative-temperature regime, both covered by the single formula.
-/

open Real

noncomputable section

namespace AxQM.Concrete

variable (E₀ E₁ kB T p : ℝ)

/-- **Boltzmann ground-state occupation** `p₀ = e^{-E₀/(k_B T)} / Z` of a two-level system with
energies `E₀` (state `|0⟩`) and `E₁` (state `|1⟩`) in thermal equilibrium at temperature `T`, with
partition function `Z = e^{-E₀/(k_B T)} + e^{-E₁/(k_B T)}` and Boltzmann constant `k_B` (N&C
Exercise 8.25). -/
def boltzmannGround : ℝ :=
  Real.exp (-E₀ / (kB * T)) / (Real.exp (-E₀ / (kB * T)) + Real.exp (-E₁ / (kB * T)))

/-- **Boltzmann excited-state occupation** `p₁ = e^{-E₁/(k_B T)} / Z` (companion of
`boltzmannGround`; N&C Exercise 8.25). -/
def boltzmannExcited : ℝ :=
  Real.exp (-E₁ / (kB * T)) / (Real.exp (-E₀ / (kB * T)) + Real.exp (-E₁ / (kB * T)))

/-- The partition function `Z = e^{-E₀/(k_B T)} + e^{-E₁/(k_B T)}` is strictly positive, so the
Boltzmann occupations are always well defined (a sum of two positive exponentials). -/
theorem boltzmann_partition_pos :
    0 < Real.exp (-E₀ / (kB * T)) + Real.exp (-E₁ / (kB * T)) := by positivity

/-- **Normalization of the Boltzmann distribution:** `p₀ + p₁ = 1`, for every temperature `T`
(the two occupations share the partition function `Z` as denominator). -/
theorem boltzmannGround_add_boltzmannExcited :
    boltzmannGround E₀ E₁ kB T + boltzmannExcited E₀ E₁ kB T = 1 := by
  rw [boltzmannGround, boltzmannExcited, ← add_div,
    div_self (boltzmann_partition_pos E₀ E₁ kB T).ne']

/-- **The temperature describing the stationary state `ρ∞ = diag(p, 1-p)`** (N&C Exercise 8.25, the
answer): `T = (E₁ - E₀) / (k_B ln(p/(1-p)))`, obtained by inverting the Boltzmann relation
`p/(1-p) = e^{(E₁-E₀)/(k_B T)}`. -/
def boltzmannTemperature : ℝ := (E₁ - E₀) / (kB * Real.log (p / (1 - p)))

/-- The log-ratio `ln(p/(1-p))` — the denominator of `boltzmannTemperature` — is nonzero for
admissible, unequal populations (`0 < p < 1`, `p ≠ 1/2`). Equal populations `p = 1/2` are the only
obstruction: there `p/(1-p) = 1` and `ln 1 = 0`, so no finite temperature exists (infinite
temperature / equal occupations). Shared by `boltzmannGround_boltzmannTemperature` and
`boltzmannTemperature_unique`, which both need the temperature to be finite. -/
theorem boltzmann_log_ratio_ne_zero (hp0 : 0 < p) (hp1 : p < 1) (hph : p ≠ 1 / 2) :
    Real.log (p / (1 - p)) ≠ 0 := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hpp : 0 < p / (1 - p) := div_pos hp0 h1p
  have hne1 : p / (1 - p) ≠ 1 := by
    intro h; apply hph
    have h2 : p = 1 - p := by field_simp [h1p.ne'] at h; linarith
    linarith
  exact Real.log_ne_zero_of_pos_of_ne_one hpp hne1

/-- **Exercise 8.25 (ground population).** At `T = boltzmannTemperature`, the Boltzmann ground-state
occupation equals `p` — the `|0⟩` population of the stationary state `ρ∞ = diag(p, 1-p)`. Needs the
populations strictly between `0` and `1` (`0 < p < 1`), unequal (`p ≠ 1/2`), a nonzero energy gap
(`E₀ ≠ E₁`), and `k_B ≠ 0`. -/
theorem boltzmannGround_boltzmannTemperature
    (hp0 : 0 < p) (hp1 : p < 1) (hph : p ≠ 1 / 2) (hE : E₀ ≠ E₁) (hkB : kB ≠ 0) :
    boltzmannGround E₀ E₁ kB (boltzmannTemperature E₀ E₁ kB p) = p := by
  set L := Real.log (p / (1 - p)) with hLdef
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hpp : 0 < p / (1 - p) := div_pos hp0 h1p
  have hL0 : L ≠ 0 := by rw [hLdef]; exact boltzmann_log_ratio_ne_zero p hp0 hp1 hph
  have hEne : E₁ - E₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hE)
  set T := boltzmannTemperature E₀ E₁ kB p with hTdef
  -- `(E₁ - E₀) / (k_B T) = ln(p/(1-p))`, the exponent that appears in the ratio `p₀/p₁`.
  have hET : (E₁ - E₀) / (kB * T) = L := by
    rw [hTdef, boltzmannTemperature]; field_simp; ring
  -- The ratio of the two exponentials is `p/(1-p)`.
  have hratio : Real.exp (-E₀ / (kB * T)) / Real.exp (-E₁ / (kB * T)) = p / (1 - p) := by
    rw [← Real.exp_sub]
    have hexp : -E₀ / (kB * T) - -E₁ / (kB * T) = L := by
      rw [div_sub_div_same]; rw [← hET]; ring_nf
    rw [hexp, hLdef, Real.exp_log hpp]
  have hBpos : 0 < Real.exp (-E₁ / (kB * T)) := Real.exp_pos _
  rw [div_eq_div_iff hBpos.ne' h1p.ne'] at hratio
  rw [boltzmannGround, div_eq_iff (by positivity)]
  linear_combination hratio

/-- **Exercise 8.25 (excited population).** At `T = boltzmannTemperature`, the Boltzmann
excited-state occupation equals `1 - p` — the `|1⟩` population of `ρ∞ = diag(p, 1-p)`. Immediate
from the ground
population and normalization. -/
theorem boltzmannExcited_boltzmannTemperature
    (hp0 : 0 < p) (hp1 : p < 1) (hph : p ≠ 1 / 2) (hE : E₀ ≠ E₁) (hkB : kB ≠ 0) :
    boltzmannExcited E₀ E₁ kB (boltzmannTemperature E₀ E₁ kB p) = 1 - p := by
  have hsum := boltzmannGround_add_boltzmannExcited E₀ E₁ kB (boltzmannTemperature E₀ E₁ kB p)
  have hg := boltzmannGround_boltzmannTemperature E₀ E₁ kB p hp0 hp1 hph hE hkB
  linarith [hsum, hg]

/-- **Exercise 8.25 (uniqueness).** `boltzmannTemperature` is the *only* nonzero temperature at
which the Boltzmann ground occupation equals `p`: if `boltzmannGround E₀ E₁ kB T = p` for some
`T ≠ 0`
(with `0 < p < 1`, `p ≠ 1/2`, `k_B ≠ 0`), then `T = boltzmannTemperature E₀ E₁ kB p`. Together with
`boltzmannGround_boltzmannTemperature` this makes it *the* temperature describing `ρ∞`. -/
theorem boltzmannTemperature_unique
    (hp0 : 0 < p) (hp1 : p < 1) (hph : p ≠ 1 / 2) (hkB : kB ≠ 0) (hT : T ≠ 0)
    (hEq : boltzmannGround E₀ E₁ kB T = p) :
    T = boltzmannTemperature E₀ E₁ kB p := by
  set L := Real.log (p / (1 - p)) with hLdef
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hL0 : L ≠ 0 := by rw [hLdef]; exact boltzmann_log_ratio_ne_zero p hp0 hp1 hph
  have hkT : kB * T ≠ 0 := mul_ne_zero hkB hT
  have hBpos : 0 < Real.exp (-E₁ / (kB * T)) := Real.exp_pos _
  have hZ : 0 < Real.exp (-E₀ / (kB * T)) + Real.exp (-E₁ / (kB * T)) := by positivity
  rw [boltzmannGround, div_eq_iff hZ.ne'] at hEq
  have hratio : Real.exp (-E₀ / (kB * T)) / Real.exp (-E₁ / (kB * T)) = p / (1 - p) := by
    rw [div_eq_div_iff hBpos.ne' h1p.ne']; linear_combination hEq
  have hexpeq : Real.exp ((E₁ - E₀) / (kB * T)) = p / (1 - p) := by
    rw [← hratio, ← Real.exp_sub]; congr 1; rw [div_sub_div_same]; ring_nf
  have hlog : (E₁ - E₀) / (kB * T) = L := by
    have h := congrArg Real.log hexpeq
    rw [Real.log_exp] at h
    rw [hLdef]; exact h
  rw [div_eq_iff hkT] at hlog
  rw [boltzmannTemperature, eq_div_iff (mul_ne_zero hkB hL0)]
  rw [hlog]; ring

end AxQM.Concrete

end
