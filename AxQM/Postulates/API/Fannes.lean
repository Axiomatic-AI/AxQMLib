/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.API.TraceDistance
import ToMathlib.Analysis.InnerProductSpace.MirskyInequality

/-!
# AxQM — the analytic core of Fannes' inequality

This file isolates the shared analytic core of Nielsen & Chuang's Theorem 11.6 (Fannes'
inequality), so that both the main bound (eq. (11.44)) and the weaker unconditional bound
(eq. (11.45)) — assembled in `AxQM/NC/Ch11/Theorem11_6.lean` — apply it rather than each
re-deriving it.

The core, `State.abs_vonNeumannEntropy_sub_le_sum_abs_eigenvalues_diff`, bounds the entropy
difference of two states by the "`Δ`-form"

`|S(ρ) − S(σ)| ≤ Δ · log d + η(Δ)`,  where `Δ = ∑ᵢ |rᵢ − sᵢ|`

is the `ℓ¹` distance between the sorted eigenvalue spectra `r`, `s` of `ρ`, `σ`
(`LinearMap.IsSymmetric.eigenvalues`), `d = finrank`, and `η = Real.negMulLog`. It is stated under
the single hypothesis `‖ρ.op − σ.op‖₁ ≤ 1`, which is exactly what makes the per-eigenvalue
continuity estimate available.

**Why `Δ`, and why the `‖·‖₁ ≤ 1` hypothesis.** The two N&C bounds diverge only *after* this point
— (11.44) lifts `η(Δ) ≤ η(T)` by monotonicity of `η` (valid for `T ≤ 1/e`), while (11.45) uses the
maximum `η(Δ) ≤ 1/e` — so the last common step is the `Δ`-form, and the core exposes `Δ`. The
hypothesis `‖ρ.op − σ.op‖₁ ≤ 1` gives, via Mirsky's inequality (`Δ ≤ ‖ρ.op − σ.op‖₁`) and the
total-variation bound `|rᵢ − sᵢ| ≤ Δ/2` (both spectra sum to `1`), the per-eigenvalue estimate
`|rᵢ − sᵢ| ≤ Δ/2 ≤ 1/2` that the continuity kernel `Real.abs_negMulLog_sub_le` requires.

The bounds where `Δ` is controlled by the `traceDistance` are in `AxQM/NC/Ch11/Theorem11_6.lean`.

## Main results

* `AxQM.State.log_finrank_nonneg` — `0 ≤ log (finrank ℂ S.space)`.
* `AxQM.State.abs_vonNeumannEntropy_sub_le_sum_abs_eigenvalues_diff` — the `Δ`-form core.
-/

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem}

/-- The logarithm of a quantum system's dimension is nonnegative: a `State` witnesses that
`S.space` is nontrivial, so `finrank ℂ S.space ≥ 1` and `log d ≥ 0`. The foundational
positivity fact used by every `log d`-type entropy bound (here, both forms of Fannes'
inequality). -/
theorem State.log_finrank_nonneg (ρ : State S) :
    0 ≤ Real.log (Module.finrank ℂ S.space : ℝ) := by
  have := ρ.nontrivial_space
  have hpos : 0 < Module.finrank ℂ S.space := Module.finrank_pos
  exact Real.log_nonneg (by exact_mod_cast hpos)

/-- **Analytic core of Fannes' inequality** (the `Δ`-form; Nielsen & Chuang Theorem 11.6, the
eq. (11.47)–(11.48) chain). For states `ρ, σ` of a quantum system `S` with sorted eigenvalue
spectra `r, s`, if the trace norm `‖ρ.op − σ.op‖₁ ≤ 1` then, writing `Δ = ∑ᵢ |rᵢ − sᵢ|`,

`|S(ρ) − S(σ)| ≤ Δ · log d + η(Δ)`,

where `d = finrank ℂ S.space` and `η = Real.negMulLog`. This is the step both Fannes bounds share;
they differ only in how the final `η(Δ)` term is bounded (see `AxQM/NC/Ch11/Theorem11_6.lean`).

The proof: `S(ρ) = ∑ᵢ η(rᵢ)`, `S(σ) = ∑ᵢ η(sᵢ)`
(`ContinuousLinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq`); Mirsky's inequality
gives `Δ ≤ ‖ρ.op − σ.op‖₁ ≤ 1`; since both spectra sum to `1`, the positive and negative parts of
`rᵢ − sᵢ` each sum to `Δ/2`, so `|rᵢ − sᵢ| ≤ Δ/2 ≤ 1/2` (total variation); the per-eigenvalue
continuity kernel `Real.abs_negMulLog_sub_le` then gives `|η(rᵢ) − η(sᵢ)| ≤ η(|rᵢ − sᵢ|)`, and
summing with the triangle inequality and the grouping bound `Real.sum_negMulLog_le` yields the
claim. -/
theorem State.abs_vonNeumannEntropy_sub_le_sum_abs_eigenvalues_diff (ρ σ : State S) {n : ℕ}
    (hn : Module.finrank ℂ S.space = n) (hT : (ρ.op - σ.op).traceNorm ≤ 1) :
    |ρ.vonNeumannEntropy - σ.vonNeumannEntropy|
      ≤ (∑ i, |ρ.isDensity.isSymmetric.eigenvalues hn i - σ.isDensity.isSymmetric.eigenvalues hn i|)
          * Real.log (n : ℝ)
        + (∑ i, |ρ.isDensity.isSymmetric.eigenvalues hn i
            - σ.isDensity.isSymmetric.eigenvalues hn i|).negMulLog := by
  classical
  set r : Fin n → ℝ := fun i => ρ.isDensity.isSymmetric.eigenvalues hn i
  set s : Fin n → ℝ := fun i => σ.isDensity.isSymmetric.eigenvalues hn i
  -- The entropies are the (nat) Shannon entropies of the spectra.
  have hSρ : ρ.vonNeumannEntropy = ∑ i, (r i).negMulLog := by
    rw [State.vonNeumannEntropy_def,
      ContinuousLinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq
        ρ.isDensity.isSymmetric hn, Real.entropy_eq]
  have hSσ : σ.vonNeumannEntropy = ∑ i, (s i).negMulLog := by
    rw [State.vonNeumannEntropy_def,
      ContinuousLinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq
        σ.isDensity.isSymmetric hn, Real.entropy_eq]
  -- Mirsky's inequality (N&C eq. (11.46)): `Δ ≤ ‖ρ.op − σ.op‖₁ ≤ 1`.
  have hMirsky : ∑ i, |r i - s i| ≤ (ρ.op - σ.op).traceNorm :=
    IsSelfAdjoint.sum_abs_eigenvalues_sub_le_traceNorm
      ρ.isDensity.isPositive.isSelfAdjoint σ.isDensity.isPositive.isSelfAdjoint hn
  set Δ : ℝ := ∑ i, |r i - s i| with hΔ_def
  have hΔ0 : 0 ≤ Δ := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hΔ1 : Δ ≤ 1 := le_trans hMirsky hT
  -- Both spectra are probability distributions: they sum to `1`.
  have hrsum : ∑ i, r i = 1 := ρ.isDensity.eigenvalues_sum_eq_one hn
  have hssum : ∑ i, s i = 1 := σ.isDensity.eigenvalues_sum_eq_one hn
  -- `|rⱼ − sⱼ| ≤ Δ/2`: the total-variation bound for equal-sum vectors.
  have hhalfsum : ∀ j, |r j - s j| ≤ Δ / 2 := by
    intro j
    have hd0 : ∑ i, (r i - s i) = 0 := by rw [Finset.sum_sub_distrib, hrsum, hssum]; ring
    have hsplit : (∑ i ∈ Finset.univ.erase j, (r i - s i)) + (r j - s j) = 0 := by
      rw [Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)]; exact hd0
    have hj : r j - s j = -∑ i ∈ Finset.univ.erase j, (r i - s i) := by linarith
    have hle : |r j - s j| ≤ ∑ i ∈ Finset.univ.erase j, |r i - s i| := by
      rw [hj, abs_neg]; exact Finset.abs_sum_le_sum_abs _ _
    have hsum : (∑ i ∈ Finset.univ.erase j, |r i - s i|) + |r j - s j| = Δ :=
      Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)
    linarith
  have hhalf : ∀ i, |r i - s i| ≤ 1 / 2 := fun i => by have := hhalfsum i; linarith [hΔ1]
  -- Per-eigenvalue continuity bound (N&C eq. (11.47)).
  have hpt : ∀ i, |(r i).negMulLog - (s i).negMulLog| ≤ (|r i - s i|).negMulLog := fun i =>
    Real.abs_negMulLog_sub_le (ρ.isDensity.eigenvalues_nonneg hn i)
      (ρ.isDensity.eigenvalues_le_one hn i) (σ.isDensity.eigenvalues_nonneg hn i)
      (σ.isDensity.eigenvalues_le_one hn i) (hhalf i)
  -- Grouping bound (N&C eq. (11.48)).
  have hgroup : ∑ i, (|r i - s i|).negMulLog ≤ Δ * Real.log (n : ℝ) + Δ.negMulLog := by
    have h := Real.sum_negMulLog_le (a := fun i => |r i - s i|) (fun i => abs_nonneg _)
    rw [hΔ_def]
    simpa [Fintype.card_fin] using h
  calc |ρ.vonNeumannEntropy - σ.vonNeumannEntropy|
      = |(∑ i, (r i).negMulLog) - ∑ i, (s i).negMulLog| := by rw [hSρ, hSσ]
    _ = |∑ i, ((r i).negMulLog - (s i).negMulLog)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |(r i).negMulLog - (s i).negMulLog| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|r i - s i|).negMulLog := Finset.sum_le_sum fun i _ => hpt i
    _ ≤ Δ * Real.log (n : ℝ) + Δ.negMulLog := hgroup

end AxQM
