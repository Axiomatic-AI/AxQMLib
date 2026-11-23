/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Fannes
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Nielsen & Chuang, Theorem 11.6 (Fannes' inequality)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.6, Box 11.2, p. 512.

*Fannes' inequality* bounds how much the von Neumann entropy can change when a state is perturbed.
N&C's Theorem 11.6 states **two** inequalities within the theorem box; both are formalised here:

* `abs_vonNeumannEntropy_sub_le_fannes` — the main bound (N&C eq. (11.44)):
  `|S(ρ) − S(σ)| ≤ T · log d + η(T)`, under the hypothesis `T ≤ 1/e`;
* `abs_vonNeumannEntropy_sub_le_fannes_weak` — the weaker **unconditional** bound (N&C eq. (11.45)):
  `|S(ρ) − S(σ)| ≤ T · log d + 1/e`, with the `T ≤ 1/e` restriction removed,

where `d` is the dimension of the state space, `η(x) = −x log x = Real.negMulLog x`, and
`1/e = Real.exp (-1)`.

## The trace-distance convention

N&C's Box 11.2 writes the trace distance in its Fannes proof as `T(ρ, σ) = tr(R) + tr(Q)` where
`ρ − σ = Q − R` is the Jordan decomposition into positive parts (eq. (11.46)): this is the **full
trace norm** `‖ρ − σ‖₁ = tr|ρ − σ|`, *twice* the metric trace distance `D(ρ, σ) = ½‖ρ − σ‖₁` of
N&C §9.2.1 eq. (9.11). The library `State.traceDistance` is the metric `D = ½‖·‖₁`, so N&C's `T`
equals `2 · State.traceDistance`. Both theorems are stated with the trace distance
and the explicit factor `2`: N&C's `T` is `2 · D(ρ, σ)` throughout, so these are exactly
N&C (11.44) and (11.45) with `T = 2D`.

## Base convention

The library measures entropy in *nats* (natural logarithm), so `S`, `log`, and `η` throughout use
`Real.log`.

* **(11.44) is base-invariant.** Every term — `S`, `log d`, and the additive `η(T)` — scales by the
  same factor `ln b` under a change to base `b`, so the inequality is the base-scaled image of
  N&C's base-2 statement; the nat rendering is a faithful reformulation.
* **(11.45)'s constant `1/e` is base-specific, and the nat rendering is the correct one.** Its
  additive term is `1/e = max_{x ≥ 0} η(x)`, a *constant*, not a term that scales with `S` and
  `log d`. The maximiser `x = 1/e` of `η_b(x) = −x log_b x` is base-independent, but the maximum
  *value* `η_b(1/e) = 1/(e · ln b)` is not: it is `1/e` in nats and `1/(e · ln 2) ≈ 0.53` in
  base 2. We state (11.45) in nats precisely because there `max η = 1/e = Real.exp (-1)`, matching
  N&C's literal `1/e`; this is the mathematically-correct reading of N&C's constant (in a base-2
  presentation the max-`η` constant would instead be `1/(e · ln 2)`). Both theorem *statements* are
  faithful; only this constant is not base-invariant.

## Proof

Both bounds share the analytic core `State.abs_vonNeumannEntropy_sub_le_sum_abs_eigenvalues_diff`
(`AxQM/Postulates/API/Fannes.lean`), which — using the sorted eigenvalue spectra `r`, `s` of `ρ`,
`σ`, Mirsky's inequality, the total-variation bound `|rᵢ − sᵢ| ≤ Δ/2`, the continuity kernel
`Real.abs_negMulLog_sub_le`, and the grouping bound `Real.sum_negMulLog_le` — establishes, whenever
`‖ρ.op − σ.op‖₁ ≤ 1`, the `Δ`-form

`|S(ρ) − S(σ)| ≤ Δ · log d + η(Δ)`,  `Δ = ∑ᵢ |rᵢ − sᵢ|`.

The two theorems apply this core and then diverge only in the last step:

* **(11.44)** (`T ≤ 1/e`, hence `‖ρ.op − σ.op‖₁ = T ≤ 1`): with `Δ ≤ T` (Mirsky) and `log d ≥ 0`,
  and `η` monotone on `[0, 1/e]` (`Real.strictMonoOn_negMulLog_Icc`) with `0 ≤ Δ ≤ T ≤ 1/e`, the
  `Δ`-form lifts to `|S(ρ) − S(σ)| ≤ T · log d + η(T)` (eq. (11.49)).
* **(11.45)** (unconditional): N&C's remark that it "follows with minor modifications" is inaccurate
  — the continuity step needs `|rᵢ − sᵢ| ≤ 1/2`, which fails once `T > 1`. We split on `T`:
  * if `T ≤ 1` the core applies, and `η(Δ) ≤ 1/e` (`Real.negMulLog_le_exp_neg_one`, the maximum of
    `η`) with `Δ · log d ≤ T · log d` gives `|S(ρ) − S(σ)| ≤ T · log d + 1/e`;
  * if `T > 1` then `|S(ρ) − S(σ)| ≤ log d ≤ T · log d ≤ T · log d + 1/e` directly, since both
    entropies lie in `[0, log d]` (`State.vonNeumannEntropy_nonneg`,
    `State.vonNeumannEntropy_le_log_finrank`) and `log d ≥ 0`.

The correction to N&C's proof of the `|rᵢ − sᵢ| ≤ 1/2` step (N&C's "a moment's thought shows
`|rᵢ − sᵢ| ≤ 1/2`" does *not* follow from the eigenvalues lying in `[0,1]` — a pure `ρ` against `σ`
with spectrum `(0.4, 0.3, 0.3)` gives `|r₁ − s₁| = 0.6` — but from the total-variation bound
`|rᵢ − sᵢ| ≤ Δ/2`) lives in the core lemma's proof.

## Ingredients

Both statements are about `State.vonNeumannEntropy` and `State.traceDistance`. The shared analytic
core is the lemma `State.abs_vonNeumannEntropy_sub_le_sum_abs_eigenvalues_diff`
(`AxQM/Postulates/API/Fannes.lean`); the spectral and real-analysis results it uses are in
`ToMathlib/` (`Real.sum_negMulLog_le`, `Real.abs_negMulLog_sub_le`,
`Real.strictMonoOn_negMulLog_Icc`, `Real.negMulLog_le_exp_neg_one`, and Mirsky's
`IsSelfAdjoint.sum_abs_eigenvalues_sub_le_traceNorm`).
-/

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem}

/-- **Fannes' inequality** (Nielsen & Chuang, Theorem 11.6, eq. (11.44)). For states `ρ, σ` of a
quantum system `S` whose trace distance satisfies `2·D(ρ, σ) ≤ 1/e`, the von Neumann entropies
differ by at most

`|S(ρ) − S(σ)| ≤ 2·D(ρ, σ) · log d + η(2·D(ρ, σ))`,

where `d = S.dim` is the dimension of the state space and `η = Real.negMulLog`. Here `2·D(ρ, σ) =
‖ρ.op − σ.op‖₁` is N&C's trace-distance `T` (see the module docstring: N&C's `T` is the full trace
norm, twice the metric `State.traceDistance`), so this is exactly N&C (11.44) with `T = 2D`. -/
theorem State.abs_vonNeumannEntropy_sub_le_fannes (ρ σ : State S)
    (hT : 2 * ρ.traceDistance σ ≤ Real.exp (-1)) :
    |ρ.vonNeumannEntropy - σ.vonNeumannEntropy|
      ≤ 2 * ρ.traceDistance σ * Real.log (S.dim : ℝ)
        + Real.negMulLog (2 * ρ.traceDistance σ) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ S.space = n := ⟨_, rfl⟩
  -- `T = ‖ρ.op − σ.op‖₁ = 2·D(ρ, σ)` is N&C's trace distance; `T ≤ 1/e ≤ 1/2 ≤ 1`.
  set T : ℝ := (ρ.op - σ.op).traceNorm
  have hT2 : 2 * ρ.traceDistance σ = T := by rw [State.traceDistance_eq]; ring
  have hTe : T ≤ Real.exp (-1) := hT2 ▸ hT
  have hehalf : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := by gcongr
      _ = 1 / 2 := by norm_num
  have hT1 : T ≤ 1 := by linarith [hTe, hehalf]
  -- `log d ≥ 0`: `d = n ≥ 1` since a state forces `S.space` nontrivial.
  have hL0 : 0 ≤ Real.log (n : ℝ) := hn ▸ ρ.log_finrank_nonneg
  have hdimn : (S.dim : ℝ) = (n : ℝ) := by exact_mod_cast hn
  -- The shared `Δ`-form core, then lift `η(Δ) ≤ η(T)` by monotonicity on `[0, 1/e]`.
  have hcore := ρ.abs_vonNeumannEntropy_sub_le_sum_abs_eigenvalues_diff σ hn hT1
  set Δ : ℝ := ∑ i, |ρ.isDensity.isSymmetric.eigenvalues hn i
    - σ.isDensity.isSymmetric.eigenvalues hn i|
  have hMirsky : Δ ≤ T :=
    IsSelfAdjoint.sum_abs_eigenvalues_sub_le_traceNorm
      ρ.isDensity.isPositive.isSelfAdjoint σ.isDensity.isPositive.isSelfAdjoint hn
  have hΔ0 : 0 ≤ Δ := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hT0 : 0 ≤ T := ContinuousLinearMap.traceNorm_nonneg _
  have hmono : Δ.negMulLog ≤ T.negMulLog :=
    Real.strictMonoOn_negMulLog_Icc.monotoneOn ⟨hΔ0, le_trans hMirsky hTe⟩ ⟨hT0, hTe⟩ hMirsky
  have hmul : Δ * Real.log (n : ℝ) ≤ T * Real.log (n : ℝ) :=
    mul_le_mul_of_nonneg_right hMirsky hL0
  rw [hT2, hdimn]
  calc |ρ.vonNeumannEntropy - σ.vonNeumannEntropy|
      ≤ Δ * Real.log (n : ℝ) + Δ.negMulLog := hcore
    _ ≤ T * Real.log (n : ℝ) + T.negMulLog := by linarith [hmul, hmono]

/-- **Weaker (unconditional) Fannes' inequality** (Nielsen & Chuang, Theorem 11.6, eq. (11.45)).
Dropping the `T ≤ 1/e` restriction, for *any* states `ρ, σ` of a quantum system `S`,

`|S(ρ) − S(σ)| ≤ 2·D(ρ, σ) · log d + 1/e`,

where `d = S.dim`, `1/e = Real.exp (-1)`, and `2·D(ρ, σ) = ‖ρ.op − σ.op‖₁` is N&C's trace-distance
`T` (see the module docstring). This is N&C (11.45) with `T = 2D`. The bound is genuinely weaker
than (11.44) — it replaces `η(T)` by its maximum `1/e` — but holds with no hypothesis on the trace
distance. -/
theorem State.abs_vonNeumannEntropy_sub_le_fannes_weak (ρ σ : State S) :
    |ρ.vonNeumannEntropy - σ.vonNeumannEntropy|
      ≤ 2 * ρ.traceDistance σ * Real.log (S.dim : ℝ) + Real.exp (-1) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ S.space = n := ⟨_, rfl⟩
  set T : ℝ := (ρ.op - σ.op).traceNorm
  have hT2 : 2 * ρ.traceDistance σ = T := by rw [State.traceDistance_eq]; ring
  have hL0 : 0 ≤ Real.log (n : ℝ) := hn ▸ ρ.log_finrank_nonneg
  have hexp0 : (0 : ℝ) ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hdimn : (S.dim : ℝ) = (n : ℝ) := by exact_mod_cast hn
  rw [hT2, hdimn]
  by_cases hT1 : T ≤ 1
  · -- Case `T ≤ 1`: the shared core, then bound the tail by the maximum `η(Δ) ≤ 1/e`.
    have hcore := ρ.abs_vonNeumannEntropy_sub_le_sum_abs_eigenvalues_diff σ hn hT1
    set Δ : ℝ := ∑ i, |ρ.isDensity.isSymmetric.eigenvalues hn i
      - σ.isDensity.isSymmetric.eigenvalues hn i|
    have hMirsky : Δ ≤ T :=
      IsSelfAdjoint.sum_abs_eigenvalues_sub_le_traceNorm
        ρ.isDensity.isPositive.isSelfAdjoint σ.isDensity.isPositive.isSelfAdjoint hn
    have hΔ0 : 0 ≤ Δ := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hmul : Δ * Real.log (n : ℝ) ≤ T * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right hMirsky hL0
    have hηΔ : Δ.negMulLog ≤ Real.exp (-1) := Real.negMulLog_le_exp_neg_one hΔ0
    calc |ρ.vonNeumannEntropy - σ.vonNeumannEntropy|
        ≤ Δ * Real.log (n : ℝ) + Δ.negMulLog := hcore
      _ ≤ T * Real.log (n : ℝ) + Real.exp (-1) := by linarith [hmul, hηΔ]
  · -- Case `T > 1`: the crude bound `|S(ρ) − S(σ)| ≤ log d ≤ T · log d`.
    rw [not_le] at hT1
    have hSρ0 : 0 ≤ ρ.vonNeumannEntropy := ρ.vonNeumannEntropy_nonneg
    have hSσ0 : 0 ≤ σ.vonNeumannEntropy := σ.vonNeumannEntropy_nonneg
    have hSρd : ρ.vonNeumannEntropy ≤ Real.log (n : ℝ) := by
      have h := ρ.vonNeumannEntropy_le_log_finrank; rwa [hn] at h
    have hSσd : σ.vonNeumannEntropy ≤ Real.log (n : ℝ) := by
      have h := σ.vonNeumannEntropy_le_log_finrank; rwa [hn] at h
    calc |ρ.vonNeumannEntropy - σ.vonNeumannEntropy|
        ≤ Real.log (n : ℝ) := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      _ ≤ T * Real.log (n : ℝ) := le_mul_of_one_le_left hL0 hT1.le
      _ ≤ T * Real.log (n : ℝ) + Real.exp (-1) := by linarith [hexp0]

end AxQM
