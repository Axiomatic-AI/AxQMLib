/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_4
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Nielsen & Chuang, Exercise 9.17 (The angle between states is a bounded distance)

Show 0<=A(rho,sigma)<=pi/2 with equality in first iff rho=sigma (angle metric).
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 9.17 (p. 413).

The **angle** between two states is `A(ρ, σ) ≡ arccos F(ρ, σ)` (N&C `(9.82)`), where
`F` is `State.fidelity`. N&C introduces it as a candidate metric derived
from the fidelity: since the fidelity is an "upside-down" distance (largest, `F = 1`, when
the states coincide, smallest when they are orthogonal), taking `arccos` turns it into an
honest non-negative distance. This exercise pins down its elementary range.

## What the exercise reduces to

The two bounds are `arccos` bookkeeping *once the range of the fidelity is known*:

* `A(ρ, σ) ≥ 0` is unconditional — `arccos` is non-negative everywhere (`Real.arccos_nonneg`);
* `A(ρ, σ) ≤ π/2` is `arccos x ≤ π/2 ↔ 0 ≤ x` (`Real.arccos_le_pi_div_two`) applied to
  `F(ρ, σ) ≥ 0` (`State.fidelity_nonneg`);
* `A(ρ, σ) = 0 ↔ ρ = σ` is `arccos x = 0 ↔ 1 ≤ x` (`Real.arccos_eq_zero`): combined with
  `F(ρ, σ) ≤ 1` this reads `F(ρ, σ) = 1`, which is `ρ = σ`.

So the real content is the **range of the fidelity**, `0 ≤ F(ρ, σ) ≤ 1` with `F = 1 ⟺ ρ = σ`
— the properties that make the fidelity (and hence the angle) a distance measure, which N&C
uses freely in §9.2.2 before this exercise. Non-negativity (`State.fidelity_nonneg`) is
already in the library; this file supplies the two missing halves and then the angle facts:

* `State.fidelity_le_one` — `F(ρ, σ) ≤ 1`;
* `State.fidelity_eq_one_iff` — `F(ρ, σ) = 1 ↔ ρ = σ`.

Both are proved from **Uhlmann's theorem** (`State.isGreatest_norm_overlap_purification`,
Theorem 9.4): `F(ρ, σ)` is the *greatest* overlap `‖⟨ψ|φ⟩‖` over purifications `ψ` of `ρ`
and `φ` of `σ`. For the upper bound, the attaining pair are unit vectors, so their overlap
is `≤ 1` by Cauchy–Schwarz (`norm_inner_le_norm`). For the equality case, `F = 1` forces
`‖⟨ψ|φ⟩‖ = ‖ψ‖‖φ‖`, the Cauchy–Schwarz *equality* case (`norm_inner_eq_norm_iff`), so the
two purifications differ only by a global phase `φ.vec = r • ψ.vec` with `‖r‖ = 1`; a global
phase is invisible to the density operator (`PureState.toState_eq_of_vec_eq_smul`), hence
their left marginals agree, i.e. `σ = ρ`. The converse is `State.fidelity_self`.

These fidelity corollaries are used by later Chapter 9 items, e.g. the contractivity of the angle,
Exercise 9.18.

## Main statements

* `AxQM.State.angle` — the angle metric `A(ρ, σ) = arccos F(ρ, σ)` (N&C `(9.82)`);
* `AxQM.State.angle_nonneg` — `0 ≤ A(ρ, σ)`;
* `AxQM.State.angle_le_pi_div_two` — `A(ρ, σ) ≤ π/2`;
* `AxQM.State.angle_eq_zero_iff` — `A(ρ, σ) = 0 ↔ ρ = σ` (equality in the first
  inequality iff the states coincide) — the heart of Exercise 9.17.

Supporting reusable fidelity range facts:

* `AxQM.State.fidelity_le_one` — `F(ρ, σ) ≤ 1`;
* `AxQM.State.fidelity_eq_one_iff` — `F(ρ, σ) = 1 ↔ ρ = σ`;
* `AxQM.State.fidelity_sq_eq_one_iff` — `F(ρ, σ)² = 1 ↔ ρ = σ` (the squared-fidelity
  form of N&C's `(9.127)` convention, used by Exercise 9.23).
-/

namespace AxQM

variable {S : QSystem}

/-- **The fidelity is bounded above by 1**, `F(ρ, σ) ≤ 1`. By Uhlmann's theorem
(`State.isGreatest_norm_overlap_purification`) the fidelity is attained as the overlap
`‖⟨ψ|φ⟩‖` of two purifications `ψ`, `φ`, which are unit vectors; Cauchy–Schwarz
(`norm_inner_le_norm`) then bounds that overlap by `‖ψ‖‖φ‖ = 1`. -/
theorem State.fidelity_le_one (ρ σ : State S) : ρ.fidelity σ ≤ 1 := by
  obtain ⟨ψ, φ, -, -, hr⟩ := (State.isGreatest_norm_overlap_purification ρ σ).1
  rw [hr, PureState.overlap_def]
  calc ‖inner ℂ ψ.vec φ.vec‖ ≤ ‖ψ.vec‖ * ‖φ.vec‖ := norm_inner_le_norm _ _
    _ = 1 := by rw [ψ.normalized, φ.normalized, mul_one]

/-- **The fidelity equals 1 exactly when the states coincide**, `F(ρ, σ) = 1 ↔ ρ = σ`
(Nielsen & Chuang `(9.60)`, the defining property of the fidelity as a distance measure).

Forward direction: by Uhlmann's theorem `F(ρ, σ) = 1` is attained as `‖⟨ψ|φ⟩‖` for
purifications `ψ` of `ρ` and `φ` of `σ`; equality `‖⟨ψ|φ⟩‖ = ‖ψ‖‖φ‖` in Cauchy–Schwarz
(`norm_inner_eq_norm_iff`) makes `φ.vec = r • ψ.vec` a global phase (`‖r‖ = 1`), which is
invisible to the density operator (`PureState.toState_eq_of_vec_eq_smul`), so the left
marginals agree: `σ = ρ`. Converse: `State.fidelity_self`. -/
theorem State.fidelity_eq_one_iff (ρ σ : State S) : ρ.fidelity σ = 1 ↔ ρ = σ := by
  constructor
  · intro hF
    obtain ⟨ψ, φ, hψ, hφ, hr⟩ := (State.isGreatest_norm_overlap_purification ρ σ).1
    -- The attained overlap magnitude is `1`.
    have hnorm : ‖ψ.overlap φ‖ = 1 := by rw [← hr, hF]
    have hψ0 : ψ.vec ≠ 0 := by rw [← norm_ne_zero_iff, ψ.normalized]; norm_num
    have hφ0 : φ.vec ≠ 0 := by rw [← norm_ne_zero_iff, φ.normalized]; norm_num
    -- Cauchy–Schwarz saturates, so `φ.vec` and `ψ.vec` are proportional.
    have key : ‖inner ℂ ψ.vec φ.vec‖ = ‖ψ.vec‖ * ‖φ.vec‖ := by
      rw [ψ.normalized, φ.normalized, mul_one, ← PureState.overlap_def, hnorm]
    obtain ⟨r, -, hrv⟩ := (norm_inner_eq_norm_iff hψ0 hφ0).1 key
    -- The proportionality constant is a global phase.
    have hrnorm : ‖r‖ = 1 := by
      have h := congrArg norm hrv
      rw [norm_smul, ψ.normalized, mul_one, φ.normalized] at h
      exact h.symm
    -- A global phase leaves the density operator — hence the left marginal — unchanged.
    have hst : φ.toState = ψ.toState := PureState.toState_eq_of_vec_eq_smul hrnorm hrv
    have hred := congrArg State.reducedLeft hst
    rw [hφ, hψ] at hred
    exact hred.symm
  · rintro rfl
    exact State.fidelity_self ρ

/-- **The squared fidelity equals 1 exactly when the states coincide**, `F(ρ, σ)² = 1 ↔ ρ = σ`.
A corollary of `State.fidelity_eq_one_iff` given the range `0 ≤ F(ρ, σ) ≤ 1`: from `F² = 1` and
`F ≥ 0` one gets `F = 1` (`le_antisymm` with `F ≤ 1`), and conversely `F = 1` gives `F² = 1`.
This packages the N&C squared-fidelity convention (as in `(9.127)`) as a distance-measure
characterization. -/
theorem State.fidelity_sq_eq_one_iff (ρ σ : State S) : ρ.fidelity σ ^ 2 = 1 ↔ ρ = σ :=
  ⟨fun h => (State.fidelity_eq_one_iff ρ σ).mp
      (le_antisymm (State.fidelity_le_one ρ σ) (by nlinarith [h, State.fidelity_nonneg ρ σ])),
    fun h => by rw [(State.fidelity_eq_one_iff ρ σ).mpr h]; norm_num⟩

/-- **The angle between two states** `A(ρ, σ) ≡ arccos F(ρ, σ)` (Nielsen & Chuang `(9.82)`):
the distance measure obtained by applying `arccos` to `State.fidelity`. -/
noncomputable def State.angle (ρ σ : State S) : ℝ := Real.arccos (ρ.fidelity σ)

/-- Unfolding lemma for the angle metric: `A(ρ, σ) = arccos F(ρ, σ)`. -/
theorem State.angle_def (ρ σ : State S) : ρ.angle σ = Real.arccos (ρ.fidelity σ) := rfl

/-- **The angle is non-negative**, `0 ≤ A(ρ, σ)` — the lower bound of Exercise 9.17. This
holds unconditionally because `arccos` is non-negative everywhere (`Real.arccos_nonneg`). -/
theorem State.angle_nonneg (ρ σ : State S) : 0 ≤ ρ.angle σ :=
  Real.arccos_nonneg _

/-- **The angle is at most `π/2`**, `A(ρ, σ) ≤ π/2` — the upper bound of Exercise 9.17,
from `arccos x ≤ π/2 ↔ 0 ≤ x` (`Real.arccos_le_pi_div_two`) applied to the non-negativity
of the fidelity (`State.fidelity_nonneg`). -/
theorem State.angle_le_pi_div_two (ρ σ : State S) : ρ.angle σ ≤ Real.pi / 2 :=
  Real.arccos_le_pi_div_two.2 (State.fidelity_nonneg ρ σ)

/-- **The angle vanishes exactly when the states coincide**, `A(ρ, σ) = 0 ↔ ρ = σ` — the
"equality in the first inequality" clause of Exercise 9.17. Via `arccos x = 0 ↔ 1 ≤ x`
(`Real.arccos_eq_zero`) the condition `A = 0` says `F(ρ, σ) ≥ 1`, which with the upper bound
`F(ρ, σ) ≤ 1` means `F(ρ, σ) = 1`, i.e. `ρ = σ` (`State.fidelity_eq_one_iff`). -/
theorem State.angle_eq_zero_iff (ρ σ : State S) : ρ.angle σ = 0 ↔ ρ = σ := by
  rw [State.angle_def, Real.arccos_eq_zero, ← State.fidelity_eq_one_iff]
  exact ⟨fun h => le_antisymm (State.fidelity_le_one ρ σ) h, fun h => h.ge⟩

end AxQM
