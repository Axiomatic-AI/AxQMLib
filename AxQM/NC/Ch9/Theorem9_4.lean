/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PureState
import AxQM.Postulates.API.Uhlmann
import AxQM.Postulates.API.Fidelity
import ToMathlib.Analysis.InnerProductSpace.Uhlmann

/-!
# Nielsen & Chuang, Theorem 9.4 (Uhlmann's theorem)

Uhlmann's theorem: F(rho,sigma)=max over purifications |<psi|phi>|.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 9.4 (p. 410).

Uhlmann's theorem characterizes the fidelity `F(ρ, σ)` (N&C `(9.53)`,
`State.fidelity`) as the **greatest overlap** `‖⟨ψ|φ⟩‖` achievable between a
purification `|ψ⟩` of `ρ` and a purification `|φ⟩` of `σ` into the doubled system. It is
the physics companion of N&C Theorem 9.1 (the trace distance as a maximum over
measurements): both express a distance measure as an extremum, but where 9.1 maximizes a
classical distance over measurements, 9.4 maximizes a pure-state overlap over purifications.

## The physical form

The theorem is `State.isGreatest_norm_overlap_purification`, phrased for states:

* the maximization ranges over `ψ φ : PureState (S ⊗ S)` — pure states of the doubled
  system, the ancilla being a *copy of the system* `S` (N&C's "system `R`, a copy of `Q`");
* `ψ` **is a purification of** `ρ` is the physical condition `ψ.toState.reducedLeft = ρ`:
  tracing out the ancilla recovers `ρ` (`State.reducedLeft`, the marginal of §2.4.3);
* the overlap `⟨ψ|φ⟩` is `PureState.overlap`, the transition amplitude;
* the value is `ρ.fidelity σ`, packaged — exactly as Theorem 9.1's headline — as an
  `IsGreatest`: the fidelity both is attained by some pair of purifications and bounds every
  achievable overlap.

Its proof reduces the physical statement to the operator-level core:

* `TensorProduct.isGreatest_norm_inner_of_isPurification` (`ToMathlib`) — the abstract
  Uhlmann theorem `IsGreatest {‖⟪Ψ, Φ⟫‖ | Ψ, Φ purify ρ.op, σ.op into E ⊗ E} ‖√ρ √σ‖₁`;
* `State.fidelity_eq_traceNorm` — the fidelity–trace-norm bridge `F(ρ, σ) = ‖√ρ √σ‖₁`;
* `PureState.reducedLeft_toState_eq_iff_isPurification` — the purification bridge translating
  the physical `reducedLeft = ρ` into the abstract `TensorProduct.IsPurification ρ.op ψ.vec`.

## Faithfulness

N&C fix `R` to be *a copy of* `Q` (same dimension) and maximize over purifications into `RQ`;
we realize "a copy of `Q`" by the system `S` itself, so the doubled system is `S ⊗ S` with
state space `S.space ⊗ S.space` — matching the abstract theorem's `E ⊗ E` ancilla exactly.
The factor order (`QR` here vs. N&C's `RQ`) is immaterial: `reducedLeft` traces out the
ancilla and the overlap is unchanged. The maximization being **attained** (an `IsGreatest`,
not merely a supremum) is faithful to N&C's `max`.

## Main statements

* `State.isGreatest_norm_overlap_purification` — Uhlmann's theorem, `(9.62)`:
  `F(ρ, σ) = max ‖⟨ψ|φ⟩‖` over purifications `ψ` of `ρ`, `φ` of `σ` into `S ⊗ S`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Theorem 9.4 (Uhlmann's theorem)**, `(9.62)`: the fidelity `F(ρ, σ)`
is the **greatest overlap magnitude** `‖⟨ψ|φ⟩‖` achievable over all purifications `ψ` of `ρ`
and `φ` of `σ` into the doubled system `S ⊗ S` (the ancilla a copy of the system):
`F(ρ, σ) = max_{|ψ⟩,|φ⟩} |⟨ψ|φ⟩|`.

Packaged as `IsGreatest`: `ρ.fidelity σ` both lies in the achievable set (attained by the
optimal pair of purifications) and upper-bounds it. Here a *purification* of `ρ` is a pure
state `ψ` of `S ⊗ S` whose left marginal `ψ.toState.reducedLeft` is `ρ`, and the overlap is
`PureState.overlap`.

The proof reduces to the operator-level core
`TensorProduct.isGreatest_norm_inner_of_isPurification`: the fidelity is the trace norm
`‖√ρ √σ‖₁` (`State.fidelity_eq_traceNorm`), and the physics achievability set coincides with
the abstract purification-overlap set via the purification bridge
`PureState.reducedLeft_toState_eq_iff_isPurification` (using that every purification of a
density operator has unit norm, `TensorProduct.norm_eq_one_of_isPurification`). -/
theorem State.isGreatest_norm_overlap_purification (ρ σ : State S) :
    IsGreatest
      {r : ℝ | ∃ ψ φ : PureState (S ⊗ S),
        ψ.toState.reducedLeft = ρ ∧ φ.toState.reducedLeft = σ ∧
        r = ‖ψ.overlap φ‖}
      (ρ.fidelity σ) := by
  -- The achievable-overlap set is exactly the abstract purification-overlap set.
  have hset :
      {r : ℝ | ∃ ψ φ : PureState (S ⊗ S),
        ψ.toState.reducedLeft = ρ ∧ φ.toState.reducedLeft = σ ∧ r = ‖ψ.overlap φ‖}
      = {r : ℝ | ∃ Ψ Φ : TensorProduct ℂ S.space S.space,
        TensorProduct.IsPurification ρ.op Ψ ∧ TensorProduct.IsPurification σ.op Φ ∧
        r = ‖(inner ℂ Ψ Φ : ℂ)‖} := by
    ext r
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ψ, φ, hψ, hφ, rfl⟩
      exact ⟨ψ.vec, φ.vec,
        (ψ.reducedLeft_toState_eq_iff_isPurification ρ).mp hψ,
        (φ.reducedLeft_toState_eq_iff_isPurification σ).mp hφ, rfl⟩
    · rintro ⟨Ψ, Φ, hΨ, hΦ, rfl⟩
      exact ⟨⟨Ψ, TensorProduct.norm_eq_one_of_isPurification ρ.isDensity hΨ⟩,
        ⟨Φ, TensorProduct.norm_eq_one_of_isPurification σ.isDensity hΦ⟩,
        (PureState.reducedLeft_toState_eq_iff_isPurification _ ρ).mpr hΨ,
        (PureState.reducedLeft_toState_eq_iff_isPurification _ σ).mpr hΦ, rfl⟩
  rw [State.fidelity_eq_traceNorm, hset]
  exact TensorProduct.isGreatest_norm_inner_of_isPurification ρ.isDensity.nonneg σ.isDensity.nonneg

end AxQM
