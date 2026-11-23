/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FidelityPure

/-!
# Nielsen & Chuang, Exercise 9.21 (pure-vs-mixed trace distance / fidelity bound)

Prove 1-F(|psi>,sigma)^2 <= D(|psi>,sigma) for pure vs mixed states.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 9.21 (p. 416).

For a general pair of states the summary bound `(9.110)` reads
`1 − F(ρ, σ) ≤ D(ρ, σ) ≤ √(1 − F(ρ, σ)²)`. When one state is **pure** the left
bound can be strengthened by replacing `F` with `F²`: since `0 ≤ F ≤ 1` we have
`F² ≤ F`, hence `1 − F ≤ 1 − F²`, so the pure-vs-mixed inequality
`1 − F(|ψ⟩, σ)² ≤ D(|ψ⟩, σ)` is a genuinely sharper lower bound than the general
`1 − F(|ψ⟩, σ) ≤ D(|ψ⟩, σ)`.

## The statement

`PureState.one_sub_fidelity_sq_le_traceDistance` is stated for `PureState` and `State`, the
fidelity `State.fidelity` (`AxQM/Postulates/API/Fidelity.lean`) and the trace distance
`State.traceDistance` (`AxQM/Postulates/API/TraceDistance.lean`).

The proof combines two lemmas from
`AxQM/Postulates/API/FidelityPure.lean`:

* `State.fidelity_toState_sq` rewrites `F(|ψ⟩, σ)² = ⟨ψ| σ |ψ⟩` (N&C `(9.60)`);
* `State.one_sub_re_inner_le_traceDistance` supplies `1 − ⟨ψ| σ |ψ⟩ ≤ D(|ψ⟩, σ)`,
  obtained from the two-outcome measurement `{|ψ⟩⟨ψ|, 1 − |ψ⟩⟨ψ|}` via the
  measurement-monotonicity direction of Theorem 9.1.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum
Information* (10th anniv. ed.). Cambridge University Press. Exercise 9.21, §9.2.3.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.21.** For a pure state `|ψ⟩` and any state `σ`,
`1 − F(|ψ⟩, σ)² ≤ D(|ψ⟩, σ)` — a strengthening (for the pure-vs-mixed case) of the
general lower bound `1 − F(ρ, σ) ≤ D(ρ, σ)` of `(9.110)`.

The proof rewrites the squared fidelity of a pure state to `⟨ψ| σ |ψ⟩`
(`State.fidelity_toState_sq`, N&C `(9.60)`) and applies the trace-distance bound
`1 − ⟨ψ| σ |ψ⟩ ≤ D(|ψ⟩, σ)` (`State.one_sub_re_inner_le_traceDistance`), itself the
two-outcome-measurement instance of Theorem 9.1. -/
theorem PureState.one_sub_fidelity_sq_le_traceDistance (ψ : PureState S) (σ : State S) :
    1 - (ψ.toState.fidelity σ) ^ 2 ≤ ψ.toState.traceDistance σ := by
  rw [State.fidelity_toState_sq]
  exact State.one_sub_re_inner_le_traceDistance ψ σ

end AxQM
