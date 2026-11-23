/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.GeneralizedDepolarizingChannel
import AxQM.Postulates.API.TracePow
import ToMathlib.Analysis.InnerProductSpace.DensityTracePow

/-!
# Nielsen & Chuang, Exercise 8.18 (Trace powers are non-increasing under depolarization)

*(N&C p. 379.)*

For k≥1 show tr(ρ^k) is never increased by the depolarizing channel.

## The formalisation

The (`d`-dimensional) **depolarizing channel** (N&C eq. 8.106) replaces the state with the
completely mixed state `I/d` with probability `p` and leaves it untouched otherwise:
`E(ρ) = p (I/d) + (1 - p) ρ`.
The exercise asks to show that, for every integer `k ≥ 1`, the `k`-th trace power `tr(ρᵏ)` — the
quantity whose `k = 2` case, the *purity* `tr(ρ²)`, measures mixedness — is **never increased**:
`tr(E(ρ)ᵏ) ≤ tr(ρᵏ)`.

* `AxQM.traceOfPow_genDepolarizingChannel_le` (this file) — the physics theorem, over
  states: for the `d`-level system `qudit d` (`d ≥ 1`), any `0 ≤ p ≤ 1`, any state `ρ`, and any
  `k ≥ 1`, `(genDepolarizingChannel d p … ρ).traceOfPow k ≤ ρ.traceOfPow k`.

## Supporting results

* `ToMathlib/Analysis/InnerProductSpace/DensityTracePow.lean` — the mathematical heart, stated for
  a density operator on a general finite-dimensional space (using `finrank`, `trace`,
  `IsDensityOp`): `ContinuousLinearMap.IsDensityOp.re_trace_depolarize_pow_le`,
  `re tr((p • (d⁻¹ • 1) + (1 - p) • ρ)ᵏ) ≤ re tr(ρᵏ)`, reduced (via the eigenbasis) to the real
  inequality `sum_mix_uniform_pow_le` — per-term convexity of `x ↦ xᵏ` plus the power-mean bound.
* `AxQM/Postulates/API/TracePow.lean` — the trace-power quantity
  `State.traceOfPow ρ k = re tr(ρ.op ^ k)` and its purity bridge `State.purity_eq_traceOfPow_two`
  (`tr(ρ²)` is the `k = 2` case).
* `AxQM/Postulates/API/GeneralizedDepolarizingChannel.lean` (Exercise 8.19) — the
  depolarizing channel `genDepolarizingChannel` as a `State → State` map on `qudit d`, a genuine
  density operator by `IsDensityOp.convex_combination`. The same channel serves both the
  operator-sum representation of 8.19 and the trace-power monotonicity of 8.18.

## Notes on the statement

* **Faithful to N&C.** General dimension `d` (not qubit-only), *all* `k ≥ 1`, and
  the full physical probability range `0 ≤ p ≤ 1`. The claim is stated as `≤` (non-increase), not
  strict `<`: at `k = 1` it is an *equality* (`tr` is preserved — the channel is trace-preserving),
  and at `p = 0` the channel is the identity, so `<` would be false. Modelling the channel as a
  genuine `State` (a convex combination) makes trace-preservation manifest.
* **The one depolarizing channel.** `genDepolarizingChannel` (Exercise 8.19) already builds
  the `d`-dimensional depolarizing channel as a density-operator `State` on `qudit d`. Its operator
  is written `(1 - p) ρ + p (I/d)`, so the proof commutes the summands (`add_comm`) to match the
  inequality's `p (I/d) + (1 - p) ρ` before applying it.
* **`qudit d` for the `d`-dimensional system.** N&C's "`d`-dimensional quantum system" is exactly
  `qudit d`; the statement uses `qudit d` with `[NeZero d]` (`d ≥ 1`, so `I/d` exists), as in
  Exercise 8.19. The `Nontrivial (qudit d).space` hypothesis of the underlying constructions is
  discharged by instance synthesis from `[NeZero d]`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 8.18.** For `k ≥ 1` the depolarizing channel never increases the
`k`-th trace power `tr(ρᵏ)`: for the `d`-level system `qudit d` (`d ≥ 1`), any probability
`0 ≤ p ≤ 1`, any state `ρ`, and any `k ≥ 1`,
`tr(E(ρ)ᵏ) ≤ tr(ρᵏ)` where `E(ρ) = p (I/d) + (1 - p) ρ` is the depolarizing channel
(`genDepolarizingChannel`, Exercise 8.19).

Since `E(ρ)` is a *function of* `ρ` sharing its eigenbasis, both trace powers are sums over `ρ`'s
own eigenvalues, and the operator inequality reduces to the real convexity/power-mean bound; this is
the lemma `ContinuousLinearMap.IsDensityOp.re_trace_depolarize_pow_le`, applied
here to `ρ.isDensity` after unfolding `traceOfPow`, rewriting the channel operator to `p (I/d) +
(1 - p) ρ` (`genDepolarizingChannel_op`, `maximallyMixedState_op`, `add_comm`). -/
theorem traceOfPow_genDepolarizingChannel_le {d : ℕ} [NeZero d] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : State (qudit d)) {k : ℕ} (hk : 1 ≤ k) :
    (genDepolarizingChannel d p hp0 hp1 ρ).traceOfPow k ≤ ρ.traceOfPow k := by
  simp only [State.traceOfPow, genDepolarizingChannel_op, maximallyMixedState_op]
  rw [add_comm]
  exact ρ.isDensity.re_trace_depolarize_pow_le hp0 hp1 hk

end AxQM
