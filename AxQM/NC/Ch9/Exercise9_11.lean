/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_2
import AxQM.NC.Ch9.Exercise9_9
import AxQM.NC.Ch9.Exercise9_10
import AxQM.Postulates.API.Mixture

/-!
# Nielsen & Chuang, Exercise 9.11 (mixing a fixed state: strictly contractive, unique fixed point)

Show a quantum op mixing in fixed state rho_0 is strictly contractive, hence unique fixed point.

## The statements

The exercise has two clauses — "`E` is strictly contractive" **and** "thus has a unique fixed
point" — and this file formalizes both. The decomposition `(9.52)` cancels the fixed component:
`E(ρ) − E(σ) = (1 − p)(E′(ρ) − E′(σ))`, so the mixing dilutes the trace distance by exactly the
factor `1 − p < 1`. The statements are

* `AxQM.traceDistance_replaceMix_le` — the **uniform contraction bound**
  `D(E ρ, E σ) ≤ (1 − p) D(ρ, σ)`. This is stronger than the bare strict inequality N&C ask for:
  `E` is a genuine Lipschitz contraction with constant `1 − p < 1`, not merely a distance-decreasing
  (Edelstein) map.
* `AxQM.traceDistance_replaceMix_lt` — **strict contractivity** at the level of a raw
  inequality, `ρ ≠ σ → D(E ρ, E σ) < D(ρ, σ)`.
* `AxQM.replaceMix_strictlyContractive` — the same fact **packaged as the predicate**
  `AxQM.StrictlyContractive E` (Exercise 9.10's `Core/StrictContraction.lean`), the
  property the exercise asks one to prove "using joint convexity".
* `AxQM.replaceMix_existsUnique_fixedPoint` — the exercise's second clause, **the unique
  fixed point** `∃! ρ, E ρ = ρ`.

## Strict contractivity, and the role of joint convexity

The mixing is expressed with `State.mixPair`
(`AxQM/Postulates/API/Mixture.lean`): the hypothesis is `∀ τ, E τ = State.mixPair p ρ₀ (E′ τ)`.
The uniform bound is a two-line composition of
already-formalized Chapter 9 facts:

* **joint convexity** of the trace distance for the binary mixture
  (`State.traceDistance_mixPair_jointly_convex`, the two-outcome case of N&C `(9.50)`) gives
  `D(E ρ, E σ) = D(p ρ₀ + (1−p) E′ρ, p ρ₀ + (1−p) E′σ) ≤ p D(ρ₀, ρ₀) + (1−p) D(E′ρ, E′σ)`, and the
  shared `ρ₀` term vanishes (`traceDistance_self`), leaving `(1−p) D(E′ρ, E′σ)`;
* **contractivity** of the trace-preserving `E′` (Theorem 9.2, `traceDistance_channel_le`) gives
  `D(E′ρ, E′σ) ≤ D(ρ, σ)`.

Strictness then follows because `1 − p < 1` (from `p > 0`) and `D(ρ, σ) > 0` when `ρ ≠ σ`
(`traceDistance_eq_zero_iff`). Only `E′` need be a channel *for strict contractivity*; `E`'s own
trace-preservation is not used there and is omitted from those two lemmas rather than carried as an
unused hypothesis.

## The unique fixed point, and why `IsChannel E` is assumed here

"…and thus has a unique fixed point" is the composition of two orthogonal facts N&C themselves split
across Exercises 9.9–9.10:

* **uniqueness** — a strictly contractive map has at most one fixed point (Exercise 9.10,
  `StrictlyContractive.eq_of_isFixedPoint`, wrapped as
  `strictlyContractive_existsUnique_fixedPoint_of_exists`); and
* **existence** — every trace-preserving quantum operation has a fixed point (Exercise 9.9,
  `IsChannel.exists_fixedPoint`, via the Markov–Kakutani/Schauder argument).

`replaceMix_existsUnique_fixedPoint` assembles them: `replaceMix_strictlyContractive` supplies
`StrictlyContractive E`, `IsChannel.exists_fixedPoint` supplies a fixed point of `E`, and
`strictlyContractive_existsUnique_fixedPoint_of_exists` combines the two into `∃! ρ, E ρ = ρ`.

**Design decision — `IsChannel E` is taken as a hypothesis.** Existence via Exercise 9.9 needs
`E` to be a genuine channel, so `IsChannel E` is *load-bearing* here (unlike in the
strict-contractivity lemmas, where it is genuinely unused). It is **not** an added hypothesis:
N&C open the exercise with "Suppose `E` is a trace-preserving quantum operation for which…", so
`IsChannel E` is exactly one of the exercise's own hypotheses — a faithful transcription, not a
weakening. One *could* instead derive `IsChannel E` from `IsChannel E′` and the mixing (the map
is the convex combination of the trace-and-replace channel `ρ ↦ ρ₀` with `E′`), obtaining a
marginally more general statement that drops the redundant hypothesis; but that requires a
separate reset-channel + convex-combination-of-channels development (a Kraus construction for
`ρ ↦ (tr ·) ρ₀` plus closure of complete positivity and trace preservation under nonnegative
combinations) that the exercise does not call for. The statement here matches N&C's hypotheses
exactly.

The instance `[Nonempty (State S)]` is the same well-formedness condition Exercise 9.9 carries:
it records that `S` is a genuine (nonzero-dimensional) quantum system, so that "there is a fixed
**state**" is non-vacuous. On a zero-dimensional space no density operator exists and the claim
would be false; N&C presuppose a real system.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th anniv.
ed.). Cambridge University Press. Exercise 9.11, §9.2.1 (p. 408).

N&C Exercise 9.11, p. 408.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A quantum operation mixing in a fixed state is a (uniform) contraction.** If `E′` is a channel
and `E` mixes its input's `E′`-image with a fixed state `ρ₀`, `E τ = p ρ₀ + (1 − p) E′(τ)` with
`0 ≤ p ≤ 1` (Nielsen & Chuang `(9.52)`), then `E` contracts the trace distance by the factor
`1 − p`: `D(E ρ, E σ) ≤ (1 − p) D(ρ, σ)`.

Proof: the fixed component cancels under joint convexity of the trace distance for binary mixtures
(`State.traceDistance_mixPair_jointly_convex`), `D(E ρ, E σ) ≤ p D(ρ₀, ρ₀) + (1 − p) D(E′ ρ, E′ σ)`,
where `D(ρ₀, ρ₀) = 0`; and `E′`, being trace-preserving, is contractive (Theorem 9.2,
`traceDistance_channel_le`), `D(E′ ρ, E′ σ) ≤ D(ρ, σ)`. -/
theorem traceDistance_replaceMix_le {E E' : State S → State S} {ρ₀ : State S} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE' : IsChannel E')
    (hE : ∀ τ, E τ = State.mixPair hp0 hp1 ρ₀ (E' τ)) (ρ σ : State S) :
    (E ρ).traceDistance (E σ) ≤ (1 - p) * ρ.traceDistance σ := by
  rw [hE ρ, hE σ]
  refine (State.traceDistance_mixPair_jointly_convex hp0 hp1 ρ₀ (E' ρ) ρ₀ (E' σ)).trans ?_
  rw [State.traceDistance_self, mul_zero, zero_add]
  exact mul_le_mul_of_nonneg_left (traceDistance_channel_le hE' ρ σ) (by linarith)

/-- **A channel mixing in a fixed state strictly decreases the trace distance.** If `E′` is a
channel and `E τ = p ρ₀ + (1 − p) E′(τ)` with `0 < p ≤ 1` (N&C `(9.52)`), then for distinct
states `ρ ≠ σ` the trace distance strictly decreases: `D(E ρ, E σ) < D(ρ, σ)`.

Proof: the uniform bound `D(E ρ, E σ) ≤ (1 − p) D(ρ, σ)` (`traceDistance_replaceMix_le`) together
with `1 − p < 1` (from `p > 0`) and `D(ρ, σ) > 0` for `ρ ≠ σ` (`State.traceDistance_eq_zero_iff`
with `traceDistance_nonneg`). -/
theorem traceDistance_replaceMix_lt {E E' : State S → State S} {ρ₀ : State S} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hE' : IsChannel E')
    (hE : ∀ τ, E τ = State.mixPair hp0.le hp1 ρ₀ (E' τ)) {ρ σ : State S} (hne : ρ ≠ σ) :
    (E ρ).traceDistance (E σ) < ρ.traceDistance σ := by
  have hle := traceDistance_replaceMix_le hp0.le hp1 hE' hE ρ σ
  have hpos : 0 < ρ.traceDistance σ :=
    (State.traceDistance_nonneg ρ σ).lt_of_ne
      (fun h => hne ((State.traceDistance_eq_zero_iff ρ σ).mp h.symm))
  nlinarith [hle, mul_pos hp0 hpos]

/-- **Nielsen & Chuang, Exercise 9.11 — a channel mixing in a fixed state is strictly contractive.**
If `E′` is a channel and `E τ = p ρ₀ + (1 − p) E′(τ)` with `0 < p ≤ 1` (N&C `(9.52)`), then `E`
satisfies `AxQM.StrictlyContractive` — it strictly decreases the trace distance between any
two *distinct* states. This is the packaged form of `traceDistance_replaceMix_lt` and the property
the exercise asks one to prove "using joint convexity". -/
theorem replaceMix_strictlyContractive {E E' : State S → State S} {ρ₀ : State S} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hE' : IsChannel E')
    (hE : ∀ τ, E τ = State.mixPair hp0.le hp1 ρ₀ (E' τ)) :
    StrictlyContractive E :=
  fun _ _ hne => traceDistance_replaceMix_lt hp0 hp1 hE' hE hne

/-- **N&C Exercise 9.11 — a channel mixing in a fixed state has a unique fixed point.**
If `E` is a channel with `E τ = p ρ₀ + (1 − p) E′(τ)` for a channel `E′` and `0 < p ≤ 1`
(N&C `(9.52)`), then `E` has a *unique* fixed point: `∃! ρ, E ρ = ρ`. This is the exercise's second
clause, "…and thus has a unique fixed point".

Proof: `E` is strictly contractive (`replaceMix_strictlyContractive`), and being a channel it has a
fixed point (`IsChannel.exists_fixedPoint`, Exercise 9.9); strict contraction upgrades existence to
existence-and-uniqueness (`strictlyContractive_existsUnique_fixedPoint_of_exists`, Exercise 9.10).
The channel hypothesis `hE` on `E` is exactly N&C's opening "Suppose `E` is a trace-preserving
quantum operation…" and enters only through the existence step; `[Nonempty (State S)]` records that
`S` is a genuine quantum system, so "a fixed **state** exists" is non-vacuous. -/
theorem replaceMix_existsUnique_fixedPoint [Nonempty (State S)] {E E' : State S → State S}
    {ρ₀ : State S} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hE : IsChannel E) (hE' : IsChannel E')
    (hmix : ∀ τ, E τ = State.mixPair hp0.le hp1 ρ₀ (E' τ)) :
    ∃! ρ : State S, E ρ = ρ :=
  strictlyContractive_existsUnique_fixedPoint_of_exists
    (replaceMix_strictlyContractive hp0 hp1 hE' hmix) hE.exists_fixedPoint

end AxQM
