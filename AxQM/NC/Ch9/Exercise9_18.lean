/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Exercise9_17
import AxQM.NC.Ch9.Theorem9_6

/-!
# Nielsen & Chuang, Exercise 9.18 (Contractivity of the angle)

Show angle A(E(rho),E(sigma))<=A(rho,sigma) is contractive under quantum operation.

The **angle** `A(ρ, σ) ≡ arccos F(ρ, σ)` (N&C `(9.82)`, the derived quantity `State.angle`
introduced in Exercise 9.17, `NC/Ch9/Exercise9_17.lean`) is the metric N&C build from the fidelity
in §9.2.2. This exercise says
it is *contractive* under any physical process: a trace-preserving quantum operation can only
bring two states closer together in the angle metric — the fidelity counterpart of the
trace-distance contractivity `D(E(ρ), E(σ)) ≤ D(ρ, σ)` (Theorem 9.2), with the inequality in the
*same* direction because a larger fidelity (smaller angle) means less distinguishable.

## Statement

A **trace-preserving quantum operation** is a quantum *channel* (`AxQM.IsChannel f`), and
the distance is the angle `AxQM.State.angle`. The statement is

* `AxQM.State.angle_channel_le` — `A(E(ρ), E(σ)) ≤ A(ρ, σ)` for every channel `f = E` and
  all states `ρ, σ`.

## Proof

The exercise is the composition of exactly the two facts N&C's own proof rests on, both already
formalized:

* **Monotonicity of the fidelity** (Theorem 9.6, `State.fidelity_le_fidelity_channel`): a channel
  never decreases the fidelity, `F(ρ, σ) ≤ F(E(ρ), E(σ))`. N&C prove Exercise 9.18 immediately after
  Theorem 9.6, and 9.18 *is* the restatement of 9.6 in the angle metric.
* **`arccos` is antitone** (`Real.arccos_le_arccos : x ≤ y → arccos y ≤ arccos x`): a larger
  argument gives a smaller arccosine.

Composing them: `F(ρ, σ) ≤ F(E(ρ), E(σ))` feeds `arccos` monotonicity to give
`arccos F(E(ρ), E(σ)) ≤ arccos F(ρ, σ)`, i.e. `A(E(ρ), E(σ)) ≤ A(ρ, σ)`. No hypothesis that the
fidelity lie in `[0, 1]` is needed: `Real.arccos_le_arccos` is antitone on all of `ℝ`.

## Remarks

* **The angle is that of Exercise 9.17.** `State.angle = arccos ∘ fidelity` is defined in
  Exercise 9.17 (`AxQM/NC/Ch9/Exercise9_17.lean`), which also proves its metric bounds `0 ≤ A ≤ π/2`
  and `A = 0 ↔ ρ = σ`. In N&C's development 9.17 establishes the angle *is* a metric and 9.18 shows
  that metric is contractive; this file proves the contractivity theorem.
* **Faithful generality.** The bound holds for *arbitrary* states `ρ, σ` and *any* trace-preserving
  quantum operation `E` (a `IsChannel`), matching N&C's "Let `E` be a trace-preserving quantum
  operation." Trace preservation is exactly what `IsChannel` packages; it is the hypothesis N&C
  state, not an added one.

N&C Exercise 9.18, p. 414.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.18 (contractivity of the angle)**, `(9.91)`: a trace-preserving
quantum operation `f = E` never increases the angle between states,
`A(E(ρ), E(σ)) ≤ A(ρ, σ)`.

Proof: the fidelity is monotone under a channel, `F(ρ, σ) ≤ F(E(ρ), E(σ))` (Theorem 9.6,
`State.fidelity_le_fidelity_channel`), and `Real.arccos` is antitone (`Real.arccos_le_arccos`), so
`A(E(ρ), E(σ)) = arccos F(E(ρ), E(σ)) ≤ arccos F(ρ, σ) = A(ρ, σ)`. This is the angle-metric
restatement of the fidelity monotonicity, exactly as N&C present it right after Theorem 9.6. -/
theorem State.angle_channel_le {f : State S → State S} (hf : IsChannel f) (ρ σ : State S) :
    (f ρ).angle (f σ) ≤ ρ.angle σ :=
  Real.arccos_le_arccos (State.fidelity_le_fidelity_channel hf ρ σ)

end AxQM
