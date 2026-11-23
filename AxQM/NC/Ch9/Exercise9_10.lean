/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.StrictContraction
import AxQM.NC.Ch9.Exercise9_9

/-!
# Nielsen & Chuang, Exercise 9.10 (Unique fixed point of a strictly contractive operation)

Show a strictly contractive trace-preserving quantum op has a unique fixed point.

This is the second half of a two-part arc. **Exercise 9.9** shows that *any* trace-preserving
quantum operation `E` has a fixed point `ρ` with `E(ρ) = ρ` (**existence**). Exercise 9.10 adds the
hypothesis of *strict contraction* and upgrades existence to
**existence-and-uniqueness** — the full `∃! ρ, E(ρ) = ρ`.

## The two halves and how they combine

A strictly contractive trace-preserving quantum operation is, in particular, both a *channel* and a
*strictly contractive* state-map, and each hypothesis discharges one half of the `∃!`:

* **Existence** — supplied by its being a **channel** (a trace-preserving quantum operation), via
  Exercise 9.9's `AxQM.IsChannel.exists_fixedPoint`. That fixed point is obtained from the
  Markov–Kakutani / mean-ergodic argument on the *linear* superoperator underlying the channel
  (`ContinuousLinearMap.exists_isDensityOp_isFixedPt`, the finite-dimensional realisation of the
  Schauder theorem N&C's Exercise 9.9 invokes) — it uses no strict-contraction structure and no
  metric fixed-point theory at all. So existence is available for *any* channel, in particular this
  one.
* **Uniqueness** — supplied by **strict contraction**, via `StrictlyContractive.eq_of_isFixedPoint`
  (`AxQM.Core.StrictContraction`). Elementary: two distinct fixed points `ρ ≠ σ` would give
  `D(ρ, σ) = D(E(ρ), E(σ)) < D(ρ, σ)`, a contradiction. It uses only strict contraction, not the
  channel structure.

Both hypotheses are therefore load-bearing — the channel property for existence, strict contraction
for uniqueness — and neither is a weakening: this is exactly Exercise 9.10's "strictly contractive
trace-preserving quantum operation", concluding the "unique fixed point" it asks for.

The two halves meet in the kernel
`strictlyContractive_existsUnique_fixedPoint_of_exists` (in `Core/StrictContraction.lean`, alongside
`StrictlyContractive` and its uniqueness lemmas), which turns an *assumed* fixed point into the
unique `∃!`. The headline below discharges the kernel's existence hypothesis with
`IsChannel.exists_fixedPoint` (Exercise 9.9), yielding the unconditional Exercise 9.10.

## Main statements

* `AxQM.IsChannel.existsUnique_fixedPoint_of_strictlyContractive` — the **full Exercise
  9.10** (this file): a strictly contractive trace-preserving quantum operation (`IsChannel` and
  `StrictlyContractive`) of a genuine quantum system has a *unique* fixed point, `∃! ρ, E(ρ) = ρ`.

The supporting lemmas are in `AxQM/Core/StrictContraction.lean`:
`strictlyContractive_existsUnique_fixedPoint_of_exists` (uniqueness given existence — the kernel
this headline specialises to channels) and `StrictlyContractive.eq_of_isFixedPoint` /
`StrictlyContractive.subsingleton_fixedPoints` (a strictly contractive map has at most one fixed
point).

The `[Nonempty (State S)]` instance is a **well-formedness** condition inherited from Exercise 9.9,
not a weakening: it says `S` is a genuine (nonzero-dimensional) quantum system, so that states — and
hence "there is a unique fixed **state**" — are non-vacuous. On a zero-dimensional space no density
operator exists and the existence claim would be false; N&C presupposes a real system.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th anniv.
ed.). Cambridge University Press. §9.2.1, Exercise 9.10 (p. 408).

N&C Exercise 9.10, p. 408.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.10 (unique fixed point of a strictly contractive operation).** A
*strictly contractive trace-preserving quantum operation* `f` — one that is both a channel
(`IsChannel`) and strictly contractive (`StrictlyContractive`) — of a genuine quantum system has a
**unique** fixed point: `∃! ρ, f ρ = ρ`.

The two hypotheses discharge the two halves of the `∃!`, assembled through the
kernel `strictlyContractive_existsUnique_fixedPoint_of_exists`. *Existence* is Exercise 9.9's
`IsChannel.exists_fixedPoint`: the channel's underlying linear superoperator preserves the compact
convex set of density operators, so the Markov–Kakutani fixed-point theorem gives a fixed density
operator — this needs only the channel structure, not strict contraction. *Uniqueness* is the
kernel's use of `StrictlyContractive.eq_of_isFixedPoint`: any second fixed point coincides with the
first, since strict contraction forbids two distinct states at equal distance from their images.
The instance `[Nonempty (State S)]` records that `S` is a genuine quantum system (its state space
is nonzero-dimensional); without it, "a fixed state exists" is vacuously false. -/
theorem IsChannel.existsUnique_fixedPoint_of_strictlyContractive [Nonempty (State S)]
    {f : State S → State S} (hchan : IsChannel f) (hf : StrictlyContractive f) :
    ∃! ρ : State S, f ρ = ρ :=
  strictlyContractive_existsUnique_fixedPoint_of_exists hf hchan.exists_fixedPoint

end AxQM
