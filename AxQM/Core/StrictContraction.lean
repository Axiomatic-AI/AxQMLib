/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TraceDistance
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Strictly contractive state-maps and uniqueness of fixed points (Nielsen & Chuang §9.2.1)

Nielsen & Chuang, in the fixed-point exercises of §9.2.1 (Exercises 9.9–9.13, p. 408–409),
distinguish two notions for a trace-preserving quantum operation `E`:

* **contractive** — `D(E(ρ), E(σ)) ≤ D(ρ, σ)` for all `ρ`, `σ` (Theorem 9.2, always true);
* **strictly contractive** — `D(E(ρ), E(σ)) < D(ρ, σ)` for all `ρ ≠ σ` (Exercise 9.10).

This file introduces the predicate `AxQM.StrictlyContractive` capturing the
second notion for an arbitrary state-map, together with its elementary but reusable consequence:
a strictly contractive map has **at most one** fixed point. These are the shared ingredients behind
Exercises 9.10 (unique fixed point), 9.11 (a mixing operation is strictly contractive), and 9.13
(the bit-flip channel is contractive but *not* strictly).

## Scope of this file: uniqueness

The content packaged here is the **uniqueness** half of the fixed-point story — "at most one fixed
point", elementary and needing *only* strict contraction — together with the "uniqueness given
existence" assembly `strictlyContractive_existsUnique_fixedPoint_of_exists`, which turns an assumed
fixed point into the unique `∃!`. It proves nothing about *existence* itself; that is the separate
matter of Exercise 9.9 (`IsChannel.exists_fixedPoint`). The two combine into the full Exercise 9.10
(`IsChannel.existsUnique_fixedPoint_of_strictlyContractive`) in `AxQM/NC/Ch9/Exercise9_10.lean`.

## The predicate and the `ρ ≠ σ` guard

N&C write the strict-contraction condition as "for any `ρ` and `σ`, `D(E(ρ), E(σ)) < D(ρ, σ)`".
Read literally over *all* pairs this is unsatisfiable: at `ρ = σ` both distances are `0`, and
`0 < 0` is false, so a literal `∀ ρ σ` would make the hypothesis `False` and every theorem
using it *vacuously* true — a dishonest reading. The intended and standard meaning (the metric-space
notion of a *contractive* map, in Edelstein's sense) restricts to *distinct* states:
`∀ ρ σ, ρ ≠ σ → D(E(ρ), E(σ)) < D(ρ, σ)`. That is exactly `StrictlyContractive`; the guard is a
faithful transcription, not an added hypothesis.

Note strict contraction is genuinely weaker than a Banach/Lipschitz contraction
(`ContractingWith K` with a uniform `K < 1`): it provides no uniform contraction constant, which is
why Mathlib's contraction-mapping API does not apply directly.

## Fixed points

Fixed points are spelled with the Mathlib fixed-point API (`Function.IsFixedPt`,
`Function.fixedPoints`) so these lemmas compose with the library.

## Main declarations

* `AxQM.StrictlyContractive` — the predicate `∀ ρ σ, ρ ≠ σ → D(f ρ, f σ) < D(ρ, σ)`.
* `AxQM.StrictlyContractive.eq_of_isFixedPoint` — two fixed points of a strictly
  contractive map coincide (the uniqueness kernel: at most one fixed point).
* `AxQM.StrictlyContractive.subsingleton_fixedPoints` — the packaging of the kernel:
  the fixed-point set `Function.fixedPoints f` is a subsingleton.
* `AxQM.strictlyContractive_existsUnique_fixedPoint_of_exists` — the reusable "uniqueness
  given existence" assembly: a strictly contractive map with a fixed point has a *unique* one
  (`∃!`). Existence is a hypothesis, discharged elsewhere (Exercise 9.9 for a channel).

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th anniv.
ed.). Cambridge University Press. §9.2.1, Exercises 9.9–9.13 (p. 408–409).
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- A state-map `f : State S → State S` is **strictly contractive** for the trace distance when it
strictly decreases the distance between any two *distinct* states:
`D(f ρ, f σ) < D(ρ, σ)` whenever `ρ ≠ σ`  (Nielsen & Chuang, Exercise 9.10, p. 408).

This is the metric notion of a *contractive* map (Edelstein): unlike `ContractingWith K`, it assumes
no uniform contraction constant `K < 1`. The `ρ ≠ σ` guard is the honest reading of N&C's informal
"for any `ρ` and `σ`" — at `ρ = σ` the strict inequality is impossible, so an unguarded quantifier
would be a `False` hypothesis. -/
def StrictlyContractive (f : State S → State S) : Prop :=
  ∀ ρ σ : State S, ρ ≠ σ → (f ρ).traceDistance (f σ) < ρ.traceDistance σ

/-- **A strictly contractive map has at most one fixed point** (the uniqueness kernel of Nielsen &
Chuang, Exercise 9.10). If `f` is strictly contractive and both `ρ` and `σ` are fixed points, then
`ρ = σ`.

Proof: were `ρ ≠ σ`, strict contraction would give `D(f ρ, f σ) < D(ρ, σ)`; but `f ρ = ρ` and
`f σ = σ` turn the left side into `D(ρ, σ)`, yielding `D(ρ, σ) < D(ρ, σ)`, a contradiction. -/
theorem StrictlyContractive.eq_of_isFixedPoint {f : State S → State S}
    (hf : StrictlyContractive f) {ρ σ : State S}
    (hρ : Function.IsFixedPt f ρ) (hσ : Function.IsFixedPt f σ) : ρ = σ := by
  by_contra hne
  have h := hf ρ σ hne
  rw [hρ, hσ] at h
  exact lt_irrefl _ h

/-- The **fixed-point set of a strictly contractive map is a subsingleton** — the set-level
packaging of `StrictlyContractive.eq_of_isFixedPoint`. Any two members of `Function.fixedPoints f`
are equal, so the fixed point (when it exists) is unique. -/
theorem StrictlyContractive.subsingleton_fixedPoints {f : State S → State S}
    (hf : StrictlyContractive f) : (Function.fixedPoints f).Subsingleton :=
  fun _ hρ _ hσ => hf.eq_of_isFixedPoint hρ hσ

/-- **Uniqueness given existence** (Nielsen & Chuang, Exercise 9.10). A strictly contractive
state-map `f` that possesses a fixed point possesses a *unique* one: `∃! ρ, f ρ = ρ`.

This is the reusable "uniqueness given existence" assembly: it isolates the part strict contraction
contributes (uniqueness, through `eq_of_isFixedPoint`) from *existence*, which is supplied as the
hypothesis `hex`. It holds for *any* strictly contractive map with a fixed point; for a
trace-preserving quantum operation `hex` is discharged by Exercise 9.9's existence theorem, giving
the full Exercise 9.10 (`IsChannel.existsUnique_fixedPoint_of_strictlyContractive`, in
`AxQM/NC/Ch9/Exercise9_10.lean`). The `_of_exists` suffix marks that existence is assumed, not
proved. -/ theorem strictlyContractive_existsUnique_fixedPoint_of_exists {f : State S → State S}
    (hf : StrictlyContractive f) (hex : ∃ ρ : State S, Function.IsFixedPt f ρ) :
    ∃! ρ : State S, Function.IsFixedPt f ρ := by
  obtain ⟨ρ, hρ⟩ := hex
  exact ⟨ρ, hρ, fun σ hσ => hf.eq_of_isFixedPoint hσ hρ⟩

end AxQM
