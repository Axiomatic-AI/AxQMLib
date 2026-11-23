/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchumacherDirect
import AxQM.Postulates.API.SchumacherConverse

/-!
# N&C Theorem 12.6 — Schumacher's noiseless channel coding theorem

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 12.6, p. 544.

Schumacher's quantum noiseless channel coding theorem characterises exactly when an i.i.d. quantum
source `{H, ρ}` can be compressed reliably. For a (qubit) rate `R`, N&C states two directions:

* **direct part** — if `R > S(ρ)` there is a reliable rate-`R` compression scheme (N&C Eqs.
  12.50–12.53); and
* **converse** — if `R < S(ρ)` no rate-`R` scheme is reliable (N&C Eqs. 12.54–12.58).

So, away from the boundary `R = S(ρ)`, the source `ρ` is reliably compressible at rate `R` **iff**
`R > S(ρ)`. Here `S(ρ) = ρ.vonNeumannEntropy` (in nats), the qubit rate `R` compares as `R * log 2`
against `S(ρ)`, and *reliability* of a rate-`R` scheme means its entanglement fidelity for `ρ^⊗n`
tends to `1` as the block length `n → ∞`.

## What this file contains

The two directional halves are established in `AxQM/Postulates/API/SchumacherDirect.lean` and
`AxQM/Postulates/API/SchumacherConverse.lean`. They are stated for the predicate
`ContinuousLinearMap.ReliablyCompressible ρ.op R` of the density operator `ρ.op`
(`ToMathlib/Analysis/InnerProductSpace/QuantumDataCompression.lean`):

* `State.reliablyCompressible_of_vonNeumannEntropy_lt` (direct, `SchumacherDirect.lean`):
  `ρ.vonNeumannEntropy < R * log 2 → ContinuousLinearMap.ReliablyCompressible ρ.op R`;
* `State.not_reliablyCompressible_of_lt_vonNeumannEntropy` (converse, `SchumacherConverse.lean`):
  `0 ≤ R → R * log 2 < ρ.vonNeumannEntropy → ¬ ContinuousLinearMap.ReliablyCompressible ρ.op R`.

This file states the theorem for states:

* `State.ReliablyCompressible` — reliable compressibility of a state `ρ : State S`, defined as the
  predicate above on `ρ.op`.
* `State.reliablyCompressible_iff_vonNeumannEntropy_lt` — **the headline** (Theorem 12.6): for a
  non-negative rate `R` away from the boundary, `ρ.ReliablyCompressible R ↔ ρ.vonNeumannEntropy <
  R * log 2`.

## Faithfulness

* **The two halves, one equivalence.** N&C states Theorem 12.6 as two implications; the single
  biconditional here is their exact conjunction and is the natural statement of the theorem
  ("reliable compression iff `R > S(ρ)`"). The two directions remain available individually as
  the lemmas above.
* **The boundary `R log 2 = S(ρ)` is deliberately excluded (`hne`), not a weakening.** N&C's theorem
  says nothing at `R = S(ρ)` — it asserts reliability only for `R > S(ρ)` and unreliability only for
  `R < S(ρ)` — so whether the source is reliably compressible *at* `R = S(ρ)` is left open by the
  textbook. The hypothesis `R * log 2 ≠ ρ.vonNeumannEntropy` restricts the equivalence to exactly
  the domain N&C characterises; claiming a strict iff at the boundary would overclaim beyond the
  source. (The two halves together give only `reliable → S(ρ) ≤ R log 2`, not the strict `<`, so the
  boundary genuinely cannot be resolved from them.)
* **Non-negative rate (`hR0`).** Inherited from the converse: a qubit rate is `R ≥ 0`, and the
  hypothesis is necessary there — a pure source (`S(ρ) = 0`) is reliably compressible at *every*
  rate, including the negative rates that are the only way `R log 2 < 0 = S(ρ)` can hold — which
  would falsify an unconditional converse.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2 (Theorem 12.6; Eqs. (12.50)–(12.58)).
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Reliable compressibility of a quantum source** (Nielsen & Chuang, §12.2.2). A source
`ρ : State S` is *reliably compressible at (qubit) rate `R`* when its density operator `ρ.op` is:
there is a family of rate-`R` quantum compression schemes whose entanglement fidelity for `ρ^⊗n`
tends to `1` as the block length `n → ∞`.

This is `ContinuousLinearMap.ReliablyCompressible` applied to the density operator `ρ.op`, so the
notion is stated for states. -/
def State.ReliablyCompressible (ρ : State S) (R : ℝ) : Prop :=
  ContinuousLinearMap.ReliablyCompressible ρ.op R

/-- **Schumacher's noiseless channel coding theorem** (Nielsen & Chuang, Theorem 12.6, p. 544). For
a non-negative (qubit) rate `R` away from the boundary `R = S(ρ)`, an i.i.d. quantum source `ρ` is
reliably compressible at rate `R` **iff** the rate exceeds the source entropy, `S(ρ) < R` (in nats,
`ρ.vonNeumannEntropy < R * log 2`).

This assembles N&C's two directions for the predicate `State.ReliablyCompressible`:

* if `S(ρ) < R log 2`, the direct part `State.reliablyCompressible_of_vonNeumannEntropy_lt` builds a
  reliable scheme; and
* if `R log 2 < S(ρ)`, the converse `State.not_reliablyCompressible_of_lt_vonNeumannEntropy` (using
  `0 ≤ R`) forbids one.

The hypothesis `R * log 2 ≠ ρ.vonNeumannEntropy` excludes the boundary `R = S(ρ)`, which N&C leaves
open (see the module docstring); it is the exact domain the textbook characterises, not a
weakening. -/
theorem State.reliablyCompressible_iff_vonNeumannEntropy_lt (ρ : State S) {R : ℝ}
    (hR0 : 0 ≤ R) (hne : R * Real.log 2 ≠ ρ.vonNeumannEntropy) :
    ρ.ReliablyCompressible R ↔ ρ.vonNeumannEntropy < R * Real.log 2 := by
  constructor
  · intro hrc
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hrc (ρ.not_reliablyCompressible_of_lt_vonNeumannEntropy hR0 h)
    · exact h
  · intro h
    exact ρ.reliablyCompressible_of_vonNeumannEntropy_lt h

end AxQM
