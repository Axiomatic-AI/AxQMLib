/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ChannelHolevoChi

/-!
# A near-optimal input ensemble for the channel Holevo χ (N&C Theorem 12.8, achievability)

The random-coding (achievability) half of the Holevo–Schumacher–Westmoreland theorem (Nielsen &
Chuang, Theorem 12.8, Box 12.5) begins by fixing an input ensemble `{pₐ, ρₐ}` whose output-ensemble
Holevo χ, `χ({pₐ, E(ρₐ)})`, is *close to* the channel Holevo χ quantity `χ(E)` — indeed strictly
above the target rate `R`.  This is the entry point of the whole argument: Alice's codebook draws
its letters i.i.d. from this ensemble, and the error estimate of eqs. (12.72)–(12.83) then shows
that any rate below `χ({pₐ, E(ρₐ)})` (hence below `χ(E)`) is achievable.

This file records that first step as an existence statement.

## Main result

* `AxQM.exists_holevoChi_comp_gt_of_lt_channelHolevoChi` — for any rate `R < χ(E)`, there
  is a *finite input ensemble* `{pₐ, ρₐ}` (indexed by `Fin m`) whose output-ensemble Holevo χ
  strictly exceeds `R`:  `R < χ({pₐ, E(ρₐ)})`.

  Since `χ(E) = sSup (channelHolevoChiSet E)` is the supremum of the achievable output-ensemble χ
  values (`channelHolevoChi`, N&C eq. (12.71)) and that set is nonempty — it contains the value `0`
  of the trivial one-state ensemble — `R < χ(E)` puts `R` strictly below the supremum, so some
  member of the set (an output-ensemble χ) exceeds `R` (`exists_lt_of_lt_csSup`).  The
  `[Nonempty (State S)]` hypothesis supplies the state the trivial ensemble names, guaranteeing the
  set is nonempty.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, Box 12.5.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A near-optimal input ensemble for `χ(E)`** (Nielsen & Chuang, Theorem 12.8, achievability, the
opening step of Box 12.5).  For any rate `R` strictly below the channel Holevo χ quantity `χ(E)`,
there is a finite input ensemble `{pₐ, ρₐ}` (indexed by `Fin m`) whose *output*-ensemble Holevo χ
strictly exceeds `R`:

`R < χ({pₐ, E(ρₐ)})`.

This is the ensemble the random-coding codebook draws its letters from.  It exists because `χ(E)` is
by definition the supremum of the output-ensemble Holevo χ values `channelHolevoChiSet E` (N&C
eq. (12.71)), a nonempty set (it contains the trivial one-state ensemble's value `0`), so a rate
below that supremum is exceeded by some member of the set (`exists_lt_of_lt_csSup`). -/
theorem exists_holevoChi_comp_gt_of_lt_channelHolevoChi [Nonempty (State S)]
    (E : State S → State S) {R : ℝ} (hR : R < channelHolevoChi E) :
    ∃ (m : ℕ) (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : Fin m → State S),
      R < State.holevoChi p hp hsum (fun i => E (ρ i)) := by
  -- `R` is below the supremum `χ(E) = sSup (channelHolevoChiSet E)` of the nonempty set of
  -- output-ensemble χ values, so some member exceeds it.
  obtain ⟨x, hxmem, hxR⟩ := exists_lt_of_lt_csSup (channelHolevoChiSet_nonempty E) hR
  obtain ⟨m, p, hp, hsum, ρ, rfl⟩ := hxmem
  exact ⟨m, p, hp, hsum, ρ, hxR⟩

end AxQM
