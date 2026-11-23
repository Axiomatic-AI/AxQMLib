/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_6
import AxQM.Postulates.API.RandomUnitaryChannel

/-!
# Nielsen & Chuang, Exercise 9.14 (Invariance of fidelity under unitary transforms)

Prove fidelity invariance under unitary transforms F(UrhoU†,UsigmaU†)=F(rho,sigma).

Applying the *same* unitary to both arguments leaves the fidelity unchanged: a change of basis
cannot alter how (in)distinguishable two states are. This is the fidelity counterpart of the
unitary invariance of the trace distance, and one of the basic properties that make the fidelity a
sensible measure of distance between states.

## Statement

The conjugation `ρ ↦ U ρ U†` is the unitary evolution `AxQM.Evolution.evolve`
(`(U.evolve ρ).op = U ρ U†`, `Evolution.evolve_op`), and the distance is
`AxQM.State.fidelity` (`ρ.fidelity σ = F(ρ, σ)`, N&C `(9.53)`). The statement is

* `AxQM.State.fidelity_evolve` — `F(U ρ U†, U σ U†) = F(ρ, σ)` for every unitary evolution
  `U` and all states `ρ, σ`.

## Proof and design

N&C suggest the direct route: `√(U ρ U†) = U √ρ U†` (conjugation commutes with the square-root
functional calculus) together with invariance of the trace under conjugation. Here we instead
reduce to already-formalized Chapter 9 results, with no new operator lemmas:

* **Monotonicity of the fidelity under channels** (Theorem 9.6,
  `State.fidelity_le_fidelity_channel`): every quantum channel `f` satisfies
  `F(ρ, σ) ≤ F(f ρ, f σ)`.
* A unitary conjugation `U.evolve` is a (random-unitary, hence CPTP) channel —
  `isChannel_of_isRandomUnitary (isRandomUnitary_evolve U)` — and so is the inverse conjugation
  `U†.evolve` by the same fact applied to `U.adjoint`.

Because `U†.evolve` is the two-sided inverse of `U.evolve`
(`Evolution.evolve_adjoint_evolve` : `U†(U ρ U†)U = ρ`), monotonicity run in **both** directions
pins the value exactly:

* `F(ρ, σ) ≤ F(U ρ U†, U σ U†)` — monotonicity for the channel `U.evolve`; and
* `F(U ρ U†, U σ U†) ≤ F(U†(U ρ U†)U, U†(U σ U†)U) = F(ρ, σ)` — monotonicity for the channel
  `U†.evolve` applied to `U ρ U†`, `U σ U†`, then the round-trip cancellation.

`le_antisymm` combines the two inequalities into the equality. This is faithful to the exercise's
statement (identical generality: arbitrary system `S`, arbitrary unitary `U`, arbitrary states)
while reusing the library's channel theory rather than re-developing the conjugation–square-root
identity; there is no circularity, since Theorem 9.6's proof does not depend on this exercise.

The state-level round-trip `Evolution.evolve_adjoint_evolve` (the density-operator companion of the
existing pure-state `Evolution.evolvePure_adjoint_evolvePure`) is the one supporting lemma; it is
reusable Evolution infrastructure and lives with its sibling in `Postulates/API/Evolution.lean`.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th anniv.
ed.). Cambridge University Press. Exercise 9.14, §9.2.2 (p. 410).

N&C Exercise 9.14, p. 410.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.14 — invariance of the fidelity under unitary transforms**
(`(9.61)`): applying the same unitary evolution `U` to both states leaves the fidelity unchanged,
`F(U ρ U†, U σ U†) = F(ρ, σ)` for all states `ρ, σ`.

Proof by antisymmetry from the monotonicity of the fidelity under channels (Theorem 9.6,
`State.fidelity_le_fidelity_channel`), applied to the mutually inverse conjugation channels
`U.evolve` and `U.adjoint.evolve` (each a random-unitary channel via `isRandomUnitary_evolve` and
`isChannel_of_isRandomUnitary`). One direction is monotonicity for `U.evolve`; the other is
monotonicity for `U.adjoint.evolve` followed by the round-trip cancellation
`Evolution.evolve_adjoint_evolve` (`U†(U ρ U†)U = ρ`). -/
theorem State.fidelity_evolve (U : Evolution S) (ρ σ : State S) :
    (U.evolve ρ).fidelity (U.evolve σ) = ρ.fidelity σ := by
  refine le_antisymm ?_ ?_
  · -- `F(U ρ U†, U σ U†) ≤ F(ρ, σ)`: monotonicity for the inverse channel `U†.evolve`, then cancel.
    have h := State.fidelity_le_fidelity_channel
      (isChannel_of_isRandomUnitary (isRandomUnitary_evolve U.adjoint)) (U.evolve ρ) (U.evolve σ)
    rwa [U.evolve_adjoint_evolve ρ, U.evolve_adjoint_evolve σ] at h
  · -- `F(ρ, σ) ≤ F(U ρ U†, U σ U†)`: monotonicity for the channel `U.evolve`.
    exact State.fidelity_le_fidelity_channel
      (isChannel_of_isRandomUnitary (isRandomUnitary_evolve U)) ρ σ

end AxQM
