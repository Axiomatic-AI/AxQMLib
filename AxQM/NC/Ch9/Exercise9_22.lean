/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Exercise9_14
import AxQM.NC.Ch9.Exercise9_17

/-!
# Nielsen & Chuang, Exercise 9.22 (Chaining property for fidelity measures)

Chaining property for fidelity measures: E(VU,F∘E)<=E(U,E)+E(V,F).

Physically: a computation is a sequence of gates, each realised by a noisy channel that only
approximates the intended unitary. This exercise shows that the *error accumulates additively* —
performing each gate with small error guarantees the whole computation has small error — so it
suffices to make each individual step accurate.

## The construction and its statement shape

The error `E(U, ℰ)` compares the *ideal* action of the gate — the unitary conjugation
`ρ ↦ U ρ U†`, the evolution generator `Evolution.evolve` (`Evolution.evolve_op`) — against the
*actual* action, the approximating operation `ℰ`, at the point that maximises their metric
distance. We package it as

* `AxQM.gateChannelError` — `E(U, ℰ) = ⨆ ρ, d(U ρ U†, ℰ ρ)` (N&C `(9.126)`).

Two deliberate modelling choices, both faithful generalisations of the textbook:

* **The metric `d` is abstract.** N&C quantifies over *any* metric on density matrices with the
  unitary-invariance property, offering the angle `arccos(F(ρ, σ))` only as an example. We match
  this exactly: `d : State S → State S → ℝ` is a parameter, and the two properties the proof
  actually consumes — the triangle inequality and unitary invariance — are hypotheses. Every
  genuine metric with N&C's invariance property satisfies both, so the theorem proves precisely
  the stated claim (and, by using only the two needed axioms, applies more generally). The
  invariance hypothesis is phrased through `Evolution.evolve`, `d(W ρ W†, W σ W†) = d(ρ, σ)`.
* **The approximating operation is a bare state-map `ℰ : State S → State S`.** N&C's "trace-
  preserving quantum operation" (`IsChannel`) is the intended framing, but the chaining inequality
  never uses channel-ness — only that `ℰ ρ` is again a state, which the type already guarantees.
  Keeping `ℰ`, `ℱ` as arbitrary state-maps is therefore the honest, more general form (and covers
  the channel case). The *ideal* side is a genuine unitary `Evolution S`.

The "`max`" is realised as the supremum `⨆` over states. In N&C's finite-dimensional setting the
density matrices form a compact set and the (continuous) metric attains its maximum; abstractly we
carry the well-definedness of that maximum as explicit `BddAbove` hypotheses on the two per-gate
families, plus `[Nonempty (State S)]` (the system has at least one state). These are exactly the
conditions under which N&C's `max` denotes a real number, not a narrowing of the physical claim.

## Main statements

* `AxQM.gateChannelError` — the gate-approximation error `E(U, ℰ) = max_ρ d(U ρ U†, ℰ ρ)`;
* `AxQM.le_gateChannelError` — each distance `d(U ρ U†, ℰ ρ)` is `≤ E(U, ℰ)` (the maximum
  is an upper bound), given boundedness;
* `AxQM.gateChannelError_comp_le` — **the chaining inequality**
  `E(V U, ℱ ∘ ℰ) ≤ E(U, ℰ) + E(V, ℱ)` — the heart of Exercise 9.22;
* `AxQM.State.angle_evolve` — unitary invariance of the angle metric
  `A(U ρ U†, U σ U†) = A(ρ, σ)`, showing N&C's example metric satisfies the invariance hypothesis.

## Proof

Fix `ρ`. Writing the composite gate's action as `V(U ρ U†)V†` (`Evolution.evolve_comp`), the
triangle inequality through the intermediate point `V ℰ(ρ) V†` gives
`d(V U ρ U† V†, ℱ(ℰ ρ)) ≤ d(V U ρ U† V†, V ℰ(ρ) V†) + d(V ℰ(ρ) V†, ℱ(ℰ ρ))`.
Unitary invariance under `V` collapses the first term to `d(U ρ U†, ℰ ρ) ≤ E(U, ℰ)`; the second is
`d(V σ V†, ℱ σ)` at `σ = ℰ ρ`, hence `≤ E(V, ℱ)`. So every `ρ` is bounded by `E(U, ℰ) + E(V, ℱ)`,
and `ciSup_le` promotes the pointwise bound to the supremum on the left.

Note the angle metric is *not* instantiated into the chaining theorem: its triangle inequality (the
remaining metric axiom) is not proved in the library, whereas its invariance (`angle_evolve`)
follows immediately from the unitary invariance of the fidelity (Exercise 9.14,
`State.fidelity_evolve`). The abstract theorem — which N&C states for any such metric — is the
faithful statement.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th anniv.
ed.). Cambridge University Press. Exercise 9.22, §9.3 (p. 418).

N&C Exercise 9.22, p. 418.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The error of a channel `ℰ` approximating a unitary gate `U`, measured by a metric `d`**
(Nielsen & Chuang `(9.126)`): `E(U, ℰ) ≡ max_ρ d(U ρ U†, ℰ ρ)`, the largest metric distance
between the ideal evolved state `U ρ U†` (`Evolution.evolve`) and the actual output `ℰ ρ` over all
input states `ρ`. The maximum is realised as the supremum `⨆` over states. -/
noncomputable def gateChannelError (d : State S → State S → ℝ) (U : Evolution S)
    (E : State S → State S) : ℝ :=
  ⨆ ρ, d (U.evolve ρ) (E ρ)

/-- Unfolding lemma: `E(U, ℰ) = ⨆ ρ, d(U ρ U†, ℰ ρ)`. -/
theorem gateChannelError_def (d : State S → State S → ℝ) (U : Evolution S)
    (E : State S → State S) :
    gateChannelError d U E = ⨆ ρ, d (U.evolve ρ) (E ρ) := rfl

/-- **Each individual distance is bounded by the gate error**: `d(U ρ U†, ℰ ρ) ≤ E(U, ℰ)`, provided
the family `ρ ↦ d(U ρ U†, ℰ ρ)` is bounded above (so its supremum is a genuine maximum). This is the
defining "`E` is the maximum" property used in the chaining proof. -/
theorem le_gateChannelError (d : State S → State S → ℝ) {U : Evolution S}
    {E : State S → State S}
    (hbdd : BddAbove (Set.range fun ρ => d (U.evolve ρ) (E ρ))) (ρ : State S) :
    d (U.evolve ρ) (E ρ) ≤ gateChannelError d U E :=
  le_ciSup hbdd ρ

/-- **Nielsen & Chuang, Exercise 9.22 — chaining property for fidelity measures.** For any metric
`d` on states satisfying the triangle inequality (`htriangle`) and unitary invariance
(`hunitary`, `d(W ρ W†, W σ W†) = d(ρ, σ)`), unitary gates `U, V`, and approximating operations
`ℰ, ℱ`, the error of the composite gate is at most the sum of the per-gate errors:
`E(V U, ℱ ∘ ℰ) ≤ E(U, ℰ) + E(V, ℱ)`.

The proof fixes an input `ρ`, splits `d(V U ρ U† V†, ℱ(ℰ ρ))` through the intermediate point
`V ℰ(ρ) V†` by the triangle inequality, uses unitary invariance under `V` to reduce the first term
to `d(U ρ U†, ℰ ρ) ≤ E(U, ℰ)`, bounds the second by `E(V, ℱ)` at the state `ℰ ρ`, and finally
promotes the pointwise bound to the supremum on the left with `ciSup_le`. The boundedness
hypotheses `hE`, `hF` and `[Nonempty (State S)]` are the well-definedness conditions making the
maxima genuine real numbers. -/
theorem gateChannelError_comp_le [Nonempty (State S)]
    (d : State S → State S → ℝ)
    (htriangle : ∀ ρ σ τ : State S, d ρ τ ≤ d ρ σ + d σ τ)
    (hunitary : ∀ (W : Evolution S) (ρ σ : State S), d (W.evolve ρ) (W.evolve σ) = d ρ σ)
    (U V : Evolution S) (E F : State S → State S)
    (hE : BddAbove (Set.range fun ρ => d (U.evolve ρ) (E ρ)))
    (hF : BddAbove (Set.range fun σ => d (V.evolve σ) (F σ))) :
    gateChannelError d (V.comp U) (F ∘ E)
      ≤ gateChannelError d U E + gateChannelError d V F := by
  rw [gateChannelError_def d (V.comp U) (F ∘ E)]
  refine ciSup_le fun ρ => ?_
  rw [Evolution.evolve_comp, Function.comp_apply]
  calc d (V.evolve (U.evolve ρ)) (F (E ρ))
      ≤ d (V.evolve (U.evolve ρ)) (V.evolve (E ρ))
          + d (V.evolve (E ρ)) (F (E ρ)) := htriangle _ _ _
    _ = d (U.evolve ρ) (E ρ) + d (V.evolve (E ρ)) (F (E ρ)) := by
        rw [hunitary V (U.evolve ρ) (E ρ)]
    _ ≤ gateChannelError d U E + gateChannelError d V F :=
        add_le_add (le_gateChannelError d hE ρ) (le_gateChannelError d hF (E ρ))

/-- **Unitary invariance of the angle metric** `A(U ρ U†, U σ U†) = A(ρ, σ)`: the canonical example
metric N&C names for Exercise 9.22 (the angle `A(ρ, σ) = arccos F(ρ, σ)`) satisfies the invariance
hypothesis of `gateChannelError_comp_le`. It is inherited directly from the unitary invariance of
the fidelity (Exercise 9.14, `State.fidelity_evolve`) through `State.angle_def`. -/
theorem State.angle_evolve (U : Evolution S) (ρ σ : State S) :
    (U.evolve ρ).angle (U.evolve σ) = ρ.angle σ := by
  simp only [State.angle_def, State.fidelity_evolve]

end AxQM
