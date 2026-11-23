/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumChannel
import ToMathlib.Analysis.InnerProductSpace.DensityFixedPoint

/-!
# Nielsen & Chuang, Exercise 9.9 (Existence of fixed points)

Use Schauder fixed-point theorem to show any trace-preserving quantum op has a fixed point.

Every quantum channel has a **stationary state**: a density operator `ρ` unchanged by the
channel, `E(ρ) = ρ`. This is the fixed-point structure underlying steady states of open-system
dynamics; the *unique*ness refinement for strictly contractive channels is Exercises 9.10–9.11.

## Statement and design

A **trace-preserving quantum operation** is a quantum channel: `AxQM.IsChannel f` says
the state-map `f : State S → State S` is the restriction of a completely-positive,
trace-preserving linear superoperator `Φ` on operators (`Postulates/API/QuantumChannel.lean`).
The result is

* `AxQM.IsChannel.exists_fixedPoint` — every channel `f` of a system that has states
  fixes some state: `∃ ρ, f ρ = ρ`.

The hypothesis `[Nonempty (State S)]` is a *well-formedness* condition, not a weakening: it says
`S` is a genuine (nonzero-dimensional) quantum system, so that states — and hence the assertion
"there is a fixed **state**" — are non-vacuous. On a zero-dimensional space no density operator
exists (trace cannot be `1`), and the claim would be false; N&C's exercise presupposes a real
system. Equivalently one could take a witness state as an explicit argument.

## Proof

The mathematical core lives, re-grounded, in `ToMathlib/`
(`ToMathlib.Analysis.InnerProductSpace.DensityFixedPoint`):

* `isCompact_setOf_isDensityOp` and `convex_setOf_isDensityOp` — the density operators form a
  compact (finite-dimensional Heine–Borel) convex set;
* `ContinuousLinearMap.exists_isFixedPt_of_isCompact_of_convex` — the Markov–Kakutani /
  mean-ergodic argument: a continuous linear self-map of a nonempty compact convex set has a
  fixed point (its Cesàro averages `(1/n) ∑_{k<n} Φᵏ x₀` stay in the set and a subsequential
  limit is fixed, since `Φ(Aₙ) − Aₙ = (Φⁿ x₀ − x₀)/n → 0`);
* `ContinuousLinearMap.exists_isDensityOp_isFixedPt` — assembling these, a superoperator
  preserving the density set has a density-operator fixed point.

Schauder's theorem is stated in N&C's hint for the general (infinite-dimensional) case; here the
state spaces are finite-dimensional, where the density set is compact and Schauder reduces to its
finite-dimensional content. Since a channel is *linear* on operators, the elementary averaging
argument suffices and is used in place of the (Mathlib-unavailable) Brouwer/Schauder theorem —
proving the same existence statement.

Here `Φ` (from unpacking `IsChannel`) preserves the density set precisely because `f` maps
states to states: for a density operator `A`, `Φ A = (f ⟨A, ·⟩).op` is again a density operator.
The abstract fixed point `ρ` from the core lemma is repackaged as a `State`, and `f ρ = ρ`
follows from `(f ρ).op = Φ ρ.op = ρ.op` via state extensionality.

N&C Exercise 9.9, p. 408.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.9 (Existence of fixed points).** Every trace-preserving
quantum operation `f` (a `AxQM.IsChannel`) of a system that has states fixes some state:
there is a density operator `ρ` with `f ρ = ρ`.

The channel's underlying superoperator `Φ` maps the compact convex set of density operators into
itself, so the Markov–Kakutani fixed-point theorem
(`ContinuousLinearMap.exists_isDensityOp_isFixedPt`, the finite-dimensional realisation of the
Schauder theorem N&C invoke) supplies a fixed density operator, which repackages as a fixed
state. The instance `[Nonempty (State S)]` records that `S` is a genuine quantum system (its
state space is nonzero-dimensional); without it, "a fixed state exists" is vacuously false. -/
theorem IsChannel.exists_fixedPoint [Nonempty (State S)] {f : State S → State S}
    (hf : IsChannel f) : ∃ ρ : State S, f ρ = ρ := by
  obtain ⟨Φ, _hCP, _hTP, hfop⟩ := hf
  obtain ⟨ρ₀⟩ := (inferInstance : Nonempty (State S))
  -- `Φ` sends density operators to density operators: any density `A` is the operator of the
  -- state `⟨A, hA⟩`, and `f` maps states to states, so `Φ A = (f ⟨A, hA⟩).op` is a density op.
  have hmaps : ∀ A : S.space →L[ℂ] S.space, A.IsDensityOp → (Φ A).IsDensityOp := by
    intro A hA
    rw [← hfop ⟨A, hA⟩]
    exact (f ⟨A, hA⟩).isDensity
  obtain ⟨ρop, hρop, hfix⟩ :=
    ContinuousLinearMap.exists_isDensityOp_isFixedPt Φ hmaps ρ₀.isDensity
  refine ⟨⟨ρop, hρop⟩, State.ext ?_⟩
  rw [hfop ⟨ρop, hρop⟩]
  exact hfix

end AxQM
