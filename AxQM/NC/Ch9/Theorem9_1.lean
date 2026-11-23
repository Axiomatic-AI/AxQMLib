/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TraceDistance
import AxQM.Postulates.Measurement
import AxQM.Concrete.TraceDistancePOVM

/-!
# Nielsen & Chuang, Theorem 9.1 (trace distance as the maximum over measurements)

D(rho,sigma) = max over POVMs of classical D(p_m,q_m) of measurement outcomes.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 9.1 (p. 405).

The (quantum) trace distance `D(ρ, σ) = ½‖ρ − σ‖₁` equals the **largest** classical
trace distance `D(pₘ, qₘ)` (N&C `(9.1)`) achievable between the outcome
distributions of `ρ` and `σ` under any measurement: no measurement can distinguish
`ρ` from `σ` better than the trace distance allows, and some measurement (a
projective measurement in an eigenbasis of `ρ − σ`) achieves the bound exactly.

## The physical form

The theorem is phrased for states and measurements. It reuses the operator-level
mathematical core proved in `AxQM/Concrete/TraceDistancePOVM.lean` (for operators
and a `POVM`), lifted to states and measurements through two definitional bridges:

* the Born-rule outcome distribution is `Measurement.bornProb`, which is
  *definitionally* `m.toPOVM.toPMF ρ.op` (the induced POVM's Born rule on the
  density operator), so the classical distances match on the nose;
* the trace distance is `State.traceDistance`
  (`AxQM/Postulates/API/TraceDistance.lean`), definitionally `½ ‖ρ.op − σ.op‖₁`.

Every statement below is in terms of `bornProb`, `traceDistance` and `classicalTraceDist`.

## Main statements

* `State.classicalTraceDist_bornProb_le` — **the bound `(9.24)–(9.30)`**: for
  *every* measurement `m`, the classical trace distance of the outcome
  distributions is at most the trace distance, `D(pₘ, qₘ) ≤ D(ρ, σ)`. This is the
  measurement-monotonicity direction, faithful to N&C's "for all POVMs".
* `State.exists_measurement_classicalTraceDist_bornProb_eq` — **achievability**:
  some measurement (the projective measurement in an eigenbasis of `ρ − σ`)
  attains the bound, `D(pₘ, qₘ) = D(ρ, σ)`.
* `State.isGreatest_classicalTraceDist_bornProb` — **the theorem itself**:
  `D(ρ, σ)` is the *greatest* achievable classical trace distance — the two
  directions assembled into N&C's equality-to-a-maximum via `IsGreatest`.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum
Information* (10th anniv. ed.). Cambridge University Press. Theorem 9.1, §9.2.1.
-/

open scoped InnerProductSpace
open AxQM.Concrete

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Theorem 9.1 (the bound `(9.24)–(9.30)`).** For every
measurement `m` on the system `S` and any states `ρ σ`, the classical trace
distance of the Born-rule outcome distributions is at most the trace distance of
the states:
`D(pₘ, qₘ) ≤ D(ρ, σ)`.

A measurement can never distinguish `ρ` from `σ` more sharply than the trace
distance permits (measurement monotonicity). Faithful to N&C's "for all POVMs":
the bound is quantified over *arbitrary* finite outcome sets `ι`, so it covers
every POVM. Proof: `m.bornProb ρ` is definitionally `m.toPOVM.toPMF ρ.op`, so this
is exactly the operator-level upper bound `classicalTraceDist_toPMF_le` applied to
the induced POVM `m.toPOVM` and the density operators `ρ.op, σ.op`. -/
theorem State.classicalTraceDist_bornProb_le {ι : Type*} [Fintype ι]
    (m : Measurement ι S) (ρ σ : State S) :
    classicalTraceDist (m.bornProb ρ) (m.bornProb σ) ≤ ρ.traceDistance σ :=
  classicalTraceDist_toPMF_le m.toPOVM ρ.op σ.op

/-- **Nielsen & Chuang, Theorem 9.1 (achievability).** Some measurement attains the
trace distance: there is a projective measurement — the measurement in an
orthonormal eigenbasis of `ρ − σ`, `Measurement.ofOrthonormalBasis` of the
eigenvector basis — whose outcome distributions have classical trace distance
exactly `D(ρ, σ)`:
`D(pₘ, qₘ) = D(ρ, σ)`.

Together with `State.classicalTraceDist_bornProb_le` (the bound for every
measurement) this exhibits `D(ρ, σ)` as the maximum. The self-adjointness of
`ρ − σ` — needed to diagonalize it — comes for free: density operators are
positive, hence self-adjoint, so their difference is self-adjoint. Proof: on the
eigenbasis `pₘ − qₘ = λₘ` (the eigenvalue), so `∑ₘ|pₘ − qₘ| = ∑ₘ|λₘ| = ‖ρ − σ‖₁`,
which is the operator-level `classicalTraceDist_toPMF_eigenbasis_eq`. -/
theorem State.exists_measurement_classicalTraceDist_bornProb_eq (ρ σ : State S) :
    ∃ (n : ℕ) (m : Measurement (Fin n) S),
      classicalTraceDist (m.bornProb ρ) (m.bornProb σ) = ρ.traceDistance σ := by
  have : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
  -- `ρ − σ` is self-adjoint (difference of density operators, which are positive),
  -- hence its underlying linear map is symmetric and can be diagonalized.
  have hsa : IsSelfAdjoint (ρ.op - σ.op) :=
    ρ.isPositive_op.isSelfAdjoint.sub σ.isPositive_op.isSelfAdjoint
  have hsymm : ((ρ.op - σ.op : S.space →L[ℂ] S.space) : S.space →ₗ[ℂ] S.space).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  refine ⟨_, Measurement.ofOrthonormalBasis (hsymm.eigenvectorBasis rfl), ?_⟩
  -- The operator-level achievability lemma, re-expressed through the projective
  -- measurement's induced POVM (`toPOVM_ofOrthonormalBasis`). The goal matches it up
  -- to unfolding `bornProb = toPOVM.toPMF ∘ .op` and `traceDistance = ‖·‖₁/2` (defeq).
  have h := classicalTraceDist_toPMF_eigenbasis_eq ρ.op σ.op hsymm
  rw [← Measurement.toPOVM_ofOrthonormalBasis] at h
  exact h

/-- **Nielsen & Chuang, Theorem 9.1** (headline): the trace distance `D(ρ, σ)` is the
**greatest** classical trace distance of the outcome distributions achievable over
all measurements —
`D(ρ, σ) = max_{measurements} D(pₘ, qₘ)`.

This is the theorem's headline equality-to-a-maximum, packaged as `IsGreatest`: the
value `D(ρ, σ)` both lies in the set of achievable classical distances (by
`State.exists_measurement_classicalTraceDist_bornProb_eq`) and is an upper bound for
it (by `State.classicalTraceDist_bornProb_le`). The measurements range over every
finite outcome cardinality `Fin n`; since every POVM is the induced POVM of some
measurement, this is N&C's maximum over all POVMs. -/
theorem State.isGreatest_classicalTraceDist_bornProb (ρ σ : State S) :
    IsGreatest
      {d : ℝ | ∃ (n : ℕ) (m : Measurement (Fin n) S),
        d = classicalTraceDist (m.bornProb ρ) (m.bornProb σ)}
      (ρ.traceDistance σ) := by
  constructor
  · obtain ⟨n, m, hm⟩ := State.exists_measurement_classicalTraceDist_bornProb_eq ρ σ
    exact ⟨n, m, hm.symm⟩
  · rintro d ⟨n, m, rfl⟩
    exact State.classicalTraceDist_bornProb_le m ρ σ

end AxQM
