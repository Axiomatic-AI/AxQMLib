/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import AxQM.Postulates.Evolution

/-!
# AxQM — deferring a basis-permuting gate past a measurement (the reindexing engine)

The reindexing companion of the deferred-measurement engine (`DeferredMeasurement.lean`). That
engine defers a gate whose measurement operators commute *up to a fixed outcome* — `Mᵢ V = Wᵢ Mᵢ`.
A gate that *permutes* the measurement basis (a swap network, a wire relabelling) does not satisfy
that: it carries the operator of one outcome onto that of *another*. The condition it satisfies is

  `Mᵢ V = Wᵢ M_{e i}`   for every outcome `i`   (`hcomm`),

with `e : ι ≃ ι` the induced *outcome* relabelling. Then measuring `m` on the evolved state
`V ρ V†` is equivalent to measuring `m` on `ρ` at the *relabelled* outcome `e i` and then applying
`Wᵢ`:

* `Measurement.postOp_evolve_of_reindex_comm` — the branch-map identity
  `Eᵢ(V ρ V†) = Wᵢ E_{e i}(ρ) Wᵢ†` (the heart; carries both consequences below).
* `Measurement.trace_postOp_evolve_of_reindex_comm` — the branch traces agree,
  `tr Eᵢ(V ρ V†) = tr E_{e i}(ρ)`.
* `Measurement.bornProb_evolve_of_reindex_comm` — **outcome probabilities are relabelled**,
  `p(i ∣ V ρ V†) = p(e i ∣ ρ)`.
* `Measurement.postMeasurement_evolve_of_reindex_comm` — **the post-measurement state defers the
  gate**, `postMeas(V ρ V†, i) = Wᵢ · postMeas(ρ, e i)`.

The physical instance is Nielsen & Chuang, Problem 5.2: the swap network at the end of the quantum
Fourier transform, being applied just before a computational-basis measurement, contributes only a
relabelling of the classical outcomes — no two-qubit gate survives. A wire permutation permutes the
computational basis, so `Mᵢ (permWires σ) = (permWires σ) M_{e i}` with `e` the outcome relabelling
induced by `σ`, and `Wᵢ = permWires σ` (the permutation reappears on the collapsed basis state as a
classical wire relabelling).

## Generality

`hcomm` (`Mᵢ V = Wᵢ M_{e i}`) is the exact structural condition; the conclusions hold for an
*arbitrary* measurement `m`, gate `V`, outcome bijection `e`, outcome-gate family `W`, and state
`ρ`, no dimension specialized.

## Proof notes

Each proof is the exact analogue of its `DeferredMeasurement.lean` sibling, with the right-hand
outcome shifted from `i` to `e i`; `postOp_evolve_of_reindex_comm` regroups `Mᵢ (V ρ V†) Mᵢ†` as
`(Mᵢ V) ρ (Mᵢ V)†`, rewrites `Mᵢ V = Wᵢ M_{e i}`, and regroups back as
`Wᵢ (M_{e i} ρ M_{e i}†) Wᵢ†`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Branch-map identity for deferring a basis-permuting gate past a measurement.** If each
measurement operator `Mᵢ` of `m` carries the gate `V` onto the *reindexed* operator `M_{e i}` up to
an outcome-gate `Wᵢ` — `Mᵢ V = Wᵢ M_{e i}` (`hcomm`) — then the unnormalized post-measurement
operator of outcome `i` on the *evolved* state `V ρ V†` equals `Wᵢ` conjugating the branch of `ρ`
at the reindexed outcome `e i`:

  `Eᵢ(V ρ V†) = Mᵢ (V ρ V†) Mᵢ† = Wᵢ (M_{e i} ρ M_{e i}†) Wᵢ† = Wᵢ E_{e i}(ρ) Wᵢ†`. -/
theorem postOp_evolve_of_reindex_comm (m : Measurement ι S) (V : Evolution S) (W : ι → Evolution S)
    (e : ι ≃ ι) (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op (e i))) (ρ : State S)
    (i : ι) :
    ContinuousLinearMap.postOp m.op (V.evolve ρ).op i
      = (W i).op.comp ((ContinuousLinearMap.postOp m.op ρ.op (e i)).comp (adjoint (W i).op)) := by
  have conj_comp : ∀ A B X : S.space →L[ℂ] S.space,
      (A.comp B).comp (X.comp (adjoint (A.comp B)))
        = A.comp ((B.comp (X.comp (adjoint B))).comp (adjoint A)) := by
    intro A B X
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
  simp only [ContinuousLinearMap.postOp, Evolution.evolve_op]
  rw [← conj_comp (m.op i) V.op ρ.op, hcomm i, conj_comp (W i).op (m.op (e i)) ρ.op]

/-- **The two branch traces agree:** `tr Eᵢ(V ρ V†) = tr E_{e i}(ρ)`. Conjugating the branch by the
unitary `Wᵢ` (the branch-map identity `postOp_evolve_of_reindex_comm`) is trace-invariant. -/
theorem trace_postOp_evolve_of_reindex_comm (m : Measurement ι S) (V : Evolution S)
    (W : ι → Evolution S) (e : ι ≃ ι)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op (e i))) (ρ : State S) (i : ι) :
    LinearMap.trace ℂ S.space (ContinuousLinearMap.postOp m.op (V.evolve ρ).op i : S.space →ₗ[ℂ] _)
      = LinearMap.trace ℂ S.space
          (ContinuousLinearMap.postOp m.op ρ.op (e i) : S.space →ₗ[ℂ] _) := by
  rw [postOp_evolve_of_reindex_comm m V W e hcomm ρ i, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_cycle,
        ← ContinuousLinearMap.toLinearMap_comp,
    (W i).adjoint_comp_self, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id,
        LinearMap.comp_id]

/-- **Outcome probabilities are relabelled when a basis-permuting gate is deferred** (Postulate 3):
under `Mᵢ V = Wᵢ M_{e i}`, the Born probability of outcome `i` on `V ρ V†` equals that of the
relabelled outcome `e i` on `ρ`, `p(i ∣ V ρ V†) = p(e i ∣ ρ)`. -/
theorem bornProb_evolve_of_reindex_comm (m : Measurement ι S) (V : Evolution S)
    (W : ι → Evolution S) (e : ι ≃ ι)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op (e i))) (ρ : State S) (i : ι) :
    m.bornProb (V.evolve ρ) i = m.bornProb ρ (e i) := by
  rw [bornProb_eq_re_trace_postOp, bornProb_eq_re_trace_postOp,
    trace_postOp_evolve_of_reindex_comm m V W e hcomm ρ i]

/-- **The post-measurement state defers a basis-permuting gate** (Postulate 4): under
`Mᵢ V = Wᵢ M_{e i}`, the state after measuring outcome `i` on `V ρ V†` equals `Wᵢ` applied to the
state after measuring the relabelled outcome `e i` on `ρ`,

  `postMeas(V ρ V†, i) = Wᵢ · postMeas(ρ, e i)`.

The outcome must be possible on `ρ` at `e i` (`hp`); it is then equally possible on `V ρ V†` at `i`
since the probabilities are relabelled (`bornProb_evolve_of_reindex_comm`). -/
theorem postMeasurement_evolve_of_reindex_comm (m : Measurement ι S) (V : Evolution S)
    (W : ι → Evolution S) (e : ι ≃ ι)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op (e i))) (ρ : State S) (i : ι)
    (hp : m.bornProb ρ (e i) ≠ 0) :
    m.postMeasurement (V.evolve ρ) i
        (by rw [bornProb_evolve_of_reindex_comm m V W e hcomm ρ i]; exact hp)
      = (W i).evolve (m.postMeasurement ρ (e i) hp) := by
  apply State.ext
  rw [postMeasurement_op, ContinuousLinearMap.postState,
    trace_postOp_evolve_of_reindex_comm m V W e hcomm ρ i,
    postOp_evolve_of_reindex_comm m V W e hcomm ρ i, Evolution.evolve_op, postMeasurement_op,
    ContinuousLinearMap.postState]
  simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]

end Measurement

end AxQM
