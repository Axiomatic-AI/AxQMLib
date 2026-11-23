/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import AxQM.Postulates.Evolution
import AxQM.Postulates.API.DeferredMeasurementReindex

/-!
# AxQM — deferring a gate past a measurement (the deferred-measurement engine)

The reusable operator engine behind Nielsen & Chuang's **principle of deferred measurement**
(N&C §4.4, Exercise 4.35): a unitary applied *before* a measurement can be commuted to *after*
it, one outcome at a time, whenever the gate commutes with each measurement operator up to an
outcome-dependent unitary on the post-measurement branch.

Concretely, fix a measurement `m` (operators `Mᵢ`, Postulate 3), a gate `V` (an `Evolution`,
Postulate 5), and a family of gates `Wᵢ` (one per outcome), and suppose

  `Mᵢ V = Wᵢ Mᵢ`   for every outcome `i`   (`hcomm`).

Then measuring `m` on the evolved state `V ρ V†` is *equivalent* to measuring `m` on `ρ` and
then applying `Wᵢ` on the branch of outcome `i`:

* `Measurement.postOp_evolve_of_comm` — the **branch-map identity** (the heart): the unnormalized
  post-measurement operator `Eᵢ(V ρ V†) = Mᵢ (V ρ V†) Mᵢ†` equals `Wᵢ Eᵢ(ρ) Wᵢ†`, i.e. `Wᵢ`
  applied as a channel to the branch of `ρ`. This single operator identity carries *both* physical
  consequences below, since `tr` reads off the probability and the normalization reads off the
  state.
* `Measurement.trace_postOp_evolve_of_comm` — the branch traces agree, `tr Eᵢ(V ρ V†) = tr Eᵢ(ρ)`
  (conjugation by the unitary `Wᵢ` is trace-invariant).
* `Measurement.bornProb_evolve_of_comm` — **outcome probabilities are unchanged**,
  `p(i ∣ V ρ V†) = p(i ∣ ρ)` (Postulate 3): the gate does not affect the measurement statistics.
* `Measurement.postMeasurement_evolve_of_comm` — **the post-measurement state defers the gate**:
  `postMeas(V ρ V†, i) = Wᵢ · postMeas(ρ, i)` (Postulate 4), the collapsed state after measuring
  the evolved input equals `Wᵢ` applied to the collapsed state after measuring `ρ`.

## Generality

`hcomm` (`Mᵢ V = Wᵢ Mᵢ`) is the exact structural condition N&C's argument uses; the conclusions hold
for an *arbitrary* measurement `m`, gate `V`, outcome-gate family `W`, and state `ρ`, no dimension
specialized. Exercise 4.35 is the instance `m = measure the control`, `V = C(U)`, `Wᵢ = U^i` on the
target (`ControlMeasurementCommute.lean`).

## Relation to the reindexing engine

`Mᵢ V = Wᵢ Mᵢ` is the special case of the *reindexing* commutation `Mᵢ V = Wᵢ M_{e i}`
(`DeferredMeasurementReindex.lean`) at the identity outcome-relabelling `e = Equiv.refl` — a gate
that *fixes* each measurement outcome, rather than permuting them. The four core lemmas below are
therefore thin `Equiv.refl` instances of their reindexing counterparts (no duplicated proof body);
only the product-form lemmas `op_comp_prod_of_forall_comm` and its Born/collapse corollaries — which
have no reindexing analogue — carry their own proofs.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- **Branch-map identity for deferring a gate past a measurement** (the engine of N&C's principle
of deferred measurement, §4.4). If each measurement operator `Mᵢ` of `m` commutes with the gate `V`
up to an outcome-gate `Wᵢ` — `Mᵢ V = Wᵢ Mᵢ` (`hcomm`) — then the unnormalized post-measurement
operator of outcome `i` on the *evolved* state `V ρ V†` equals `Wᵢ` conjugating the branch of `ρ`:

  `Eᵢ(V ρ V†) = Mᵢ (V ρ V†) Mᵢ† = Wᵢ (Mᵢ ρ Mᵢ†) Wᵢ† = Wᵢ Eᵢ(ρ) Wᵢ†`.

This one operator identity packages both physical consequences (probability and post-state), since
the trace reads off `p(i)` and the normalization reads off the collapsed state. -/
theorem postOp_evolve_of_comm (m : Measurement ι S) (V : Evolution S) (W : ι → Evolution S)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op i)) (ρ : State S) (i : ι) :
    ContinuousLinearMap.postOp m.op (V.evolve ρ).op i
      = (W i).op.comp ((ContinuousLinearMap.postOp m.op ρ.op i).comp (adjoint (W i).op)) :=
  postOp_evolve_of_reindex_comm m V W (Equiv.refl ι) hcomm ρ i

/-- **The two branch traces agree:** `tr Eᵢ(V ρ V†) = tr Eᵢ(ρ)`. Conjugating the branch `Eᵢ(ρ)` by
the unitary `Wᵢ` (the branch-map identity `postOp_evolve_of_comm`) is trace-invariant, by cyclicity
of the trace collapsing `Wᵢ† Wᵢ = 1`. This is the operator fact under both the probability equality
and the shared normalization factor of the post-measurement states. -/
theorem trace_postOp_evolve_of_comm (m : Measurement ι S) (V : Evolution S) (W : ι → Evolution S)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op i)) (ρ : State S) (i : ι) :
    LinearMap.trace ℂ S.space (ContinuousLinearMap.postOp m.op (V.evolve ρ).op i : S.space →ₗ[ℂ] _)
      = LinearMap.trace ℂ S.space (ContinuousLinearMap.postOp m.op ρ.op i : S.space →ₗ[ℂ] _) :=
  trace_postOp_evolve_of_reindex_comm m V W (Equiv.refl ι) hcomm ρ i

/-- **Outcome probabilities are unchanged when the gate is deferred** (Postulate 3): under the
commutation `Mᵢ V = Wᵢ Mᵢ`, the Born probability of outcome `i` on the evolved state `V ρ V†` equals
that on `ρ`, `p(i ∣ V ρ V†) = p(i ∣ ρ)`. The measurement statistics do not see the gate `V`. -/
theorem bornProb_evolve_of_comm (m : Measurement ι S) (V : Evolution S) (W : ι → Evolution S)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op i)) (ρ : State S) (i : ι) :
    m.bornProb (V.evolve ρ) i = m.bornProb ρ i :=
  bornProb_evolve_of_reindex_comm m V W (Equiv.refl ι) hcomm ρ i

/-- **The post-measurement state defers the gate** (Postulate 4): under the commutation
`Mᵢ V = Wᵢ Mᵢ`, the state after measuring outcome `i` on the evolved input `V ρ V†` equals `Wᵢ`
applied to the state after measuring outcome `i` on `ρ`,

  `postMeas(V ρ V†, i) = Wᵢ · postMeas(ρ, i)`.

The `V`-then-measure branch is the measure-then-`Wᵢ` branch. The outcome must be possible on `ρ`
(`hp : p(i ∣ ρ) ≠ 0`); it is then equally possible on `V ρ V†`, since the probabilities agree
(`bornProb_evolve_of_comm`). -/
theorem postMeasurement_evolve_of_comm (m : Measurement ι S) (V : Evolution S) (W : ι → Evolution S)
    (hcomm : ∀ i, (m.op i).comp V.op = (W i).op.comp (m.op i)) (ρ : State S) (i : ι)
    (hp : m.bornProb ρ i ≠ 0) :
    m.postMeasurement (V.evolve ρ) i
        (by rw [bornProb_evolve_of_comm m V W hcomm ρ i]; exact hp)
      = (W i).evolve (m.postMeasurement ρ i hp) :=
  postMeasurement_evolve_of_reindex_comm m V W (Equiv.refl ι) hcomm ρ i hp

/-! ## Deferring a measurement past a *composition* of gates

The single-gate deferral above commutes a measurement past one gate. A circuit is a *product* of
gates, so the whole-circuit reduction needs to commute a measurement past a run of them. If the
measurement commutes with *each* gate `V a` of a family (indexed by `a ∈ Us`) up to a branch family
`W a` — `Mᵢ (V a) = (W a i) Mᵢ` — then it commutes with the whole composition `(Us.map V).prod` up
to the *composition* of the branch gates, and the Born-rule / collapse readings follow at the
product. This is the inductive engine a measured circuit's reduction runs one gate at a time. -/

/-- **Deferring a measurement past a composition of gates** (the product form of the commutation
hypothesis `hcomm`). If a measurement `m` commutes with every gate `V a` (`a ∈ Us`) up to the branch
family `W a` — `Mᵢ (V a) = (W a i) Mᵢ` (`hcomm`) — then `m` commutes with their whole composition
`(Us.map V).prod` up to the *composed* branch gates `(Us.map (fun a => W a i)).prod`:

  `Mᵢ · (Vₖ ⋯ V₁) = (Wₖ ⋯ W₁)ᵢ · Mᵢ`.

Induction over `Us`: the head commutation `Mᵢ (V hd) = (W hd i) Mᵢ` threads past the accumulated
tail commutation, using multiplicativity of `Evolution.op` on the list product
(`Evolution.mul_def` / `Evolution.comp_op`) and associativity of composition. This is the exact
hypothesis `postOp_evolve_of_comm` (and its corollaries) consume, so a whole sub-circuit of gates —
each individually deferrable — defers as one. -/
theorem op_comp_prod_of_forall_comm {α : Type*} (m : Measurement ι S) (Us : List α)
    (V : α → Evolution S) (W : α → ι → Evolution S)
    (hcomm : ∀ a ∈ Us, ∀ i, (m.op i).comp (V a).op = (W a i).op.comp (m.op i)) (i : ι) :
    (m.op i).comp (Us.map V).prod.op
      = (Us.map (fun a => W a i)).prod.op.comp (m.op i) := by
  revert hcomm
  induction Us with
  | nil => intro _; simp [ContinuousLinearMap.one_def]
  | cons hd tl ih =>
    intro hcomm
    simp only [List.map_cons, List.prod_cons, Evolution.mul_def, Evolution.comp_op]
    rw [← ContinuousLinearMap.comp_assoc, hcomm hd List.mem_cons_self i,
      ContinuousLinearMap.comp_assoc, ih (fun a ha => hcomm a (List.mem_cons_of_mem hd ha)),
      ← ContinuousLinearMap.comp_assoc]

/-- **Outcome probabilities are unchanged when a whole composition of gates is deferred**
(Postulate 3, product form). Under the pointwise commutation `Mᵢ (V a) = (W a i) Mᵢ` for every
`a ∈ Us`, the Born probability of outcome `i` on the state evolved by the composition
`(Us.map V).prod` equals that on `ρ`: the measurement statistics do not see the sub-circuit. The
instance of `bornProb_evolve_of_comm` at the product gate and the composed branch family, whose
commutation is `op_comp_prod_of_forall_comm`. -/
theorem bornProb_evolve_prod_of_forall_comm {α : Type*} (m : Measurement ι S) (Us : List α)
    (V : α → Evolution S) (W : α → ι → Evolution S)
    (hcomm : ∀ a ∈ Us, ∀ i, (m.op i).comp (V a).op = (W a i).op.comp (m.op i))
    (ρ : State S) (i : ι) :
    m.bornProb ((Us.map V).prod.evolve ρ) i = m.bornProb ρ i :=
  bornProb_evolve_of_comm m (Us.map V).prod (fun i => (Us.map (fun a => W a i)).prod)
    (fun i => op_comp_prod_of_forall_comm m Us V W hcomm i) ρ i

/-- **The post-measurement state defers a whole composition of gates** (Postulate 4, product form).
Under the pointwise commutation `Mᵢ (V a) = (W a i) Mᵢ` for every `a ∈ Us`, the state after
measuring outcome `i` on the input evolved by the composition `(Us.map V).prod` equals the composed
branch gates `(Us.map (fun a => W a i)).prod` applied to the state after measuring `ρ`:

  `postMeas((Vₖ ⋯ V₁) ρ (Vₖ ⋯ V₁)†, i) = (Wₖ ⋯ W₁)ᵢ · postMeas(ρ, i)`.

The whole sub-circuit is deferred past the measurement in one step. The instance of
`postMeasurement_evolve_of_comm` at the product gate and the composed branch family
(`op_comp_prod_of_forall_comm`). -/
theorem postMeasurement_evolve_prod_of_forall_comm {α : Type*} (m : Measurement ι S) (Us : List α)
    (V : α → Evolution S) (W : α → ι → Evolution S)
    (hcomm : ∀ a ∈ Us, ∀ i, (m.op i).comp (V a).op = (W a i).op.comp (m.op i))
    (ρ : State S) (i : ι) (hp : m.bornProb ρ i ≠ 0) :
    m.postMeasurement ((Us.map V).prod.evolve ρ) i
        (by rw [bornProb_evolve_prod_of_forall_comm m Us V W hcomm]; exact hp)
      = (Us.map (fun a => W a i)).prod.evolve (m.postMeasurement ρ i hp) :=
  postMeasurement_evolve_of_comm m (Us.map V).prod (fun i => (Us.map (fun a => W a i)).prod)
    (fun i => op_comp_prod_of_forall_comm m Us V W hcomm i) ρ i hp

end Measurement

end AxQM
