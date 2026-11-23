/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.API.MeasurementPrecompose
import AxQM.Postulates.API.CertainMeasurement
import AxQM.Postulates.API.DeferredMeasurement
import AxQM.Postulates.API.ToffoliHadamard
import AxQM.Postulates.API.AdaptiveMeasurement
import AxQM.Postulates.API.MeasurementReindex
import AxQM.Postulates.Composite

/-!
# Finite-round two-way LOCC protocols on a bipartite system

This module introduces the apparatus needed to state **Nielsen & Chuang, Proposition 12.14**
faithfully — a formal type of **LOCC protocol** (Local Operations and Classical Communication) over
a bipartite system `A ⊗ B`, together with its deterministic transformation semantics and the
one-way (single Alice-measurement / Bob-unitary) protocol form that the proposition reduces to.

## The model

A finite-round two-way LOCC protocol is a tree (`LOCCProtocol A B`): at each node one party performs
a **local operation** on their own factor — a measurement (a local *instrument*, the general form of
a local quantum operation, with the classical outcome broadcast to the other party) or a local
unitary — and the protocol continues, with the next operation allowed to depend on the whole
classical record so far (the branch). The five constructors are:

* `terminal` — stop.
* `aliceMeasure n m k` — Alice measures `m` (an `n`-outcome measurement on `A`), broadcasts the
  outcome `j`, and the protocol continues as `k j` (Alice→Bob classical communication).
* `bobMeasure n m k` — Bob measures `m` on `B`, broadcasts `j`, continue as `k j` (Bob→Alice
  classical communication).
* `aliceUnitary U k` / `bobUnitary V k` — a party applies a local unitary and continues.

Outcome sets are taken to be `Fin n`; every finite measurement reindexes to this canonical form, so
this is a faithful model, not a restriction. This is a genuine model of the finite-round two-way
LOCC of N&C §12.5.1: local instruments interleaved with two-way classical communication (the
alternation of `aliceMeasure`/`bobMeasure` and the outcome-dependent continuation `k`).

## Semantics

`LOCCProtocol.Transforms P ρ σ` is **deterministic** transformation of `ρ` into `σ`: running `P` on
`ρ`, *every* branch that occurs with nonzero probability ends in `σ`. This is exactly N&C's notion
of "`ρ` can be transformed to `σ` by LOCC" in the pure-state setting — "she starts with `ρ` and ends
with `σ` regardless of the measurement outcome" (Theorem 12.15's usage of this proposition).

## The reduction target and the Proposition 12.14 goal

`OneWayLOCC ρ σ` is the single-round form: `∃` an Alice measurement `{Mⱼ}` and Bob unitaries `{Vⱼ}`
such that on every branch `j`, after Alice measures and Bob applies `Vⱼ`, the state is `σ`. It is
realized by the concrete protocol `LOCCProtocol.oneWay` (`OneWayLOCC.exists_transforms`), so it is a
bona-fide sub-class of general LOCC transformability. This is precisely the density-operator content
that `State.LOCCConvertible` (Theorem 12.15) packages on the *reduced* states.

**Proposition 12.14** is then the headline reduction

> `∀ (P : LOCCProtocol A B) (ρ σ), P.Transforms ρ σ → OneWayLOCC ρ σ`

— every finite-round two-way protocol collapses to the one-way form. This module supplies the type
in which that statement lives; the proof (using the measurement-simulation crux, generalised off
the swap-symmetric normal form, plus the deferral of Bob's unitaries past Alice's later
measurements — `Evolution.onLeft_comm_onRight` — and the combination of Alice's measurements,
Ex. 2.57) is in `AxQM/NC/Ch12/Proposition12_14.lean`.
-/

noncomputable section

namespace AxQM

/-- A **finite-round two-way LOCC protocol** on the bipartite system `A ⊗ B`: a tree of local
operations (measurements and unitaries by either party) interleaved with classical communication.
At an `aliceMeasure`/`bobMeasure` node the measuring party broadcasts its `Fin n` outcome and the
continuation `k` may depend on it (the classical record); `aliceUnitary`/`bobUnitary` are
deterministic local unitary rounds. Outcome sets are `Fin n` (every finite measurement reindexes to
this), so the model is faithful to N&C §12.5.1's LOCC without loss of generality. -/
inductive LOCCProtocol (A B : QSystem) where
  /-- Stop: the protocol performs no further operations. -/
  | terminal : LOCCProtocol A B
  /-- Alice measures the `n`-outcome measurement `m` on her factor `A`, broadcasts the outcome `j`,
  and the protocol continues as `k j` (Alice→Bob classical communication). -/
  | aliceMeasure (n : ℕ) (m : Measurement (Fin n) A) (k : Fin n → LOCCProtocol A B) :
      LOCCProtocol A B
  /-- Bob measures the `n`-outcome measurement `m` on his factor `B`, broadcasts the outcome `j`,
  and the protocol continues as `k j` (Bob→Alice classical communication). -/
  | bobMeasure (n : ℕ) (m : Measurement (Fin n) B) (k : Fin n → LOCCProtocol A B) :
      LOCCProtocol A B
  /-- Alice applies the local unitary `U` on her factor `A`, then continues as `k`. -/
  | aliceUnitary (U : Evolution A) (k : LOCCProtocol A B) : LOCCProtocol A B
  /-- Bob applies the local unitary `V` on his factor `B`, then continues as `k`. -/
  | bobUnitary (V : Evolution B) (k : LOCCProtocol A B) : LOCCProtocol A B

variable {A B : QSystem}

/-- **Deterministic transformation semantics.** `P.Transforms ρ σ` holds when running the protocol
`P` on the joint state `ρ` sends *every* branch of nonzero probability to `σ`. This is N&C's
"transformed to `σ` by LOCC" in the deterministic sense: the outcome is `σ` regardless of the
measurement results. Defined by structural recursion on `P`: a measurement round requires each
possible post-measurement branch to transform onward to `σ`; a unitary round evolves the state and
continues; `terminal` requires the current state to already be `σ`. -/
def LOCCProtocol.Transforms :
    LOCCProtocol A B → State (A.compose B) → State (A.compose B) → Prop
  | .terminal, ρ, σ => ρ = σ
  | .aliceMeasure _ m k, ρ, σ =>
      ∀ j, (h : (m.onLeft B).bornProb ρ j ≠ 0) →
        (k j).Transforms ((m.onLeft B).postMeasurement ρ j h) σ
  | .bobMeasure _ m k, ρ, σ =>
      ∀ j, (h : (m.onRight A).bornProb ρ j ≠ 0) →
        (k j).Transforms ((m.onRight A).postMeasurement ρ j h) σ
  | .aliceUnitary U k, ρ, σ => k.Transforms ((U.onLeft B).evolve ρ) σ
  | .bobUnitary V k, ρ, σ => k.Transforms ((V.onRight A).evolve ρ) σ

@[simp] theorem LOCCProtocol.terminal_transforms_iff (ρ σ : State (A.compose B)) :
    (LOCCProtocol.terminal : LOCCProtocol A B).Transforms ρ σ ↔ ρ = σ := Iff.rfl

/-- `terminal` transforms every state to itself. -/
theorem LOCCProtocol.terminal_transforms_self (ρ : State (A.compose B)) :
    (LOCCProtocol.terminal : LOCCProtocol A B).Transforms ρ ρ := rfl

@[simp] theorem LOCCProtocol.aliceMeasure_transforms_iff (n : ℕ) (m : Measurement (Fin n) A)
    (k : Fin n → LOCCProtocol A B) (ρ σ : State (A.compose B)) :
    (LOCCProtocol.aliceMeasure n m k).Transforms ρ σ
      ↔ ∀ j, (h : (m.onLeft B).bornProb ρ j ≠ 0) →
          (k j).Transforms ((m.onLeft B).postMeasurement ρ j h) σ := Iff.rfl

@[simp] theorem LOCCProtocol.bobMeasure_transforms_iff (n : ℕ) (m : Measurement (Fin n) B)
    (k : Fin n → LOCCProtocol A B) (ρ σ : State (A.compose B)) :
    (LOCCProtocol.bobMeasure n m k).Transforms ρ σ
      ↔ ∀ j, (h : (m.onRight A).bornProb ρ j ≠ 0) →
          (k j).Transforms ((m.onRight A).postMeasurement ρ j h) σ := Iff.rfl

@[simp] theorem LOCCProtocol.aliceUnitary_transforms_iff (U : Evolution A) (k : LOCCProtocol A B)
    (ρ σ : State (A.compose B)) :
    (LOCCProtocol.aliceUnitary U k).Transforms ρ σ ↔ k.Transforms ((U.onLeft B).evolve ρ) σ :=
  Iff.rfl

@[simp] theorem LOCCProtocol.bobUnitary_transforms_iff (V : Evolution B) (k : LOCCProtocol A B)
    (ρ σ : State (A.compose B)) :
    (LOCCProtocol.bobUnitary V k).Transforms ρ σ ↔ k.Transforms ((V.onRight A).evolve ρ) σ :=
  Iff.rfl

/-- The canonical **one-way protocol** of N&C Proposition 12.14: Alice performs the single
measurement `m` on her factor, broadcasts the outcome `j`, and Bob applies the conditional unitary
`V j` on his factor. This is the protocol the proposition reduces every finite-round two-way LOCC
protocol to. -/
def LOCCProtocol.oneWay (n : ℕ) (m : Measurement (Fin n) A) (V : Fin n → Evolution B) :
    LOCCProtocol A B :=
  .aliceMeasure n m (fun j => .bobUnitary (V j) .terminal)

/-- The one-way protocol `LOCCProtocol.oneWay n m V` transforms `ρ` to `σ` exactly when, for every
outcome `j` Alice can obtain, applying Bob's conditional unitary `V j` to Alice's post-measurement
state gives `σ`. This is N&C's single-round form written out. -/
theorem LOCCProtocol.oneWay_transforms (n : ℕ) (m : Measurement (Fin n) A)
    (V : Fin n → Evolution B) (ρ σ : State (A.compose B)) :
    (LOCCProtocol.oneWay n m V).Transforms ρ σ
      ↔ ∀ j, (h : (m.onLeft B).bornProb ρ j ≠ 0) →
          ((V j).onRight A).evolve ((m.onLeft B).postMeasurement ρ j h) = σ := Iff.rfl

/-- **One-way LOCC reachability** of joint states (N&C Proposition 12.14's target form): there is an
Alice measurement `{Mⱼ}` and a family of Bob unitaries `{Vⱼ}` such that, deterministically on every
branch, Alice measuring and Bob applying `Vⱼ` carries `ρ` to `σ`. This is the joint-state form of
the one-way protocol that the reduced-state predicate `State.LOCCConvertible` (Theorem 12.15)
packages; `Proposition 12.14` asserts that general LOCC transformability collapses to it. -/
def OneWayLOCC (ρ σ : State (A.compose B)) : Prop :=
  ∃ (n : ℕ) (m : Measurement (Fin n) A) (V : Fin n → Evolution B),
    (LOCCProtocol.oneWay n m V).Transforms ρ σ

/-- The one-way form is a genuine LOCC protocol: if `ρ` is one-way reachable to `σ`, then some
`LOCCProtocol` transforms `ρ` to `σ`. Hence `OneWayLOCC` is a sub-class of general LOCC
transformability — the easy inclusion of Proposition 12.14; the proposition proves the converse. -/
theorem OneWayLOCC.exists_transforms {ρ σ : State (A.compose B)} (h : OneWayLOCC ρ σ) :
    ∃ P : LOCCProtocol A B, P.Transforms ρ σ := by
  obtain ⟨n, m, V, hP⟩ := h
  exact ⟨_, hP⟩

/-! ## Closure of one-way LOCC under the deterministic protocol steps

The reduction `LOCCProtocol.Transforms P ρ σ → OneWayLOCC ρ σ` (Proposition 12.14) is an induction
on the protocol tree `P`. Its five cases are exactly five closure properties of `OneWayLOCC` — one
per constructor. The first three below cover the *deterministic* steps (`terminal`, `aliceUnitary`,
`bobUnitary`), which need no measurement simulation: reflexivity, and closure under prepending a
local unitary by either party. `prepend_aliceMeasure` handles the `aliceMeasure` case by combining
Alice's rounds into a single measurement (the dependent Ex. 2.57 cascade). The last case
(`bobMeasure`, simulating Bob's measurement by Alice — N&C's Eq. (12.159) crux) is built in
`NC/Ch12/Proposition12_14.lean` (`OneWayLOCC.prepend_bobMeasure`). -/

/-- **Reflexivity of one-way LOCC reachability.** Every joint state is one-way reachable to itself:
Alice performs the trivial single-outcome measurement (which does not disturb the state) and Bob
does nothing. This is the `terminal` case of the Proposition 12.14 reduction induction. -/
theorem OneWayLOCC.refl (ρ : State (A.compose B)) : OneWayLOCC ρ ρ := by
  refine ⟨1, certainMeasurement (T := A) (0 : Fin 1), fun _ => Evolution.id, ?_⟩
  rw [LOCCProtocol.oneWay_transforms]
  intro j hj
  have hop : ((certainMeasurement (T := A) (0 : Fin 1)).onLeft B).op j = 1 := by
    have hj0 : j = 0 := Subsingleton.elim j 0
    subst hj0
    rw [Measurement.onLeft_op, certainMeasurement_op, ite_eq_left rfl]
    exact TensorProduct.mapL_one
  rw [Measurement.postMeasurement_eq_self_of_op_eq_one
    ((certainMeasurement (T := A) (0 : Fin 1)).onLeft B) ρ j hop hj,
    Evolution.id_onRight, Evolution.evolve_id]

/-- **One-way LOCC absorbs a leading Alice-local unitary.** If the state `(U ⊗ 1) ρ (U ⊗ 1)†`
obtained after Alice applies `U` on her factor is one-way reachable to `σ`, then so is `ρ`: fold `U`
into Alice's measurement operators (`Measurement.precompose`), since "apply `U` then measure `m`" is
itself a single Alice measurement. This is the `aliceUnitary` case of the reduction induction. -/
theorem OneWayLOCC.prepend_aliceUnitary (U : Evolution A) {ρ σ : State (A.compose B)}
    (h : OneWayLOCC ((U.onLeft B).evolve ρ) σ) : OneWayLOCC ρ σ := by
  obtain ⟨n, m, V, hP⟩ := h
  rw [LOCCProtocol.oneWay_transforms] at hP
  refine ⟨n, m.precompose U, V, ?_⟩
  rw [LOCCProtocol.oneWay_transforms]
  intro j hj
  rw [Measurement.onLeft_precompose_postMeasurement]
  exact hP j _

/-- **One-way LOCC absorbs a leading Bob-local unitary.** If the state `(1 ⊗ V) ρ (1 ⊗ V)†` obtained
after Bob applies `V` on his factor is one-way reachable to `σ`, then so is `ρ`: `V` commutes with
Alice's measurement (they act on disjoint factors), so it defers past her round and composes into
Bob's conditional correction `Wⱼ ↦ Wⱼ V`. This is the `bobUnitary` case of the reduction. -/
theorem OneWayLOCC.prepend_bobUnitary (V : Evolution B) {ρ σ : State (A.compose B)}
    (h : OneWayLOCC ((V.onRight A).evolve ρ) σ) : OneWayLOCC ρ σ := by
  obtain ⟨n, m, W, hP⟩ := h
  rw [LOCCProtocol.oneWay_transforms] at hP
  refine ⟨n, m, fun j => (W j).comp V, ?_⟩
  rw [LOCCProtocol.oneWay_transforms]
  intro j hj
  have hcomm : ∀ k, ((m.onLeft B).op k).comp (V.onRight A).op
      = (V.onRight A).op.comp ((m.onLeft B).op k) :=
    fun k => Measurement.onLeft_op_comm_onRight_op m V k
  have hjV : (m.onLeft B).bornProb ((V.onRight A).evolve ρ) j ≠ 0 := by
    rw [Measurement.bornProb_evolve_of_comm (m.onLeft B) (V.onRight A) (fun _ => V.onRight A)
      hcomm ρ j]
    exact hj
  rw [← Evolution.onRight_comp, Evolution.evolve_comp,
    ← Measurement.postMeasurement_evolve_of_comm (m.onLeft B) (V.onRight A) (fun _ => V.onRight A)
      hcomm ρ j hj]
  exact hP j hjV

/-- **One-way LOCC absorbs a leading Alice measurement round** — the `aliceMeasure` case of the
Proposition 12.14 reduction, and the formal content of N&C's "all the measurements performed by
Alice can be combined into one single measurement (Exercise 2.57)".

If, after Alice measures `m` (an `n`-outcome measurement on her factor) and obtains any possible
outcome `j`, the resulting post-measurement state is one-way reachable to `σ`, then `ρ` itself is:
Alice performs the *single* measurement `m.adaptiveCascade M'` that measures `m` and then, depending
on the outcome `j`, the measurement `M' j` witnessing the reachability of branch `j` (the dependent
Exercise 2.57 cascade). Its `Σ j, Fin (N j)` outcomes are relabelled to `Fin _`
(`reindexOutcome`); for the joint outcome `⟨j, k⟩` Bob applies the correction `V' j k` from branch
`j`'s witness. A joint outcome `⟨j, k⟩` of nonzero probability forces `j` to be a possible outcome
of `m` (`adaptiveCascade_bornProb_fst_ne_zero`), so the branch witness applies; the Born
probabilities and post-measurement states of the combined round chain through the cascade laws
(`adaptiveCascade_bornProb` / `adaptiveCascade_postMeasurement`). Branches `j` of zero probability
are filled with a trivial witness — they never occur, so their choice is immaterial. -/
theorem OneWayLOCC.prepend_aliceMeasure {n : ℕ} (m : Measurement (Fin n) A)
    {ρ σ : State (A.compose B)}
    (h : ∀ j, (hj : (m.onLeft B).bornProb ρ j ≠ 0) →
      OneWayLOCC ((m.onLeft B).postMeasurement ρ j hj) σ) :
    OneWayLOCC ρ σ := by
  classical
  -- Totalise the per-branch witnesses (trivial on the zero-probability branches, which never
  -- occur).
  have h' : ∀ j, ∃ (N : ℕ) (M' : Measurement (Fin N) A) (V' : Fin N → Evolution B),
      (hj : (m.onLeft B).bornProb ρ j ≠ 0) →
        (LOCCProtocol.oneWay N M' V').Transforms ((m.onLeft B).postMeasurement ρ j hj) σ := by
    intro j
    by_cases hj : (m.onLeft B).bornProb ρ j = 0
    · exact ⟨1, certainMeasurement (T := A) (0 : Fin 1), fun _ => Evolution.id,
        fun hj' => absurd hj hj'⟩
    · obtain ⟨N, M', V', hV'⟩ := h j hj
      exact ⟨N, M', V', fun _ => hV'⟩
  choose N M' V' hV' using h'
  set e : Fin (Fintype.card (Σ j, Fin (N j))) ≃ (Σ j, Fin (N j)) :=
    (Fintype.equivFin (Σ j, Fin (N j))).symm with he
  refine ⟨Fintype.card (Σ j, Fin (N j)), (m.adaptiveCascade M').reindexOutcome e,
    fun i => V' (e i).1 (e i).2, ?_⟩
  rw [LOCCProtocol.oneWay_transforms]
  intro i hi
  rcases hjk : e i with ⟨j, k⟩
  -- The reindexed combined measurement (lifted to `A ⊗ B`) at outcome `i` has the same operator as
  -- the lifted adaptive cascade at `⟨j, k⟩`, so its statistics transport through the cascade laws.
  have hop : (((m.adaptiveCascade M').reindexOutcome e).onLeft B).op i
      = ((m.onLeft B).adaptiveCascade (fun j' => (M' j').onLeft B)).op ⟨j, k⟩ := by
    rw [Measurement.onLeft_op, Measurement.reindexOutcome_op, hjk,
      ← Measurement.adaptiveCascade_onLeft_op, Measurement.onLeft_op]
  have hcomb :
      ((m.onLeft B).adaptiveCascade (fun j' => (M' j').onLeft B)).bornProb ρ ⟨j, k⟩ ≠ 0 := by
    rwa [← Measurement.bornProb_congr hop ρ]
  have hl : (m.onLeft B).bornProb ρ j ≠ 0 :=
    Measurement.adaptiveCascade_bornProb_fst_ne_zero (m.onLeft B) (fun j' => (M' j').onLeft B)
      ρ j k hcomb
  have hfac : ((m.onLeft B).adaptiveCascade (fun j' => (M' j').onLeft B)).bornProb ρ ⟨j, k⟩
      = (m.onLeft B).bornProb ρ j
        * ((M' j).onLeft B).bornProb ((m.onLeft B).postMeasurement ρ j hl) k :=
    Measurement.adaptiveCascade_bornProb (m.onLeft B) (fun j' => (M' j').onLeft B) ρ j k hl
  have hm : ((M' j).onLeft B).bornProb ((m.onLeft B).postMeasurement ρ j hl) k ≠ 0 :=
    right_ne_zero_of_mul (hfac ▸ hcomb)
  have hpost : (((m.adaptiveCascade M').reindexOutcome e).onLeft B).postMeasurement ρ i hi
      = ((M' j).onLeft B).postMeasurement ((m.onLeft B).postMeasurement ρ j hl) k hm := by
    rw [Measurement.postMeasurement_congr hop ρ hi hcomb]
    exact Measurement.adaptiveCascade_postMeasurement (m.onLeft B) (fun j' => (M' j').onLeft B)
      ρ j k hl hm
  rw [hpost]
  have key := hV' j hl
  rw [LOCCProtocol.oneWay_transforms] at key
  exact key k hm

/-- **One-way LOCC absorbs a leading Alice measurement round with an arbitrary finite outcome set.**
The general-outcome-index form of `OneWayLOCC.prepend_aliceMeasure`: for a measurement `m` on
Alice's factor whose outcomes range over any finite type `κ` (not necessarily `Fin n`), if each
possible post-measurement branch is one-way reachable to `σ`, then so is `ρ`. Relabel the outcomes
`κ → Fin (Fintype.card κ)` along `Fintype.equivFin` (`Measurement.reindexOutcome`) and apply the
`Fin`-indexed `prepend_aliceMeasure`; the relabelling leaves the physics untouched, so Born
probabilities and post-measurement states transport by `Measurement.bornProb_congr` /
`Measurement.postMeasurement_congr` on the equal outcome operators
(`(m.reindexOutcome e).op i = m.op (e i)`). This lets an Alice measurement with a non-`Fin`
outcome set feed the `aliceMeasure` closure — used by Proposition 12.14, whose simulating Alice
measurement is indexed by `Option ι` (Bob's outcomes plus a completeness caveat). -/
theorem OneWayLOCC.prepend_aliceMeasure' {κ : Type*} [Fintype κ] (m : Measurement κ A)
    {ρ σ : State (A.compose B)}
    (h : ∀ j, (hj : (m.onLeft B).bornProb ρ j ≠ 0) →
      OneWayLOCC ((m.onLeft B).postMeasurement ρ j hj) σ) :
    OneWayLOCC ρ σ := by
  refine OneWayLOCC.prepend_aliceMeasure (m.reindexOutcome (Fintype.equivFin κ).symm)
    (fun i hi => ?_)
  have hop : ((m.reindexOutcome (Fintype.equivFin κ).symm).onLeft B).op i
      = (m.onLeft B).op ((Fintype.equivFin κ).symm i) := by
    rw [Measurement.onLeft_op, Measurement.reindexOutcome_op, Measurement.onLeft_op]
  have hj : (m.onLeft B).bornProb ρ ((Fintype.equivFin κ).symm i) ≠ 0 := by
    rwa [← Measurement.bornProb_congr hop ρ]
  rw [Measurement.postMeasurement_congr hop ρ hi hj]
  exact h _ hj

end AxQM
