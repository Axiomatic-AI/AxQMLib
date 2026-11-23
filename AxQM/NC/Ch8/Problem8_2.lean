/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.API.MeasurementCoarseGrain
import AxQM.Postulates.API.Mixture
import AxQM.Postulates.API.Associator
import AxQM.Postulates.SystemIso
import AxQM.Postulates.Evolution

/-!
# Nielsen & Chuang, Problem 8.2 (Teleportation as a quantum operation)

*(N&C p. 395; due to Nielsen and Caves [NC97].)*

Show teleportation via imperfect entanglement induces operation Ê_m reversible by R_m to recover ρ.

This file formalises **both halves** of the problem, in terms of states, measurements and
evolutions. The **first half** — *that Alice's local
measurement induces an operation `Êₘ` carrying the input state of system 1 to the (normalised) final
state of system 3* — is the induced-state block (`teleportationInducedState` and the outcome
probabilities). The **second half** — *the reversibility criterion (8.189), that teleportation is
accomplished when Bob can reverse `Êₘ` by a trace-preserving quantum operation `Rₘ`* — is the
recovery block (`teleportationRecovery`, `TeleportationRecovers` and its injectivity consequence).

## The physical setup, and how it is modelled

Three systems: `A` (system 1, Alice's qubit `ρ` to teleport), `B` (system 2, Alice's half of the
resource) and `C` (system 3, Bob's half). The imperfect entanglement is a *fixed resource state*
`σ : State (B ⊗ C)` — a general (possibly mixed, possibly non-maximally-entangled) joint state, so
"imperfectly entangled" is captured by letting `σ` be arbitrary rather than a maximally entangled
pair. The global initial state is the product `ρ ⊗ σ` on `A ⊗ (B ⊗ C)`.

Alice measures systems 1 and 2, i.e. the pair `A ⊗ B`. To act on that pair we regroup the global
system to `(A ⊗ B) ⊗ C` through the **associator** `QSystem.assoc A B C` (a system isomorphism
`QSystem.Iso`) transported with `State.congr`; Alice's measurement is then lifted to the
joint system by `Measurement.onLeft C` (acting on `A ⊗ B`, identity on Bob's `C`). This regrouping
is intrinsic to teleportation: Alice's region `{1,2}` and the resource's region `{2,3}` *overlap* on
system 2, so no single tensor bracketing makes both `ρ ⊗ σ` and Alice's operator clean tensor
factors — the associator carries exactly that overlap.

### Alice's operation: a genuine *set of quantum operations* (no single-Kraus restriction)

N&C's "measurement described by a set of quantum operations `Eₘ`" is, in full generality, a family
`Eₘ(ρ) = Σₖ Eₘₖ ρ Eₘₖ†` (each `Eₘ` a completely-positive, possibly multi-Kraus quantum operation)
with the collective completeness `Σₘₖ Eₘₖ† Eₘₖ = I` (a *quantum instrument*). We model **exactly
this general object**, using a standard equivalence: *a set of quantum operations is a single-Kraus
measurement on a refined outcome set, followed by classical coarse-graining.* Concretely Alice's
family is

* a **fine measurement** `m : Measurement κ (A ⊗ B)` — a family of Kraus operators `Mₖ` with
  `Σₖ Mₖ† Mₖ = I` (a `Measurement`, single-Kraus per *fine* outcome `k`), and
* a **coarse-graining** `g : κ → ι` — the classical result `m ∈ ι` reported for fine outcome `k`.

The outcome-`i` quantum operation is then the fibre-sum `Êᵢ(ρ) = Σ_{k : g k = i} Mₖ ρ Mₖ†` over the
fibre `g⁻¹(i)`. This is a faithful bijection (up to refinement) with N&C's general instruments:
given `{Eₘ}`, take `κ = {(m,k)}`, `M_{(m,k)} = Eₘₖ` and `g(m,k) = m`; conversely every `(m, g)`
gives a valid set of quantum operations. There is **no** dimension, rank, or single-Kraus
restriction — the fibres are arbitrary finite sets, so each `Eᵢ` has arbitrarily many Kraus
operators. (The special case `κ = ι`, `g = id` recovers a projective/Bell measurement, the
standard-protocol instantiation.)

## The formalisation

* `teleportationJointState ρ σ` — the global initial state `ρ ⊗ σ`, regrouped to `(A ⊗ B) ⊗ C` via
  the associator, ready for Alice's measurement of the first pair.
* `teleportationFineProb m σ ρ k` — the Born probability of a **fine** outcome `k`, `p(k)`.
* `teleportationFineInducedState m σ ρ k` — the (normalised) final state of system 3 for a fine
  outcome `k` (the single-Kraus building block `Mₖ · Mₖ†`'s output); the marginal on `C` of the
  post-measurement joint state when `k` is possible, and an inert placeholder otherwise (an
  impossible fine outcome carries weight `0` in the mixture below and so never contributes).
* `teleportationProb m g σ ρ i` — the **induced outcome probability** `p(i) = tr[Êᵢ(ρ)]`: the Born
  probability of the *coarse-grained* lifted measurement `(m.onLeft C).coarseGrain g`, equal to the
  fibre-sum `Σ_{k : g k = i} p(k)` of the fine probabilities.
* `teleportationInducedState m g σ ρ i hp : State C` — **the induced operation `Êᵢ`'s normalised
  output**, `Êᵢ(ρ) / tr[Êᵢ(ρ)]`: the state of system 3 Bob holds after Alice's coarse outcome `i`.
  It is the probabilistic **mixture** `State.mix`, over the fibre `g⁻¹(i)`, of the fine induced
  states weighted by the conditional probabilities `p(k) / p(i)` — precisely the normalised
  fibre-sum `Σ_{k : g k = i} p(k) (MₖρMₖ†/p(k))-marginal / p(i)`. The map
  `ρ ↦ teleportationInducedState m g σ ρ i hp` is the induced operation `Êᵢ` of the problem, and is
  the object to which N&C's recovery `Rᵢ` is applied in (8.189).
* `teleportationProb_sum_eq_one` — the family `{Êᵢ}` is collectively **trace-preserving**:
  `Σᵢ tr[Êᵢ(ρ)] = 1`. This is the Born normalisation for the coarse-grained lifted measurement, and
  records that Alice's instrument induces a *complete* family of operations (system 1 → system 3).
* `teleportationProb_nonneg`, `teleportationProb_le_one` — each induced probability lies in `[0,1]`.

The **recovery block** (second half, eq. 8.189):

* `teleportationRecovery e ω U τ : State A` — **Bob's recovery `Rᵢ` applied to `τ`**, a general
  trace-preserving quantum operation on system 3 given in Stinespring/environment form: attach a
  private ancilla `D` in a state `ω`, evolve `C ⊗ D` by a unitary `U : Evolution (C ⊗ D)`, discard
  the ancilla (`reducedLeft`), and relabel the result to system 1 through the physical
  identification `e : A ≃ₛ C` of the two qubits.
* `TeleportationRecovers e m g σ i : Prop` — **the reversibility criterion (8.189)**: for outcome
  `i`, Bob has a *fixed* recovery `(D, ω, U)` (chosen knowing only `i`) reversing `Êᵢ` for every
  input, `Rᵢ(Êᵢ(ρ) / tr[Êᵢ(ρ)]) = ρ`.
* `teleportationInducedState_injective_of_recovers` — **the headline consequence**: if outcome `i`
  is recoverable, the (normalised) induced operation `ρ ↦ Êᵢ(ρ) / tr[Êᵢ(ρ)]` is injective — Bob's
  final state pins down Alice's original `ρ`, the precise sense in which teleportation is
  *accomplished*.

## Design notes

* **Why the general instrument via fine measurement + coarse-graining (and why it is not a
  weakening).** Modelling Alice's family as a *single* `Measurement ι (A ⊗ B)` — one Kraus operator
  per classical outcome — would specialise N&C's "set of quantum operations" to the single-Kraus
  case, a genuine narrowing (a multi-Kraus `Eᵢ` sends a pure input to a *mixed* output, which one
  Kraus operator cannot). We avoid that specialisation: `(m : Measurement κ (A ⊗ B), g : κ → ι)`
  ranges over **all** sets of quantum operations, exactly. The induced probabilities are read off
  the coarse-graining `Measurement.coarseGrain` (whose Born rule `coarseGrain_bornProb` *is* the
  fibre-sum `p(i) = Σ_{g k = i} p(k)`), and the induced state is the mixture `State.mix`.
* **Why the normalised-state framing.** N&C's (8.189) applies `Rᵢ` to the
  *normalised* object `Êᵢ(ρ) / tr[Êᵢ(ρ)]`, a genuine density operator — a `State`. Modelling the
  induced operation through its normalised output lets the whole first half be stated with
  `State` and `Measurement`: `postMeasurement` (Postulate 4), `reducedRight` (§2.4.3 marginal),
  `State.mix` (mixtures), `Measurement.coarseGrain` (grouped Born rule), `State.congr` /
  `QSystem.assoc` (system-isomorphism transport) and `bornProb` (Postulate 3). The *unnormalised*
  `Êᵢ(ρ)` and the abstract statement that `Êᵢ` is completely positive / trace-non-increasing are not
  needed to state either half here — the induced output is already a genuine `State` (positive,
  trace one), which certifies `Êᵢ`'s output, and `teleportationProb_sum_eq_one` certifies the family
  is trace-preserving.
* **Why the Stinespring dilation for `Rᵢ` (and why it is general).**
  Equation (8.189) quantifies over a general *trace-preserving quantum operation* `Rᵢ`. Besides the
  unitary `Evolution.evolve`, a general channel is obtained, without any new object, by the
  **environment/Stinespring form** `Rᵢ(τ) = discardₐₙ𝒸ᵢₗₗₐ(U (τ ⊗ ω) U†)` — the shape N&C use for
  quantum operations (eq. 8.6) and the convention of Exercise 8.3. *Every* trace-preserving quantum
  operation arises this way, so existentially quantifying over `(D, ω, U)` in
  `TeleportationRecovers` is faithful to "there exists a trace-preserving quantum operation `Rᵢ`" —
  it does not narrow `Rᵢ` to a unitary (the ancilla `D` supplies the full generality). Compare the
  operator-sum representation of Theorem 8.1.
  `teleportationRecovery` is trace-preserving *by construction* (it maps `State`s to `State`s).
* **Generality.** The resource `σ` is an *arbitrary* `State (B ⊗ C)`, Alice's family `(m, g)` is
  an *arbitrary* set of quantum operations (multi-Kraus, arbitrary fibres), and Bob's recovery `Rᵢ`
  ranges over *all* trace-preserving quantum operations (via the dilation): nothing is specialised
  to a maximally entangled pair, a projective measurement, a single-Kraus operation, or a unitary
  recovery. `teleportationProb_sum_eq_one` is the exact trace-preserving content, not a surrogate.
* **The reversibility theorem, and what it does not claim.** `TeleportationRecovers` is N&C's
  success *criterion*; `teleportationInducedState_injective_of_recovers` extracts its one
  non-trivial mathematical consequence (recoverability forces the induced operation to preserve all
  information about `ρ`). Whether a *given* imperfect resource `σ` admits a recovery is a separate,
  resource-dependent question (perfect teleportation — a maximally entangled `σ` with a Bell
  measurement, where `Rᵢ` is a Pauli unitary — is the standard-protocol content of
  `AxQM/Postulates/API/Teleportation.lean`); this file states the general criterion and its
  consequence, not an existence claim for a particular `σ`.
-/

noncomputable section

namespace AxQM

universe uD

variable {A B C : QSystem} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- **The regrouped global initial state** of Problem 8.2: the product `ρ ⊗ σ` of the input state
`ρ` of system 1 with the (imperfect) resource state `σ` on systems 2⊗3, transported from the natural
grouping `A ⊗ (B ⊗ C)` to `(A ⊗ B) ⊗ C` via the associator `QSystem.assoc A B C`, so that Alice's
pair (systems 1,2 = `A ⊗ B`) is a single tensor factor available for measurement. -/
def teleportationJointState (ρ : State A) (σ : State (B ⊗ C)) : State ((A ⊗ B) ⊗ C) :=
  State.congr (QSystem.assoc A B C) (ρ ⊗ σ)

/-- **The fine-outcome probability** `p(k)`: the Born probability of a fine Kraus outcome `k` of
Alice's instrument `m : Measurement κ (A ⊗ B)`, lifted to the joint system by `Measurement.onLeft C`
(identity on Bob's system 3) and evaluated on the regrouped joint state. The induced (coarse)
probability `teleportationProb` is the fibre-sum of these over `g⁻¹(i)`. -/
def teleportationFineProb (m : Measurement κ (A ⊗ B)) (σ : State (B ⊗ C)) (ρ : State A)
    (k : κ) : ℝ :=
  (m.onLeft C).bornProb (teleportationJointState ρ σ) k

/-- **The induced outcome probability** `p(i) = tr[Êᵢ(ρ)]` (N&C 8.189): the Born probability that
Alice reports classical result `i`, i.e. the Born probability of the *coarse-grained* lifted
measurement `(m.onLeft C).coarseGrain g` on the regrouped joint state. By `coarseGrain_bornProb`
this is the fibre-sum `Σ_{k : g k = i} p(k)` of the fine probabilities — the trace of the
(unnormalised) induced operation `Êᵢ(ρ) = Σ_{k : g k = i} Mₖ ρ Mₖ†`. -/
def teleportationProb (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C)) (ρ : State A)
    (i : ι) : ℝ :=
  ((m.onLeft C).coarseGrain g).bornProb (teleportationJointState ρ σ) i

/-- **The induced family `{Êᵢ}` is collectively trace-preserving:** the induced outcome
probabilities sum to one, `Σᵢ tr[Êᵢ(ρ)] = 1`. This is the Born-rule normalisation for the
coarse-grained lifted measurement `(m.onLeft C).coarseGrain g`, and records that Alice's instrument
induces a *complete* family of operations on the input–output pair (system 1 → system 3). -/
theorem teleportationProb_sum_eq_one (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C))
    (ρ : State A) : ∑ i, teleportationProb m g σ ρ i = 1 :=
  ((m.onLeft C).coarseGrain g).sum_bornProb_eq_one (teleportationJointState ρ σ)

/-- Each induced outcome probability is non-negative. -/
theorem teleportationProb_nonneg (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C))
    (ρ : State A) (i : ι) : 0 ≤ teleportationProb m g σ ρ i :=
  ((m.onLeft C).coarseGrain g).bornProb_nonneg (teleportationJointState ρ σ) i

/-- Each induced outcome probability is at most one. -/
theorem teleportationProb_le_one (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C))
    (ρ : State A) (i : ι) : teleportationProb m g σ ρ i ≤ 1 :=
  ((m.onLeft C).coarseGrain g).bornProb_le_one (teleportationJointState ρ σ) i

/-- **The fine-outcome induced state** — the single-Kraus building block of `Êᵢ`. For a *possible*
fine outcome `k` (`p(k) ≠ 0`) it is the normalised final state of system 3, the marginal on `C`
(tracing out Alice's `A ⊗ B`) of the post-measurement joint state `(m.onLeft C).postMeasurement …`,
i.e. `(Mₖ ρ Mₖ† / p(k))`'s system-3 marginal. For an *impossible* fine outcome (`p(k) = 0`) it is an
inert placeholder (`σ`'s system-3 marginal): such `k` carries conditional weight `0` in the mixture
`teleportationInducedState` and so never contributes to the induced operation. -/
def teleportationFineInducedState (m : Measurement κ (A ⊗ B)) (σ : State (B ⊗ C)) (ρ : State A)
    (k : κ) : State C := by
  classical
  exact if hk : teleportationFineProb m σ ρ k = 0 then σ.reducedRight
    else ((m.onLeft C).postMeasurement (teleportationJointState ρ σ) k hk).reducedRight

/-- **The induced operation `Êᵢ`, as its normalised output** (N&C Problem 8.2, eq. 8.189): the final
state of system 3 (Bob's) after Alice measures systems 1,2 with her instrument and reports classical
result `i` (`hp : p(i) ≠ 0`), namely `Êᵢ(ρ) / tr[Êᵢ(ρ)]`.

It is the probabilistic **mixture**, over the fibre `g⁻¹(i)`, of the fine induced states
`teleportationFineInducedState` weighted by the conditional probabilities `p(k) / p(i)` — precisely
the normalised fibre-sum `(Σ_{k : g k = i} p(k)·(system-3 marginal of MₖρMₖ†/p(k))) / p(i)`, the
state Bob holds and to which N&C's recovery `Rᵢ` is applied in (8.189). The map
`ρ ↦ teleportationInducedState m g σ ρ i hp` is the induced operation `Êᵢ` relating the initial
state of system 1 to the final state of system 3. -/
def teleportationInducedState (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C))
    (ρ : State A) (i : ι) (hp : teleportationProb m g σ ρ i ≠ 0) : State C :=
  State.mix
    (fun k => if g k = i then teleportationFineProb m σ ρ k / teleportationProb m g σ ρ i else 0)
    (fun k => by
      split_ifs with hk
      · exact div_nonneg ((m.onLeft C).bornProb_nonneg _ k) (teleportationProb_nonneg m g σ ρ i)
      · exact le_refl 0)
    (by
      have h := (m.onLeft C).coarseGrain_bornProb g (teleportationJointState ρ σ) i
      simp only [teleportationProb, teleportationFineProb]
      rw [← Finset.sum_filter, ← Finset.sum_div, ← h]
      exact div_self hp)
    (fun k => teleportationFineInducedState m σ ρ k)

/-- **Bob's recovery operation `Rᵢ`, applied to a state of system 3** (N&C Problem 8.2, eq. 8.189).
A general trace-preserving quantum operation on Bob's system 3 (`C`) is realised in the
**environment/Stinespring form** (the shape N&C use for quantum operations, eq. 8.6, and the
library's channel convention, cf. Exercise 8.3): attach a private ancilla `D` prepared in a state
`ω`, evolve the pair `C ⊗ D` by a unitary `U`, and discard the ancilla (`reducedLeft`, keeping `C`).
The resulting state of system 3 is relabelled to system 1 (`A`) through the physical identification
`e : A ≃ₛ C` of the two single-qubit systems, so that it can be compared with the input `ρ : State
A`. Every trace-preserving quantum operation arises this way, so quantifying over `(D, ω, U)` is
exactly quantifying over N&C's trace-preserving quantum operation `Rᵢ`. The output is a genuine
`State` (trace one), so `Rᵢ` is trace-preserving by construction. -/
def teleportationRecovery (e : A ≃ₛ C) {D : QSystem.{uD}} (ω : State D) (U : Evolution (C ⊗ D))
    (τ : State C) : State A :=
  ((U.evolve (τ ⊗ ω)).reducedLeft).congr e.symm

/-- **The reversibility criterion for Alice's outcome `i`** — Nielsen & Chuang, Problem 8.2, eq.
(8.189). *Teleportation is accomplished* for outcome `i` when Bob possesses a **fixed**
trace-preserving quantum operation `Rᵢ` — a Stinespring dilation `(D, ω, U)`, applied by
`teleportationRecovery` — that reverses the induced operation `Êᵢ`, recovering the input state of
system 1 from the normalised final state of system 3, `Rᵢ(Êᵢ(ρ) / tr[Êᵢ(ρ)]) = ρ`, for *every*
input `ρ` capable of producing outcome `i`. The recovery is chosen once for the outcome
(existentially quantified *outside* the `∀ ρ`), reflecting that Bob applies it knowing only the
classical result `i`, never Alice's unknown `ρ`. -/
def TeleportationRecovers (e : A ≃ₛ C) (m : Measurement κ (A ⊗ B)) (g : κ → ι) (σ : State (B ⊗ C))
    (i : ι) : Prop :=
  ∃ (D : QSystem.{uD}) (ω : State D) (U : Evolution (C ⊗ D)),
    ∀ (ρ : State A) (hp : teleportationProb m g σ ρ i ≠ 0),
      teleportationRecovery e ω U (teleportationInducedState m g σ ρ i hp) = ρ

/-- **Teleportation success forces the induced operation to be injective on inputs** (N&C Problem
8.2). If Bob can reverse `Êᵢ` for outcome `i` (`TeleportationRecovers`), then distinct inputs `ρ`
produce distinct normalised final states of system 3: the induced map
`ρ ↦ Êᵢ(ρ) / tr[Êᵢ(ρ)]` is injective (on inputs able to yield outcome `i`). This is the precise
sense in which *teleportation is accomplished* — Bob's final state determines Alice's original `ρ`
uniquely, so no information about `ρ` is lost in transit. The proof is immediate: the fixed recovery
`Rᵢ` is a left inverse of the normalised induced operation, and a map with a left inverse is
injective. -/
theorem teleportationInducedState_injective_of_recovers (e : A ≃ₛ C) (m : Measurement κ (A ⊗ B))
    (g : κ → ι) (σ : State (B ⊗ C)) (i : ι) (h : TeleportationRecovers e m g σ i) {ρ₁ ρ₂ : State A}
    (hp₁ : teleportationProb m g σ ρ₁ i ≠ 0) (hp₂ : teleportationProb m g σ ρ₂ i ≠ 0)
    (hτ : teleportationInducedState m g σ ρ₁ i hp₁ = teleportationInducedState m g σ ρ₂ i hp₂) :
    ρ₁ = ρ₂ := by
  obtain ⟨D, ω, U, hrec⟩ := h
  calc ρ₁ = teleportationRecovery e ω U (teleportationInducedState m g σ ρ₁ i hp₁) :=
        (hrec ρ₁ hp₁).symm
    _ = teleportationRecovery e ω U (teleportationInducedState m g σ ρ₂ i hp₂) := by rw [hτ]
    _ = ρ₂ := hrec ρ₂ hp₂

end AxQM
