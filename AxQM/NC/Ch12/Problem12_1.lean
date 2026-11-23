/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.HolevoChi
import AxQM.Core.MeasurementChannel
import AxQM.NC.Ch11.Theorem11_15
import AxQM.Postulates.API.PartialTraceReassoc
import AxQM.Postulates.API.ReducedStateComm
import AxQM.Postulates.API.HolevoMeasurementMarginal
import AxQM.Postulates.API.HolevoMeasurementDilation
import AxQM.Postulates.API.QuditMeasurement
import ToMathlib.Analysis.SpecialFunctions.JointEntropy

/-!
# N&C Problem 12.1 — an alternate proof of the Holevo bound

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Problem 12.1, p. 602.

The problem develops an alternate proof of the Holevo bound built entirely on the **monotonicity of
the Holevo χ quantity** `χ = S(ρ) − ∑ₓ pₓ S(ρₓ)` (eq. (12.208)). It has three parts:

1. **`χ_A ≤ χ_AB`** — for an ensemble of states on a bipartite system `A ⊗ B`, the χ of the
   `A`-marginal ensemble is at most the χ of the joint ensemble (χ cannot increase when a subsystem
   is traced out). N&C's hint is to introduce an index system correlated with the ensemble and apply
   strong subadditivity.
2. **`χ′ ≤ χ`** — the Holevo χ decreases under any quantum operation `E`.
3. The **apparatus construction**: for a POVM `{Eᵧ}` and an apparatus register `M`, the operation
   `E(ρ ⊗ |0⟩⟨0|) = ∑ᵧ √Eᵧ ρ √Eᵧ ⊗ |y⟩⟨y|` produces `χ_M = H(X : Y)`; combined with parts (1)–(2)
   this yields the Holevo bound `H(X : Y) ≤ S(ρ) − ∑ₓ pₓ S(ρₓ)` (eq. (12.212)).

The engine, supplied by `Core/HolevoChi.lean`, is that **χ is the quantum mutual
information of the classical–quantum state** `∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ`
(`State.holevoChi_eq_vonNeumannMutualInfo_holevoCQState`). Under that identification each
χ-monotonicity statement becomes a mutual-information monotonicity already proved in
`NC/Ch11/Theorem11_15.lean`.

## This file (Parts 1–3 and the assembled Holevo bound)

`State.holevoChi_reducedLeft_le` is **Part (1)**, `χ_A ≤ χ_AB` (eq. (12.209)). Its proof is exactly
N&C's hint made precise:

* the "index system correlated with `AB`" is the classical register `P` of the cq-state
  `holevoCQState`, so `χ_AB = S(P : A,B)` and `χ_A = S(P : A)` by the χ ↔ mutual-information bridge;
* discarding the subsystem `B` sends the tripartite cq-state on `P ⊗ (A ⊗ B)` to the bipartite
  cq-state on `P ⊗ A` of the `A`-marginal ensemble — this is the marginal-consistency lemma
  `State.holevoCQState_congr_assoc_reducedLeft`;
* strong subadditivity, in the form "discarding never increases mutual information"
  (`State.vonNeumannMutualInfo_le_of_discard'`, N&C Theorem 11.15(2), faithfulness-free so it
  applies to the rank-deficient cq-state), gives `S(P : A) ≤ S(P : A,B)`, i.e. `χ_A ≤ χ_AB`.

`State.holevoChi_dilatedChannel_le` is **Part (2)**, `χ′ ≤ χ` (eq. (12.210)): the Holevo χ of the
image ensemble `{pᵢ, E(ρᵢ)}` under a quantum operation `E` is at most the χ of `{pᵢ, ρᵢ}`. Following
N&C's own three-step argument (append the environment, evolve unitarily, discard it), the operation
is presented by its Chapter-8 **dilation** — `State.dilatedChannel ρ U ω = Tr_C (U (ρ ⊗ |ω⟩⟨ω|) U†)`
for a unitary `U` on `S ⊗ C` and a pure ancilla `ω` — exactly as N&C's Theorem 11.15(3) presents the
channel it feeds on (a general trace-preserving `E` has no Kraus/dilation form to quantify over in
the library's API). The three steps are each a χ-monotonicity/invariance already in the library:

* **discard the environment** `C`: `χ(E∘ρ) = χ_S ≤ χ_{S,C} = χ(U(ρ ⊗ ω)U†)` is Part (1)
  `State.holevoChi_reducedLeft_le` (`E(ρᵢ)` is the `S`-marginal `Tr_C` of `U(ρᵢ ⊗ ω)U†`);
* **the unitary interaction** leaves χ invariant, `χ(U(ρ ⊗ ω)U†) = χ(ρ ⊗ ω)`
  (`State.holevoChi_evolve`, from unitary invariance of the von Neumann entropy);
* **appending the pure environment** leaves χ invariant, `χ(ρ ⊗ ω) = χ(ρ)`
  (`State.holevoChi_tmul_pure_right`, since a pure ancilla adds `S(ω) = 0` entropy).

Chaining the three gives `χ(E∘ρ) ≤ χ(ρ)`. (This route reuses Part (1)
rather than the dilated-channel mutual-information bound
`vonNeumannMutualInfo_dilatedChannelOnRight_le` directly: it needs only the two clean
χ-invariance lemmas above plus Part (1), all already available.)

`State.holevoChi_measState_eq_mutualInfo` is **Part (3)**, the apparatus identity `χ_M = H(X:Y)`
(which N&C states with no equation number): Alice prepares `ρₓ` with probability `pₓ` (random
variable `X`) and Bob measures with a POVM `m` (outcome `Y`). N&C's apparatus operation
`E(ρ ⊗ |0⟩⟨0|) = ∑ᵧ √Eᵧ ρ √Eᵧ ⊗ |y⟩⟨y|` (eq. (12.211)) leaves the apparatus register `M` in the
marginal `Tr_S E(ρₓ ⊗ |0⟩⟨0|) = ∑ᵧ Tr(Eᵧ ρₓ) |y⟩⟨y|`, which
is exactly the measure-and-record outcome channel `m.measState ρₓ` (`Measurement.measState`, from
`Core/MeasurementChannel.lean`) — so the χ of the ensemble `{pₓ, m.measState ρₓ}` is stated
directly over `measState`, without reconstructing `E`. It equals the classical mutual information of
the joint distribution `p(x, y) = pₓ · Tr(Eᵧ ρₓ)`:

* each apparatus state is diagonal in the outcome basis, so its von Neumann entropy is the Shannon
  entropy of its Born distribution (`Measurement.vonNeumannEntropy_measState`); hence
  `χ_M = H(Y) − ∑ₓ pₓ H(Y | X = x)`;
* the χ-mixture is the outcome channel of the average state
  (`Measurement.measState_mix`), whose Born distribution is the average of the component
  distributions (`Measurement.bornProb_mix`);
* the classical conditional-joint identity `Real.mutualInfo_prod_conditional`
  (`H(X:Y) = H(Y) − H(Y|X)` for a joint `pₓ · q x y`) identifies `χ_M` with `H(X:Y)`.

The Holevo χ ↔ classical-mutual-information transcription mirrors, on the outcome register,
the bridge `State.holevoChi_eq_vonNeumannMutualInfo_holevoCQState` that drives Parts (1)–(2).

`State.holevoChi_measState_le` composes Parts (1)–(3) into the χ-monotonicity heart of the bound,
`χ(fun x => m.measState ρₓ) ≤ χ(ρ)` (Holevo χ decreases under a measurement). It reruns N&C's
apparatus argument on `𝓔` (`holevoMeasurementChannel`, Exercise 12.2): apply `𝓔` to `ρₓ ⊗ |0⟩`,
whose apparatus `M`-marginal `Tr_Q 𝓔(ρₓ ⊗ |0⟩⟨0|)` is the diagonal Born state
`holevoMeasurementChannel_reducedRight` — i.e. `m.measState ρₓ` up to the register reindexing
`quditFinCardIso` (`qudit r ≃ₛ qudit (Fintype.card (Fin r))`, since `measState` records in
`qudit (Fintype.card (Fin r))` but `𝓔` in `qudit r`); then discard `Q` (Part (1), `reducedRight`
form), invoke that `𝓔` is a dilation (`holevoMeasurementChannel_eq_reducedLeft_evolve`) and apply
Part (2), and strip the reset apparatus (`State.holevoChi_tmul_pure_right`).

`holevoBound_of_chi_monotone` is the **headline Holevo bound** `H(X:Y) ≤ S(ρ) − ∑ₓ pₓ S(ρₓ)`
(eq. (12.212)): Part (3) `State.holevoChi_measState_eq_mutualInfo` rewrites `H(X:Y)` as
`χ(fun x => m.measState ρₓ)`, which `State.holevoChi_measState_le` bounds by `χ(ρ) = S(ρ) − ∑ₓ pₓ
S(ρₓ)`. This is N&C's alternate route — χ monotonicity throughout, in place of the direct
relative-entropy / data-processing argument of Theorem 12.1.

## Dependencies

Part (1) uses the discard bound `State.vonNeumannMutualInfo_le_of_discard'`
(`AxQM/NC/Ch11/Theorem11_15.lean`), and Part (2) uses Part (1). The proof of the assembled bound
`holevoBound_of_chi_monotone` also uses the register-reindexing isomorphism `quditFinCardIso` and
the measurement apparatus `holevoMeasurementChannel` with its marginal and dilation bridges, both
in `AxQM/Postulates/API/`. -/

noncomputable section

namespace AxQM

variable {A B : QSystem} {ι : Type*} [Fintype ι]
  (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State (A ⊗ B))

/-- **Discarding a subsystem sends the joint cq-state to the marginal cq-state.** For an ensemble
`{pᵢ, ρᵢ}` of states on `A ⊗ B`, re-associating the classical–quantum state
`∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ` on `P ⊗ (A ⊗ B)` to `(P ⊗ A) ⊗ B` and tracing out `B` yields the
classical–quantum state `∑ᵢ pᵢ |i⟩⟨i| ⊗ (ρᵢ)_A` of the `A`-marginal ensemble `{pᵢ, (ρᵢ)_A}`:

`Tr_B (assoc (holevoCQState p ρ)) = holevoCQState p (fun i => (ρ i)_A)`.

Both `State.congr`/`State.reducedLeft` are linear on mixtures (`State.congr_mix`,
`State.reducedLeft_mix`), reducing the claim to the per-component middle-marginal fact
`State.reducedLeft_congr_assoc_tmul`: the classical ket `|i⟩⟨i|` passes through the trace untouched
while `B` is traced off `ρᵢ`, leaving `|i⟩⟨i| ⊗ (ρᵢ)_A`. This is the structural heart of N&C's hint
(the "extra system correlated with `AB`" is the classical register `P`). -/
theorem State.holevoCQState_congr_assoc_reducedLeft :
    (State.congr (QSystem.assoc (qudit (Fintype.card ι)) A B)
          (State.holevoCQState p hp hsum ρ)).reducedLeft =
      State.holevoCQState p hp hsum (fun i => (ρ i).reducedLeft) := by
  unfold State.holevoCQState
  simp only [State.congr_mix, State.reducedLeft_mix, State.reducedLeft_congr_assoc_tmul]

/-- **N&C Problem 12.1(1): the Holevo χ quantity decreases under tracing out a subsystem**
(eq. (12.209)). For an ensemble `{pᵢ, ρᵢ}` of states on a bipartite system `A ⊗ B`,

`χ_A ≤ χ_AB`,

where `χ_A` is the Holevo χ of the `A`-marginal ensemble `{pᵢ, (ρᵢ)_A}` and `χ_AB` is the Holevo χ
of the joint ensemble `{pᵢ, ρᵢ}`.

The proof is N&C's hint made precise. By the χ ↔ mutual-information bridge
`State.holevoChi_eq_vonNeumannMutualInfo_holevoCQState`, `χ_AB = S(P : A,B)` for the
classical–quantum state on `P ⊗ (A ⊗ B)`, and `χ_A = S(P : A)` for its `A`-marginal cq-state, which
`State.holevoCQState_congr_assoc_reducedLeft` identifies with the discarded marginal. Strong
subadditivity in the form "discarding never increases mutual information"
(`State.vonNeumannMutualInfo_le_of_discard'`, N&C Theorem 11.15(2)) then gives
`S(P : A) ≤ S(P : A,B)`. -/
theorem State.holevoChi_reducedLeft_le :
    State.holevoChi p hp hsum (fun i => (ρ i).reducedLeft) ≤ State.holevoChi p hp hsum ρ := by
  rw [← State.holevoChi_eq_vonNeumannMutualInfo_holevoCQState p hp hsum
        (fun i => (ρ i).reducedLeft),
    ← State.holevoChi_eq_vonNeumannMutualInfo_holevoCQState p hp hsum ρ,
    ← State.holevoCQState_congr_assoc_reducedLeft p hp hsum ρ]
  exact State.vonNeumannMutualInfo_le_of_discard' (State.holevoCQState p hp hsum ρ)

/-- **The Holevo χ quantity decreases under tracing out the *left* subsystem**: the mirror of
Part (1) `State.holevoChi_reducedLeft_le` for the other factor. For an ensemble `{pᵢ, ρᵢ}` of states
on `A ⊗ B`,

`χ_B ≤ χ_AB`,

where `χ_B` is the Holevo χ of the `B`-marginal ensemble `{pᵢ, (ρᵢ)_B}` (`State.reducedRight`, which
traces out the *left* factor `A`). The apparatus step of the alternate Holevo-bound proof discards
the *measured system* `S` and keeps the *apparatus* register `M`, i.e. traces out the left factor;
this lemma supplies that direction. It reduces to Part (1) by the swap isomorphism: tracing out the
left factor is tracing out the right factor of the swapped state
(`State.reducedRight_congr_comm`), and χ is invariant under the swap transport
(`State.holevoChi_congr`). -/
theorem State.holevoChi_reducedRight_le :
    State.holevoChi p hp hsum (fun i => (ρ i).reducedRight) ≤ State.holevoChi p hp hsum ρ :=
  calc State.holevoChi p hp hsum (fun i => (ρ i).reducedRight)
      = State.holevoChi p hp hsum
          (fun i => (State.congr (QSystem.Iso.comm A B) (ρ i)).reducedLeft) := by
        simp only [State.reducedRight_congr_comm]
    _ ≤ State.holevoChi p hp hsum (fun i => State.congr (QSystem.Iso.comm A B) (ρ i)) :=
        State.holevoChi_reducedLeft_le p hp hsum
          (fun i => State.congr (QSystem.Iso.comm A B) (ρ i))
    _ = State.holevoChi p hp hsum ρ :=
        State.holevoChi_congr p hp hsum ρ (QSystem.Iso.comm A B)

/-- **The output of a dilated quantum operation on a single system.** For a state `ρ` on `S`, a
unitary `U` on `S ⊗ C`, and an environment `C` prepared in the pure state `ω`, this is Nielsen &
Chuang's Chapter-8 dilation `E(ρ) = Tr_C (U (ρ ⊗ |ω⟩⟨ω|) U†)` of a trace-preserving quantum
operation `E` on `S`: adjoin the pure ancilla (`ρ ⊗ |ω⟩⟨ω|`), evolve by `U`, then discard `C`
(trace out the right factor). Every trace-preserving quantum operation on `S` arises this way (the
environment/Stinespring representation, N&C §8.2.3). This is the single-system counterpart of
`State.dilatedChannelOnRight` (which dilates a channel acting on the right factor of a bipartite
state); presenting `E` by its dilation, rather than as an abstract trace-preserving map, is forced
by the library's API (no general Kraus/dilation-form theorem to quantify over) and matches N&C's own
argument. -/
noncomputable def State.dilatedChannel {S C : QSystem} (ρ : State S) (U : Evolution (S ⊗ C))
    (ω : PureState C) : State S :=
  (U.evolve (ρ.tmul ω.toState)).reducedLeft

/-- **N&C Problem 12.1(2): the Holevo χ quantity decreases under a quantum operation**
(eq. (12.210)).
For an ensemble `{pᵢ, ρᵢ}` of states on `S` and a trace-preserving quantum operation `E` on `S`,
presented by its Chapter-8 dilation (a unitary `U` on `S ⊗ C` with the environment `C` in a pure
state `ω`),

`χ′ = χ(E∘ρ) ≤ χ = χ(ρ)`,

where `χ(E∘ρ)` is the Holevo χ of the image ensemble `{pᵢ, E(ρᵢ)}`.

The proof is N&C's own argument (p. 601), reusing Part (1): `E(ρᵢ) = Tr_C (U (ρᵢ ⊗ ω) U†)` is the
`S`-marginal of `U (ρᵢ ⊗ ω) U†`, so discarding the environment gives
`χ(E∘ρ) ≤ χ(U(ρ ⊗ ω)U†)` by Part (1) `State.holevoChi_reducedLeft_le`; the unitary interaction
leaves χ invariant, `χ(U(ρ ⊗ ω)U†) = χ(ρ ⊗ ω)` (`State.holevoChi_evolve`); and the pure
environment adds no χ, `χ(ρ ⊗ ω) = χ(ρ)` (`State.holevoChi_tmul_pure_right`). -/
theorem State.holevoChi_dilatedChannel_le {S C : QSystem} {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (ρ : ι → State S)
    (U : Evolution (S ⊗ C)) (ω : PureState C) :
    State.holevoChi p hp hsum (fun i => (ρ i).dilatedChannel U ω)
      ≤ State.holevoChi p hp hsum ρ := by
  simp only [State.dilatedChannel]
  calc State.holevoChi p hp hsum (fun i => (U.evolve ((ρ i).tmul ω.toState)).reducedLeft)
      ≤ State.holevoChi p hp hsum (fun i => U.evolve ((ρ i).tmul ω.toState)) :=
        State.holevoChi_reducedLeft_le p hp hsum (fun i => U.evolve ((ρ i).tmul ω.toState))
    _ = State.holevoChi p hp hsum (fun i => (ρ i).tmul ω.toState) :=
        State.holevoChi_evolve p hp hsum (fun i => (ρ i).tmul ω.toState) U
    _ = State.holevoChi p hp hsum ρ :=
        State.holevoChi_tmul_pure_right p hp hsum ρ ω

/-- **N&C Problem 12.1(3): the Holevo χ quantity of the measurement apparatus equals the classical
mutual information** `H(X : Y)` (which N&C states with no equation number). Alice prepares the state
`ρₓ` with probability `pₓ` (`{pₓ, ρₓ}`, random variable `X`); Bob performs a POVM measurement `m`
with outcome `Y`. Under N&C's apparatus operation `E(ρ ⊗ |0⟩⟨0|) = ∑ᵧ √Eᵧ ρ √Eᵧ ⊗ |y⟩⟨y|`
(eq. (12.211)) the apparatus register `M`
ends in the marginal `Tr_S E(ρₓ ⊗ |0⟩⟨0|) = ∑ᵧ Tr(Eᵧ ρₓ) |y⟩⟨y|`, which is exactly the
measure-and-record outcome channel `m.measState ρₓ`. This theorem states that the Holevo χ of the
apparatus ensemble `{pₓ, m.measState ρₓ}` equals the classical mutual information of the joint
distribution `p(x, y) = pₓ · Tr(Eᵧ ρₓ) = pₓ · m.bornProb ρₓ y` of `X` and `Y`:

`χ_M = H(X : Y)`.

Proof: `S(m.measState ρ) = H(m.bornProb ρ)` (`Measurement.vonNeumannEntropy_measState`, each
apparatus state is diagonal in the outcome basis), and the χ-mixture is the outcome channel of the
average state (`Measurement.measState_mix`) whose Born distribution is the average of the components
(`Measurement.bornProb_mix`); so `χ_M = H(Y) − ∑ₓ pₓ H(Y|X=x)`, which the conditional-joint identity
`Real.mutualInfo_prod_conditional` identifies with `H(X:Y)`. Combined with Parts (1)–(2) this yields
the Holevo bound (assembled in `holevoBound_of_chi_monotone` below). -/
theorem State.holevoChi_measState_eq_mutualInfo {S : QSystem} {κ ι : Type*} [Fintype κ] [Fintype ι]
    (p : κ → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (ρ : κ → State S)
    (m : Measurement ι S) :
    State.holevoChi p hp hsum (fun x => m.measState (ρ x))
      = Real.mutualInfo (fun xy : κ × ι => p xy.1 * m.bornProb (ρ xy.1) xy.2) := by
  have hq : ∀ x, ∑ y, m.bornProb (ρ x) y = 1 := fun x => m.sum_bornProb_eq_one (ρ x)
  have hbar : m.bornProb (State.mix p hp hsum ρ) = fun y => ∑ x, p x * m.bornProb (ρ x) y := by
    funext y; exact m.bornProb_mix p hp hsum ρ y
  rw [State.holevoChi_def, ← Measurement.measState_mix m p hp hsum ρ]
  simp_rw [Measurement.vonNeumannEntropy_measState]
  rw [hbar, ← Real.mutualInfo_prod_conditional p (fun x => m.bornProb (ρ x)) hq]

section HolevoBound

variable {Q : QSystem} {r : ℕ} [NeZero r] {κ : Type*} [Fintype κ]
  (p : κ → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (ρ : κ → State Q)
  (m : Measurement (Fin r) Q)

/-- **N&C Problem 12.1: the Holevo χ quantity decreases under a measurement** — the composition of
Parts (1)–(3). For an ensemble `{pₓ, ρₓ}` of states on `Q` and a measurement `m` with `r` outcomes,
recording the outcome with the apparatus operation and discarding the measured system cannot
increase χ:

`χ(fun x => m.measState (ρ x)) ≤ χ(fun x => ρ x)`,

where `m.measState (ρ x) = ∑_y Tr(E_y ρ_x) |y⟩⟨y|` is the measure-and-record outcome state.

This is the (★) inequality of the alternate Holevo-bound proof, obtained by applying N&C's apparatus
operation `𝓔` (`holevoMeasurementChannel`, Exercise 12.2) to `ρ_x ⊗ |0⟩` and then following the four
χ-monotonicity/invariance steps:

* **(i)** `m.measState (ρ x)` is the transported apparatus `M`-marginal `Tr_Q 𝓔(ρ_x ⊗ |0⟩⟨0|)`
  (`holevoMeasurementChannel_reducedRight` gives the diagonal Born state; the register mismatch
  `qudit (Fintype.card (Fin r))` vs `qudit r` is bridged by `quditFinCardIso`, under which χ is
  invariant, `State.holevoChi_congr`);
* **(ii)** discarding the measured system `Q` cannot increase χ (Part (1) in its `reducedRight`
  form `State.holevoChi_reducedRight_le`);
* **(iii)** the apparatus operation `𝓔` is a dilated quantum operation
  (`holevoMeasurementChannel_eq_reducedLeft_evolve` presents it as
  `State.dilatedChannel`), under which χ cannot increase (Part (2)
  `State.holevoChi_dilatedChannel_le`);
* **(iv)** appending the reset apparatus `|0⟩` leaves χ unchanged
  (`State.holevoChi_tmul_pure_right`). -/
theorem State.holevoChi_measState_le :
    State.holevoChi p hp hsum (fun x => m.measState (ρ x))
      ≤ State.holevoChi p hp hsum ρ := by
  -- Step (i): each outcome state is the transported apparatus `M`-marginal of `𝓔(ρ_x ⊗ |0⟩⟨0|)`.
  have hstep1 : (fun x => m.measState (ρ x))
      = fun x => State.congr (quditFinCardIso r)
          ((holevoMeasurementChannel m ((ρ x).tmul (quditBasis (0 : Fin r)).toState)).reducedRight)
      := by
    funext x
    rw [Measurement.measState_def, holevoMeasurementChannel_reducedRight, State.congr_mix]
    simp only [quditFinCardIso_congr_toState]
  calc State.holevoChi p hp hsum (fun x => m.measState (ρ x))
      = State.holevoChi p hp hsum
          (fun x => State.congr (quditFinCardIso r)
            ((holevoMeasurementChannel m
                ((ρ x).tmul (quditBasis (0 : Fin r)).toState)).reducedRight))
          := by rw [hstep1]
    -- (i) χ is invariant under the register reindexing.
    _ = State.holevoChi p hp hsum
          (fun x =>
            (holevoMeasurementChannel m ((ρ x).tmul (quditBasis (0 : Fin r)).toState)).reducedRight)
          := State.holevoChi_congr p hp hsum _ (quditFinCardIso r)
    -- (ii) discarding the measured system `Q` cannot increase χ.
    _ ≤ State.holevoChi p hp hsum
          (fun x => holevoMeasurementChannel m ((ρ x).tmul (quditBasis (0 : Fin r)).toState))
          := State.holevoChi_reducedRight_le p hp hsum _
    -- (iii) `𝓔` is a dilated quantum operation, under which χ cannot increase.
    _ ≤ State.holevoChi p hp hsum
          (fun x => (ρ x).tmul (quditBasis (0 : Fin r)).toState) := by
        have hfam : (fun x => holevoMeasurementChannel m
              ((ρ x).tmul (quditBasis (0 : Fin r)).toState))
            = fun x => State.dilatedChannel ((ρ x).tmul (quditBasis (0 : Fin r)).toState)
                (measurementModelEvolution (quditOrthonormalBasis r)
                  (quditBasis (0 : Fin r)).normalized (holevoMeasurementKraus m)
                  (holevoMeasurementKraus_completeness m)) (quditBasis (0 : Fin r)) := by
          funext x
          exact holevoMeasurementChannel_eq_reducedLeft_evolve m
            ((ρ x).tmul (quditBasis (0 : Fin r)).toState)
        rw [hfam]
        exact State.holevoChi_dilatedChannel_le p hp hsum
          (fun x => (ρ x).tmul (quditBasis (0 : Fin r)).toState) _ (quditBasis (0 : Fin r))
    -- (iv) appending the reset apparatus leaves χ unchanged.
    _ = State.holevoChi p hp hsum ρ :=
        State.holevoChi_tmul_pure_right p hp hsum ρ (quditBasis (0 : Fin r))

/-- **N&C Problem 12.1: the Holevo bound** (eq. (12.212)), assembled from Parts (1)–(3) via the
monotonicity of the Holevo χ quantity — the alternate proof developed in this problem. Alice
prepares the state `ρₓ` with probability `pₓ` (random variable `X`); Bob measures with a POVM `m`
with `r` outcomes (random variable `Y`). Then the classical mutual information of the joint
distribution `p(x, y) = pₓ · Tr(Eᵧ ρₓ)` obeys

`H(X : Y) ≤ S(ρ) − ∑ₓ pₓ S(ρₓ)`,

the right-hand side being the Holevo χ quantity `χ = S(∑ₓ pₓ ρₓ) − ∑ₓ pₓ S(ρₓ)`
(`State.holevoChi`, `State.holevoChi_def`).

The proof combines the two ingredients of this file: Part (3)
`State.holevoChi_measState_eq_mutualInfo` rewrites `H(X : Y)` as the Holevo χ of the
measure-and-record ensemble `{pₓ, m.measState ρₓ}`, and `State.holevoChi_measState_le` — the
composition of Parts (1)–(2) with the apparatus construction — bounds that by the χ of the original
ensemble `{pₓ, ρₓ}`. This is N&C's alternate route to the Holevo bound, replacing the direct
relative-entropy / data-processing argument (Theorem 12.1) by χ monotonicity throughout. -/
theorem holevoBound_of_chi_monotone :
    Real.mutualInfo (fun xy : κ × Fin r => p xy.1 * m.bornProb (ρ xy.1) xy.2)
      ≤ State.holevoChi p hp hsum ρ := by
  rw [← State.holevoChi_measState_eq_mutualInfo p hp hsum ρ m]
  exact State.holevoChi_measState_le p hp hsum ρ m

end HolevoBound

end AxQM
