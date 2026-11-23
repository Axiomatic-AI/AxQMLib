/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.CoherentInformation
import AxQM.NC.Ch12.Exercise12_15
import AxQM.NC.Ch2.Exercise2_78
import AxQM.NC.Ch2.Exercise2_80
import AxQM.Postulates.API.ReducedStateComm
import AxQM.Postulates.API.CompositeReducedEvolution
import AxQM.Postulates.API.CompositeStateEvolution
import AxQM.Postulates.API.SystemIsoCongrTmul
import AxQM.Postulates.API.MiddleFactorMarginal
import AxQM.Postulates.API.MutualInformationEvolution
import AxQM.Postulates.API.LeftCommMarginal
import AxQM.Postulates.API.ReducedStateTransport
import AxQM.Postulates.API.Interchange
import AxQM.Postulates.API.InterchangeMarginal
import AxQM.Postulates.API.SchmidtReducedSpectrum
import AxQM.Postulates.API.SameNonzeroSpectrumTmul
import AxQM.Postulates.API.LeftPairGate
import ToMathlib.Analysis.InnerProductSpace.TensorProductNoCommDriving

/-!
# N&C Exercise 12.22 — Entanglement conversion without communication (the model)

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 12.22, p. 577.

Entanglement conversion without communication possible iff lambda_psi ~= lambda_phi tensor x.

This file is the **complete formalisation** of the exercise: the **operational model** (the
predicate the iff is stated over, together with the local-channel infrastructure it needs), both
directions of the iff — **sufficiency (`⟸`)** (`PureState.convertibleNoComm_of_sameNonzeroSpectrum`)
and **necessity (`⟹`)** (`PureState.ConvertibleNoComm.exists_sameNonzeroSpectrum_tmul`) — and the
**biconditional** assembling them
(`PureState.convertibleNoComm_iff_exists_sameNonzeroSpectrum_tmul`).
Throughout, `λ_ψ` is realised as the spectrum of the reduced state `ρ_ψ = ψ.reducedLeft`, whose
`≅` relation `State.SameNonzeroSpectrum` (identical non-zero eigenvalues) is defined
in `AxQM/Postulates/API/SameNonzeroSpectrum.lean`, and the probability vector `x` as the
eigenvalue spectrum of some ancilla state `τ` (a density operator, so `x` is non-negative and sums
to one).

## Alice's local channel

`State.dilatedChannelOnRight` (`AxQM/NC/Ch11/Theorem11_15.lean`) is Nielsen & Chuang's Chapter-8
dilation of a trace-preserving quantum operation on the *right* factor `B` of `A ⊗ B` — Bob's
side. Its mirror on the *left* factor `A` — Alice's side — is `State.dilatedChannelOnLeft`,
defined here by conjugating
`dilatedChannelOnRight` with the swap `A ⊗ B ≃ B ⊗ A` (`QSystem.Iso.comm`): swap the factors, run
the channel on the (now right-hand) `A` factor, swap back. Its two marginal laws — *Alice's channel
acts on Alice's marginal and leaves Bob's untouched* — are
`State.reducedLeft_dilatedChannelOnLeft` / `State.reducedRight_dilatedChannelOnLeft`, read off the
`dilatedChannelOnRight` laws by pushing the swap through the marginals
(`State.reducedLeft_congr_comm`, `State.reducedRight_congr_comm`, which exchange the two reduced
states under `QSystem.Iso.comm`).

## The predicate

`PureState.ConvertibleNoComm ψ φ`: `ψ` can be converted to `φ` by local operations without classical
communication. Following the accepted design decision, each party's local operation is modelled in
Stinespring / isometric-dilation form — the representation N&C's own solution uses and the one the
library already provides via `State.dilatedChannel*`:

`ψ →_LO φ  :=  ∃ CA CB (UA : Evolution (A ⊗ CA)) (UB : Evolution (B ⊗ CB)) (ωA : PureState CA)`
`              (ωB : PureState CB), φ = (ψ.dilatedChannelOnRight UB ωB).dilatedChannelOnLeft UA ωA`.

This is faithful: Stinespring says every trace-preserving quantum operation has this dilation form,
and a unitary followed by a fixed pure ancilla and a partial trace is deterministic — matching
"convert `|ψ⟩` **into** `|φ⟩`". It captures the genuinely bipartite "no communication" constraint
because Alice's dilation `(UA, ωA)` and Bob's `(UB, ωB)` act on disjoint factors with no cross-talk
(neither party's operation is conditioned on the other's outcome). As documented for
`LOCCConvertible` under Theorem 12.15, the informal "local operations" quantifier is expressed
through dilations, not through a general tensor-product-of-CPTP-maps type (the library does not
provide one).

## Main definitions

* `State.dilatedChannelOnLeft` — Alice's dilated quantum operation on the left factor.
* `State.dilatedChannelNoComm` — the two-sided no-communication channel (Bob's dilation on the
  right factor followed by Alice's on the left), the operation `ConvertibleNoComm` is phrased over.
* `PureState.ConvertibleNoComm` — convertibility by local operations without communication.

## Main statements

* `State.reducedLeft_dilatedChannelOnLeft` — Alice's channel acts on Alice's marginal.
* `State.reducedRight_dilatedChannelOnLeft` — Alice's channel preserves Bob's marginal.
* `State.reducedLeft_dilatedChannelNoComm` / `State.reducedRight_dilatedChannelNoComm` — under a
  no-communication conversion the two parties' marginals decouple, each undergoing only its own
  local channel (`ρ_A ↦ E_A(ρ_A)`, `ρ_B ↦ E_B(ρ_B)`). The `⟹`-direction (necessity) ingredient.
* `State.dilatedChannelOnRight_eq_dilatedChannel` / `State.dilatedChannelOnLeft_eq_dilatedChannel` —
  each two-sided dilated channel is a single-system `State.dilatedChannel` of the *whole* bipartite
  system, driven by the local unitary lifted (and, for Alice, swapped) onto `(A ⊗ B) ⊗ Cᵢ`.
* `State.dilatedChannelNoComm_eq_dilatedChannelComp` — the no-communication channel is the
  sequential composite (`State.dilatedChannelComp`, Exercise 12.15) of those two single-system
  dilations. The
  first reduction step of the `⟸`-direction (sufficiency), toward evaluating `dilatedChannelNoComm`
  on a pure input as a single joint dilation.
* `State.dilatedChannelComp_eq_reducedRight_reducedLeft` — the sequential composite of two
  single-system dilations (`State.dilatedChannelComp`, Exercise 12.15) rewritten as a **single joint
  evolution with both environments deferred**: apply the second unitary `U₂` on the surviving system
  (with the first environment held idle), then trace out *both* environments at the end. This is the
  next reduction step: on a pure input the whole right-hand side is a pure joint state whose
  double-trace is the channel output, so `dilatedChannelNoComm` on a pure state becomes a single
  purification-style calculation.
* `State.dilatedChannelComp_eq_dilatedChannel` — the sequential composite of two single-system
  dilations collapsed into **one** single-system `State.dilatedChannel` over the product ancilla
  `ω₁ ⊗ ω₂`, driven by the two unitaries lifted onto `Q ⊗ (C ⊗ D)` (the second with the first
  environment as an idle middle factor). The single-dilation form of the two-stage process: the
  channel-composition companion of `dilatedChannelComp_eq_reducedRight_reducedLeft`, built on the
  left-commutation marginal law `State.reducedLeft_congr_leftComm`.
* `State.dilatedChannel_congr_ancilla` — a single-system dilated channel is invariant under
  relabelling its environment by a unitary `g : C ≃ₛ C'` (conjugate the driving unitary by `I_Q ⊗ g`
  and transport the ancilla by `g`). The environment relabelling commutes past the evolution and
  disappears in the discard. The ancilla-order bookkeeping tool for the final sufficiency reduction:
  it reconciles the `CB ⊗ CA` ancilla ordering produced by `dilatedChannelComp_eq_dilatedChannel`
  with the `CA ⊗ CB` ordering the product-unitary (interchange) form of `dilatedChannelNoComm`
  reads.
* `Evolution.noComm_driving_eq` — the composite driving unitary equals the interchange-transported
  **product** `UA ⊗ UB` (reordered to the `CB ⊗ CA` ancilla), for *arbitrary* local unitaries. The
  general-operator linchpin: it transports the bilinear-lift identity
  `TensorProduct.noComm_driving_raw_eq` through the definitional `.toIsometry` bridges.
* `State.dilatedChannelNoComm_eq_dilatedChannel` — a no-communication conversion is a **single**
  joint dilation `State.dilatedChannel` of `A ⊗ B` driven by the interchange-transported product
  `UA ⊗ UB`, with product ancilla `ωA ⊗ ωB`. The completed `⟸`-direction (sufficiency) reduction:
  on a pure input the whole output is a marginal of one purification.
* `PureState.convertibleNoComm_of_sameNonzeroSpectrum` — the **sufficiency (`⟸`) direction** of
  Exercise 12.22: if `ρ_ψ ≅ ρ_φ ⊗ τ` for some ancilla state `τ` (i.e. `λ_ψ ≅ λ_φ ⊗ x` with
  `x = λ_τ` a probability vector), then `ψ.ConvertibleNoComm φ`. Builds a purification `χ` of `τ`,
  regroups the joint states across the parties∣ancillas vs Alice∣Bob cuts through the interchange
  braid (`QSystem.Iso.interchange_symm`), matches their Schmidt coefficients via the
  reduced-spectrum bridge, invokes Nielsen & Chuang Exercise 2.80 for the local unitaries, and
  closes with the sufficiency hook.
* `PureState.ConvertibleNoComm.exists_sameNonzeroSpectrum_tmul` — the **necessity (`⟹`) direction**
  of Exercise 12.22: if `ψ.ConvertibleNoComm φ`, then `ρ_ψ ≅ ρ_φ ⊗ τ` for some ancilla state `τ`
  (i.e. `λ_ψ ≅ λ_φ ⊗ x`). Runs the sufficiency reduction in reverse: on a pure input the joint state
  is a single dilation (`State.dilatedChannelNoComm_eq_dilatedChannel`); its pure `A ⊗ B` marginal
  `|φ⟩⟨φ|` forces it to factor as `|φ⟩ ⊗ |χ⟩` (`PureState.isProduct_iff_isPure_reducedLeft`); and
  its Alice-cut marginal, computed both through that product form (`= ρ_φ ⊗ τ`) and through the
  product-unitary form (`≅ ρ_ψ`, by `State.sameNonzeroSpectrum_evolve_tmul_pure_right`), equates the
  two spectra. The witness `τ = χ.reducedLeft`.
* `PureState.convertibleNoComm_iff_exists_sameNonzeroSpectrum_tmul` — the **biconditional** of
  Exercise 12.22, assembling necessity and sufficiency:
  `ψ.ConvertibleNoComm φ ↔ ∃ τ, ρ_ψ ≅ ρ_φ ⊗ τ`.
  The headline claim of the exercise ("conversion without communication is possible iff
  `λ_ψ ≅ λ_φ ⊗ x`"). Ancilla systems are taken in universe `0` (WLOG for finite dimensions).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **Alice's dilated quantum operation on the left factor `A`.** For a bipartite state `ρ` on
`A ⊗ B`, a unitary `U` on `A ⊗ C`, and an ancilla `C` prepared in the pure state `ω`, this is the
state on `A ⊗ B` obtained by applying Nielsen & Chuang's Chapter-8 dilation of a channel `E` on `A`
to the left factor — the left-factor mirror of `State.dilatedChannelOnRight`. It is defined by
conjugating `dilatedChannelOnRight` with the swap `A ⊗ B ≃ B ⊗ A` (`QSystem.Iso.comm`): swap the two
factors, dilate the channel on the (now right-hand) `A` factor, then swap back. It realises
`(E ⊗ id_B) ρ` with `E(·) = Tr_C (U (· ⊗ |ω⟩⟨ω|) U†)`. -/
noncomputable def State.dilatedChannelOnLeft (ρ : State (A ⊗ B)) (U : Evolution (A ⊗ C))
    (ω : PureState C) : State (A ⊗ B) :=
  State.congr (QSystem.Iso.comm B A)
    ((State.congr (QSystem.Iso.comm A B) ρ).dilatedChannelOnRight U ω)

/-- **A quantum operation on the left factor acts on the left marginal.** For a bipartite state `ρ`
on `A ⊗ B` and a channel `E` on `A` presented by its dilation `(U, ω)`, tracing out `B` from
`(E ⊗ id_B) ρ = ρ.dilatedChannelOnLeft U ω` gives `E` applied to the `A`-marginal of `ρ`:
`Tr_B((E ⊗ id_B) ρ) = E(Tr_B ρ) = (Tr_B ρ).dilatedChannel U ω`. Read off the `dilatedChannelOnRight`
law by exchanging the two reduced states across the swap (`State.reducedRight_congr_comm`,
`State.reducedLeft_congr_comm`). -/
theorem State.reducedLeft_dilatedChannelOnLeft (ρ : State (A ⊗ B)) (U : Evolution (A ⊗ C))
    (ω : PureState C) :
    (ρ.dilatedChannelOnLeft U ω).reducedLeft = ρ.reducedLeft.dilatedChannel U ω := by
  unfold State.dilatedChannelOnLeft
  rw [← State.reducedRight_congr_comm, State.reducedRight_dilatedChannelOnRight,
    ← State.reducedLeft_congr_comm]

/-- **A quantum operation on the left factor leaves the right marginal unchanged.** For a bipartite
state `ρ` on `A ⊗ B` and a channel `E` on `A` presented by its dilation `(U, ω)`, tracing out `A`
from `(E ⊗ id_B) ρ = ρ.dilatedChannelOnLeft U ω` gives the same `B`-marginal as tracing out `A` from
`ρ`: `Tr_A((E ⊗ id_B) ρ) = Tr_A ρ`. Read off the `dilatedChannelOnRight` law by exchanging the two
reduced states across the swap (`State.reducedLeft_congr_comm`, `State.reducedRight_congr_comm`). -/
theorem State.reducedRight_dilatedChannelOnLeft (ρ : State (A ⊗ B)) (U : Evolution (A ⊗ C))
    (ω : PureState C) : (ρ.dilatedChannelOnLeft U ω).reducedRight = ρ.reducedRight := by
  unfold State.dilatedChannelOnLeft
  rw [← State.reducedLeft_congr_comm, State.reducedLeft_dilatedChannelOnRight,
    ← State.reducedRight_congr_comm]

variable {CA CB : QSystem}

/-- **The two-sided no-communication dilated channel.** For a bipartite state `ρ` on `A ⊗ B`,
Alice's dilation `(UA, ωA)` on `A ⊗ CA` and Bob's dilation `(UB, ωB)` on `B ⊗ CB`, this is the state
on `A ⊗ B` obtained by running Bob's local dilated channel on the right factor and *then* Alice's on
the left factor — the two parties acting independently, with no operation conditioned on the other's
(the "no communication" constraint). It is exactly the state that `PureState.ConvertibleNoComm`
requires `ψ` to be carried into: `ψ.ConvertibleNoComm φ` says `φ.toState` is
`ψ.toState.dilatedChannelNoComm UA UB ωA ωB` for some dilations. Because the two dilations act on
disjoint factors, the order in which they are applied is immaterial and each party's marginal
undergoes only its own channel (`State.reducedLeft_dilatedChannelNoComm` /
`State.reducedRight_dilatedChannelNoComm`). -/
noncomputable def State.dilatedChannelNoComm (ρ : State (A ⊗ B)) (UA : Evolution (A ⊗ CA))
    (UB : Evolution (B ⊗ CB)) (ωA : PureState CA) (ωB : PureState CB) : State (A ⊗ B) :=
  (ρ.dilatedChannelOnRight UB ωB).dilatedChannelOnLeft UA ωA

/-- **Alice's marginal after a no-communication conversion undergoes only Alice's channel.** Tracing
out Bob's factor `B` from `ρ.dilatedChannelNoComm UA UB ωA ωB` gives Alice's channel `E_A` applied
to `ρ`'s `A`-marginal:

`(ρ.dilatedChannelNoComm UA UB ωA ωB).reducedLeft = (ρ.reducedLeft).dilatedChannel UA ωA`.

Bob's trace-preserving operation leaves the `A`-marginal untouched
(`State.reducedLeft_dilatedChannelOnRight`), and Alice's operation acts on it as the single-system
dilated channel `State.dilatedChannel` (`State.reducedLeft_dilatedChannelOnLeft`). This is the
`⟹`-direction ingredient of Exercise 12.22 (necessity): `ρ_φ = E_A(ρ_ψ)`. -/
theorem State.reducedLeft_dilatedChannelNoComm (ρ : State (A ⊗ B)) (UA : Evolution (A ⊗ CA))
    (UB : Evolution (B ⊗ CB)) (ωA : PureState CA) (ωB : PureState CB) :
    (ρ.dilatedChannelNoComm UA UB ωA ωB).reducedLeft = ρ.reducedLeft.dilatedChannel UA ωA := by
  rw [State.dilatedChannelNoComm, State.reducedLeft_dilatedChannelOnLeft,
    State.reducedLeft_dilatedChannelOnRight]

/-- **Bob's marginal after a no-communication conversion undergoes only Bob's channel.** Tracing out
Alice's factor `A` from `ρ.dilatedChannelNoComm UA UB ωA ωB` gives Bob's channel `E_B` applied to
`ρ`'s `B`-marginal:

`(ρ.dilatedChannelNoComm UA UB ωA ωB).reducedRight = (ρ.reducedRight).dilatedChannel UB ωB`.

Alice's operation, acting on the disjoint left factor, leaves the `B`-marginal untouched
(`State.reducedRight_dilatedChannelOnLeft`), and Bob's operation acts on it as the single-system
dilated channel `State.dilatedChannel` (`State.reducedRight_dilatedChannelOnRight`). The mirror of
`State.reducedLeft_dilatedChannelNoComm`, witnessing that the two parties' marginals decouple — the
formal content of "no communication". -/
theorem State.reducedRight_dilatedChannelNoComm (ρ : State (A ⊗ B)) (UA : Evolution (A ⊗ CA))
    (UB : Evolution (B ⊗ CB)) (ωA : PureState CA) (ωB : PureState CB) :
    (ρ.dilatedChannelNoComm UA UB ωA ωB).reducedRight = ρ.reducedRight.dilatedChannel UB ωB := by
  rw [State.dilatedChannelNoComm, State.reducedRight_dilatedChannelOnLeft,
    State.reducedRight_dilatedChannelOnRight]

/-- **A right-factor dilated channel is a single-system dilated channel on the whole bipartite
system.** For a bipartite state `ρ` on `A ⊗ B`, Bob's dilated operation on the right factor
`ρ.dilatedChannelOnRight U ω` is Nielsen & Chuang's single-system dilation `State.dilatedChannel`
of the whole system `A ⊗ B`, driven by the *lifted* unitary `(I_A ⊗ U)` re-associated onto
`(A ⊗ B) ⊗ C`:

`ρ.dilatedChannelOnRight U ω = ρ.dilatedChannel ((I_A ⊗ U).congr (assoc A B C)) ω`.

The two forms differ only in *where* the associator `A ⊗ (B ⊗ C) ≃ₛ (A ⊗ B) ⊗ C` is applied — inside
the dilation (the `dilatedChannelOnRight` definition) or absorbed into the driving unitary (the
`dilatedChannel` form) — so they agree by pushing the associator through the evolution
(`Evolution.congr_evolve_congr`) and cancelling the roundtrip (`State.congr_congr_symm`).
Re-expressing `dilatedChannelOnRight` this way lets the two-party no-communication channel be read
as a *composition of single dilations* (`State.dilatedChannelNoComm_eq_dilatedChannelComp`). -/
theorem State.dilatedChannelOnRight_eq_dilatedChannel (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C))
    (ω : PureState C) :
    ρ.dilatedChannelOnRight U ω =
      ρ.dilatedChannel ((Evolution.id (S := A)).tmul U |>.congr (QSystem.assoc A B C)) ω := by
  rw [State.dilatedChannelOnRight, State.dilatedChannel, ← Evolution.congr_evolve_congr,
    State.congr_congr_symm]

/-- **A left-factor dilated channel is a single-system dilated channel on the whole bipartite
system.** The left-factor mirror of `State.dilatedChannelOnRight_eq_dilatedChannel`: for a bipartite
state `ρ` on `A ⊗ B`, Alice's dilated operation on the left factor `ρ.dilatedChannelOnLeft U ω` is a
single-system dilation `State.dilatedChannel` of the whole system `A ⊗ B`, driven by the lifted
unitary that runs `(I_B ⊗ U)` on the swapped `(B ⊗ A) ⊗ C` and transports back by the factor swap
`QSystem.Iso.comm`:

`ρ.dilatedChannelOnLeft U ω = ρ.dilatedChannel (((I_B ⊗ U).congr assoc).congr (comm ⊗ id)) ω`.

`dilatedChannelOnLeft` is `dilatedChannelOnRight` conjugated by the swap `A ⊗ B ≃ₛ B ⊗ A`, so after
applying the right-factor form the outer swap is pulled through the partial trace
(`State.reducedLeft_congr_tmul_left`, which carries a unitary on the kept factor through the trace)
and absorbed into the driving unitary via `Evolution.congr_evolve_congr`; the leftover roundtrip of
swaps on the input collapses by `State.congr_tmul` and `QSystem.Iso.comm_symm`. -/
theorem State.dilatedChannelOnLeft_eq_dilatedChannel (ρ : State (A ⊗ B)) (U : Evolution (A ⊗ C))
    (ω : PureState C) :
    ρ.dilatedChannelOnLeft U ω =
      ρ.dilatedChannel
        (((Evolution.id (S := B)).tmul U |>.congr (QSystem.assoc B A C)).congr
          ((QSystem.Iso.comm B A).tmul (QSystem.Iso.refl C)))
        ω := by
  rw [State.dilatedChannelOnLeft, State.dilatedChannelOnRight_eq_dilatedChannel,
    State.dilatedChannel, State.dilatedChannel, ← State.reducedLeft_congr_tmul_left,
    ← Evolution.congr_evolve_congr, State.congr_tmul, State.congr_refl,
    ← QSystem.Iso.comm_symm, State.congr_symm_congr]

/-- **The no-communication channel is a composition of two single-system dilations.** Because
Alice's and Bob's local operations both act on the whole bipartite system `A ⊗ B` (as `E_A ⊗ id_B`
and
`id_A ⊗ E_B`), the two-sided no-communication channel `State.dilatedChannelNoComm` is exactly the
sequential composite `State.dilatedChannelComp` of the two operations, each presented as a
single-system `State.dilatedChannel` on `A ⊗ B`:

`ρ.dilatedChannelNoComm UA UB ωA ωB = ρ.dilatedChannelComp WB ωB WA ωA`,

where `WB = (I_A ⊗ UB).congr (assoc A B CB)` is Bob's lifted unitary
(`State.dilatedChannelOnRight_eq_dilatedChannel`) and
`WA = ((I_B ⊗ UA).congr (assoc B A CA)).congr (comm B A ⊗ id_CA)` is Alice's
(`State.dilatedChannelOnLeft_eq_dilatedChannel`). This connects the exercise's operational model to
the composite-dilation infrastructure of Exercise 12.15 (`State.dilatedChannelComp`), and is the
first reduction step toward evaluating `dilatedChannelNoComm` on a pure input via a single joint
dilation. -/
theorem State.dilatedChannelNoComm_eq_dilatedChannelComp (ρ : State (A ⊗ B))
    (UA : Evolution (A ⊗ CA)) (UB : Evolution (B ⊗ CB)) (ωA : PureState CA) (ωB : PureState CB) :
    ρ.dilatedChannelNoComm UA UB ωA ωB =
      ρ.dilatedChannelComp
        ((Evolution.id (S := A)).tmul UB |>.congr (QSystem.assoc A B CB)) ωB
        (((Evolution.id (S := B)).tmul UA |>.congr (QSystem.assoc B A CA)).congr
          ((QSystem.Iso.comm B A).tmul (QSystem.Iso.refl CA))) ωA := by
  rw [State.dilatedChannelNoComm, State.dilatedChannelOnLeft_eq_dilatedChannel,
    State.dilatedChannelOnRight_eq_dilatedChannel, State.dilatedChannelComp]

/-- **A composite of two single-system dilations is a single joint evolution with deferred
environment traces.** The sequential composite `State.dilatedChannelComp` (Nielsen & Chuang
Exercise 12.15) — first the dilation `(U₁, ω₁)` with environment `E`, then `(U₂, ω₂)` with
environment `F`, each discarding its environment immediately — equals the state obtained by

* forming the joint state after the first stage `U₁(ρ ⊗ |ω₁⟩⟨ω₁|)U₁†` on `Q ⊗ E` **without** tracing
  `E` yet, adjoining the second environment `|ω₂⟩⟨ω₂|` on `F`;
* running the second unitary `U₂` on the surviving system `Q ⊗ F` with `E` held idle
  (`(I_E ⊗ U₂)`, after the middle factor `E` is swapped to the front so `Q ⊗ F` is exposed);
* tracing out **both** environments only at the end (`Tr_E` then `Tr_F`, i.e.
  `reducedRight.reducedLeft`).

`ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂`
`  = Tr_E Tr_F ((I_E ⊗ U₂)(U₁(ρ⊗|ω₁⟩⟨ω₁|)U₁† ⊗ |ω₂⟩⟨ω₂|)(I_E ⊗ U₂)†)`.

Deferring the first environment's trace past the second unitary is legitimate because `U₂` acts only
on `Q ⊗ F` and leaves `E` untouched: the first environment's trace commutes through it
(`State.reducedRight_evolve_id_tmul`), and re-exposing the surviving system `Q` after the first
stage discarded `E` traces `E` from *between* `Q` and the adjoined `F`
(`State.reducedRight_congr_symm_assoc_comm_tmul`, the middle-factor marginal law). This is the
reduction the sufficiency direction needs: on a pure input `ρ = |ψ⟩⟨ψ|` the right-hand side is a
*single pure joint state* on `Q ⊗ (E ⊗ F)` traced down to `Q`, so evaluating `dilatedChannelNoComm`
(a `dilatedChannelComp` by `State.dilatedChannelNoComm_eq_dilatedChannelComp`) on a pure state
reduces to reading off a marginal of one purification. -/
theorem State.dilatedChannelComp_eq_reducedRight_reducedLeft {Q E F : QSystem} (ρ : State Q)
    (U₁ : Evolution (Q ⊗ E)) (ω₁ : PureState E) (U₂ : Evolution (Q ⊗ F)) (ω₂ : PureState F) :
    ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂ =
      (((Evolution.id (S := E)).tmul U₂).evolve
        (State.congr (QSystem.assoc E Q F).symm
          ((State.congr (QSystem.Iso.comm Q E) (U₁.evolve (ρ.tmul ω₁.toState))).tmul
            ω₂.toState))).reducedRight.reducedLeft := by
  rw [State.dilatedChannelComp, State.dilatedChannel, State.dilatedChannel,
    ← State.reducedRight_congr_symm_assoc_comm_tmul, State.reducedRight_evolve_id_tmul]

/-- **A composite of two single-system dilations is a single dilation over the product ancilla.**
Nielsen & Chuang's two-stage single-system process `State.dilatedChannelComp` (Exercise 12.15) —
first the dilation `(U₁, ω₁)` with environment `C`, discarding `C`, then `(U₂, ω₂)` with environment
`D`, discarding `D` — equals a *single* dilation `State.dilatedChannel` of `Q` with the **combined**
ancilla `ω₁ ⊗ ω₂` on `C ⊗ D`, driven by the composite unitary that runs the lifted `U₁` (on `Q ⊗ C`,
with `D` idle) and then the lifted `U₂` (on `Q ⊗ D`, with `C` idle):

`ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂ = ρ.dilatedChannel W (ω₁ ⊗ ω₂)`, where `W` composes the lifted
`(I_C ⊗ U₂).congr (leftComm C Q D)` after `(U₁ ⊗ I_D).congr (assoc Q C D).symm`.

`U₁.onLeft D = U₁ ⊗ I_D` is re-associated onto `Q ⊗ (C ⊗ D)` (`QSystem.assoc`), and `U₂.onRight C =
I_C ⊗ U₂` is transported so that `C` becomes the idle *middle* factor
(`QSystem.Iso.leftComm C Q D`). The proof defers the first environment's trace past the second
unitary — `U₂` acts only on `Q ⊗ D`, so tracing `C` commutes through it — reading the deferred trace
off with the left-commutation marginal law (`State.reducedLeft_congr_leftComm`,
`State.reducedRight_evolve_id_tmul`) and re-exposing the surviving system by the middle-factor law
(`State.reducedRight_congr_symm_assoc_comm_tmul`). Turning the sequential composite into one joint
dilation is the reduction toward evaluating `dilatedChannelNoComm` on a pure input as a single
purification marginal. -/
theorem State.dilatedChannelComp_eq_dilatedChannel {Q C D : QSystem} (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂ =
      ρ.dilatedChannel
        ((Evolution.congr (QSystem.Iso.leftComm C Q D) (U₂.onRight C)).comp
          (Evolution.congr (Q.assoc C D).symm (U₁.onLeft D)))
        (ω₁.tmul ω₂) := by
  rw [State.dilatedChannelComp, State.dilatedChannel, State.dilatedChannel, State.dilatedChannel,
    PureState.toState_tmul, Evolution.evolve_comp, ← State.congr_assoc_symm_tmul_tmul,
    Evolution.congr_evolve_congr, Evolution.onLeft, Evolution.tmul_evolve, Evolution.evolve_id]
  conv_rhs => rw [← State.congr_congr_symm (QSystem.Iso.leftComm C Q D)
      (State.congr (Q.assoc C D).symm ((U₁.evolve (ρ ⊗ ω₁.toState)).tmul ω₂.toState)),
    Evolution.congr_evolve_congr]
  rw [State.reducedLeft_congr_leftComm, Evolution.onRight, State.reducedRight_evolve_id_tmul,
    ← State.congr_trans, QSystem.Iso.assoc_symm_trans_leftComm_symm, State.congr_trans,
    State.congr_tmul, State.congr_refl, State.reducedRight_congr_symm_assoc_comm_tmul]

/-- **A single-system dilated channel is invariant under transporting its environment by a
unitary.** Conjugating the driving unitary by `I_Q ⊗ g` on the ancilla factor and transporting the
ancilla pure state by the same isomorphism `g : C ≃ₛ C'` leaves the channel output unchanged:

`ρ.dilatedChannel ((I_Q ⊗ g) U) (g ω) = ρ.dilatedChannel U ω`.

The relabelling `g` of the environment is invisible: it commutes past the evolution
(`Evolution.congr_evolve_congr`) and, acting only on the traced-out factor, disappears when the
environment is discarded (`State.reducedLeft_congr_tmul_refl`). Used to reconcile the two ancilla
orderings (`C ⊗ D` vs `D ⊗ C`) that arise when the no-communication composite is collapsed to a
single dilation. -/
theorem State.dilatedChannel_congr_ancilla {Q C C' : QSystem} (ρ : State Q)
    (U : Evolution (Q ⊗ C)) (ω : PureState C) (g : C.Iso C') :
    ρ.dilatedChannel (Evolution.congr ((QSystem.Iso.refl Q).tmul g) U) (PureState.congr g ω)
      = ρ.dilatedChannel U ω := by
  rw [State.dilatedChannel, State.dilatedChannel, PureState.congr_toState,
    ← State.congr_refl ρ, ← State.congr_tmul, Evolution.congr_evolve_congr,
    State.reducedLeft_congr_tmul_refl, State.congr_refl]

set_option maxHeartbeats 2000000 in
-- The final `exact` matches the raw lemma against the reduced `Evolution`-operator goal up
-- to the composite `QSystem.space` tensor-instance diamond, reconciled node-by-node over the large
-- reshaping expression, so the definitional check needs a generous heartbeat budget.
/-- **The no-communication composite driving unitary is the interchange-transported product.** The
composite driving unitary produced by collapsing the two sequential single-system dilations of a
no-communication conversion — Bob's on the right factor, then Alice's on the left, presented as one
`State.dilatedChannelComp` (`State.dilatedChannelComp_eq_dilatedChannel`) — equals the clean
**product** unitary `UA ⊗ UB` transported by the interchange braid
`(A ⊗ CA) ⊗ (B ⊗ CB) ≃ₛ (A ⊗ B) ⊗ (CA ⊗ CB)` (`QSystem.Iso.interchange`), reordered to the reversed
`CB ⊗ CA` ancilla by `(refl_{A⊗B}) ⊗ comm CA CB`:

`W_composite = conj_{refl ⊗ comm CA CB} (conj_{interchange A CA B CB} (UA ⊗ UB))`.

Holds for *arbitrary* local unitaries: both sides are `ℂ`-bilinear in `(UA.op, UB.op)`, so the
identity reduces to the product case on the spanning product operators. The bilinear lift is carried
out at the level of the underlying operators in `TensorProduct.noComm_driving_raw_eq` (where the
tensor-instance diamond of the composite `QSystem.space` is absent); this `Evolution` identity
transports it through the definitional `.toIsometry` bridges (`Evolution.congr_op` reduces the
equation to the operator identity, and each `QSystem.Iso` reshape's `.toIsometry` unfolds to the
matching isometry of the underlying spaces). It is the linchpin that turns `dilatedChannelNoComm`
on a pure input into a single joint dilation (`State.dilatedChannelNoComm_eq_dilatedChannel`). -/
theorem Evolution.noComm_driving_eq (UA : Evolution (A ⊗ CA)) (UB : Evolution (B ⊗ CB)) :
    (Evolution.congr (QSystem.Iso.leftComm CB (A ⊗ B) CA)
        (((((Evolution.id (S := B)).tmul UA).congr (QSystem.assoc B A CA)).congr
            ((QSystem.Iso.comm B A).tmul (QSystem.Iso.refl CA))).onRight CB)).comp
        (Evolution.congr ((A ⊗ B).assoc CB CA).symm
          (((Evolution.id (S := A)).tmul UB |>.congr (QSystem.assoc A B CB)).onLeft CA))
      = Evolution.congr ((QSystem.Iso.refl (A ⊗ B)).tmul (QSystem.Iso.comm CA CB))
          (Evolution.congr (QSystem.Iso.interchange A CA B CB) (UA.tmul UB)) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, Evolution.congr_op, Evolution.onLeft, Evolution.onRight,
    Evolution.tmul_op, Evolution.id_op, QSystem.Iso.leftComm, QSystem.Iso.trans_toIsometry,
    QSystem.assoc_toIsometry, QSystem.assoc_symm_toIsometry, QSystem.Iso.tmul_toIsometry,
    QSystem.Iso.comm_toIsometry, QSystem.Iso.refl_toIsometry, QSystem.Iso.interchange_toIsometry]
  exact TensorProduct.noComm_driving_raw_eq UA.op UB.op

/-- **A no-communication conversion is a single joint dilation by the interchange-transported
product unitary.** The completed sufficiency reduction of Exercise 12.22: for a bipartite `ρ` on
`A ⊗ B`, running Bob's and Alice's local dilated channels with no communication is a **single**
`State.dilatedChannel` of the whole system `A ⊗ B`, driven by the clean product unitary `UA ⊗ UB`
transported by the interchange braid `(A ⊗ CA) ⊗ (B ⊗ CB) ≃ₛ (A ⊗ B) ⊗ (CA ⊗ CB)`, with the combined
product ancilla `ωA ⊗ ωB`:

`ρ.dilatedChannelNoComm UA UB ωA ωB = ρ.dilatedChannel (conj_{interchange}(UA ⊗ UB)) (ωA ⊗ ωB)`.

Three reduction steps assemble it: the no-communication channel is a sequential composite of the two
single-system dilations (`State.dilatedChannelNoComm_eq_dilatedChannelComp`); that composite
collapses to one dilation over the reversed `CB ⊗ CA` ancilla
(`State.dilatedChannelComp_eq_dilatedChannel`);
its driving unitary is the interchange-transported product up to an ancilla swap
(`Evolution.noComm_driving_eq`), and that swap `refl ⊗ comm CA CB` is absorbed by transporting the
ancilla back to `CA ⊗ CB` (`State.dilatedChannel_congr_ancilla`, using the ancilla-swap
`PureState.congr_comm_tmul`). On a pure input this exhibits the whole
no-communication output as a marginal of one purification `conj_{interchange}(UA ⊗ UB)(|ψ⟩ ⊗ |ωA⟩ ⊗
|ωB⟩)`, the form the `⟸`-direction (sufficiency) of the exercise's iff evaluates.
* `PureState.convertibleNoComm_of_evolvePure_interchange` — the **sufficiency hook**: if the joint
  driving unitary `interchange · (UA ⊗ UB)` carries `|ψ⟩ ⊗ |ωA⟩ ⊗ |ωB⟩` into a product `|φ⟩ ⊗ |χ⟩`
  across the parties∣ancillas cut `A ⊗ B ∣ CA ⊗ CB`, then `ψ.ConvertibleNoComm φ`. Combining the
  single-dilation form (`State.dilatedChannelNoComm_eq_dilatedChannel`) with the product-marginal
  law (`State.reducedLeft_tmul`), it reduces the last rung of the `⟸`-direction to a spectral
  same-Schmidt-coefficients argument (via Exercise 2.80). -/
theorem State.dilatedChannelNoComm_eq_dilatedChannel (ρ : State (A ⊗ B)) (UA : Evolution (A ⊗ CA))
    (UB : Evolution (B ⊗ CB)) (ωA : PureState CA) (ωB : PureState CB) :
    ρ.dilatedChannelNoComm UA UB ωA ωB
      = ρ.dilatedChannel (Evolution.congr (QSystem.Iso.interchange A CA B CB) (UA.tmul UB))
          (ωA.tmul ωB) := by
  rw [State.dilatedChannelNoComm_eq_dilatedChannelComp, State.dilatedChannelComp_eq_dilatedChannel,
    Evolution.noComm_driving_eq, ← PureState.congr_comm_tmul ωA ωB,
    State.dilatedChannel_congr_ancilla]

universe uCA uCB

/-- **Entanglement conversion without classical communication.** `ψ.ConvertibleNoComm φ` holds when
Alice and Bob can convert the bipartite pure state `|ψ⟩` on `A ⊗ B` into `|φ⟩` using local
operations only — no classical communication (Nielsen & Chuang, Exercise 12.22). Each party's local
operation is modelled by its Stinespring / Chapter-8 dilation: Alice adjoins a pure ancilla `ωA` on
an ancilla system `CA`, applies a unitary `UA` on `A ⊗ CA`, and discards `CA`
(`State.dilatedChannelOnLeft`); Bob does likewise on his side with `(CB, UB, ωB)`
(`State.dilatedChannelOnRight`). The two dilations act on disjoint factors, capturing "no
communication": neither operation is conditioned on the other's result.

The ancilla systems `CA`, `CB` are quantified over their own universes (`QSystem.{uCA}`,
`QSystem.{uCB}`), matching the library's idiom for existentially adjoined systems — every universe
of finite-dimensional ancilla is allowed, so no generality is lost. -/
def PureState.ConvertibleNoComm {A B : QSystem} (ψ φ : PureState (A ⊗ B)) : Prop :=
  ∃ (CA : QSystem.{uCA}) (CB : QSystem.{uCB}) (UA : Evolution (A ⊗ CA)) (UB : Evolution (B ⊗ CB))
    (ωA : PureState CA) (ωB : PureState CB),
    φ.toState = ψ.toState.dilatedChannelNoComm UA UB ωA ωB

/-- **Sufficiency hook: a product-producing joint unitary gives a no-communication conversion.** If,
after adjoining Alice's and Bob's pure ancillas `ωA`, `ωB`, the single interchange-transported
product unitary `UA ⊗ UB` (the joint driving unitary of the no-communication channel, from
`State.dilatedChannelNoComm_eq_dilatedChannel`) carries `|ψ⟩ ⊗ |ωA⟩ ⊗ |ωB⟩` into a **product**
`|φ⟩ ⊗ |χ⟩` across the split `A ⊗ B ∣ CA ⊗ CB` — i.e.

`(interchange · (UA ⊗ UB)) |ψ, ωA, ωB⟩ = |φ⟩ ⊗ |χ⟩`  (an `evolvePure` equation)

— then `ψ.ConvertibleNoComm φ`: Alice `(CA, UA, ωA)` and Bob `(CB, UB, ωB)` convert `|ψ⟩` into `|φ⟩`
with no classical communication.

This is the final rung of the `⟸`-direction (sufficiency): it turns "the local unitaries produce a
state that factorises across the parties∣ancillas cut" into the `ConvertibleNoComm` predicate.
On a pure input the no-communication channel is one joint dilation
(`State.dilatedChannelNoComm_eq_dilatedChannel`), so `dilatedChannelNoComm` unfolds to the
`reducedLeft` of the pure joint state `(UA ⊗ UB)|ψ, ωA, ωB⟩`; the hypothesis makes that joint state
the pure product `|φ⟩ ⊗ |χ⟩`, whose left marginal is exactly `|φ⟩⟨φ|` (`State.reducedLeft_tmul`),
the environments `CA ⊗ CB` tracing away with `χ`. The bridge from the `evolvePure` (vector)
hypothesis to the `evolve` (density) marginal is `toState_evolvePure` / `PureState.toState_tmul`.

A caller supplies the hypothesis by producing `UA`, `UB`, `χ` from a same-Schmidt-coefficients
argument (Nielsen & Chuang, Exercise 2.80,
`PureState.exists_evolution_tmul_of_sameSchmidtCoeffs`) in the interchange frame — the remaining
sufficiency work, which is a purely spectral calculation once this hook is in place. -/
theorem PureState.convertibleNoComm_of_evolvePure_interchange.{uA, uB, uCA', uCB'}
    {A : QSystem.{uA}} {B : QSystem.{uB}} {CA : QSystem.{uCA'}} {CB : QSystem.{uCB'}}
    (ψ φ : PureState (A ⊗ B)) (UA : Evolution (A ⊗ CA)) (UB : Evolution (B ⊗ CB))
    (ωA : PureState CA) (ωB : PureState CB) (χ : PureState (CA ⊗ CB))
    (h : (Evolution.congr (QSystem.Iso.interchange A CA B CB) (UA.tmul UB)).evolvePure
          (ψ.tmul (ωA.tmul ωB)) = φ.tmul χ) :
    PureState.ConvertibleNoComm.{uCA', uCB', uA, uB} ψ φ := by
  refine ⟨CA, CB, UA, UB, ωA, ωB, ?_⟩
  rw [State.dilatedChannelNoComm_eq_dilatedChannel, State.dilatedChannel,
    ← PureState.toState_tmul, ← toState_evolvePure, h, PureState.toState_tmul,
    State.reducedLeft_tmul]

/-- **Sufficiency (`⟸`) of Nielsen & Chuang Exercise 12.22.** If the Schmidt-coefficient vector of
`ψ` matches that of `φ` *tensored with some probability vector* `x` — realised here as
`λ_ψ ≅ λ_φ ⊗ λ_τ`, i.e. `ρ_ψ ≅ ρ_φ ⊗ τ` for **some** ancilla state `τ` on a system `C` (whose
eigenvalues are `x`) — then Alice and Bob can convert `|ψ⟩` into `|φ⟩` by local operations with no
classical communication: `ψ.ConvertibleNoComm φ`.

The construction realises Nielsen & Chuang's solution. Alice takes ancilla `CA := C`, Bob takes
`CB := ` a copy of `C` (the purification ancilla of `τ`), and `χ := τ.purify` is a purification of
`τ` on `CA ⊗ CB` (so `Tr_{CB} χ = τ`, `State.purify_reducedLeft_eq`). Regroup the two candidate
joint pure states across the *parties∣ancillas* cut `A ⊗ B ∣ CA ⊗ CB` to the *Alice∣Bob* cut
`A ⊗ CA ∣ B ⊗ CB` via the interchange braid's inverse
(`QSystem.Iso.interchange_symm`, turning it into a forward braid so the product-marginal law
`State.reducedLeft_congr_interchange_tmul` applies):

* `Ψ := interchange⁻¹ (|ψ⟩ ⊗ |ωA⟩ ⊗ |ωB⟩)` has left marginal `ρ_ψ ⊗ |ωA⟩⟨ωA| ≅ ρ_ψ`
  (a pure ancilla is spectrum-free, `State.sameNonzeroSpectrum_tmul_pure_right`);
* `Φ' := interchange⁻¹ (|φ⟩ ⊗ |χ⟩)` has left marginal `ρ_φ ⊗ τ`.

The hypothesis `ρ_ψ ≅ ρ_φ ⊗ τ` therefore gives `ρ_A(Φ') ≅ ρ_A(Ψ)`, i.e. `Ψ` and `Φ'` have identical
Schmidt coefficients across the Alice∣Bob cut
(`PureState.sameSchmidtCoeffs_iff_sameNonzeroSpectrum_reducedLeft`). By Nielsen & Chuang
Exercise 2.80 (`PureState.exists_evolution_tmul_of_sameSchmidtCoeffs`) a **local product unitary**
`UA ⊗ UB` (Alice's `UA` on `A ⊗ CA`, Bob's `UB` on `B ⊗ CB`) carries `Ψ` to `Φ'`; transporting that
identity back through the interchange (`Evolution.congr_evolvePure_congr` and the transport
roundtrip `PureState.congr_congr_symm`) makes the joint driving unitary carry
`|ψ⟩ ⊗ |ωA⟩ ⊗ |ωB⟩` to the product `|φ⟩ ⊗ |χ⟩`, which is exactly the sufficiency hook
`PureState.convertibleNoComm_of_evolvePure_interchange`.

The ancilla input states `ωA`, `ωB` are *arbitrary* pure states (any pure state is spectrum-free, so
their choice does not affect the reduced spectra); they exist because a system carrying a state has
a nontrivial space (`State.nontrivial_space`), from which `PureState.normalize` produces a unit
vector. This is the `⟸`-direction of the exercise's iff; the `⟹`-direction (necessity) and the
biconditional assembly are proved below. -/
theorem PureState.convertibleNoComm_of_sameNonzeroSpectrum.{uA', uB', uC}
    {A : QSystem.{uA'}} {B : QSystem.{uB'}}
    (ψ φ : PureState (A ⊗ B)) {C : QSystem.{uC}} (τ : State C)
    (h : ψ.toState.reducedLeft.SameNonzeroSpectrum (φ.toState.reducedLeft.tmul τ)) :
    PureState.ConvertibleNoComm.{uC, 0, uA', uB'} ψ φ := by
  have : Nontrivial C.space := τ.nontrivial_space
  have : Nontrivial (QSystem.ofModel (EuclideanSpace ℂ (Fin C.dim))).space :=
    τ.purify.toState.reducedRight.nontrivial_space
  obtain ⟨vA, hvA⟩ := exists_ne (0 : C.space)
  obtain ⟨vB, hvB⟩ := exists_ne (0 : (QSystem.ofModel (EuclideanSpace ℂ (Fin C.dim))).space)
  set ωA : PureState C := PureState.normalize vA hvA
  set ωB : PureState (QSystem.ofModel (EuclideanSpace ℂ (Fin C.dim))) :=
    PureState.normalize vB hvB
  set χ : PureState (C ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin C.dim))) := τ.purify with hχ
  have key :
      (PureState.congr (QSystem.Iso.interchange A C B
          (QSystem.ofModel (EuclideanSpace ℂ (Fin C.dim)))).symm (φ.tmul χ)).SameSchmidtCoeffs
        (PureState.congr (QSystem.Iso.interchange A C B
          (QSystem.ofModel (EuclideanSpace ℂ (Fin C.dim)))).symm (ψ.tmul (ωA.tmul ωB))) := by
    rw [PureState.sameSchmidtCoeffs_iff_sameNonzeroSpectrum_reducedLeft]
    have e2 :
        (PureState.congr (QSystem.Iso.interchange A C B
            (QSystem.ofModel (EuclideanSpace ℂ (Fin C.dim)))).symm (φ.tmul χ)).toState.reducedLeft
          = φ.toState.reducedLeft.tmul τ := by
      rw [PureState.congr_toState, PureState.toState_tmul, QSystem.Iso.interchange_symm,
        State.reducedLeft_congr_interchange_tmul, hχ, State.purify_reducedLeft_eq]
    rw [PureState.reducedLeft_congr_interchange_symm_tmul_tmul, e2]
    exact h.symm.trans (State.sameNonzeroSpectrum_tmul_pure_right ψ.toState.reducedLeft ωA).symm
  obtain ⟨UA, UB, hUV⟩ := PureState.exists_evolution_tmul_of_sameSchmidtCoeffs key
  refine PureState.convertibleNoComm_of_evolvePure_interchange ψ φ UA UB ωA ωB χ ?_
  rw [← PureState.congr_congr_symm (QSystem.Iso.interchange A C B
      (QSystem.ofModel (EuclideanSpace ℂ (Fin C.dim)))) (ψ.tmul (ωA.tmul ωB)),
    Evolution.congr_evolvePure_congr, ← hUV, PureState.congr_congr_symm]

/-- **Necessity (`⟹`) of Nielsen & Chuang Exercise 12.22.** If Alice and Bob can convert the
bipartite pure state `|ψ⟩` on `A ⊗ B` into `|φ⟩` by local operations with no classical communication
(`ψ.ConvertibleNoComm φ`), then the Schmidt-coefficient vector of `ψ` equals that of `φ` tensored
with a probability vector: `λ_ψ ≅ λ_φ ⊗ x`, realised here as `ρ_ψ ≅ ρ_φ ⊗ τ` for **some** ancilla
state `τ` (whose eigenvalues are the probability vector `x`).

The witness `τ` is `Tr_{CB} χ = χ.reducedLeft`, the Alice-ancilla marginal of the residual pure
state `χ` produced below. The proof runs the sufficiency machinery in reverse:

* On a pure input the no-communication channel is a single joint dilation
  (`State.dilatedChannelNoComm_eq_dilatedChannel`): with `Ψ` the pure joint state
  `interchange · (UA ⊗ UB) |ψ, ωA, ωB⟩` on the parties∣ancillas cut `(A ⊗ B) ∣ (CA ⊗ CB)`, the
  conversion hypothesis says `ρ_φ = |φ⟩⟨φ|` is `Ψ`'s `A ⊗ B` marginal (`hred`).
* A pure state whose reduced marginal is pure is a product across that cut (Nielsen & Chuang
  Exercise 2.78, `PureState.isProduct_iff_isPure_reducedLeft`): `Ψ = a ⊗ χ` with `a` on `A ⊗ B` and
  `χ` on `CA ⊗ CB`, and `a`'s marginal is `φ` (`State.reducedLeft_tmul`, giving `ha`).
* Regroup `Ψ` to the Alice∣Bob cut `(A ⊗ CA) ∣ (B ⊗ CB)` through the interchange braid's inverse
  (`QSystem.Iso.interchange_symm`). Its Alice-side marginal is computed two ways: through the
  **product** form `a ⊗ χ` it is exactly `ρ_φ ⊗ τ` (`State.reducedLeft_congr_interchange_tmul`,
  giving the equality `hB`); through the **product-unitary** form `UA ⊗ UB` it is
  `UA (ρ_ψ ⊗ |ωA⟩⟨ωA|) UA†`, which keeps `ρ_ψ`'s non-zero spectrum (`State.reducedLeft_evolve_tmul`
  clears `UB`, `State.sameNonzeroSpectrum_evolve_tmul_pure_right` handles the unitary and the pure
  ancilla, giving `hA`).

Equating the two marginals gives `ρ_ψ ≅ ρ_φ ⊗ τ`. This is the `⟹`-direction of the exercise's iff;
the `⟸`-direction is `PureState.convertibleNoComm_of_sameNonzeroSpectrum`. -/
theorem PureState.ConvertibleNoComm.exists_sameNonzeroSpectrum_tmul.{uCA', uCB', uA', uB'}
    {A : QSystem.{uA'}} {B : QSystem.{uB'}} {ψ φ : PureState (A ⊗ B)}
    (h : PureState.ConvertibleNoComm.{uCA', uCB', uA', uB'} ψ φ) :
    ∃ (C : QSystem.{uCA'}) (τ : State C),
      ψ.toState.reducedLeft.SameNonzeroSpectrum (φ.toState.reducedLeft.tmul τ) := by
  obtain ⟨CA, CB, UA, UB, ωA, ωB, hφ⟩ := h
  set Ψ : PureState ((A ⊗ B) ⊗ (CA ⊗ CB)) :=
    (Evolution.congr (QSystem.Iso.interchange A CA B CB) (UA.tmul UB)).evolvePure
      (ψ.tmul (ωA.tmul ωB)) with hΨ
  -- `φ` is the `A ⊗ B` marginal of the pure joint state `Ψ` (single-dilation form of the channel).
  have hred : Ψ.toState.reducedLeft = φ.toState := by
    rw [hΨ, toState_evolvePure, PureState.toState_tmul, hφ,
      State.dilatedChannelNoComm_eq_dilatedChannel, State.dilatedChannel]
  -- A pure state with a pure marginal factors across the cut; the left factor's marginal is `ρ_φ`.
  obtain ⟨a, χ, haχ⟩ := (PureState.isProduct_iff_isPure_reducedLeft Ψ).mpr ⟨φ, hred⟩
  have ha : a.toState = φ.toState := by
    rw [← hred, haχ, PureState.toState_tmul, State.reducedLeft_tmul]
  refine ⟨CA, χ.toState.reducedLeft, ?_⟩
  -- Route B: on the Alice∣Bob cut, the product form makes the Alice marginal exactly `ρ_φ ⊗ τ`.
  have hB : (PureState.congr (QSystem.Iso.interchange A CA B CB).symm Ψ).toState.reducedLeft
      = φ.toState.reducedLeft.tmul χ.toState.reducedLeft := by
    rw [haχ, PureState.congr_toState, PureState.toState_tmul, QSystem.Iso.interchange_symm,
      State.reducedLeft_congr_interchange_tmul, ha]
  -- Route A: the same marginal, via the product-unitary form, keeps `ρ_ψ`'s non-zero spectrum.
  have hA : ((PureState.congr (QSystem.Iso.interchange A CA B CB).symm Ψ).toState.reducedLeft)
      |>.SameNonzeroSpectrum ψ.toState.reducedLeft := by
    rw [hΨ, Evolution.evolvePure_congr_symm, toState_evolvePure, State.reducedLeft_evolve_tmul,
      PureState.reducedLeft_congr_interchange_symm_tmul_tmul]
    exact State.sameNonzeroSpectrum_evolve_tmul_pure_right ψ.toState.reducedLeft UA ωA
  rw [← hB]
  exact hA.symm

/-- **Nielsen & Chuang Exercise 12.22 (the biconditional).** Alice and Bob can convert the bipartite
pure state `|ψ⟩` on `A ⊗ B` into `|φ⟩` by local operations with **no** classical communication if
and only if the Schmidt-coefficient vector of `ψ` equals that of `φ` tensored with a probability
vector:
`λ_ψ ≅ λ_φ ⊗ x`, realised as `ρ_ψ ≅ ρ_φ ⊗ τ` for some ancilla state `τ` (whose eigenvalues form the
probability vector `x`, non-negative and summing to one because `τ` is a density operator).

Assembles the exercise's two directions: necessity (`⟹`) is
`PureState.ConvertibleNoComm.exists_sameNonzeroSpectrum_tmul`, sufficiency (`⟸`) is
`PureState.convertibleNoComm_of_sameNonzeroSpectrum`.

The ancilla systems are taken in universe `0`. This is no loss of generality: every
finite-dimensional ancilla is isomorphic to one modelled on `EuclideanSpace ℂ (Fin n)` in universe
`0` (the library's idiom used throughout — e.g. Bob's ancilla in the sufficiency proof already lives
there), so pinning the ancilla universes fixes a representative without weakening the physical
claim. -/
theorem PureState.convertibleNoComm_iff_exists_sameNonzeroSpectrum_tmul.{uA, uB}
    {A : QSystem.{uA}} {B : QSystem.{uB}} (ψ φ : PureState (A ⊗ B)) :
    PureState.ConvertibleNoComm.{0, 0, uA, uB} ψ φ ↔
      ∃ (C : QSystem.{0}) (τ : State C),
        ψ.toState.reducedLeft.SameNonzeroSpectrum (φ.toState.reducedLeft.tmul τ) := by
  constructor
  · exact PureState.ConvertibleNoComm.exists_sameNonzeroSpectrum_tmul
  · rintro ⟨C, τ, hτ⟩
    exact ψ.convertibleNoComm_of_sameNonzeroSpectrum φ τ hτ

end AxQM
