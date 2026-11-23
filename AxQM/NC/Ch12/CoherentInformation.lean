/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.Theorem11_15
import AxQM.NC.Ch11.TriangleInequality
import AxQM.NC.Ch12.Problem12_1
import AxQM.Core.ConditionalEntropy
import AxQM.Postulates.API.ReferencePurification
import AxQM.Postulates.API.ReducedStateTransport

/-!
# Entropy exchange and coherent information (N&C §12.4.1–12.4.2)

Definitions and lemmas for the quantum data processing inequality (N&C Theorem 12.10). Following
Nielsen & Chuang §12.4.1–12.4.2, a trace-preserving quantum operation `E` on a system `Q` is
presented by its Chapter-8 dilation — a unitary `U` on `Q ⊗ C` with the environment `C` prepared in
a pure state `ω`, so that `E(ρ) = Tr_C(U(ρ ⊗ |ω⟩⟨ω|)U†) = ρ.dilatedChannel U ω`.

## The `R'Q'` state and its marginals

Introduce a reference `R` and purify `ρ` into `|RQ⟩ = State.refPurify ρ` (reference on the left,
`State.refPurify`). Applying `E` to the system factor gives the state
`R'Q' = (refPurify ρ).dilatedChannelOnRight U ω` on `R ⊗ Q`. The two entropy-exchange definitions
rest on how tracing out one factor of a **channel acting on the right** behaves — proved here for a
*general* bipartite state, so the lemmas are reusable:

* `State.reducedLeft_dilatedChannelOnRight` — the left (untouched) marginal is unchanged,
  `Tr_B((id ⊗ E) ρ) = Tr_B ρ`;
* `State.reducedRight_dilatedChannelOnRight` — the right marginal is the channel applied to the
  right marginal, `Tr_A((id ⊗ E) ρ) = E(Tr_A ρ)`.

## The quantities (N&C eq. (12.107)/(12.118))

* `State.entropyExchange ρ U ω := S(R'Q')` — the **entropy exchange** `S(ρ, E)`, N&C's purification
  formulation `S(ρ, E) = S(R', Q')` (§12.4.1). This is the purification-side companion
  of Theorem 12.9's w-matrix quantity `ContinuousLinearMap.entropyExchange`
  (`S(ρ, E) = S(W)`); the two agree but this one exposes the `R'Q'` bipartite structure that the
  data processing inequality needs.
* `State.coherentInfo ρ U ω := S(E(ρ)) − S(ρ, E)` — the **coherent information** `I(ρ, E)`
  (eq. (12.118)).

## The purification reference

The purification reference is `State.refPurify` (in `AxQM/Postulates/API/`); it appears here only in
proof bodies, never in a statement.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {A B C Q : QSystem}

/-- **A quantum operation on the right factor leaves the left marginal unchanged.** For a bipartite
state `ρ` on `A ⊗ B` and a channel `E` on `B` presented by its dilation `(U, ω)`, tracing out `B`
from `(id_A ⊗ E) ρ = ρ.dilatedChannelOnRight U ω` gives the same `A`-marginal as tracing out `B`
from `ρ`: `Tr_B((id_A ⊗ E) ρ) = Tr_B ρ`. Read off the dilation by pushing `reducedLeft` through the
associator reshapes (`State.reducedLeft_reducedLeft_congr_assoc`,
`State.reducedLeft_congr_assoc_symm`), the local unitary `id ⊗ U`
(`State.reducedLeft_evolve_id_tmul`), and the pure ancilla (`State.reducedLeft_tmul`). -/
theorem State.reducedLeft_dilatedChannelOnRight (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C))
    (ω : PureState C) : (ρ.dilatedChannelOnRight U ω).reducedLeft = ρ.reducedLeft := by
  unfold State.dilatedChannelOnRight
  rw [State.reducedLeft_reducedLeft_congr_assoc, State.reducedLeft_evolve_id_tmul,
    State.reducedLeft_congr_assoc_symm, State.reducedLeft_tmul]

/-- **A quantum operation on the right factor acts on the right marginal.** For a bipartite state
`ρ` on `A ⊗ B` and a channel `E` on `B` presented by its dilation `(U, ω)`, tracing out `A` from
`(id_A ⊗ E) ρ = ρ.dilatedChannelOnRight U ω` gives `E` applied to the `B`-marginal of `ρ`:
`Tr_A((id_A ⊗ E) ρ) = E(Tr_A ρ) = (Tr_A ρ).dilatedChannel U ω`. This is the compatibility of the
partial trace with a local channel; read off the dilation by pushing `reducedRight` through the
associator reshape (`State.reducedRight_reducedLeft_congr_assoc`), the local unitary `id ⊗ U`
(`State.reducedRight_evolve_id_tmul`), and the ancilla adjunction
(`State.reducedRight_congr_symm_assoc_tmul`), landing on the single-system dilation
`State.dilatedChannel`. -/
theorem State.reducedRight_dilatedChannelOnRight (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C))
    (ω : PureState C) :
    (ρ.dilatedChannelOnRight U ω).reducedRight = ρ.reducedRight.dilatedChannel U ω := by
  unfold State.dilatedChannelOnRight State.dilatedChannel
  rw [State.reducedRight_reducedLeft_congr_assoc, State.reducedRight_evolve_id_tmul,
    State.reducedRight_congr_symm_assoc_tmul]

/-- **Entropy exchange** `S(ρ, E)` of a quantum operation `E` on `Q`, presented by its dilation
`(U, ω)` (Nielsen & Chuang §12.4.1, eq. (12.107)). Purify `ρ` into `R'Q' = R ⊗ Q` via
`State.refPurify` and apply `E` to the system factor; the entropy exchange is the von Neumann
entropy of the resulting joint state, `S(ρ, E) = S(R', Q')`. Equivalently (Theorem 12.9) this is
`S(W)` for the w-matrix `W_{ij} = tr(Eᵢ ρ Eⱼ†)`; the purification form is used here because the data
processing inequality argument reasons about the `R'Q'` bipartition directly. -/
def State.entropyExchange (ρ : State Q) (U : Evolution (Q ⊗ C)) (ω : PureState C) : ℝ :=
  ((State.refPurify ρ).toState.dilatedChannelOnRight U ω).vonNeumannEntropy

/-- **Coherent information** `I(ρ, E)` of a quantum operation `E` on `Q`, presented by its dilation
`(U, ω)` (Nielsen & Chuang §12.4.2, eq. (12.118)):

`I(ρ, E) = S(E(ρ)) − S(ρ, E)`,

the entropy of the output state `E(ρ) = ρ.dilatedChannel U ω` minus the entropy exchange
`State.entropyExchange`. It plays, in the quantum data processing inequality (Theorem 12.10), the
role the mutual information `H(X:Y)` plays classically. -/
def State.coherentInfo (ρ : State Q) (U : Evolution (Q ⊗ C)) (ω : PureState C) : ℝ :=
  (ρ.dilatedChannel U ω).vonNeumannEntropy - ρ.entropyExchange U ω

/-- **First inequality of the quantum data processing inequality** (Nielsen & Chuang Theorem 12.10,
eq. (12.119), first stage): the coherent information never exceeds the input entropy,

`I(ρ, E) ≤ S(ρ)`.

This is N&C's argument (12.122)–(12.126) cast in the purification picture. Writing
`σ = R'Q' = (refPurify ρ).dilatedChannelOnRight U ω` for the reference–system state after `E`, the
coherent information is `I(ρ, E) = S(Q') − S(R', Q')` since the output marginal is `E(ρ)`
(`State.reducedRight_dilatedChannelOnRight` + `State.refPurify_reducedRight`) and the joint entropy
is the entropy exchange (`State.entropyExchange`). The Araki–Lieb triangle inequality
`S(Q') − S(R') ≤ S(R', Q')` (`State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le`, N&C
eq. (11.79)) then bounds it by `S(R')`, and the reference marginal is isentropic with the input,
`S(R') = S(ρ)` (the channel leaves the `R`-marginal untouched,
`State.reducedLeft_dilatedChannelOnRight`, and `R` is a purifying reference,
`State.vonNeumannEntropy_refPurify_reducedLeft`). N&C note equality holds iff `E` is perfectly
reversible on `ρ` (Exercise 12.16). -/
theorem State.coherentInfo_le_vonNeumannEntropy (ρ : State Q) (U : Evolution (Q ⊗ C))
    (ω : PureState C) : ρ.coherentInfo U ω ≤ ρ.vonNeumannEntropy := by
  have hAL := State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le
    ((State.refPurify ρ).toState.dilatedChannelOnRight U ω)
  rw [State.reducedRight_dilatedChannelOnRight, State.refPurify_reducedRight,
    State.reducedLeft_dilatedChannelOnRight, State.vonNeumannEntropy_refPurify_reducedLeft] at hAL
  unfold State.coherentInfo State.entropyExchange
  linarith

/-!
## The data processing inequality (second stage): `I(ρ, E1) ≥ I(ρ, E2 ∘ E1)`

The second inequality of N&C Theorem 12.10 is the *quantum data processing inequality* proper. N&C
prove it (eqs (12.122)–(12.131)) with a four-system construction `R Q E1 E2` and the **strong
subadditivity** inequality. We recast that argument in the purification picture already set up for
the first inequality, so that the whole second stage becomes a monotonicity statement about the
**state coherent information** `I(A⟩B) = S(B) − S(A,B)` (`State.coherentInfoOfState`, the negative
conditional entropy, `AxQM/Core/ConditionalEntropy.lean`) under a channel acting on the `B`
factor. That monotonicity is a corollary: via the bridge `I(A⟩B) = S(A:B) − S(A)`
(`State.coherentInfoOfState_eq_vonNeumannMutualInfo_sub_reducedLeft`) and the channel-invariance of
the reference marginal `S(A)` (`State.reducedLeft_dilatedChannelOnRight`), it follows
from the mutual-information monotonicity
`State.vonNeumannMutualInfo_dilatedChannelOnRight_le` (N&C Theorem 11.15(3), which itself packages
N&C's SSA-discard / local-unitary / product-ancilla argument).

The key observations:

* The channel coherent information `I(ρ, E)` is the state quantity on the processed purification:
  it is `I(R'⟩Q')` for `R'Q' = (refPurify ρ).dilatedChannelOnRight U ω` (derived in the proof of
  `State.coherentInfoComp_le_coherentInfo`; cf. `State.entropyExchange`, which likewise uses
  `refPurify` only in its body).
* Applying `E2` to the system factor of `R'Q'` produces `R''Q''`, whose output marginal is
  `E2(E1(ρ)) = (E2 ∘ E1)(ρ)` (each right-factor dilation commutes with tracing out the reference,
  `State.reducedRight_dilatedChannelOnRight`, and the reference marginal of the purification is `ρ`,
  `State.refPurify_reducedRight`) and whose joint entropy is the entropy exchange `S(ρ, E2 ∘ E1)`
  (the purification formulation, N&C eq. (12.130) read through the purity of the global
  `R''Q''E1''E2''` state). Hence `I(R''⟩Q'') = S((E2 ∘ E1)(ρ)) − S(ρ, E2 ∘ E1) = I(ρ, E2 ∘ E1)`,
  captured by the definition `State.coherentInfoComp`.
* `State.coherentInfoOfState_dilatedChannelOnRight_le` is the monotonicity `I(A'⟩B') ≤ I(A⟩B)` under
  a channel on `B`; instantiated at `σ = R'Q'` it is exactly `I(ρ, E2 ∘ E1) ≤ I(ρ, E1)`.

This route sidesteps composing the two dilations into a single environment `Q ⊗ (C1 ⊗ C2)`:
sequential application on the right factor already realises `E2 ∘ E1` faithfully, and the
purification definition of the entropy exchange makes `S(ρ, E2 ∘ E1) = S(R''Q'')`
hold by construction.
-/

/-- **The state coherent information is non-increasing under a channel on the system factor** — the
state-level quantum data processing inequality. For a bipartite state `σ` on `A ⊗ B` and a
trace-preserving quantum operation `E` on `B`, presented by its Chapter-8 dilation (a unitary `U` on
`B ⊗ C` with the ancilla `C` in a pure state `ω`),

`I(A ⟩ E(B)) ≤ I(A⟩B)`,

where the processed state is `(id_A ⊗ E) σ = σ.dilatedChannelOnRight U ω`. This is a direct
corollary of the mutual-information monotonicity
`State.vonNeumannMutualInfo_dilatedChannelOnRight_le` (N&C Theorem 11.15(3), which packages
N&C's SSA-discard / local-unitary / product-ancilla dilation argument): via the bridge
`I(A⟩B) = S(A:B) − S(A)` (`State.coherentInfoOfState_eq_vonNeumannMutualInfo_sub_reducedLeft`), the
two coherent informations differ from their mutual informations by the *same* reference marginal
entropy `S(A)`, which the channel on `B` leaves untouched
(`State.reducedLeft_dilatedChannelOnRight`, `Tr_A((id_A ⊗ E) σ) = Tr_A σ`); so the
coherent-information inequality is the mutual-information one shifted by that common constant. -/
theorem State.coherentInfoOfState_dilatedChannelOnRight_le (σ : State (A ⊗ B))
    (U : Evolution (B ⊗ C)) (ω : PureState C) :
    (σ.dilatedChannelOnRight U ω).coherentInfoOfState ≤ σ.coherentInfoOfState := by
  have hmi := σ.vonNeumannMutualInfo_dilatedChannelOnRight_le U ω
  rw [State.coherentInfoOfState_eq_vonNeumannMutualInfo_sub_reducedLeft,
    State.coherentInfoOfState_eq_vonNeumannMutualInfo_sub_reducedLeft,
    State.reducedLeft_dilatedChannelOnRight]
  linarith

/-- **Coherent information of the two-stage composed operation** `I(ρ, E2 ∘ E1)` (Nielsen & Chuang
Theorem 12.10). The composed channel `E2 ∘ E1` — first `E1` (dilation `(U₁, ω₁)` on `Q ⊗ C₁`), then
`E2` (dilation `(U₂, ω₂)` on `Q ⊗ C₂`) — is realised faithfully by applying the two dilations in
sequence to the system factor of the reference purification of `ρ`, giving the reference–system
state `R''Q''`. The composed coherent information is the state coherent information of `R''Q''`:

`I(ρ, E2 ∘ E1) = I(R''⟩Q'') = S((E2 ∘ E1)(ρ)) − S(ρ, E2 ∘ E1)`.

The output marginal of `R''Q''` is `(E2 ∘ E1)(ρ)` (each right-factor dilation commutes with tracing
out the reference, `State.reducedRight_dilatedChannelOnRight`, and the reference marginal of the
purification is `ρ`, `State.refPurify_reducedRight`), and its joint entropy `S(R''Q'')` is the
entropy exchange `S(ρ, E2 ∘ E1)` — the purification formulation of N&C eq. (12.130), matching the
single-channel `State.entropyExchange`. Presenting the composition as sequential right-factor
dilations, rather than as one dilation on a combined environment `Q ⊗ (C₁ ⊗ C₂)`, avoids reshaping
across the joint environment while remaining faithful to N&C. -/
def State.coherentInfoComp (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : ℝ :=
  (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂
    ω₂).coherentInfoOfState

end AxQM
