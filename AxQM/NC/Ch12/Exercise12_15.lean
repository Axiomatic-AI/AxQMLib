/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.CoherentInformation
import AxQM.Postulates.API.ReducedStateLeftBlock

/-!
# N&C Exercise 12.15 — entropy inequalities for a two-stage quantum process

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 12.15, p. 568.

Derive all subadditivity/strong-subadditivity inequalities for two-stage process.

## The construction (N&C §12.4.1–12.4.2)

Each operation is presented by its Chapter-8 dilation — `E(ρ) = Tr_C(U(ρ ⊗ |ω⟩⟨ω|)U†) =
ρ.dilatedChannel U ω` for a unitary `U` on `Q ⊗ C` with the environment `C` in a pure state `ω`
(see `AxQM/NC/Ch12/CoherentInformation.lean`). Purifying `ρ` by a reference `R`
(`State.refPurify`) and applying the dilations in sequence to the system factor gives the
reference–system states after each stage,

* `σ₁ = R'Q' = (refPurify ρ).dilatedChannelOnRight U₁ ω₁`, and
* `σ₂ = R''Q'' = σ₁.dilatedChannelOnRight U₂ ω₂`,

whose marginals and joint entropies are the physical quantities of the process (all via the
§12.4 infrastructure, `State.reducedLeft_dilatedChannelOnRight`,
`State.reducedRight_dilatedChannelOnRight`, `State.refPurify_reducedRight`,
`State.vonNeumannEntropy_refPurify_reducedLeft`):

| quantity | meaning | as a state entropy |
| --- | --- | --- |
| `S(ρ)` | input entropy | `S(σ₁_R) = S(σ₂_R)` (the reference is untouched) |
| `S(ρ')` | intermediate output `S(E₁(ρ))` | `S(σ₁_Q)` |
| `S(ρ'')` | final output `S((E₂∘E₁)(ρ))` | `S(σ₂_Q)` |
| `S(ρ, E₁)` | entropy exchange of `E₁` (`State.entropyExchange`) | `S(σ₁)` |
| `S(ρ, E₂∘E₁)` | entropy exchange of the composite (`State.entropyExchangeComp`) | `S(σ₂)` |

The complete family of inequalities expressible in these quantities then falls out of subadditivity
`S(A,B) ≤ S(A) + S(B)` (`State.vonNeumannEntropy_le_reducedLeft_add_reducedRight`) and its lower
Araki–Lieb companion `|S(A) − S(B)| ≤ S(A,B)`
(`State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le` and its mirror) applied to `σ₁` and `σ₂`.

## Single-operation and composite inequalities

The **single-operation** inequalities — reusable at either stage — and the **composite** ones:

* `State.entropyExchange_le_vonNeumannEntropy_add_dilatedChannel` : `S(ρ, E) ≤ S(ρ) + S(E(ρ))`
  (subadditivity on `R'Q'`);
* `State.vonNeumannEntropy_le_dilatedChannel_add_entropyExchange` : `S(ρ) ≤ S(E(ρ)) + S(ρ, E)`, i.e.
  N&C eq. (12.144) `ΔS + S(ρ, E) ≥ 0` — the "second law" inequality highlighted just before the
  exercise (triangle on `R'Q'`);
* `State.entropyExchangeComp` — the **composite entropy exchange** `S(ρ, E₂∘E₁) = S(R''Q'')`, and
  `State.dilatedChannelComp` — the composite output `ρ'' = (E₂∘E₁)(ρ)`;
* `State.entropyExchangeComp_le_vonNeumannEntropy_add_dilatedChannelComp` : `S(ρ, E₂∘E₁) ≤ S(ρ) +
  S(ρ'')`;
* `State.vonNeumannEntropy_le_dilatedChannelComp_add_entropyExchangeComp` : `S(ρ) ≤ S(ρ'') +
  S(ρ, E₂∘E₁)` (composite eq. (12.144));
* `State.coherentInfoComp_le_vonNeumannEntropy` : `I(ρ, E₂∘E₁) ≤ S(ρ)` (composite first-stage data
  processing bound, from the triangle on `R''Q''`).

Two combinations are **already available** and cited rather than restated: the first-stage
data-processing bound `I(ρ, E₁) ≤ S(ρ)` (`State.coherentInfo_le_vonNeumannEntropy`) and the
strong-subadditivity data-processing inequality `I(ρ, E₂∘E₁) ≤ I(ρ, E₁)`
(`State.coherentInfoComp_le_coherentInfo`, N&C Theorem 12.10).

## Two-environment inequalities

The genuinely **two-environment** combinations — the triangle inequalities relating all *three*
entropy exchanges — together with a small reusable infrastructure and the explicit second-stage
named theorems. Since `S(ρ', E₂)` uses a fresh purification of `ρ'`, these cannot be read off a
single reference–system bipartition; following N&C's four-system argument they live on the joint
state that keeps the second environment `C₂` explicit:

* `State.dilatedJoint` — the **un-traced** dilation on `(A ⊗ B) ⊗ C` (`State.dilatedChannelOnRight`
  before its final trace), with `State.reducedLeft_dilatedJoint` (= channel output),
  `State.reducedRight_dilatedJoint` (= environment marginal) and
  `State.vonNeumannEntropy_dilatedJoint` (`= S(ρ)`); `State.dilationEnv` — the environment marginal
  `Tr_B(U(χ ⊗ |ω⟩⟨ω|)U†)`;
* `State.entropyExchange_eq_vonNeumannEntropy_dilationEnv` — N&C §12.4.1's `S(ρ, E) = S(E′)`, which
  makes the entropy exchange purification-independent;
* the three triangle inequalities on the joint state `τ = σ₁.dilatedJoint U₂ ω₂`
  (`σ₁ = (refPurify ρ).dilatedChannelOnRight U₁ ω₁`), using `S(τ) = S(ρ, E₁)`,
  `S(τ_{RQ}) = S(ρ, E₂∘E₁)`, `S(τ_{C₂}) = S(ρ', E₂)`:
  `State.entropyExchangeComp_le_entropyExchange_add_entropyExchange` — the headline **subadditivity
  of entropy exchange** `S(ρ, E₂∘E₁) ≤ S(ρ, E₁) + S(ρ', E₂)` (Araki–Lieb on `τ`), plus its two
  companions `State.entropyExchange_le_entropyExchangeComp_add_entropyExchange` (subadditivity on
  `τ`) and `State.entropyExchange_dilatedChannel_le_entropyExchange_add_entropyExchangeComp`;
* the explicit **second-stage** single-operation theorems (operation `E₂` on
  `ρ' = ρ.dilatedChannel U₁ ω₁`):
  `State.entropyExchange_dilatedChannel_le_vonNeumannEntropy_add_dilatedChannelComp`
  `S(ρ', E₂) ≤ S(ρ') + S(ρ'')` and
  `State.vonNeumannEntropy_dilatedChannel_le_dilatedChannelComp_add_entropyExchange`
  `S(ρ') ≤ S(ρ'') + S(ρ', E₂)` (second-stage eq. (12.144)), thin instantiations of the
  single-operation lemmas above.

Also cited rather than restated: the SSA data-processing inequality `I(ρ, E₂∘E₁) ≤ I(ρ, E₁)`
(`State.coherentInfoComp_le_coherentInfo`, N&C Theorem 12.10).

## The escape clause

The exercise's **escape clause**. Among the marginal entropies of the four-system state
`R''Q''E₁''E₂''` there is exactly one that no combination of subadditivity/SSA expresses in
`S(ρ), S(ρ'), S(ρ'')` and the three entropy exchanges: the pair entropy `S(Q''E₁'') = S(R''E₂'')`
(the two are equal by purity of the global state, but neither reduces to the six standard
quantities). N&C ask for a *prescription* to compute it from `ρ` and the operation elements
`{Eⱼ}` (for `E₁`), `{Fₖ}` (for `E₂`). We give it:

* `State.crossEnvEntropy` — the reference–second-environment entropy `S(R''E₂'')`, defined directly
  as the von Neumann entropy of the `R ⊗ C₂`-marginal of the joint state `τ = σ₁.dilatedJoint U₂ ω₂`
  (`σ₁ = (refPurify ρ).dilatedChannelOnRight U₁ ω₁`), i.e. `τ` with the *middle* system `Q` traced
  out. Everything in `τ` is a fixed function of `ρ` and the dilations `(U₁, ω₁), (U₂, ω₂)` that
  present the operations, so this **is** the requested prescription — a definite real number
  computed from `ρ` and the operation elements. The middle trace is realised by the reshape
  `(R ⊗ Q) ⊗ C₂ ≃ C₂ ⊗ (R ⊗ Q) ≃ (C₂ ⊗ R) ⊗ Q` (`QSystem.Iso.comm`, `QSystem.assoc`) followed by
  `State.reducedLeft`, so that its two marginals fall out of the associator/commutator reduced-state
  lemmas (`State.reducedLeft_reducedLeft_congr_assoc`, `State.reducedRight_reducedLeft_congr_assoc`,
  `State.reducedLeft_congr_comm`, `State.reducedRight_congr_comm`).
* the inequalities in which the escape quantity **appears** — subadditivity and the two Araki–Lieb
  directions applied to the pair `(R'', E₂'')`, the direct two-stage analogue of N&C eq. (12.143):
  `State.crossEnvEntropy_le_vonNeumannEntropy_add_entropyExchange_dilatedChannel`
  `S(R''E₂'') ≤ S(ρ) + S(ρ', E₂)`, and the companions
  `State.vonNeumannEntropy_le_crossEnvEntropy_add_entropyExchange_dilatedChannel`
  `S(ρ) ≤ S(R''E₂'') + S(ρ', E₂)` and
  `State.entropyExchange_dilatedChannel_le_crossEnvEntropy_add_vonNeumannEntropy`
  `S(ρ', E₂) ≤ S(R''E₂'') + S(ρ)` — together the full triangle
  `|S(ρ) − S(ρ', E₂)| ≤ S(R''E₂'') ≤ S(ρ) + S(ρ', E₂)`. The two known marginals are read off `τ` by
  the same chain as the triangle proofs (`R`-marginal isentropic with the input,
  `S(R'') = S(ρ)`; `C₂`-marginal the environment of `E₂` on `ρ'`,
  `S(E₂'') = S(ρ', E₂)` via `State.entropyExchange_eq_vonNeumannEntropy_dilationEnv`).

The preceding sections give all the combinations expressible in the standard quantities, and this
one supplies the prescription for the one that is not.

## Related declarations

The statements use `State.entropyExchange`, `State.entropyExchangeComp`, `State.dilatedChannel`,
`State.dilatedChannelComp`, `State.coherentInfoComp`, `State.vonNeumannEntropy` and the
constructions `State.dilatedJoint`/`State.dilationEnv`. As in its sibling
`AxQM/NC/Ch12/CoherentInformation.lean`, the purification reference `R` (`State.refPurify`, in
`AxQM/Postulates/API/`) appears only in the bodies of definitions and proofs.
-/

noncomputable section

namespace AxQM

variable {Q C : QSystem}

/-! ### Single-operation inequalities

These hold for any one operation `E` (dilation `(U, ω)`); applied to `(ρ, E₁)` they are the first
stage of the process, applied to `(ρ', E₂)` the second. -/

/-- **Subadditivity bound on the entropy exchange** (Nielsen & Chuang §12.4, a subadditivity
combination for the process of Exercise 12.15). For a state `ρ` on `Q` and an operation `E`
presented by its dilation `(U, ω)`,

`S(ρ, E) ≤ S(ρ) + S(E(ρ))`.

Subadditivity `S(R', Q') ≤ S(R') + S(Q')`
(`State.vonNeumannEntropy_le_reducedLeft_add_reducedRight`) applied to the reference–system state
`R'Q' = (refPurify ρ).dilatedChannelOnRight U ω` whose joint entropy is the entropy exchange
`S(ρ, E) = S(R'Q')` (`State.entropyExchange`), whose reference marginal is isentropic with the input
`S(R') = S(ρ)` (`State.reducedLeft_dilatedChannelOnRight`,
`State.vonNeumannEntropy_refPurify_reducedLeft`), and whose system marginal is the output
`S(Q') = S(E(ρ))` (`State.reducedRight_dilatedChannelOnRight`, `State.refPurify_reducedRight`). -/
theorem State.entropyExchange_le_vonNeumannEntropy_add_dilatedChannel (ρ : State Q)
    (U : Evolution (Q ⊗ C)) (ω : PureState C) :
    ρ.entropyExchange U ω ≤ ρ.vonNeumannEntropy + (ρ.dilatedChannel U ω).vonNeumannEntropy := by
  have hsub := State.vonNeumannEntropy_le_reducedLeft_add_reducedRight
    (ρ.refPurify.toState.dilatedChannelOnRight U ω)
  rw [State.reducedRight_dilatedChannelOnRight, State.refPurify_reducedRight,
    State.reducedLeft_dilatedChannelOnRight, State.vonNeumannEntropy_refPurify_reducedLeft] at hsub
  unfold State.entropyExchange
  linarith

/-- **N&C eq. (12.144): `ΔS + S(ρ, E) ≥ 0`** — the change in the system entropy plus the entropy
exchange is non-negative (an "eminently reasonable statement in accord with the second law of
thermodynamics", N&C p. 568). Stated as

`S(ρ) ≤ S(E(ρ)) + S(ρ, E)`

(with `ΔS = S(E(ρ)) − S(ρ)`). This is the subadditivity inequality applied to the systems `Q'E'`,
which N&C's preamble to Exercise 12.15 rewrites as eq. (12.143); in the purification picture it is
the Araki–Lieb triangle inequality `S(R') − S(Q') ≤ S(R', Q')`
(`State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le`) on `R'Q' =
(refPurify ρ).dilatedChannelOnRight U ω`, using `S(R') = S(ρ)`, `S(Q') = S(E(ρ))` and `S(R'Q') =
S(ρ, E)` exactly as in `State.entropyExchange_le_vonNeumannEntropy_add_dilatedChannel`. -/
theorem State.vonNeumannEntropy_le_dilatedChannel_add_entropyExchange (ρ : State Q)
    (U : Evolution (Q ⊗ C)) (ω : PureState C) :
    ρ.vonNeumannEntropy ≤ (ρ.dilatedChannel U ω).vonNeumannEntropy + ρ.entropyExchange U ω := by
  have htri := State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le
    (ρ.refPurify.toState.dilatedChannelOnRight U ω)
  rw [State.reducedRight_dilatedChannelOnRight, State.refPurify_reducedRight,
    State.reducedLeft_dilatedChannelOnRight, State.vonNeumannEntropy_refPurify_reducedLeft] at htri
  unfold State.entropyExchange
  linarith

/-! ### Composite process

The two-stage output `ρ'' = (E₂ ∘ E₁)(ρ)` and its entropy exchange `S(ρ, E₂∘E₁)`, with the same
subadditivity/triangle inequalities read off the twice-processed reference–system state `R''Q''`. -/

/-- The **composite output** `ρ'' = (E₂ ∘ E₁)(ρ)` of the two-stage process: apply `E₁` (dilation
`(U₁, ω₁)` on `Q ⊗ C`) then `E₂` (dilation `(U₂, ω₂)` on `Q ⊗ D`) to the single system `Q`. This is
the system-only companion of `State.coherentInfoComp`/`State.entropyExchangeComp`, and its entropy
`S(ρ'')` is the `S(Q'')` marginal entropy of the reference–system state `R''Q''`. -/
def State.dilatedChannelComp (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C)
    {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : State Q :=
  (ρ.dilatedChannel U₁ ω₁).dilatedChannel U₂ ω₂

/-- The **entropy exchange of the two-stage composite operation** `S(ρ, E₂ ∘ E₁) = S(R''Q'')`
(Nielsen & Chuang eq. (12.130), purification form). It is the joint entropy of the twice-processed
reference–system state `R''Q''` obtained by applying both right-factor dilations to `refPurify ρ`,
the composite counterpart of the single-channel `State.entropyExchange`. By the framework's
purification definition it equals the entropy of the composite environment `E₁E₂` after both stages,
`S(ρ, E₂ ∘ E₁) = S(E₁''E₂'')`, and it enters `State.coherentInfoComp` as
`I(ρ, E₂∘E₁) = S(ρ'') − S(ρ, E₂∘E₁)`. -/
def State.entropyExchangeComp (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C)
    {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : ℝ :=
  ((ρ.refPurify.toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂).vonNeumannEntropy

/-- **Subadditivity bound on the composite entropy exchange**: for the two-stage process of
Exercise 12.15,

`S(ρ, E₂ ∘ E₁) ≤ S(ρ) + S(ρ'')`.

Subadditivity `S(R'', Q'') ≤ S(R'') + S(Q'')` on the twice-processed reference–system state, with
`S(R''Q'') = S(ρ, E₂∘E₁)` (`State.entropyExchangeComp`), the reference marginal still isentropic
with the input `S(R'') = S(ρ)` (`R` is untouched by both stages, two
`State.reducedLeft_dilatedChannelOnRight` steps + `State.vonNeumannEntropy_refPurify_reducedLeft`),
and the system marginal the composite output `S(Q'') = S(ρ'')` (two
`State.reducedRight_dilatedChannelOnRight` steps + `State.refPurify_reducedRight`). -/
theorem State.entropyExchangeComp_le_vonNeumannEntropy_add_dilatedChannelComp (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) :
    ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ ≤
      ρ.vonNeumannEntropy + (ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂).vonNeumannEntropy := by
  have hsub := State.vonNeumannEntropy_le_reducedLeft_add_reducedRight
    ((ρ.refPurify.toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂)
  rw [State.reducedRight_dilatedChannelOnRight, State.reducedRight_dilatedChannelOnRight,
    State.refPurify_reducedRight, State.reducedLeft_dilatedChannelOnRight,
    State.reducedLeft_dilatedChannelOnRight,
    State.vonNeumannEntropy_refPurify_reducedLeft] at hsub
  unfold State.entropyExchangeComp State.dilatedChannelComp
  linarith

/-- **Composite form of N&C eq. (12.144)**: for the two-stage process,

`S(ρ) ≤ S(ρ'') + S(ρ, E₂ ∘ E₁)`.

The Araki–Lieb triangle inequality `S(R'') − S(Q'') ≤ S(R'', Q'')`
(`State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le`) on the twice-processed reference–system
state, with the same three identifications as
`State.entropyExchangeComp_le_vonNeumannEntropy_add_dilatedChannelComp`. -/
theorem State.vonNeumannEntropy_le_dilatedChannelComp_add_entropyExchangeComp (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) :
    ρ.vonNeumannEntropy ≤
      (ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂).vonNeumannEntropy + ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ := by
  have htri := State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le
    ((ρ.refPurify.toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂)
  rw [State.reducedRight_dilatedChannelOnRight, State.reducedRight_dilatedChannelOnRight,
    State.refPurify_reducedRight, State.reducedLeft_dilatedChannelOnRight,
    State.reducedLeft_dilatedChannelOnRight,
    State.vonNeumannEntropy_refPurify_reducedLeft] at htri
  unfold State.entropyExchangeComp State.dilatedChannelComp
  linarith

/-- **Composite first-stage data-processing bound**: for the two-stage process,

`I(ρ, E₂ ∘ E₁) ≤ S(ρ)`.

This is the coherent-information reading of the composite eq. (12.144)
(`State.vonNeumannEntropy_le_dilatedChannelComp_add_entropyExchangeComp`): unfolding
`I(ρ, E₂∘E₁) = S(ρ'') − S(ρ, E₂∘E₁)` (`State.coherentInfoComp`, `State.coherentInfoOfState_def`), it
is the other Araki–Lieb direction `S(Q'') − S(R'') ≤ S(R'', Q'')`
(`State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le`) on `R''Q''` with `S(R'') = S(ρ)`. It
also follows from the chain `S(ρ) ≥ I(ρ, E₁) ≥ I(ρ, E₂∘E₁)` (N&C Theorem 12.10); the direct
derivation from the triangle inequality is recorded as one of the Exercise 12.15 combinations. -/
theorem State.coherentInfoComp_le_vonNeumannEntropy (ρ : State Q) (U₁ : Evolution (Q ⊗ C))
    (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    ρ.coherentInfoComp U₁ ω₁ U₂ ω₂ ≤ ρ.vonNeumannEntropy := by
  have htri := State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le
    ((ρ.refPurify.toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂)
  rw [State.reducedLeft_dilatedChannelOnRight, State.reducedLeft_dilatedChannelOnRight,
    State.vonNeumannEntropy_refPurify_reducedLeft] at htri
  unfold State.coherentInfoComp
  rw [State.coherentInfoOfState_def]
  linarith

/-! ### Two-environment infrastructure: the joint dilation and its environment marginal

The genuinely two-environment combinations of Exercise 12.15 — the ones relating all *three*
entropy exchanges `S(ρ, E₁)`, `S(ρ', E₂)`, `S(ρ, E₂∘E₁)` — cannot be read off a single
reference–system bipartition, because `S(ρ', E₂)` uses a *fresh* purification of the intermediate
state `ρ'`. Following N&C's four-system argument, they live on the state that keeps the **second
environment `C₂`** explicit. We build that state as the **un-traced** dilation `State.dilatedJoint`
(exactly `State.dilatedChannelOnRight` *before* its final partial trace) together with the
environment marginal `State.dilationEnv`, and record N&C §12.4.1's identity `S(ρ, E) = S(E′)`
(`State.entropyExchange_eq_vonNeumannEntropy_dilationEnv`): the entropy exchange equals the entropy
of the environment after the interaction, and the environment marginal depends on the input only
through its state. -/

variable {A B : QSystem}

/-- **The joint state of a channel dilated on the right factor, keeping its environment.** For a
bipartite state `ρ` on `A ⊗ B`, a unitary `U` on `B ⊗ C` and a pure ancilla `ω` on `C`, this is
`(I_A ⊗ U)(ρ ⊗ |ω⟩⟨ω|)(I_A ⊗ U)†` on `(A ⊗ B) ⊗ C` — the state that `State.dilatedChannelOnRight`
traces its environment `C` out of. Its `A ⊗ B`-marginal is the channel output
`(id_A ⊗ E) ρ = ρ.dilatedChannelOnRight U ω` (`State.reducedLeft_dilatedJoint`) and its `C`-marginal
is the environment after the interaction (`State.reducedRight_dilatedJoint`); keeping both is what
lets the entropy-exchange triangle inequalities of Exercise 12.15 see `C₂` as an explicit factor. -/
def State.dilatedJoint (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C)) (ω : PureState C) :
    State ((A ⊗ B) ⊗ C) :=
  (((Evolution.id (S := A)).tmul U).evolve
      (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω.toState))).congr (QSystem.assoc A B C)

/-- The pure-state track of `State.dilatedJoint`: for a *pure* input `ψ` the joint dilation is again
pure (unitary evolution and reshapes preserve purity), which is what exhibits `S(R′Q′) = S(E′)` as
an entropy of complementary marginals of one pure state. Its `toState` is
`State.dilatedJoint ψ.toState U ω` (`PureState.dilatedJoint_toState`). -/
def PureState.dilatedJoint (ψ : PureState (A ⊗ B)) (U : Evolution (B ⊗ C)) (ω : PureState C) :
    PureState ((A ⊗ B) ⊗ C) :=
  (((Evolution.id (S := A)).tmul U).evolvePure
      (PureState.congr (QSystem.assoc A B C).symm (ψ.tmul ω))).congr (QSystem.assoc A B C)

/-- The density operator of the pure joint dilation is the mixed-state joint dilation of the
underlying state: `(ψ.dilatedJoint U ω).toState = ψ.toState.dilatedJoint U ω`. Immediate from the
`toState` naturality of `PureState.tmul`, `PureState.congr` and `evolvePure`. -/
theorem PureState.dilatedJoint_toState (ψ : PureState (A ⊗ B)) (U : Evolution (B ⊗ C))
    (ω : PureState C) : (ψ.dilatedJoint U ω).toState = ψ.toState.dilatedJoint U ω := by
  unfold PureState.dilatedJoint State.dilatedJoint
  rw [PureState.congr_toState, toState_evolvePure, PureState.congr_toState, PureState.toState_tmul]

/-- **The `A ⊗ B`-marginal of the joint dilation is the channel output.**
`State.dilatedChannelOnRight` is `State.dilatedJoint` with the environment traced out, so this holds
definitionally. -/
theorem State.reducedLeft_dilatedJoint (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C))
    (ω : PureState C) : (ρ.dilatedJoint U ω).reducedLeft = ρ.dilatedChannelOnRight U ω := rfl

/-- **The joint dilation is isentropic with the input**:
`S((I_A ⊗ U)(ρ ⊗ |ω⟩⟨ω|)(I_A ⊗ U)†) = S(ρ)`. The reshapes (`State.vonNeumannEntropy_congr`) and the
local unitary `I_A ⊗ U` (`State.vonNeumannEntropy_evolve`) preserve the entropy, and appending the
pure ancilla `ω` adds none
(`State.vonNeumannEntropy_tmul`, `PureState.vonNeumannEntropy_toState_eq_zero`). -/
theorem State.vonNeumannEntropy_dilatedJoint (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C))
    (ω : PureState C) : (ρ.dilatedJoint U ω).vonNeumannEntropy = ρ.vonNeumannEntropy := by
  unfold State.dilatedJoint
  rw [State.vonNeumannEntropy_congr, State.vonNeumannEntropy_evolve, State.vonNeumannEntropy_congr,
    State.vonNeumannEntropy_tmul, PureState.vonNeumannEntropy_toState_eq_zero, add_zero]

/-- **The environment marginal** `E′ = Tr_B(U(χ ⊗ |ω⟩⟨ω|)U†)` of dilating a single-system state `χ`
on `B` by `(U, ω)`: the `C`-marginal of the interacted state — the complement of the channel output
`State.dilatedChannel` (which keeps `B`). This is N&C's environment `E` after the operation, into
which the entropy exchange is deposited
(`State.entropyExchange_eq_vonNeumannEntropy_dilationEnv`). -/
def State.dilationEnv (χ : State B) (U : Evolution (B ⊗ C)) (ω : PureState C) : State C :=
  (U.evolve (χ.tmul ω.toState)).reducedRight

/-- **The `C`-marginal of the joint dilation is the environment marginal of the `B`-marginal.**
`Tr_{A⊗B}((I_A ⊗ U)(ρ ⊗ |ω⟩⟨ω|)(I_A ⊗ U)†) = Tr_B(U(ρ_B ⊗ |ω⟩⟨ω|)U†)`: the environment `C` sees the
input `ρ` only through its `B`-marginal `ρ_B = ρ.reducedRight`. The `State.reducedRight` mirror of
`State.reducedRight_dilatedChannelOnRight` — the same three reshapes
(`State.reducedRight_congr_assoc`, `State.reducedRight_evolve_id_tmul`,
`State.reducedRight_congr_symm_assoc_tmul`), tracing the whole `A ⊗ B` block rather than only
`A`. -/
theorem State.reducedRight_dilatedJoint (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C))
    (ω : PureState C) : (ρ.dilatedJoint U ω).reducedRight = ρ.reducedRight.dilationEnv U ω := by
  unfold State.dilatedJoint State.dilationEnv
  rw [State.reducedRight_congr_assoc, State.reducedRight_evolve_id_tmul,
    State.reducedRight_congr_symm_assoc_tmul]

/-- **N&C §12.4.1: the entropy exchange is the entropy of the environment**, `S(ρ, E) = S(E′)`.
For a state `χ` on `B` and an operation `E` presented by its dilation `(U, ω)`, the entropy exchange
`S(χ, E) = S(R′Q′)` (`State.entropyExchange`, the reference–system reading) equals the von Neumann
entropy of the environment marginal `E′ = χ.dilationEnv U ω`. Since the reference-purified,
dilated state `refPurify χ ▸ dilatedJoint` is pure, its complementary marginals `R′Q′` and `E′`
are isentropic (`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`); the `R′Q′`-marginal is
the channel output-side `dilatedChannelOnRight` (`State.reducedLeft_dilatedJoint`, whose entropy is
the
entropy exchange), and the `E′`-marginal is `dilationEnv` of the `B`-marginal of the purification,
which is `χ` itself (`State.reducedRight_dilatedJoint`, `State.refPurify_reducedRight`). This is the
identity N&C invoke to make the entropy exchange purification-independent. -/
theorem State.entropyExchange_eq_vonNeumannEntropy_dilationEnv (χ : State B)
    (U : Evolution (B ⊗ C)) (ω : PureState C) :
    χ.entropyExchange U ω = (χ.dilationEnv U ω).vonNeumannEntropy := by
  have hpure := PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight
    ((State.refPurify χ).dilatedJoint U ω)
  rw [PureState.dilatedJoint_toState, State.reducedLeft_dilatedJoint,
    State.reducedRight_dilatedJoint, State.refPurify_reducedRight] at hpure
  unfold State.entropyExchange
  exact hpure

/-! ### Entropy-exchange triangle inequalities (all three entropy exchanges)

Applying subadditivity and the Araki–Lieb triangle inequality to the joint state
`τ = σ₁.dilatedJoint U₂ ω₂` on `(R ⊗ Q) ⊗ C₂` — where
`σ₁ = (refPurify ρ).dilatedChannelOnRight U₁ ω₁`
is the reference–system state after `E₁` — yields the combinations relating all three entropy
exchanges. The three marginal identities are

* `S(τ) = S(σ₁) = S(ρ, E₁)` (`State.vonNeumannEntropy_dilatedJoint`, `τ` is `σ₁` dilated by a
  unitary with a pure ancilla);
* `S(τ_{RQ}) = S(σ₁ .dilatedChannelOnRight U₂ ω₂) = S(ρ, E₂∘E₁)` (`State.reducedLeft_dilatedJoint`,
  the `entropyExchangeComp` state);
* `S(τ_{C₂}) = S(ρ', E₂)` (`State.reducedRight_dilatedJoint`,
  `State.reducedRight_dilatedChannelOnRight` and `State.refPurify_reducedRight` identify the
  `C₂`-marginal as the environment of `E₂` acting on `ρ' = E₁(ρ)`;
  `State.entropyExchange_eq_vonNeumannEntropy_dilationEnv` reads it back as the entropy exchange).

These are N&C's `S(E₁E₂)`, `S(R''Q'') = S(E₁E₂)` and `S(E₂)` in the four-system picture.

The three identities are applied *inline* in each proof (a short shared rewrite chain), rather than
as named lemmas. The `refPurify`-free content is factored out:
`State.vonNeumannEntropy_dilatedJoint`, `State.reducedLeft_dilatedJoint`,
`State.reducedRight_dilatedJoint` and `State.entropyExchange_eq_vonNeumannEntropy_dilationEnv` are
the shared lemmas each proof composes. -/

/-- **Subadditivity of the entropy exchange** — the headline entropy-exchange triangle inequality of
Exercise 12.15: for the two-stage process `ρ → ρ' = E₁(ρ) → ρ'' = (E₂∘E₁)(ρ)`,

`S(ρ, E₂∘E₁) ≤ S(ρ, E₁) + S(ρ', E₂)`.

The joint environment `E₁E₂` is no more disordered than its parts: the Araki–Lieb triangle
`S(τ_{RQ}) − S(τ_{C₂}) ≤ S(τ)` (`State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le`) on the
joint state `τ = σ₁.dilatedJoint U₂ ω₂` becomes, under the three marginal identities above,
`S(ρ, E₂∘E₁) − S(ρ', E₂) ≤ S(ρ, E₁)`. -/
theorem State.entropyExchangeComp_le_entropyExchange_add_entropyExchange (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) :
    ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ ≤
      ρ.entropyExchange U₁ ω₁ + (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := by
  have hAL := State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le
    (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedJoint U₂ ω₂)
  rw [State.reducedLeft_dilatedJoint, State.vonNeumannEntropy_dilatedJoint,
    State.reducedRight_dilatedJoint, State.reducedRight_dilatedChannelOnRight,
    State.refPurify_reducedRight] at hAL
  rw [State.entropyExchange_eq_vonNeumannEntropy_dilationEnv (ρ.dilatedChannel U₁ ω₁) U₂ ω₂]
  unfold State.entropyExchangeComp State.entropyExchange
  linarith

/-- **Araki–Lieb companion of entropy-exchange subadditivity**: for the two-stage process,

`S(ρ, E₁) ≤ S(ρ, E₂∘E₁) + S(ρ', E₂)`.

Subadditivity `S(τ) ≤ S(τ_{RQ}) + S(τ_{C₂})`
(`State.vonNeumannEntropy_le_reducedLeft_add_reducedRight`) on the joint state `τ`, under the same
three marginal identities as `State.entropyExchangeComp_le_entropyExchange_add_entropyExchange`. -/
theorem State.entropyExchange_le_entropyExchangeComp_add_entropyExchange (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) :
    ρ.entropyExchange U₁ ω₁ ≤
      ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ + (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := by
  have hsub := State.vonNeumannEntropy_le_reducedLeft_add_reducedRight
    (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedJoint U₂ ω₂)
  rw [State.reducedLeft_dilatedJoint, State.vonNeumannEntropy_dilatedJoint,
    State.reducedRight_dilatedJoint, State.reducedRight_dilatedChannelOnRight,
    State.refPurify_reducedRight] at hsub
  rw [State.entropyExchange_eq_vonNeumannEntropy_dilationEnv (ρ.dilatedChannel U₁ ω₁) U₂ ω₂]
  unfold State.entropyExchangeComp State.entropyExchange
  linarith

/-- **Second Araki–Lieb companion of entropy-exchange subadditivity**: for the two-stage process,

`S(ρ', E₂) ≤ S(ρ, E₁) + S(ρ, E₂∘E₁)`.

The other Araki–Lieb direction `S(τ_{C₂}) − S(τ_{RQ}) ≤ S(τ)`
(`State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le`) on the joint state `τ`, under the same
three marginal identities. The three companions together are the full triangle
`|S(ρ, E₁) − S(ρ', E₂)| ≤ S(ρ, E₂∘E₁) ≤ S(ρ, E₁) + S(ρ', E₂)` for the entropy exchanges. -/
theorem State.entropyExchange_dilatedChannel_le_entropyExchange_add_entropyExchangeComp
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ ≤
      ρ.entropyExchange U₁ ω₁ + ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ := by
  have hAL := State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le
    (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedJoint U₂ ω₂)
  rw [State.reducedLeft_dilatedJoint, State.vonNeumannEntropy_dilatedJoint,
    State.reducedRight_dilatedJoint, State.reducedRight_dilatedChannelOnRight,
    State.refPurify_reducedRight] at hAL
  rw [State.entropyExchange_eq_vonNeumannEntropy_dilationEnv (ρ.dilatedChannel U₁ ω₁) U₂ ω₂]
  unfold State.entropyExchangeComp State.entropyExchange
  linarith

/-! ### Explicit second-stage single-operation inequalities

The single-operation inequalities of §12.4 (this file's
`State.entropyExchange_le_..._dilatedChannel` and
`State.vonNeumannEntropy_le_dilatedChannel_add_entropyExchange`) applied to the **second stage**
— operation `E₂` on the intermediate state `ρ' = E₁(ρ) = ρ.dilatedChannel U₁ ω₁` — named for
citation, with the third entropy exchange `S(ρ', E₂)` and the final output
`ρ'' = ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂`. -/

/-- **Second-stage subadditivity bound on the entropy exchange**: `S(ρ', E₂) ≤ S(ρ') + S(ρ'')`, the
single-operation `State.entropyExchange_le_vonNeumannEntropy_add_dilatedChannel` instantiated at the
intermediate state `ρ' = ρ.dilatedChannel U₁ ω₁` and operation `E₂`. -/
theorem State.entropyExchange_dilatedChannel_le_vonNeumannEntropy_add_dilatedChannelComp
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ ≤
      (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy +
        (ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂).vonNeumannEntropy :=
  (ρ.dilatedChannel U₁ ω₁).entropyExchange_le_vonNeumannEntropy_add_dilatedChannel U₂ ω₂

/-- **Second-stage form of N&C eq. (12.144)**: `S(ρ') ≤ S(ρ'') + S(ρ', E₂)`, i.e.
`ΔS₂ + S(ρ', E₂) ≥ 0` for the second stage, the single-operation
`State.vonNeumannEntropy_le_dilatedChannel_add_entropyExchange` instantiated at
`ρ' = ρ.dilatedChannel U₁ ω₁` and operation `E₂`. -/
theorem State.vonNeumannEntropy_dilatedChannel_le_dilatedChannelComp_add_entropyExchange
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy ≤
      (ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂).vonNeumannEntropy +
        (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ :=
  (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy_le_dilatedChannel_add_entropyExchange U₂ ω₂

/-! ### The non-expressible quantity: the prescription for `S(Q''E₁'') = S(R''E₂'')`

Every quantity appearing in the subadditivity/SSA combinations of the two-stage process is a
marginal entropy of the four-system state `R''Q''E₁''E₂''` (pure, since `R` purifies the input and
the environments start pure). All but one reduce to `S(ρ), S(ρ'), S(ρ'')` and the three entropy
exchanges via complementary-marginal purity; the exception is the pair entropy
`S(Q''E₁'') = S(R''E₂'')`. The exercise asks for a prescription to compute it from `ρ` and the
operation elements. We supply it as
`State.crossEnvEntropy`, the von Neumann entropy of the `R ⊗ C₂`-marginal of the joint state
`τ = σ₁.dilatedJoint U₂ ω₂` — `τ` with its middle system `Q` traced out — and record the
inequalities in which it appears. -/

/-- **The reference–second-environment entropy `S(R''E₂'')`** — the prescription (Nielsen & Chuang
Exercise 12.15, escape clause) for the one quantity of the two-stage process
`ρ → ρ' = E₁(ρ) → ρ'' = (E₂∘E₁)(ρ)` that no combination of subadditivity/strong subadditivity
expresses in `S(ρ), S(ρ'), S(ρ'')` and the entropy exchanges `S(ρ, E₁), S(ρ', E₂), S(ρ, E₂∘E₁)`.

In the four-system picture `R''Q''E₁''E₂''` this quantity is `S(R''E₂'')`, equal by global purity to
`S(Q''E₁'')` but not to any of the six standard quantities. It is defined here directly as the von
Neumann entropy of the `R ⊗ C₂`-marginal of the joint dilated state `τ = σ₁.dilatedJoint U₂ ω₂`,
where `σ₁ = (refPurify ρ).dilatedChannelOnRight U₁ ω₁` is the reference–system state after `E₁` and
`C₂` is the second environment — i.e. `τ` (on `(R ⊗ Q) ⊗ C₂`) with the *middle* system `Q` traced
out. Because `τ` is a fixed function of `ρ` and the dilations `(U₁, ω₁), (U₂, ω₂)` that present the
operations `{Eⱼ}, {Fₖ}`, this is precisely N&C's requested prescription: a definite real number
computed from `ρ` and the operation elements. The middle trace is realised by the reshape
`(R ⊗ Q) ⊗ C₂ ≃ C₂ ⊗ (R ⊗ Q) ≃ (C₂ ⊗ R) ⊗ Q` (`QSystem.Iso.comm` then `QSystem.assoc`) followed by
`State.reducedLeft`, keeping the reference `R` in the definition body only (as with
`State.entropyExchange` and the triangle inequalities, it does not appear in any statement). -/
def State.crossEnvEntropy (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C)
    {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : ℝ :=
  (State.congr (QSystem.assoc D _ Q)
      (State.congr (QSystem.Iso.comm _ D)
        (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedJoint U₂ ω₂))).reducedLeft
    |>.vonNeumannEntropy

/-! ### Marginals of the `R ⊗ C₂` block

The `R ⊗ C₂`-block whose entropy is `State.crossEnvEntropy` is
`τ = σ₁.dilatedJoint U₂ ω₂` reshaped so `Q` is the outer factor and traced off
(`σ₁ = (refPurify ρ).dilatedChannelOnRight U₁ ω₁`). Its two marginals carry the two *expressible*
quantities: the `C₂`-side (`.reducedLeft.reducedLeft`) is `E₂''` with entropy `S(ρ', E₂)`, and the
`R`-side (`.reducedLeft.reducedRight`) is `R''` with entropy `S(ρ)`.

The first half of that computation — the associator/commutator reshape composed with the
`dilatedJoint` marginal identities, for an **arbitrary** bipartite `σ` — is the content of
the two generic `_dilatedJointReshape` lemmas below, used by all three inequalities. The remaining
part — the purification identifications `σ₁_R = ρ` and `σ₁_Q = E₁(ρ)`
(`State.reducedRight_dilatedChannelOnRight`, `State.refPurify_reducedRight`,
`State.reducedLeft_dilatedChannelOnRight`, `State.vonNeumannEntropy_refPurify_reducedLeft`) — is
applied inline in each inequality. -/

/-- **Reshaped joint state: the outer-pair (`E ⊗ A`) marginal's `E`-side entropy is `S(σ_B, E)`.**
For a *generic* bipartite state `σ` on `A ⊗ B` dilated on its `B` factor by `(U, ω)`, reshape the
joint state `σ.dilatedJoint U ω` (on `(A ⊗ B) ⊗ E`) to put `B` outermost and trace it off; the
`E`-side of the resulting `E ⊗ A` block carries the entropy exchange of the channel on the
`B`-marginal `σ_B = σ.reducedRight`. Stated generically, with no
purification reference, it applies to the `crossEnvEntropy` block by instantiation. The reshape
(`State.reducedLeft_reducedLeft_congr_assoc`, `State.reducedRight_congr_comm`) lands on
`(σ.dilatedJoint U ω).reducedRight`, the environment output (`State.reducedRight_dilatedJoint`),
read as an entropy exchange by
`State.entropyExchange_eq_vonNeumannEntropy_dilationEnv`. -/
theorem State.vonNeumannEntropy_reducedLeft_reducedLeft_dilatedJointReshape {A B E : QSystem}
    (σ : State (A ⊗ B)) (U : Evolution (B ⊗ E)) (ω : PureState E) :
    (State.congr (QSystem.assoc E A B)
          (State.congr (QSystem.Iso.comm (A ⊗ B) E)
            (σ.dilatedJoint U ω))).reducedLeft.reducedLeft.vonNeumannEntropy
      = σ.reducedRight.entropyExchange U ω := by
  rw [State.reducedLeft_reducedLeft_congr_assoc, ← State.reducedRight_congr_comm,
    State.reducedRight_dilatedJoint, ← State.entropyExchange_eq_vonNeumannEntropy_dilationEnv]

/-- **Reshaped joint state: the outer-pair (`E ⊗ A`) marginal's `A`-side entropy is `S(σ_A)`.**
For a generic bipartite state `σ` on `A ⊗ B` dilated on its `B` factor, the `A`-side of the reshaped
`E ⊗ A` block is the untouched `A`-marginal `σ_A = σ.reducedLeft`: the channel and the dilation act
only on `B`/`E`. Stated with no purification reference. The reshape
(`State.reducedRight_reducedLeft_congr_assoc`, `State.reducedLeft_congr_comm`) lands on
`(σ.dilatedJoint U ω).reducedLeft.reducedLeft` (`State.reducedLeft_dilatedJoint`,
`State.reducedLeft_dilatedChannelOnRight`), which is `σ.reducedLeft`. -/
theorem State.vonNeumannEntropy_reducedLeft_reducedRight_dilatedJointReshape {A B E : QSystem}
    (σ : State (A ⊗ B)) (U : Evolution (B ⊗ E)) (ω : PureState E) :
    (State.congr (QSystem.assoc E A B)
          (State.congr (QSystem.Iso.comm (A ⊗ B) E)
            (σ.dilatedJoint U ω))).reducedLeft.reducedRight.vonNeumannEntropy
      = σ.reducedLeft.vonNeumannEntropy := by
  rw [State.reducedRight_reducedLeft_congr_assoc, ← State.reducedLeft_congr_comm,
    State.reducedLeft_dilatedJoint, State.reducedLeft_dilatedChannelOnRight]

/-- **Subadditivity for the escape quantity**: applying subadditivity to the pair `(R'', E₂'')` —
the two-stage analogue of N&C eq. (12.143) — gives

`S(R''E₂'') ≤ S(ρ) + S(ρ', E₂)`.

Subadditivity `S(R''E₂'') ≤ S(R'') + S(E₂'')`
(`State.vonNeumannEntropy_le_reducedLeft_add_reducedRight` on the `R ⊗ C₂`-marginal) with
`S(R'') = S(ρ)` (the reference is untouched, so its marginal is isentropic with the input) and
`S(E₂'') = S(ρ', E₂)` (the `C₂`-marginal is the environment of `E₂` acting on `ρ'`, read as an
entropy exchange by `State.entropyExchange_eq_vonNeumannEntropy_dilationEnv`). The two marginals of
the `R ⊗ C₂`-block are extracted from the joint state `τ` by the associator / commutator
reduced-state lemmas. -/
theorem State.crossEnvEntropy_le_vonNeumannEntropy_add_entropyExchange_dilatedChannel
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    ρ.crossEnvEntropy U₁ ω₁ U₂ ω₂ ≤
      ρ.vonNeumannEntropy + (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := by
  unfold State.crossEnvEntropy
  refine le_trans (State.vonNeumannEntropy_le_reducedLeft_add_reducedRight _) ?_
  rw [State.vonNeumannEntropy_reducedLeft_reducedLeft_dilatedJointReshape,
    State.vonNeumannEntropy_reducedLeft_reducedRight_dilatedJointReshape,
    State.reducedRight_dilatedChannelOnRight, State.refPurify_reducedRight,
    State.reducedLeft_dilatedChannelOnRight, State.vonNeumannEntropy_refPurify_reducedLeft]
  linarith

/-- **Araki–Lieb lower bound on `S(ρ)` by the escape quantity**: for the two-stage process,

`S(ρ) ≤ S(R''E₂'') + S(ρ', E₂)`.

The Araki–Lieb triangle inequality `S(R'') − S(E₂'') ≤ S(R''E₂'')`
(`State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le` on the `R ⊗ C₂`-marginal, whose right
factor `R''` carries `S(ρ)` and whose left factor `E₂''` carries `S(ρ', E₂)`). Together with the
subadditivity bound this brackets the escape quantity from below. -/
theorem State.vonNeumannEntropy_le_crossEnvEntropy_add_entropyExchange_dilatedChannel
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    ρ.vonNeumannEntropy ≤
      ρ.crossEnvEntropy U₁ ω₁ U₂ ω₂ + (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := by
  have hAL := State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le
    (State.congr (QSystem.assoc D _ Q)
      (State.congr (QSystem.Iso.comm _ D)
        (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedJoint U₂ ω₂))).reducedLeft
  rw [State.vonNeumannEntropy_reducedLeft_reducedLeft_dilatedJointReshape,
    State.vonNeumannEntropy_reducedLeft_reducedRight_dilatedJointReshape,
    State.reducedRight_dilatedChannelOnRight, State.refPurify_reducedRight,
    State.reducedLeft_dilatedChannelOnRight, State.vonNeumannEntropy_refPurify_reducedLeft] at hAL
  unfold State.crossEnvEntropy
  linarith

/-- **Araki–Lieb lower bound on `S(ρ', E₂)` by the escape quantity**: for the two-stage process,

`S(ρ', E₂) ≤ S(R''E₂'') + S(ρ)`.

The other Araki–Lieb direction `S(E₂'') − S(R'') ≤ S(R''E₂'')`
(`State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le` on the `R ⊗ C₂`-marginal). With its two
siblings this is the full triangle `|S(ρ) − S(ρ', E₂)| ≤ S(R''E₂'') ≤ S(ρ) + S(ρ', E₂)`, the
complete family of inequalities relating the escape quantity to the two standard quantities that
flank it. -/
theorem State.entropyExchange_dilatedChannel_le_crossEnvEntropy_add_vonNeumannEntropy
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) {D : QSystem}
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ ≤
      ρ.crossEnvEntropy U₁ ω₁ U₂ ω₂ + ρ.vonNeumannEntropy := by
  have hAL := State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le
    (State.congr (QSystem.assoc D _ Q)
      (State.congr (QSystem.Iso.comm _ D)
        (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedJoint U₂ ω₂))).reducedLeft
  rw [State.vonNeumannEntropy_reducedLeft_reducedLeft_dilatedJointReshape,
    State.vonNeumannEntropy_reducedLeft_reducedRight_dilatedJointReshape,
    State.reducedRight_dilatedChannelOnRight, State.refPurify_reducedRight,
    State.reducedLeft_dilatedChannelOnRight, State.vonNeumannEntropy_refPurify_reducedLeft] at hAL
  unfold State.crossEnvEntropy
  linarith

end AxQM
