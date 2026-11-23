/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.CoherentInformation

/-!
# N&C Theorem 12.10 — the quantum data processing inequality

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 12.10, p. 564.

For a quantum state `ρ` and trace-preserving quantum operations `E1`, `E2`, the coherent information
`I(ρ, E) = S(E(ρ)) − S(ρ, E)` (N&C eq. (12.118)) obeys the two-stage chain

`S(ρ) ≥ I(ρ, E1) ≥ I(ρ, E2 ∘ E1)`  (eq. (12.119)),

the quantum analogue of the classical data processing inequality `H(X) ≥ H(X:Y) ≥ H(X:Z)` for a
Markov chain `X → Y → Z`. This file formalises this inequality chain;
N&C's additional clause — equality in the first inequality iff `E1` is perfectly
reversible on `ρ` (Exercise 12.16) — is a separate characterisation and is not formalised here.

## The formalisation (two named claims)

The two inequalities of the chain are the two claims, stated as separate theorems.

* **First inequality** `S(ρ) ≥ I(ρ, E1)` — `AxQM.State.coherentInfo_le_vonNeumannEntropy`
  (`NC/Ch12/CoherentInformation.lean`). N&C's subadditivity argument (12.122)–(12.126) in the
  purification picture: with `R'Q' = (refPurify ρ).dilatedChannelOnRight U₁ ω₁`, the Araki–Lieb
  triangle inequality bounds `I(ρ, E1) = S(Q') − S(R'Q')` by `S(R') = S(ρ)`.
* **Second inequality** `I(ρ, E1) ≥ I(ρ, E2 ∘ E1)` — `State.coherentInfoComp_le_coherentInfo`
  (below). N&C's strong-subadditivity argument (12.127)–(12.131). Both coherent informations are
  read as the state coherent information `I(A⟩B) = S(B) − S(A,B)` of the reference–system state
  (`State.coherentInfoComp`; the identification of `I(ρ, E1)` is derived in the proof body), and the
  inequality is the monotonicity of `I(A⟩B)` under a channel on `B`
  (`State.coherentInfoOfState_dilatedChannelOnRight_le`) instantiated at `σ = R'Q'`.

## Presentation of the operations and the composition

As throughout §12.4 (the library has no abstract "every trace-preserving map has a
Kraus/dilation form" to quantify over), each operation is presented by its Chapter-8 dilation — a
unitary `U` on `Q ⊗ Cᵢ` with the environment `Cᵢ` prepared in a pure state `ωᵢ`. The composition
`E2 ∘ E1` is realised by applying the two dilations in sequence to the system factor of the
reference purification (`State.coherentInfoComp`), which is faithful to N&C's four-system dynamics
(`Q` interacts with `E1`, then with `E2`, while the reference `R` is untouched) and makes
`S(ρ, E2 ∘ E1) = S(R''Q'')` hold by the framework's purification definition of the entropy exchange.

The data processing infrastructure — `State.coherentInfoOfState`, the dilation marginal lemmas,
the coherent-information definitions and monotonicity — is in
`AxQM/Core/ConditionalEntropy.lean` and `AxQM/NC/Ch12/CoherentInformation.lean`; this file states
the second inequality and assembles the theorem.
-/

noncomputable section

namespace AxQM

variable {Q C : QSystem}

/-- **Second inequality of the quantum data processing inequality** (Nielsen & Chuang Theorem 12.10,
eq. (12.119), second stage):

`I(ρ, E2 ∘ E1) ≤ I(ρ, E1)`.

The composed coherent information `I(ρ, E2 ∘ E1)` (`State.coherentInfoComp`, the state coherent
information of the twice-processed reference–system state `R''Q''`) is at most the single-channel
coherent information `I(ρ, E1)` (`ρ.coherentInfo U₁ ω₁`). This is N&C's strong-subadditivity
argument (12.127)–(12.131): rewriting `I(ρ, E1)` as the state coherent information `I(R'⟩Q')` of
`R'Q' = (refPurify ρ).dilatedChannelOnRight U₁ ω₁` (an in-body step, from the dilation marginal
identities and `State.refPurify_reducedRight`), the claim is the monotonicity of the state
coherent information under the channel `E2` acting on the system factor `Q'`
(`State.coherentInfoOfState_dilatedChannelOnRight_le`), whose engine is strong subadditivity.

Together with `State.coherentInfo_le_vonNeumannEntropy` (the first inequality `S(ρ) ≥ I(ρ, E1)`)
this gives the full chain `S(ρ) ≥ I(ρ, E1) ≥ I(ρ, E2 ∘ E1)`. -/
theorem State.coherentInfoComp_le_coherentInfo (ρ : State Q) (U₁ : Evolution (Q ⊗ C))
    (ω₁ : PureState C) {D : QSystem} (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) :
    ρ.coherentInfoComp U₁ ω₁ U₂ ω₂ ≤ ρ.coherentInfo U₁ ω₁ := by
  unfold State.coherentInfoComp
  -- `I(ρ, E1) = I(R'⟩Q')`: the single-channel coherent information is the state coherent info
  -- of the processed purification; cf. `State.entropyExchange`.
  have hEq : ρ.coherentInfo U₁ ω₁
      = ((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).coherentInfoOfState := by
    unfold State.coherentInfo State.entropyExchange
    rw [State.coherentInfoOfState_def, State.reducedRight_dilatedChannelOnRight,
      State.refPurify_reducedRight]
  rw [hEq]
  exact State.coherentInfoOfState_dilatedChannelOnRight_le _ U₂ ω₂

end AxQM
