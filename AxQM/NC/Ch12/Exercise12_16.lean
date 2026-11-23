/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Exercise12_15
import AxQM.NC.Ch12.Theorem12_10

/-!
# N&C Exercise 12.16 — equality in the error-correction entropy bound

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 12.16, p. 571.

Show S(rho)-S(rho')+S(rho',R) >= 0 holds with equality when R perfectly corrects E.

## The formalisation

The declarations in this file for Exercise 12.16 are:

* `State.IsPerfectlyCorrected` — the predicate "`R` perfectly corrects `E` for `ρ`" (entanglement
  fidelity `F(ρ, R ∘ E) = 1`, purification form);
* `State.vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_nonneg` — N&C eq. (12.153),
  `0 ≤ S(ρ) − S(ρ') + S(ρ', R)` under cycle closure;
* `State.vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_eq_zero_of_perfectCorrection` —
  Exercise 12.16 proper, the balance `= 0` under perfect correction.

The §12.4 lemmas these use — the entropy-exchange triangle inequalities, coherent
information, and data-processing — are in `AxQM/NC/Ch12/Exercise12_15.lean`,
`AxQM/NC/Ch12/CoherentInformation.lean` and `AxQM/NC/Ch12/Theorem12_10.lean`.

Here `E` is the noise process `ρ → ρ' = E(ρ)`, `R` is the recovery operation, `S(ρ)` and `S(ρ')` are
von Neumann entropies, and `S(ρ', R)` is the **entropy exchange** of the recovery `R` on its input
`ρ'` (N&C §12.4.1). Inequality (12.152)/(12.153) is N&C eq. (12.144) — `ΔS + S(σ, R) ≥ 0` — applied
to the operation `R` at input `σ = ρ'`, using `S(R(ρ')) = S(ρ)` when `R` closes the cycle.

## Presentation of the operations (as throughout §12.4)

Each operation is presented by its Chapter-8 dilation — a unitary `U` on `Q ⊗ Cᵢ` with the ancilla
`Cᵢ` in a pure state `ωᵢ` — (the library has no quantifier over abstract
trace-preserving maps). So the noise `E` is `(U₁, ω₁)` and the recovery `R` is `(U₂, ω₂)`, and:

* `ρ' = E(ρ) = ρ.dilatedChannel U₁ ω₁`;
* `R(ρ') = (E₂ ∘ E₁)(ρ) = ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂`;
* `S(ρ', R) = (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂` (entropy exchange of `R` at `ρ'`).

## "`R` perfectly corrects `E` for the input `ρ`"

`State.IsPerfectlyCorrected` encodes this as the **entanglement fidelity `F(ρ, R ∘ E) = 1`** in its
purification form: applying the composite `R ∘ E` to the system factor of the reference purification
`|RQ⟩ = refPurify ρ` restores it *exactly*, so the final reference–system state `R''Q''` equals the
original `|RQ⟩⟨RQ|`:
`((refPurify ρ).dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂ = refPurify ρ`. This is
Schumacher's characterisation of perfect quantum error-correction — not merely the state `ρ` but its
full entanglement with a reference is recovered.

The equality proof consumes only two *consequences* of `F = 1`, both of which N&C itself derives
from it (p. 566: `ρ'' = ρ`, and via the quantum Fano inequality `S(ρ, R ∘ E) = 0`):

1. `ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂ = ρ` — state restoration, the right marginal of
   `R''Q'' = refPurify ρ` (N&C's cycle condition `ρ'' = ρ`); and
2. `ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ = 0` — the composite entropy exchange `S(ρ, R ∘ E)` vanishes,
   since `R''Q'' = refPurify ρ` is pure.

So the equality in fact holds under the strictly weaker hypothesis (1) ∧ (2), and the theorem is a
faithful *generalisation* of the exercise — but the hypothesis is stated as genuine perfect
correction (`F = 1`) to match N&C's framing. **(1) ∧ (2) alone is not perfect correction**: a
bit-flip `R ∘ E = X(·)X` on `ρ = I/2` satisfies both (`X(I/2)X = I/2`, and `(I ⊗ X)|Φ⁺⟩ = |Ψ⁺⟩` is
pure) yet has `F = |⟨Φ⁺|Ψ⁺⟩|² = 0` and corrects nothing; it is condition `F = 1`, i.e.
`R''Q'' = refPurify ρ` (here `|Ψ⁺⟩ ≠ |Φ⁺⟩`), that excludes it.

## The two claims

* **N&C eq. (12.153)** — `State.vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_nonneg` :
  `0 ≤ S(ρ) − S(ρ') + S(ρ', R)` whenever the recovery closes the cycle (`(R ∘ E)(ρ) = ρ`). This is
  eq. (12.144) for `R` at `ρ'`, `S(ρ') ≤ S(R(ρ')) + S(ρ', R)`
  (`State.vonNeumannEntropy_le_dilatedChannel_add_entropyExchange`), with `S(R(ρ')) = S(ρ)`.
* **Exercise 12.16** —
  `State.vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_eq_zero_of_perfectCorrection` :
  `S(ρ) − S(ρ') + S(ρ', R) = 0` when `R` perfectly corrects `E`. From `F = 1` we read off (1) and
  (2) above; then the reverse `≤ 0`, i.e. `S(ρ', R) ≤ S(ρ') − S(ρ)`, is where reversibility (2)
  bites: the entropy-exchange triangle inequality `S(ρ', R) ≤ S(ρ, E) + S(ρ, R ∘ E)`
  (`State.entropyExchange_dilatedChannel_le_entropyExchange_add_entropyExchangeComp`, the
  two-environment combination of Exercise 12.15) collapses under (2) to `S(ρ', R) ≤ S(ρ, E)`; and
  (1)+(2) force the first
  data-processing inequality tight — `I(ρ, R ∘ E) = S(ρ)`, squeezed against
  `State.coherentInfoComp_le_coherentInfo` and bounded by `S(ρ)`, gives `I(ρ, E) ≥ S(ρ)`, i.e.
  `S(ρ, E) ≤ S(ρ') − S(ρ)`. Chaining yields the reverse of (12.153).

## Related declarations

The statements use `State.dilatedChannel`, `State.dilatedChannelComp`, `State.entropyExchange`,
`State.entropyExchangeComp`, `State.coherentInfo(Comp)` and `State.vonNeumannEntropy`. The
predicate `State.IsPerfectlyCorrected`, like `State.entropyExchange`, uses the purification
reference `State.refPurify` only inside its definition. The shared §12.4 results — including the
entropy-exchange triangle inequalities on the joint `(R ⊗ Q) ⊗ C₂` state — are in
`AxQM/NC/Ch12/CoherentInformation.lean`, `AxQM/NC/Ch12/Exercise12_15.lean` and
`AxQM/NC/Ch12/Theorem12_10.lean`.
-/

noncomputable section

namespace AxQM

variable {Q C D : QSystem}

/-- **"The recovery `R` perfectly corrects the noise `E` for the input `ρ`"** — the entanglement
fidelity `F(ρ, R ∘ E) = 1`, in purification form. With `E = (U₁, ω₁)` and `R = (U₂, ω₂)`, the
composite `R ∘ E` applied to the system factor of the reference purification `|RQ⟩ = refPurify ρ`
restores it exactly, `R''Q'' = |RQ⟩⟨RQ|`:

`((refPurify ρ).dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂ = refPurify ρ`.

This is Schumacher's condition for perfect quantum error-correction: the full state *and its
entanglement with a reference* are recovered. Its two consequences — state restoration
`dilatedChannelComp = ρ` (N&C's `ρ'' = ρ`, the right marginal of `R''Q''`) and the vanishing
composite entropy exchange `entropyExchangeComp = 0` (`R''Q''` pure) — are what the equality proof
consumes; N&C derives both from `F = 1` (p. 566). Strictly stronger than that pair: a bit-flip
`X(·)X` on `ρ = I/2` satisfies the pair yet has `F = 0`, so is *not* perfect correction. -/
def State.IsPerfectlyCorrected (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C)
    (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D) : Prop :=
  ((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight U₂ ω₂
    = (State.refPurify ρ).toState

/-- **N&C eq. (12.153): the error-correction entropy bound.** When the recovery `R` closes the cycle
— `(R ∘ E)(ρ) = ρ`, i.e. `ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂ = ρ` — the change in the system entropy
during error-correction plus the entropy exchange of the recovery is non-negative:

`0 ≤ S(ρ) − S(ρ') + S(ρ', R)`,

with `ρ' = E(ρ) = ρ.dilatedChannel U₁ ω₁` and `S(ρ', R) = (ρ.dilatedChannel U₁ ω₁).entropyExchange`.
This is N&C eq. (12.144) — `ΔS + S(σ, R) ≥ 0`
(`State.vonNeumannEntropy_le_dilatedChannel_add_entropyExchange`) — applied to `R` at input
`σ = ρ'`: `S(ρ') ≤ S(R(ρ')) + S(ρ', R)`, and `R(ρ') = (R ∘ E)(ρ) = ρ` makes `S(R(ρ')) = S(ρ)`. The
cycle-closure hypothesis is exactly the first consequence of perfect correction
(`State.IsPerfectlyCorrected`). -/
theorem State.vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_nonneg (ρ : State Q)
    (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) (U₂ : Evolution (Q ⊗ D)) (ω₂ : PureState D)
    (hcorr : ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂ = ρ) :
    0 ≤ ρ.vonNeumannEntropy - (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy +
      (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ := by
  have hcc : (ρ.dilatedChannel U₁ ω₁).dilatedChannel U₂ ω₂ = ρ := hcorr
  have h := (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy_le_dilatedChannel_add_entropyExchange U₂ ω₂
  rw [hcc] at h
  linarith

/-- **N&C Exercise 12.16.** When the recovery `R` *perfectly* corrects the noise `E` for the input
`ρ` (`State.IsPerfectlyCorrected`, i.e. entanglement fidelity `F(ρ, R ∘ E) = 1`), the
error-correction entropy bound (12.153) holds with equality:

`S(ρ) − S(ρ') + S(ρ', R) = 0`,

with `ρ' = E(ρ) = ρ.dilatedChannel U₁ ω₁` and `S(ρ', R) = (ρ.dilatedChannel U₁ ω₁).entropyExchange`.

From `F = 1` (`R''Q'' = refPurify ρ`) we read off its two consequences: the state restoration
`hcorr : dilatedChannelComp = ρ` (the right marginal of both sides,
`State.reducedRight_dilatedChannelOnRight` + `State.refPurify_reducedRight`) and the vanishing
composite entropy exchange `hrev : entropyExchangeComp = 0` (`R''Q'' = refPurify ρ` is pure,
`PureState.vonNeumannEntropy_toState_eq_zero`). The `≥ 0` direction is then (12.153)
(`State.vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_nonneg` at `hcorr`). The reverse
`≤ 0`, i.e. `S(ρ', R) ≤ S(ρ') − S(ρ)`, is where reversibility (`hrev`) bites, via two facts:

* the **entropy-exchange triangle inequality**
  `S(ρ', R) ≤ S(ρ, E) + S(ρ, R ∘ E)`
  (`State.entropyExchange_dilatedChannel_le_entropyExchange_add_entropyExchangeComp`) collapses to
  `S(ρ', R) ≤ S(ρ, E)` since `S(ρ, R ∘ E) = 0`; and
* the **first data-processing inequality is tight**: `I(ρ, R ∘ E) = S(ρ)` (from `hcorr`, `hrev`:
  `S(ρ'') = S(ρ)` and `S(ρ, R ∘ E) = 0`), squeezed against `I(ρ, R ∘ E) ≤ I(ρ, E)`
  (`State.coherentInfoComp_le_coherentInfo`), forces `I(ρ, E) ≥ S(ρ)`, i.e.
  `S(ρ, E) ≤ S(ρ') − S(ρ)`.

Chaining the two gives `S(ρ', R) ≤ S(ρ') − S(ρ)`, the reverse inequality. -/
theorem State.vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_eq_zero_of_perfectCorrection
    (ρ : State Q) (U₁ : Evolution (Q ⊗ C)) (ω₁ : PureState C) (U₂ : Evolution (Q ⊗ D))
    (ω₂ : PureState D) (h : ρ.IsPerfectlyCorrected U₁ ω₁ U₂ ω₂) :
    ρ.vonNeumannEntropy - (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy +
      (ρ.dilatedChannel U₁ ω₁).entropyExchange U₂ ω₂ = 0 := by
  unfold State.IsPerfectlyCorrected at h
  -- The two consequences of `F = 1` (`R''Q'' = refPurify ρ`) that N&C derives (p. 566).
  have hcorr : ρ.dilatedChannelComp U₁ ω₁ U₂ ω₂ = ρ := by
    have hr := congrArg State.reducedRight h
    rw [State.reducedRight_dilatedChannelOnRight, State.reducedRight_dilatedChannelOnRight,
      State.refPurify_reducedRight] at hr
    exact hr
  have hrev : ρ.entropyExchangeComp U₁ ω₁ U₂ ω₂ = 0 := by
    unfold State.entropyExchangeComp
    rw [h]
    exact (State.refPurify ρ).vonNeumannEntropy_toState_eq_zero
  -- `≥ 0`: N&C eq. (12.153).
  have hge := ρ.vonNeumannEntropy_sub_dilatedChannel_add_entropyExchange_nonneg U₁ ω₁ U₂ ω₂ hcorr
  -- Perfect correction forces the composite coherent information to equal `S(ρ)`.
  have hcohComp : ρ.coherentInfoComp U₁ ω₁ U₂ ω₂ = ρ.vonNeumannEntropy := by
    have hcc : (ρ.dilatedChannel U₁ ω₁).dilatedChannel U₂ ω₂ = ρ := hcorr
    have hev : (((State.refPurify ρ).toState.dilatedChannelOnRight U₁ ω₁).dilatedChannelOnRight
        U₂ ω₂).vonNeumannEntropy = 0 := hrev
    unfold State.coherentInfoComp
    rw [State.coherentInfoOfState_def, State.reducedRight_dilatedChannelOnRight,
      State.reducedRight_dilatedChannelOnRight, State.refPurify_reducedRight, hcc, hev]
    ring
  -- Data-processing (Theorem 12.10, second stage): `I(ρ, R ∘ E) ≤ I(ρ, E)`.
  have hdpi := ρ.coherentInfoComp_le_coherentInfo U₁ ω₁ U₂ ω₂
  -- Coherent-information definition: `I(ρ, E) = S(ρ') − S(ρ, E)`.
  have hcoh : ρ.coherentInfo U₁ ω₁
      = (ρ.dilatedChannel U₁ ω₁).vonNeumannEntropy - ρ.entropyExchange U₁ ω₁ := rfl
  -- Entropy-exchange triangle inequality collapsed by `S(ρ, R ∘ E) = 0`.
  have htri :=
    ρ.entropyExchange_dilatedChannel_le_entropyExchange_add_entropyExchangeComp U₁ ω₁ U₂ ω₂
  linarith [hge, hcohComp, hdpi, hcoh, htri, hrev]

end AxQM
