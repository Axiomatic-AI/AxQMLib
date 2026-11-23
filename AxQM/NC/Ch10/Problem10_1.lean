/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.RandomUnitaryChannel
import AxQM.Postulates.API.ProjectiveRecovery

/-!
# Nielsen & Chuang, Problem 10.1 — channel equivalence and error-correction

Channel equivalence E2=U∘E1∘V is an equivalence relation; turn EC code for E1 into one for E2.

A **unitary channel** is the state map `ρ ↦ U ρ U†` induced by a unitary `Evolution U`
(`Evolution.evolve`). Two channels `E₁`, `E₂` are **equivalent** when a unitary channel can be
applied *before* and *after* one to obtain the other: `E₂ = U ∘ E₁ ∘ V` for unitary channels
`U`, `V`.

## This file

This file collects the formalisation of Problem 10.1.

**Part (1)** — channel equivalence is an equivalence relation:

* `AxQM.ChannelEquiv` — the channel-equivalence relation
  `∃ U V : Evolution S, ∀ ρ, E₂ ρ = U.evolve (E₁ (V.evolve ρ))`;
* `AxQM.channelEquiv_equivalence` — it is an **equivalence relation** (N&C 10.1(1));
* `AxQM.channelEquiv_isChannel` — it preserves being a **CPTP channel** (so the "channels
  `E₁`, `E₂`" of the problem statement stay channels under equivalence).

**Part (2)** — turning an error-correcting code for `E₁` into one for `E₂ = U ∘ E₁ ∘ V`:

* `AxQM.Corrects` — a *recovery* `R` corrects a channel `E` on a code `C` (a set of code
  states) when `R (E ρ) = ρ` for every `ρ ∈ C`;
* `AxQM.corrects_of_channelEquiv` — the abstract transfer: from any recovery `R₁` for `E₁`
  on `C`, the recovery `R₂ = V† ∘ R₁ ∘ U†` corrects `E₂` on the transported code `V† C` (this is the
  content of part (2) — a code/recovery for `E₁` becomes one for `E₂`);
* `AxQM.corrects_conjugate` — the same transfer for a recovery performed **in the assumed
  fashion**, "a projective measurement followed by a conditional unitary" (a
  `ProjectiveUnitaryRecovery`, in `AxQM/Postulates/API/ProjectiveRecovery.lean`):
  the transformed recovery
  `R.conjugate U V` — new syndrome `{U Mᵢ U†}`, new corrections `{V† Wᵢ U†}` — is again a projective
  measurement followed by a conditional unitary, and corrects `E₂`. So "the error-correction
  procedure for `E₂` can be performed in the same fashion."

### Design

`ChannelEquiv` is a relation on *arbitrary* state maps `State S → State S`: being an equivalence
relation is a purely relational fact that needs no completeness/positivity hypothesis, and stating
it unconditionally is the faithful reading of "the relation of channel equivalence is an
equivalence relation". That the equivalence class of a genuine channel consists of channels is the
separate `channelEquiv_isChannel`. The three laws use only the `Evolution` gate structure:
reflexivity from the identity gate (`Evolution.evolve_id`), symmetry from the adjoint (inverse)
gate and the two-sided cancellation `U (U† ρ U) U† = ρ` / `U† (U ρ U†) U = ρ`
(`Evolution.evolve_adjoint_evolve'` / `Evolution.evolve_adjoint_evolve`), and transitivity from
composing gates (`Evolution.evolve_comp`).

Part (2) is likewise stated for states and evolutions: `Corrects` and the two transfer theorems
use only `State`, `Evolution.evolve`, `Evolution.adjoint`, `Set.image`, and the recovery
`ProjectiveUnitaryRecovery.apply`/`.conjugate`. The correction condition is
phrased on arbitrary state maps `R`, `E` (a recovery is any map returning code states), so
`corrects_of_channelEquiv` needs no channel/measurement hypothesis; that a *concrete*
measurement-then-conditional-unitary recovery survives the transfer is the separate
`corrects_conjugate`, built on `ProjectiveUnitaryRecovery.apply_conjugate`
(`(R.conjugate U V).apply = V† ∘ R.apply ∘ U†`). The transported code `V† C = V.adjoint.evolve '' C`
is the image of `C` under the pre-gate's inverse, exactly matching `V ρ ∈ C₁` for `ρ ∈ V† C₁`. The
operator-level recovery machinery is in `AxQM/Postulates/API/ProjectiveRecovery.lean`.

N&C Problem 10.1, p. 495.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Channel equivalence** (Nielsen & Chuang, Problem 10.1). Two state maps `E₁, E₂ : State S →
State S` are *equivalent* when there are unitary channels `U`, `V` (unitary conjugations
`Evolution.evolve`, `ρ ↦ U ρ U†`) with `E₂ = U ∘ E₁ ∘ V`, i.e. `E₂ ρ = U.evolve (E₁ (V.evolve ρ))`
for every state `ρ`. Stated on arbitrary state maps (an equivalence relation regardless of complete
positivity); `channelEquiv_isChannel` records that it preserves being a genuine CPTP channel. -/
def ChannelEquiv (E₁ E₂ : State S → State S) : Prop :=
  ∃ U V : Evolution S, ∀ ρ : State S, E₂ ρ = U.evolve (E₁ (V.evolve ρ))

/-- **Channel equivalence is an equivalence relation** (Nielsen & Chuang, Problem 10.1(1)).

* *Reflexivity*: `E = id ∘ E ∘ id` — the identity gate acts trivially on states
  (`Evolution.evolve_id`).
* *Symmetry*: from `E₂ = U ∘ E₁ ∘ V` recover `E₁ = U† ∘ E₂ ∘ V†` using the adjoint (inverse) gates,
  since conjugating by a gate and then by its adjoint cancels
  (`Evolution.evolve_adjoint_evolve'`, `Evolution.evolve_adjoint_evolve`).
* *Transitivity*: composing `E₂ = U ∘ E₁ ∘ V` and `E₃ = U' ∘ E₂ ∘ V'` gives
  `E₃ = (U' U) ∘ E₁ ∘ (V V')`, folding the two pre- and post-gates with `Evolution.evolve_comp`. -/
theorem channelEquiv_equivalence : Equivalence (ChannelEquiv (S := S)) := by
  constructor
  · -- reflexivity: witnesses `U = V = id`
    intro E
    exact ⟨Evolution.id, Evolution.id, fun ρ => by
      rw [Evolution.evolve_id, Evolution.evolve_id]⟩
  · -- symmetry: witnesses `U† , V†`
    rintro E₁ E₂ ⟨U, V, h⟩
    exact ⟨U.adjoint, V.adjoint, fun ρ => by
      rw [h (V.adjoint.evolve ρ), Evolution.evolve_adjoint_evolve',
        Evolution.evolve_adjoint_evolve]⟩
  · -- transitivity: witnesses `U' U , V V'`
    rintro E₁ E₂ E₃ ⟨U, V, h⟩ ⟨U', V', h'⟩
    exact ⟨U'.comp U, V.comp V', fun ρ => by
      rw [h' ρ, h (V'.evolve ρ), Evolution.evolve_comp, Evolution.evolve_comp]⟩

/-- **Channel equivalence preserves being a CPTP channel.** If `E₁` is a quantum channel
(`IsChannel`) and `E₂` is equivalent to it (`ChannelEquiv E₁ E₂`), then `E₂` is a channel too.
Immediate from closure of channels under composition (`isChannel_comp`) and the fact that a unitary
conjugation is a channel (`isChannel_evolve`): `E₂ = U.evolve ∘ E₁ ∘ V.evolve`. This is why the
problem may speak of the equivalent objects `E₁`, `E₂` as *channels*. -/
theorem channelEquiv_isChannel {E₁ E₂ : State S → State S}
    (h₁ : IsChannel E₁) (h : ChannelEquiv E₁ E₂) : IsChannel E₂ := by
  obtain ⟨U, V, hUV⟩ := h
  have hE : E₂ = fun ρ => U.evolve (E₁ (V.evolve ρ)) := funext hUV
  rw [hE]
  exact isChannel_comp (isChannel_evolve U) (isChannel_comp h₁ (isChannel_evolve V))

/-! ### Part (2): transferring an error-correcting code from `E₁` to `E₂` -/

/-- **A recovery corrects a channel on a code** (Nielsen & Chuang, Problem 10.1(2)). A state map
`R : State S → State S` (the *recovery/error-correction procedure*) **corrects** the channel
`E : State S → State S` on the **code** `C` (the set of encoded/code states) when running the noise
then the recovery returns every code state unchanged: `R (E ρ) = ρ` for all `ρ ∈ C`. This is the
error-correction success condition; the code `C` together with a recovery `R` correcting `E` on it
is precisely "an error-correcting code for `E`". Stated on arbitrary state maps — the condition is a
plain functional identity on the code states, needing no completeness/positivity hypothesis. -/
def Corrects (R E : State S → State S) (C : Set (State S)) : Prop :=
  ∀ ρ ∈ C, R (E ρ) = ρ

/-- **Transferring an error-correcting code along a channel equivalence** (Nielsen & Chuang, Problem
10.1(2)). If `R₁` corrects `E₁` on a code `C`, and `E₂ = U ∘ E₁ ∘ V` is equivalent to `E₁` (the
witnesses `U`, `V` of `ChannelEquiv E₁ E₂`, i.e. `E₂ ρ = U (E₁ (V ρ V†)) U†`), then the recovery
`R₂ = V† ∘ R₁ ∘ U†` corrects `E₂` on the transported code `V† C` (`V.adjoint.evolve '' C`).

The computation: for `σ = V† ρ V` with `ρ ∈ C`,
`R₂ (E₂ σ) = V† (R₁ (U† (U (E₁ (V (V† ρ V) V†)) U†) U)) V = V† (R₁ (E₁ ρ)) V = V† ρ V = σ`, using
the two-sided unitary cancellations `V (V† ρ V) V† = ρ` (`Evolution.evolve_adjoint_evolve'`) and
`U† (U τ U†) U = τ` (`Evolution.evolve_adjoint_evolve`), and `R₁ (E₁ ρ) = ρ` (`R₁` corrects `E₁` on
`C ∋ ρ`). This is the abstract heart of part (2): a code/recovery for `E₁` becomes one for `E₂`. The
concrete "projective measurement then conditional unitary" form is preserved by
`corrects_conjugate`. -/
theorem corrects_of_channelEquiv {E₁ E₂ R₁ : State S → State S} {C : Set (State S)}
    (U V : Evolution S) (hE : ∀ ρ, E₂ ρ = U.evolve (E₁ (V.evolve ρ)))
    (hR : Corrects R₁ E₁ C) :
    Corrects (fun σ => V.adjoint.evolve (R₁ (U.adjoint.evolve σ))) E₂ (V.adjoint.evolve '' C) := by
  rintro σ ⟨ρ, hρ, rfl⟩
  simp only [hE, Evolution.evolve_adjoint_evolve', Evolution.evolve_adjoint_evolve, hR ρ hρ]

/-- **Turning a projective-measurement-then-conditional-unitary recovery for `E₁` into one for
`E₂`** (Nielsen & Chuang, Problem 10.1(2), the "same fashion" conclusion). If the recovery `R` — *a
projective measurement `{Mᵢ}` followed by a conditional unitary `{Wᵢ}`*
(`ProjectiveUnitaryRecovery`) — corrects `E₁` on a code `C`, then its transform `R.conjugate U V` —
*again a projective measurement `{U Mᵢ U†}` followed by a conditional unitary `{V† Wᵢ U†}}`* —
corrects the equivalent channel `E₂ = U ∘ E₁ ∘ V` on the transported code `V† C`.

So the error-correction procedure for `E₂` is performed in the *same fashion* as that for `E₁`: the
recovery is again `ProjectiveUnitaryRecovery.apply` of an explicit projective-measurement-plus-
conditional-unitary datum. The proof rewrites `(R.conjugate U V).apply` as
`V† ∘ R.apply ∘ U†` (`ProjectiveUnitaryRecovery.apply_conjugate`) and applies
`corrects_of_channelEquiv`. -/
theorem corrects_conjugate {ι : Type*} [Fintype ι] {E₁ : State S → State S} {C : Set (State S)}
    (R : ProjectiveUnitaryRecovery ι S) (U V : Evolution S) (hR : Corrects R.apply E₁ C) :
    Corrects (R.conjugate U V).apply (fun ρ => U.evolve (E₁ (V.evolve ρ)))
      (V.adjoint.evolve '' C) := by
  have hfun : (R.conjugate U V).apply
      = fun σ => V.adjoint.evolve (R.apply (U.adjoint.evolve σ)) :=
    funext fun σ => R.apply_conjugate U V σ
  rw [hfun]
  exact corrects_of_channelEquiv U V (fun _ => rfl) hR

end AxQM
