/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite
import AxQM.Postulates.SystemIso
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.API.ReducedStateComm
import AxQM.Postulates.API.PureMarginalEntropy

/-!
# Reference purification with the reference on the left (N&C §12.4.1)

Nielsen & Chuang's discussion of entropy exchange and coherent information (§12.4.1–12.4.2)
introduces a *reference system* `R` and a purification `|RQ⟩` of the input state `ρ` on `Q`,
written with the reference `R` as the **first** factor so that a quantum operation `E` on `Q`
acts on the *right* factor of `R ⊗ Q` (matching `State.dilatedChannelOnRight`, whose channel acts
on the right).

The library's canonical purification `State.purify` places the ancilla on the *right*
(`ρ.purify : PureState (Q ⊗ R)`, left marginal `ρ`). This file wraps it with the swap isomorphism
`QSystem.Iso.comm` to obtain the reference-on-the-left form `State.refPurify ρ : PureState (R ⊗ Q)`,
together with the two facts the entropy-exchange development needs:

* `State.refPurify_reducedRight` — the `Q`-marginal (right factor) of `refPurify ρ` is `ρ`;
* `State.vonNeumannEntropy_refPurify_reducedLeft` — the reference marginal `R` is isentropic with
  `ρ`, `S(R) = S(ρ)`, since `refPurify ρ` is pure and complementary marginals of a pure state share
  their entropy.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Reference purification with the reference on the left.** For a state `ρ` on `S`, this is the
canonical purification `ρ.purify` (a pure state on `S ⊗ R` with left marginal `ρ`) with its two
factors swapped, giving a pure state on `R ⊗ S` — the reference `R` first, the system `S` second.
Nielsen & Chuang §12.4.1 use exactly this ordering `|RQ⟩` so that a quantum operation on the system
acts on the right factor. -/
def State.refPurify (ρ : State S) :
    PureState ((QSystem.ofModel (EuclideanSpace ℂ (Fin S.dim))).compose S) :=
  PureState.congr (QSystem.Iso.comm S _) ρ.purify

/-- The system marginal of the reference purification is the original state: tracing out the
reference `R` (the left factor of `R ⊗ S`) from `refPurify ρ` recovers `ρ`. Since `refPurify` is
`ρ.purify` with the factors swapped and `ρ.purify` has left marginal `ρ`
(`State.purify_reducedLeft_eq`), the swap turns that left marginal into the right marginal
(`State.reducedLeft_congr_comm`). -/
theorem State.refPurify_reducedRight (ρ : State S) :
    (State.refPurify ρ).toState.reducedRight = ρ := by
  rw [State.refPurify, PureState.congr_toState, ← State.reducedLeft_congr_comm,
    State.purify_reducedLeft_eq]

/-- The reference marginal of the reference purification is isentropic with the state:
`S(R) = S(ρ)`. As `refPurify ρ` is pure on `R ⊗ S`, its two reduced states share their von Neumann
entropy (`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`, N&C Theorem 11.8(3)), and the
`S`-marginal is `ρ` (`State.refPurify_reducedRight`). -/
theorem State.vonNeumannEntropy_refPurify_reducedLeft (ρ : State S) :
    (State.refPurify ρ).toState.reducedLeft.vonNeumannEntropy = ρ.vonNeumannEntropy := by
  rw [PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight, State.refPurify_reducedRight]

end AxQM
