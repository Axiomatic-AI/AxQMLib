/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ReducedStateTransport
import AxQM.Postulates.API.PureMarginalEntropy
import AxQM.Postulates.Composite

/-!
# AxQM — purification-marginal reshaping toward weak monotonicity (N&C Exercise 11.24)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Exercise 11.24** (p. 521) asks to
derive the "form-1" strong-subadditivity inequality — **weak monotonicity**

`S(A) + S(B) ≤ S(A,C) + S(B,C)`  (N&C eq. (11.107))

as a *consequence* of strong subadditivity `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)` (eq. (11.108),
formalised faithfulness-free as `State.vonNeumannEntropy_add_le_add'`). N&C's derivation is the
mirror of the forward one: introduce a reference `R` **purifying** `ABC`, apply strong subadditivity
to the tripartite `(R, B, C)` marginal,

`S(R,B,C) + S(B) ≤ S(R,B) + S(B,C)`,

and rewrite the two `R`-terms by the pure-state complementary-subsystem identity
(`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`, N&C Theorem 11.8(3)): on the pure
four-party state `ABCR`, `S(R,B,C) = S(A)` and `S(R,B) = S(A,C)`, giving eq. (11.107).

## What this file provides

This file proves the **reference-pull reshape** and the **subsystem-`A`
purity identity** `S(A) = S(R,B,C)`. Concretely, for the purification `ρ.purify` on
`(A ⊗ (B ⊗ C)) ⊗ R`, the `R ⊗ (B ⊗ C)` marginal — the state to which strong subadditivity is
applied — is read off after the reshape `pullRefReshape`, and this file proves its entropy is
`S(A)`. The generic `reducedLeft` reshaping lemmas this rests on
(`State.reducedLeft_congr_tmul_refl`, `State.congr_trans`,
`State.reducedLeft_congr_assoc_symm`) are in `AxQM/Postulates/API/ReducedStateTransport.lean`.

* `QSystem.pullRefReshape` — the reshape `(A ⊗ M) ⊗ R ≃ₛ A ⊗ (R ⊗ M)` bringing the reference `R`
  beside `M` (used with `M := B ⊗ C`);
* `State.reducedLeft_congr_pullRefReshape` — the `A`-marginal of the `pullRefReshape` reshape is
  the iterated `A`-marginal `reducedLeft.reducedLeft`;
* `PureState.vonNeumannEntropy_reducedLeft_reducedLeft_eq_pullRefReshape` — the purity identity
  `S(A) = S(R ⊗ M-marginal)` for a pure state on `(A ⊗ M) ⊗ R`.

The complementary `reducedRight`-side identities (`S(B,C)`, `S(B)`, `S(A,C) = S(R,B)`) require the
`partialTraceLeft` counterparts of the reassociation lemmas and are proved separately, in
`AxQM/Postulates/API/WeakMonotonicityReducedRight.lean` and
`AxQM/Postulates/API/WeakMonotonicitySecondComplement.lean`; weak monotonicity itself is assembled
in `AxQM/NC/Ch11/Exercise11_24.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C R : QSystem}

/-- The **reference-pull reshape** `(A ⊗ M) ⊗ R ≃ₛ A ⊗ (R ⊗ M)`: re-bracket to `A ⊗ (M ⊗ R)`, then
swap the inner pair to bring the reference `R` beside `M`. For a purification on
`(A ⊗ (B ⊗ C)) ⊗ R` (with `M := B ⊗ C`) this exposes the `R ⊗ (B ⊗ C)` marginal — the tripartite
state to which strong subadditivity is applied in N&C Exercise 11.24 — as the `reducedRight` of the
reshape. -/
def QSystem.pullRefReshape (A M R : QSystem) : ((A ⊗ M) ⊗ R) ≃ₛ (A ⊗ (R ⊗ M)) :=
  (QSystem.assoc A M R).symm.trans (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm M R))

/-- **`A`-marginal of the reference-pull reshape.** `(congr (pullRefReshape A M R) ρ).reducedLeft =
ρ.reducedLeft.reducedLeft`: the reshape only rearranges the non-`A` factors, so the `A`-marginal is
the iterated `A`-marginal of `ρ`. Combines `State.reducedLeft_congr_tmul_refl` (the swap leaves the
`A`-marginal alone) with `State.reducedLeft_congr_assoc_symm` (the re-bracketing) through
`State.congr_trans`. -/
theorem State.reducedLeft_congr_pullRefReshape {A M R : QSystem} (ρ : State ((A ⊗ M) ⊗ R)) :
    (State.congr (QSystem.pullRefReshape A M R) ρ).reducedLeft = ρ.reducedLeft.reducedLeft := by
  rw [QSystem.pullRefReshape, State.congr_trans, State.reducedLeft_congr_tmul_refl,
    State.reducedLeft_congr_assoc_symm]

/-- **Subsystem-`A` purity identity** (N&C Exercise 11.24, the `S(R,B,C) = S(A)` step). For a pure
state `ψ` on `(A ⊗ M) ⊗ R`, the entropy of the subsystem `A` equals the entropy of the `R ⊗ M`
marginal (the complement of `A` in the pure four-party state):

`S(A) = S(R ⊗ M-marginal)`,

where `S(A) = S(ψ.reducedLeft.reducedLeft)` and the `R ⊗ M` marginal is read off as the
`reducedRight` of the `pullRefReshape` reshape. Immediate from the pure-state
complementary-subsystem identity `PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight` applied
to the reshaped pure state, whose `reducedLeft` is `S(A)` by
`State.reducedLeft_congr_pullRefReshape`. With `M := B ⊗ C` and `ψ := ρ.purify` this is the
`S(A) = S(R,B,C)` half of the derivation of weak monotonicity from strong subadditivity. -/
theorem PureState.vonNeumannEntropy_reducedLeft_reducedLeft_eq_pullRefReshape {A M R : QSystem}
    (ψ : PureState ((A ⊗ M) ⊗ R)) :
    ψ.toState.reducedLeft.reducedLeft.vonNeumannEntropy =
      (State.congr (QSystem.pullRefReshape A M R) ψ.toState).reducedRight.vonNeumannEntropy := by
  have h := PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight
    (PureState.congr (QSystem.pullRefReshape A M R) ψ)
  rwa [PureState.congr_toState, State.reducedLeft_congr_pullRefReshape] at h

end AxQM
