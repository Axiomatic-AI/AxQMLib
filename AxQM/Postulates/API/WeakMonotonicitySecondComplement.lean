/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ReducedStateReshape
import AxQM.Postulates.API.WeakMonotonicity

/-!
# AxQM — the second complementarity identity `S(A,B) = S(C,R)` for weak monotonicity

Nielsen & Chuang **Exercise 11.24** (p. 521) derives weak monotonicity
`S(A) + S(C) ≤ S(A,B) + S(B,C)` (the "form-1" strong-subadditivity inequality, N&C eq. (11.107))
from strong subadditivity by **purifying** `ρ` on `A ⊗ (B ⊗ C)` with a reference `R` to a pure
four-party state `ψ` on `(A ⊗ (B ⊗ C)) ⊗ R`, applying strong subadditivity to the `R ⊗ (C ⊗ B)`
marginal, and rewriting the reference terms by pure-state complementarity. That derivation needs two
complementary-subsystem entropy identities on the pure four-party state:

* the **subsystem-`A` identity** `S(A) = S(R,B,C)`
  (`PureState.vonNeumannEntropy_reducedLeft_reducedLeft_eq_pullRefReshape`,
  `Postulates/API/WeakMonotonicity`, the `1‖3` split `A ‖ (R,B,C)`);
* the **`A⊗B` identity** `S(A,B) = S(C,R)` (this file, the balanced `2‖2` split
  `(A,B) ‖ (C,R)`).

## What this file provides

For a pure state `ψ` on `(A ⊗ (B ⊗ C)) ⊗ R`, split the four factors into the complementary pairs
`{A, B}` and `{C, R}`. The reshape `QSystem.abcrReshape` regroups `(A ⊗ (B ⊗ C)) ⊗ R` into
`(A ⊗ B) ⊗ (C ⊗ R)`, exposing those two blocks as the left and right factors; pure-state
complementarity (`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`, N&C Theorem 11.8(3))
then equates their marginal entropies:

`S(A,B) = S(C,R)`,

where the `A ⊗ B` marginal is read off as `(ρ.congr (assoc A B C)).reducedLeft` with `ρ := ψ`'s
`A ⊗ (B ⊗ C)`-marginal (`State.reducedLeft_congr_abcrReshape`), and the `C ⊗ R` marginal is the
`reducedRight` of the reshape.

* `QSystem.abcrReshape` — the reshape `(A ⊗ (B ⊗ C)) ⊗ R ≃ₛ (A ⊗ B) ⊗ (C ⊗ R)`;
* `State.reducedLeft_congr_abcrReshape` — the `A ⊗ B`-marginal of the reshape is the
  `A ⊗ B`-marginal of the `A ⊗ (B ⊗ C)`-marginal `ψ.reducedLeft`;
* `PureState.vonNeumannEntropy_ab_eq_cr` — the balanced complementarity `S(A,B) = S(C,R)`.

With `ψ := ρ.purify` (whose `A ⊗ (B ⊗ C)`-marginal is `ρ`, `State.purify_reducedLeft_eq`) this is
the `S(A,B) = S(R,C)` half of N&C Exercise 11.24. The reduced-state reshaping toolkit it uses is in
`ReducedStateReshape` and `ReducedStateTransport`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C R : QSystem}

/-- The **front-pair reshape** `(A ⊗ (B ⊗ C)) ⊗ R ≃ₛ (A ⊗ B) ⊗ (C ⊗ R)`: re-bracket the front
factor `A ⊗ (B ⊗ C)` to `(A ⊗ B) ⊗ C` and then de-associate the outer `⊗ R`, grouping the pair
`{A, B}` on the left and the complementary pair `{C, R}` on the right. On a purification of `ρ`
(with `R` the reference) this exposes both `ρ`'s `A ⊗ B` marginal and the complementary `C ⊗ R`
marginal of the pure four-party state — the two blocks whose entropies complementarity equates. -/
def QSystem.abcrReshape (A B C R : QSystem) :
    (((A ⊗ (B ⊗ C)) ⊗ R)) ≃ₛ ((A ⊗ B) ⊗ (C ⊗ R)) :=
  (QSystem.Iso.tmul (QSystem.assoc A B C) (QSystem.Iso.refl R)).trans
    ((QSystem.assoc (A ⊗ B) C R).symm)

/-- **`A ⊗ B`-marginal of the front-pair reshape.** For a state `ψ` on `(A ⊗ (B ⊗ C)) ⊗ R`,
`(ψ.congr (abcrReshape A B C R)).reducedLeft = (ψ.reducedLeft.congr (assoc A B C)).reducedLeft`: the
reshape only rearranges the non-`A⊗B` factors, so its `A ⊗ B`-marginal is the `A ⊗ B`-marginal of
`ψ`'s `A ⊗ (B ⊗ C)`-marginal. Combines `State.reducedLeft_congr_assoc_symm` (the outer
de-association leaves the left block alone) with `State.reducedLeft_congr_tmul_left` (the front
re-bracketing is carried through the trace) via `State.congr_trans`. -/
theorem State.reducedLeft_congr_abcrReshape (ψ : State ((A ⊗ (B ⊗ C)) ⊗ R)) :
    (State.congr (QSystem.abcrReshape A B C R) ψ).reducedLeft
      = (State.congr (QSystem.assoc A B C) ψ.reducedLeft).reducedLeft := by
  rw [QSystem.abcrReshape, State.congr_trans, State.reducedLeft_congr_assoc_symm,
    State.reducedLeft_congr_tmul_left]

/-- **Second complementarity identity `S(A,B) = S(C,R)`** (N&C Exercise 11.24, the `2‖2` half). For
a pure state `ψ` on `(A ⊗ (B ⊗ C)) ⊗ R`, the entropy of the `A ⊗ B` marginal equals the entropy of
the complementary `C ⊗ R` marginal of the pure four-party state:

`S(A,B) = S(C,R)`,

where `S(A,B) = S((ψ.reducedLeft.congr (assoc A B C)).reducedLeft)` (the `A ⊗ B`-marginal of `ψ`'s
`A ⊗ (B ⊗ C)`-marginal) and the `C ⊗ R` marginal is the `reducedRight` of the front-pair reshape
`QSystem.abcrReshape`. Immediate from pure-state complementarity
`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight` (N&C Theorem 11.8(3)) applied to the
reshaped pure state, whose `reducedLeft` is the `A ⊗ B` marginal by
`State.reducedLeft_congr_abcrReshape`. With `ψ := ρ.purify` this is the `S(A,B) = S(R,C)` step in
the derivation of weak monotonicity from strong subadditivity. -/
theorem PureState.vonNeumannEntropy_ab_eq_cr (ψ : PureState ((A ⊗ (B ⊗ C)) ⊗ R)) :
    (State.congr (QSystem.assoc A B C) ψ.toState.reducedLeft).reducedLeft.vonNeumannEntropy
      = (State.congr (QSystem.abcrReshape A B C R) ψ.toState).reducedRight.vonNeumannEntropy := by
  have h := PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight
    (PureState.congr (QSystem.abcrReshape A B C R) ψ)
  rwa [PureState.congr_toState, State.reducedLeft_congr_abcrReshape] at h

end AxQM
