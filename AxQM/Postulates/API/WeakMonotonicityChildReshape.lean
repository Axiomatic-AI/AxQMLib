/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.WeakMonotonicityReducedRight
import AxQM.Postulates.API.ReducedStateReshape

/-!
# AxQM — the `wmChildReshape` marginal toolkit for the "child-form" weak monotonicity

Nielsen & Chuang **Exercise 11.24** (p. 521) derives weak monotonicity from strong subadditivity by
purifying a state `ρ` on `A ⊗ (B ⊗ C)` with a reference `R` and applying strong subadditivity to the
`{B, C, R}` marginal of the purification. There are two symmetric ways to expose that marginal, and
the arithmetic of the resulting inequality depends on the choice:

* the **`R ⊗ (B ⊗ C)`** arrangement (`QSystem.pullRefReshape`, `Postulates/API/WeakMonotonicity`)
  yields the "parent" inequality `S(A) + S(B) ≤ S(A,C) + S(B,C)` (needs the `S(R,B) = S(A,C)`
  identity);
* the **`B ⊗ (C ⊗ R)`** arrangement (`QSystem.wmChildReshape`) yields the "child" inequality
  `S(A) + S(C) ≤ S(A,B) + S(B,C)` — all four marginals of which (`A`, `C`, `A ⊗ B`, `B ⊗ C`) are
  *adjacent* marginals of `ρ`, so the assembly avoids the awkward non-adjacent `A ⊗ C` block, and
  the `{C,R}`-complementarity it needs is exactly `S(A,B) = S(C,R)`
  (`PureState.vonNeumannEntropy_ab_eq_cr`).

## What this file provides

For the reshape `QSystem.wmChildReshape : (A ⊗ (B ⊗ C)) ⊗ R ≃ₛ A ⊗ (B ⊗ (C ⊗ R))` (which exposes the
subsystem `A` on the left and the `B ⊗ (C ⊗ R)` block on the right, so the `{B,C,R}` marginal is the
`reducedRight` of the reshape), this file computes the three marginals of that block that strong
subadditivity reads off, back onto the original state's own marginals:

* `State.reducedLeft_congr_wmChildReshape` — the `A`-marginal of the reshape is the iterated
  `A`-marginal (`reducedLeft.reducedLeft`); with purity this gives the `S(A)` term.
* `State.reducedRight_congr_wmChildReshape` — the `{B,C,R}` marginal `σ`, written as a
  transported `(B ⊗ C) ⊗ R` marginal (the identity that lets the other two be read off).
* `State.reducedRight_reducedLeft_congr_wmChildReshape` — the `C`-marginal
  `σ.reducedRight.reducedLeft = S(C)` is `ρ`'s own `C`-marginal.
* `State.reducedLeft_congr_assoc_wmChildReshape` — the `B ⊗ C`-marginal
  `(σ.congr (assoc B C R)).reducedLeft = S(B,C)` is `ρ`'s own `B ⊗ C`-marginal.

The `S(B,C)` and `S(C)` identities are the marginal-consistency facts that turn the two
strong-subadditivity terms produced on `σ` into `ρ`'s marginals. They both reduce to the
trace-commutation lemma `State.reducedRight_reducedLeft_congr_assoc_symm`
(`Postulates/API/WeakMonotonicityReducedRight`, "trace `A` then `R` = trace `R` then `A`") after the
reshape is peeled off with `State.reducedRight_congr_tmul_right`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C R : QSystem}

/-- The **child-form reshape** `(A ⊗ (B ⊗ C)) ⊗ R ≃ₛ A ⊗ (B ⊗ (C ⊗ R))`: de-associate the outer
`⊗ R` to `A ⊗ ((B ⊗ C) ⊗ R)`, then re-bracket the right block `(B ⊗ C) ⊗ R` to `B ⊗ (C ⊗ R)`. On a
purification of `ρ` (with `R` the reference) the `reducedRight` of this reshape is the `{B,C,R}`
marginal arranged as `B ⊗ (C ⊗ R)` — the tripartite state to which strong subadditivity is applied
in the "child-form" derivation of weak monotonicity (N&C Exercise 11.24). -/
def QSystem.wmChildReshape (A B C R : QSystem) :
    (((A ⊗ (B ⊗ C)) ⊗ R)) ≃ₛ (A ⊗ (B ⊗ (C ⊗ R))) :=
  (QSystem.assoc A (B ⊗ C) R).symm.trans
    (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.assoc B C R).symm)

/-- **`A`-marginal of the child-form reshape.** `(congr (wmChildReshape A B C R) ω).reducedLeft =
ω.reducedLeft.reducedLeft`: the reshape only rearranges the non-`A` factors, so its `A`-marginal is
the iterated `A`-marginal of `ω`. Combines `State.reducedLeft_congr_tmul_refl` (the block
re-bracketing is on the traced-out right factor) with `State.reducedLeft_congr_assoc_symm` (the
outer de-association) through `State.congr_trans`. On a purification, with pure-state
complementarity, this is the `S(A) = S(B,C,R)` term. -/
theorem State.reducedLeft_congr_wmChildReshape (ω : State ((A ⊗ (B ⊗ C)) ⊗ R)) :
    (State.congr (QSystem.wmChildReshape A B C R) ω).reducedLeft = ω.reducedLeft.reducedLeft := by
  rw [QSystem.wmChildReshape, State.congr_trans, State.reducedLeft_congr_tmul_refl,
    State.reducedLeft_congr_assoc_symm]

/-- **`{B,C,R}` marginal of the child-form reshape**, written as a transported `(B ⊗ C) ⊗ R`
marginal: `(congr (wmChildReshape A B C R) ω).reducedRight =
(congr (assoc A (B ⊗ C) R).symm ω).reducedRight.congr (assoc B C R).symm`. Tracing out `A` commutes
past the right-block re-bracketing (`State.reducedRight_congr_tmul_right`), so the `B ⊗ (C ⊗ R)`
marginal is the transport (along `assoc⁻¹`) of the `(B ⊗ C) ⊗ R` marginal. This is the bridge that
lets the two strong-subadditivity terms below be read off. -/
theorem State.reducedRight_congr_wmChildReshape (ω : State ((A ⊗ (B ⊗ C)) ⊗ R)) :
    (State.congr (QSystem.wmChildReshape A B C R) ω).reducedRight
      = (State.congr (QSystem.assoc A (B ⊗ C) R).symm ω).reducedRight.congr
          (QSystem.assoc B C R).symm := by
  rw [QSystem.wmChildReshape, State.congr_trans, State.reducedRight_congr_tmul_right]

/-- **`C`-marginal consistency** (N&C Exercise 11.24, the `S(C)` term). The `C`-marginal of the
child-form `{B,C,R}` marginal `σ` equals `ω`'s own `C`-marginal:
`σ.reducedRight.reducedLeft = ω.reducedLeft.reducedRight.reducedRight`, where
`σ = (congr (wmChildReshape A B C R) ω).reducedRight`. After rewriting `σ` by
`State.reducedRight_congr_wmChildReshape`, both trace out `A`, `R`, `B` leaving `C`;
the order does not matter (`State.reducedRight_reducedLeft_congr_assoc_symm`, the trace-commutation
lemma). -/
theorem State.reducedRight_reducedLeft_congr_wmChildReshape (ω : State ((A ⊗ (B ⊗ C)) ⊗ R)) :
    ((State.congr (QSystem.wmChildReshape A B C R) ω).reducedRight).reducedRight.reducedLeft
      = ω.reducedLeft.reducedRight.reducedRight := by
  rw [State.reducedRight_congr_wmChildReshape, State.reducedRight_reducedLeft_congr_assoc_symm,
    State.reducedRight_reducedLeft_congr_assoc_symm]

/-- **`B ⊗ C`-marginal consistency** (N&C Exercise 11.24, the `S(B,C)` term). The `B ⊗ C`-marginal
of the child-form `{B,C,R}` marginal `σ` equals `ω`'s own `B ⊗ C`-marginal:
`(σ.congr (assoc B C R)).reducedLeft = ω.reducedLeft.reducedRight`, where
`σ = (congr (wmChildReshape A B C R) ω).reducedRight`. After rewriting `σ`, re-assoc cancels the
`assoc⁻¹` transport (`QSystem.Iso.symm_trans_self`), leaving the `(B ⊗ C)`-marginal of the
`(B ⊗ C) ⊗ R` marginal, which is `ω`'s `B ⊗ C`-marginal by the trace-commutation lemma
`State.reducedRight_reducedLeft_congr_assoc_symm`. -/
theorem State.reducedLeft_congr_assoc_wmChildReshape (ω : State ((A ⊗ (B ⊗ C)) ⊗ R)) :
    ((State.congr (QSystem.wmChildReshape A B C R) ω).reducedRight.congr
        (QSystem.assoc B C R)).reducedLeft = ω.reducedLeft.reducedRight := by
  rw [State.reducedRight_congr_wmChildReshape, ← State.congr_trans, QSystem.Iso.symm_trans_self,
    State.congr_refl, State.reducedRight_reducedLeft_congr_assoc_symm]

end AxQM
