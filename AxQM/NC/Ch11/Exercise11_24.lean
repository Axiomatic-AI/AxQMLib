/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.WeakMonotonicity
import AxQM.Postulates.API.WeakMonotonicityReducedRight
import AxQM.Postulates.API.WeakMonotonicitySecondComplement
import AxQM.Postulates.API.ReducedStateLeftBlock
import AxQM.NC.Ch11.StrongSubadditivityGeneral

/-!
# N&C Exercise 11.24 — weak monotonicity from strong subadditivity

Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Exercise 11.24** (p. 521). N&C
obtained strong subadditivity `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)` (eq. (11.108)) *from* the
"form-1" inequality — **weak monotonicity** `S(A) + S(B) ≤ S(A,C) + S(B,C)` (eq. (11.107)). The
exercise asks for the converse: derive weak monotonicity **as a consequence of strong
subadditivity**.

## The result

`State.vonNeumannEntropy_weakMonotonicity` — for an arbitrary state `ρ` on the tripartite system
`A ⊗ (B ⊗ C)`,

`S(A) + S(C) ≤ S(A,B) + S(B,C)`,

with the marginals read off as reduced states: `S(A) = S(ρ.reducedLeft)`,
`S(C) = S(ρ.reducedRight.reducedRight)`, `S(A,B) = S((assoc A B C · ρ).reducedLeft)` and
`S(B,C) = S(ρ.reducedRight)`. This is N&C eq. (11.107) with the subsystem labels permuted
(`B ↔ C` versus the book's `S(A) + S(B) ≤ S(A,C) + S(B,C)`); the labels are universally quantified,
so the two are the same theorem. This "shared-A" orientation makes all four terms clean adjacent
marginals of `ρ` (both mixed pairs `A,B` and `B,C` are adjacent), and is the exact form used for
the second-entry conditional subadditivity `S(A|B,C) ≤ S(A|B) + S(A|C)` (N&C Theorem 11.16) and the
mutual-information bound `S(A:B) + S(A:C) ≤ 2 S(A)` (N&C Exercise 11.26).

## The derivation (N&C's, dualised)

Introduce a reference `R` purifying `ρ` (`State.purify`) to a pure four-party state `ψ` on
`(A ⊗ (B ⊗ C)) ⊗ R`. Apply the general (faithfulness-free) strong subadditivity
`State.vonNeumannEntropy_add_le_add'` (N&C Theorem 11.14) to the reference marginal
`τ = Tr_A ψ` on `R ⊗ (B ⊗ C)`, reshaped to `R ⊗ (C ⊗ B)` so the middle factor is `C`:

`S(R,C,B) + S(C) ≤ S(R,C) + S(C,B)`.

Rewrite the reference terms by pure-state complementary-subsystem entropy (N&C Theorem 11.8(3)):
`S(R,C,B) = S(A)` (the `1‖3` split, via
`PureState.vonNeumannEntropy_reducedLeft_reducedLeft_eq_pullRefReshape`)
and `S(R,C) = S(A,B)` (the `2‖2` split `PureState.vonNeumannEntropy_ab_eq_cr`). Marginal consistency
(`State.reducedRight_reducedRight_congr_pullRefReshape`, `State.reducedRight_congr_comm`) identifies
`S(C,B)` and `S(C)` with `ρ`'s own `S(B,C)` and `S(C)`, giving eq. (11.107). `linarith` assembles.

## Supporting results

`State.vonNeumannEntropy_weakMonotonicity` depends on the general strong-subadditivity theorem
`State.vonNeumannEntropy_add_le_add'` in `AxQM/NC/Ch11/StrongSubadditivityGeneral.lean` (N&C
Theorem 11.14). Its supporting reshape-frame identity
`QSystem.pullRefReshape_assoc_eq_abcrReshape_comm` is an equality of two `QSystem.Iso` composites,
proved by extensionality on pure tensors. The purification, complementarity and
marginal-consistency results it uses are in `AxQM/Postulates/API/WeakMonotonicity.lean`,
`AxQM/Postulates/API/WeakMonotonicityReducedRight.lean`,
`AxQM/Postulates/API/WeakMonotonicitySecondComplement.lean` and
`AxQM/Postulates/API/ReducedStateLeftBlock.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- Reshape-frame bridge for weak monotonicity: the associator/swap composite that the
strong-subadditivity `R ⊗ C` marginal is read through equals the front-pair reshape
`QSystem.abcrReshape` post-composed with the inner `C ↔ R` swap. Both send
`(a ⊗ (b ⊗ c)) ⊗ r ↦ a ⊗ (b ⊗ (r ⊗ c))`; proved by extensionality on pure tensors. -/
theorem QSystem.pullRefReshape_assoc_eq_abcrReshape_comm {A B C R : QSystem} :
    (((A.pullRefReshape (B ⊗ C) R).trans
          ((QSystem.Iso.refl A).tmul
            (((QSystem.Iso.refl R).tmul (QSystem.Iso.comm B C)).trans (QSystem.assoc R C B)))).trans
        ((QSystem.Iso.refl A).tmul (QSystem.Iso.comm (R ⊗ C) B)))
      = ((A.abcrReshape B C R).trans (QSystem.assoc A B (C ⊗ R)).symm).trans
          ((QSystem.Iso.refl A).tmul ((QSystem.Iso.refl B).tmul (QSystem.Iso.comm C R))) := by
  apply congrArg QSystem.Iso.mk
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  refine TensorProduct.ext_threefold fun a bc r => ?_
  simp only [QSystem.pullRefReshape, QSystem.abcrReshape]
  induction bc using TensorProduct.inductionOn with
  | add u v hu hv =>
    erw [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, map_add, hu, hv]
  | tmul b c => rfl

/-- **Weak monotonicity of the von Neumann entropy** (Nielsen & Chuang, Exercise 11.24, the
"form-1" strong-subadditivity inequality eq. (11.107)): for an arbitrary state `ρ` on the
tripartite system `A ⊗ (B ⊗ C)`,

`S(A) + S(C) ≤ S(A,B) + S(B,C)`,

derived here **as a consequence of strong subadditivity** (`State.vonNeumannEntropy_add_le_add'`).
The proof purifies `ρ` with a reference `R`, applies strong subadditivity to the `R ⊗ (C ⊗ B)`
marginal of the purification, and rewrites the reference terms `S(R,C,B) = S(A)` and `S(R,C) =
S(A,B)` by pure-state complementary-subsystem entropy (Theorem 11.8(3)); see the module docstring.
Faithful to N&C up to a `B ↔ C` relabelling of the bound subsystems (this "shared-`A`" orientation
is the one Theorem 11.16 and Exercise 11.26 consume). -/
theorem State.vonNeumannEntropy_weakMonotonicity (ρ : State (A ⊗ (B ⊗ C))) :
    ρ.reducedLeft.vonNeumannEntropy + ρ.reducedRight.reducedRight.vonNeumannEntropy ≤
      (State.congr (QSystem.assoc A B C) ρ).reducedLeft.vonNeumannEntropy
        + ρ.reducedRight.vonNeumannEntropy := by
  -- Purify `ρ` on `A ⊗ (B ⊗ C)` with reference `R`.
  set ψ := ρ.purify with hψ
  -- The reference-pull marginal `τ = Tr_A (pullRefReshape ψ)` on `R ⊗ (B ⊗ C)`.
  set τ := (State.congr (QSystem.pullRefReshape A (B ⊗ C) _) ψ.toState).reducedRight with hτ
  -- Reshape `τ` to `R ⊗ (C ⊗ B)` so strong subadditivity has middle factor `C`.
  set σ := State.congr (QSystem.Iso.tmul (QSystem.Iso.refl _) (QSystem.Iso.comm B C)) τ with hσ
  have hρ : ψ.toState.reducedLeft = ρ := State.purify_reducedLeft_eq ρ
  -- `S(σ) = S(A)`: total of the reference marginal is the `A`-entropy (first purity identity).
  have hA : σ.vonNeumannEntropy = ρ.reducedLeft.vonNeumannEntropy := by
    rw [hσ, State.vonNeumannEntropy_congr, hτ,
      ← PureState.vonNeumannEntropy_reducedLeft_reducedLeft_eq_pullRefReshape ψ, hρ]
  -- `S(σ.reducedRight) = S(B,C)`: the `C ⊗ B` marginal of `τ` is `ρ`'s `B ⊗ C` marginal.
  have hBC : σ.reducedRight.vonNeumannEntropy = ρ.reducedRight.vonNeumannEntropy := by
    rw [hσ, State.reducedRight_congr_tmul_right, State.vonNeumannEntropy_congr, hτ,
      State.reducedRight_reducedRight_congr_pullRefReshape, hρ]
  -- `S(σ.reducedRight.reducedLeft) = S(C)`: further tracing `B` gives the `C` marginal.
  have hC : σ.reducedRight.reducedLeft.vonNeumannEntropy
      = ρ.reducedRight.reducedRight.vonNeumannEntropy := by
    rw [hσ, State.reducedRight_congr_tmul_right, hτ,
      State.reducedRight_reducedRight_congr_pullRefReshape, hρ,
      ← State.reducedRight_congr_comm]
  -- `S((assoc R C B σ).reducedLeft) = S(A,B)`: the `R ⊗ C` marginal, matched by complementarity.
  have hAB : (State.congr (QSystem.assoc _ C B) σ).reducedLeft.vonNeumannEntropy
      = (State.congr (QSystem.assoc A B C) ρ).reducedLeft.vonNeumannEntropy := by
    rw [← hρ, PureState.vonNeumannEntropy_ab_eq_cr ψ, hσ, hτ, ← State.congr_trans,
      ← State.reducedRight_congr_tmul_right, ← State.congr_trans,
      ← State.reducedRight_reducedRight_congr_assoc_symm, ← State.congr_trans]
    rw [State.reducedLeft_congr_comm, ← State.reducedRight_congr_tmul_right, ← State.congr_trans,
      QSystem.pullRefReshape_assoc_eq_abcrReshape_comm, State.congr_trans,
      State.reducedRight_congr_tmul_right, State.reducedRight_congr_tmul_right,
      State.vonNeumannEntropy_congr]
  have hssa := State.vonNeumannEntropy_add_le_add' σ
  rw [hA, hC, hAB, hBC] at hssa
  exact hssa

end AxQM
