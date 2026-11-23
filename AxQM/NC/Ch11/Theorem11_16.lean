/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.NC.Ch11.Exercise11_24
import AxQM.Postulates.API.ReducedStateReshape
import AxQM.Postulates.API.ReducedStateComm
import AxQM.Postulates.API.ReducedStateTransport
import AxQM.Postulates.API.SubadditivityReformulations

/-!
# N&C Theorem 11.16 — subadditivity of the conditional entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.16, p. 523. The quantum conditional entropy `S(·|·) = S(·,·) − S(·)` is subadditive both
jointly and in each of its two entries. N&C imposes **no positivity restriction** — the inequalities
hold for arbitrary states (the `0·log 0 = 0` convention, eq. (11.40)) — and all three are formalised
here at that full generality (**faithfulness-free**):

* **(11.116) joint** — `State.vonNeumannEntropy_joint_cond_subadditive`, four-system composite,
  `S(A,B|C,D) ≤ S(A|C) + S(B|D)`;
* **(11.117) first entry** — `State.vonNeumannEntropy_cond_subadditive_first`, for a three-system
  composite, `S(A,B|C) ≤ S(A|C) + S(B|C)`;
* **(11.118) second entry** — `State.vonNeumannEntropy_cond_subadditive_second`,
  `S(A|B,C) ≤ S(A|B) + S(A|C)`.

## Ingredients

Each conditional entropy is written out inline as its defining `S(·,·) − S(·)` von Neumann entropy
difference. The common ingredient is the general (faithfulness-free) strong subadditivity
`State.vonNeumannEntropy_add_le_add'` (`AxQM/NC/Ch11/StrongSubadditivityGeneral.lean`, N&C
Theorem 11.14 eq. (11.73)); the second entry additionally needs weak monotonicity
`State.vonNeumannEntropy_weakMonotonicity` (`AxQM/NC/Ch11/Exercise11_24.lean`, N&C eq. (11.72)).

## The reductions to strong subadditivity

* **First entry (11.117).** With the state on `A ⊗ (C ⊗ B)`, strong subadditivity with middle `C`
  reads `S(A,C,B) + S(C) ≤ S(A,C) + S(C,B)`; writing each conditional entropy as its difference
  makes the claim a one-line `linarith`, matching N&C p. 523 ("trivially equivalent to strong
  subadditivity").
* **Joint (11.116).** With the state on `A ⊗ (C ⊗ (D ⊗ B))`, two direct strong-subadditivity
  instances suffice — one on `ρ` (middle `C`), one on the `B,C,D` marginal `ρ.reducedRight`
  (middle `D`). The shared marginal `S(B,C,D) = S(ρ.reducedRight)` is the *same* reduced state in
  both, so `linarith` cancels it with no re-association; the arrangement is chosen so every marginal
  reads off directly. Faithfulness-free because the general strong subadditivity applies to the
  non-faithful marginal too.
* **Second entry (11.118).** The equivalent (11.123)
  `S(A,B,C) + S(B) + S(C) ≤ S(A,B) + S(A,C) + S(B,C)` is the arithmetic mean of three inequalities
  (N&C p. 523 proves it by a case split; the mean avoids it): strong subadditivity with middle `B`
  (`S(A,B,C)+S(B) ≤ S(A,B)+S(B,C)`), with middle `C` (`S(A,B,C)+S(C) ≤ S(A,C)+S(B,C)`), and weak
  monotonicity with shared `A` (`S(B)+S(C) ≤ S(A,B)+S(A,C)`). Summing and halving gives (11.123);
  `linarith` assembles. The three instances live on three reshapes of `ρ`
  (`A ⊗ (B ⊗ C)`, `A ⊗ (C ⊗ B)`, `B ⊗ (A ⊗ C)`), so most of the proof identifies their marginals
  with `ρ`'s own via the reduced-state transport toolkit; the `S(A,C)` term produced by the two
  strong-subadditivity/weak-monotonicity reshapes is matched through an `{A,C}`-block reshape-frame
  identity.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C D : QSystem}

/-- **N&C Theorem 11.16, subadditivity of the conditional entropy in the first entry (11.117).**
For an **arbitrary** state `ρ` on the tripartite system `A ⊗ (C ⊗ B)`,

`S(A,B|C) ≤ S(A|C) + S(B|C)`,

with each conditional entropy written as its defining difference `S(·|C) = S(·,C) − S(C)` —
`S(A,B|C) = S(ρ) − S(C)`, `S(A|C) = S(A,C) − S(C)`, `S(B|C) = S(B,C) − S(C)` — and the marginals
read off as `S(C) = S(ρ.reducedRight.reducedLeft)` (the middle subsystem),
`S(A,C) = S((ρ.congr (assoc A C B)).reducedLeft)` (re-associate to `(A ⊗ C) ⊗ B`, trace out `B`),
`S(B,C) = S(ρ.reducedRight)`. Immediate from the general strong subadditivity
`S(A,C,B) + S(C) ≤ S(A,C) + S(C,B)` (middle `C`) by `linarith`; faithfulness-free, matching N&C. -/
theorem State.vonNeumannEntropy_cond_subadditive_first (ρ : State (A ⊗ (C ⊗ B))) :
    ρ.vonNeumannEntropy - ρ.reducedRight.reducedLeft.vonNeumannEntropy ≤
      ((ρ.congr (QSystem.assoc A C B)).reducedLeft.vonNeumannEntropy
          - ρ.reducedRight.reducedLeft.vonNeumannEntropy)
        + (ρ.reducedRight.vonNeumannEntropy - ρ.reducedRight.reducedLeft.vonNeumannEntropy) := by
  have h := State.vonNeumannEntropy_add_le_add' ρ
  linarith

/-- **N&C Theorem 11.16, joint subadditivity of the conditional entropy (11.116).** For an
**arbitrary** state `ρ` on the four-system composite `A ⊗ (C ⊗ (D ⊗ B))`,

`S(A,B|C,D) ≤ S(A|C) + S(B|D)`,

with each conditional entropy written as its defining difference. The marginals are read off as
reduced states: `S(A,B,C,D) = S(ρ)`;
`S(C,D) = S((ρ.reducedRight.congr (assoc C D B)).reducedLeft)` (the `C ⊗ D` marginal of the `B,C,D`
marginal `ρ.reducedRight`); `S(A,C) = S((ρ.congr (assoc A C (D ⊗ B))).reducedLeft)` (trace out
`D ⊗ B`); `S(C) = S(ρ.reducedRight.reducedLeft)`; `S(B,D) = S(ρ.reducedRight.reducedRight)`;
`S(D) = S(ρ.reducedRight.reducedRight.reducedLeft)`. So `S(A,B|C,D) = S(ρ) − S(C,D)`,
`S(A|C) = S(A,C) − S(C)`, `S(B|D) = S(B,D) − S(D)`.

The proof adds two strong-subadditivity instances (N&C p. 524, eqs. (11.119)–(11.122)): one on `ρ`
(middle `C`), one on the `B,C,D` marginal `ρ.reducedRight` (middle `D`); the shared marginal
`S(B,C,D) = S(ρ.reducedRight)` is the *same* term in both, so `linarith` cancels it.
Faithfulness-free — the general strong subadditivity applies to the (non-faithful) marginal
`ρ.reducedRight` directly, so no marginal-faithfulness side condition is needed. -/
theorem State.vonNeumannEntropy_joint_cond_subadditive (ρ : State (A ⊗ (C ⊗ (D ⊗ B)))) :
    ρ.vonNeumannEntropy
        - (ρ.reducedRight.congr (QSystem.assoc C D B)).reducedLeft.vonNeumannEntropy ≤
      ((ρ.congr (QSystem.assoc A C (D ⊗ B))).reducedLeft.vonNeumannEntropy
          - ρ.reducedRight.reducedLeft.vonNeumannEntropy)
        + (ρ.reducedRight.reducedRight.vonNeumannEntropy
          - ρ.reducedRight.reducedRight.reducedLeft.vonNeumannEntropy) := by
  have hi := State.vonNeumannEntropy_add_le_add' ρ
  have hii := State.vonNeumannEntropy_add_le_add' ρ.reducedRight
  linarith

/-- The "shared-`A`" reshape `A ⊗ (B ⊗ C) ≃ₛ B ⊗ (A ⊗ C)`: move `A` into the middle so weak
monotonicity `S(B) + S(C) ≤ S(A,B) + S(A,C)` reads off directly. -/
private def secondEntryReshape (A B C : QSystem) : (A ⊗ (B ⊗ C)) ≃ₛ (B ⊗ (A ⊗ C)) :=
  (QSystem.assoc A B C).trans
    (((QSystem.Iso.comm A B).tmul (QSystem.Iso.refl C)).trans (QSystem.assoc B A C).symm)

/-- **N&C Theorem 11.16, subadditivity of the conditional entropy in the second entry (11.118).**
For an **arbitrary** state `ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A|B,C) ≤ S(A|B) + S(A|C)`,

with each conditional entropy written as its defining difference — `S(A|B,C) = S(ρ) − S(B,C)`,
`S(A|B) = S(A,B) − S(B)`, `S(A|C) = S(A,C) − S(C)` — and the marginals read off as reduced states:
`S(B,C) = S(ρ.reducedRight)`, `S(A,B) = S((ρ.congr (assoc A B C)).reducedLeft)`,
`S(B) = S(ρ.reducedRight.reducedLeft)`, `S(C) = S(ρ.reducedRight.reducedRight)`, and the `A ⊗ C`
marginal `S(A,C) = S(((ρ.congr (id ⊗ comm B C)).congr (assoc A C B)).reducedLeft)` (reshape to
`A ⊗ (C ⊗ B)`, re-associate to `(A ⊗ C) ⊗ B`, trace out `B`).

Equivalent to (11.123) `S(A,B,C) + S(B) + S(C) ≤ S(A,B) + S(A,C) + S(B,C)`, the mean of two strong
subadditivity instances (`State.vonNeumannEntropy_add_le_add'`, middles `B` and `C`) and weak
monotonicity (`State.vonNeumannEntropy_weakMonotonicity`, shared `A`); see the module docstring.
Faithfulness-free — the weak-monotonicity ingredient itself needs general strong subadditivity. -/
theorem State.vonNeumannEntropy_cond_subadditive_second (ρ : State (A ⊗ (B ⊗ C))) :
    ρ.vonNeumannEntropy - ρ.reducedRight.vonNeumannEntropy ≤
      ((ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy
          - ρ.reducedRight.reducedLeft.vonNeumannEntropy)
        + (((ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm B C))).congr
              (QSystem.assoc A C B)).reducedLeft.vonNeumannEntropy
          - ρ.reducedRight.reducedRight.vonNeumannEntropy) := by
  -- form2-i: strong subadditivity on ρ, middle B — `S(A,B,C)+S(B) ≤ S(A,B)+S(B,C)`.
  have hi := State.vonNeumannEntropy_add_le_add' ρ
  -- form2-ii: strong subadditivity on ρ reshaped to A ⊗ (C ⊗ B), middle C —
  -- `S(A,B,C)+S(C) ≤ S(A,C)+S(B,C)`.
  have hii := State.vonNeumannEntropy_add_le_add'
    (ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm B C)))
  rw [State.reducedRight_congr_tmul_right, State.vonNeumannEntropy_congr,
    ← State.reducedRight_congr_comm, State.vonNeumannEntropy_congr] at hii
  -- WM: weak monotonicity on ρ reshaped to B ⊗ (A ⊗ C) — `S(B)+S(C) ≤ S(A,B)+S(A,C)`.
  have hwm := State.vonNeumannEntropy_weakMonotonicity (ρ.congr (secondEntryReshape A B C))
  -- `S(B) = S(ρ_B)`: the `B`-marginal of the reshaped state is `ρ`'s.
  have eB : (State.congr (secondEntryReshape A B C) ρ).reducedLeft
      = ρ.reducedRight.reducedLeft := by
    simp only [secondEntryReshape]
    rw [State.congr_trans, State.congr_trans, State.reducedLeft_congr_assoc_symm,
      State.reducedLeft_congr_tmul_left, ← State.reducedRight_congr_comm,
      State.reducedRight_reducedLeft_congr_assoc]
  -- `S(C) = S(ρ_C)`.
  have eC : (State.congr (secondEntryReshape A B C) ρ).reducedRight.reducedRight
      = ρ.reducedRight.reducedRight := by
    simp only [secondEntryReshape]
    rw [State.congr_trans, State.congr_trans, State.reducedRight_reducedRight_congr_assoc_symm,
      State.reducedRight_congr_tmul_refl,
      ← State.reducedRight_reducedRight_congr_assoc_symm (State.congr (QSystem.assoc A B C) ρ),
      ← State.congr_trans, QSystem.Iso.trans_symm_self, State.congr_refl]
  -- `S(B,A) = S(A,B)`: the `assoc` cancels its inverse in `e3`, leaving `ρ_{AB}` up to `A ↔ B`.
  have eAB :
      (State.congr (QSystem.assoc B A C) (State.congr (secondEntryReshape A B C) ρ)).reducedLeft
        = (ρ.congr (QSystem.assoc A B C)).reducedLeft.congr (QSystem.Iso.comm A B) := by
    simp only [secondEntryReshape]
    rw [State.congr_trans, State.congr_trans, ← State.congr_trans, QSystem.Iso.symm_trans_self,
      State.congr_refl, State.reducedLeft_congr_tmul_left]
  -- `S(A,C)`: the `{A,C}` marginal of the reshaped state matches the one in the statement.
  have eAC : (State.congr (secondEntryReshape A B C) ρ).reducedRight
      = ((ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm B C))).congr
          (QSystem.assoc A C B)).reducedLeft := by
    rw [State.reducedRight_congr_comm, ← State.congr_trans, ← State.congr_trans]
    apply congrArg State.reducedLeft
    apply congrArg (fun e => State.congr e ρ)
    -- both isos send `a ⊗ (b ⊗ c) ↦ (a ⊗ c) ⊗ b`; prove equal on pure tensors.
    simp only [secondEntryReshape]
    apply congrArg QSystem.Iso.mk
    apply LinearIsometryEquiv.toLinearEquiv_injective
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro a bc
    induction bc using TensorProduct.inductionOn with
    | add u v hu hv => erw [TensorProduct.tmul_add, map_add, map_add, hu, hv]
    | tmul b c => rfl
  rw [eB, eC, eAB, eAC, State.vonNeumannEntropy_congr] at hwm
  linarith

end AxQM
