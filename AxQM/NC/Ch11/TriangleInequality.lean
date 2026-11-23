/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.Subadditivity
import AxQM.Postulates.API.PureMarginalEntropy
import AxQM.Postulates.API.ReducedStateTransport
import AxQM.Postulates.API.WeakMonotonicityReducedRight
import AxQM.Postulates.API.ReducedStateLeftBlock
import AxQM.Postulates.API.ReducedStateComm

/-!
# Araki–Lieb triangle inequality for the von Neumann entropy (N&C §11.3.4, eq. (11.79))

Nielsen & Chuang, §11.3.4: for a bipartite state `ρ` on `A ⊗ B`,

`|S(A) − S(B)| ≤ S(A, B)`      (**triangle / Araki–Lieb inequality**, eq. (11.79)),

the lower companion of subadditivity `S(A,B) ≤ S(A) + S(B)`
(`State.vonNeumannEntropy_le_reducedLeft_add_reducedRight`). Both directions of the absolute value
are supplied here as separate inequalities:

* `State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le` — `S(A) − S(B) ≤ S(A,B)`;
* `State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le` — `S(B) − S(A) ≤ S(A,B)`.

## Proof

N&C's argument (p. 516): purify `ρ` by a reference `R` into a pure state `Θ` on `(A ⊗ B) ⊗ R`
(`State.purify`, whose left marginal is `ρ`). Then

* `S(ρ) = S(R)` because `Θ` is pure on `(A ⊗ B) ⊗ R`
  (`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`, N&C Theorem 11.8(3): complementary
  marginals of a pure state are isentropic);
* re-associating `Θ` to `A ⊗ (B ⊗ R)` it is pure on the bipartition `A | (B ⊗ R)`, so
  `S(A) = S(B, R)` by the same complementarity;
* subadditivity on the `B ⊗ R` marginal gives `S(B, R) ≤ S(B) + S(R) = S(B) + S(ρ)`.

Chaining these yields `S(A) − S(B) ≤ S(ρ)`, the first inequality. The second is obtained by
applying the first to the swapped state `ρ.congr (comm A B)` on `B ⊗ A`, under which the two
marginals exchange roles and the joint entropy is unchanged.

## Ingredients

The proofs use the faithfulness-free subadditivity of `AxQM/NC/Ch11/Subadditivity.lean`; the
purifying reference `R` appears only in proof bodies, never in a statement.
-/

noncomputable section

namespace AxQM

variable {A B : QSystem}

/-- **Araki–Lieb triangle inequality, first direction** (Nielsen & Chuang, §11.3.4, eq. (11.79)):
for a bipartite state `ρ` on `A ⊗ B`,

`S(A) − S(B) ≤ S(A, B)`.

Purify `ρ` by a reference `R` (`State.purify`, left marginal `ρ`); the purification `Θ` on
`(A ⊗ B) ⊗ R` is pure, so `S(ρ) = S(R)`. Re-associating `Θ` to `A ⊗ (B ⊗ R)` it is pure on the
bipartition `A | (B ⊗ R)`, whence `S(A) = S(B, R)` by pure-state complementarity
(`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`); subadditivity of the `B ⊗ R` marginal
(`State.vonNeumannEntropy_le_reducedLeft_add_reducedRight`) gives `S(B, R) ≤ S(B) + S(R) = S(B) +
S(ρ)`. The three marginal identifications use the associator reshaping lemmas
`State.reducedLeft_congr_assoc_symm`, `State.reducedRight_reducedLeft_congr_assoc_symm`,
`State.reducedRight_reducedRight_congr_assoc_symm`. -/
theorem State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le (ρ : State (A.compose B)) :
    ρ.reducedLeft.vonNeumannEntropy - ρ.reducedRight.vonNeumannEntropy ≤ ρ.vonNeumannEntropy := by
  -- purification `Θ` on `(A ⊗ B) ⊗ R`, left marginal `ρ`
  have hΘL : ρ.purify.toState.reducedLeft = ρ := State.purify_reducedLeft_eq ρ
  -- `S(ρ) = S(R)` by pure-state complementarity
  have hSρ : ρ.vonNeumannEntropy = ρ.purify.toState.reducedRight.vonNeumannEntropy := by
    have hpc := PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight ρ.purify
    rw [hΘL] at hpc
    exact hpc
  -- the re-associated pure state `Θ' = Θ.congr (assoc A B R).symm` on `A ⊗ (B ⊗ R)`
  set Θ' : State (A.compose (B.compose _)) :=
    (PureState.congr (A.assoc B _).symm ρ.purify).toState with hΘ'
  -- `S(A) = S(B, R)` by pure-state complementarity on the bipartition `A | (B ⊗ R)`
  have hcompl : Θ'.reducedLeft.vonNeumannEntropy = Θ'.reducedRight.vonNeumannEntropy := by
    rw [hΘ']; exact PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight _
  -- identify the marginals of `Θ'`: left is `ρ_A`, right's left is `ρ_B`, right's right is `R`
  have hΘ'L : Θ'.reducedLeft = ρ.reducedLeft := by
    rw [hΘ', PureState.congr_toState, State.reducedLeft_congr_assoc_symm, hΘL]
  have hΘ'RL : Θ'.reducedRight.reducedLeft = ρ.reducedRight := by
    rw [hΘ', PureState.congr_toState, State.reducedRight_reducedLeft_congr_assoc_symm, hΘL]
  have hΘ'RR : Θ'.reducedRight.reducedRight = ρ.purify.toState.reducedRight := by
    rw [hΘ', PureState.congr_toState, State.reducedRight_reducedRight_congr_assoc_symm]
  -- subadditivity on the `B ⊗ R` marginal `Θ'_right`
  have hsub := State.vonNeumannEntropy_le_reducedLeft_add_reducedRight Θ'.reducedRight
  rw [hΘ'RL, hΘ'RR] at hsub
  rw [hΘ'L] at hcompl
  -- `S(A) = S(Θ'_right) ≤ S(B) + S(R) = S(B) + S(ρ)`
  linarith [hcompl, hsub, hSρ]

/-- **Araki–Lieb triangle inequality, second direction** (Nielsen & Chuang, §11.3.4, eq. (11.79)):
for a bipartite state `ρ` on `A ⊗ B`,

`S(B) − S(A) ≤ S(A, B)`.

Obtained from the first direction `State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le` applied
to the swapped state `ρ.congr (QSystem.Iso.comm A B)` on `B ⊗ A`: the swap exchanges the two
marginals (`State.reducedLeft_congr_comm`, `State.reducedRight_congr_comm`) and preserves the joint
entropy (`State.vonNeumannEntropy_congr`). Together with subadditivity this is the quantum triangle
inequality `|S(A) − S(B)| ≤ S(A, B)`. -/
theorem State.vonNeumannEntropy_reducedRight_sub_reducedLeft_le (ρ : State (A.compose B)) :
    ρ.reducedRight.vonNeumannEntropy - ρ.reducedLeft.vonNeumannEntropy ≤ ρ.vonNeumannEntropy := by
  have h := State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le
    (State.congr (QSystem.Iso.comm A B) ρ)
  rw [← State.reducedRight_congr_comm, ← State.reducedLeft_congr_comm,
    State.vonNeumannEntropy_congr] at h
  exact h

end AxQM
