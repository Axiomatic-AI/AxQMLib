/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.API.MutualInformation
import AxQM.Postulates.PartialTrace

/-!
# AxQM — quantum conditional entropy `S(A|B)`

The **quantum conditional entropy** of a bipartite state `ρ` on `A ⊗ B` (Nielsen & Chuang §11.3.4,
summary of Chapter 11):

`S(A|B) = S(A,B) − S(B)`,

the von Neumann entropy of the whole minus that of the `B`-marginal. Unlike its classical
counterpart it can be **negative** — the signature of entanglement (a maximally entangled `ρ_{AB}`
has `S(A,B) = 0` but `S(B) = log dim B > 0`, so `S(A|B) = −log dim B < 0`). This negativity is what
makes several classical entropy inequalities fail quantumly (Nielsen & Chuang Problem 11.3).

It is defined from `State.vonNeumannEntropy` and `State.reducedRight` (trace out the left
factor `A`).

## Main definitions

* `AxQM.State.condVonNeumannEntropy` — `S(A|B) = S(A,B) − S(B)`.
-/

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- The **quantum conditional entropy** `S(A|B) = S(A,B) − S(B)` of a bipartite state `ρ` on
`A ⊗ B`: the von Neumann entropy of the joint state minus that of the reduced state on the
conditioning system `B` (the right factor, `ρ.reducedRight = Tr_A ρ`). Nielsen & Chuang §11.3.4.
May be negative when `A` and `B` are entangled. -/
def State.condVonNeumannEntropy (ρ : State (S ⊗ T)) : ℝ :=
  ρ.vonNeumannEntropy - ρ.reducedRight.vonNeumannEntropy

/-- Unfolding lemma for the conditional entropy: `S(A|B) = S(A,B) − S(B)`. -/
theorem State.condVonNeumannEntropy_def (ρ : State (S ⊗ T)) :
    ρ.condVonNeumannEntropy = ρ.vonNeumannEntropy - ρ.reducedRight.vonNeumannEntropy := rfl

/-- The **coherent information** `I(A⟩B) = S(B) − S(A,B)` of a bipartite state `ρ` on `A ⊗ B`,
the negative of the conditional entropy `S(A|B)` (Nielsen & Chuang §12.4.2). It measures how much
quantum information about the reference `A` is preserved by the state on `B`; being `−S(A|B)`, it is
positive exactly when `S(A|B) < 0`, i.e. when `A` and `B` are entangled. In N&C's data processing
inequality (Theorem 12.10) the coherent information `I(ρ, E)` of a *quantum operation* is this
quantity evaluated on the reference–system state `R'Q'` obtained by purifying `ρ` and applying `E`
to the system factor. -/
def State.coherentInfoOfState (ρ : State (S ⊗ T)) : ℝ := -ρ.condVonNeumannEntropy

/-- Unfolding lemma for the state coherent information: `I(A⟩B) = S(B) − S(A,B)`, the right marginal
entropy minus the joint entropy. -/
theorem State.coherentInfoOfState_def (ρ : State (S ⊗ T)) :
    ρ.coherentInfoOfState = ρ.reducedRight.vonNeumannEntropy - ρ.vonNeumannEntropy := by
  rw [State.coherentInfoOfState, State.condVonNeumannEntropy_def]; ring

/-- **The state coherent information as mutual information minus reference entropy:**
`I(A⟩B) = S(A:B) − S(A)`. Both sides equal `S(B) − S(A,B)`: expanding the quantum mutual information
`S(A:B) = S(A) + S(B) − S(A,B)` and subtracting the reference marginal entropy `S(A)` leaves exactly
the coherent information. This bridge lets coherent-information (in)equalities be discharged by the
corresponding mutual-information results (the left/reference marginal `S(A)` being the shared,
often channel-invariant, term). -/
theorem State.coherentInfoOfState_eq_vonNeumannMutualInfo_sub_reducedLeft (ρ : State (S ⊗ T)) :
    ρ.coherentInfoOfState = ρ.vonNeumannMutualInfo - ρ.reducedLeft.vonNeumannEntropy := by
  rw [State.coherentInfoOfState_def, State.vonNeumannMutualInfo_def]; ring

end AxQM
