/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.PartialTrace

/-!
# AxQM — quantum mutual information `S(A:B)`

The **quantum mutual information** of a bipartite state `ρ` on `A ⊗ B` (Nielsen & Chuang §11.3.4,
eq. (11.60)):

`S(A:B) = S(A) + S(B) − S(A,B)`,

the sum of the von Neumann entropies of the two marginals minus the joint entropy. It measures the
total (classical + quantum) correlations between `A` and `B`; strong subadditivity is exactly the
statement that it is monotone under discarding part of one subsystem (Nielsen & Chuang
Theorem 11.15(2), formalised in `AxQM/Postulates/API/SubadditivityReformulations.lean`).

It is built from `State.vonNeumannEntropy`, `State.reducedLeft` (trace out `B`) and
`State.reducedRight` (trace out `A`). It is used in the strong-subadditivity reformulations of
Theorem 11.15 (`State.vonNeumannMutualInfo_le_of_discard`). The conditional-entropy reformulation of
the same theorem states the conditional entropy inline instead of using
`State.condVonNeumannEntropy`.

## Main definitions

* `AxQM.State.vonNeumannMutualInfo` — `S(A:B) = S(A) + S(B) − S(A,B)`.
-/

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- The **quantum mutual information** `S(A:B) = S(A) + S(B) − S(A,B)` of a bipartite state `ρ` on
`A ⊗ B`: the sum of the von Neumann entropies of the reduced states on `A` (`ρ.reducedLeft`) and on
`B` (`ρ.reducedRight`) minus the von Neumann entropy of the joint state. Nielsen & Chuang §11.3.4,
eq. (11.60). Non-negative (subadditivity), and monotone under discarding a subsystem (strong
subadditivity, Theorem 11.15(2)). -/
def State.vonNeumannMutualInfo (ρ : State (S ⊗ T)) : ℝ :=
  ρ.reducedLeft.vonNeumannEntropy + ρ.reducedRight.vonNeumannEntropy - ρ.vonNeumannEntropy

/-- Unfolding lemma for the mutual information: `S(A:B) = S(A) + S(B) − S(A,B)`. -/
theorem State.vonNeumannMutualInfo_def (ρ : State (S ⊗ T)) :
    ρ.vonNeumannMutualInfo =
      ρ.reducedLeft.vonNeumannEntropy + ρ.reducedRight.vonNeumannEntropy - ρ.vonNeumannEntropy :=
  rfl

end AxQM
