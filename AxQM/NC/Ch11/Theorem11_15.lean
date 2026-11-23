/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.Postulates.API.SubadditivityReformulations
import AxQM.Postulates.API.MutualInformationAncilla
import AxQM.Postulates.API.MutualInformationEvolution

/-!
# N&C Theorem 11.15 — reformulations of strong subadditivity

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.15, p. 522.

Theorem 11.15 collects three elementary reformulations of strong subadditivity that "provide a
powerful intuitive guide to the properties of quantum entropy":

1. **Conditioning reduces entropy.** For a composite system `A ⊗ (B ⊗ C)`, `S(A|B,C) ≤ S(A|B)`.
2. **Discarding quantum systems never increases mutual information.** For `A ⊗ (B ⊗ C)`,
   `S(A:B) ≤ S(A:B,C)`.
3. **Quantum operations never increase mutual information.** For a composite `A ⊗ B` and a
   trace-preserving quantum operation `E` on `B`, `S(A':B') ≤ S(A:B)`.

N&C proves (1) and (2) as pure algebraic rearrangements of strong subadditivity
`S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)` (Theorem 11.14, eq. (11.73)); (3) via the Chapter-8 dilation of
a channel to a unitary interaction with an ancilla followed by discarding the ancilla, so that (3)
reduces to (2).

## The formalisation

The *strictly-positive* forms of parts (1) and (2) carry the hypothesis `IsStrictlyPositive ρ.op`
(the finite, real-valued requirement inherited from the strong subadditivity
`State.vonNeumannEntropy_add_le_add`). They are in `AxQM/Postulates/API/`, as for Theorem 11.14 and
Problem 11.4, which they follow from:

* `AxQM.State.vonNeumannMutualInfo`
  (`AxQM/Postulates/API/MutualInformation.lean`) — the quantum mutual-information
  `S(A:B) = S(A) + S(B) − S(A,B)` that part (2) is phrased over.
* `AxQM.State.conditioning_reduces_vonNeumannEntropy`
  (`AxQM/Postulates/API/SubadditivityReformulations.lean`) — **part (1)**, `S(A|B,C) ≤ S(A|B)`,
  stated inline over von Neumann entropy differences (its two sides are the values of the
  conditional entropy `State.condVonNeumannEntropy`).
* `AxQM.State.vonNeumannMutualInfo_le_of_discard`
  (`AxQM/Postulates/API/SubadditivityReformulations.lean`) — **part (2)**, `S(A:B) ≤ S(A:B,C)`,
  stated over the mutual information.

Both reduce to strong subadditivity via the two marginal-consistency lemmas
`State.reducedLeft_reducedLeft_congr_assoc` (the `S(A)`-marginal) and
`State.reducedRight_reducedLeft_congr_assoc` (the `S(B)`-marginal), which identify the marginals of
the `A ⊗ B`-marginal state with those of the original tripartite state.

The **positivity-free forms** of parts (1) and (2) — matching N&C, who state both
reformulations for an *arbitrary* quantum state — drop the `IsStrictlyPositive` hypothesis. They are
`State.conditioning_reduces_vonNeumannEntropy'` and `State.vonNeumannMutualInfo_le_of_discard'`,
proved in this file. Each is immediate from the **faithfulness-free strong
subadditivity** `State.vonNeumannEntropy_add_le_add'`
(`AxQM/NC/Ch11/StrongSubadditivityGeneral.lean`, also used for Theorem 11.16), together with the two
marginal-consistency lemmas above.

## Part (3): quantum operations never increase mutual information

Part (3) is proved here as `State.vonNeumannMutualInfo_dilatedChannelOnRight_le`, following N&C's
own argument on p. 523: the channel `E` on `B` is dilated to a unitary interaction `U` on `B ⊗ C`
with an ancilla `C` prepared in a **pure** product state `ω`, and the operation `(id_A ⊗ E) ρ` is
realised as the state `ρ.dilatedChannelOnRight U ω` — adjoin the pure ancilla, act by `I_A ⊗ U` on
the `B ⊗ C` factor, discard `C`. The monotonicity `S(A' : B') ≤ S(A : B)` is then read straight off
the graph as

`S(A':B') ≤ S(A:B,C) = S(A:B,C)ₚᵣₑ = S(A:B)`,

chaining three facts: the **discarding** step (first inequality) is the faithful discard bound
`State.vonNeumannMutualInfo_le_of_discard'`; the **local unitary** `I_A ⊗ U` leaves the mutual
information invariant (`State.vonNeumannMutualInfo_evolve_id_tmul`, the equality-case ingredient);
and the **pure product ancilla** contributes no mutual information
(`State.vonNeumannMutualInfo_tmul_pure_right`,
`AxQM/Postulates/API/MutualInformationAncilla.lean`).

The discarding step applies part (2) — equivalently, strong
subadditivity — to the *dilated* tripartite state `U (ρ_AB ⊗ |0⟩⟨0|_C) U†`, whose pure ancilla
`|0⟩⟨0|_C` makes it rank-deficient, hence *not* strictly positive, so the strict part (2) does not
apply there. The **positivity-free discard bound `State.vonNeumannMutualInfo_le_of_discard'`**
applies: it holds for every state, resting on the faithfulness-free SSA
`State.vonNeumannEntropy_add_le_add'` obtained by a regularisation/limiting argument
(`ρ_t := (1-t)·ρ + t·(d⁻¹·1)`, `t → 0⁺`) with continuity keystone
`ContinuousLinearMap.IsDensityOp.continuousOn_vonNeumannEntropy`
(`ToMathlib/Analysis/InnerProductSpace/VonNeumannEntropyContinuous.lean`).

Stating the operation via its dilation (rather than an abstract trace-preserving map) is faithful to
N&C's proof: the channel is given by its environment/Stinespring representation rather than as an
abstract trace-preserving map.

## Main results (this file)

* `AxQM.State.conditioning_reduces_vonNeumannEntropy'` — N&C Thm 11.15(1), arbitrary `ρ`.
* `AxQM.State.vonNeumannMutualInfo_le_of_discard'` — N&C Thm 11.15(2), arbitrary `ρ`.
* `AxQM.State.dilatedChannelOnRight` — the output `(id_A ⊗ E) ρ` of a dilated channel on
  `B`.
* `AxQM.State.vonNeumannMutualInfo_dilatedChannelOnRight_le` — N&C Thm 11.15(3).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **N&C Theorem 11.15(1), faithful form: conditioning reduces entropy for every state.** For an
*arbitrary* state `ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A|B,C) ≤ S(A|B)`,

written inline over von Neumann entropy differences exactly as in the strictly-positive
`State.conditioning_reduces_vonNeumannEntropy` (each side is the corresponding value of the
conditional entropy). Immediate from the
faithfulness-free strong subadditivity `State.vonNeumannEntropy_add_le_add'`
(`AxQM/NC/Ch11/StrongSubadditivityGeneral.lean`); no faithfulness hypothesis is needed, matching
N&C's statement for a general state. -/
theorem State.conditioning_reduces_vonNeumannEntropy' (ρ : State (A ⊗ (B ⊗ C))) :
    ρ.vonNeumannEntropy - ρ.reducedRight.vonNeumannEntropy ≤
      (ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy -
        ρ.reducedRight.reducedLeft.vonNeumannEntropy := by
  have h := State.vonNeumannEntropy_add_le_add' ρ
  linarith

/-- **N&C Theorem 11.15(2), faithful form: discarding never increases mutual information for every
state.** For an *arbitrary* state `ρ` on the tripartite system `A ⊗ (B ⊗ C)`,

`S(A:B) ≤ S(A:B,C)`,

with `S(A:B)` the mutual information of the `A ⊗ B`-marginal and `S(A:B,C)` that of `ρ`. Every
state's operator is a density operator, so no faithfulness hypothesis is needed — matching N&C, who
state the reformulation for a general quantum state. The proof mirrors the strictly-positive
`State.vonNeumannMutualInfo_le_of_discard` but invokes the faithfulness-free strong subadditivity
`State.vonNeumannEntropy_add_le_add'` (`AxQM/NC/Ch11/StrongSubadditivityGeneral.lean`); the shared
`S(A)` and `S(B)` marginals are identified across the two readings by
`State.reducedLeft_reducedLeft_congr_assoc` and `State.reducedRight_reducedLeft_congr_assoc`. This
form is used for part (3), on the rank-deficient pure-ancilla dilated state. -/
theorem State.vonNeumannMutualInfo_le_of_discard' (ρ : State (A ⊗ (B ⊗ C))) :
    ((ρ.congr (QSystem.assoc A B C)).reducedLeft).vonNeumannMutualInfo ≤
      ρ.vonNeumannMutualInfo := by
  have hSSA := State.vonNeumannEntropy_add_le_add' ρ
  rw [State.vonNeumannMutualInfo_def, State.vonNeumannMutualInfo_def,
    State.reducedLeft_reducedLeft_congr_assoc, State.reducedRight_reducedLeft_congr_assoc]
  linarith

/-- **The output of a dilated quantum operation on `B`.** For a bipartite state `ρ` on `A ⊗ B`, a
unitary `U` on `B ⊗ C`, and an ancilla `C` prepared in the pure state `ω`, this is the state on
`A ⊗ B` obtained by Nielsen & Chuang's Chapter-8 dilation of a channel `E` on `B`: adjoin the pure
ancilla (`ρ ⊗ |ω⟩⟨ω|`, re-associated to `A ⊗ (B ⊗ C)`), let `U` act on the `B ⊗ C` factor
(`I_A ⊗ U`), then discard `C` (re-associate to `(A ⊗ B) ⊗ C` and trace it out). It realises
`(id_A ⊗ E) ρ` with `E(·) = Tr_C (U (· ⊗ |ω⟩⟨ω|) U†)` — every trace-preserving quantum operation on
`B` arises this way (the environment/Stinespring representation, N&C §8.2.3). -/
noncomputable def State.dilatedChannelOnRight (ρ : State (A ⊗ B)) (U : Evolution (B ⊗ C))
    (ω : PureState C) : State (A ⊗ B) :=
  ((((Evolution.id (S := A)).tmul U).evolve
      (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω.toState))).congr
      (QSystem.assoc A B C)).reducedLeft

/-- **N&C Theorem 11.15(3): quantum operations never increase mutual information.** For a bipartite
state `ρ` on `A ⊗ B` and a trace-preserving quantum operation `E` on `B`, presented by its
Chapter-8 dilation (a unitary `U` on `B ⊗ C` with the ancilla `C` in a pure state `ω`),

`S(A' : B') ≤ S(A : B)`,

where the primed state is `(id_A ⊗ E) ρ = ρ.dilatedChannelOnRight U ω`. This is N&C's proof on
p. 523 read off the graph: the discarding step is the faithful discard bound
`State.vonNeumannMutualInfo_le_of_discard'` (which, being positivity-free, applies to the
*rank-deficient* pure-ancilla dilated state); the local unitary `I_A ⊗ U` on the `B ⊗ C` factor
leaves the mutual information unchanged (`State.vonNeumannMutualInfo_evolve_id_tmul`); and appending
the pure product ancilla creates no correlations (`State.vonNeumannMutualInfo_tmul_pure_right`), so
the two chained equalities carry `S(A : B, C)` back to the original `S(A : B)`.

Stating the operation via its dilation is faithful to N&C's own argument: the channel is given by
its environment (Stinespring) representation rather than as an abstract trace-preserving map. -/
theorem State.vonNeumannMutualInfo_dilatedChannelOnRight_le (ρ : State (A ⊗ B))
    (U : Evolution (B ⊗ C)) (ω : PureState C) :
    (ρ.dilatedChannelOnRight U ω).vonNeumannMutualInfo ≤ ρ.vonNeumannMutualInfo := by
  unfold State.dilatedChannelOnRight
  calc ((((Evolution.id (S := A)).tmul U).evolve
          (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω.toState))).congr
          (QSystem.assoc A B C)).reducedLeft.vonNeumannMutualInfo
      ≤ (((Evolution.id (S := A)).tmul U).evolve
          (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω.toState))).vonNeumannMutualInfo :=
        State.vonNeumannMutualInfo_le_of_discard' _
    _ = (State.congr (QSystem.assoc A B C).symm (ρ.tmul ω.toState)).vonNeumannMutualInfo :=
        State.vonNeumannMutualInfo_evolve_id_tmul U _
    _ = ρ.vonNeumannMutualInfo := State.vonNeumannMutualInfo_tmul_pure_right ρ ω

end AxQM
