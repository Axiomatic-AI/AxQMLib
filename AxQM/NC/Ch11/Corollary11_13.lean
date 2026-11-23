/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.Exercise11_25
import AxQM.Postulates.API.ConditionalEntropyConcave

/-!
# N&C Corollary 11.13 — Concavity of the quantum conditional entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Corollary 11.13, p. 520.

Concavity of the quantum conditional entropy `S(A|B)` in the joint state `ρ^AB`.

Concretely: for a probability distribution `p` and a family `ρᵢ` of states of `A ⊗ B`,

`∑ᵢ pᵢ S(A|B)(ρᵢ) ≤ S(A|B)(∑ᵢ pᵢ ρᵢ)`,   `S(A|B) = S(A,B) − S(B)`,

for **every** family of states. N&C's corollary carries no faithfulness or full-rank restriction,
and the formalisation below matches that generality.

## The formalisation (the exact corollary)

The corollary's statement is formalised, in full generality, by

* `AxQM.State.condVonNeumannEntropy_concave`
  (in `AxQM/NC/Ch11/Exercise11_25.lean`):
  `∑ᵢ pᵢ S(A|B)(ρᵢ) ≤ S(A|B)(∑ᵢ pᵢ ρᵢ)` with **no faithfulness hypothesis**, where `S(A|B)` is the
  conditional entropy `AxQM.State.condVonNeumannEntropy`
  (`= S(ρ) − S(ρ.reducedRight)`, `State.condVonNeumannEntropy_def`) and `∑ᵢ pᵢ ρᵢ = State.mix …`.

This single theorem is the exact content shared by Corollary 11.13 and Exercise 11.25. In N&C,
strong subadditivity (Theorem 11.14) is obtained *from* the concavity of `S(A|B)`, and
Exercise 11.25 asks for the converse — concavity *from* strong subadditivity. The library proves
that converse direction, whose conclusion *is* the corollary's claim in full generality, so the
one theorem is shared between the two items rather than re-proved for each (the flag-register
argument is in `AxQM/NC/Ch11/Exercise11_25.lean`).

Its foundation is the **faithfulness-free** strong subadditivity
`AxQM.State.vonNeumannEntropy_add_le_add'`
(in `AxQM/NC/Ch11/StrongSubadditivityGeneral.lean`), rearranged into N&C Theorem 11.15(1),
*conditioning reduces the conditional entropy* `S(A|B,C) ≤ S(A|B)`
(`AxQM.State.conditioning_reduces_vonNeumannEntropy'`). That general strong subadditivity
is itself obtained from the strictly-positive form by the faithful-approximant limit
`ρₙ = (1 − 1/(n+1)) ρ + (1/(n+1)) (I/d) → ρ` (each `ρₙ` strictly positive), both sides being
continuous in trace distance via Fannes' inequality
(`AxQM.State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance`). So the passage from the
faithful branch to all states is the continuity argument on the strong-subadditivity route.

## N&C's own proof of the corollary (relative-entropy route, strictly-positive branch)

N&C prove Corollary 11.13 as a corollary of the joint convexity of the relative entropy
(Theorem 11.12), via the reduced-state identity (`d = dim A`, `ρ_B = Tr_A ρ`)

`S(A|B)(ρ) = log d − D(ρ ‖ (I/d) ⊗ ρ_B)`,

which exhibits `S(A|B)` as `log d` minus a relative entropy whose second argument is affine in `ρ`;
the joint convexity of `D` then yields concavity. This is N&C's *own* argument, and it is formalised
in `AxQM/Postulates/API/ConditionalEntropyConcave.lean`:

* `AxQM.State.quantumRelativeEntropy_maximallyMixed_tmul_reducedRight_eq` — the identity
  `D(ρ ‖ (I/d) ⊗ ρ_B) = log d + S(ρ_B) − S(ρ)`;
* `AxQM.State.vonNeumannEntropy_sub_reducedRight_concave` — concavity via that identity and
  the joint convexity `State.quantumRelativeEntropy_jointly_convex_sum`;
* supporting `State.isStrictlyPositive_mix_op`, `State.mix_reducedRight_op`,
  `State.mix_reducedLeft_op`.

This route carries the hypothesis `IsStrictlyPositive (ρᵢ).op` (each `ρᵢ` faithful): the operator
identity `ContinuousLinearMap.quantumRelativeEntropy_mapL_maximallyMixed_left_eq` factors
`log((I/d) ⊗ ρ_B)` additively through `IsSelfAdjoint.cfc_log_tensorMap`, which requires the
eigenvalues of `ρ_B` to be positive. It is therefore a faithful-branch formalisation of N&C's
*method*; the corollary's *statement*, in full generality, is given by
`condVonNeumannEntropy_concave` above.
-/
