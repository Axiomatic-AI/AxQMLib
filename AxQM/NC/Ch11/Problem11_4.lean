/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.Core.ConditionalEntropy
import ToMathlib.Analysis.SpecialFunctions.ConditionalEntropy

/-!
# N&C Problem 11.4 — Conditional forms of strong subadditivity

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 11.4, p. 526.

Conditional forms of strong subadditivity: prove quantum form; show classical analogue can fail.

The two parts contrast a quantum inequality that **holds for every state** with the classical
statement obtained by reversing the conditioning direction, which **fails**.

## Part (1) — the quantum inequality holds

`S(A, B, C | D) + S(B | D) ≤ S(A, B | D) + S(B, C | D)` is strong subadditivity (N&C Theorem 11.14)
with a spectator system `D` adjoined to every term: writing `S(· | D) = S(·, D) − S(D)`, the four
`−S(D)` cancel in pairs, leaving `S(A, B, C, D) + S(B, D) ≤ S(A, B, D) + S(B, C, D)`, which is
strong subadditivity applied with the middle subsystem enlarged to `B ⊗ D`.

The proof places the state on `A ⊗ ((B ⊗ D) ⊗ C)` — the tripartition whose middle factor
is `B ⊗ D` — and reads off the four conditional entropies as named quantities:

* `State.condEntropyTripleGivenD ρ = S(A, B, C | D)`;
* `State.condEntropyMiddleGivenD ρ = S(B | D)`, the conditional entropy
  (`State.condVonNeumannEntropy`) of the bipartite `B ⊗ D` marginal;
* `State.condEntropyLeftPairGivenD ρ = S(A, B | D)`;
* `State.condEntropyRightPairGivenD ρ = S(B, C | D)`;

and the inequality is `State.condEntropy_add_le_add`.

### No strict-positivity restriction

The underlying strong-subadditivity step is `State.vonNeumannEntropy_add_le_add'`, the **general
(faithfulness-free)** form of N&C Theorem 11.14: it holds for an *arbitrary* state, with no
`IsStrictlyPositive` hypothesis. Consequently Problem 11.4(1) is proved here for **every** state on
`A ⊗ ((B ⊗ D) ⊗ C)`, exactly as N&C states it — strong subadditivity carries no restriction on the
density operator. 
### The four conditional entropies

All four conditional entropies are built from `State.vonNeumannEntropy`, `State.reducedLeft`,
`State.reducedRight`, `State.congr`, and `State.condVonNeumannEntropy`.
The conditional entropy `State.condVonNeumannEntropy` (`S(A | B) = S(A, B) − S(B)`, eq. (11.46)) is
the one used in Problem 11.3; it is used here for the `S(B | D)` term (whose `B ⊗ D` marginal is a
genuine bipartite state). The remaining three terms have `D` buried inside a larger register, so, as
in Problem 11.3, they are written as their defining difference `S(·, D) − S(D)`, sharing the single
`S(D)`.

## Part (2) — the classical analogue fails

Conditioning `D` on the other variables gives a *different* inequality
`H(D | A, B, C) + H(D | B) ≤ H(D | A, B) + H(D | B, C)`, which is not always true. The witness is a
fair bit `x` with `A = C = D = x` (three copies) and `B` trivial: then `D` is a common cause of `A`
and `C`, and the four conditional entropies are `0`, `log 2`, `0`, `0`, so the left-hand side
exceeds the right by a full bit.

This is pure classical information theory (distributions on a finite sample space). The
declarations are in `ToMathlib/Analysis/SpecialFunctions/ConditionalEntropy.lean`:

* `Real.condEntropyMap` — the conditional Shannon entropy `H(f | g) = H(f, g) − H(g)` of random
  variables on a common sample space.
* `Real.exists_conditional_strong_subadditivity_counterexample` — the explicit counterexample.
* `Real.not_forall_conditional_strong_subadditivity` — its packaging as the refutation of the
  classical conditional inequality.

## Faithfulness

The base-2 logarithm of N&C is replaced by the natural logarithm in both halves; every (in)equality
is base-independent (both sides scale by the same factor), so this is a faithful reformulation, not
a weakening.

## Main results

* `AxQM.State.condEntropyTripleGivenD` / `condEntropyMiddleGivenD` /
  `condEntropyLeftPairGivenD` / `condEntropyRightPairGivenD` — the four conditional entropies
  `S(A, B, C | D)`, `S(B | D)`, `S(A, B | D)`, `S(B, C | D)` of a state on `A ⊗ ((B ⊗ D) ⊗ C)`.
* `AxQM.State.condEntropy_add_le_add` — Part (1): conditional strong subadditivity
  `S(A, B, C | D) + S(B | D) ≤ S(A, B | D) + S(B, C | D)`, for **every** state (no faithfulness
  hypothesis).
* Part (2) (classical, `ToMathlib/`): `Real.not_forall_conditional_strong_subadditivity`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C D : QSystem}

/-- **`S(A, B, C | D) = S(A, B, C, D) − S(D)`**, for a state on `A ⊗ ((B ⊗ D) ⊗ C)`: the conditional
entropy of the whole non-`D` part given `D`. Here `S(A, B, C, D) = S(ρ)` is the entropy of the whole
state and `S(D) = S(ρ.reducedRight.reducedLeft.reducedRight)` is that of the `D` marginal (trace out
`A`, then `C`, then `B`, leaving `D` — the right factor of the middle `B ⊗ D`). -/
def State.condEntropyTripleGivenD (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) : ℝ :=
  ρ.vonNeumannEntropy - ρ.reducedRight.reducedLeft.reducedRight.vonNeumannEntropy

/-- **`S(B | D) = S(B, D) − S(D)`**, for a state on `A ⊗ ((B ⊗ D) ⊗ C)`: the conditional entropy of
the middle system `B` given `D`. The `B ⊗ D` marginal is `ρ.reducedRight.reducedLeft` (trace out `A`
then `C`), a genuine bipartite state whose right factor is the conditioning system `D`, so this is
its bipartite conditional entropy `State.condVonNeumannEntropy`. -/
def State.condEntropyMiddleGivenD (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) : ℝ :=
  ρ.reducedRight.reducedLeft.condVonNeumannEntropy

/-- **`S(A, B | D) = S(A, B, D) − S(D)`**, for a state on `A ⊗ ((B ⊗ D) ⊗ C)`: the conditional
entropy of the pair `A, B` given `D`. The `A ⊗ (B ⊗ D)` marginal is read off by re-associating
`A ⊗ ((B ⊗ D) ⊗ C) ≃ (A ⊗ (B ⊗ D)) ⊗ C` and tracing out `C`; `S(D)` is shared with the other
conditional entropies. -/
def State.condEntropyLeftPairGivenD (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) : ℝ :=
  (ρ.congr (QSystem.assoc A (B ⊗ D) C)).reducedLeft.vonNeumannEntropy
    - ρ.reducedRight.reducedLeft.reducedRight.vonNeumannEntropy

/-- **`S(B, C | D) = S(B, C, D) − S(D)`**, for a state on `A ⊗ ((B ⊗ D) ⊗ C)`: the conditional
entropy of the pair `B, C` given `D`. The `(B ⊗ D) ⊗ C` marginal is `ρ.reducedRight` (trace out
`A`), and its entropy is `S(B, C, D)`; `S(D)` is shared with the other conditional entropies. -/
def State.condEntropyRightPairGivenD (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) : ℝ :=
  ρ.reducedRight.vonNeumannEntropy
    - ρ.reducedRight.reducedLeft.reducedRight.vonNeumannEntropy

/-- **N&C Problem 11.4(1): conditional strong subadditivity of the von Neumann entropy.** For
**every** state `ρ` on `A ⊗ ((B ⊗ D) ⊗ C)`,

`S(A, B, C | D) + S(B | D) ≤ S(A, B | D) + S(B, C | D)`.

This is strong subadditivity (`State.vonNeumannEntropy_add_le_add'`, N&C Theorem 11.14 in its
general form) with the middle subsystem enlarged to `B ⊗ D`: the joint inequality
`S(A, B, C, D) + S(B, D) ≤ S(A, B, D) + S(B, C, D)` holds for every state, and subtracting the
common `S(D)` from all four terms — the `−S(D)` cancel in pairs — yields the conditional form. No
faithfulness (`IsStrictlyPositive`) hypothesis is needed, matching N&C, because the underlying SSA
step is the faithfulness-free `State.vonNeumannEntropy_add_le_add'`. -/
theorem State.condEntropy_add_le_add (ρ : State (A ⊗ ((B ⊗ D) ⊗ C))) :
    ρ.condEntropyTripleGivenD + ρ.condEntropyMiddleGivenD ≤
      ρ.condEntropyLeftPairGivenD + ρ.condEntropyRightPairGivenD := by
  have hssa := State.vonNeumannEntropy_add_le_add' (A := A) (B := B ⊗ D) (C := C) ρ
  rw [State.condEntropyTripleGivenD, State.condEntropyMiddleGivenD, State.condVonNeumannEntropy_def,
    State.condEntropyLeftPairGivenD, State.condEntropyRightPairGivenD]
  linarith

end AxQM
