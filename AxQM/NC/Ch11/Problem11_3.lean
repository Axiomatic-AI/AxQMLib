/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ConditionalEntropy
import AxQM.Postulates.API.PartialTraceReassoc
import AxQM.Postulates.API.EntropyComposite
import AxQM.Postulates.API.BellBasis
import AxQM.Postulates.API.Qubit
import AxQM.NC.Ch2.Exercise2_75
import AxQM.NC.Ch11.TriangleInequality

/-!
# N&C Problem 11.3 — Analogue of the triangle inequality for conditional entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Problem 11.3, p. 525. The problem has three parts:

1. **(classical)** `H(X, Y | Z) ≥ H(X | Z)`.
2. **(quantum)** `S(A, B | C) ≥ S(A | C)` is *not* always true.
3. **(quantum)** the "conditional triangle inequality" `S(A, B | C) ≥ S(A | C) − S(B | C)`.

This file develops the **quantum** parts (2 and 3). Part 1 is classical Shannon information
theory; it is `Real.condEntropy_marginalFstLast_le_condEntropyPairGivenLast` in
`ToMathlib/Analysis/SpecialFunctions/ConditionalEntropyMonotone.lean`
(`H(X | Z) ≤ H(X, Y | Z)`, with `Real.condEntropyPairGivenLast` the classical pair conditional
entropy `H(X, Y | Z)`). It is the classical inequality that the quantum part 2 below shows *fails*.

## Tripartite conditional entropies

For a tripartite state on `A ⊗ (C ⊗ B)` (the conditioning system `C` is placed as the inner-left
factor, so its partner `B` — the one to be traced out for the `A ⊗ C` marginal — is the outer
factor after re-association) we use three conditional entropies (Nielsen & Chuang §11.3.4):

* `State.condEntropyPairGivenC ρ = S(A,B|C) = S(A,B,C) − S(C)` (the pair `A,B` is all but `C`);
* `State.condEntropyFirstGivenC ρ = S(A|C) = S(A,C) − S(C)`, the conditional entropy
  (`State.condVonNeumannEntropy`) of the `A ⊗ C` marginal;
* `State.condEntropySecondGivenC ρ = S(B|C) = S(B,C) − S(C)`, the conditional entropy of the `B`
  system alone given `C` (needed for Part 3, below).

## This file: Part 2 — quantum conditional-entropy monotonicity fails

The quantum conditional entropy `S(A|B) = S(A,B) − S(B)` — unlike its classical counterpart, which
is `≥ 0` — can be **negative**. The witness is `condTriangleState`, the state on `A ⊗ (C ⊗ B)`

`τ = |0⟩_A ⊗ |Φ⁺⟩_{CB}`,

with `A` a spectator qubit in `|0⟩` and the *conditioning* qubit `C` maximally entangled with `B`.
Its marginals are `S(A,B,C) = 0` (pure), `ρ_C = I/2` (`S(C) = log 2`), `ρ_{AC} = |0⟩⟨0| ⊗ I/2`
(`S(A,C) = log 2`), so

* `S(A,B|C) = 0 − log 2 = −log 2`,
* `S(A|C) = log 2 − log 2 = 0`,

hence `S(A,B|C) = −log 2 < 0 = S(A|C)`: monotonicity fails. Adjoining `B` (which purifies `A`'s
correlations with `C`) *decreases* the conditional entropy.

## This file: Part 3 — the "conditional triangle inequality" is FALSE as stated

Nielsen & Chuang, eq. (11.136), states the "conditional version of the triangle inequality"
`S(A,B|C) ≥ S(A|C) − S(B|C)`. This is **false**, and the *same* witness `condTriangleState =
|0⟩_A ⊗ |Φ⁺⟩_{CB}` refutes it. There

`S(A,B|C) = −log 2`,  `S(A|C) = 0`,  `S(B|C) = S(B,C) − S(C) = 0 − log 2 = −log 2`,

so the stated right-hand side is `S(A|C) − S(B|C) = 0 − (−log 2) = log 2`, while
`S(A,B|C) = −log 2`, and `−log 2 < log 2`. (Equivalently the claim reduces to
`S(A,B,C) + S(B,C) ≥ S(A,C) + S(C)`, which
the witness violates: `0 ≥ 2 log 2` is false.) We
**refute** the literal statement rather than silently repair it.

The genuinely-true "conditional triangle inequality" is `S(A,B|C) ≥ S(A|C) − S(B)` — with the
*unconditioned* `S(B)` (`State.entropySecond`), not `S(B|C)` — which follows from the Araki–Lieb
triangle inequality `S(A,C) ≤ S(A,B,C) + S(B)` (applied to the bipartition `(A,C) | B`), and is
**proved here** as `State.condEntropyFirstGivenC_sub_entropySecond_le_condEntropyPairGivenC` (the
common conditioning entropy `S(C)` of the two conditional entropies cancels). It is moreover *tight*
for the very witness that refutes eq. (11.136): equality `S(A|C) − S(B) = S(A,B|C)`
(`0 − log 2 = −log 2`) holds there
(`condTriangleState_condEntropyPairGivenC_eq_condEntropyFirstGivenC_sub_entropySecond`), so the
corrected bound is the sharp one — it cannot be strengthened back towards the false (11.136).

## Main results

* Part 1 (classical, in `ToMathlib/`):
  `Real.condEntropy_marginalFstLast_le_condEntropyPairGivenLast` — `H(X, Y | Z) ≥ H(X | Z)`.
* `AxQM.State.condEntropyPairGivenC` / `condEntropyFirstGivenC` / `condEntropySecondGivenC`
  — the three conditional entropies `S(A,B|C)`, `S(A|C)`, `S(B|C)` of a tripartite state.
* `AxQM.condTriangleState` — the witness `|0⟩_A ⊗ |Φ⁺⟩_{CB}`.
* `AxQM.exists_condEntropyPairGivenC_lt` — Part 2: a state with `S(A,B|C) < S(A|C)`.
* `AxQM.not_condEntropyPairGivenC_ge_condEntropyFirstGivenC_sub_condEntropySecondGivenC` —
  Part 3: N&C (11.136) is false as stated; a tripartite state violates
  `S(A,B|C) ≥ S(A|C) − S(B|C)`.
* `State.entropySecond` — `S(B)`, the entropy of the second system `B` (the *unconditioned*
  companion of `condEntropySecondGivenC = S(B|C)`).
* `State.condEntropyFirstGivenC_sub_entropySecond_le_condEntropyPairGivenC` — Part 3 (corrected):
  the *true* conditional triangle inequality `S(A,B|C) ≥ S(A|C) − S(B)`, for every tripartite
  state, with the unconditioned `S(B)`; proved from the Araki–Lieb triangle inequality.
* `condTriangleState_condEntropyPairGivenC_eq_condEntropyFirstGivenC_sub_entropySecond` — the
  corrected inequality is *tight*: the refuting witness saturates it (`0 − log 2 = −log 2`).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **Conditional entropy of the pair given the conditioning system**,
`S(A,B|C) = S(A,B,C) − S(C)`, for a tripartite state on `A ⊗ (C ⊗ B)`. Here `C` is the inner-left
factor (`reducedRight.reducedLeft` is its marginal `Tr_{A,B} ρ`); the pair `A, B` is all else. -/
def State.condEntropyPairGivenC (ρ : State (A ⊗ (C ⊗ B))) : ℝ :=
  ρ.vonNeumannEntropy - ρ.reducedRight.reducedLeft.vonNeumannEntropy

/-- **Conditional entropy of the first system given the conditioning system**,
`S(A|C) = S(A,C) − S(C)`, for a tripartite state on `A ⊗ (C ⊗ B)`. It is the bipartite conditional
entropy (`State.condVonNeumannEntropy`) of the `A ⊗ C` marginal, read off by re-associating
`A ⊗ (C ⊗ B) ≃ (A ⊗ C) ⊗ B` and tracing out `B`. -/
def State.condEntropyFirstGivenC (ρ : State (A ⊗ (C ⊗ B))) : ℝ :=
  (State.congr (QSystem.assoc A C B) ρ).reducedLeft.condVonNeumannEntropy

/-- **The Problem 11.3 counterexample state** `τ = |0⟩_A ⊗ |Φ⁺⟩_{CB}` on `A ⊗ (C ⊗ B)`
(three qubits): a spectator `|0⟩` on `A` tensored with a Bell pair on the conditioning system `C`
and its partner `B`. Pure, with `S(A,B|C) = −log 2 < 0 = S(A|C)`
(`exists_condEntropyPairGivenC_lt`). -/
def condTriangleState : State (qubit ⊗ (qubit ⊗ qubit)) :=
  qubitKet0.toState.tmul bellPhiPlus.toState

/-- The counterexample state is pure: `S(A,B,C) = 0`. -/
theorem condTriangleState_vonNeumannEntropy_eq_zero :
    condTriangleState.vonNeumannEntropy = 0 := by
  rw [condTriangleState, State.vonNeumannEntropy_tmul,
    PureState.vonNeumannEntropy_toState_eq_zero, PureState.vonNeumannEntropy_toState_eq_zero,
    add_zero]

/-- **The `C`-marginal is maximally mixed**: `ρ_C = Tr_{A,B} τ = I/2`. Tracing out `A` leaves the
Bell pair `|Φ⁺⟩_{CB}`, and tracing out its `B` half leaves `C` maximally mixed. -/
theorem condTriangleState_reducedC_eq :
    condTriangleState.reducedRight.reducedLeft = maximallyMixedState qubit := by
  rw [condTriangleState, State.reducedRight_tmul, ← bellState_zero_zero]
  exact bellState_reducedLeft 0 0

/-- **The `A ⊗ C`-marginal is a product with `C` maximally mixed**: `ρ_{AC} = Tr_B τ =
|0⟩⟨0|_A ⊗ I/2`. Since `A` is a spectator, tracing out `B` factors through it; the trace lands on
the Bell pair's `B` half, leaving `C` maximally mixed. Uses `State.reducedLeft_congr_assoc_tmul`
to read the `A ⊗ C` marginal off after re-associating `A ⊗ (C ⊗ B) ≃ (A ⊗ C) ⊗ B`. -/
theorem condTriangleState_reducedAC_eq :
    (State.congr (QSystem.assoc qubit qubit qubit) condTriangleState).reducedLeft
      = qubitKet0.toState.tmul (maximallyMixedState qubit) := by
  rw [condTriangleState, State.reducedLeft_congr_assoc_tmul, ← bellState_zero_zero,
    bellState_reducedLeft]

/-- **`S(A|C) = 0`** for the counterexample: `ρ_{AC} = |0⟩⟨0| ⊗ I/2` has
`S(A,C) = 0 + log 2 = log 2` and reduced `C` again `I/2` with `S(C) = log 2`, so
`S(A|C) = S(A,C) − S(C) = 0`. -/
theorem condTriangleState_condEntropyFirstGivenC_eq_zero :
    condTriangleState.condEntropyFirstGivenC = 0 := by
  rw [State.condEntropyFirstGivenC, condTriangleState_reducedAC_eq, State.condVonNeumannEntropy_def,
    State.vonNeumannEntropy_tmul, PureState.vonNeumannEntropy_toState_eq_zero,
    State.reducedRight_tmul, zero_add, sub_self]

/-- **`S(A,B|C) = −log 2`** for the counterexample: `S(A,B,C) − S(C) = 0 − log 2`. -/
theorem condTriangleState_condEntropyPairGivenC_eq :
    condTriangleState.condEntropyPairGivenC = -Real.log 2 := by
  rw [State.condEntropyPairGivenC, condTriangleState_vonNeumannEntropy_eq_zero,
    condTriangleState_reducedC_eq, State.vonNeumannEntropy_maximallyMixed, finrank_qubit_space,
    Nat.cast_ofNat, zero_sub]

/-- **N&C Problem 11.3, Part 2: `S(A,B|C) ≥ S(A|C)` is not always true.** There is a tripartite
state — `condTriangleState = |0⟩_A ⊗ |Φ⁺⟩_{CB}` — whose conditional entropy of the pair `A, B`
given `C` is strictly less than that of `A` alone given `C`: concretely `S(A,B|C) = −log 2 < 0 =
S(A|C)`.

The quantum conditional entropy `S(A,B|C)` becomes negative — impossible classically, where
`H(X,Y|Z) ≥ H(X|Z) ≥ 0` (Part 1). -/
theorem exists_condEntropyPairGivenC_lt :
    ∃ τ : State (qubit ⊗ (qubit ⊗ qubit)), τ.condEntropyPairGivenC < τ.condEntropyFirstGivenC := by
  refine ⟨condTriangleState, ?_⟩
  rw [condTriangleState_condEntropyPairGivenC_eq, condTriangleState_condEntropyFirstGivenC_eq_zero]
  exact neg_lt_zero.mpr (Real.log_pos (by norm_num))

/-- **Conditional entropy of the second system given the conditioning system**,
`S(B|C) = S(B,C) − S(C)`, for a tripartite state on `A ⊗ (C ⊗ B)`. The joint `B, C` marginal is
`ρ.reducedRight = Tr_A ρ` (its von Neumann entropy is `S(B,C)`, independent of the factor order),
and `S(C)` is that of `ρ.reducedRight.reducedLeft = Tr_{A,B} ρ` — the *same* `S(C)` as in
`State.condEntropyPairGivenC`. Used to state N&C Problem 11.3, Part 3. -/
def State.condEntropySecondGivenC (ρ : State (A ⊗ (C ⊗ B))) : ℝ :=
  ρ.reducedRight.vonNeumannEntropy - ρ.reducedRight.reducedLeft.vonNeumannEntropy

/-- **`S(B|C) = −log 2`** for the counterexample: the `B, C` marginal is the pure Bell pair
`|Φ⁺⟩_{CB}` (so `S(B,C) = 0`) while `ρ_C = I/2` (`S(C) = log 2`), hence `S(B|C) = 0 − log 2`. -/
theorem condTriangleState_condEntropySecondGivenC_eq :
    condTriangleState.condEntropySecondGivenC = -Real.log 2 := by
  rw [State.condEntropySecondGivenC, condTriangleState_reducedC_eq,
    State.vonNeumannEntropy_maximallyMixed, finrank_qubit_space, Nat.cast_ofNat,
    condTriangleState, State.reducedRight_tmul, PureState.vonNeumannEntropy_toState_eq_zero,
    zero_sub]

/-- **N&C Problem 11.3, Part 3: the "conditional triangle inequality" `S(A,B|C) ≥ S(A|C) − S(B|C)`
(Nielsen & Chuang eq. 11.136) is FALSE as stated.** No such inequality holds for all tripartite
states: the witness `condTriangleState = |0⟩_A ⊗ |Φ⁺⟩_{CB}` has `S(A,B|C) = −log 2` yet
`S(A|C) − S(B|C) = 0 − (−log 2) = log 2 > −log 2`, so `S(A,B|C) < S(A|C) − S(B|C)`.

We refute the literal statement (rather than silently repairing it to the genuinely-true form
`S(A,B|C) ≥ S(A|C) − S(B)` with the *unconditioned* `S(B)`; see the module docstring). It suffices
to exhibit a single tripartite (three-qubit) state violating it — which refutes the universal claim
a fortiori. The inequality is written in its `(S(A|C) − S(B|C)) ≤ S(A,B|C)` form. -/
theorem not_condEntropyPairGivenC_ge_condEntropyFirstGivenC_sub_condEntropySecondGivenC :
    ¬ ∀ τ : State (qubit ⊗ (qubit ⊗ qubit)),
      τ.condEntropyFirstGivenC - τ.condEntropySecondGivenC ≤ τ.condEntropyPairGivenC := by
  intro h
  have hτ := h condTriangleState
  rw [condTriangleState_condEntropyFirstGivenC_eq_zero,
    condTriangleState_condEntropySecondGivenC_eq, condTriangleState_condEntropyPairGivenC_eq] at hτ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- **Entropy of the second system** `S(B) = ρ.reducedRight.reducedRight.vonNeumannEntropy`, for a
tripartite state on `A ⊗ (C ⊗ B)`: the von Neumann entropy of the `B` marginal `Tr_{A,C} ρ` (trace
out `A`, then the conditioning `C`). The *unconditioned* companion of `condEntropySecondGivenC =
S(B|C)`; it is the quantity the corrected conditional triangle inequality
(`State.condEntropyFirstGivenC_sub_entropySecond_le_condEntropyPairGivenC`) subtracts, in place of
the `S(B|C)` of the false N&C eq. (11.136). -/
def State.entropySecond (ρ : State (A ⊗ (C ⊗ B))) : ℝ :=
  ρ.reducedRight.reducedRight.vonNeumannEntropy

/-- **N&C Problem 11.3, Part 3 (corrected): the true conditional triangle inequality**
`S(A,B|C) ≥ S(A|C) − S(B)`. For *every* tripartite state `ρ` on `A ⊗ (C ⊗ B)`,

`S(A|C) − S(B) ≤ S(A,B|C)`,

with `S(B) = ρ.entropySecond` the entropy of the `B` marginal. This is the faithful replacement for
the false eq. (11.136) refuted just above: the traced-out system's entropy enters **unconditioned**
as `S(B)`, not as `S(B|C)`.

**Proof.** Re-associate `ρ` to `σ = State.congr (QSystem.assoc A C B) ρ` on `(A ⊗ C) ⊗ B` and apply
the Araki–Lieb triangle inequality `S(A,C) ≤ S(A,B,C) + S(B)`
(`State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le`, i.e. `S(σ_L) − S(σ_R) ≤ S(σ)`), with the
marginals identified by `State.reducedRight_congr_assoc` (`S(σ_R) = S(ρ_B)`) and
`State.vonNeumannEntropy_congr` (`S(σ) = S(ρ) = S(A,B,C)`). Unfolding `S(A|C)` and `S(A,B|C)`, the
shared conditioning entropy `S(C)` — reached as `σ_L`'s right marginal on one side
(`State.reducedRight_reducedLeft_congr_assoc`) and as `ρ.reducedRight.reducedLeft` on the other —
cancels, leaving exactly the Araki–Lieb bound. -/
theorem State.condEntropyFirstGivenC_sub_entropySecond_le_condEntropyPairGivenC
    (ρ : State (A ⊗ (C ⊗ B))) :
    ρ.condEntropyFirstGivenC - ρ.entropySecond ≤ ρ.condEntropyPairGivenC := by
  -- Araki–Lieb on the re-associated state `σ` on `(A ⊗ C) ⊗ B`, split `(A ⊗ C) | B`
  have hAL := State.vonNeumannEntropy_reducedLeft_sub_reducedRight_le
    (State.congr (QSystem.assoc A C B) ρ)
  rw [State.reducedRight_congr_assoc, State.vonNeumannEntropy_congr] at hAL
  -- unfold both conditional entropies; the shared `S(C)` matches on both sides and cancels
  rw [State.condEntropyPairGivenC, State.condEntropyFirstGivenC, State.condVonNeumannEntropy_def,
    State.reducedRight_reducedLeft_congr_assoc, State.entropySecond]
  linarith

/-- **`S(B) = log 2`** for the counterexample `condTriangleState = |0⟩_A ⊗ |Φ⁺⟩_{CB}`: the `B`
marginal is the maximally mixed qubit (the other half of the Bell pair `|Φ⁺⟩_{CB}` after tracing
out `A` and the conditioning `C`), so its von Neumann entropy is `log 2`. -/
theorem condTriangleState_entropySecond_eq :
    condTriangleState.entropySecond = Real.log 2 := by
  rw [State.entropySecond, condTriangleState, State.reducedRight_tmul, ← bellState_zero_zero,
    bellState_reducedRight, State.vonNeumannEntropy_maximallyMixed, finrank_qubit_space,
    Nat.cast_ofNat]

/-- **The corrected conditional triangle inequality is tight.** The very witness
`condTriangleState = |0⟩_A ⊗ |Φ⁺⟩_{CB}` that refutes the false eq. (11.136) *saturates* the
corrected bound `S(A,B|C) ≥ S(A|C) − S(B)` with equality: `S(A,B|C) = −log 2 = 0 − log 2 =
S(A|C) − S(B)`. Hence `S(B)` is the sharp quantity — the bound cannot be tightened back towards the
`S(B|C)` of (11.136). -/
theorem condTriangleState_condEntropyPairGivenC_eq_condEntropyFirstGivenC_sub_entropySecond :
    condTriangleState.condEntropyPairGivenC
      = condTriangleState.condEntropyFirstGivenC - condTriangleState.entropySecond := by
  rw [condTriangleState_condEntropyPairGivenC_eq, condTriangleState_condEntropyFirstGivenC_eq_zero,
    condTriangleState_entropySecond_eq, zero_sub]

end AxQM
