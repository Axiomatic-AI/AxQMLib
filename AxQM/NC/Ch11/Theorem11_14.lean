/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch11.StrongSubadditivityGeneral
import AxQM.NC.Ch11.Exercise11_24

/-!
# N&C Theorem 11.14 — Strong subadditivity of the von Neumann entropy

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 11.14, p. 521.

Strong subadditivity states that **for any trio of quantum systems `A`, `B`, `C`** — with no
restriction on the state — the two inequalities

* eq. (11.107): `S(A) + S(B) ≤ S(A,C) + S(B,C)`   (the "form-1" / *weak monotonicity* inequality);
* eq. (11.108): `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)`   (*strong subadditivity* proper)

hold. N&C remarks that "the two inequalities are in fact equivalent": it proves (11.107) from the
concavity of the conditional entropy (Corollary 11.13) and then derives (11.108) by purifying `ABC`
with a reference `R` (so `S(R) = S(A,B,C)` and `S(R,C) = S(A,B)`).

## The formalisation

Both inequalities are formalised at N&C's **full generality** — arbitrary states, no positivity
hypothesis. They are used throughout Chapter 11 (Theorem 11.15, Theorem 11.16, Exercise 11.24,
Exercise 11.26, `AxQM/NC/Ch11/Subadditivity.lean`). Compare the relative-entropy results of
Theorem 11.12 and Theorem 11.17. The two statements:

* `AxQM.State.vonNeumannEntropy_add_le_add'`
  (`AxQM/NC/Ch11/StrongSubadditivityGeneral.lean`) — **strong subadditivity, eq. (11.108),
  for an arbitrary state** `ρ` on `A ⊗ (B ⊗ C)`: `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)`, with the
  marginals read off as reduced states — `S(A,B,C) = S(ρ)`, `S(B) = S(ρ.reducedRight.reducedLeft)`,
  `S(B,C) = S(ρ.reducedRight)`, and `S(A,B) = S((ρ.congr (QSystem.assoc A B C)).reducedLeft)` after
  re-associating to `(A ⊗ B) ⊗ C`. This is the main statement.
* `AxQM.State.vonNeumannEntropy_weakMonotonicity`
  (`AxQM/NC/Ch11/Exercise11_24.lean`) — the equivalent **form-1 inequality, eq. (11.107),
  for an arbitrary state**: `S(A) + S(C) ≤ S(A,B) + S(B,C)` (N&C's `S(A) + S(B) ≤ S(A,C) + S(B,C)`
  with the bound subsystems `B ↔ C` relabelled; the labels are universally quantified, so it is the
  same theorem). It is the content of the separate item **Exercise 11.24** — "obtain the
  form-1 inequality as a consequence of strong subadditivity" — and is derived there from
  `vonNeumannEntropy_add_le_add'` via purification, exactly N&C's dual of the (11.107) ⇒ (11.108)
  step.

Underlying these, the strictly-positive form:

* `AxQM.State.vonNeumannEntropy_add_le_add`
  (`AxQM/Postulates/API/StrongSubadditivity.lean`) — eq. (11.108) for a **faithful**
  (`IsStrictlyPositive ρ.op`) state. The `IsStrictlyPositive` hypothesis is the finite, real-valued
  requirement of the relative-entropy argument it is proved through (Lieb's theorem ⇒ Lindblad joint
  convexity of the relative entropy ⇒ mixed-unitary/twirl monotonicity ⇒ the operator inequality
  `ContinuousLinearMap.vonNeumannEntropy_add_partialTrace_le`). It is an
  **intermediate** step: `vonNeumannEntropy_add_le_add'` removes its faithfulness
  hypothesis by a perturbation-and-limit argument — approximate `ρ` by the strictly-positive
  `ρₙ = (1 − 1/(n+1)) ρ + (1/(n+1)) (I/d)` and pass to the limit, using continuity of the entropy in
  trace distance (Fannes' inequality, `State.tendsto_vonNeumannEntropy_of_tendsto_traceDistance`)
  and the fact that a marginal of a mixture is the mixture of the marginals.

## Faithfulness

The statements `vonNeumannEntropy_add_le_add'` and `vonNeumannEntropy_weakMonotonicity` carry **no
positivity restriction**, matching N&C's "for any trio of quantum systems"; the strict-positivity of
the intermediate form is removed before the theorem is stated, not imposed on it — so neither
inequality is weakened. The library establishes (11.108) directly (via the relative-entropy /
Lieb route) and then obtains (11.107) from it by purification (Exercise 11.24), the reverse of N&C's
own order; this is a faithful reformulation of the *derivation* — the two formalised statements are
exactly N&C's (11.107) and (11.108).

(The docstrings of the two underlying declarations label the same pair of inequalities
(11.72)/(11.73), the numbering of an earlier printing of N&C; the 10th anniversary edition followed
here numbers them (11.107)/(11.108), as above. The statements are identical.) -/
