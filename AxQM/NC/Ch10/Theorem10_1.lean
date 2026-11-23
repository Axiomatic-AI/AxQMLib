/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumErrorCorrection

/-!
# Nielsen & Chuang, Theorem 10.1 (Quantum error-correction conditions)

QEC conditions: R correcting E on C exists iff P Ei-dag Ej P = alpha_ij P for Hermitian alpha.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 10.1 (p. 436).

The **Knill–Laflamme conditions** are the foundational characterisation of quantum error-correction:
they say a set of errors `{Eᵢ}` is correctable on a code exactly when the code cannot distinguish
the errors' effect — `P Eᵢ† Eⱼ P` is the same operator `αᵢⱼ P` for all `i, j`, so measuring the
"syndrome" reveals which error occurred without disturbing the encoded information. Sufficiency is
constructive: N&C build the two-part *syndrome-measure-then-rotate* recovery, which also underlies
the discretization of errors (Theorem 10.2).

## The statement

Theorem 10.1's statement is about **operation elements** — the code projector `P`, the Kraus
operators `Eᵢ`/`Rₒ`, the matrix `α` — operators `S.space →L[ℂ] S.space`. The formalisation has an
operator core, which is general Hilbert-space mathematics in `ToMathlib/`, and a reading for a
quantum system in `AxQM/Postulates/API/`. Compare N&C Theorems 8.1/8.2 (the operator-sum
representation) and Theorem 10.2 (discretization).

## The formalisation

The operator theory, in
`ToMathlib/Analysis/InnerProductSpace/QuantumErrorCorrection.lean`:

* `ContinuousLinearMap.SatisfiesKLConditions P E α` — the Knill–Laflamme conditions
  `P Eᵢ† Eⱼ P = αᵢⱼ P` (N&C Eq. (10.16)).
* `ContinuousLinearMap.Corrects P E R` — a recovery `R` corrects the errors `E` on the code
  (N&C Eq. (10.15)).
* `ContinuousLinearMap.satisfiesKLConditions_of_corrects` — **necessity** (`⟹`, N&C
  Eqs. (10.27)–(10.30)): a trace-preserving recovery correcting `E` forces the KL conditions with
  Hermitian `α`.
* `ContinuousLinearMap.corrects_of_satisfiesKLConditions` — **sufficiency** (`⟸`, N&C
  Eqs. (10.17)–(10.26)): the KL conditions yield the explicit syndrome recovery, which corrects `E`.
* `ContinuousLinearMap.satisfiesKLConditions_iff_exists_correction` — **Theorem 10.1**, the two
  directions assembled into the biconditional.

The physics reading over a quantum system, in
`AxQM/Postulates/API/QuantumErrorCorrection.lean`:

* `AxQM.SatisfiesQECConditions` — the QEC conditions as a physics-facing predicate on a
  code projector and noise operation elements of a `QSystem`.
* `AxQM.satisfiesQECConditions_iff_exists_correction` — **Theorem 10.1 for a quantum
  system**: the conditions hold iff a trace-preserving recovery correcting `E` on the code exists.
* `AxQM.SatisfiesQECConditions.exists_correctionChannel` — the physical reading: the QEC
  conditions produce a recovery **channel** returning every code state to a single scalar multiple
  of itself (`R(E(ρ)) ∝ ρ` with a state-independent constant, N&C Eq. (10.15)).
-/
