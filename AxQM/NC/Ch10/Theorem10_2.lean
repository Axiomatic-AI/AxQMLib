/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ErrorCorrectionDiscretization

/-!
# Nielsen & Chuang, Theorem 10.2 (Discretization of the errors)

Discretization: R correcting noise E also corrects any F whose op elements are linear combinations
of Ei.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 10.2 (p. 438).

This is the discretization of errors: a recovery operation built to correct one noise process
automatically corrects every noise process whose operation elements are linear combinations of the
original error operators — so a single recovery covers a whole (continuous) class of noise.

## The statement

Theorem 10.2's statement is about **operation elements** — the Kraus operators `Eᵢ`, `Rₖ`, the code
projector `P`, and *linear combinations* `Fⱼ = ∑ᵢ mⱼᵢ Eᵢ` of them — operators
`S.space →L[ℂ] S.space`; the conclusion is phrased with `State.op`. The theorem is formalised in
`AxQM/Postulates/API/ErrorCorrectionDiscretization.lean`; compare Theorem 10.1, whose operator
core is likewise formalised as operator theory.

The **clean correction criterion** used as the hypothesis — `Rₖ Eᵢ P = cₖᵢ P` (N&C Eqs. (10.29) /
(10.35)) — is the only property of the recovery `R` constructed in Theorem 10.1 that the proof of
Theorem 10.2 uses; the recovery built there satisfies it by construction. Taking it as a hypothesis
gives a faithful (mildly more general) reading of "the recovery operation `R` constructed in
Theorem 10.1".

## The formalisation

In `AxQM/Postulates/API/ErrorCorrectionDiscretization.lean`:

* `AxQM.CorrectsErrors` — the clean correction criterion `∃ c, ∀ k i, Rₖ Eᵢ P = cₖᵢ P`
  for a code projector `P`, recovery elements `R`, and error elements `E`.
* `AxQM.correctsErrors_linearCombination` — **Theorem 10.2, core.** `CorrectsErrors P R E`
  implies `CorrectsErrors P R F` for every `Fⱼ = ∑ᵢ mⱼᵢ Eᵢ` (new scalars `∑ᵢ mⱼᵢ cₖᵢ`).
* `AxQM.CorrectsErrors.krausSumₗ_op_proportional` — the physical meaning of "corrects"
  (N&C Eq. (10.15), (10.38)–(10.40)): a corrected noise `G` returns every code state to *one*
  state-independent scalar multiple of itself — `∃ λ ≥ 0, ∀ ρ ⊆ C`,
  `krausSumₗ R (krausSumₗ G ρ) = λ ρ`, `λ = ∑ₖⱼ ‖cₖⱼ‖²` — i.e. `R ∘ G` is proportional to the
  identity channel on the code.
* `AxQM.correctsErrors_krausSumₗ_op_proportional_linearCombination` — **Theorem 10.2 in
  full**: if `R` corrects `E` on the self-adjoint code projector `P`, there is a single `λ ≥ 0`
  with `(R ∘ F)(ρ) = λ ρ` for every code state `ρ` (N&C's uniform constant, Eq. (10.39)).
-/
