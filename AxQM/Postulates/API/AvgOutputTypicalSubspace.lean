/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.TypicalSubspace
import AxQM.Postulates.API.CondTypicalSubspace
import AxQM.Postulates.API.Mixture

/-!
# The average-output typical subspace projector, `piTensor`-native (N&C Theorem 12.8, Box 12.5)

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, Box 12.5), the decoding measurement is built from the **typical subspace projector**
`P` of the *average output state* `σ̄ = ∑ₐ pₐ E(ρₐ)`, applied to the `n`-use output block, together
with the **conditional typical subspace projectors** `P_M` of the individual product codewords
`σ_M = ⨂ᵢ E(ρ_{Mᵢ})`.

These two operators are born on *definitionally equal but syntactically distinct* systems: the
average-output projector `σ̄.typicalSubspaceProj n ε` lives on `S ^⊗ₛ n` (the `n`-fold tensor
**power**), while `State.condTypicalSubspaceProj` and the pretty-good decoder `POVM.prettyGood`
live on `⨂ₛ _ : Fin n, S` (the indexed tensor **product** of the constant family).  The two systems
are equal by `QSystem.tensorPow_eq` — a `rfl` identity — but the `binop%`/coercion elaborator, which
unifies at *reducible* transparency, cannot bridge them, so a raw `QSystem.tensorPow_eq ▸ …`
transport left in a statement makes every later operator product re-run the cross-system
`▸`-match and time out.

This file introduces the projector **once**, as an opaque `piTensor`-native definition, and proves
the handful of facts the pretty-good product-state code and its code-level expected-error bound
need, so those consumers use `avgOutputTypicalProj` as an atom — never the `▸`-blob.

## What this file provides

* `State.avgOutputTypicalProj p hp hsum E ρ n ε` — the average-output ε-typical subspace projector
  `P = σ̄.typicalSubspaceProj n ε` **presented on `⨂ₛ _ : Fin n, S`**, definitionally the
  `QSystem.tensorPow_eq`-transport of `σ̄.typicalSubspaceProj n ε` (`avgOutputTypicalProj_eq`), for
  `σ̄ = State.mix p hp hsum (fun a => E (ρ a))`.

* `State.avgOutputTypicalProj_isSelfAdjoint` / `_idem` — `P` is a self-adjoint idempotent (an
  orthogonal projection), inherited from `State.typicalSubspaceProj_isSelfAdjoint`/`_idem` across
  the defeq transport.  These are exactly the `IsSelfAdjoint P` / `P ∘ P = P` hypotheses of the
  per-code
  and expected-error bounds (`State.avgError_prettyGood_le_re_trace_percode`,
  `State.expectation_avgError_prettyGood_le`).

* `State.avgOutputTypicalProj_condTypical_conj_nonneg` — `0 ≤ P (P_M) P` for any product codeword's
  conditional typical projector `P_M = State.condTypicalSubspaceProj σ s ε'`: the positivity of the
  decoder family `A_{M'} = P P_{M'} P` (from which `POVM.prettyGood A` is assembled), via
  `IsPositive.adjoint_conj` and self-adjointness of `P`.  This discharges the `hA` hypothesis of
  those bounds.

* `State.re_trace_one_sub_avgOutputTypicalProj_tensorPow_eq` — the typical-weight trace identity
  `re tr((1 − P) σ̄^⊗n) = 1 − Pr[σ̄^⊗n typical]`, expressing the first ("typical defect") term
  of the HSW expected-error bound (N&C eq. (12.80)) as one minus the Born probability that `σ̄^⊗n`
  lies in its own ε-typical subspace (`State.typicalSubspaceMeasurement`).  Done once here, across
  the change of representation, so that it is a clean rewrite against the typical-subspace
  weight bound `tr((1 − P) σ̄^⊗n) ≤ δ`.
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem} {α : Type*} [Fintype α]

/-- **The average-output ε-typical subspace projector, `piTensor`-native** (Nielsen & Chuang,
Theorem 12.8, Box 12.5).  For an input ensemble `{pₐ, ρₐ}`, quantum operation `E`, block length
`n`, and threshold `ε`, this is the ε-typical subspace projector `P(n, ε)` of the **average output
state** `σ̄ = ∑ₐ pₐ E(ρₐ)` (`State.mix p hp hsum (fun a => E (ρ a))`), presented as a continuous
linear
endomorphism of the indexed tensor product `⨂ₛ _ : Fin n, S` rather than the tensor power
`S ^⊗ₛ n`.

Definitionally it is the `QSystem.tensorPow_eq S n`-transport of `σ̄.typicalSubspaceProj n ε`
(`avgOutputTypicalProj_eq`); the two systems `S ^⊗ₛ n` and `⨂ₛ _ : Fin n, S` are equal by `rfl`.
The point of naming it is to hide that transport behind an opaque definition, so that the
pretty-good product-state decoder — which lives natively on `⨂ₛ _ : Fin n, S` alongside the
conditional typical projectors `State.condTypicalSubspaceProj` — can conjugate against `P` without
the cross-system
`▸`-match re-firing (and timing out) at every operator product. -/
def State.avgOutputTypicalProj (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (E : State S → State S) (ρ : α → State S) (n : ℕ) (ε : ℝ) :
    (QSystem.piTensor fun _ : Fin n => S).space →L[ℂ]
      (QSystem.piTensor fun _ : Fin n => S).space :=
  QSystem.tensorPow_eq S n ▸ (State.mix p hp hsum fun a => E (ρ a)).typicalSubspaceProj n ε

/-- **Defining unfold of `avgOutputTypicalProj`**: it is the `QSystem.tensorPow_eq`-transport of the
average output state's typical subspace projector `σ̄.typicalSubspaceProj n ε`.  A `rfl` identity;
the shape in which `State.expectation_avgError_prettyGood_le` (N&C eqs. (12.80)–(12.82)) takes its
typical projector, so instantiating that bound at `P = avgOutputTypicalProj` discharges its
`P = QSystem.tensorPow_eq S n ▸ σ̄.typicalSubspaceProj n ε` hypothesis by `rfl`. -/
theorem State.avgOutputTypicalProj_eq (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (E : State S → State S) (ρ : α → State S) (n : ℕ) (ε : ℝ) :
    State.avgOutputTypicalProj p hp hsum E ρ n ε
      = QSystem.tensorPow_eq S n ▸ (State.mix p hp hsum fun a => E (ρ a)).typicalSubspaceProj n ε :=
  rfl

/-- The average-output typical subspace projector `P` is **self-adjoint** (an orthonormal
projector), inherited from `State.typicalSubspaceProj_isSelfAdjoint` across the `rfl` transport.
Discharges the `IsSelfAdjoint P` hypothesis of the pretty-good per-code / expected-error bounds. -/
theorem State.avgOutputTypicalProj_isSelfAdjoint (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (E : State S → State S) (ρ : α → State S) (n : ℕ) (ε : ℝ) :
    IsSelfAdjoint (State.avgOutputTypicalProj p hp hsum E ρ n ε) :=
  (State.mix p hp hsum fun a => E (ρ a)).typicalSubspaceProj_isSelfAdjoint n ε

/-- The average-output typical subspace projector `P` is **idempotent**, `P ∘ P = P` (an orthonormal
projector), inherited from `State.typicalSubspaceProj_idem` across the `rfl` transport.  Discharges
the `P ∘ P = P` hypothesis of the pretty-good per-code / expected-error bounds. -/
theorem State.avgOutputTypicalProj_idem (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (E : State S → State S) (ρ : α → State S) (n : ℕ) (ε : ℝ) :
    (State.avgOutputTypicalProj p hp hsum E ρ n ε).comp
        (State.avgOutputTypicalProj p hp hsum E ρ n ε)
      = State.avgOutputTypicalProj p hp hsum E ρ n ε :=
  (State.mix p hp hsum fun a => E (ρ a)).typicalSubspaceProj_idem n ε

/-- **Positivity of the pretty-good decoder family** `A_{M'} = P P_{M'} P` (Nielsen & Chuang,
Theorem 12.8, Box 12.5, eq. (12.78)).  For the average-output typical projector
`P = avgOutputTypicalProj …` and any product codeword's conditional typical projector
`P_{M'} = State.condTypicalSubspaceProj σ s ε'`, the conjugate `P P_{M'} P` is a positive operator.

`P_{M'}` is a self-adjoint idempotent, hence positive
(`ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint`); conjugating a positive
operator by the self-adjoint `P` (`ContinuousLinearMap.IsPositive.adjoint_conj`, using `P† = P`)
keeps it positive.  This is exactly the family-positivity hypothesis `hA` of
`State.avgError_prettyGood_le_re_trace_percode` and `State.expectation_avgError_prettyGood_le`, from
which the square-root decoder `POVM.prettyGood A` is assembled. -/
theorem State.avgOutputTypicalProj_condTypical_conj_nonneg (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (E : State S → State S) (ρ : α → State S) (n : ℕ) (ε : ℝ)
    (σ : Fin n → State S) (s ε' : ℝ) :
    (0 : (QSystem.piTensor fun _ : Fin n => S).space →L[ℂ]
        (QSystem.piTensor fun _ : Fin n => S).space)
      ≤ (State.avgOutputTypicalProj p hp hsum E ρ n ε).comp
          ((State.condTypicalSubspaceProj σ s ε').comp
            (State.avgOutputTypicalProj p hp hsum E ρ n ε)) := by
  have hPsa := State.avgOutputTypicalProj_isSelfAdjoint p hp hsum E ρ n ε
  have h := (State.condTypicalSubspaceProj_isPositive σ s ε').adjoint_conj
    (State.avgOutputTypicalProj p hp hsum E ρ n ε)
  rw [hPsa.adjoint_eq] at h
  exact ContinuousLinearMap.nonneg_iff_isPositive.mpr h

/-- **The typical-defect trace identity** (Nielsen & Chuang, Theorem 12.8, Box 12.5, the first term
of eq. (12.80)).  The average-output typical-defect trace `re tr((1 − P) σ̄^⊗n)` equals one minus
the Born probability that the average output block `σ̄^⊗n` lies in its own ε-typical subspace:

`re tr((1 − P) σ̄^⊗n)  =  1 − Pr[σ̄^⊗n ∈ T(n, ε)]`,

where `P = avgOutputTypicalProj …` and the right-hand probability is the `true` outcome of
`σ̄.typicalSubspaceMeasurement n ε` on `σ̄^⊗n`.  The left-hand side is exactly the first summand of
`State.expectation_avgError_prettyGood_le`, transported to the `⨂ₛ _ : Fin n, S` system.

Proof: split `re tr((1 − P)·A) = re tr A − re tr(P·A)` (`ContinuousLinearMap.re_trace_one_sub_mul`);
`re tr A = 1` since `A = σ̄^⊗n.op` is a state (`State.trace_op_eq_one`), and `re tr(P·A)` is the
typical Born probability (`State.typicalSubspaceMeasurement_bornProb_eq_re_trace`, since `P` unfolds
to `σ̄.typicalSubspaceProj n ε`).  Both traces are read across the `rfl` transport of the average
output operator to `⨂ₛ _ : Fin n, S`. -/
theorem State.re_trace_one_sub_avgOutputTypicalProj_tensorPow_eq (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (E : State S → State S) (ρ : α → State S) (n : ℕ) (ε : ℝ) :
    RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
        (↑((1 - State.avgOutputTypicalProj p hp hsum E ρ n ε) *
            (QSystem.tensorPow_eq S n ▸ ((State.mix p hp hsum fun a => E (ρ a)).tensorPow n).op)) :
          (QSystem.piTensor fun _ : Fin n => S).space →ₗ[ℂ]
            (QSystem.piTensor fun _ : Fin n => S).space))
      = 1 - ((State.mix p hp hsum fun a => E (ρ a)).typicalSubspaceMeasurement n ε).bornProb
          ((State.mix p hp hsum fun a => E (ρ a)).tensorPow n) true := by
  set σbar := State.mix p hp hsum fun a => E (ρ a)
  rw [ContinuousLinearMap.re_trace_one_sub_mul]
  have h1 : RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
      (↑(QSystem.tensorPow_eq S n ▸ (σbar.tensorPow n).op) :
        (QSystem.piTensor fun _ : Fin n => S).space →ₗ[ℂ]
          (QSystem.piTensor fun _ : Fin n => S).space)) = 1 := by
    have ht : (LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
        (↑(QSystem.tensorPow_eq S n ▸ (σbar.tensorPow n).op) :
          (QSystem.piTensor fun _ : Fin n => S).space →ₗ[ℂ]
            (QSystem.piTensor fun _ : Fin n => S).space) = 1 :=
      (σbar.tensorPow n).trace_op_eq_one
    rw [ht]; exact RCLike.one_re
  have h2 : RCLike.re ((LinearMap.trace ℂ (QSystem.piTensor fun _ : Fin n => S).space)
      (↑(State.avgOutputTypicalProj p hp hsum E ρ n ε *
          (QSystem.tensorPow_eq S n ▸ (σbar.tensorPow n).op)) :
        (QSystem.piTensor fun _ : Fin n => S).space →ₗ[ℂ]
          (QSystem.piTensor fun _ : Fin n => S).space))
      = (σbar.typicalSubspaceMeasurement n ε).bornProb (σbar.tensorPow n) true := by
    rw [σbar.typicalSubspaceMeasurement_bornProb_eq_re_trace n ε (σbar.tensorPow n),
      State.avgOutputTypicalProj_eq]
    rfl
  rw [h1, h2]

end AxQM
