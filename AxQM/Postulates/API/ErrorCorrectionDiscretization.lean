/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumChannel

/-!
# AxQM.Postulates.API — discretization of the errors (Nielsen & Chuang, Theorem 10.2)

Nielsen & Chuang's **Theorem 10.2** (the *discretization of the errors*, p. 438) is the deep fact
that makes quantum error-correction possible: a recovery operation built to correct one noise
process automatically corrects a whole *continuum* of noise processes.

Discretization: R correcting noise E also corrects any F whose op elements are linear combinations
of Ei.

## The structural core the proof uses

The recovery `R` constructed in Theorem 10.1 has operation elements `{Rₖ}` (concretely
`Rₖ = Uₖ† Pₖ`) with the property that, on the code space, it maps each error `Eᵢ` back into the
code up to a scalar: N&C's Equation (10.35) reads `Uₖ† Pₖ Eᵢ √ρ = δₖᵢ √dₖₖ √ρ`, i.e. at the
operator level

  `Rₖ Eᵢ P = cₖᵢ P`

for a code projector `P` and scalars `cₖᵢ` (Equation (10.29) of the necessity half of
Theorem 10.1). This **clean correction criterion** — captured here by `CorrectsErrors` — is the
*only* property of the constructed `R` that Theorem 10.2's proof uses, so we take it as the
hypothesis: the theorem is proved for **any** recovery `R` correcting `{Eᵢ}` in this sense, of
which Theorem 10.1's `R` is the instance. This is a faithful reading (a mild generalisation, not a
weakening): Theorem 10.1's specific `R` satisfies the hypothesis by construction.

## Contents

* `AxQM.CorrectsErrors` — the clean correction criterion `∃ c, ∀ k i, Rₖ Eᵢ P = cₖᵢ P`
  for a code projector `P`, recovery elements `R`, and error elements `E`.
* `AxQM.correctsErrors_linearCombination` — **Theorem 10.2, core.** If `R` corrects `E`
  then it corrects any `F` with `Fⱼ = ∑ᵢ mⱼᵢ Eᵢ` (the new scalars are `∑ᵢ mⱼᵢ cₖᵢ`). This is the
  discretization step: `{Eᵢ}` correctable ⟹ every linear-combination family is correctable.
* `AxQM.CorrectsErrors.krausSumₗ_op_proportional` — the physical meaning of "corrects"
  (N&C Eq. (10.15) and (10.38)–(10.40)): if `R` corrects `G`, there is a **single** `λ ≥ 0`
  (state-independent, `λ = ∑ₖⱼ ‖cₖⱼ‖²`) with `(R ∘ G)(ρ) = ∑ₖⱼ Rₖ Gⱼ ρ Gⱼ† Rₖ† = λ ρ` for **every**
  code state `ρ` (`P ρ P = ρ`) — `∃ λ, ∀ ρ`, so `R ∘ G` is proportional to the identity channel on
  the code (not a merely per-state factor).
* `AxQM.correctsErrors_krausSumₗ_op_proportional_linearCombination` — the two combined:
  Theorem 10.2 in full, `∃ λ ≥ 0, ∀ ρ ⊆ C, (R ∘ F)(ρ) = λ ρ` for the linear-combination noise `F`
  (N&C's uniform proportionality constant on the whole code).

## Operator sums

The statement of Theorem 10.2 is in `AxQM/NC/Ch10/Theorem10_2.lean`; the declarations are here.

The operator sum `∑ₖ Rₖ (·) Rₖ†` is the existing `ContinuousLinearMap.krausSumₗ` (N&C Chapter 8),
so `(R ∘ F)(ρ)` is `krausSumₗ R (krausSumₗ F ρ)`.
-/

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A recovery family corrects a set of errors on a code** (Nielsen & Chuang, the clean
correction criterion of Theorem 10.1, Eqs. (10.29) and (10.35)). Given a code projector
`P : S.space →L[ℂ] S.space`, recovery operation elements `R : κ → S.space →L[ℂ] S.space`, and error
operation elements `E : ι → S.space →L[ℂ] S.space`, we say `R` **corrects** `E` on the code `P`
when there are scalars `cₖᵢ` with

  `Rₖ Eᵢ P = cₖᵢ P`   for all `k, i`

(operator product `R k * E i * P`, composition on `S.space`). Physically: after an error `Eᵢ` acts
on a code state and recovery Kraus element `Rₖ` is applied, the result is the code state back again
up to the scalar `cₖᵢ`. This is exactly the structural property of the recovery operation `R`
constructed in the proof of Theorem 10.1 (N&C Eq. (10.35), `Uₖ† Pₖ Eᵢ √ρ = δₖᵢ √dₖₖ √ρ`), and the
only property Theorem 10.2 needs. -/
def CorrectsErrors {κ ι : Type*} (P : S.space →L[ℂ] S.space)
    (R : κ → S.space →L[ℂ] S.space) (E : ι → S.space →L[ℂ] S.space) : Prop :=
  ∃ c : κ → ι → ℂ, ∀ (k : κ) (i : ι), R k * E i * P = c k i • P

/-- **Discretization of the errors** (Nielsen & Chuang, Theorem 10.2 — the core step). If a
recovery family `R` corrects the errors `E` on the code `P` (`CorrectsErrors P R E`), then it also
corrects any family `F` whose operation elements are **linear combinations** `Fⱼ = ∑ᵢ mⱼᵢ Eᵢ` of
the `Eᵢ` (here `F = fun j => ∑ i, m j i • E i`).

The witnessing scalars for `F` are `cₖⱼ' = ∑ᵢ mⱼᵢ cₖᵢ`, since
`Rₖ (∑ᵢ mⱼᵢ Eᵢ) P = ∑ᵢ mⱼᵢ (Rₖ Eᵢ P) = ∑ᵢ mⱼᵢ cₖᵢ P = (∑ᵢ mⱼᵢ cₖᵢ) P`. This is the essence of the
discretization: correctability of `{Eᵢ}` transfers to every family built from linear combinations
of the `Eᵢ`, so a single recovery covers a whole (continuous) class of noise processes. -/
theorem correctsErrors_linearCombination {κ ι ι' : Type*} [Fintype ι]
    {P : S.space →L[ℂ] S.space} {R : κ → S.space →L[ℂ] S.space}
    {E : ι → S.space →L[ℂ] S.space} (m : ι' → ι → ℂ) (h : CorrectsErrors P R E) :
    CorrectsErrors P R (fun j => ∑ i, m j i • E i) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun k j => ∑ i, m j i * c k i, fun k j => ?_⟩
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, hc, Finset.sum_smul,
    smul_smul]

/-- **A corrected noise process is discretized to a single scalar on the code** (Nielsen & Chuang,
Theorem 10.2, Eqs. (10.38)–(10.40); the physical meaning of "the recovery `R` corrects the noise").
If the recovery family `R` corrects the errors `G` on the code `P` (`CorrectsErrors P R G`) and the
code projector `P` is self-adjoint, then there is **one** nonnegative constant `λ` — depending only
on `R`, `G`, `P` (not on the state) — such that for **every** state `ρ` whose support lies in the
code (`P ρ P = ρ`), applying the noise `G` and then the recovery `R` returns `ρ` scaled by that same
`λ`:

  `∃ λ ≥ 0, ∀ ρ ⊆ C,  (R ∘ G)(ρ) = ∑ₖⱼ Rₖ Gⱼ ρ Gⱼ† Rₖ† = λ ρ`,   `λ = ∑ₖⱼ ‖cₖⱼ‖²`.

The order of quantifiers matters: `∃ λ, ∀ ρ` says `R ∘ G` acts as the *same* scalar multiple of the
identity on the whole code (N&C Eq. (10.39)'s state-independent constant `∑ₖⱼ|mⱼₖ|²dₖₖ`), so it
preserves code-state superpositions — genuine error-correction. (The weaker `∀ ρ, ∃ λ` would admit
`ρ`-dependent factors that corrupt superpositions.) This is N&C's `R(E(ρ)) ∝ ρ` (Eq. (10.15)): with
`Rₖ Gⱼ P = cₖⱼ P` and `ρ = P ρ P`, each term is `Rₖ Gⱼ ρ Gⱼ† Rₖ† = (cₖⱼ P) ρ (cₖⱼ P)† = ‖cₖⱼ‖² ρ`,
and the constant `∑ₖⱼ ‖cₖⱼ‖²` is built from the correction scalars `cₖⱼ` alone. -/
theorem CorrectsErrors.krausSumₗ_op_proportional {κ ι : Type*} [Fintype κ] [Fintype ι]
    {P : S.space →L[ℂ] S.space} {R : κ → S.space →L[ℂ] S.space}
    {G : ι → S.space →L[ℂ] S.space} (h : CorrectsErrors P R G) (hP : IsSelfAdjoint P) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ ρ : State S, P * ρ.op * P = ρ.op →
      ContinuousLinearMap.krausSumₗ R (ContinuousLinearMap.krausSumₗ G ρ.op)
        = (lam : ℂ) • ρ.op := by
  obtain ⟨c, hc⟩ := h
  refine ⟨∑ k, ∑ j, Complex.normSq (c k j),
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _, ?_⟩
  intro ρ hρ
  -- each recovery element sends `Gⱼ P` to a scalar; its adjoint sends `P Gⱼ†` to the conjugate
  have key2 : ∀ (k : κ) (j : ι),
      P * star (G j) * star (R k) = star (c k j) • P := by
    intro k j
    have hstar := congrArg star (hc k j)
    rwa [star_mul, star_mul, hP.star_eq, star_smul, hP.star_eq, ← mul_assoc] at hstar
  -- coefficient identity `cₖⱼ · cₖⱼ⋆ = ‖cₖⱼ‖²` (`Complex.mul_conj`, with `star = conj` on ℂ)
  have hcoef : ∀ (k : κ) (j : ι),
      c k j * star (c k j) = (↑(Complex.normSq (c k j)) : ℂ) := fun k j => Complex.mul_conj _
  -- per-term: `Rₖ (Gⱼ ρ Gⱼ†) Rₖ† = ‖cₖⱼ‖² ρ` for `ρ` supported in the code
  have term : ∀ (k : κ) (j : ι),
      R k * (G j * ρ.op * star (G j)) * star (R k)
        = (↑(Complex.normSq (c k j)) : ℂ) • ρ.op := by
    intro k j
    calc R k * (G j * ρ.op * star (G j)) * star (R k)
        = (R k * G j * P) * ρ.op * (P * star (G j) * star (R k)) := by
          conv_lhs => rw [← hρ]
          simp only [mul_assoc]
      _ = (c k j • P) * ρ.op * (star (c k j) • P) := by rw [hc k j, key2 k j]
      _ = (c k j * star (c k j)) • (P * ρ.op * P) := by
          rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = (↑(Complex.normSq (c k j)) : ℂ) • ρ.op := by rw [hρ, hcoef k j]
  -- assemble the double sum
  simp only [ContinuousLinearMap.krausSumₗ_eq_sum_mul_star, Finset.sum_mul, Finset.mul_sum,
    Complex.ofReal_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => term k j

/-- **Theorem 10.2 (discretization of the errors), in full** (Nielsen & Chuang, p. 438). If a
recovery family `R` corrects the errors `E` on the code `P` (`CorrectsErrors P R E`), `P` is a
self-adjoint code projector, and the noise `F` has operation elements that are **linear
combinations** `Fⱼ = ∑ᵢ mⱼᵢ Eᵢ` of the `Eᵢ`, then `R` also corrects `F`: there is a **single**
nonnegative constant `λ` (independent of the state) with

  `∀ ρ ⊆ C,  (R ∘ F)(ρ) = λ ρ`,

i.e. `R ∘ F` is proportional to the identity channel on the whole code — N&C's `R(F(ρ)) ∝ ρ` with
the uniform constant `∑ₖⱼ|mⱼₖ|²dₖₖ` of Eq. (10.39). Combines `correctsErrors_linearCombination`
(correctability transfers to the linear-combination family) with
`CorrectsErrors.krausSumₗ_op_proportional` (a corrected noise is returned to *one* scalar multiple
of the code states). -/
theorem correctsErrors_krausSumₗ_op_proportional_linearCombination {κ ι ι' : Type*}
    [Fintype κ] [Fintype ι] [Fintype ι'] {P : S.space →L[ℂ] S.space}
    {R : κ → S.space →L[ℂ] S.space} {E : ι → S.space →L[ℂ] S.space} (m : ι' → ι → ℂ)
    (h : CorrectsErrors P R E) (hP : IsSelfAdjoint P) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ ρ : State S, P * ρ.op * P = ρ.op →
      ContinuousLinearMap.krausSumₗ R
          (ContinuousLinearMap.krausSumₗ (fun j => ∑ i, m j i • E i) ρ.op)
        = (lam : ℂ) • ρ.op :=
  (correctsErrors_linearCombination m h).krausSumₗ_op_proportional hP

end AxQM
