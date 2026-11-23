/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumChannel
import ToMathlib.Analysis.InnerProductSpace.QuantumErrorCorrection

/-!
# AxQM.Postulates.API — quantum error-correction conditions (N&C, Theorem 10.1)

Nielsen & Chuang's **Theorem 10.1** (the *quantum error-correction conditions*, p. 436) is the
characterisation of when a noise process can be reversed on a code:

QEC conditions: R correcting E on C exists iff P Ei-dag Ej P = alpha_ij P for Hermitian alpha.

This file states the result over a quantum system `S : QSystem`: the code
projector `P`, the noise's operation elements `E`, and the recovery `R` are operators on the
system's state space `S.space`, and the recovery is exhibited as a genuine quantum channel
(`AxQM.IsChannel`) acting on the system's states (`State S`). The operator
theory itself — both directions of the biconditional and the explicit recovery construction — is
in `ToMathlib/Analysis/InnerProductSpace/QuantumErrorCorrection.lean`
(`ContinuousLinearMap.satisfiesKLConditions_iff_exists_correction`), as for N&C
Theorems 8.1/8.2. The statement of Theorem 10.1 is in `AxQM/NC/Ch10/Theorem10_1.lean`.

## Contents

* `AxQM.SatisfiesQECConditions` — the **quantum error-correction conditions** as a
  predicate on a code projector `P` and noise operation elements `E`:
  `∃ Hermitian α, P Eᵢ† Eⱼ P = αᵢⱼ P` (N&C Eq. (10.16)).
* `AxQM.satisfiesQECConditions_iff_exists_correction` — **Theorem 10.1**, as the
  biconditional: `SatisfiesQECConditions P E ↔` there exists a trace-preserving recovery family
  `R` (`∑ₒ Rₒ† Rₒ = 1`) correcting `E` on the code.
* `AxQM.SatisfiesQECConditions.exists_correctionChannel` — **the physical reading**: if
  the QEC conditions hold, there is a recovery **channel** `rec` (`IsChannel`) and a single
  state-independent `λ ≥ 0` such that on every code state `ρ`, applying the noise `E` and then the
  recovery returns `ρ` to `λ • ρ` (N&C's `R(E(ρ)) ∝ ρ`, Eq. (10.15), with a *uniform* constant).

The statements are phrased with operators `S.space →L[ℂ] S.space` and the density operator
`State.op`. Compare the neighbouring Theorem 10.2
(`AxQM/Postulates/API/ErrorCorrectionDiscretization.lean`).
-/

open scoped Matrix

noncomputable section

namespace AxQM

universe uι

variable {S : QSystem} {ι : Type uι} [Fintype ι]

/-- **The quantum error-correction conditions** (Nielsen & Chuang, Theorem 10.1, Eq. (10.16)), as a
predicate on a quantum system `S`. For a code projector `P : S.space →L[ℂ] S.space`
and a finite family of noise operation elements `E : ι → S.space →L[ℂ] S.space`, the conditions hold
when there is a **Hermitian** matrix `α` with `P Eᵢ† Eⱼ P = αᵢⱼ P` for all `i, j`
(`ContinuousLinearMap.SatisfiesKLConditions`). This is N&C's "`P Eᵢ† Eⱼ P = αᵢⱼ P` for some
Hermitian matrix `α`" — the condition the theorem characterises correctability by. -/
def SatisfiesQECConditions (P : S.space →L[ℂ] S.space) (E : ι → S.space →L[ℂ] S.space) : Prop :=
  ∃ α : Matrix ι ι ℂ, α.IsHermitian ∧ ContinuousLinearMap.SatisfiesKLConditions P E α

/-- **Nielsen & Chuang, Theorem 10.1, for a quantum system.** For a **nonzero** orthogonal code
projector `P` (self-adjoint idempotent) on a quantum system `S` and a finite family of noise
operation elements `E`, the quantum error-correction conditions hold **iff** there is a
**trace-preserving** recovery family `R` (`∑ₒ Rₒ† Rₒ = 1` — an error-correction operation) that
**corrects** `E` on the code (`ContinuousLinearMap.Corrects P E R`: the composed noise-then-recovery
operator sum returns every operator supported on the code to a scalar multiple of itself).

This is the physics reading of the operator biconditional
`ContinuousLinearMap.satisfiesKLConditions_iff_exists_correction`, for the
system `S` (its state space `S.space`). No assumption is made that `E` is itself a valid
quantum operation (`∑ᵢ Eᵢ† Eᵢ ≤ 1`): the characterisation holds for **any** family of operation
elements, a faithful generalisation of N&C's statement (which takes `E` a quantum operation). -/
theorem satisfiesQECConditions_iff_exists_correction {P : S.space →L[ℂ] S.space}
    {E : ι → S.space →L[ℂ] S.space}
    (hP : IsSelfAdjoint P) (hPidem : P ∘L P = P) (hP0 : P ≠ 0) :
    SatisfiesQECConditions P E ↔
      ∃ (κ : Type uι) (_ : Fintype κ) (R : κ → S.space →L[ℂ] S.space),
        (∑ o, ContinuousLinearMap.adjoint (R o) ∘L R o = 1) ∧
          ContinuousLinearMap.Corrects P E R :=
  (ContinuousLinearMap.satisfiesKLConditions_iff_exists_correction hP hPidem hP0).symm

/-- **The physical reading of the sufficiency of the quantum error-correction conditions** (Nielsen
& Chuang, Theorem 10.1). If the QEC conditions hold for a nonzero orthogonal code projector `P` and
noise operation elements `E`, then there is an **error-correction channel**
`rec : State S → State S` (a genuine quantum channel, `IsChannel`) with Kraus family `R`, and a
**single** nonnegative constant `λ` — depending only on `P`, `E`, `R`, not on the state — such that
for **every** code state `ρ`
(`P ρ P = ρ`),

  `krausSumₗ R (krausSumₗ E ρ) = λ • ρ`.

The recovery channel's operator action is `krausSumₗ R` (`hrec`), so the displayed identity says the
composed noise-then-recovery process returns every code state to the *same* scalar multiple of
itself — N&C's `R(E(ρ)) ∝ ρ` (Eq. (10.15)) with a **state-independent** constant `λ`, the hallmark
of genuine error-correction (it preserves code-state superpositions). The uniform `λ ≥ 0` is N&C's
remark that the proportionality factor "must be a constant, if both sides are to be linear"
(Eq. (10.28)); it is derived, not assumed (`Corrects.exists_nonneg_forall_eq_smul`). -/
theorem SatisfiesQECConditions.exists_correctionChannel {P : S.space →L[ℂ] S.space}
    {E : ι → S.space →L[ℂ] S.space}
    (hP : IsSelfAdjoint P) (hPidem : P ∘L P = P) (hP0 : P ≠ 0)
    (h : SatisfiesQECConditions P E) :
    ∃ (κ : Type uι) (_ : Fintype κ) (R : κ → S.space →L[ℂ] S.space) (rec : State S → State S),
      IsChannel rec ∧ (∀ ρ : State S, (rec ρ).op = ContinuousLinearMap.krausSumₗ R ρ.op) ∧
        ∃ lam : ℝ, 0 ≤ lam ∧ ∀ ρ : State S, P ∘L ρ.op ∘L P = ρ.op →
          ContinuousLinearMap.krausSumₗ R (ContinuousLinearMap.krausSumₗ E ρ.op)
            = (lam : ℂ) • ρ.op := by
  obtain ⟨α, hα, hE⟩ := h
  obtain ⟨κ, hκ, R, hR, hcorr⟩ :=
    ContinuousLinearMap.corrects_of_satisfiesKLConditions hP hPidem hP0 hα hE
  let : Fintype κ := hκ
  obtain ⟨rec, hrecCh, hrecOp⟩ := exists_isChannel_of_completeness R hR
  obtain ⟨lam, hlam0, hlam⟩ := hcorr.exists_nonneg_forall_eq_smul hP hPidem hP0
  refine ⟨κ, hκ, R, rec, hrecCh, hrecOp, lam, hlam0, fun ρ hρ => ?_⟩
  have hρ' := hlam ρ.op
  rwa [hρ] at hρ'

/-- **Discretization of the quantum error-correction conditions under linear recombination of the
errors** — the QEC-predicate form of Nielsen & Chuang's discretization of errors (Theorem 10.2). If
a code projector `P` and a finite noise error family `E : ι → S.space →L[ℂ] S.space` satisfy the QEC
conditions, then so does **any** family `F : κ → S.space →L[ℂ] S.space` each of whose members is a
linear combination `F k = ∑ i, u i k • E i` of the `E i` (for a matrix `u : Matrix ι κ ℂ` of
scalars). The recombined family is allowed to have a *different* (e.g. larger) number of members
(`κ ≠ ι`).

This is exactly N&C's principle that "any error process whose operation elements are linear
combinations of a correctable set is itself corrected" (p. 440), stated for the conditions
themselves: the new Hermitian coefficient matrix is the Gram-type conjugate `uᴴ α u` (Hermitian
because `α` is), and the recombined conditions follow from
`ContinuousLinearMap.SatisfiesKLConditions.recombine`. A typical use: a code that corrects the
Pauli set `{I, Zᵢ}` automatically corrects any set of projectors/operators built from them, since
each is a linear combination of the `Zᵢ`. -/
theorem SatisfiesQECConditions.recombine {κ : Type*}
    {P : S.space →L[ℂ] S.space} {E : ι → S.space →L[ℂ] S.space}
    (h : SatisfiesQECConditions P E) (u : Matrix ι κ ℂ) {F : κ → S.space →L[ℂ] S.space}
    (hF : ∀ k, F k = ∑ i, u i k • E i) :
    SatisfiesQECConditions P F := by
  obtain ⟨α, hα, hE⟩ := h
  refine ⟨uᴴ * α * u, Matrix.isHermitian_conjTranspose_mul_mul u hα, ?_⟩
  rw [funext hF]
  exact hE.recombine u

end AxQM
