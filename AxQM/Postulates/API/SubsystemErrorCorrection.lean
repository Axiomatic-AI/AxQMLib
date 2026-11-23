/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumErrorCorrection

/-!
# AxQM.Postulates.API — correcting arbitrary errors on a subsystem

Infrastructure for **Nielsen & Chuang, Exercise 12.14** (p. 567): the reference system `R` and the
subsystem `Q₁` on which errors are to be corrected must be *uncorrelated*, `ρ^{RQ1} = ρ^R ⊗ ρ^{Q1}`,
and this decoupling is *sufficient* for the errors on `Q₁` to be correctable. This file establishes
the second, purely code-theoretic half of that statement — the bridge from a *decoupling*
hypothesis to *correctability* is the subsystem specialisation of the Knill–Laflamme conditions
(N&C Theorem 10.1); the decoupling hypothesis itself is turned into the condition below in
`AxQM/Postulates/API/SubsystemErrorCorrectionDecoupling.lean` and
`AxQM/Postulates/API/SubsystemErrorCorrectionProtection.lean`.

## The subsystem-protection condition

Write the coded system as a composite `Q₁ ⊗ Q₂`, with `Q₁` the subsystem on which errors occur. An
operator acting on `Q₁` and leaving `Q₂` alone is `A ⊗ I_{Q₂}` (`leftFactorOp A`); an *arbitrary*
error on `Q₁` is a linear combination of these, and the complete such family, in an orthonormal
basis `b` of `Q₁`, is the matrix-unit family `leftFactorErrorBasis b (a, c) = |b a⟩⟨b c| ⊗ I_{Q₂}`.
A code projector `P` on `Q₁ ⊗ Q₂` **protects the left factor `Q₁`** (`ProtectsLeftFactor P`) when

`∀ A : Q₁ → Q₁, ∃ c : ℂ, P (A ⊗ I_{Q₂}) P = c • P`,

i.e. the code "does not see" any operator acting on `Q₁`.

## Contents

* `AxQM.leftFactorOp` — the lift `A ↦ A ⊗ I_{Q₂}` of a `Q₁`-operator to `Q₁ ⊗ Q₂` (a single
  wrapper for `TensorProduct.mapL A 1`, so its adjoint/composition/scalar algebra is stated once).
* `AxQM.leftFactorErrorBasis` — the complete matrix-unit error family `{|b a⟩⟨b c| ⊗ I}`.
* `AxQM.ProtectsLeftFactor` — the subsystem-protection predicate above.
* `AxQM.ProtectsLeftFactor.satisfiesQECConditions` — protection **implies** the
  Knill–Laflamme quantum error-correction conditions (`SatisfiesQECConditions`, N&C Theorem 10.1)
  for the complete `Q₁`-error family. The coefficient matrix is
  `α_{(a,c),(a',c')} = δ_{a a'} · γ_{c c'}`, where `γ_{c c'}` is the (unique, since `P ≠ 0`)
  protection scalar at `A = |b c⟩⟨b c'|`, and Hermiticity of `α` is the conjugate symmetry
  `γ_{c' c} = conj γ_{c c'}` (adjoint the sandwich `P (A ⊗ I) P`, using `P† = P`, and cancel `P`).

Since the complete family `leftFactorErrorBasis b` spans every operator on `Q₁`, this is exactly
"the errors on `Q₁` can be corrected": feeding `satisfiesQECConditions` into the sufficiency
direction of N&C Theorem 10.1 (`satisfiesQECConditions_iff_exists_correction` /
`SatisfiesQECConditions.exists_correctionChannel`) exhibits the recovery. That final composition,
and its assembly with the decoupling condition `ρ^{RQ1} = ρ^R ⊗ ρ^{Q1} ⟹ ProtectsLeftFactor`, is
in `AxQM/Postulates/API/SubsystemErrorCorrectionSufficiency.lean`.
-/

open scoped TensorProduct
open InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

variable {Q₁ Q₂ : QSystem}

/-- The lift `A ↦ A ⊗ I_{Q₂}` of an operator on the left factor `Q₁` to the composite `Q₁ ⊗ Q₂`
(the operator that acts by `A` on `Q₁` and does nothing on `Q₂`), as `TensorProduct.mapL A 1`.
Wrapping the tensor-product map in a named definition keeps every occurrence of `A ⊗ I` in one
normal form, so the adjoint/composition/scalar lemmas below can be applied by rewriting. -/
def leftFactorOp (A : Q₁.space →L[ℂ] Q₁.space) : (Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space :=
  TensorProduct.mapL A (1 : Q₂.space →L[ℂ] Q₂.space)

/-- The adjoint of `A ⊗ I_{Q₂}` is `A† ⊗ I_{Q₂}`. -/
theorem leftFactorOp_adjoint (A : Q₁.space →L[ℂ] Q₁.space) :
    adjoint (leftFactorOp (Q₂ := Q₂) A) = leftFactorOp (adjoint A) := by
  change adjoint (TensorProduct.mapL A (1 : Q₂.space →L[ℂ] Q₂.space))
    = TensorProduct.mapL (adjoint A) 1
  rw [TensorProduct.adjoint_mapL, ← ContinuousLinearMap.star_eq_adjoint (1 : _), star_one]

/-- Composing left-factor operators multiplies the `Q₁`-parts: `(A ⊗ I)(B ⊗ I) = (A B) ⊗ I`. -/
theorem leftFactorOp_comp (A B : Q₁.space →L[ℂ] Q₁.space) :
    (leftFactorOp (Q₂ := Q₂) A).comp (leftFactorOp B) = leftFactorOp (A.comp B) := by
  change (TensorProduct.mapL A (1 : Q₂.space →L[ℂ] Q₂.space)).comp (TensorProduct.mapL B 1)
    = TensorProduct.mapL (A.comp B) 1
  rw [← TensorProduct.mapL_comp]
  congr 1

/-- The left-factor lift is `ℂ`-linear: `(c • A) ⊗ I = c • (A ⊗ I)`. -/
theorem leftFactorOp_smul (c : ℂ) (A : Q₁.space →L[ℂ] Q₁.space) :
    leftFactorOp (Q₂ := Q₂) (c • A) = c • leftFactorOp A := by
  change TensorProduct.mapL (c • A) (1 : Q₂.space →L[ℂ] Q₂.space) = c • TensorProduct.mapL A 1
  rw [TensorProduct.mapL_smul_left]

/-- The **complete family of errors on the left factor `Q₁`**, in an orthonormal basis `b` of
`Q₁.space`: the matrix units `|b a⟩⟨b c|` acting on `Q₁`, tensored with the identity on `Q₂`,
`leftFactorErrorBasis b (a, c) = |b a⟩⟨b c| ⊗ I_{Q₂}` (indexed by `ι × ι`). Every operator on `Q₁`
is a linear combination of the `|b a⟩⟨b c|`, so any error acting on the subsystem `Q₁` is a linear
combination of this family; it is the "worst-case" error set for `Q₁`, whose correctability is
equivalent to `Q₁`-subsystem correctability (N&C Ex 12.14). -/
def leftFactorErrorBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ Q₁.space) :
    ι × ι → ((Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space) :=
  fun p => leftFactorOp (rankOne ℂ (b p.1) (b p.2))

/-- A code projector `P` on `Q₁ ⊗ Q₂` **protects the left factor `Q₁`** when the code does not see
any operator acting on `Q₁`: for every `A : Q₁ → Q₁` the sandwich `P (A ⊗ I_{Q₂}) P` is a scalar
multiple of `P`,

`∀ A, ∃ c : ℂ, P (A ⊗ I_{Q₂}) P = c • P`.

This is the subsystem specialisation of the Knill–Laflamme error-correction conditions
(`ProtectsLeftFactor.satisfiesQECConditions`): it says exactly that the code can correct an
arbitrary error on `Q₁`. It is N&C's decoupling condition `ρ^{RQ1} = ρ^R ⊗ ρ^{Q1}` read on the code
projector (Exercise 12.14). -/
def ProtectsLeftFactor (P : (Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space) : Prop :=
  ∀ A : Q₁.space →L[ℂ] Q₁.space, ∃ c : ℂ, P ∘L leftFactorOp A ∘L P = c • P

/-- The product `(|b a⟩⟨b c| ⊗ I)† (|b a'⟩⟨b c'| ⊗ I)` of two members of the complete `Q₁`-error
family collapses to `δ_{a a'} • (|b c⟩⟨b c'| ⊗ I)`: the environment/right factor is untouched, and
on `Q₁` the matrix units compose as `⟨b a, b a'⟩ |b c⟩⟨b c'| = δ_{a a'} |b c⟩⟨b c'|`. This is the
computation underlying the Knill–Laflamme coefficient matrix for the family. -/
theorem leftFactorErrorBasis_adjoint_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ Q₁.space) (a c a' c' : ι) :
    adjoint (leftFactorErrorBasis (Q₂ := Q₂) b (a, c)) ∘L leftFactorErrorBasis (Q₂ := Q₂) b (a', c')
      = (if a = a' then (1 : ℂ) else 0) • leftFactorOp (rankOne ℂ (b c) (b c')) := by
  change adjoint (leftFactorOp (rankOne ℂ (b a) (b c))) ∘L leftFactorOp (rankOne ℂ (b a') (b c'))
    = (if a = a' then (1 : ℂ) else 0) • leftFactorOp (rankOne ℂ (b c) (b c'))
  rw [leftFactorOp_adjoint, adjoint_rankOne, leftFactorOp_comp, rankOne_comp_rankOne,
    orthonormal_iff_ite.mp b.orthonormal a a', leftFactorOp_smul]

/-- **Subsystem protection implies the Knill–Laflamme error-correction conditions.** If a code
projector `P` on `Q₁ ⊗ Q₂` (self-adjoint, nonzero) protects the left factor `Q₁`, then the complete
`Q₁`-error family `leftFactorErrorBasis b` satisfies the quantum error-correction conditions
(`SatisfiesQECConditions`, N&C Theorem 10.1). The Hermitian coefficient matrix is
`α_{(a,c),(a',c')} = δ_{a a'} · γ_{c c'}`, where `γ_{c c'}` is the (unique, as `P ≠ 0`) protection
scalar at `A = |b c⟩⟨b c'|`; the Knill–Laflamme identity is `leftFactorErrorBasis_adjoint_comp`
followed by the defining property of `γ`, and Hermiticity of `α` is the conjugate symmetry
`γ_{c' c} = conj γ_{c c'}`, obtained by taking the adjoint of the sandwich `P (A ⊗ I) P` (using
`P† = P`) and cancelling `P`. -/
theorem ProtectsLeftFactor.satisfiesQECConditions {ι : Type*} [Fintype ι]
    {P : (Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space} (hP : IsSelfAdjoint P) (hP0 : P ≠ 0)
    (b : OrthonormalBasis ι ℂ Q₁.space) (h : ProtectsLeftFactor P) :
    SatisfiesQECConditions P (leftFactorErrorBasis (Q₂ := Q₂) b) := by
  classical
  choose γ hγ using h
  have hPadj : adjoint P = P := by rw [← ContinuousLinearMap.star_eq_adjoint]; exact hP.star_eq
  -- Cancellation `c₁ • P = c₂ • P → c₁ = c₂`, as `P ≠ 0` (Mathlib's general `smul_left_injective`).
  have hcancel : ∀ {c₁ c₂ : ℂ}, c₁ • P = c₂ • P → c₁ = c₂ :=
    fun {_ _} he => smul_left_injective ℂ hP0 he
  -- Conjugate symmetry of the protection scalar under swapping the rank-one legs, by taking the
  -- adjoint of the sandwich `P (|x⟩⟨y| ⊗ I) P` (using `P† = P`) and cancelling `P`.
  have hconj : ∀ x y : Q₁.space, γ (rankOne ℂ y x) = star (γ (rankOne ℂ x y)) := by
    intro x y
    apply hcancel
    have hR : adjoint (γ (rankOne ℂ x y) • P) = star (γ (rankOne ℂ x y)) • P := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_smul, hP.star_eq]
    have hs := congrArg adjoint (hγ (rankOne ℂ x y))
    have hg := hγ (rankOne ℂ y x)
    simp only [ContinuousLinearMap.adjoint_comp, hPadj, leftFactorOp_adjoint, adjoint_rankOne, hR,
      ← ContinuousLinearMap.comp_assoc] at hs hg
    rw [← hg, hs]
  refine ⟨Matrix.of fun p q => if p.1 = q.1 then γ (rankOne ℂ (b p.2) (b q.2)) else 0, ?_, ?_⟩
  · -- `α` is Hermitian.
    ext p q
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases hpq : q.1 = p.1
    · rw [ite_eq_left hpq, ite_eq_left hpq.symm, hconj (b p.2) (b q.2), star_star]
    · rw [ite_eq_right hpq, ite_eq_right (fun h => hpq h.symm), star_zero]
  · -- The Knill–Laflamme identity.
    rw [ContinuousLinearMap.satisfiesKLConditions_iff]
    rintro ⟨a, c⟩ ⟨a', c'⟩
    rw [← ContinuousLinearMap.comp_assoc (adjoint (leftFactorErrorBasis (Q₂ := Q₂) b (a, c)))
        (leftFactorErrorBasis (Q₂ := Q₂) b (a', c')) P, leftFactorErrorBasis_adjoint_comp]
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rw [hγ (rankOne ℂ (b c) (b c')), smul_smul, Matrix.of_apply]
    split_ifs with haa' <;> simp

end AxQM
