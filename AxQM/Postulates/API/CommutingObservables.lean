/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Observable
import ToMathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# AxQM.Postulates.API — commuting observables share a common eigenbasis

Commuting families of observables.

* `Observable.Commutes A B` — the predicate "`A` and `B` commute", `[A, B] = 0`, defined as
  `Commute` of the underlying self-adjoint operators.
* `Observable.exists_commonEigenbasis_of_pairwise_commute` — **simultaneous diagonalization of
  commuting observables**: a finite family of pairwise-commuting observables has a single
  orthonormal eigenbasis `b` with real eigenvalue functions `X`, `Mⱼ (bᵢ) = Xⱼᵢ • bᵢ`. This is the
  physical content behind *co-measurability* (Nielsen & Chuang, Exercise 12.33): commuting
  observables can be measured simultaneously, so one projective measurement in `b` reads them all.

The construction reduces to the general-mathematics lemma
`LinearMap.IsSymmetric.exists_orthonormalBasis_forall_apply_eq_smul_of_pairwise_commute` (the
`n`-operator simultaneous-diagonalization theorem in `ToMathlib/`), then upgrades the scalar
eigenvalues to **real** numbers using the self-adjointness of each observable — an observable's
eigenvalues are its real possible measurement values.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Two observables commute** (`[A, B] = 0`): their underlying self-adjoint operators commute.
-/
def Observable.Commutes (A B : Observable S) : Prop := Commute A.op B.op

/-- `A.Commutes B` unfolds to the operator commutation `A B = B A`. -/
theorem Observable.commutes_iff_op {A B : Observable S} :
    A.Commutes B ↔ A.op * B.op = B.op * A.op := Iff.rfl

/-- Commutation of observables is symmetric. -/
theorem Observable.Commutes.symm {A B : Observable S} (h : A.Commutes B) : B.Commutes A :=
  Commute.symm h

/-- **Simultaneous diagonalization of commuting observables.** A finite family `M` of
pairwise-commuting observables on a system `S` shares a single orthonormal eigenbasis `b`: there is
an orthonormal basis `b` and real eigenvalue functions `X` with `Mⱼ (bᵢ) = Xⱼᵢ • bᵢ` for every
observable index `j` and basis index `i`. Every `Mⱼ` is diagonal in the one basis `b`, so the family
is *co-measurable* — a single projective measurement in `b` determines every observable's value.

The eigenvalues are real because each `Mⱼ` is self-adjoint (`⟪bᵢ, Mⱼ bᵢ⟫ = μⱼᵢ` is its own complex
conjugate). The underlying orthonormal basis of common eigenvectors comes from the family
simultaneous-diagonalization theorem in `ToMathlib/`,
`LinearMap.IsSymmetric.exists_orthonormalBasis_forall_apply_eq_smul_of_pairwise_commute`. -/
theorem Observable.exists_commonEigenbasis_of_pairwise_commute {ι : Type*} [Finite ι]
    (M : ι → Observable S) (hM : ∀ i j, (M i).Commutes (M j)) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ S.space)) ℂ S.space)
      (X : ι → Fin (Module.finrank ℂ S.space) → ℝ),
      ∀ j i, (M j).op (b i) = (X j i : ℂ) • b i := by
  -- Each observable is symmetric, and the family pairwise-commutes as linear maps.
  have hT : ∀ j, ((M j).op.toLinearMap).IsSymmetric := fun j => (M j).isSymmetric
  have hC : Pairwise (Function.onFun Commute (fun j => (M j).op.toLinearMap)) := by
    intro i j _
    exact (hM i j).map ContinuousLinearMap.toLinearMapRingHom
  obtain ⟨b, μ, hb⟩ :=
    LinearMap.IsSymmetric.exists_orthonormalBasis_forall_apply_eq_smul_of_pairwise_commute hT hC
  simp only [ContinuousLinearMap.coe_coe] at hb
  refine ⟨b, fun j i => (μ j i).re, fun j i => ?_⟩
  -- `μ j i = ⟪bᵢ, Mⱼ bᵢ⟫` is real by self-adjointness, so it equals its own real part.
  have hinner : ⟪b i, (M j).op (b i)⟫_ℂ = μ j i := by
    rw [hb j i, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i i]; simp
  have hreal : (starRingEnd ℂ) (μ j i) = μ j i := by
    rw [← hinner, inner_conj_symm]; exact (M j).isSymmetric (b i) (b i)
  rw [hb j i, Complex.conj_eq_iff_re.mp hreal]

end AxQM
