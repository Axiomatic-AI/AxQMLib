/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SameNonzeroSpectrum
import ToMathlib.Analysis.InnerProductSpace.SingularValues

/-!
# AxQM.Postulates.API — isospectrality of `X X†` and `X† X`

The reusable spectral fact `X X† ≅ X† X`: for any operator `X : S.space →L[ℂ] T.space` between two
quantum systems, the two positive operators `X X†` (on `T`) and `X† X` (on `S`) have the *same
non-zero spectrum*. Packaged at the state level as
`State.sameNonzeroSpectrum_of_op_eq_smul_comp_adjoint`: if two states `ρ`, `σ` have density
operators `ρ.op = c • (X X†)` and `σ.op = c • (X† X)` (the same real scalar `c`), then
`ρ.SameNonzeroSpectrum σ`.

This is the operator-conjugation companion of the existing structural invariances of `≅`
(`State.sameNonzeroSpectrum_evolve` for a *unitary* conjugation,
`State.sameNonzero_eigenvalueDist_tmul` for a product). It is the load-bearing linear-algebra fact
behind **Nielsen & Chuang, Proposition 12.14** away from the swap-symmetric normal form
(`AxQM/NC/Ch12/Proposition12_14.lean`): a post-measurement reduced operator has the shape `M ρ M†`
(`AxQM/Postulates/API/ReducedStateOneFactor.lean`), which is `(M √ρ)(M √ρ)†`, so comparing Bob's
`M_j ρ_B M_j†` with Alice's simulating `N_j ρ_A N_j†` proceeds by repeatedly flipping such
conjugations `Y Y† ≅ Y† Y` — the manoeuvre this lemma performs.

## The proof

Both `X X†` and `X† X` are diagonalised by singular vectors with the squared singular values as
eigenvalues (`ContinuousLinearMap.adjoint_comp_self_apply_svdRight`, applied to `X` and — via the
involutivity of the adjoint — to `X†`), and the singular values are adjoint-invariant
(`ContinuousLinearMap.singularValues_adjoint`). So each of `ρ.eigenvalueDist`, `σ.eigenvalueDist`
has the same
non-zero entries as the family `i ↦ c · (sᵢ)²` (`State.sameNonzero_eigenvalueDist_of_isEigenbasis`),
indexed over `Fin (finrank T.space)` resp. `Fin (finrank S.space)`. Those two families are `≅` by
the heterogeneous-index bridge `sameNonzero_fin_val`: both are the single sequence `n ↦ c · (sₙ)²`
truncated to a `Fin`-range covering its support
(`singularValues_eq_zero_iff_le_finrank_range` locates the support at `[0, finrank X.range)`, which
sits inside both dimensions by `finrank_range_le`).
-/

open ContinuousLinearMap (adjoint)

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **A `Y† Y` conjugation is diagonal in `Y`'s right singular vectors.** For any operator
`Y : A.space →L[ℂ] B.space` and real scalar `c`, a state whose density operator is
`τ.op = c • (Y† Y)` has eigenvalue distribution with the same non-zero entries as
`i ↦ c · (Y.singularValues i)²`: the
right singular vectors `Y.svdRight` diagonalise `Y† Y` with eigenvalues the squared singular values
(`ContinuousLinearMap.adjoint_comp_self_apply_svdRight`), which recognition
(`State.sameNonzero_eigenvalueDist_of_isEigenbasis`) identifies with the spectrum. The single-sided
building block behind `State.sameNonzeroSpectrum_of_op_eq_smul_comp_adjoint`, applied there to both
`Y = X` (for `σ = c • X† X`) and `Y = X†` (for `ρ = c • X X† = c • (X†)† X†`). -/
theorem State.sameNonzero_eigenvalueDist_of_op_eq_smul_adjoint_comp_self
    {A B : QSystem} {τ : State A} {Y : A.space →L[ℂ] B.space} {c : ℝ}
    (hτ : τ.op = (c : ℂ) • ((adjoint Y).comp Y)) :
    SameNonzero (fun i : Fin (Module.finrank ℂ A.space) => c * (Y.singularValues ↑i) ^ 2)
      τ.eigenvalueDist := by
  refine τ.sameNonzero_eigenvalueDist_of_isEigenbasis Y.svdRight ?_
  intro i
  rw [hτ, _root_.smul_apply, ContinuousLinearMap.svdRight_toLinearMap,
    ContinuousLinearMap.adjoint_comp_self_apply_svdRight, smul_smul,
    ← ContinuousLinearMap.singularValues_toLinearMap]
  congr 1
  norm_num

/-- **Isospectrality of `X X†` and `X† X`.** For any operator `X : S.space →L[ℂ] T.space` and any
real scalar `c`, two states whose density operators are the two conjugations
`ρ.op = c • (X X†)` (on `T`) and `σ.op = c • (X† X)` (on `S`) have the same non-zero spectrum,
`ρ ≅ σ`. This is the operator-conjugation invariance of `State.SameNonzeroSpectrum`: swapping the
order of a factor and its adjoint preserves the non-zero eigenvalues (with multiplicity), the
state-level form of the fact that `X X†` and `X† X` share the squared singular values of `X` as
their non-zero spectrum.

It is the workhorse behind Nielsen & Chuang Proposition 12.14's measurement-simulation argument off
the swap-symmetric normal form: a post-measurement reduced operator `M ρ M† = (M √ρ)(M √ρ)†`
(`Measurement.reducedRight_postMeasurement_onRight_op`) is a conjugation `Y Y†`, and comparing Bob's
and Alice's post-measurement marginals reduces — via the Schmidt-basis identification `W` — to
flipping such conjugations `Y Y† ≅ Y† Y`. -/
theorem State.sameNonzeroSpectrum_of_op_eq_smul_comp_adjoint
    {ρ : State T} {σ : State S} {X : S.space →L[ℂ] T.space} {c : ℝ}
    (hρ : ρ.op = (c : ℂ) • (X.comp (adjoint X)))
    (hσ : σ.op = (c : ℂ) • ((adjoint X).comp X)) :
    ρ.SameNonzeroSpectrum σ := by
  -- The common eigenvalue sequence `n ↦ c · sₙ²` vanishes beyond the rank of `X`.
  have hzero : ∀ n, Module.finrank ℂ (↑X : S.space →ₗ[ℂ] T.space).range ≤ n →
      c * (X.singularValues n) ^ 2 = 0 := by
    intro n hn
    have hn0 : X.singularValues n = 0 := by
      rw [ContinuousLinearMap.singularValues_toLinearMap]
      exact (LinearMap.singularValues_eq_zero_iff_le_finrank_range _).2 hn
    simp [hn0]
  -- `σ.op = c • X† X` is diagonal in `X`'s right singular vectors with eigenvalues `c · sᵢ²`.
  have hσrec := State.sameNonzero_eigenvalueDist_of_op_eq_smul_adjoint_comp_self hσ
  -- `ρ.op = c • X X† = c • (X†)† X†`: the same fact for `X†`, whose singular values are `X`'s.
  have hρrec : SameNonzero (fun i : Fin (Module.finrank ℂ T.space) =>
      c * (X.singularValues ↑i) ^ 2) ρ.eigenvalueDist := by
    simpa only [ContinuousLinearMap.singularValues_adjoint] using
      State.sameNonzero_eigenvalueDist_of_op_eq_smul_adjoint_comp_self
        (τ := ρ) (Y := adjoint X) (c := c) (by rw [hρ, ContinuousLinearMap.adjoint_adjoint])
  -- The two eigenvalue families differ only in their index range; both cover `X`'s support.
  have hbridge := sameNonzero_fin_val (w := fun n => c * (X.singularValues n) ^ 2)
    (m := Module.finrank ℂ T.space) (m' := Module.finrank ℂ S.space)
    (k := Module.finrank ℂ (↑X : S.space →ₗ[ℂ] T.space).range)
    (Submodule.finrank_le _) (LinearMap.finrank_range_le _) hzero
  exact hρrec.symm.trans (hbridge.trans hσrec)

end AxQM
