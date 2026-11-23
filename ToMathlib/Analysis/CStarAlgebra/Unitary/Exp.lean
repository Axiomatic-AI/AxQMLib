/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Every unitary matrix is the exponential of a Hermitian matrix

For a unitary `u` in a unital C⋆-algebra `A`, Mathlib defines the selfadjoint element
`Unitary.argSelfAdjoint u = cfc arg u` (the "argument" `-i log u`), and proves
`selfAdjoint.expUnitary (argSelfAdjoint u) = u` — i.e. `exp (i • argSelfAdjoint u) = u` — but
**only** when `‖u - 1‖ < 2` (equivalently `-1 ∉ spectrum ℂ u`), which is what keeps `Complex.arg`
continuous on the spectrum (`expUnitary_argSelfAdjoint`).

The single obstruction to dropping that hypothesis is the *continuity* of `Complex.arg` on
`spectrum ℂ u`. We isolate the general statement
`expUnitary_argSelfAdjoint_of_continuousOn_arg`, whose only hypothesis is that continuity, and
then discharge it unconditionally for **matrices**: a square matrix has a finite spectrum
(`Matrix.finite_spectrum`), and every function is continuous on a finite subset of a `T1Space`
(`Set.Finite.continuousOn`).

The matrix results are phrased for `CStarMatrix n n ℂ`, i.e. `n × n` complex matrices carrying the
C⋆-algebra (operator) norm — the honest C⋆-algebra of matrices, and the setting in which the
`Unitary.argSelfAdjoint` / `selfAdjoint.expUnitary` machinery lives. Recall `selfAdjoint.expUnitary`
is by definition `x ↦ exp (i • x)` (`selfAdjoint.expUnitary_coe`), and a selfadjoint matrix is
exactly a Hermitian one, so these say precisely: **every unitary matrix `U` can be written as
`exp (i K)` for a Hermitian `K`** (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 2.56; `K = -i log U = argSelfAdjoint U`).

## Main results

* `expUnitary_argSelfAdjoint_of_continuousOn_arg`: in any unital C⋆-algebra, if `Complex.arg` is
  continuous on `spectrum ℂ u` then `selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u`. This
  generalises `expUnitary_argSelfAdjoint` by replacing `‖u - 1‖ < 2` with its sole
  consequence used in the proof.
* `CStarMatrix.finite_spectrum`: the spectrum of a square C⋆-matrix over `ℂ` is finite.
* `CStarMatrix.expUnitary_argSelfAdjoint`: for every unitary matrix `u`,
  `selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u`, with no restriction on the spectrum.
* `CStarMatrix.expUnitary_surjective`: `selfAdjoint.expUnitary` maps the selfadjoint (Hermitian)
  matrices *onto* the unitary matrices.
* `CStarMatrix.exists_expUnitary_eq_of_mem_unitary`: every unitary matrix `U` equals
  `selfAdjoint.expUnitary K = exp (i K)` for some Hermitian `K`.
-/

@[expose] public section

open Complex NormedSpace selfAdjoint Unitary
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

/-- **Recovery of a unitary from its argument.** In a unital C⋆-algebra, if the principal argument
`Complex.arg` is continuous on the spectrum of a unitary `u`, then
`selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u`, i.e. `exp (i • (-i log u)) = u`.

This generalises `expUnitary_argSelfAdjoint`, which assumes `‖u - 1‖ < 2`
(equivalently `-1 ∉ spectrum ℂ u`); that hypothesis is used solely to obtain the continuity
required here. -/
theorem expUnitary_argSelfAdjoint_of_continuousOn_arg {u : unitary A}
    (hu : ContinuousOn Complex.arg (spectrum ℂ (u : A))) :
    selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u := by
  ext
  have : ContinuousOn arg (spectrum ℂ (u : A)) := hu
  rw [expUnitary_coe, argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : Complex.I * y.arg = Complex.log y :=
    Complex.ext (by simp [Complex.log_re, spectrum.norm_eq_one_of_unitary u.2 hy])
      (by simp [Complex.log_im])
  simpa [← exp_eq_exp_ℂ, this] using Complex.exp_log (by aesop)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectrum of a square C⋆-matrix over `ℂ` is finite: it is the finite spectrum of the
underlying `Matrix` (`Matrix.finite_spectrum`), transported along the star-algebra isomorphism
`CStarMatrix.ofMatrixStarAlgEquiv`. -/
theorem CStarMatrix.finite_spectrum (u : CStarMatrix n n ℂ) : (spectrum ℂ u).Finite := by
  have h := Matrix.finite_spectrum (CStarMatrix.ofMatrix.symm u)
  have he : CStarMatrix.ofMatrixStarAlgEquiv.toAlgEquiv (CStarMatrix.ofMatrix.symm u) = u :=
    CStarMatrix.ofMatrix.apply_symm_apply u
  rw [← he, AlgEquiv.spectrum_eq]
  exact h

/-- **Every unitary matrix is recovered from its argument.** For any unitary matrix `u`,
`selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u`, i.e. `exp (i • (-i log u)) = u`.

Unlike the general C⋆-algebra statement `expUnitary_argSelfAdjoint`, no hypothesis on the
spectrum is needed: the spectrum of a matrix is finite, so `Complex.arg` is automatically continuous
on it. -/
theorem CStarMatrix.expUnitary_argSelfAdjoint (u : unitary (CStarMatrix n n ℂ)) :
    selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u :=
  expUnitary_argSelfAdjoint_of_continuousOn_arg <|
    (CStarMatrix.finite_spectrum (u : CStarMatrix n n ℂ)).continuousOn _

/-- **`exp (i •)` is surjective onto the unitary matrices.** The map `selfAdjoint.expUnitary`,
sending a selfadjoint (Hermitian) matrix `K` to the unitary `exp (i K)`, is surjective; a preimage
of `u` is `Unitary.argSelfAdjoint u = -i log u`. -/
theorem CStarMatrix.expUnitary_surjective :
    Function.Surjective
      (selfAdjoint.expUnitary : selfAdjoint (CStarMatrix n n ℂ) → unitary (CStarMatrix n n ℂ)) :=
  fun u => ⟨Unitary.argSelfAdjoint u, CStarMatrix.expUnitary_argSelfAdjoint u⟩

/-- **Nielsen & Chuang, Exercise 2.56.** Every unitary matrix `U` can be written as `exp (i K)` for
some Hermitian matrix `K`. Here `K` ranges over `selfAdjoint (CStarMatrix n n ℂ)` (the Hermitian
matrices) and `selfAdjoint.expUnitary K` is `exp (i • K)` by `selfAdjoint.expUnitary_coe`; a witness
is `K = Unitary.argSelfAdjoint U = -i log U`. -/
theorem CStarMatrix.exists_expUnitary_eq_of_mem_unitary
    {U : CStarMatrix n n ℂ} (hU : U ∈ unitary (CStarMatrix n n ℂ)) :
    ∃ K : selfAdjoint (CStarMatrix n n ℂ), (selfAdjoint.expUnitary K : CStarMatrix n n ℂ) = U :=
  ⟨Unitary.argSelfAdjoint ⟨U, hU⟩,
    congrArg Subtype.val (CStarMatrix.expUnitary_argSelfAdjoint ⟨U, hU⟩)⟩
