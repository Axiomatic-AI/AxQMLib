/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.CStarAlgebra.Unitary.Exp
public import ToMathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Every unitary endomorphism of a finite-dimensional Hilbert space is `exp (i • A)`

`CStarMatrix.exists_expUnitary_eq_of_mem_unitary` (Nielsen & Chuang, *Quantum Computation and
Quantum Information*, Exercise 2.56) states that every unitary `n × n` matrix is `exp (i K)` for a
Hermitian matrix `K`. This file gives the coordinate-free counterpart, for continuous linear
endomorphisms of a finite-dimensional complex Hilbert space:

* `ContinuousLinearMap.exists_isSelfAdjoint_exp_smul_I_eq_of_mem_unitary` — for a
  finite-dimensional complex inner product space `E`, every unitary `U : E →L[ℂ] E` equals
  `exp (i • A)` for some self-adjoint `A : E →L[ℂ] E`.

## Proof outline

`E →L[ℂ] E` is itself a C⋆-algebra, so the general
`expUnitary_argSelfAdjoint_of_continuousOn_arg` applies: its only hypothesis is that
`Complex.arg` is continuous on `spectrum ℂ U`. That continuity is automatic here because the
spectrum is *finite* — the spectrum of `U` as a continuous linear map coincides with that of the
underlying linear map (`ContinuousLinearMap.spectrum_eq`), which is finite in finite dimensions
(`Module.End.finite_spectrum`). The witness is then `A = Unitary.argSelfAdjoint U` (`= -i log U`),
self-adjoint by construction. Unlike the general `expUnitary_argSelfAdjoint`, no `‖U - 1‖ < 2`
restriction is needed — finiteness of the spectrum supplies the continuity in full.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder

namespace ContinuousLinearMap

/-- **Every unitary endomorphism of a finite-dimensional complex Hilbert space is the exponential
of `i` times a self-adjoint operator.** The coordinate-free form of Nielsen & Chuang Exercise 2.56
(`CStarMatrix.exists_expUnitary_eq_of_mem_unitary`): for a unitary `U : E →L[ℂ] E` there is a
self-adjoint `A : E →L[ℂ] E` with `exp (i • A) = U`. Physically, `A` is a Hamiltonian generating
the unitary `U` (up to sign, `A = -i log U`).

The witness is `A = Unitary.argSelfAdjoint U`; the recovery `exp (i • A) = U` holds because a
finite-dimensional operator has finite spectrum, on which the principal argument is continuous
(`expUnitary_argSelfAdjoint_of_continuousOn_arg`). -/
theorem exists_isSelfAdjoint_exp_smul_I_eq_of_mem_unitary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E] {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) :
    ∃ A : E →L[ℂ] E, IsSelfAdjoint A ∧ NormedSpace.exp (Complex.I • A) = U := by
  let u : unitary (E →L[ℂ] E) := ⟨U, hU⟩
  -- A finite-dimensional operator has finite spectrum (that of its underlying linear map), so the
  -- principal-argument function is continuous on it.
  have hfin : (spectrum ℂ (u : E →L[ℂ] E)).Finite := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact Module.End.finite_spectrum _
  -- The self-adjoint `A = -i log U` (`Unitary.argSelfAdjoint`) then satisfies `exp (i • A) = U`,
  -- with no restriction on the spectrum: the `‖u - 1‖ < 2` hypothesis of
  -- `expUnitary_argSelfAdjoint` is replaced by the continuity that finiteness supplies.
  have hrec := expUnitary_argSelfAdjoint_of_continuousOn_arg (u := u) (hfin.continuousOn _)
  refine ⟨(Unitary.argSelfAdjoint u : E →L[ℂ] E),
    selfAdjoint.mem_iff.mp (Unitary.argSelfAdjoint u).2, ?_⟩
  rw [← selfAdjoint.expUnitary_coe, hrec]

/-- **Every unitary endomorphism of a finite-dimensional complex Hilbert space is `exp (-i • A)`
for a self-adjoint `A` whose spectrum lies in `[0, 2π]`.** This refines
`exists_isSelfAdjoint_exp_smul_I_eq_of_mem_unitary` by fixing the branch of the logarithm: writing
`U = exp (-i A)`, the self-adjoint generator `A` can be chosen with every eigenvalue a real number
in `[0, 2π]` (`spectrum ℂ A ⊆ ℝ ∩ [0, 2π]`). This is the operator content of Nielsen & Chuang,
*Quantum Computation and Quantum Information*, Problem 4.3(1): `H = i log U` is Hermitian with
eigenvalues in the range `0` to `2π`.

The witness is `A = cfc β U`, where `β z` is the unique argument in `[0, 2π)` for which
`exp (-i β z) = z` on the unit circle (`β z = -arg z` for `arg z ≤ 0`, else `2π - arg z`).
Self-adjointness holds since
`β` is real-valued; the spectral bound is the spectral mapping theorem (`cfc_map_spectrum`) together
with `β '' (unit circle) ⊆ [0, 2π)`; and the recovery `exp (-i • A) = U` reduces, via the continuous
functional calculus, to `exp (-i β z) = z` on the spectrum, where finiteness of the spectrum
supplies the continuity `β` needs.

The spectral bound is phrased over `spectrum ℂ` (as `A`'s eigenvalues are real numbers lying in the
interval `[0, 2π]`) rather than `spectrum ℝ`, avoiding the auxiliary `Algebra ℝ`/`IsScalarTower`
scaffolding of the real functional calculus; for the self-adjoint `A`, `spectrum ℝ A` is the real
part of `spectrum ℂ A`, so the two formulations carry the same content. -/
theorem exists_isSelfAdjoint_spectrum_Icc_exp_neg_smul_I_eq_of_mem_unitary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E] {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) :
    ∃ A : E →L[ℂ] E, IsSelfAdjoint A ∧
      spectrum ℂ A ⊆ Complex.ofReal '' Set.Icc 0 (2 * Real.pi) ∧
      NormedSpace.exp (-Complex.I • A) = U := by
  classical
  set u : unitary (E →L[ℂ] E) := ⟨U, hU⟩ with hu
  have : IsStarNormal (u : E →L[ℂ] E) := isStarNormal_of_mem_unitary u.2
  -- The `[0, 2π)`-branch of `i log`: `β z` is the argument in `[0, 2π)` with `exp (-i β z) = z`.
  set β : ℂ → ℂ := fun z => ((if z.arg ≤ 0 then -z.arg else 2 * Real.pi - z.arg : ℝ) : ℂ) with hβ
  have hfin : (spectrum ℂ (u : E →L[ℂ] E)).Finite := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact Module.End.finite_spectrum _
  have hcont : ContinuousOn β (spectrum ℂ (u : E →L[ℂ] E)) := hfin.continuousOn _
  have hsa : IsSelfAdjoint (cfc β (u : E →L[ℂ] E)) := by
    change star (cfc β (u : E →L[ℂ] E)) = cfc β (u : E →L[ℂ] E)
    rw [← cfc_star]
    exact cfc_congr fun z _ => by simp [hβ, Complex.conj_ofReal]
  refine ⟨cfc β (u : E →L[ℂ] E), hsa, ?_, ?_⟩
  · -- Spectral bound: `spectrum ℂ (cfc β u) = β '' spectrum ℂ u`, and `β z ∈ ofReal '' [0, 2π]`.
    rw [cfc_map_spectrum β (u : E →L[ℂ] E)]
    rintro _ ⟨z, _, rfl⟩
    have ha1 := Complex.neg_pi_lt_arg z
    have ha2 := Complex.arg_le_pi z
    have hpi := Real.pi_pos
    refine ⟨if z.arg ≤ 0 then -z.arg else 2 * Real.pi - z.arg, ?_, by simp [hβ]⟩
    constructor <;> · split_ifs <;> linarith
  · -- Recovery: `exp (-i • cfc β u) = cfc (fun z => exp (-i β z)) u = cfc id u = u`.
    change NormedSpace.exp (-Complex.I • cfc β (u : E →L[ℂ] E)) = (u : E →L[ℂ] E)
    rw [(cfc_smul (-Complex.I) β (u : E →L[ℂ] E)).symm, ← CFC.complex_exp_eq_normedSpace_exp,
      ← cfc_comp' Complex.exp (fun z => -Complex.I • β z) (u : E →L[ℂ] E)]
    conv_rhs => rw [← cfc_id' ℂ (u : E →L[ℂ] E)]
    refine cfc_congr fun z hz => ?_
    have hz1 : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hz
    have hrec := Complex.norm_mul_exp_arg_mul_I z
    rw [hz1] at hrec
    simp only [hβ]
    rcases le_or_gt z.arg 0 with h | h
    · have he : -Complex.I • ((-z.arg : ℝ) : ℂ) = (z.arg : ℂ) * Complex.I := by
        rw [smul_eq_mul]; push_cast; ring
      rw [ite_eq_left h, he]
      simpa using hrec
    · have he : -Complex.I • ((2 * Real.pi - z.arg : ℝ) : ℂ)
          = (z.arg : ℂ) * Complex.I - 2 * (Real.pi : ℂ) * Complex.I := by
        rw [smul_eq_mul]; push_cast; ring
      rw [ite_eq_right (not_le.mpr h), he, Complex.exp_sub, Complex.exp_two_pi_mul_I]
      simpa using hrec

end ContinuousLinearMap
