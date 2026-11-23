/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import ToMathlib.Analysis.InnerProductSpace.Adjoint
public import ToMathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Real dimension of the self-adjoint elements of a complex star module

For a finite-dimensional complex star module `A` (a complex vector space with a compatible
conjugate-linear involution `star`), the real vector space `selfAdjoint A` of its self-adjoint
elements has real dimension equal to the *complex* dimension of `A`:

`finrank ℝ (selfAdjoint A) = finrank ℂ A`   (`finrank_real_selfAdjoint`).

The complex module `A` splits as the real-internal direct sum of its self-adjoint and skew-adjoint
parts (`StarModule.decomposeProdAdjoint`), and multiplication by `-i` (`skewAdjoint.negIEquiv`) is a
real-linear isomorphism between the two summands, so each has real dimension
`(finrank ℝ A) / 2 = finrank ℂ A` (`finrank_real_of_complex`).

Specialising `A` to the endomorphism algebra `E →L[ℂ] E` of a finite-dimensional complex inner
product space, whose star is the adjoint, gives

`finrank ℝ (selfAdjoint (E →L[ℂ] E)) = (finrank ℂ E)²`
(`finrank_real_selfAdjoint_continuousLinearMap`),

the `d²` real degrees of freedom of a Hermitian operator on a `d`-dimensional space. This is the
ambient dimension in the Carathéodory bound on the number of pure states needed to attain a
channel's Holevo χ quantity (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 12.11).

## Main statements

* `skewAdjoint.negIEquiv` — multiplication by `-i` as a real-linear equivalence
  `skewAdjoint A ≃ₗ[ℝ] selfAdjoint A`.
* `finrank_real_selfAdjoint` — the general star-module identity.
* `finrank_real_selfAdjoint_continuousLinearMap` — the operator specialisation.
-/

public section

/-- **Multiplication by `-i` as a real-linear equivalence `skewAdjoint A ≃ₗ[ℝ] selfAdjoint A`**
for a complex star module `A`. The invertible upgrade of Mathlib's bare real-linear map
`skewAdjoint.negISMul`: multiplication by `i` is a two-sided inverse, since `i • (-i • x) = x`
(`skewAdjoint.I_smul_neg_I`) and `i • s` is skew-adjoint whenever `s` is self-adjoint. -/
noncomputable def skewAdjoint.negIEquiv (A : Type*) [AddCommGroup A] [Module ℂ A]
    [StarAddMonoid A] [StarModule ℂ A] : skewAdjoint A ≃ₗ[ℝ] selfAdjoint A :=
  LinearEquiv.ofBijective skewAdjoint.negISMul
    ⟨fun a b hab => by
      have h1 : Complex.I • (↑(skewAdjoint.negISMul a) : A) =
          Complex.I • ↑(skewAdjoint.negISMul b) := by rw [hab]
      rw [skewAdjoint.I_smul_neg_I, skewAdjoint.I_smul_neg_I] at h1
      exact SetLike.coe_eq_coe.mp h1,
     fun s => by
      have hmem : Complex.I • (↑s : A) ∈ skewAdjoint A := by
        rw [skewAdjoint.mem_iff, star_smul, selfAdjoint.mem_iff.mp s.2]
        simp [Complex.conj_I]
      exact ⟨⟨Complex.I • (↑s : A), hmem⟩, by
        rw [← SetLike.coe_eq_coe, skewAdjoint.negISMul_apply_coe, smul_smul]
        simp [Complex.I_mul_I]⟩⟩

/-- **The real dimension of the self-adjoint elements of a finite-dimensional complex star module
`A` equals its complex dimension**: `finrank ℝ (selfAdjoint A) = finrank ℂ A`.

`A` decomposes as the real-internal direct sum `selfAdjoint A ⊕ skewAdjoint A`
(`StarModule.decomposeProdAdjoint`); multiplication by `-i` is a real-linear isomorphism
`skewAdjoint A ≃ₗ[ℝ] selfAdjoint A` (`skewAdjoint.negIEquiv`), so the two summands have equal real
dimension. Since `finrank ℝ A = 2 · finrank ℂ A` (`finrank_real_of_complex`), each summand — in
particular `selfAdjoint A` — has real dimension `finrank ℂ A`. -/
theorem finrank_real_selfAdjoint (A : Type*) [AddCommGroup A] [Module ℂ A]
    [StarAddMonoid A] [StarModule ℂ A] [Module.Finite ℂ A] :
    Module.finrank ℝ (selfAdjoint A) = Module.finrank ℂ A := by
  have : Module.Finite ℝ A := Module.Finite.trans ℂ A
  have : Module.Finite ℝ (↥(selfAdjoint A) × ↥(skewAdjoint A)) :=
    Module.Finite.equiv (StarModule.decomposeProdAdjoint ℝ A)
  have : Module.Finite ℝ ↥(selfAdjoint A) :=
    Module.Finite.of_surjective (LinearMap.fst ℝ (↥(selfAdjoint A)) (↥(skewAdjoint A)))
      Prod.fst_surjective
  have : Module.Finite ℝ ↥(skewAdjoint A) :=
    Module.Finite.of_surjective (LinearMap.snd ℝ (↥(selfAdjoint A)) (↥(skewAdjoint A)))
      Prod.snd_surjective
  -- `selfAdjoint` and `skewAdjoint` have equal real dimension (`skewAdjoint.negIEquiv` is a
  -- real-linear equivalence between them), together exhausting `finrank ℝ A`
  have hss : Module.finrank ℝ (selfAdjoint A) = Module.finrank ℝ (skewAdjoint A) :=
    (skewAdjoint.negIEquiv A).finrank_eq.symm
  have hdecomp : Module.finrank ℝ A =
      Module.finrank ℝ (selfAdjoint A) + Module.finrank ℝ (skewAdjoint A) := by
    rw [(StarModule.decomposeProdAdjoint ℝ A).finrank_eq, Module.finrank_prod]
  have hA : Module.finrank ℝ A = 2 * Module.finrank ℂ A := finrank_real_of_complex A
  rw [← hss] at hdecomp
  omega

/-- **The real dimension of the self-adjoint (Hermitian) operators on a finite-dimensional complex
inner product space `E` is `(finrank ℂ E)²`**:
`finrank ℝ (selfAdjoint (E →L[ℂ] E)) = (finrank ℂ E)²`.

The star on `E →L[ℂ] E` is the adjoint, so `selfAdjoint (E →L[ℂ] E)` is the space of Hermitian
operators. Applying `finrank_real_selfAdjoint` to `A = E →L[ℂ] E` reduces the claim to the complex
dimension `finrank ℂ (E →L[ℂ] E) = (finrank ℂ E)²`, computed via the linear equivalence with
`E →ₗ[ℂ] E` (`LinearMap.toContinuousLinearMap`, all linear maps on a finite-dimensional space being
continuous) and `Module.finrank_linearMap`. For `d = finrank ℂ E` this records the `d²` real degrees
of freedom of a Hermitian operator on a `d`-dimensional space — the ambient dimension in the
Carathéodory bound of Nielsen & Chuang, Exercise 12.11. -/
theorem finrank_real_selfAdjoint_continuousLinearMap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] :
    Module.finrank ℝ (selfAdjoint (E →L[ℂ] E)) = (Module.finrank ℂ E) ^ 2 := by
  rw [finrank_real_selfAdjoint (E →L[ℂ] E),
    ← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := E) (F' := E)).finrank_eq,
    Module.finrank_linearMap ℂ ℂ E E, sq]
