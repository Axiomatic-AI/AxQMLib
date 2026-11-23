/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.SingularValues
public import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropy
public import ToMathlib.Analysis.InnerProductSpace.RankOneSum
public import ToMathlib.Analysis.InnerProductSpace.GramMatrix
public import ToMathlib.Analysis.CStarAlgebra.Matrix
public import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-! # Gram versus sum-of-rank-ones: equal von Neumann entropy

For a finite family of vectors `φ : ι → H` in a finite-dimensional complex inner product space,
the **frame operator** `Σᵢ |φᵢ⟩⟨φᵢ|` (a positive operator on `H`) and the **Gram matrix**
`Gᵢⱼ = ⟨φᵢ, φⱼ⟩` (a positive semidefinite `ι × ι` matrix) share the same nonzero spectrum, hence
the same von Neumann entropy:
`S(Σᵢ |φᵢ⟩⟨φᵢ|) = S(gram φ)`.

The underlying linear-algebra fact is that for any operator `A` between finite-dimensional inner
product spaces, `A Aᴴ` and `Aᴴ A` have the same nonzero singular-value spectrum, so their von
Neumann entropies (Shannon entropies of the eigenvalue spectrum, with `0 log 0 = 0`) agree even
though they act on spaces of different dimension. Writing `A = synthesisMap φ` (the operator
`eᵢ ↦ φᵢ`) gives `A Aᴴ = Σᵢ |φᵢ⟩⟨φᵢ|` and `Aᴴ A = gram φ`.

This is the operator identity behind the **entropy exchange** of Nielsen & Chuang, *Quantum
Computation and Quantum Information*, §12.4.1 (eq. (12.110)): the entropy exchange
`S(ρ, E) = S(W)` of the `w`-matrix `Wᵢⱼ = tr(Eᵢ ρ Eⱼ†)` equals the von Neumann entropy of the
state `ρ_{R'Q'} = Σᵢ |E_i √ρ⟩⟨E_i √ρ|`, because `W` is the Gram matrix of the family `E_i √ρ`.

## Main results

* `ContinuousLinearMap.vonNeumannEntropy_comp_adjoint_comm`:
  `S(A ∘ Aᴴ) = S(Aᴴ ∘ A)` for `A : E →L[ℂ] F` (in fact over any `RCLike` field).
* `ContinuousLinearMap.vonNeumannEntropy_sum_rankOne_self_eq_gram`:
  `S(Σᵢ |φᵢ⟩⟨φᵢ|) = S(gram φ)`, the Gram / sum-of-rank-ones entropy equality.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.4.1 (eq. (12.110)).
-/

open scoped InnerProductSpace

@[expose] public section

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The von Neumann entropy of the Gram operator `Tᴴ ∘ T` of a linear map `T : E →ₗ F` is the
Shannon entropy of the squared singular values of `T`. Since `(sᵢ)² = λᵢ(Tᴴ T)` are exactly the
eigenvalues of the (positive, self-adjoint) Gram operator, this is just the definition of von
Neumann entropy unfolded through `LinearMap.sq_singularValues_fin`. -/
theorem vonNeumannEntropy_adjoint_comp_self_eq_entropy_sq_singularValues (T : E →ₗ[𝕜] F) :
    (LinearMap.adjoint T ∘ₗ T).vonNeumannEntropy
      = Real.entropy fun i : Fin (Module.finrank 𝕜 E) => T.singularValues i ^ 2 := by
  rw [LinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq
        (isSymmetric_adjoint_comp_self T) rfl]
  congr 1
  funext i
  exact (T.sq_singularValues_fin rfl i).symm

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [CompleteSpace F]

/-- Two finite `Fin`-indexed Shannon-entropy sums of the same eventually-`negMulLog`-vanishing
sequence agree: if `g k` has `negMulLog (g k) = 0` for all `k ≥ r` and both `m₁, m₂ ≥ r`, then
`Real.entropy (g|_{Fin m₁}) = Real.entropy (g|_{Fin m₂})`, both collapsing to the length-`r` sum.
This is the "entropy ignores zero eigenvalues" step: the two operators `A Aᴴ` and `Aᴴ A` live on
spaces of different dimension but share the same nonzero (squared singular value) spectrum. -/
private theorem entropy_fin_eq_of_negMulLog_vanish {g : ℕ → ℝ} {r m₁ m₂ : ℕ}
    (hr : ∀ k, r ≤ k → (g k).negMulLog = 0) (h₁ : r ≤ m₁) (h₂ : r ≤ m₂) :
    Real.entropy (fun i : Fin m₁ => g i) = Real.entropy (fun i : Fin m₂ => g i) := by
  have key : ∀ m, r ≤ m → ∑ k ∈ Finset.range m, (g k).negMulLog
      = ∑ k ∈ Finset.range r, (g k).negMulLog := by
    intro m hm
    refine (Finset.sum_subset (Finset.range_mono hm) fun x _ hx => ?_).symm
    exact hr x (by simpa [Finset.mem_range, not_lt] using hx)
  simp only [Real.entropy_eq]
  rw [Fin.sum_univ_eq_sum_range (fun k => (g k).negMulLog) m₁,
      Fin.sum_univ_eq_sum_range (fun k => (g k).negMulLog) m₂, key m₁ h₁, key m₂ h₂]

/-- **`A Aᴴ` and `Aᴴ A` have equal von Neumann entropy.** For a continuous linear map
`A : E →L[𝕜] F` between finite-dimensional inner product spaces, `S(A ∘ Aᴴ) = S(Aᴴ ∘ A)`.

Both sides are the Shannon entropy of the squared singular-value spectrum of `A` (the entropies of
`A Aᴴ` on `F` and of `Aᴴ A` on `E` differ only by extra zero eigenvalues, which contribute
`0 log 0 = 0`). This is the operator form of the fact that a Gram matrix and a sum of rank-one
projectors share their nonzero spectrum. -/
theorem vonNeumannEntropy_comp_adjoint_comm (A : E →L[𝕜] F) :
    (A ∘L ContinuousLinearMap.adjoint A).vonNeumannEntropy
      = (ContinuousLinearMap.adjoint A ∘L A).vonNeumannEntropy := by
  rw [← vonNeumannEntropy_toLinearMap, ← vonNeumannEntropy_toLinearMap,
      ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
      ← ContinuousLinearMap.adjoint_toLinearMap]
  -- `↑(A ∘ Aᴴ) = ↑A ∘ₗ (adjoint ↑A)` and `↑(Aᴴ ∘ A) = (adjoint ↑A) ∘ₗ ↑A`.
  set T : E →ₗ[𝕜] F := (A : E →ₗ[𝕜] F) with hT
  -- Right-hand side: directly the Gram operator `Tᴴ ∘ T`.
  have hRHS := LinearMap.vonNeumannEntropy_adjoint_comp_self_eq_entropy_sq_singularValues T
  -- Left side: the Gram operator `(Tᴴ)ᴴ ∘ Tᴴ` of `Tᴴ`; its singular values match those of `T`.
  have hLHS := LinearMap.vonNeumannEntropy_adjoint_comp_self_eq_entropy_sq_singularValues
    (LinearMap.adjoint T)
  rw [LinearMap.adjoint_adjoint, LinearMap.singularValues_adjoint] at hLHS
  rw [hLHS, hRHS]
  refine entropy_fin_eq_of_negMulLog_vanish
    (g := fun k => T.singularValues k ^ 2)
    (r := Module.finrank 𝕜 (LinearMap.range T)) (fun k hk => ?_)
    (Submodule.finrank_le _) (LinearMap.finrank_range_le T)
  have hzero : T.singularValues k = 0 :=
    (LinearMap.singularValues_eq_zero_iff_le_finrank_range T).mpr hk
  simp [hzero]

/-- **Gram versus sum-of-rank-ones entropy equality.** For a finite family `φ : ι → H` in a
finite-dimensional inner product space over an `RCLike` field `𝕜`, the frame operator
`Σᵢ |φᵢ⟩⟨φᵢ|` and the Gram matrix `gram φ` (with entries `⟨φᵢ, φⱼ⟩`) have equal von Neumann
entropy:
`S(Σᵢ |φᵢ⟩⟨φᵢ|) = S(gram φ)`.

The frame operator is `A Aᴴ` for the synthesis operator `A = synthesisMap φ`, and its companion
`Aᴴ A` is the operator on `EuclideanSpace 𝕜 ι` with matrix `gram φ`; the equality is then
`vonNeumannEntropy_comp_adjoint_comm`. -/
theorem vonNeumannEntropy_sum_rankOne_self_eq_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
    [CompleteSpace H] (φ : ι → H) :
    (∑ i, InnerProductSpace.rankOne 𝕜 (φ i) (φ i)).vonNeumannEntropy
      = (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (Matrix.gram 𝕜 φ)).vonNeumannEntropy := by
  rw [InnerProductSpace.sum_rankOne_self_eq_synthesisMap_comp_adjoint,
      vonNeumannEntropy_comp_adjoint_comm]
  congr 1
  -- `(synthesisMap φ)ᴴ ∘ synthesisMap φ = (gram φ).toEuclideanCLM` on `EuclideanSpace 𝕜 ι`.
  refine ContinuousLinearMap.ext fun x => ext_inner_left 𝕜 fun w => ?_
  -- The Gram side is the Gram bilinear form of the two synthesis combinations.
  have hR : inner 𝕜 w (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (Matrix.gram 𝕜 φ) x)
      = inner 𝕜 (∑ i, (w.ofLp i) • φ i) (∑ i, (x.ofLp i) • φ i) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM,
        dotProduct_comm, Matrix.star_dotProduct_gram_mulVec]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      InnerProductSpace.synthesisMap_apply, InnerProductSpace.synthesisMap_apply, hR]

end ContinuousLinearMap
