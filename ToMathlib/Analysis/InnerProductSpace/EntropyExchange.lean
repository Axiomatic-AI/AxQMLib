/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropyGram
public import ToMathlib.Analysis.InnerProductSpace.OperatorGram
public import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelity
public import ToMathlib.Analysis.InnerProductSpace.Density
public import ToMathlib.Analysis.InnerProductSpace.Uhlmann
public import ToMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Entropy exchange `S(ρ, E)` and the reference-system output state

For a state `ρ` (a density operator on a `d`-dimensional complex inner product space `H`) and a
finite family of operation elements `E : ι → (H →L[ℂ] H)` of a trace-preserving quantum operation,
Nielsen & Chuang define the **entropy exchange** (Nielsen & Chuang, *Quantum Computation and
Quantum Information*, §12.4.1, eqs. (12.107)–(12.110)) by
`S(ρ, E) := S(R', Q') = S(W)`,
where `Wⱼₖ = tr(Eⱼ ρ Eₖ†)` is the **`w`-matrix** — the density operator of the environment in the
Stinespring dilation, in the operation-element basis (eq. (12.109)) — and `S(W) = -tr(W log W)` is
its von Neumann entropy (eq. (12.110)).

This file supplies the `w`-matrix, the entropy-exchange quantity `S(ρ, E) = S(W)`, and the
identification of `S(W)` with the entropy of the reference-plus-system output state
`ρ_{R'Q'} = Σᵢ |E_i √ρ⟩⟨E_i √ρ|` — realized here in the Hilbert–Schmidt space `H ⊗ H` (of dimension
`d²`) as the frame operator of the vectorized family `√ρ Eᵢ†`. This is the operator content of the
quantum Fano inequality (N&C Theorem 12.9): its proof (`QuantumFanoInequality`) applies the
density-operator Fano bound
`S(ρ_{R'Q'}) ≤ H(⟨√ρ, ρ_{R'Q'} √ρ⟩) + (1 - ⟨√ρ, ρ_{R'Q'} √ρ⟩) · log(d² - 1)` to `ρ_{R'Q'}` with
the (unit) Hilbert–Schmidt vector `√ρ`.

## Main definitions

* `ContinuousLinearMap.wMatrix` — the `w`-matrix `Wⱼₖ = tr(Eⱼ ρ Eₖ†)` (N&C eq. (12.109)–(12.110)).
* `ContinuousLinearMap.entropyExchange` — the entropy exchange `S(ρ, E) = S(W)` (N&C eq. (12.110)).
* `ContinuousLinearMap.entropyExchangeState` — the reference-plus-system output density operator
  `ρ_{R'Q'} = Σᵢ |vec(√ρ Eᵢ†)⟩⟨vec(√ρ Eᵢ†)|` on `H ⊗ H`.

## Main results

* `ContinuousLinearMap.entropyExchange_eq_vonNeumannEntropy_entropyExchangeState` — the entropy
  exchange is the von Neumann entropy of `ρ_{R'Q'}`, `S(ρ, E) = S(ρ_{R'Q'})`, because `W` is the
  Gram matrix of the family `√ρ Eᵢ†` (the Gram / sum-of-rank-ones entropy equality
  `vonNeumannEntropy_sum_rankOne_self_eq_gram`).
* `ContinuousLinearMap.re_inner_entropyExchangeState_sqrt_eq_entanglementFidelity` — the diagonal
  entry `⟨√ρ, ρ_{R'Q'} √ρ⟩ = Σᵢ |tr(ρ Eᵢ)|² = F(ρ, E)` is the entanglement fidelity.
* `ContinuousLinearMap.entropyExchangeState_isDensityOp` — `ρ_{R'Q'}` is a density operator (trace
  `1`, from the completeness relation `Σᵢ Eᵢ† Eᵢ = 1`).
* `ContinuousLinearMap.norm_matricize_symm_cfc_sqrt` — `√ρ` is a unit Hilbert–Schmidt vector.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.4.1 (eqs. (12.107)–(12.110), Theorem 12.9); §9.3 (Eq. (9.135)).
-/

open scoped InnerProductSpace TensorProduct ComplexConjugate
open InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  {ιb ι : Type*} [Fintype ιb]

/-- The **`w`-matrix** `Wⱼₖ = tr(Eⱼ ρ Eₖ†)` of a state `ρ` and a family of operation elements
`E : ι → (H →L[ℂ] H)` (Nielsen & Chuang, *Quantum Computation and Quantum Information*, eqs.
(12.109)–(12.110)). It is the matrix of the environment's density operator `ρ_{E'}` in the
operation-element basis of the Stinespring dilation; its von Neumann entropy is the entropy
exchange. -/
noncomputable def wMatrix (ρ : H →L[ℂ] H) (E : ι → H →L[ℂ] H) : Matrix ι ι ℂ :=
  fun j k => LinearMap.trace ℂ H ((E j * ρ * adjoint (E k) : H →L[ℂ] H) : H →ₗ[ℂ] H)

/-- The **entropy exchange** `S(ρ, E) = S(W) = -tr(W log W)` of a state `ρ` under a quantum
operation with operation elements `E` (Nielsen & Chuang, eq. (12.110)). Defined as the von Neumann
entropy of the operator on `EuclideanSpace ℂ ι` represented by the `w`-matrix `W = wMatrix ρ E`. -/
noncomputable def entropyExchange [Fintype ι] [DecidableEq ι] (ρ : H →L[ℂ] H)
    (E : ι → H →L[ℂ] H) : ℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (wMatrix ρ E)).vonNeumannEntropy

/-- The **reference-plus-system output density operator** `ρ_{R'Q'}` (Nielsen & Chuang, eq.
(12.107)), realized in the Hilbert–Schmidt space `H ⊗ H` as the frame operator
`Σᵢ |vec(√ρ Eᵢ†)⟩⟨vec(√ρ Eᵢ†)|` of the vectorized family `√ρ Eᵢ†`, where `vec` is the inverse
matricization `(matricize b).symm` for an orthonormal basis `b` of `H`. Its von Neumann entropy is
the entropy exchange `S(ρ, E)` and its diagonal entry against `vec √ρ` is the entanglement
fidelity. -/
noncomputable def entropyExchangeState [Fintype ι] (b : OrthonormalBasis ιb ℂ H)
    (ρ : H →L[ℂ] H) (E : ι → H →L[ℂ] H) : (H ⊗[ℂ] H) →L[ℂ] (H ⊗[ℂ] H) :=
  ∑ i, InnerProductSpace.rankOne ℂ
    ((TensorProduct.matricize b).symm (cfc Real.sqrt ρ * adjoint (E i)))
    ((TensorProduct.matricize b).symm (cfc Real.sqrt ρ * adjoint (E i)))

/-- The Hilbert–Schmidt inner product of vectorized operators is the operator trace pairing:
`⟨vec A, vec B⟩ = tr(A† B)`, where `vec = (matricize b).symm`. The matricization bridge
`TensorProduct.matricize_inner_eq_trace_adjoint_comp` restated on inverse matricizations. -/
theorem inner_matricize_symm (b : OrthonormalBasis ιb ℂ H) (A B : H →L[ℂ] H) :
    inner ℂ ((TensorProduct.matricize b).symm A) ((TensorProduct.matricize b).symm B)
      = LinearMap.trace ℂ H ((adjoint A * B : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  rw [TensorProduct.matricize_inner_eq_trace_adjoint_comp b, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, ContinuousLinearMap.toLinearMap_mul, Module.End.mul_eq_comp]

omit [FiniteDimensional ℂ H] in
/-- The adjoint of the vectorization factor `(√ρ Eᵢ†)† = Eᵢ √ρ`, from anti-multiplicativity of the
adjoint and self-adjointness of `√ρ` (`adjoint_cfc_real_sqrt`). -/
theorem adjoint_sqrt_mul_adjoint (ρ : H →L[ℂ] H) (E : ι → H →L[ℂ] H) (i : ι) :
    adjoint (cfc Real.sqrt ρ * adjoint (E i)) = E i * cfc Real.sqrt ρ := by
  simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star]
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_cfc_real_sqrt]

omit [FiniteDimensional ℂ H] in
/-- The composed operator `(√ρ Eⱼ†)† (√ρ Eₖ†) = Eⱼ ρ Eₖ†`, the algebraic core linking the Gram
matrix of the family `√ρ Eᵢ†` to the `w`-matrix. Uses `(√ρ Eⱼ†)† = Eⱼ √ρ`
(`adjoint_sqrt_mul_adjoint`) and `√ρ √ρ = ρ` (`cfc_real_sqrt_mul_self`). -/
theorem adjoint_sqrt_mul_sqrt {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (E : ι → H →L[ℂ] H) (j k : ι) :
    adjoint (cfc Real.sqrt ρ * adjoint (E j)) * (cfc Real.sqrt ρ * adjoint (E k))
      = E j * ρ * adjoint (E k) := by
  rw [adjoint_sqrt_mul_adjoint, mul_assoc (E j), ← mul_assoc (cfc Real.sqrt ρ),
    cfc_real_sqrt_mul_self_of_nonneg hρ, ← mul_assoc]

/-- The `w`-matrix is the Gram matrix of the vectorized family `√ρ Eᵢ†`: `W = krausGram b (√ρ E†)`.
Entry-wise, `Wⱼₖ = tr(Eⱼ ρ Eₖ†) = tr((√ρ Eⱼ†)† (√ρ Eₖ†))` (`adjoint_sqrt_mul_sqrt`). -/
theorem wMatrix_eq_krausGram (b : OrthonormalBasis ιb ℂ H) {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ)
    (E : ι → H →L[ℂ] H) :
    wMatrix ρ E = krausGram b (fun i => cfc Real.sqrt ρ * adjoint (E i)) := by
  ext j k
  rw [wMatrix, krausGram_apply, ← Module.End.mul_eq_comp, ← ContinuousLinearMap.toLinearMap_mul,
    adjoint_sqrt_mul_sqrt hρ]

/-- **The entropy exchange is the von Neumann entropy of the reference-plus-system state**,
`S(ρ, E) = S(ρ_{R'Q'})` (Nielsen & Chuang, eqs. (12.107), (12.110)). The `w`-matrix `W` is the Gram
matrix of the family `√ρ Eᵢ†` (`wMatrix_eq_krausGram`), so `S(W)` — the von Neumann entropy of the
`ι × ι` matrix — equals the entropy of the frame operator `Σᵢ |vec(√ρ Eᵢ†)⟩⟨vec(√ρ Eᵢ†)|` on the
`d²`-dimensional Hilbert–Schmidt space, by the Gram / sum-of-rank-ones entropy equality
`vonNeumannEntropy_sum_rankOne_self_eq_gram`. -/
theorem entropyExchange_eq_vonNeumannEntropy_entropyExchangeState [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ιb ℂ H) {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (E : ι → H →L[ℂ] H) :
    entropyExchange ρ E = (entropyExchangeState b ρ E).vonNeumannEntropy := by
  unfold entropyExchange entropyExchangeState
  rw [wMatrix_eq_krausGram b hρ,
    vonNeumannEntropy_sum_rankOne_self_eq_gram
      (fun i => (TensorProduct.matricize b).symm (cfc Real.sqrt ρ * adjoint (E i)))]
  rfl

/-- **The diagonal entry of `ρ_{R'Q'}` against `vec √ρ` is the entanglement fidelity**,
`⟨√ρ, ρ_{R'Q'} √ρ⟩ = Σᵢ |tr(ρ Eᵢ)|² = F(ρ, E)` (Nielsen & Chuang, eqs. (9.135), (12.113)). Each
overlap `⟨vec(√ρ Eᵢ†), vec √ρ⟩ = tr(Eᵢ ρ) = tr(ρ Eᵢ)` by the Hilbert–Schmidt bridge, so the sum of
squared overlaps is the entanglement fidelity. -/
theorem re_inner_entropyExchangeState_sqrt_eq_entanglementFidelity [Fintype ι]
    (b : OrthonormalBasis ιb ℂ H) {ρ : H →L[ℂ] H} (hρ : 0 ≤ ρ) (E : ι → H →L[ℂ] H) :
    RCLike.re (inner ℂ ((TensorProduct.matricize b).symm (cfc Real.sqrt ρ))
        (entropyExchangeState b ρ E ((TensorProduct.matricize b).symm (cfc Real.sqrt ρ))))
      = entanglementFidelity ρ E := by
  set Ω := (TensorProduct.matricize b).symm (cfc Real.sqrt ρ) with hΩ
  have key : inner ℂ Ω (entropyExchangeState b ρ E Ω) = (entanglementFidelity ρ E : ℂ) := by
    simp only [entropyExchangeState, _root_.sum_apply, inner_sum]
    rw [entanglementFidelity, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set φ := (TensorProduct.matricize b).symm (cfc Real.sqrt ρ * adjoint (E i)) with hφ
    have hv : inner ℂ φ Ω = LinearMap.trace ℂ H ((ρ * E i : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rw [hφ, hΩ, inner_matricize_symm, adjoint_sqrt_mul_adjoint, mul_assoc,
        cfc_real_sqrt_mul_self_of_nonneg hρ, ContinuousLinearMap.toLinearMap_mul,
        ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm]
    rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm Ω φ, hv,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [key]
  simp

/-- The Hilbert–Schmidt vector `√ρ` (i.e. `vec √ρ`) is a unit vector: `‖vec √ρ‖ = 1`, since
`‖vec √ρ‖² = tr(√ρ √ρ) = tr ρ = 1` for a density operator `ρ`. -/
theorem norm_matricize_symm_cfc_sqrt (b : OrthonormalBasis ιb ℂ H) {ρ : H →L[ℂ] H}
    (hρ : ρ.IsDensityOp) : ‖(TensorProduct.matricize b).symm (cfc Real.sqrt ρ)‖ = 1 := by
  set Ω := (TensorProduct.matricize b).symm (cfc Real.sqrt ρ) with hΩ
  have h : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [hΩ, inner_matricize_symm, adjoint_cfc_real_sqrt, cfc_real_sqrt_mul_self_of_nonneg hρ.nonneg]
    exact hρ.trace_eq_one
  have h2 : ‖Ω‖ ^ 2 = 1 := by rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h, RCLike.one_re]
  rw [← Real.sqrt_one, ← h2, Real.sqrt_sq (norm_nonneg _)]

/-- **The reference-plus-system state `ρ_{R'Q'}` is a density operator** (Nielsen & Chuang, eq.
(12.107)). It is a sum of rank-one self-projections, hence positive; its trace is
`Σᵢ tr(Eᵢ ρ Eᵢ†) = tr((Σᵢ Eᵢ† Eᵢ) ρ) = tr ρ = 1` by the completeness relation `Σᵢ Eᵢ† Eᵢ = 1` of a
trace-preserving operation. -/
theorem entropyExchangeState_isDensityOp [Fintype ι] (b : OrthonormalBasis ιb ℂ H)
    {ρ : H →L[ℂ] H} (hρ : ρ.IsDensityOp) {E : ι → H →L[ℂ] H}
    (htp : ∑ i, adjoint (E i) * E i = 1) : (entropyExchangeState b ρ E).IsDensityOp := by
  refine ⟨?_, ?_⟩
  · rw [entropyExchangeState]
    exact ContinuousLinearMap.isPositive_sum _ fun i _ =>
      InnerProductSpace.isPositive_rankOne_self _
  · rw [entropyExchangeState, ContinuousLinearMap.toLinearMap_sum, map_sum]
    have hterm : ∀ i, LinearMap.trace ℂ (H ⊗[ℂ] H)
        ((InnerProductSpace.rankOne ℂ
            ((TensorProduct.matricize b).symm (cfc Real.sqrt ρ * adjoint (E i)))
            ((TensorProduct.matricize b).symm (cfc Real.sqrt ρ * adjoint (E i))) :
              (H ⊗[ℂ] H) →L[ℂ] (H ⊗[ℂ] H)) : (H ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] H))
        = LinearMap.trace ℂ H ((adjoint (E i) * E i * ρ : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      intro i
      rw [InnerProductSpace.trace_rankOne, inner_matricize_symm,
        adjoint_sqrt_mul_sqrt hρ.nonneg E i i, ContinuousLinearMap.toLinearMap_mul,
        LinearMap.trace_mul_comm, ← ContinuousLinearMap.toLinearMap_mul, ← mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← map_sum]
    have hsum : ∑ i, ((adjoint (E i) * E i * ρ : H →L[ℂ] H) : H →ₗ[ℂ] H)
        = ((ρ : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rw [← ContinuousLinearMap.toLinearMap_sum, ← Finset.sum_mul, htp, one_mul]
    rw [hsum]
    exact hρ.trace_eq_one

end ContinuousLinearMap
