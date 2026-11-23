/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.Matricization
public import ToMathlib.Analysis.InnerProductSpace.Purification
public import ToMathlib.Analysis.InnerProductSpace.RankOneSum
public import ToMathlib.Analysis.InnerProductSpace.TensorProduct
public import ToMathlib.Analysis.InnerProductSpace.Transpose
public import ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl

/-!
# Unitary freedom in purifications

Two purifications of the same density operator `ρ` to the *same* bipartite space `E ⊗ F` are
related by a unitary acting only on the ancilla factor `F`:

* `TensorProduct.exists_mem_unitary_mapL_id_eq` : if `Ψ, Φ : E ⊗[ℂ] F` have the same reduced
  operator on `E` (equal right-partial-traces of `|Ψ⟩⟨Ψ|` and `|Φ⟩⟨Φ|`), then there is a unitary
  `U` on `F` with `(I_E ⊗ U) Ψ = Φ`.

This is the operator/vector content of Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Exercise 2.81 ("freedom in purifications"). The proof reduces the reduced-operator
condition to `M_Ψ M_Ψ† = M_Φ M_Φ†` for the matricizations `M_• = matricize b •` and applies the
"rectangular operator crux" `ContinuousLinearMap.exists_unitary_comp_of_comp_adjoint_eq` (the heart
of the unitary-freedom-in-the-ensemble theorem, N&C Thm 2.6) to obtain a unitary `W` on `F` with
`M_Φ = M_Ψ ∘ W`. The bridge back to the tensor factor is the observation that `I_E ⊗ U` acts on the
matricization by right-composition with the **transpose** `b.transposeOp U` of `U` in the basis `b`
(`TensorProduct.matricize_mapL_id`); taking `U := b.transposeOp W` and using involutivity of the
transpose closes the goal via injectivity of `matricize`.

## Relation to existing API

`OrthonormalBasis.transposeOp` is the transpose of an operator relative to an *arbitrary*
orthonormal basis; it **generalizes** the `EuclideanSpace`-specific `EuclideanSpace.transposeOp`
(`ToMathlib/Analysis/InnerProductSpace/Transpose.lean`). The two agree at the standard basis:
`OrthonormalBasis.transposeOp_basisFun` proves
`(EuclideanSpace.basisFun ι ℂ).transposeOp U = EuclideanSpace.transposeOp U`. The general form is
needed here because the quantum ancilla is a general finite-dimensional Hilbert space (a `QSystem`
space), not literally an `EuclideanSpace`. Likewise `TensorProduct.matricize_mapL_id` is the
general-orthonormal-basis analogue, at `A = 1`, of the `EuclideanSpace`-specific
`TensorProduct.matricize_mapL` (`ToMathlib/Analysis/InnerProductSpace/LiebConcavityTrace.lean`); at
`EuclideanSpace.basisFun` the two coincide via `transposeOp_basisFun`.

## Main definitions

* `OrthonormalBasis.transposeOp` : the transpose of `U : F →L[ℂ] F` relative to an orthonormal
  basis `b` of `F`, characterized by `⟪b p, b.transposeOp U (b q)⟫ = ⟪b q, U (b p)⟫`.

## Main results

* `TensorProduct.matricize_mapL_id` : the bridge
  `matricize b ((I_E ⊗ U) Ψ) = (matricize b Ψ) ∘ b.transposeOp U`.
* `OrthonormalBasis.transposeOp_mem_unitary` : the transpose of a unitary is unitary.
* `TensorProduct.exists_mem_unitary_mapL_id_eq` : unitary freedom in purifications.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

@[expose] public section

namespace OrthonormalBasis

section Transpose

variable {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]

/-- **Coordinate expansion of an operator's action in an orthonormal basis.** For an orthonormal
basis `b`, an operator `T : F →L[ℂ] F`, and a vector `z`, the `k`-th coordinate of `T z` is the
matrix-element combination `⟪b k, T z⟫ = ∑ l, ⟪b k, T (b l)⟫ * ⟪b l, z⟫`: expand
`z = ∑ l ⟪b l, z⟫ • b l` (`OrthonormalBasis.sum_repr'`) and push `T` and the inner product through
the sum. The identity-operator analogue of `transposeOp_inner_apply` (which carries the extra basis
transpose). -/
theorem inner_op_eq_sum (b : OrthonormalBasis ι ℂ F) (T : F →L[ℂ] F) (k : ι) (z : F) :
    inner ℂ (b k) (T z) = ∑ l, inner ℂ (b k) (T (b l)) * inner ℂ (b l) z := by
  conv_lhs => rw [← b.sum_repr' z, map_sum]
  rw [inner_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_smul, inner_smul_right, mul_comm]

/-- The **transpose** of an operator `U : F →L[ℂ] F` relative to an orthonormal basis `b` of `F`.
Built as the double sum `∑ i k, ⟪b k, U (b i)⟫ • |b i⟩⟨b k|`, it is characterized on the basis by
`⟪b p, b.transposeOp U (b q)⟫ = ⟪b q, U (b p)⟫` (`transposeOp_inner`). This generalizes
`EuclideanSpace.transposeOp` from the standard basis to an arbitrary orthonormal basis
(`transposeOp_basisFun`). -/
noncomputable def transposeOp (b : OrthonormalBasis ι ℂ F) (U : F →L[ℂ] F) : F →L[ℂ] F :=
  ∑ i, ∑ k, inner ℂ (b k) (U (b i)) • (InnerProductSpace.rankOne ℂ (b i) (b k) : F →L[ℂ] F)

/-- Value form of the transpose:
`b.transposeOp U z = ∑ i k, (⟪b k, U (b i)⟫ * ⟪b k, z⟫) • b i`. -/
theorem transposeOp_apply (b : OrthonormalBasis ι ℂ F) (U : F →L[ℂ] F) (z : F) :
    b.transposeOp U z = ∑ i, ∑ k, (inner ℂ (b k) (U (b i)) * inner ℂ (b k) z) • b i := by
  simp only [transposeOp, _root_.sum_apply, _root_.smul_apply,
    InnerProductSpace.rankOne_apply, smul_smul]

/-- Matrix entry of `b.transposeOp U` against a general vector `z`:
`⟪b p, b.transposeOp U z⟫ = ∑ k, ⟪b k, U (b p)⟫ * ⟪b k, z⟫`. -/
theorem transposeOp_inner_apply (b : OrthonormalBasis ι ℂ F) (U : F →L[ℂ] F) (p : ι) (z : F) :
    inner ℂ (b p) (b.transposeOp U z) = ∑ k, inner ℂ (b k) (U (b p)) * inner ℂ (b k) z := by
  classical
  rw [transposeOp_apply]
  simp only [inner_sum, inner_smul_right, b.inner_eq_ite, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Basis matrix entry of the transpose: `⟪b p, b.transposeOp U (b q)⟫ = ⟪b q, U (b p)⟫`. -/
theorem transposeOp_inner (b : OrthonormalBasis ι ℂ F) (U : F →L[ℂ] F) (p q : ι) :
    inner ℂ (b p) (b.transposeOp U (b q)) = inner ℂ (b q) (U (b p)) := by
  classical
  rw [transposeOp_inner_apply]
  simp only [b.inner_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- The transpose is an involution: `b.transposeOp (b.transposeOp U) = U`. -/
theorem transposeOp_transposeOp (b : OrthonormalBasis ι ℂ F) (U : F →L[ℂ] F) :
    b.transposeOp (b.transposeOp U) = U := by
  refine b.ext_inner_basis fun p q => ?_
  rw [transposeOp_inner, transposeOp_inner]

/-- The transpose of the identity is the identity. -/
@[simp]
theorem transposeOp_one (b : OrthonormalBasis ι ℂ F) : b.transposeOp 1 = 1 := by
  classical
  refine b.ext_inner_basis fun p q => ?_
  rw [transposeOp_inner]
  simp only [one_apply_eq_self, b.inner_eq_ite, eq_comm]

section CompleteSpace
variable [CompleteSpace F]

/-- The transpose commutes with the adjoint: `star (b.transposeOp U) = b.transposeOp (star U)`. -/
theorem star_transposeOp (b : OrthonormalBasis ι ℂ F) (U : F →L[ℂ] F) :
    star (b.transposeOp U) = b.transposeOp (star U) := by
  refine b.ext_inner_basis fun p q => ?_
  rw [transposeOp_inner, ContinuousLinearMap.star_eq_adjoint, adjoint_inner_right,
    ContinuousLinearMap.star_eq_adjoint, adjoint_inner_right, ← inner_conj_symm, transposeOp_inner,
    inner_conj_symm]

/-- The transpose reverses composition:
`b.transposeOp (U * V) = b.transposeOp V * b.transposeOp U`. -/
theorem transposeOp_mul (b : OrthonormalBasis ι ℂ F) (U V : F →L[ℂ] F) :
    b.transposeOp (U * V) = b.transposeOp V * b.transposeOp U := by
  refine b.ext_inner_basis fun p q => ?_
  rw [transposeOp_inner]
  simp only [mul_apply_eq_comp]
  rw [transposeOp_inner_apply]
  simp_rw [transposeOp_inner]
  have key := b.sum_inner_mul_inner (adjoint U (b q)) (V (b p))
  simp_rw [adjoint_inner_left] at key
  rw [← key]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The transpose of a unitary is unitary. -/
theorem transposeOp_mem_unitary (b : OrthonormalBasis ι ℂ F) {U : F →L[ℂ] F}
    (hU : U ∈ unitary (F →L[ℂ] F)) : b.transposeOp U ∈ unitary (F →L[ℂ] F) := by
  rw [Unitary.mem_iff] at hU ⊢
  obtain ⟨h1, h2⟩ := hU
  refine ⟨?_, ?_⟩
  · rw [star_transposeOp, ← transposeOp_mul, h2, transposeOp_one]
  · rw [star_transposeOp, ← transposeOp_mul, h1, transposeOp_one]

end CompleteSpace

end Transpose

/-- The basis-relative transpose at the standard basis of `EuclideanSpace` coincides with
`EuclideanSpace.transposeOp`. Both operators have basis matrix entry `⟪b q, U (b p)⟫`; for
`EuclideanSpace.transposeOp` this unfolds through the `conjVec` anti-isometry
(`EuclideanSpace.transposeOp_apply`). -/
theorem transposeOp_basisFun {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    (EuclideanSpace.basisFun ι ℂ).transposeOp U = EuclideanSpace.transposeOp U := by
  classical
  set b := EuclideanSpace.basisFun ι ℂ with hb
  have hc : ∀ r, EuclideanSpace.conjVec (b r) = b r := by
    intro r; ext j; simp [EuclideanSpace.conjVec_apply, hb, EuclideanSpace.basisFun_apply]
  refine b.ext_inner_basis fun p q => ?_
  rw [transposeOp_inner, EuclideanSpace.transposeOp_apply, hc]
  apply star_injective
  rw [← EuclideanSpace.conjVec_inner, hc, ContinuousLinearMap.star_eq_adjoint, adjoint_inner_right]
  exact inner_conj_symm _ _

end OrthonormalBasis

namespace TensorProduct

variable {E F ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
  [Fintype ι]

omit [CompleteSpace E] in
omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- The right-restriction of `(I_E ⊗ U) Ψ` expands over the basis:
`restrictRight b k ((I_E ⊗ U) Ψ) = ∑ m, ⟪b k, U (b m)⟫ • restrictRight b m Ψ`. Internal stepping
stone for `matricize_mapL_id`. -/
private theorem restrictRight_mapL_id (b : OrthonormalBasis ι ℂ F) (U : F →L[ℂ] F)
    (Ψ : E ⊗[ℂ] F) (k : ι) :
    LinearMap.restrictRight b k (mapL (1 : E →L[ℂ] E) U Ψ)
      = ∑ m, inner ℂ (b k) (U (b m)) • LinearMap.restrictRight b m Ψ := by
  have key : ∀ w : F, inner ℂ (b k) (U w)
      = ∑ m, inner ℂ (b k) (U (b m)) * inner ℂ (b m) w := by
    intro w
    have h := b.sum_inner_mul_inner (adjoint U (b k)) w
    simp_rw [adjoint_inner_left] at h
    exact h.symm
  induction Ψ using TensorProduct.inductionOn with
  | tmul x y =>
    rw [mapL_tmul, one_apply_eq_self, LinearMap.restrictRight_tmul]
    simp_rw [LinearMap.restrictRight_tmul, smul_smul, ← Finset.sum_smul, ← key]
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂]
    simp_rw [map_add, smul_add]
    rw [Finset.sum_add_distrib]

omit [CompleteSpace E] in
omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- **Matricization bridge.** Applying `I_E ⊗ U` to a bipartite vector right-composes its
matricization with the transpose of `U`:
`matricize b ((I_E ⊗ U) Ψ) = (matricize b Ψ) ∘L b.transposeOp U`. This is the
general-orthonormal-basis analogue, at `A = 1`, of the `EuclideanSpace`-specific
`TensorProduct.matricize_mapL`. -/
theorem matricize_mapL_id (b : OrthonormalBasis ι ℂ F) (U : F →L[ℂ] F) (Ψ : E ⊗[ℂ] F) :
    matricize b (mapL (1 : E →L[ℂ] E) U Ψ) = (matricize b Ψ).comp (b.transposeOp U) := by
  ext φ
  rw [matricize_apply, ContinuousLinearMap.comp_apply, matricize_apply]
  simp only [restrictRight_mapL_id, Finset.smul_sum, smul_smul,
    OrthonormalBasis.transposeOp_inner_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

/-- **Unitary freedom in purifications** (Nielsen & Chuang, Exercise 2.81, for vectors).
If two bipartite vectors `Ψ, Φ : E ⊗[ℂ] F` have the same reduced operator on `E` (equal
right-partial-traces of the rank-one projectors), then there is a unitary `U` on the ancilla `F`
with `(I_E ⊗ U) Ψ = Φ`. -/
theorem exists_mem_unitary_mapL_id_eq (b : OrthonormalBasis ι ℂ F) (Ψ Φ : E ⊗[ℂ] F)
    (h : LinearMap.partialTraceRight b (↑((InnerProductSpace.rankOne ℂ Ψ) Ψ) :
          E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)
      = LinearMap.partialTraceRight b (↑((InnerProductSpace.rankOne ℂ Φ) Φ) :
          E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F)) :
    ∃ U ∈ unitary (F →L[ℂ] F), mapL (1 : E →L[ℂ] E) U Ψ = Φ := by
  rw [partialTraceRight_rankOne_self, partialTraceRight_rankOne_self] at h
  have hgram : (matricize b Φ).comp (adjoint (matricize b Φ))
      = (matricize b Ψ).comp (adjoint (matricize b Ψ)) :=
    (ContinuousLinearMap.coe_injective h).symm
  obtain ⟨W, hW, hWeq⟩ := ContinuousLinearMap.exists_unitary_comp_of_comp_adjoint_eq hgram
  refine ⟨b.transposeOp W, b.transposeOp_mem_unitary hW, ?_⟩
  apply (matricize b).injective
  rw [matricize_mapL_id, OrthonormalBasis.transposeOp_transposeOp]
  exact hWeq.symm

end TensorProduct
