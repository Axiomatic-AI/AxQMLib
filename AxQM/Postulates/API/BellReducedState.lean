/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellBasis
import AxQM.Postulates.API.MaximallyMixed
import AxQM.Postulates.PartialTraceTensor

/-!
# AxQM.Postulates.API — reduced density operators of the Bell states

The reduced density operators (marginals) of the four **Bell states** `|β_xy⟩` are the
**maximally mixed** qubit state `I/2` (Nielsen & Chuang, Exercise 2.75). Each Bell state is
maximally entangled, so tracing out either qubit destroys all information about the other and
leaves the completely mixed state — the operator-level content of Exercise 2.75.

* `bellState_reducedLeft_op` / `bellState_reducedRight_op` — the reduced operators
  `Tr_B|β_xy⟩⟨β_xy| = Tr_A|β_xy⟩⟨β_xy| = (1/2) I` on each qubit, for every `x, y`.
* `maximallyMixedState_qubit_op` — `(maximallyMixedState qubit).op = (1/2) I` (`dim qubit = 2`);
  the bridge that turns the `_op` computations into the statement of Exercise 2.75.

## Design notes

The computation is a Schmidt-decomposition calculation.  Each Bell vector is written in Schmidt
form `|β_xy⟩ = ∑ᵢ σᵢ |eᵢ⟩|fᵢ⟩` with the sign `(-1)ˣ` **folded into a real coefficient**
`σ = ![(√2)⁻¹, (-1)ˣ (√2)⁻¹]`, so **both** Schmidt factor families `eᵢ = |i⟩` and
`fᵢ = |y+i⟩` are the phase-free computational basis (`bellSchmidt_decomp`).  This makes both
orthonormality conditions trivial and makes every squared coefficient `σᵢ² = 1/2`
(`bellSchmidt_coeff_sq`), independent of the sign.

The Schmidt partial-trace lemmas
(`LinearMap.partialTrace{Right,Left}_rankOne_eq_sum_rankOne_of_schmidt`) then reduce the marginal
to `∑ᵢ (1/2) |gᵢ⟩⟨gᵢ|` over the surviving orthonormal computational basis, which is `(1/2) I` by
the resolution of identity `sum_rankOne_qubitBasis_eq_one` (`∑ᵢ |i⟩⟨i| = I`, reindexed by
`sum_rankOne_qubitBasis_shift` for the right marginal, whose surviving basis is `|y+i⟩`).

The statement of Exercise 2.75,
`(bellState x y).toState.reduced{Left,Right} = maximallyMixedState qubit`, is in
`AxQM/NC/Ch2/Exercise2_75.lean`, proved by `State.ext` from these `_op` lemmas.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The maximally mixed qubit state is `I/2`: `(maximallyMixedState qubit).op = (1/2) I`
(since `dim qubit = 2`).  The bridge from `bellState_reduced*_op` to Exercise 2.75. -/
theorem maximallyMixedState_qubit_op :
    (maximallyMixedState qubit).op = ((2 : ℂ)⁻¹ • 1 : qubit.space →L[ℂ] qubit.space) := by
  rw [maximallyMixedState_op, finrank_qubit_space]
  norm_num

/-- **Resolution of identity for the qubit computational basis:** `∑ᵢ |i⟩⟨i| = I`.  The standard
basis `|0⟩, |1⟩` is orthonormal (`EuclideanSpace.basisFun`), so its rank-one projectors sum to the
identity (`OrthonormalBasis.sum_rankOne_eq_id`). -/
theorem sum_rankOne_qubitBasis_eq_one :
    (∑ i : Fin 2, (InnerProductSpace.rankOne ℂ (qubitBasis i).vec (qubitBasis i).vec :
      qubit.space →L[ℂ] qubit.space)) = 1 := by
  have h := OrthonormalBasis.sum_rankOne_eq_id (EuclideanSpace.basisFun (Fin 2) ℂ)
  simp only [EuclideanSpace.basisFun_apply] at h
  rw [ContinuousLinearMap.one_def]; exact h

/-- **Shifted resolution of identity:** `∑ᵢ |y+i⟩⟨y+i| = I` for any `y`.  Reindexing `sum_rankOne`
`_qubitBasis_eq_one` along the bijection `i ↦ y + i` (`Equiv.addLeft y`); needed for the right
marginal, whose surviving Schmidt basis is `|y⟩, |ȳ⟩` (i.e. `|y+i⟩`). -/
theorem sum_rankOne_qubitBasis_shift (y : Fin 2) :
    (∑ i : Fin 2, (InnerProductSpace.rankOne ℂ (qubitBasis (y + i)).vec (qubitBasis (y + i)).vec :
      qubit.space →L[ℂ] qubit.space)) = 1 := by
  rw [← sum_rankOne_qubitBasis_eq_one]
  exact Equiv.sum_comp (Equiv.addLeft y)
    (fun j => InnerProductSpace.rankOne ℂ (qubitBasis j).vec (qubitBasis j).vec)

/-- The **Schmidt decomposition of the Bell vector** with the sign folded into a real coefficient:
`|β_xy⟩ = ∑ᵢ σᵢ |i⟩|y+i⟩` with `σ = ![(√2)⁻¹, (-1)ˣ (√2)⁻¹]`.  Both factor families `|i⟩` and
`|y+i⟩` are the phase-free computational basis; the `(-1)ˣ` lives only in the real coefficient. -/
theorem bellSchmidt_decomp (x y : Fin 2) :
    (bellBasisVec x y : qubit.space ⊗[ℂ] qubit.space)
      = ∑ i, ((![(Real.sqrt 2)⁻¹, (-1 : ℝ) ^ (x : ℕ) * (Real.sqrt 2)⁻¹] : Fin 2 → ℝ) i : ℂ) •
          (fun i => (qubitBasis i).vec) i ⊗ₜ[ℂ] (fun i => (qubitBasis (y + i)).vec) i := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    bellBasisVec, PureState.tmul_vec, add_zero]
  erw [smul_add, smul_smul]
  push_cast; rw [mul_comm]; rfl

/-- Each **squared Schmidt coefficient is `1/2`**: `σᵢ² = 1/2` for `σ = ![(√2)⁻¹, (-1)ˣ (√2)⁻¹]`,
since `((√2)⁻¹)² = 1/2` and the sign `((-1)ˣ)² = 1` drops out. -/
theorem bellSchmidt_coeff_sq (x : Fin 2) : ∀ i : Fin 2,
    (((![(Real.sqrt 2)⁻¹, (-1 : ℝ) ^ (x : ℕ) * (Real.sqrt 2)⁻¹] : Fin 2 → ℝ) i : ℂ)) ^ 2
      = (2 : ℂ)⁻¹ := by
  have hsq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = (2 : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsign : ((-1 : ℝ) ^ (x : ℕ)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    rw [← Complex.ofReal_pow]
  · rw [hsq, Complex.ofReal_inv, Complex.ofReal_ofNat]
  · rw [mul_pow, hsq, hsign, one_mul, Complex.ofReal_inv, Complex.ofReal_ofNat]

/-- The density operator of a Bell state as the rank-one projector on the Bell vector, ascribed to
the underlying tensor product space so the `ToMathlib` partial-trace API applies:
`|β_xy⟩⟨β_xy| = rankOne (bellBasisVec x y) (bellBasisVec x y)`. -/
private theorem bellState_toState_op_toLinearMap (x y : Fin 2) :
    ((bellState x y).toState.op.toLinearMap :
      qubit.space ⊗[ℂ] qubit.space →ₗ[ℂ] qubit.space ⊗[ℂ] qubit.space)
      = ↑(InnerProductSpace.rankOne ℂ (bellBasisVec x y : qubit.space ⊗[ℂ] qubit.space)
          (bellBasisVec x y : qubit.space ⊗[ℂ] qubit.space)) := by
  simp only [PureState.toState_op, bellState_vec]

/-- **Left reduced operator of a Bell state is `I/2`** (Nielsen & Chuang, Exercise 2.75, operator
form): tracing out the second qubit of `|β_xy⟩⟨β_xy|` gives the maximally mixed qubit state,
`Tr_B|β_xy⟩⟨β_xy| = (1/2) I`, for every `x, y`.  The right Schmidt factors `|y+i⟩` are orthonormal,
so the `partialTraceRight` Schmidt lemma gives `∑ᵢ σᵢ² |i⟩⟨i|`, which is `(1/2) I` by the
resolution of identity `∑ᵢ |i⟩⟨i| = I`. -/
theorem bellState_reducedLeft_op (x y : Fin 2) :
    (bellState x y).toState.reducedLeft.op = ((2 : ℂ)⁻¹ • 1 : qubit.space →L[ℂ] qubit.space) := by
  have hforth : Orthonormal ℂ (fun i : Fin 2 => (qubitBasis (y + i)).vec) := by
    rw [orthonormal_iff_ite]; intro i j
    simp only [qubitBasis_inner_qubitBasis, add_right_inj]
  apply ContinuousLinearMap.coe_injective
  rw [State.reducedLeft_op, LinearMap.coe_toContinuousLinearMap,
    bellState_toState_op_toLinearMap]
  refine Eq.trans (LinearMap.partialTraceRight_rankOne_eq_sum_rankOne_of_schmidt
    (stdOrthonormalBasis ℂ qubit.space)
    ![(Real.sqrt 2)⁻¹, (-1 : ℝ) ^ (x : ℕ) * (Real.sqrt 2)⁻¹]
    (fun i => (qubitBasis i).vec) (fun i => (qubitBasis (y + i)).vec) hforth
    (bellSchmidt_decomp x y)) ?_
  rw [ContinuousLinearMap.toLinearMap_smul, ← sum_rankOne_qubitBasis_eq_one,
    ContinuousLinearMap.toLinearMap_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact bellSchmidt_coeff_sq x i

/-- **Right reduced operator of a Bell state is `I/2`** (Nielsen & Chuang, Exercise 2.75, operator
form): tracing out the first qubit of `|β_xy⟩⟨β_xy|` gives the maximally mixed qubit state,
`Tr_A|β_xy⟩⟨β_xy| = (1/2) I`, for every `x, y`.  The left Schmidt factors `|i⟩` are orthonormal,
so the `partialTraceLeft` Schmidt lemma gives `∑ᵢ σᵢ² |y+i⟩⟨y+i| = (1/2) ∑ᵢ |y+i⟩⟨y+i| =
(1/2) I` (resolution of identity over the reindexed basis, `sum_rankOne_qubitBasis_shift`). -/
theorem bellState_reducedRight_op (x y : Fin 2) :
    (bellState x y).toState.reducedRight.op = ((2 : ℂ)⁻¹ • 1 : qubit.space →L[ℂ] qubit.space) := by
  have heorth : ∀ i j : Fin 2,
      ((![(Real.sqrt 2)⁻¹, (-1 : ℝ) ^ (x : ℕ) * (Real.sqrt 2)⁻¹] : Fin 2 → ℝ) i) ≠ 0 →
      ((![(Real.sqrt 2)⁻¹, (-1 : ℝ) ^ (x : ℕ) * (Real.sqrt 2)⁻¹] : Fin 2 → ℝ) j) ≠ 0 →
      inner ℂ ((fun i => (qubitBasis i).vec) i) ((fun i => (qubitBasis i).vec) j)
        = if i = j then (1 : ℂ) else 0 :=
    fun i j _ _ => qubitBasis_inner_qubitBasis i j
  apply ContinuousLinearMap.coe_injective
  rw [State.reducedRight_op, LinearMap.coe_toContinuousLinearMap,
    bellState_toState_op_toLinearMap]
  refine Eq.trans (LinearMap.partialTraceLeft_rankOne_eq_sum_rankOne_of_schmidt
    (stdOrthonormalBasis ℂ qubit.space)
    ![(Real.sqrt 2)⁻¹, (-1 : ℝ) ^ (x : ℕ) * (Real.sqrt 2)⁻¹]
    (fun i => (qubitBasis i).vec) (fun i => (qubitBasis (y + i)).vec) heorth
    (bellSchmidt_decomp x y)) ?_
  rw [ContinuousLinearMap.toLinearMap_smul, ← sum_rankOne_qubitBasis_shift y,
    ContinuousLinearMap.toLinearMap_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact bellSchmidt_coeff_sq x i

end AxQM
