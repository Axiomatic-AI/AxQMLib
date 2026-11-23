/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SchmidtDecomposition
import AxQM.Postulates.API.PureState
import AxQM.Postulates.API.Qubit
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# AxQM — the Schmidt decomposition of the entangled state `(|00⟩ + |01⟩ + |10⟩)/√3`

The third state of Nielsen & Chuang, Exercise 2.79. Unlike the two clean states (the Bell state
and the product state `|+⟩⊗|+⟩`, handled in `SchmidtDecompositionExamples.lean`), this one is
**genuinely entangled** with *irrational* Schmidt coefficients, so it is developed here on its own.

## The decomposition

Writing `|ψ⟩ = ∑ⱼₖ aⱼₖ |j⟩|k⟩` the coefficient array is `a = (1/√3)·!![1, 1; 1, 0]`, so the
reduced density operator is `ρᴬ = a aᵀ = (1/3)·!![2, 1; 1, 1]`, with eigenvalues `(3 ± √5)/6`.
The Schmidt coefficients are therefore `√((3 ± √5)/6)`, and the Schmidt bases are the orthonormal
eigenvectors of `ρᴬ`. Diagonalising the *symmetric* matrix `!![1, 1; 1, 0]` (eigenvalues the
golden ratio `φ` and its conjugate `ψ`, eigenvectors `(φ, 1)` and `(ψ, 1)`) gives the clean
spectral identity

  `(φ|0⟩+|1⟩) ⊗ (φ|0⟩+|1⟩) − (ψ|0⟩+|1⟩) ⊗ (ψ|0⟩+|1⟩) = √5 · (|00⟩ + |01⟩ + |10⟩)`,

(using `φ² − ψ² = φ − ψ = √5`), from which the Schmidt decomposition follows by normalising the
two eigenvectors. The two Schmidt coefficients are `√((3+√5)/6) = φ/√3` and
`√((3−√5)/6) = −ψ/√3` (`ψ < 0`); the right Schmidt basis carries the sign `(φ,1) ↦ (φ,1)`,
`(ψ,1) ↦ −(ψ,1)` folding the negative eigenvalue `ψ` into an orthonormal vector.

The Schmidt *number* `entangledThreeState.schmidtNumber = 2` is in
`AxQM/NC/Ch2/Exercise2_79.lean`, computed via
`PureState.schmidtNumber_eq_of_isSchmidtDecomposition` (the Schmidt number is the number of terms of
any reduced Schmidt decomposition), which is in `AxQM/Postulates/API/SchmidtNumber.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### The state `(|00⟩ + |01⟩ + |10⟩)/√3` -/

/-- The **unnormalised vector** `|00⟩ + |01⟩ + |10⟩` in the two-qubit state space
`qubit.space ⊗[ℂ] qubit.space`; its norm is `√3` (`entangledThreeVec_inner_self`). -/
def entangledThreeVec : (qubit ⊗ qubit).space :=
  (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec + (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec
    + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec

/-- **The squared norm of `|00⟩ + |01⟩ + |10⟩` is `3`:** `⟨ψ|ψ⟩ = 3`. The three kets `|00⟩`,
`|01⟩`, `|10⟩` are orthonormal (`qubitBasis_inner_qubitBasis`, `TensorProduct.inner_tmul`), so the
cross terms vanish and only the three unit diagonal terms survive. -/
theorem entangledThreeVec_inner_self : (inner ℂ entangledThreeVec entangledThreeVec : ℂ) = 3 := by
  change (@inner ℂ (TensorProduct ℂ qubit.space qubit.space) _
    entangledThreeVec entangledThreeVec : ℂ) = 3
  simp only [entangledThreeVec, inner_add_left, inner_add_right, TensorProduct.inner_tmul,
    qubitBasis_inner_qubitBasis]
  norm_num

/-- **The norm of `|00⟩ + |01⟩ + |10⟩` is `√3`** (from `entangledThreeVec_inner_self`). -/
theorem entangledThreeVec_norm : ‖entangledThreeVec‖ = Real.sqrt 3 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), entangledThreeVec_inner_self]; norm_num

/-- The unnormalised state vector is **nonzero** (its norm `√3 ≠ 0`). -/
theorem entangledThreeVec_ne_zero : entangledThreeVec ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [entangledThreeVec_norm]; positivity)

/-- The **state** `(|00⟩ + |01⟩ + |10⟩)/√3`, a genuinely entangled pure state of `qubit ⊗ qubit`,
built through the shared `PureState.normalize` constructor from the unnormalised vector
`entangledThreeVec`. -/
def entangledThreeState : PureState (qubit ⊗ qubit) :=
  PureState.normalize entangledThreeVec entangledThreeVec_ne_zero

/-- The underlying unit vector of `entangledThreeState` is `(√3)⁻¹ • (|00⟩ + |01⟩ + |10⟩)` — the
`normalize` coefficient `‖entangledThreeVec‖⁻¹` evaluated to `(√3)⁻¹` (`entangledThreeVec_norm`).
The explicit `(√3)⁻¹` form is convenient for rewriting in the Schmidt-decomposition algebra. -/
@[simp]
theorem entangledThreeState_vec :
    entangledThreeState.vec = (Real.sqrt 3 : ℂ)⁻¹ • entangledThreeVec := by
  rw [entangledThreeState, PureState.normalize_vec, entangledThreeVec_norm]

/-! ### The Schmidt eigenvectors `(s, 1) = s|0⟩ + |1⟩` and their normalisations -/

/-- The single-qubit vector `s|0⟩ + |1⟩` (i.e. `(s, 1)`) for a real `s`. Instantiated at the
golden ratio `φ` and its conjugate `ψ` these are the (unnormalised) eigenvectors of the reduced
density operator `ρᴬ`, hence the Schmidt bases of `entangledThreeState`. -/
def entangledThreeEvec (s : ℝ) : qubit.space :=
  (s : ℂ) • (qubitBasis 0).vec + (qubitBasis 1).vec

/-- **Inner product of two eigenvector lines:** `⟨(s,1) | (t,1)⟩ = s·t + 1` (for real `s`, `t`).
The computational basis is orthonormal (`qubitBasis_inner_qubitBasis`), so the only surviving
terms are `s̄·t·⟨0|0⟩ + ⟨1|1⟩`, and `s` is real. -/
theorem entangledThreeEvec_inner (s t : ℝ) :
    (inner ℂ (entangledThreeEvec s) (entangledThreeEvec t) : ℂ) = (s : ℂ) * t + 1 := by
  simp only [entangledThreeEvec, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, qubitBasis_inner_qubitBasis]
  norm_num [Complex.conj_ofReal]
  ring

/-- **The squared norm of the eigenvector line `(s, 1)` is `s² + 1`.** From
`entangledThreeEvec_inner s s = s² + 1`, whose real part is the squared norm. -/
theorem entangledThreeEvec_norm_sq (s : ℝ) : ‖entangledThreeEvec s‖ ^ 2 = s ^ 2 + 1 := by
  rw [← @inner_self_eq_norm_sq ℂ, entangledThreeEvec_inner]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    RCLike.re_to_complex, mul_zero, sub_zero]
  ring

/-- The eigenvector line `(s, 1)` is **nonzero** (its `|1⟩` component is `1`); equivalently its
squared norm `s² + 1` is positive. -/
theorem entangledThreeEvec_ne_zero (s : ℝ) : entangledThreeEvec s ≠ 0 := by
  intro h
  have := entangledThreeEvec_norm_sq s
  rw [h, norm_zero] at this
  nlinarith [sq_nonneg s]

/-- The **normalised Schmidt vector** `(s, 1)/‖(s, 1)‖`. At `s = φ` and `s = ψ` these are the
orthonormal Schmidt bases of `entangledThreeState`. -/
def entangledThreeSchmidtVec (s : ℝ) : qubit.space :=
  (‖entangledThreeEvec s‖ : ℂ)⁻¹ • entangledThreeEvec s

/-- The normalised Schmidt vector `(s, 1)/‖(s, 1)‖` is a **unit vector**. -/
theorem entangledThreeSchmidtVec_norm (s : ℝ) : ‖entangledThreeSchmidtVec s‖ = 1 := by
  have hne : (‖entangledThreeEvec s‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr (entangledThreeEvec_ne_zero s)
  rw [entangledThreeSchmidtVec, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hne]

/-! ### The spectral identity -/

/-- **The spectral identity.** The two eigenvector tensors combine to the (unnormalised) state:
`(φ,1)⊗(φ,1) − (ψ,1)⊗(ψ,1) = √5 · (|00⟩ + |01⟩ + |10⟩)`. This is the diagonalisation of the
symmetric coefficient matrix `!![1,1;1,0]` (eigenvalues `φ`, `ψ`), using `φ² − ψ² = φ − ψ = √5`
(where `φ`, `ψ` unfold to `(1 ± √5)/2`, so the `√5²` terms cancel and the scalar identities are
purely by `ring`). Stated in the raw tensor space `qubit.space ⊗[ℂ] qubit.space` (where the
bilinearity lemmas and `match_scalars` fire uniformly); it is definitionally the composite state
`√5 • entangledThreeVec`. -/
theorem entangledThree_tensor_diff :
    entangledThreeEvec Real.goldenRatio ⊗ₜ[ℂ] entangledThreeEvec Real.goldenRatio
        - entangledThreeEvec Real.goldenConj ⊗ₜ[ℂ] entangledThreeEvec Real.goldenConj
      = (Real.sqrt 5 : ℂ) • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec
          + (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 1).vec
          + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 0).vec) := by
  simp only [entangledThreeEvec, TensorProduct.add_tmul, TensorProduct.tmul_add,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add, smul_smul]
  match_scalars <;> ring

/-! ### Orthonormality of the Schmidt bases -/

/-- **The two normalised eigenvectors are orthogonal:** `⟨(φ,1)/‖·‖ | (ψ,1)/‖·‖⟩ = 0`. The
eigenvectors of a symmetric operator for distinct eigenvalues are orthogonal; concretely
`⟨(φ,1)|(ψ,1)⟩ = φ·ψ + 1 = 0` since `φ·ψ = −1`. -/
theorem entangledThreeSchmidt_orthogonal :
    (inner ℂ (entangledThreeSchmidtVec Real.goldenRatio)
      (entangledThreeSchmidtVec Real.goldenConj) : ℂ) = 0 := by
  rw [entangledThreeSchmidtVec, entangledThreeSchmidtVec, inner_smul_left, inner_smul_right,
    entangledThreeEvec_inner,
    show (Real.goldenRatio : ℂ) * Real.goldenConj + 1 = 0 by
      rw [← Complex.ofReal_mul, Real.goldenRatio_mul_goldenConj]; norm_num]
  ring

/-- **The left Schmidt basis `{(φ,1)/‖·‖, (ψ,1)/‖·‖}` is orthonormal.** Both vectors are unit
(`entangledThreeSchmidtVec_norm`) and orthogonal (`entangledThreeSchmidt_orthogonal`). -/
theorem entangledThreeSchmidt_orthonormal :
    Orthonormal ℂ ![entangledThreeSchmidtVec Real.goldenRatio,
      entangledThreeSchmidtVec Real.goldenConj] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [ite_true, inner_self_eq_norm_sq_to_K, entangledThreeSchmidtVec_norm]; norm_num
  · rw [ite_eq_right (by decide)]; exact entangledThreeSchmidt_orthogonal
  · rw [ite_eq_right (by decide), ← inner_conj_symm, entangledThreeSchmidt_orthogonal, map_zero]
  · rw [ite_true, inner_self_eq_norm_sq_to_K, entangledThreeSchmidtVec_norm]; norm_num

/-- **The right Schmidt basis `{(φ,1)/‖·‖, −(ψ,1)/‖·‖}` is orthonormal.** Same as the left basis
up to the sign on the second vector (which folds the *negative* eigenvalue `ψ` into a positive
Schmidt coefficient); negation preserves norms and orthogonality. -/
theorem entangledThreeSchmidt_orthonormal_neg :
    Orthonormal ℂ ![entangledThreeSchmidtVec Real.goldenRatio,
      -entangledThreeSchmidtVec Real.goldenConj] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [ite_true, inner_self_eq_norm_sq_to_K, entangledThreeSchmidtVec_norm]; norm_num
  · rw [ite_eq_right (by decide), inner_neg_right, entangledThreeSchmidt_orthogonal, neg_zero]
  · rw [ite_eq_right (by decide), inner_neg_left, ← inner_conj_symm,
        entangledThreeSchmidt_orthogonal,
      map_zero, neg_zero]
  · rw [ite_true, inner_neg_left, inner_neg_right, neg_neg, inner_self_eq_norm_sq_to_K,
      entangledThreeSchmidtVec_norm]; norm_num

/-! ### The Schmidt decomposition -/

/-- **First Schmidt term.** `√((3+√5)/6) · v̂₀⊗v̂₀ = (√15)⁻¹ · (φ,1)⊗(φ,1)`, where `v̂₀` is the
normalised eigenvector. The coefficient collapses because `√((3+√5)/6) = φ/√3`,
`‖(φ,1)‖² = φ²+1 = φ+2 = √5·φ`, so `√((3+√5)/6)/‖(φ,1)‖² = φ/(√3·√5·φ) = (√15)⁻¹`. -/
theorem entangledThree_term_zero :
    (Real.sqrt ((3 + Real.sqrt 5) / 6) : ℂ) • (entangledThreeSchmidtVec Real.goldenRatio
        ⊗ₜ[ℂ] entangledThreeSchmidtVec Real.goldenRatio)
      = (Real.sqrt 15 : ℂ)⁻¹ • (entangledThreeEvec Real.goldenRatio
          ⊗ₜ[ℂ] entangledThreeEvec Real.goldenRatio) := by
  have hcoeff : Real.sqrt ((3 + Real.sqrt 5) / 6)
      * (‖entangledThreeEvec Real.goldenRatio‖⁻¹ * ‖entangledThreeEvec Real.goldenRatio‖⁻¹)
      = (Real.sqrt 15)⁻¹ := by
    have hlam : Real.sqrt ((3 + Real.sqrt 5) / 6) = Real.goldenRatio / Real.sqrt 3 := by
      rw [show (3 + Real.sqrt 5) / 6 = Real.goldenRatio ^ 2 / 3 by
          linarith [Real.goldenRatio_sq, Real.goldenRatio_add_goldenConj,
            Real.goldenRatio_sub_goldenConj],
        Real.sqrt_div (sq_nonneg _) 3, Real.sqrt_sq Real.goldenRatio_pos.le]
    have hn : ‖entangledThreeEvec Real.goldenRatio‖⁻¹ * ‖entangledThreeEvec Real.goldenRatio‖⁻¹
        = (Real.goldenRatio + 2)⁻¹ := by
      rw [← mul_inv, ← sq, entangledThreeEvec_norm_sq]; congr 1; linarith [Real.goldenRatio_sq]
    rw [hlam, hn, show Real.goldenRatio + 2 = Real.sqrt 5 * Real.goldenRatio by
        nlinarith [Real.goldenRatio_sub_goldenConj, Real.goldenRatio_sq,
          Real.goldenRatio_mul_goldenConj],
      show Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]; norm_num]
    have h3 : Real.sqrt 3 ≠ 0 := by positivity
    have h5 : Real.sqrt 5 ≠ 0 := by positivity
    have hg : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
    -- freeze `φ` as an abstract nonzero scalar so `field_simp` cannot unfold it to `(1+√5)/2`
    revert hg; generalize Real.goldenRatio = g; intro hg
    field_simp
  simp only [entangledThreeSchmidtVec, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_smul]
  congr 1
  exact_mod_cast hcoeff

/-- **Second Schmidt term.** `√((3−√5)/6) · v̂₁⊗(−v̂₁) = −(√15)⁻¹ · (ψ,1)⊗(ψ,1)`, where `v̂₁` is
the normalised eigenvector. The sign folds the *negative* eigenvalue `ψ` into a positive Schmidt
coefficient; the magnitude collapses as in `entangledThree_term_zero` via `√((3−√5)/6) = −ψ/√3`,
`‖(ψ,1)‖² = ψ+2 = −√5·ψ`. -/
theorem entangledThree_term_one :
    (Real.sqrt ((3 - Real.sqrt 5) / 6) : ℂ) • (entangledThreeSchmidtVec Real.goldenConj
        ⊗ₜ[ℂ] (-entangledThreeSchmidtVec Real.goldenConj))
      = -((Real.sqrt 15 : ℂ)⁻¹ • (entangledThreeEvec Real.goldenConj
          ⊗ₜ[ℂ] entangledThreeEvec Real.goldenConj)) := by
  have hcoeff : Real.sqrt ((3 - Real.sqrt 5) / 6)
      * (‖entangledThreeEvec Real.goldenConj‖⁻¹ * ‖entangledThreeEvec Real.goldenConj‖⁻¹)
      = (Real.sqrt 15)⁻¹ := by
    have hlam : Real.sqrt ((3 - Real.sqrt 5) / 6) = -Real.goldenConj / Real.sqrt 3 := by
      rw [show (3 - Real.sqrt 5) / 6 = (-Real.goldenConj) ^ 2 / 3 by
          linarith [Real.goldenConj_sq, Real.goldenRatio_add_goldenConj,
            Real.goldenRatio_sub_goldenConj],
        Real.sqrt_div (sq_nonneg _) 3,
        Real.sqrt_sq (neg_nonneg.mpr Real.goldenConj_neg.le)]
    have hn : ‖entangledThreeEvec Real.goldenConj‖⁻¹ * ‖entangledThreeEvec Real.goldenConj‖⁻¹
        = (Real.goldenConj + 2)⁻¹ := by
      rw [← mul_inv, ← sq, entangledThreeEvec_norm_sq]; congr 1; linarith [Real.goldenConj_sq]
    rw [hlam, hn, show Real.goldenConj + 2 = -Real.sqrt 5 * Real.goldenConj by
        nlinarith [Real.goldenRatio_sub_goldenConj, Real.goldenConj_sq,
          Real.goldenRatio_mul_goldenConj],
      show Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]; norm_num]
    have h3 : Real.sqrt 3 ≠ 0 := by positivity
    have h5 : Real.sqrt 5 ≠ 0 := by positivity
    have hψ : Real.goldenConj ≠ 0 := Real.goldenConj_ne_zero
    -- freeze `ψ` as an abstract nonzero scalar so `field_simp` cannot unfold it to `(1−√5)/2`
    revert hψ; generalize Real.goldenConj = g; intro hψ
    field_simp
  rw [TensorProduct.tmul_neg, smul_neg]
  congr 1
  simp only [entangledThreeSchmidtVec, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_smul]
  congr 1
  exact_mod_cast hcoeff

/-- **Nielsen & Chuang, Exercise 2.79 (state 3).** The genuinely entangled two-qubit state
`(|00⟩ + |01⟩ + |10⟩)/√3` (`entangledThreeState`) has the Schmidt decomposition with the two
**irrational** Schmidt coefficients `√((3+√5)/6)` and `√((3−√5)/6)` (the square roots of the
eigenvalues `(3±√5)/6` of the reduced density operator `ρᴬ = (1/3)!![2,1;1,1]`) and Schmidt bases
the normalised eigenvectors `(φ,1)/‖·‖`, `(ψ,1)/‖·‖`. The right basis carries the extra sign
`(ψ,1) ↦ −(ψ,1)`, folding the negative eigenvalue `ψ = (1−√5)/2` of the coefficient matrix into a
positive Schmidt coefficient. This is the third state of the exercise, whose two nonzero Schmidt
coefficients witness that it is entangled with Schmidt number 2 (`entangledThreeState_schmidtNumber`
in `AxQM/NC/Ch2/Exercise2_79.lean`). -/
theorem entangledThree_isSchmidtDecomposition :
    entangledThreeState.IsSchmidtDecomposition
      ![Real.sqrt ((3 + Real.sqrt 5) / 6), Real.sqrt ((3 - Real.sqrt 5) / 6)]
      ![entangledThreeSchmidtVec Real.goldenRatio, entangledThreeSchmidtVec Real.goldenConj]
      ![entangledThreeSchmidtVec Real.goldenRatio, -entangledThreeSchmidtVec Real.goldenConj] := by
  have h5lt3 : Real.sqrt 5 < 3 := by
    nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  refine ⟨?_, entangledThreeSchmidt_orthonormal, entangledThreeSchmidt_orthonormal_neg, ?_, ?_⟩
  · -- the two Schmidt coefficients are strictly positive
    intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact Real.sqrt_pos.mpr (by positivity)
    · exact Real.sqrt_pos.mpr (by linarith)
  · -- ∑ λᵢ² = 1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith)]
    ring
  · -- the decomposition identity: `|ψ⟩ = √((3+√5)/6)•v̂₀⊗v̂₀ + √((3−√5)/6)•v̂₁⊗(−v̂₁)`
    have hscal : (Real.sqrt 15 : ℂ)⁻¹ * (Real.sqrt 5 : ℂ) = (Real.sqrt 3 : ℂ)⁻¹ := by
      have h : (Real.sqrt 15)⁻¹ * Real.sqrt 5 = (Real.sqrt 3)⁻¹ := by
        rw [show Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 by
          rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]; norm_num, mul_inv, mul_assoc,
          inv_mul_cancel₀ (by positivity : Real.sqrt 5 ≠ 0), mul_one]
      exact_mod_cast h
    rw [entangledThreeState_vec, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [entangledThree_term_zero, entangledThree_term_one, ← sub_eq_add_neg, ← smul_sub,
      entangledThree_tensor_diff, smul_smul, hscal]
    rfl

end AxQM
