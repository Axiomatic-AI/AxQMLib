/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PureState
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.Measurement

/-!
# AxQM.Postulates.API — projective measurement of a `±1` observable, and `v · σ` on `|0⟩`

The infrastructure behind Nielsen & Chuang Exercises 2.60–2.61: the **projective
measurement of an observable whose square is the identity** (a self-adjoint involution, eigenvalues
`±1`), and its specialization to the Pauli vector observable `v · σ` measured on the computational
basis state `|0⟩`.

## The `±1` (dichotomic) measurement

For an observable `A : Observable S` with `A² = I`, the two orthogonal projectors

* `Observable.projPlus  A = (I + A)/2`  (onto the `+1` eigenspace),
* `Observable.projMinus A = (I − A)/2`  (onto the `−1` eigenspace)

are the eigenprojectors of Exercise 2.60. Each is self-adjoint (`A` is), and — using `A² = I` —
idempotent (`P±² = P±`) with `P₊ + P₋ = I`; hence `∑ Mᵢ† Mᵢ = P₊ + P₋ = I` and they assemble into a
genuine two-outcome `Measurement (Fin 2) S`, `Observable.signMeasurement` (outcome `0 ↔ +1`,
`1 ↔ −1`). The Born rule for its `+1` outcome on a pure state is

`bornProb (signMeasurement A) |ψ⟩⟨ψ| 0 = (1 + ⟪A⟫_ψ) / 2`

(`Observable.bornProb_signMeasurement_plus`), in terms of the `Measurement.bornProb` and
`PureState.expectation` — the general form of Exercise 2.61's probability.

## The qubit `|0⟩` and `v · σ`

* `pauliObservable_expectation_qubitKet0` — `⟪v · σ⟫_{|0⟩} = v₃` (`= n 2`), since only the `Z`
  component survives on `|0⟩`. (The `|0⟩` state `qubitKet0` and the normalization helper
  `PureState.normalize` are in `AxQM/Postulates/API/Qubit.lean` and
  `AxQM/Postulates/API/PureState.lean`.)

Combining, the `+1` probability on `|0⟩` is `(1 + v₃)/2` — the answer to Exercise 2.61, stated as
the statement of Exercise 2.61 in `AxQM/NC/Ch2/Exercise2_61.lean`.
-/

open scoped InnerProductSpace Matrix
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

namespace Observable

/-! ### The eigenprojectors `P± = (I ± A)/2` of a `±1` observable -/

/-- The **`+1` eigenprojector** `P₊ = (I + A)/2` of an observable `A` (N&C Exercise 2.60). A genuine
projector exactly when `A² = I`. -/
def projPlus (A : Observable S) : S →L[ℂ] S := (2⁻¹ : ℂ) • (1 + A.op)

/-- The **`−1` eigenprojector** `P₋ = (I − A)/2` of an observable `A` (N&C Exercise 2.60). -/
def projMinus (A : Observable S) : S →L[ℂ] S := (2⁻¹ : ℂ) • (1 - A.op)

/-- `P₊` is self-adjoint: `A` is, and `(I + A)/2` is a real combination of self-adjoints. -/
theorem projPlus_isSelfAdjoint (A : Observable S) : IsSelfAdjoint A.projPlus := by
  rw [projPlus, IsSelfAdjoint, star_smul, star_add, star_one, A.selfAdjoint.star_eq]
  norm_num

/-- `P₋` is self-adjoint. -/
theorem projMinus_isSelfAdjoint (A : Observable S) : IsSelfAdjoint A.projMinus := by
  rw [projMinus, IsSelfAdjoint, star_smul, star_sub, star_one, A.selfAdjoint.star_eq]
  norm_num

/-- `adjoint P₊ = P₊` (self-adjointness in operator form). -/
theorem adjoint_projPlus (A : Observable S) : adjoint A.projPlus = A.projPlus := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact A.projPlus_isSelfAdjoint

/-- `adjoint P₋ = P₋`. -/
theorem adjoint_projMinus (A : Observable S) : adjoint A.projMinus = A.projMinus := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact A.projMinus_isSelfAdjoint

/-- For an involution `A² = I`, the `+1` eigenprojector is **idempotent**: `P₊² = P₊`. -/
theorem projPlus_mul_self (A : Observable S) (hinv : A.op * A.op = 1) :
    A.projPlus * A.projPlus = A.projPlus := by
  have hB : (1 + A.op) * (1 + A.op) = (2 : ℂ) • (1 + A.op) := by
    rw [two_smul, mul_add, add_mul, add_mul]
    simp only [mul_one, one_mul, hinv]; abel
  rw [projPlus, smul_mul_smul_comm, hB, smul_smul]
  norm_num

/-- For an involution `A² = I`, the `−1` eigenprojector is idempotent: `P₋² = P₋`. -/
theorem projMinus_mul_self (A : Observable S) (hinv : A.op * A.op = 1) :
    A.projMinus * A.projMinus = A.projMinus := by
  have hB : (1 - A.op) * (1 - A.op) = (2 : ℂ) • (1 - A.op) := by
    rw [two_smul, mul_sub, sub_mul, sub_mul]
    simp only [mul_one, one_mul, hinv]; abel
  rw [projMinus, smul_mul_smul_comm, hB, smul_smul]
  norm_num

/-- The eigenprojectors resolve the identity: `P₊ + P₋ = I`. -/
theorem projPlus_add_projMinus (A : Observable S) : A.projPlus + A.projMinus = 1 := by
  rw [projPlus, projMinus, ← smul_add]
  rw [show (1 + A.op) + (1 - A.op) = (2 : ℂ) • (1 : S →L[ℂ] S) by rw [two_smul]; abel, smul_smul]
  norm_num

/-! ### The two-outcome projective measurement -/

/-- The **projective measurement of a `±1` observable** `A` (an involution `A² = I`): the
two-outcome measurement with operators `M₀ = P₊`, `M₁ = P₋` (outcome `0 ↔ +1`, `1 ↔ −1`).
Completeness `∑ᵢ Mᵢ† Mᵢ = P₊ + P₋ = I` uses that each `P±` is a self-adjoint idempotent. This is
the projective measurement "of the observable `A`" (N&C §2.2.5); its `+1` outcome is Exercise
2.61. -/
def signMeasurement (A : Observable S) (hinv : A.op * A.op = 1) : Measurement (Fin 2) S where
  op := ![A.projPlus, A.projMinus]
  complete := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      A.adjoint_projPlus, A.adjoint_projMinus, ← ContinuousLinearMap.mul_def,
      A.projPlus_mul_self hinv, A.projMinus_mul_self hinv]
    exact A.projPlus_add_projMinus

@[simp]
theorem signMeasurement_op_zero (A : Observable S) (hinv : A.op * A.op = 1) :
    (A.signMeasurement hinv).op 0 = A.projPlus := rfl

@[simp]
theorem signMeasurement_op_one (A : Observable S) (hinv : A.op * A.op = 1) :
    (A.signMeasurement hinv).op 1 = A.projMinus := rfl

/-! ### The Born rule for the `+1` outcome on a pure state -/

/-- **Born rule for the `+1` outcome** of the `±1` measurement of `A` on a pure state `|ψ⟩`:
`p(+1) = (1 + ⟪A⟫_ψ)/2`. In terms of `Measurement.bornProb` and
`PureState.expectation`: `p(+1) = Re⟪ψ, P₊ ψ⟫ = Re⟪ψ, (ψ + A ψ)/2⟫ = (1 + Re⟪ψ, A ψ⟫)/2`.
The general form of Nielsen & Chuang Exercise 2.61's probability. -/
theorem bornProb_signMeasurement_plus (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) :
    (A.signMeasurement hinv).bornProb ψ.toState 0 = (1 + ψ.expectation A) / 2 := by
  rw [Measurement.bornProb, POVM.toPMF_eq, Measurement.toPOVM_elements, signMeasurement_op_zero,
    A.adjoint_projPlus]
  simp only [← ContinuousLinearMap.mul_def]
  rw [A.projPlus_mul_self hinv, PureState.toState_op, ContinuousLinearMap.mul_def,
    InnerProductSpace.comp_rankOne, InnerProductSpace.trace_rankOne, projPlus]
  simp only [_root_.smul_apply, _root_.add_apply,
    one_apply_eq_self, inner_smul_right, inner_add_right,
    inner_self_eq_norm_sq_to_K, ψ.normalized, PureState.expectation]
  rw [RCLike.re_to_complex, Complex.mul_re, Complex.add_re]; norm_num; ring

/-- **Born rule for the `−1` outcome** of the `±1` measurement of `A` on a pure state `|ψ⟩`:
`p(−1) = (1 − ⟪A⟫_ψ)/2`. The companion of `bornProb_signMeasurement_plus`, obtained from it via
Born-rule normalization `p(+1) + p(−1) = 1` (`sum_bornProb_eq_one` on the two-outcome measurement):
`p(−1) = 1 − (1 + ⟪A⟫_ψ)/2 = (1 − ⟪A⟫_ψ)/2`. -/
theorem bornProb_signMeasurement_minus (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) :
    (A.signMeasurement hinv).bornProb ψ.toState 1 = (1 - ψ.expectation A) / 2 := by
  have hsum := (A.signMeasurement hinv).sum_bornProb_eq_one ψ.toState
  rw [Fin.sum_univ_two, A.bornProb_signMeasurement_plus hinv ψ] at hsum
  linarith

/-- The post-measurement operation for the `+1` outcome sends `|ψ⟩⟨ψ|` to the rank-one operator
`|P₊ψ⟩⟨P₊ψ|`: `M₀ ρ M₀† = P₊ |ψ⟩⟨ψ| P₊ = |P₊ψ⟩⟨P₊ψ|`, using `adjoint P₊ = P₊` and the rank-one
composition rules. The core of both the Born-rule norm-square form and the collapse identity. -/
theorem postOp_signMeasurement_zero (A : Observable S) (hinv : A.op * A.op = 1) (ψ : PureState S) :
    ContinuousLinearMap.postOp (A.signMeasurement hinv).op ψ.toState.op 0
      = rankOne ℂ (A.projPlus ψ.vec) (A.projPlus ψ.vec) := by
  simp only [ContinuousLinearMap.postOp, signMeasurement_op_zero, PureState.toState_op,
    A.adjoint_projPlus, InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp]

/-- **Born probability of `+1` as a squared norm:** `p(+1) = ‖P₊|ψ⟩‖²`. Follows from
`bornProb_eq_re_trace_postOp` and `postOp_signMeasurement_zero`. Used to certify that `+1` is a
possible outcome (`p ≠ 0`) exactly when `P₊|ψ⟩ ≠ 0`. -/
theorem bornProb_signMeasurement_plus_eq_normSq (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) :
    (A.signMeasurement hinv).bornProb ψ.toState 0 = ‖A.projPlus ψ.vec‖ ^ 2 := by
  rw [Measurement.bornProb_eq_re_trace_postOp, postOp_signMeasurement_zero,
    InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq]

/-- If the `+1` outcome is possible (`p(+1) ≠ 0`), then `P₊|ψ⟩ ≠ 0` — the post-measurement state is
well-defined. Contrapositive of `bornProb_signMeasurement_plus_eq_normSq`. -/
theorem projPlus_apply_ne_zero_of_bornProb (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) (hp : (A.signMeasurement hinv).bornProb ψ.toState 0 ≠ 0) :
    A.projPlus ψ.vec ≠ 0 := by
  intro h0
  exact hp (by rw [bornProb_signMeasurement_plus_eq_normSq, h0, norm_zero]; norm_num)

/-! ### The post-measurement state after obtaining `+1` -/

/-- The **normalized `+1` post-measurement pure state** `P₊|ψ⟩ / ‖P₊|ψ⟩‖` — the collapsed state of
Postulate 4 after the `±1` measurement of `A` yields `+1`, defined when `P₊|ψ⟩ ≠ 0` (i.e. when `+1`
is a possible outcome). It is the `+1` eigenstate of `A` (Nielsen & Chuang Exercise 2.61). -/
def postMeasPlus (A : Observable S) (ψ : PureState S) (hne : A.projPlus ψ.vec ≠ 0) :
    PureState S :=
  PureState.normalize (A.projPlus ψ.vec) hne

@[simp]
theorem postMeasPlus_vec (A : Observable S) (ψ : PureState S) (hne : A.projPlus ψ.vec ≠ 0) :
    (A.postMeasPlus ψ hne).vec = ((‖A.projPlus ψ.vec‖ : ℝ) : ℂ)⁻¹ • A.projPlus ψ.vec := rfl

/-- **Postulate 4 / Exercise 2.61 (state update).** When the `±1` measurement of `A` on `|ψ⟩` yields
`+1`, the system collapses to the normalized state `P₊|ψ⟩ / ‖P₊|ψ⟩‖`: the post-measurement state is
`|ψ'⟩⟨ψ'|` for `|ψ'⟩ = postMeasPlus`. In terms of `Measurement.postMeasurement`.
Proof: `M₀ ρ M₀† = P₊|ψ⟩⟨ψ|P₊ = |P₊ψ⟩⟨P₊ψ|` (rank-one algebra, `adjoint P₊ = P₊`), and the
normalization `tr(·)⁻¹ = ‖P₊ψ‖⁻²` folds into the rank-one via sesquilinearity. -/
theorem postMeasurement_signMeasurement_plus (A : Observable S) (hinv : A.op * A.op = 1)
    (ψ : PureState S) (hne : A.projPlus ψ.vec ≠ 0)
    (hp : (A.signMeasurement hinv).bornProb ψ.toState 0 ≠ 0) :
    (A.signMeasurement hinv).postMeasurement ψ.toState 0 hp = (A.postMeasPlus ψ hne).toState := by
  have htr : RCLike.re (LinearMap.trace ℂ S.space
      ↑(ContinuousLinearMap.postOp (A.signMeasurement hinv).op ψ.toState.op 0))
      = ‖A.projPlus ψ.vec‖ ^ 2 := by
    rw [postOp_signMeasurement_zero, InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq]
  apply State.ext
  rw [Measurement.postMeasurement_op, ContinuousLinearMap.postState, htr,
    postOp_signMeasurement_zero, PureState.toState_op, postMeasPlus_vec,
    InnerProductSpace.rankOne_smul_smul_self]
  congr 1
  rw [map_inv₀, Complex.conj_ofReal]
  push_cast
  ring

end Observable

/-! ### The `±1` eigenvalue selected by a data bit -/

/-- **The `±1` eigenvalue selected by a bit `s`** under the sign-measurement convention: `+1` for
`s = 0`, `−1` for `s = 1` (i.e. `(-1)^s`). A protocol-neutral selector: in a qubit
key-distribution protocol the `s`-th data bit prepares the `signEigenvalue s`-eigenstate of a basis
observable, and `s` is the `Fin 2` index of the corresponding `Observable.signMeasurement` outcome
(`0 ↔ +1`, `1 ↔ −1`). Shared by the BB84 (Exercise 12.26) and six-state (Exercise 12.29)
protocols. -/
def signEigenvalue : Fin 2 → ℝ := ![1, -1]

@[simp] theorem signEigenvalue_zero : signEigenvalue 0 = 1 := rfl

@[simp] theorem signEigenvalue_one : signEigenvalue 1 = -1 := rfl

/-- `signEigenvalue s ≠ 0` (it is `±1`). The nonzero-eigenvalue side-condition consumed by the
anticommutation fair-coin rules (`Observable.bornProb_signMeasurement_*_of_anticomm_eigenstate`). -/
theorem signEigenvalue_ne_zero (s : Fin 2) : signEigenvalue s ≠ 0 := by
  fin_cases s <;> norm_num [signEigenvalue]

/-! ### The Pauli vector observable on `|0⟩` -/

/-- **The expectation of `v · σ` in the state `|0⟩` is `v₃`** (`= n 2`): only the `Z` component of
`n · σ = n₀X + n₁Y + n₂Z` contributes on `|0⟩`, since `⟨0|X|0⟩ = ⟨0|Y|0⟩ = 0` and `⟨0|Z|0⟩ = 1`.
(`qubitKet0 = |0⟩` is the computational basis ket from `Postulates/API/Qubit.lean`.) -/
theorem pauliObservable_expectation_qubitKet0 (n : Fin 3 → ℝ) :
    qubitKet0.expectation (pauliObservable n) = n 2 := by
  have happ : (pauliObservable n).op qubitKet0.vec
      = WithLp.toLp 2 (Concrete.pauliDot n *ᵥ Concrete.ket 0) := by
    rw [qubitKet0_vec, pauliObservable_op]
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.pauliDot n)
        (WithLp.toLp 2 (Concrete.ket 0)) = _
    rw [Matrix.toEuclideanCLM_toLp]
  rw [PureState.expectation, happ, qubitKet0_vec]
  change (⟪(WithLp.toLp 2 (Concrete.ket 0) : EuclideanSpace ℂ (Fin 2)),
      WithLp.toLp 2 (Concrete.pauliDot n *ᵥ Concrete.ket 0)⟫_ℂ).re = n 2
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Concrete.pauliDot_eq, Concrete.ket, dotProduct, Matrix.mulVec, Pi.single_apply]

/-! ### The Pauli-`Z` eigenprojectors as computational rank-one projectors -/

/-- The `+1` eigenprojector of Pauli `Z` is `|0⟩⟨0|`: `(I + Z)/2 = |0⟩⟨0|`. -/
theorem pauliZObservable_projPlus_rankOne :
    pauliZObservable.projPlus = rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec := by
  apply ContinuousLinearMap.coe_injective
  apply Module.Basis.ext qubitModuleBasis
  intro i
  rw [qubitModuleBasis_apply]
  simp only [ContinuousLinearMap.coe_coe, Observable.projPlus, _root_.smul_apply,
    _root_.add_apply, one_apply_eq_self,
    pauliZObservable_op_apply_qubitBasis, rankOne_apply, qubitBasis_inner_qubitBasis]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, pow_zero, pow_one, Fin.reduceEq,
      ite_true, ite_false]
  all_goals module

/-- The `-1` eigenprojector of Pauli `Z` is `|1⟩⟨1|`: `(I - Z)/2 = |1⟩⟨1|`. -/
theorem pauliZObservable_projMinus_rankOne :
    pauliZObservable.projMinus = rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec := by
  apply ContinuousLinearMap.coe_injective
  apply Module.Basis.ext qubitModuleBasis
  intro i
  rw [qubitModuleBasis_apply]
  simp only [ContinuousLinearMap.coe_coe, Observable.projMinus, _root_.smul_apply,
    _root_.sub_apply, one_apply_eq_self,
    pauliZObservable_op_apply_qubitBasis, rankOne_apply, qubitBasis_inner_qubitBasis]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, pow_zero, pow_one, Fin.reduceEq,
      ite_true, ite_false]
  all_goals module

/-! ### The Pauli-`X` eigenprojectors as `|±⟩` rank-one projectors -/

/-- The `+1` eigenprojector of Pauli `X` is `|+⟩⟨+|`: `(I + X)/2 = |+⟩⟨+|`.  The Hadamard-basis
counterpart of `pauliZObservable_projPlus_rankOne`; `|+⟩ = qubitPlus` is the `+1` eigenstate. -/
theorem pauliXObservable_projPlus_rankOne :
    pauliXObservable.projPlus = rankOne ℂ qubitPlus.vec qubitPlus.vec := by
  apply ContinuousLinearMap.coe_injective
  apply Module.Basis.ext qubitModuleBasis
  intro i
  rw [qubitModuleBasis_apply]
  simp only [ContinuousLinearMap.coe_coe, Observable.projPlus, _root_.smul_apply,
    _root_.add_apply, one_apply_eq_self,
    pauliXObservable_op_apply_qubitBasis, rankOne_apply]
  rw [← inner_conj_symm qubitPlus.vec (qubitBasis i).vec, inner_qubitBasis_qubitPlus,
    Concrete.xPlus_apply, qubitPlus_vec_eq_smul_add, smul_smul]
  have hc : (starRingEnd ℂ) Concrete.invSqrt2 * Concrete.invSqrt2 = 2⁻¹ := by
    rw [starRingEnd_apply, Concrete.invSqrt2_star, Concrete.invSqrt2_mul_self]
  rw [hc]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.reduceAdd]
  · simp only [Fin.mk_one, Fin.reduceAdd]
    module

/-- The `−1` eigenprojector of Pauli `X` is `|−⟩⟨−|`: `(I − X)/2 = |−⟩⟨−|`.  The Hadamard-basis
counterpart of `pauliZObservable_projMinus_rankOne`; `|−⟩ = qubitMinus` is the `−1` eigenstate. -/
theorem pauliXObservable_projMinus_rankOne :
    pauliXObservable.projMinus = rankOne ℂ qubitMinus.vec qubitMinus.vec := by
  apply ContinuousLinearMap.coe_injective
  apply Module.Basis.ext qubitModuleBasis
  intro i
  rw [qubitModuleBasis_apply]
  simp only [ContinuousLinearMap.coe_coe, Observable.projMinus, _root_.smul_apply,
    _root_.sub_apply, one_apply_eq_self,
    pauliXObservable_op_apply_qubitBasis, rankOne_apply]
  rw [← inner_conj_symm qubitMinus.vec (qubitBasis i).vec, inner_qubitBasis_qubitMinus,
    qubitMinus_vec_eq_smul_sub, smul_smul]
  have hc : (starRingEnd ℂ) Concrete.invSqrt2 * Concrete.invSqrt2 = 2⁻¹ := by
    rw [starRingEnd_apply, Concrete.invSqrt2_star, Concrete.invSqrt2_mul_self]
  fin_cases i
  · simp only [Concrete.xMinus, Fin.zero_eta, Matrix.cons_val_zero, hc, Fin.reduceAdd]
  · simp only [Concrete.xMinus, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      map_neg, neg_mul, hc, Fin.reduceAdd]
    module

end AxQM
