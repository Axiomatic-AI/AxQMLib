/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ThreeQubitBitFlipCode
import AxQM.Postulates.API.QuditMeasurement
import AxQM.Postulates.API.PeriodShift
import AxQM.Postulates.API.ProjectiveRecovery

/-!
# AxQM.Postulates.API — the eight-projector recovery of the three-qubit bit-flip code

Nielsen & Chuang, Exercise 10.4 asks what happens when the syndrome measurement of the
three-qubit bit-flip code is performed with the **eight rank-one computational-basis
projectors** `|x⟩⟨x|` (`x : Fin 8`) instead of the four commuting syndrome projectors. This
file supplies the computational core behind parts (2)–(3): the recovery as a
`ProjectiveUnitaryRecovery`, the *dephasing identity* that fully computes its action, and the
encoded logical qubit `a|0_L⟩ + b|1_L⟩`. The conclusions ("the recovery destroys code
superpositions") are in `AxQM/NC/Ch10/Exercise10_4.lean`.

## The recovery

`bitFlipRecovery` is the `ProjectiveUnitaryRecovery (Fin 8) (qudit 8)` whose syndrome
measurement is the eight-projector computational-basis measurement `quditMeasurement 8`
(projective — each `|x⟩⟨x|` is a rank-one projector) and whose conditional correction on
outcome `x` is the recovery flip `quditPerm (xorPerm (errorMask (syndrome x)))` (re-apply the
diagnosed single-qubit error). Its action is the operator sum
`R(ρ) = ∑ₓ Wₓ |x⟩⟨x| ρ |x⟩⟨x| Wₓ†` (`ProjectiveUnitaryRecovery.apply`).

## The dephasing identity

Because each syndrome operator is the *rank-one* projector `|x⟩⟨x|`, the Kraus term collapses
to a scalar times a rank-one projector:

  `Wₓ |x⟩⟨x| ρ |x⟩⟨x| Wₓ† = ⟨x|ρ|x⟩ · |t x⟩⟨t x|`,   `t x = recoveryTarget x ∈ {000, 111}`,

so `R(ρ) = ∑ₓ ⟨x|ρ|x⟩ · |t x⟩⟨t x|` (`bitFlipRecovery_apply_op`) — the recovered operator keeps
only the *diagonal* `⟨x|ρ|x⟩` of the input in the computational basis and relabels each `|x⟩`
to its majority codeword `|t x⟩`. This is exactly why the recovery destroys superpositions: all
off-diagonal coherence (e.g. `⟨000|ρ|111⟩`) is erased.

## Dependencies

The statements use the bit-flip combinatorics (`xorPerm`/`syndrome`/`recoveryTarget`) of
`AxQM/Concrete/ThreeQubitBitFlipCode.lean` and the recovery notion
`ProjectiveUnitaryRecovery`.
-/

open scoped InnerProductSpace
open AxQM.Concrete InnerProductSpace ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The eight-projector recovery of the three-qubit bit-flip code** (Nielsen & Chuang, Exercise
10.4): the projective-measurement-then-conditional-unitary recovery whose

* syndrome measurement is the eight-projector computational-basis measurement `quditMeasurement 8`
  (outcome `x` the rank-one projector `|x⟩⟨x|`; projective because each `|x⟩⟨x|` is a star
  projection, `isStarProjection_rankOne_self`), and
* conditional correction on outcome `x` is the recovery flip
  `quditPerm (xorPerm (errorMask (syndrome x)))` — the permutation gate that re-applies the
  single-qubit error diagnosed by the majority-vote `syndrome x`.

Its action `R(ρ) = ∑ₓ Wₓ |x⟩⟨x| ρ |x⟩⟨x| Wₓ†` is `ProjectiveUnitaryRecovery.apply`. -/
def bitFlipRecovery : ProjectiveUnitaryRecovery (Fin 8) (qudit 8) where
  meas := quditMeasurement 8
  proj := fun i => by
    rw [quditMeasurement_op]
    exact isStarProjection_rankOne_self (quditBasis i).normalized
  corr x := quditPerm (xorPerm (errorMask (syndrome x)))

@[simp] theorem bitFlipRecovery_meas : bitFlipRecovery.meas = quditMeasurement 8 := rfl

@[simp] theorem bitFlipRecovery_corr (x : Fin 8) :
    bitFlipRecovery.corr x = quditPerm (xorPerm (errorMask (syndrome x))) := rfl

/-- **The correction gate maps a syndrome outcome to its majority codeword**: on outcome `x` the
recovery flip carries the basis vector `|x⟩` to `|recoveryTarget x⟩` (the majority-vote codeword,
`0 = 000` or `7 = 111`). Combines the action of the permutation gate on basis vectors
(`quditPerm_op_apply_quditBasis`) with `xorPerm_errorMask_syndrome`. -/
theorem bitFlipRecovery_corr_op_quditBasis (x : Fin 8) :
    (bitFlipRecovery.corr x).op (quditBasis x).vec = (quditBasis (recoveryTarget x)).vec := by
  rw [bitFlipRecovery_corr, quditPerm_op_apply_quditBasis, xorPerm_errorMask_syndrome]

/-- **The dephasing identity for the eight-projector recovery** (the computational core of Exercise
10.4). The recovered density operator is

  `R(ρ) = ∑ₓ ⟨x|ρ|x⟩ · |t x⟩⟨t x|`,   `t x = recoveryTarget x`,

i.e. the recovery keeps only the *diagonal* `⟨x|ρ|x⟩` of the input in the computational basis
and relabels each basis state `|x⟩` to its majority codeword `|t x⟩`. Every off-diagonal
coherence of `ρ` is erased. Proved term-by-term: `Wₓ |x⟩⟨x|` is rank-one, so its Kraus term is
`⟨x|ρ|x⟩ · |Wₓ x⟩⟨Wₓ x| = ⟨x|ρ|x⟩ · |t x⟩⟨t x|` (`rankOne_apply`, `adjoint_rankOne`,
`bitFlipRecovery_corr_op_quditBasis`). -/
theorem bitFlipRecovery_apply_op (ρ : State (qudit 8)) :
    (bitFlipRecovery.apply ρ).op
      = ∑ x : Fin 8, inner ℂ (quditBasis x).vec (ρ.op (quditBasis x).vec) •
          rankOne ℂ (quditBasis (recoveryTarget x)).vec (quditBasis (recoveryTarget x)).vec := by
  rw [ProjectiveUnitaryRecovery.apply_op, krausSumₗ_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Measurement.conjUnitary_op, bitFlipRecovery_meas, quditMeasurement_op,
    ContinuousLinearMap.adjoint_comp, adjoint_rankOne]
  ext v
  simp only [ContinuousLinearMap.comp_apply, rankOne_apply, map_smul,
    ContinuousLinearMap.adjoint_inner_right, bitFlipRecovery_corr_op_quditBasis,
    _root_.smul_apply]
  rw [smul_comm]

/-- **The encoded logical qubit** `a|0_L⟩ + b|1_L⟩ = a|000⟩ + b|111⟩` of the three-qubit
bit-flip code, as the pure state `a•|0⟩ + b•|7⟩` of `qudit 8`, for amplitudes with
`‖a‖² + ‖b‖² = 1`. It is normalised because the codewords `|0⟩ = |000⟩` and `|7⟩ = |111⟩` are
orthonormal, so `‖a•|0⟩ + b•|7⟩‖² = ‖a‖² + ‖b‖²`. The two logical basis codewords are
`encodedCodeState 1 0` (`|0_L⟩`) and `encodedCodeState 0 1` (`|1_L⟩`); a genuine superposition
has `a ≠ 0` and `b ≠ 0`. -/
def encodedCodeState (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : PureState (qudit 8) where
  vec := a • (quditBasis 0).vec + b • (quditBasis 7).vec
  normalized := by
    set v : (qudit 8).space := a • (quditBasis 0).vec + b • (quditBasis 7).vec with hv
    have horth : inner ℂ (quditBasis (0 : Fin 8)).vec (quditBasis (7 : Fin 8)).vec = 0 := by
      rw [quditBasis_inner, ite_eq_right (by decide)]
    have hcross : RCLike.re (inner ℂ (a • (quditBasis (0 : Fin 8)).vec)
        (b • (quditBasis (7 : Fin 8)).vec)) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth, mul_zero, mul_zero, map_zero]
    have hsq : ‖v‖ ^ 2 = 1 := by
      rw [hv, norm_add_sq (𝕜 := ℂ), hcross, norm_smul, norm_smul, (quditBasis 0).normalized,
        (quditBasis 7).normalized, mul_one, mul_one, mul_zero, add_zero]
      exact h
    rw [← Real.sqrt_sq (norm_nonneg v), hsq, Real.sqrt_one]

/-- The underlying vector of `encodedCodeState a b h` is `a•|0⟩ + b•|7⟩`. -/
@[simp] theorem encodedCodeState_vec (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    (encodedCodeState a b h).vec = a • (quditBasis 0).vec + b • (quditBasis 7).vec := rfl

/-- **The recovery relabels a computational-basis input to its majority codeword.** Applied to a
basis state `|c⟩` the recovery returns `|recoveryTarget c⟩` (the majority-vote codeword `000` or
`111`): measuring `|c⟩⟨c|` is certain to give outcome `c`, whose correction flip carries `|c⟩` to
`|recoveryTarget c⟩`. A direct evaluation of the dephasing identity at the diagonal input
`⟨x||c⟩⟨c||x⟩ = δₓ,c`. -/
theorem bitFlipRecovery_apply_quditBasis (c : Fin 8) :
    bitFlipRecovery.apply (quditBasis c).toState = (quditBasis (recoveryTarget c)).toState := by
  apply State.ext
  simp only [bitFlipRecovery_apply_op, PureState.toState_op]
  have hcc : inner ℂ (quditBasis c).vec (quditBasis c).vec = (1 : ℂ) := by
    rw [quditBasis_inner]; simp
  rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
  · rw [rankOne_apply, inner_smul_right, hcc, one_mul, one_smul]
  · intro x _ hx
    rw [rankOne_apply, inner_smul_right, quditBasis_inner, quditBasis_inner, ite_eq_right hx,
      mul_zero, zero_smul]

/-- **The recovery erases the codeword coherence** `⟨000|R(ρ)|111⟩ = 0` for every state `ρ`. The
dephasing identity writes `R(ρ)` as a sum of rank-one projectors `|t x⟩⟨t x|` onto codewords
`t x ∈ {000, 111}`, so its `(000, 111)` matrix element vanishes term-by-term: no `t x` is both `000`
and `111`. This is the exact obstruction to recovering a code superposition. -/
theorem bitFlipRecovery_apply_inner_logical (ρ : State (qudit 8)) :
    inner ℂ (quditBasis (0 : Fin 8)).vec ((bitFlipRecovery.apply ρ).op (quditBasis 7).vec) = 0 := by
  rw [bitFlipRecovery_apply_op, _root_.sum_apply, inner_sum]
  apply Finset.sum_eq_zero
  intro x _
  rw [_root_.smul_apply, rankOne_apply, inner_smul_right, inner_smul_right,
    quditBasis_inner, quditBasis_inner]
  rcases recoveryTarget_eq x with hx | hx <;> rw [hx] <;> simp

/-- Amplitude of the encoded state on `|000⟩`: `⟨000, a|000⟩ + b|111⟩⟩ = a`. -/
theorem encodedCodeState_inner_zero (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    inner ℂ (quditBasis (0 : Fin 8)).vec (encodedCodeState a b h).vec = a := by
  rw [encodedCodeState_vec, inner_add_right, inner_smul_right, inner_smul_right,
    quditBasis_inner, quditBasis_inner]
  simp

/-- Amplitude of the encoded state on `|111⟩`: `⟨111, a|000⟩ + b|111⟩⟩ = b`. -/
theorem encodedCodeState_inner_seven (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    inner ℂ (quditBasis (7 : Fin 8)).vec (encodedCodeState a b h).vec = b := by
  rw [encodedCodeState_vec, inner_add_right, inner_smul_right, inner_smul_right,
    quditBasis_inner, quditBasis_inner]
  simp

/-- **The codeword coherence of the encoded state** `⟨000|ρ|111⟩ = b̄·a` for `ρ = |ψ⟩⟨ψ|`,
`ψ = a|000⟩ + b|111⟩`, nonzero exactly when both amplitudes are nonzero. Contrasted with
`bitFlipRecovery_apply_inner_logical` (always `0`), this shows the recovery changes a genuine
code superposition. -/
theorem encodedCodeState_toState_inner (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    inner ℂ (quditBasis (0 : Fin 8)).vec
        ((encodedCodeState a b h).toState.op (quditBasis 7).vec)
      = (starRingEnd ℂ) b * a := by
  rw [PureState.toState_op, rankOne_apply, inner_smul_right, encodedCodeState_inner_zero,
    ← inner_conj_symm, encodedCodeState_inner_seven]

/-- **Amplitude of the encoded state on a computational-basis vector** (`δ`-form). For any
`x : Fin 8`, `⟨x, a|000⟩ + b|111⟩⟩ = a·δ_{x,0} + b·δ_{x,7}`: the encoded logical qubit has amplitude
`a` on `|000⟩`, `b` on `|111⟩`, and `0` on every other basis vector. Generalises
`encodedCodeState_inner_zero` / `encodedCodeState_inner_seven` to an arbitrary basis index; the
input to the diagonal computation below. -/
theorem encodedCodeState_inner (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (x : Fin 8) :
    inner ℂ (quditBasis x).vec (encodedCodeState a b h).vec
      = a * (if x = 0 then 1 else 0) + b * (if x = 7 then 1 else 0) := by
  rw [encodedCodeState_vec, inner_add_right, inner_smul_right, inner_smul_right,
    quditBasis_inner, quditBasis_inner]

/-- `conj z · z = ‖z‖²` (as a complex number), the identity turning a diagonal `⟨x|ρ|x⟩` into a
Born weight. -/
private theorem conj_mul_self_ofReal (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.conj_mul']; push_cast; ring

/-- **The diagonal of the encoded density operator** in the computational basis:
`⟨x|ρ|x⟩ = ‖a‖²·δ_{x,0} + ‖b‖²·δ_{x,7}` for `ρ = |ψ_L⟩⟨ψ_L|`, `ψ_L = a|000⟩ + b|111⟩`. These are the
Born weights the eight-projector measurement reads off `ψ_L`: `‖a‖²` on `|000⟩`, `‖b‖²` on `|111⟩`,
`0` on every other basis state. -/
theorem encodedCodeState_toState_diag (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (x : Fin 8) :
    inner ℂ (quditBasis x).vec ((encodedCodeState a b h).toState.op (quditBasis x).vec)
      = (((if x = 0 then ‖a‖ ^ 2 else 0) + (if x = 7 then ‖b‖ ^ 2 else 0) : ℝ) : ℂ) := by
  rw [PureState.toState_op, rankOne_apply, inner_smul_right, ← inner_conj_symm]
  simp only [encodedCodeState_inner]
  fin_cases x <;> simp [conj_mul_self_ofReal]

/-- **The eight-projector recovery dephases the encoded logical qubit into a classical mixture.**
For the encoded state `ρ = |ψ_L⟩⟨ψ_L|` with `ψ_L = a|000⟩ + b|111⟩`, the recovered operator is
`R(ρ) = ‖a‖²·|000⟩⟨000| + ‖b‖²·|111⟩⟨111|` — a diagonal (incoherent) mixture of the two logical
codewords with the input Born weights. All coherence `⟨000|ρ|111⟩ = b̄a` has been erased: the
measurement collapses the superposition, the majority-vote correction relabels each computational
outcome `x` to its codeword `recoveryTarget x`, and only `x ∈ {000, 111}` carry weight. This is the
computational heart of Exercise 10.4(3). -/
theorem bitFlipRecovery_apply_encodedCodeState_op (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    (bitFlipRecovery.apply (encodedCodeState a b h).toState).op
      = ((‖a‖ ^ 2 : ℝ) : ℂ) • rankOne ℂ (quditBasis 0).vec (quditBasis 0).vec
        + ((‖b‖ ^ 2 : ℝ) : ℂ) • rankOne ℂ (quditBasis 7).vec (quditBasis 7).vec := by
  rw [bitFlipRecovery_apply_op]
  simp only [encodedCodeState_toState_diag]
  rw [Fin.sum_univ_eight, show recoveryTarget 0 = 0 from by decide,
    show recoveryTarget 7 = 7 from by decide]
  simp only [Fin.reduceEq, reduceIte, add_zero, zero_add, Complex.ofReal_zero, zero_smul]

/-- **The recovered fidelity numerator (squared fidelity) of the encoded logical qubit.** The
expectation of the recovered state in the input `ψ_L = a|000⟩ + b|111⟩` is
`⟨ψ_L|R(ρ)|ψ_L⟩ = ‖a‖⁴ + ‖b‖⁴`. Evaluated from the dephasing form
`R(ρ) = ‖a‖²|000⟩⟨000| + ‖b‖²|111⟩⟨111|`: only the two logical amplitudes survive, each squared. -/
theorem bitFlipRecovery_encodedCodeState_expectation (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    inner ℂ (encodedCodeState a b h).vec
        ((bitFlipRecovery.apply (encodedCodeState a b h).toState).op (encodedCodeState a b h).vec)
      = (((‖a‖ ^ 2) ^ 2 + (‖b‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  have h0 : inner ℂ (encodedCodeState a b h).vec (quditBasis (0 : Fin 8)).vec
      = (starRingEnd ℂ) a := by
    rw [← inner_conj_symm, encodedCodeState_inner_zero]
  have h7 : inner ℂ (encodedCodeState a b h).vec (quditBasis (7 : Fin 8)).vec
      = (starRingEnd ℂ) b := by
    rw [← inner_conj_symm, encodedCodeState_inner_seven]
  rw [bitFlipRecovery_apply_encodedCodeState_op]
  simp only [_root_.add_apply, _root_.smul_apply, rankOne_apply,
    inner_add_right, inner_smul_right, encodedCodeState_inner_zero, encodedCodeState_inner_seven,
    h0, h7]
  rw [mul_comm a, conj_mul_self_ofReal, mul_comm b, conj_mul_self_ofReal]
  push_cast
  ring

end AxQM
