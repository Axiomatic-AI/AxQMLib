/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ThreeQubitBitFlipCode
import AxQM.Postulates.API.QuditMeasurement
import AxQM.Postulates.API.PeriodShift
import AxQM.Postulates.API.ThreeQubitBitFlipRecovery
import AxQM.Postulates.API.FidelityPure

/-!
# Nielsen & Chuang, Exercise 10.4 — the eight-projector syndrome measurement of the bit-flip code

Three qubit bit flip: eight computational-basis projectors; recovery works only for basis states;
min fidelity.

The three qubit bit flip code encodes `a|0⟩ + b|1⟩ ↦ a|000⟩ + b|111⟩`. Its physical register is the
three-qubit space `(ℂ²)^⊗³`, modelled here as `qudit 8` with the computational basis `|x⟩` indexed
by `x : Fin 8` under the big-endian convention `x = 4·b₁ + 2·b₂ + b₃`; the two logical codewords are
`|0_L⟩ = |000⟩ = |0⟩` and `|1_L⟩ = |111⟩ = |7⟩` (`logicalZero`, `logicalOne`). The combinatorics of
the code — the bit-flip error permutations, the majority-vote syndrome, and the recovery — live in
`AxQM/Concrete/ThreeQubitBitFlipCode.lean` (pure `Fin 8` mathematics).

## This file (parts 1–3)

**The eight projectors.** The measurement in question is the computational-basis projective
measurement `quditMeasurement 8`, whose outcome `x : Fin 8` is the rank-one projector `|x⟩⟨x|` — the
eight orthogonal projectors onto the eight computational basis states.

**Diagnosing the syndrome (part 1).** A bit-flip error on the subset of qubits with bitmask `m` is
the computational-basis permutation `quditPerm (xorPerm m)` (`bitFlipError` for a single-qubit error
`errorMask j`), which sends a basis state to a basis state. Measuring the *corrupted* codeword is
therefore deterministic (`bornProb_quditMeasurement_quditBasis`): the outcome is certain to be the
corrupted basis label, and — the content of part (1) — its majority-vote syndrome `syndrome` is
exactly the error `j` that occurred (`bitFlipError_diagnoses_syndrome`). So reading the measurement
result and applying `syndrome` correctly diagnoses "no bit flipped (`j = 0`) or bit number `j`
flipped".

**Recovery works only for basis states (part 2).** The recovery `bitFlipRecovery` measures the eight
projectors and applies the diagnosed correction; its action is the dephasing map
`R(ρ) = ∑ₓ ⟨x|ρ|x⟩ · |t x⟩⟨t x|` (`bitFlipRecovery_apply_op`, in `Postulates/API`). On a *basis*
codeword the recovery is faithful — it returns the codeword `|0_L⟩`, `|1_L⟩`
(`bitFlipRecovery_apply_logicalZero`, `bitFlipRecovery_apply_logicalOne`) — but on a genuine
superposition `a|0_L⟩ + b|1_L⟩` (`a, b ≠ 0`) it does not: the eight-projector measurement erases the
codeword coherence `⟨0_L|·|1_L⟩`, so the recovered state differs from the input
(`bitFlipRecovery_apply_encoded_ne`). Together these say the recovery works *only* for computational
basis states.

**Minimum fidelity (part 3).** Nielsen & Chuang measure error correction by the fidelity
`F(|ψ⟩, ρ) = √⟨ψ|ρ|ψ⟩` (p. 429) with which the protected state survives. Because the recovered
operator is the classical diagonal `R(ρ) = ‖a‖²|000⟩⟨000| + ‖b‖²|111⟩⟨111|`
(`bitFlipRecovery_apply_encodedCodeState_op`, in `Postulates/API`), the squared fidelity is
`F² = ‖a‖⁴ + ‖b‖⁴` (`bitFlipRecovery_fidelity_encodedCodeState_sq`), i.e.
`F = √(‖a‖⁴ + ‖b‖⁴)` (`bitFlipRecovery_fidelity_encodedCodeState`). Minimising over the unit sphere
`‖a‖² + ‖b‖² = 1` gives the exercise's answer: the least fidelity is `1/√2 = √2/2`, attained at the
equal superposition `‖a‖² = ‖b‖² = 1/2` (`threeQubitBitFlip_minFidelity`). This is dramatically
worse than the proper four-projector code (whose minimum fidelity → 1 as the physical error rate
`p → 0`): the eight-projector measurement dephases the codeword *before* any correction, so the
answer `1/√2` holds even with a perfect channel and, since the majority vote fixes every
*correctable* single-qubit error, is independent of `p` (see `threeQubitBitFlip_minFidelity`).

N&C Exercise 10.4 (p. 432); part (3) completes
the item's formalisation (`bitFlipError_diagnoses_syndrome`, `bitFlipRecovery_apply_logicalZero` /
`_logicalOne`, `bitFlipRecovery_apply_encoded_ne`, `threeQubitBitFlip_minFidelity`).
-/

open scoped InnerProductSpace
open AxQM.Concrete

noncomputable section

namespace AxQM

/-- The **logical zero** `|0_L⟩ = |000⟩` of the three qubit bit flip code, the computational-basis
state `|0⟩` of `qudit 8`. -/
def logicalZero : PureState (qudit 8) := quditBasis 0

/-- The **logical one** `|1_L⟩ = |111⟩` of the three qubit bit flip code, the computational-basis
state `|7⟩` of `qudit 8`. -/
def logicalOne : PureState (qudit 8) := quditBasis 7

/-- A **single-qubit bit-flip error** on the three-qubit register, indexed by the syndrome value
`j : Fin 4` it produces: the computational-basis permutation gate
`quditPerm (xorPerm (errorMask j))` that XORs the register by the error's bitmask
(`errorMask 0 = 0` no error; `errorMask j` flips qubit `j` for `j ∈ {1,2,3}`). -/
def bitFlipError (j : Fin 4) : Evolution (qudit 8) := quditPerm (xorPerm (errorMask j))

/-- **Part (1): the eight-projector measurement diagnoses the error syndrome.** Applying a
single-qubit bit-flip error `bitFlipError j` (`j : Fin 4`, `j = 0` = no error) to either logical
codeword `c ∈ {|000⟩, |111⟩}` and then measuring the eight computational-basis projectors is a
*deterministic* measurement: there is a unique outcome `y` that occurs with probability one, and its
majority-vote syndrome `syndrome y` equals `j`. Thus the measurement result, run through `syndrome`,
correctly diagnoses which error occurred — no bit flipped (`j = 0`) or bit number `j` flipped.

The outcome is `y = xorPerm (errorMask j) c`, the corrupted basis label (the bit-flip gate carries
the basis codeword to a basis state, `quditPerm_evolvePure_quditBasis`); the measurement is certain
on a basis state (`bornProb_quditMeasurement_quditBasis`); and `syndrome` reads off the error
(`syndrome_xorPerm_errorMask`). -/
theorem bitFlipError_diagnoses_syndrome (j : Fin 4) (c : Fin 8) (hc : c = 0 ∨ c = 7) :
    ∃ y : Fin 8, syndrome y = j ∧ ∀ x : Fin 8,
      (quditMeasurement 8).bornProb ((bitFlipError j).evolvePure (quditBasis c)).toState x
        = if x = y then 1 else 0 := by
  refine ⟨xorPerm (errorMask j) c, syndrome_xorPerm_errorMask j c hc, fun x => ?_⟩
  rw [bitFlipError, quditPerm_evolvePure_quditBasis, bornProb_quditMeasurement_quditBasis]

/-- **Part (2): the recovery is faithful on the logical zero `|0_L⟩ = |000⟩`.** Applying the
eight-projector recovery `bitFlipRecovery` to the basis codeword `|0_L⟩` returns it unchanged:
measuring `|000⟩` is certain to give outcome `000`, whose syndrome is `0`, so the (trivial)
correction leaves it fixed. A computational basis state is recovered exactly. -/
theorem bitFlipRecovery_apply_logicalZero :
    bitFlipRecovery.apply logicalZero.toState = logicalZero.toState := by
  unfold logicalZero
  rw [bitFlipRecovery_apply_quditBasis, show recoveryTarget 0 = 0 from by decide]

/-- **Part (2): the recovery is faithful on the logical one `|1_L⟩ = |111⟩`.** As for `|0_L⟩`, the
basis codeword `|1_L⟩` is recovered exactly: measuring `|111⟩` gives outcome `111` with certainty,
syndrome `0`, and the correction leaves it fixed. -/
theorem bitFlipRecovery_apply_logicalOne :
    bitFlipRecovery.apply logicalOne.toState = logicalOne.toState := by
  unfold logicalOne
  rw [bitFlipRecovery_apply_quditBasis, show recoveryTarget 7 = 7 from by decide]

/-- **Part (2): the recovery destroys a genuine code superposition.** For an encoded logical qubit
`a|0_L⟩ + b|1_L⟩` with *both* amplitudes nonzero, the eight-projector recovery does **not** return
the input state: `bitFlipRecovery.apply ρ ≠ ρ`. The eight rank-one projectors collapse the
superposition and erase its codeword coherence — the recovered state has `⟨0_L|R(ρ)|1_L⟩ = 0`
(`bitFlipRecovery_apply_inner_logical`) whereas the input has `⟨0_L|ρ|1_L⟩ = b̄·a ≠ 0`
(`encodedCodeState_toState_inner`). Combined with `bitFlipRecovery_apply_logicalZero` /
`bitFlipRecovery_apply_logicalOne`, this is the exercise's conclusion: the recovery procedure works
*only* for computational basis states. -/
theorem bitFlipRecovery_apply_encoded_ne (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    bitFlipRecovery.apply (encodedCodeState a b h).toState ≠ (encodedCodeState a b h).toState := by
  intro heq
  have key : inner ℂ (quditBasis (0 : Fin 8)).vec
        ((bitFlipRecovery.apply (encodedCodeState a b h).toState).op (quditBasis 7).vec)
      = inner ℂ (quditBasis (0 : Fin 8)).vec
        ((encodedCodeState a b h).toState.op (quditBasis 7).vec) := by rw [heq]
  rw [bitFlipRecovery_apply_inner_logical, encodedCodeState_toState_inner] at key
  rcases mul_eq_zero.mp key.symm with h1 | h2
  · rw [starRingEnd_apply, star_eq_zero] at h1
    exact hb h1
  · exact ha h2

/-- **Part (3): the squared fidelity of the eight-projector error-correction procedure.** Feeding
the encoded logical qubit `ψ_L = a|0_L⟩ + b|1_L⟩` through the procedure (measure the eight
computational-basis projectors, then apply the majority-vote correction — `bitFlipRecovery`) yields
a recovered state whose fidelity with the input `ψ_L` satisfies `F(ψ_L, R(ρ))² = ‖a‖⁴ + ‖b‖⁴`. This
is Nielsen & Chuang's fidelity `F(|ψ⟩, ρ) = √⟨ψ|ρ|ψ⟩`; the identity follows from the
squared-fidelity formula `State.fidelity_toState_sq` (`F² = ⟨ψ_L|R(ρ)|ψ_L⟩`) with the dephasing
computation `bitFlipRecovery_encodedCodeState_expectation`. -/
theorem bitFlipRecovery_fidelity_encodedCodeState_sq (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ((encodedCodeState a b h).toState.fidelity
        (bitFlipRecovery.apply (encodedCodeState a b h).toState)) ^ 2 = ‖a‖ ^ 4 + ‖b‖ ^ 4 := by
  rw [State.fidelity_toState_sq, bitFlipRecovery_encodedCodeState_expectation]
  rw [show RCLike.re (((‖a‖ ^ 2) ^ 2 + (‖b‖ ^ 2) ^ 2 : ℝ) : ℂ) = (‖a‖ ^ 2) ^ 2 + (‖b‖ ^ 2) ^ 2 from
    Complex.ofReal_re _]
  ring

/-- **Part (3): the fidelity in closed form**, `F(ψ_L, R(ρ)) = √(‖a‖⁴ + ‖b‖⁴)`, the nonnegative
square root of `bitFlipRecovery_fidelity_encodedCodeState_sq`. Its minimum over the unit sphere
`‖a‖² + ‖b‖² = 1` is the exercise's answer (`threeQubitBitFlip_minFidelity`). -/
theorem bitFlipRecovery_fidelity_encodedCodeState (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    (encodedCodeState a b h).toState.fidelity
        (bitFlipRecovery.apply (encodedCodeState a b h).toState)
      = Real.sqrt (‖a‖ ^ 4 + ‖b‖ ^ 4) := by
  rw [← bitFlipRecovery_fidelity_encodedCodeState_sq a b h,
    Real.sqrt_sq (State.fidelity_nonneg _ _)]

/-- **Part (3): the minimum fidelity for the error-correction procedure is `1/√2`.** Over all
encoded logical qubits `ψ_L = a|0_L⟩ + b|1_L⟩` (`‖a‖² + ‖b‖² = 1`), the least fidelity the
eight-projector error-correction procedure achieves is `1/√2 = √2/2`, attained at the equal
superposition `‖a‖² = ‖b‖² = 1/2`.

The fidelity is `√(‖a‖⁴ + ‖b‖⁴)` (`bitFlipRecovery_fidelity_encodedCodeState`); with
`‖a‖² + ‖b‖² = 1` one has `‖a‖⁴ + ‖b‖⁴ = 1 - 2‖a‖²‖b‖² ≥ 1/2` (AM–GM, `sq_nonneg`), with equality
exactly when `‖a‖² = ‖b‖²`. Hence `F ≥ √(1/2) = √2/2`, and `a = b = 1/√2` attains it.

**Why this is the minimum fidelity of the procedure, and why it is `1/√2` regardless of the
channel.** Unlike the four-projector syndrome measurement (whose recovery leaves a code
superposition intact, so its minimum fidelity → 1 as the physical error rate `p → 0`), the
eight-projector measurement collapses the superposition *before* any correction, destroying the
codeword coherence (`bitFlipRecovery_apply_encoded_ne`). Two facts make `1/√2` the exact worst-case
fidelity of the full procedure, independent of `p`: (i) at the equal superposition the recovered
diagonal state `‖a‖²|000⟩⟨000| + ‖b‖²|111⟩⟨111|` has fidelity `1/√2` with the input; and (ii) every
*correctable* single-qubit bit-flip carries `ψ_L` to another basis-pair superposition whose recovery
is the same diagonal state (the majority vote fixes the error), so no correctable error changes the
fidelity. Thus the noiseless recovery here already realises the worst case, and the answer is the
`p`-independent `1/√2`. -/
theorem threeQubitBitFlip_minFidelity :
    IsLeast {F : ℝ | ∃ (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1),
        (encodedCodeState a b h).toState.fidelity
          (bitFlipRecovery.apply (encodedCodeState a b h).toState) = F} (Real.sqrt 2 / 2) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hnorm : ‖((Real.sqrt 2 / 2 : ℝ) : ℂ)‖ = Real.sqrt 2 / 2 :=
    Complex.norm_of_nonneg (by positivity)
  have hc2 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by rw [div_pow, Real.sq_sqrt h2]; norm_num
  have hsqrt : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
    rw [← hc2, Real.sqrt_sq (by positivity)]
  constructor
  · refine ⟨((Real.sqrt 2 / 2 : ℝ) : ℂ), ((Real.sqrt 2 / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [hnorm, hc2]; norm_num
    · have h4 : (Real.sqrt 2 / 2) ^ 4 + (Real.sqrt 2 / 2) ^ 4 = 1 / 2 := by nlinarith [hc2]
      rw [bitFlipRecovery_fidelity_encodedCodeState, hnorm, h4, hsqrt]
  · rintro F ⟨a, b, h, rfl⟩
    rw [bitFlipRecovery_fidelity_encodedCodeState, ← hsqrt]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (‖a‖ ^ 2 - ‖b‖ ^ 2), h]

end AxQM
