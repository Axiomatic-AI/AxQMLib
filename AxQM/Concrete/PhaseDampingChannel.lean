/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QubitBasisOperators
import ToMathlib.Analysis.InnerProductSpace.AdjointAntilinear
import Mathlib.Analysis.SpecialFunctions.Sqrt
import ToMathlib.LinearAlgebra.UnitaryGroup
import ToMathlib.LinearAlgebra.Matrix.Hermitian
import ToMathlib.LinearAlgebra.Matrix.HermitianUnitary

/-!
# Concrete: phase damping and its unitary freedom (N&C §8.3.6, Exercise 8.27)

This file defines, at the level of raw
operators on an arbitrary two-dimensional complex inner product space (a qubit) with a chosen
computational orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`, the **phase-damping** operation
elements of Nielsen & Chuang, *Quantum Computation and Quantum Information*, §8.3.6, and proves the
content of **Exercise 8.27**: the two operator-sum representations of phase damping are related by
an explicit unitary mixing.

## The exercise

Phase damping (loss of quantum phase without loss of energy) has, with damping parameter `λ`, the
operation elements (N&C eqs. 8.127–8.128)

`E₀ = diag(1, √(1-λ)) = P₀ + √(1-λ) P₁`,   `E₁ = diag(0, √λ) = √λ P₁`.

Applying the unitary freedom of quantum operations (N&C Theorem 8.2), a unitary recombination gives
a second set (N&C eqs. 8.129–8.130)

`Ẽ₀ = √α · I`,   `Ẽ₁ = √(1-α) · Z`   with `Z = diag(1,-1) = P₀ - P₁`,   `α = (1 + √(1-λ))/2`,

exhibiting phase damping as **exactly the phase-flip channel** (`Ẽ₀`/`Ẽ₁` do nothing / apply Pauli
`Z` with probabilities `α` / `1-α`). **Exercise 8.27** asks for the unitary `u` with
`Ẽₖ = Σⱼ uₖⱼ Eⱼ`.
The answer is the real, symmetric, orthogonal `2 × 2` matrix

`u = !![√α, √(1-α); √(1-α), -√α]`   (`phaseDampMixingUnitary`),

and the two facts `phaseDamp_unitaryFreedom` (`Ẽₖ = Σⱼ uₖⱼ Eⱼ`) and
`phaseDampMixingUnitary_mem_unitaryGroup` (`u` is unitary) together *are* the exercise: by
Theorem 8.2 they certify that `{E₀,E₁}` and `{Ẽ₀,Ẽ₁}` are two operator-sum representations of one
and the same quantum operation.

The two nonlinear scalar inputs are `√(1-α) √λ = √α (1 - √(1-λ))` and `√α √λ = √(1-α)(1 + √(1-λ))`
(proved by squaring, using `α = (1+√(1-λ))/2`); both, and the unitarity of `u`, need `0 ≤ λ ≤ 1`,
exactly N&C's physical range for the scattering probability.

## Setting

Everything is stated for bare `LinearMap`s on an inner product space, an
`OrthonormalBasis`, and the index-mixing matrix `Matrix.unitaryGroup`, over a *general* qubit `H`.
Compare the amplitude-damping development (`AxQM/Concrete/AmplitudeDampingChannel.lean`) and
Theorem 8.2 itself (whose mathematical core is in `ToMathlib/`). The statement of Exercise 8.27
is in `AxQM/NC/Ch8/Exercise8_27.lean`.

## Contents

* `phaseDampKrausZero b λ`, `phaseDampKrausOne b λ` — the operation elements `E₀`, `E₁`
  (eqs. 8.127–8.128), and the family `phaseDampKraus b λ = ![E₀, E₁]`.
* `phaseFlipProb λ = (1 + √(1-λ))/2` — the phase-flip "no-error" probability `α`, with
  `phaseFlipProb_nonneg`, `phaseFlipProb_le_one`, `one_sub_phaseFlipProb_nonneg`.
* `phaseDampKrausZeroTilde λ = √α · I`, `phaseDampKrausOneTilde b λ = √(1-α)(P₀ - P₁)` — the
  recombined elements `Ẽ₀`, `Ẽ₁` (eqs. 8.129–8.130), and the family `phaseDampKrausTilde b λ`.
* `phaseDampMixingUnitary λ` — the relating matrix `u` (**the answer to Exercise 8.27**), with
  `phaseDampMixingUnitary_isHermitian`, `phaseDampMixingUnitary_mul_self`
  (`u² = I`) and `phaseDampMixingUnitary_mem_unitaryGroup` (`u` is unitary, `0 ≤ λ ≤ 1`).
* `phaseDamp_unitaryFreedom` — **Exercise 8.27**: `Ẽₖ = Σⱼ uₖⱼ Eⱼ` for `k = 0, 1` (`0 ≤ λ ≤ 1`).
* `adjoint_phaseDampKrausZero`, `adjoint_phaseDampKrausOne` — both operation elements are
  self-adjoint (`E₀† = E₀`, `E₁† = E₁`; diagonal operators), and `phaseDampChannel λ ρ =
  E₀ ρ E₀† + E₁ ρ E₁†` — the phase-damping channel action (analogue of `ampDampChannel`), reused by
  the unitality development of Exercise 8.29 (`Concrete/ChannelUnitality.lean`).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **first phase-damping operation element** `E₀ = diag(1, √(1-λ)) = P₀ + √(1-λ) P₁`
(N&C eq. 8.127): it leaves `|0⟩` unchanged and shrinks the `|1⟩` amplitude by `√(1-λ)`, where
`λ = 1 - cos²(χΔt)` is the probability a photon of the system was scattered. -/
noncomputable def phaseDampKrausZero (lam : ℝ) : H →ₗ[ℂ] H :=
  qubitProj b 0 + (Real.sqrt (1 - lam) : ℂ) • qubitProj b 1

/-- The **second phase-damping operation element** `E₁ = diag(0, √λ) = √λ P₁` (N&C eq. 8.128):
unlike amplitude damping it destroys `|0⟩` and shrinks (does not flip) the `|1⟩` amplitude — no
energy is exchanged, only phase information is lost. -/
noncomputable def phaseDampKrausOne (lam : ℝ) : H →ₗ[ℂ] H :=
  (Real.sqrt lam : ℂ) • qubitProj b 1

/-- The phase-damping operation elements as an indexed family `![E₀, E₁]` (N&C eqs. 8.127–8.128),
the form in which the unitary-freedom relation `Ẽₖ = Σⱼ uₖⱼ Eⱼ` sums over `j`. -/
noncomputable def phaseDampKraus (lam : ℝ) : Fin 2 → (H →ₗ[ℂ] H) :=
  ![phaseDampKrausZero b lam, phaseDampKrausOne b lam]

/-- The phase-flip **"no-error" probability** `α = (1 + √(1-λ))/2` (N&C eqs. 8.129–8.130): in the
phase-flip picture of phase damping, nothing happens to the qubit with probability `α` and the Pauli
`Z` is applied with probability `1-α`. -/
noncomputable def phaseFlipProb (lam : ℝ) : ℝ := (1 + Real.sqrt (1 - lam)) / 2

/-- `α ≥ 0` (a probability): `α = (1 + √(1-λ))/2` and `√(1-λ) ≥ 0`. -/
theorem phaseFlipProb_nonneg (lam : ℝ) : 0 ≤ phaseFlipProb lam := by
  unfold phaseFlipProb; positivity

/-- `α ≤ 1` (a probability), for `0 ≤ λ`: then `√(1-λ) ≤ 1`, so `(1 + √(1-λ))/2 ≤ 1`. -/
theorem phaseFlipProb_le_one {lam : ℝ} (h0 : 0 ≤ lam) : phaseFlipProb lam ≤ 1 := by
  have h : Real.sqrt (1 - lam) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_one] at h
  unfold phaseFlipProb; linarith

/-- `1 - α ≥ 0` (the complementary probability), for `0 ≤ λ`. -/
theorem one_sub_phaseFlipProb_nonneg {lam : ℝ} (h0 : 0 ≤ lam) : 0 ≤ 1 - phaseFlipProb lam := by
  linarith [phaseFlipProb_le_one h0]

/-- The **first recombined operation element** `Ẽ₀ = √α · I` (N&C eq. 8.129): with probability `α`,
phase damping leaves the qubit untouched. -/
noncomputable def phaseDampKrausZeroTilde (lam : ℝ) : H →ₗ[ℂ] H :=
  (Real.sqrt (phaseFlipProb lam) : ℂ) • LinearMap.id

/-- The **second recombined operation element** `Ẽ₁ = √(1-α) · Z = √(1-α)(P₀ - P₁)`
(N&C eq. 8.130): with probability `1-α`, phase damping applies the Pauli `Z` (a phase flip). -/
noncomputable def phaseDampKrausOneTilde (lam : ℝ) : H →ₗ[ℂ] H :=
  (Real.sqrt (1 - phaseFlipProb lam) : ℂ) • (qubitProj b 0 - qubitProj b 1)

/-- The recombined phase-flip operation elements as an indexed family `![Ẽ₀, Ẽ₁]`
(N&C eqs. 8.129–8.130). -/
noncomputable def phaseDampKrausTilde (lam : ℝ) : Fin 2 → (H →ₗ[ℂ] H) :=
  ![phaseDampKrausZeroTilde lam, phaseDampKrausOneTilde b lam]

/-- **The answer to Exercise 8.27**: the `2 × 2` unitary `u = !![√α, √(1-α); √(1-α), -√α]` relating
the two sets of phase-damping operation elements via `Ẽₖ = Σⱼ uₖⱼ Eⱼ` (`α = phaseFlipProb λ`). It is
real, symmetric and orthogonal — a reflection. Note `u` mixes the *index* `{0,1}` of the operation
elements, hence is a `Matrix (Fin 2) (Fin 2) ℂ`, not an operator on the qubit. -/
noncomputable def phaseDampMixingUnitary (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt (phaseFlipProb lam) : ℂ), (Real.sqrt (1 - phaseFlipProb lam) : ℂ);
     (Real.sqrt (1 - phaseFlipProb lam) : ℂ), -(Real.sqrt (phaseFlipProb lam) : ℂ)]

/-- `u` is Hermitian (`uᴴ = u`): its entries `√α, √(1-α), √(1-α), -√α` are real, and it is
symmetric. -/
theorem phaseDampMixingUnitary_isHermitian (lam : ℝ) :
    Matrix.IsHermitian (phaseDampMixingUnitary lam) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseDampMixingUnitary, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-- `u² = I` (`0 ≤ λ`): the off-diagonal entries cancel, and each diagonal entry is
`(√α)² + (√(1-α))² = α + (1-α) = 1` — `u` is an involution (a reflection). Only `0 ≤ λ` is needed
(so that `1 - α ≥ 0` and `(√(1-α))² = 1-α`); `α ≥ 0` is automatic. -/
theorem phaseDampMixingUnitary_mul_self {lam : ℝ} (h0 : 0 ≤ lam) :
    phaseDampMixingUnitary lam * phaseDampMixingUnitary lam = 1 := by
  have hαsq : (Real.sqrt (phaseFlipProb lam) : ℂ) * (Real.sqrt (phaseFlipProb lam) : ℂ)
      = (phaseFlipProb lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (phaseFlipProb_nonneg lam)]
  have h1αsq : (Real.sqrt (1 - phaseFlipProb lam) : ℂ) * (Real.sqrt (1 - phaseFlipProb lam) : ℂ)
      = 1 - (phaseFlipProb lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (one_sub_phaseFlipProb_nonneg h0)]; push_cast; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [phaseDampMixingUnitary, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.one_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true, Matrix.one_apply_ne]
  · linear_combination hαsq + h1αsq
  · ring
  · ring
  · linear_combination h1αsq + hαsq

/-- `u ∈ unitaryGroup` (`0 ≤ λ`): from Hermiticity (`uᴴ = u`) and the involution `u² = I`,
so `uᴴ u = u² = I`. This is the "unitary" half of Exercise 8.27. -/
theorem phaseDampMixingUnitary_mem_unitaryGroup {lam : ℝ} (h0 : 0 ≤ lam) :
    phaseDampMixingUnitary lam ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (phaseDampMixingUnitary_isHermitian lam).mem_unitaryGroup
    (phaseDampMixingUnitary_mul_self h0)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **Exercise 8.27**: the recombined phase-flip operation elements are the unitary mixing
`Ẽₖ = Σⱼ uₖⱼ Eⱼ` of the phase-damping operation elements, for `k = 0, 1` and `0 ≤ λ ≤ 1`. Together
with `phaseDampMixingUnitary_mem_unitaryGroup` this exhibits `u = !![√α, √(1-α); √(1-α), -√α]` as
the unitary demanded by the exercise; by N&C Theorem 8.2 it certifies `{Eₖ}` and `{Ẽₖ}` as two
operator-sum representations of one quantum operation (phase damping = the phase-flip channel).

The `k = 0` row reduces to the coefficient identity `√α √(1-λ) + √(1-α) √λ = √α` (i.e.
`√(1-α) √λ = √α(1 - √(1-λ))`); the `k = 1` row to `√(1-α) √(1-λ) - √α √λ = -√(1-α)` (i.e.
`√α √λ = √(1-α)(1 + √(1-λ))`); both hold by squaring, using `α = (1 + √(1-λ))/2`. -/
theorem phaseDamp_unitaryFreedom {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (k : Fin 2) :
    phaseDampKrausTilde b lam k
      = ∑ j, phaseDampMixingUnitary lam k j • phaseDampKraus b lam j := by
  have hα_nonneg : 0 ≤ phaseFlipProb lam := phaseFlipProb_nonneg lam
  have h1α_nonneg : 0 ≤ 1 - phaseFlipProb lam := one_sub_phaseFlipProb_nonneg h0
  have hs_le : Real.sqrt (1 - lam) ≤ 1 := by
    have h : Real.sqrt (1 - lam) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at h
  have hs2 : Real.sqrt (1 - lam) ^ 2 = 1 - lam := Real.sq_sqrt (by linarith)
  -- Identity (I): √(1-α) √λ = √α (1 - √(1-λ)).
  have hI : (Real.sqrt (1 - phaseFlipProb lam) : ℂ) * (Real.sqrt lam : ℂ)
      = (Real.sqrt (phaseFlipProb lam) : ℂ) * (1 - (Real.sqrt (1 - lam) : ℂ)) := by
    have hreal : Real.sqrt (1 - phaseFlipProb lam) * Real.sqrt lam
        = Real.sqrt (phaseFlipProb lam) * (1 - Real.sqrt (1 - lam)) := by
      rw [← Real.sqrt_mul h1α_nonneg,
        show (1 - Real.sqrt (1 - lam)) = Real.sqrt ((1 - Real.sqrt (1 - lam)) ^ 2) from
          (Real.sqrt_sq (by linarith)).symm, ← Real.sqrt_mul hα_nonneg]
      congr 1; unfold phaseFlipProb; nlinarith [hs2]
    exact_mod_cast hreal
  -- Identity (II): √α √λ = √(1-α)(1 + √(1-λ)).
  have hII : (Real.sqrt (phaseFlipProb lam) : ℂ) * (Real.sqrt lam : ℂ)
      = (Real.sqrt (1 - phaseFlipProb lam) : ℂ) * (1 + (Real.sqrt (1 - lam) : ℂ)) := by
    have hreal : Real.sqrt (phaseFlipProb lam) * Real.sqrt lam
        = Real.sqrt (1 - phaseFlipProb lam) * (1 + Real.sqrt (1 - lam)) := by
      rw [← Real.sqrt_mul hα_nonneg,
        show (1 + Real.sqrt (1 - lam)) = Real.sqrt ((1 + Real.sqrt (1 - lam)) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm, ← Real.sqrt_mul h1α_nonneg]
      congr 1; unfold phaseFlipProb; nlinarith [hs2]
    exact_mod_cast hreal
  fin_cases k
  · -- k = 0: √α • id = √α • E₀ + √(1-α) • E₁
    simp only [phaseDampKrausTilde, phaseDampKraus, phaseDampMixingUnitary,
      phaseDampKrausZeroTilde, phaseDampKrausZero, phaseDampKrausOne, Fin.sum_univ_two,
      Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    rw [← sum_qubitProj b]
    simp only [smul_add, smul_smul]
    rw [hI]; module
  · -- k = 1: √(1-α) • (P₀ - P₁) = √(1-α) • E₀ + (-√α) • E₁
    simp only [phaseDampKrausTilde, phaseDampKraus, phaseDampMixingUnitary,
      phaseDampKrausOneTilde, phaseDampKrausZero, phaseDampKrausOne, Fin.sum_univ_two,
      Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    simp only [smul_sub, smul_add, smul_smul]
    rw [neg_mul, hII]; module

/-- `E₀` is self-adjoint: `E₀† = E₀`. The real-diagonal operator `E₀ = diag(1, √(1-λ)) =
P₀ + √(1-λ) P₁` is a real combination of the self-adjoint projectors `P₀`, `P₁` (`√(1-λ)` is
conjugation-fixed). -/
@[simp] theorem adjoint_phaseDampKrausZero (lam : ℝ) :
    LinearMap.adjoint (phaseDampKrausZero b lam) = phaseDampKrausZero b lam := by
  rw [phaseDampKrausZero, map_add, LinearMap.adjoint_smul, adjoint_qubitProj, adjoint_qubitProj]
  simp only [RCLike.star_def, Complex.conj_ofReal]

/-- `E₁` is self-adjoint: `E₁† = E₁`. The operator `E₁ = diag(0, √λ) = √λ P₁` is a real multiple of
the self-adjoint projector `P₁`. -/
@[simp] theorem adjoint_phaseDampKrausOne (lam : ℝ) :
    LinearMap.adjoint (phaseDampKrausOne b lam) = phaseDampKrausOne b lam := by
  rw [phaseDampKrausOne, LinearMap.adjoint_smul, adjoint_qubitProj]
  simp only [RCLike.star_def, Complex.conj_ofReal]

/-- The **phase-damping channel** `E_PD(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` (N&C §8.3.6): the quantum
operation with operation elements `E₀ = diag(1, √(1-λ))` and `E₁ = diag(0, √λ)` (eqs. 8.127–8.128).
The phase-damping analogue of `ampDampChannel` (`Concrete/AmplitudeDampingChannel.lean`); unlike
amplitude damping it exchanges no energy — both operation elements are diagonal, hence self-adjoint
(`adjoint_phaseDampKrausZero`, `adjoint_phaseDampKrausOne`) — losing only phase coherence. -/
noncomputable def phaseDampChannel (lam : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  phaseDampKrausZero b lam ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampKrausZero b lam)
    + phaseDampKrausOne b lam ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampKrausOne b lam)

end AxQM.Concrete

end
