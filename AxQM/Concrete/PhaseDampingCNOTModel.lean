/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ControlledFlipConjugation
import AxQM.Concrete.PhaseDampingChannel
import ToMathlib.Analysis.InnerProductSpace.Trace
import ToMathlib.Analysis.InnerProductSpace.AdjointAntilinear

/-!
# Concrete: a single CNOT with a mixed environment models phase damping (N&C Exercise 8.28)

This file works, at the level of raw
operators on an arbitrary two-dimensional complex inner product space `H` (a qubit) with a chosen
computational orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`, through Nielsen & Chuang,
*Quantum Computation and Quantum Information*, **Exercise 8.28** (p. 386):

Show a single CNOT with mixed environment state models phase damping.

## The construction

The gate is the **controlled-flip** `U = P₀ ⊗ I + P₁ ⊗ X` of N&C eq. 8.16 — the CNOT with the
**system** (left qubit) controlling a bit-flip of the **environment** (right qubit) — already
defined and proved unitary as `AxQM.Concrete.controlledFlip` (Exercise 8.4). Instead of a
pure `|0⟩` environment (which gives the completely dephasing channel, Exercise 8.4), the environment
is prepared in the **mixed** state, in the `±` basis,

`σ_p = (1-p) |+⟩⟨+| + p |-⟩⟨-|`   (`phaseDampEnv`),

a genuine density operator (`trace σ_p = 1`, `trace_phaseDampEnv`) that is `|+⟩` with probability
`1-p` and `|-⟩` with probability `p`. The induced quantum operation on the system is obtained by
applying `U` and tracing out the environment,

`E_p(ρ) = tr_env(U (ρ ⊗ σ_p) U†)`   (`phaseDampCNOTChannel`).

## The result

The two `±`-basis conjugation facts of `Concrete/ControlledFlipConjugation.lean` (Exercise 8.28,
part 1) say the CNOT is invisible on a `|+⟩` environment and kicks back a Pauli `Z` on a `|-⟩` one:
`U(ρ⊗P₊)U† = ρ⊗P₊` and `U(ρ⊗P₋)U† = (ZρZ)⊗P₋`. Averaging over the mixture and tracing out (each
`|±⟩` projector has unit trace) therefore gives the **phase-flip channel**

`E_p(ρ) = (1-p) ρ + p Z ρ Z`   (`phaseDampCNOTChannel_eq_phaseFlipChannel`),

nothing happening with probability `1-p` and a Pauli `Z` (a phase flip) applied with probability
`p`. This is *exactly* the phase-flip = phase-damping channel of N&C §8.3.5: writing it in
operator-sum form recovers the recombined operation elements `Ẽ₀ = √(1-p) I`, `Ẽ₁ = √p Z` of N&C
eqs. 8.129–8.130 (`phaseFlipChannel_eq_operatorSum`, parameterized by the flip probability `p`, so
the no-error probability is `α = 1-p`), and specializing the mixture weight to `p = 1 - α(λ)` with
the phase-flip "no-error" probability `α(λ) = (1+√(1-λ))/2 = phaseFlipProb λ` recovers the
library's phase-damping operation elements `phaseDampKrausTilde b λ` verbatim
(`phaseDampCNOTChannel_eq_phaseDampKrausTilde`). Thus a *single* CNOT with a mixed environment
models phase damping, and — as the exercise stresses — **the amount of damping is set by the
mixture probability `p`** (the weight of the `|-⟩` component that triggers the phase flip):
`p = 1 - α(λ)` realizes phase damping of parameter `λ`, with `p = 0` (pure `|+⟩`) the identity and
larger `p` stronger damping.

## Setting

Everything is stated for bare `LinearMap`s on an inner product space,
`TensorProduct.map`, the abstract partial trace of
`ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract`, an `OrthonormalBasis`. The reduced
dynamics `tr_env(U(ρ⊗σ)U†)` is expressed directly with these. Compare the phase-damping circuit
(Exercise 8.26) and the controlled-flip gate it reuses (Exercises 8.4 / 8.28 part 1). The
statement of Exercise 8.28 is in `AxQM/NC/Ch8/Exercise8_28.lean`.
-/

open scoped TensorProduct InnerProductSpace

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

variable (b : OrthonormalBasis (Fin 2) ℂ H)

/-! ### Traces of the basic qubit operators -/

omit [CompleteSpace H] in
/-- Each computational-basis projector has unit trace: `tr Pᵢ = ⟨i|i⟩ = 1`
(`trace_rankOne` + orthonormality). -/
theorem trace_qubitProj (i : Fin 2) : (LinearMap.trace ℂ H) (qubitProj b i) = 1 := by
  rw [qubitProj, InnerProductSpace.trace_rankOne, b.inner_eq_ite]
  simp

omit [CompleteSpace H] in
/-- The bit-flip is traceless: `tr X = ⟨1|0⟩ + ⟨0|1⟩ = 0` (its diagonal entries vanish). -/
theorem trace_qubitFlip : (LinearMap.trace ℂ H) (qubitFlip b) = 0 := by
  rw [qubitFlip, map_add, InnerProductSpace.trace_rankOne, InnerProductSpace.trace_rankOne,
    b.inner_eq_ite, b.inner_eq_ite]
  simp

omit [CompleteSpace H] in
/-- The `|+⟩⟨+|` projector is a density operator: `tr P₊ = ½(tr I + tr X) = ½((1+1) + 0) = 1`,
using `tr I = tr P₀ + tr P₁` (`sum_qubitProj`). -/
theorem trace_qubitPlusProj : (LinearMap.trace ℂ H) (qubitPlusProj b) = 1 := by
  rw [qubitPlusProj, map_smul, map_add, trace_qubitFlip, ← sum_qubitProj b, map_add,
    trace_qubitProj, trace_qubitProj]
  norm_num [smul_eq_mul]

omit [CompleteSpace H] in
/-- The `|-⟩⟨-|` projector is a density operator: `tr P₋ = ½(tr I - tr X) = ½((1+1) - 0) = 1`. -/
theorem trace_qubitMinusProj : (LinearMap.trace ℂ H) (qubitMinusProj b) = 1 := by
  rw [qubitMinusProj, map_smul, map_sub, trace_qubitFlip, ← sum_qubitProj b, map_add,
    trace_qubitProj, trace_qubitProj]
  norm_num [smul_eq_mul]

/-! ### The mixed environment state and the single-CNOT channel -/

/-- The **mixed environment state** `σ_p = (1-p) |+⟩⟨+| + p |-⟩⟨-|` (N&C Exercise 8.28): the
environment enters the `±` basis as `|+⟩` with probability `1-p` and `|-⟩` with probability `p`.
Written with the `½(I ± X)` projectors `qubitPlusProj`/`qubitMinusProj`, so it is manifestly a
density operator (`trace_phaseDampEnv`). -/
noncomputable def phaseDampEnv (p : ℝ) : H →ₗ[ℂ] H :=
  (1 - (p : ℂ)) • qubitPlusProj b + (p : ℂ) • qubitMinusProj b

omit [CompleteSpace H] in
/-- The mixed environment `σ_p` is a valid state: `tr σ_p = (1-p) · 1 + p · 1 = 1`. -/
theorem trace_phaseDampEnv (p : ℝ) : (LinearMap.trace ℂ H) (phaseDampEnv b p) = 1 := by
  rw [phaseDampEnv, map_add, map_smul, map_smul, trace_qubitPlusProj, trace_qubitMinusProj]
  simp only [smul_eq_mul, mul_one]
  ring

/-- The **single-CNOT phase-damping model** `E_p(ρ) = tr_env(U (ρ ⊗ σ_p) U†)` (N&C Exercise 8.28):
prepare the environment in the mixed state `σ_p = phaseDampEnv b p`, apply the controlled-flip
`U = controlledFlip b`, and discard the environment. -/
noncomputable def phaseDampCNOTChannel (p : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b
    (controlledFlip b ∘ₗ TensorProduct.map ρ (phaseDampEnv b p)
      ∘ₗ LinearMap.adjoint (controlledFlip b))

/-- The **phase-flip channel** `E(ρ) = (1-p) ρ + p Z ρ Z` (N&C §8.3.3/§8.3.5): with probability
`1-p` nothing happens, and with probability `p` the Pauli `Z` (a phase flip) is applied. -/
noncomputable def phaseFlipChannel (p : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  (1 - (p : ℂ)) • ρ + (p : ℂ) • (qubitPauliZ b ∘ₗ ρ ∘ₗ qubitPauliZ b)

/-! ### The exercise: the single-CNOT model is the phase-flip = phase-damping channel -/

/-- **Exercise 8.28.** The single controlled-`NOT` gate with the mixed environment `σ_p` models the
**phase-flip channel** `E_p(ρ) = (1-p) ρ + p Z ρ Z`:
`tr_env(U (ρ ⊗ σ_p) U†) = (1-p) ρ + p Z ρ Z`.

The `|+⟩` component of the mixture passes through untouched (`controlledFlip_conj_plusProj`) and the
`|-⟩` component kicks back a Pauli `Z` on the system (`controlledFlip_conj_minusProj`); tracing out
the unit-trace `|±⟩` projectors (`partialTraceRight_tensorMap`, `trace_qubitPlusProj`,
`trace_qubitMinusProj`) then averages the two into the phase flip. -/
theorem phaseDampCNOTChannel_eq_phaseFlipChannel (p : ℝ) (ρ : H →ₗ[ℂ] H) :
    phaseDampCNOTChannel b p ρ = phaseFlipChannel b p ρ := by
  rw [phaseDampCNOTChannel, phaseDampEnv, TensorProduct.map_add_right,
    TensorProduct.map_smul_right, TensorProduct.map_smul_right, LinearMap.add_comp,
    LinearMap.smul_comp, LinearMap.smul_comp, LinearMap.comp_add, LinearMap.comp_smul,
    LinearMap.comp_smul, controlledFlip_conj_plusProj, controlledFlip_conj_minusProj,
    ← LinearMap.partialTraceRightLM_apply, map_add, map_smul, map_smul,
    LinearMap.partialTraceRightLM_apply, LinearMap.partialTraceRightLM_apply,
    LinearMap.partialTraceRight_tensorMap, LinearMap.partialTraceRight_tensorMap,
    trace_qubitPlusProj, trace_qubitMinusProj, phaseFlipChannel]
  simp only [one_smul]

/-! ### Operator-sum form: the phase-damping operation elements `Ẽ₀ = √(1-p) I`, `Ẽ₁ = √p Z` -/

/-- The phase-flip channel in **operator-sum form** with the recombined phase-damping operation
elements `Ẽ₀ = √(1-p) I`, `Ẽ₁ = √p Z` of N&C eqs. 8.129–8.130 (here parameterized by the phase-flip
probability `p`, so the no-error probability is `α = 1-p`):
`(1-p) ρ + p Z ρ Z = Ẽ₀ ρ Ẽ₀† + Ẽ₁ ρ Ẽ₁†`. Needs `0 ≤ p ≤ 1` so `(√(1-p))² = 1-p`, `(√p)² = p`;
since `I` and `Z` are self-adjoint and `√` is real, `Ẽ₀ ρ Ẽ₀† = (1-p) ρ` and
`Ẽ₁ ρ Ẽ₁† = p Z ρ Z`. -/
theorem phaseFlipChannel_eq_operatorSum {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : H →ₗ[ℂ] H) :
    phaseFlipChannel b p ρ =
      ((Real.sqrt (1 - p) : ℂ) • LinearMap.id) ∘ₗ ρ
          ∘ₗ LinearMap.adjoint ((Real.sqrt (1 - p) : ℂ) • LinearMap.id)
        + ((Real.sqrt p : ℂ) • qubitPauliZ b) ∘ₗ ρ
          ∘ₗ LinearMap.adjoint ((Real.sqrt p : ℂ) • qubitPauliZ b) := by
  have e0 : LinearMap.adjoint ((Real.sqrt (1 - p) : ℂ) • (LinearMap.id : H →ₗ[ℂ] H))
      = (Real.sqrt (1 - p) : ℂ) • LinearMap.id := by
    rw [LinearMap.adjoint_smul, ← starRingEnd_apply, Complex.conj_ofReal, LinearMap.adjoint_id]
  have e1 : LinearMap.adjoint ((Real.sqrt p : ℂ) • qubitPauliZ b)
      = (Real.sqrt p : ℂ) • qubitPauliZ b := by
    rw [LinearMap.adjoint_smul, ← starRingEnd_apply, Complex.conj_ofReal, adjoint_qubitPauliZ]
  rw [phaseFlipChannel, e0, e1]
  simp only [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_id, LinearMap.id_comp,
    smul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt hp0,
    Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ 1 - p)]
  rw [Complex.ofReal_sub, Complex.ofReal_one]

/-- **"The amount of damping is determined by the probability in the mixture."** With the mixture
weight `p = 1 - α(λ)` (`α(λ) = phaseFlipProb λ = (1+√(1-λ))/2`), the single-CNOT model equals the
library's phase-damping operation elements `Ẽₖ = phaseDampKrausTilde b λ` (N&C eqs. 8.129–8.130),
for `0 ≤ λ`:
`tr_env(U (ρ ⊗ σ_{1-α}) U†) = Σₖ Ẽₖ ρ Ẽₖ†`.
So a single CNOT whose environment is the mixture `σ_{1-α(λ)}` models phase damping of parameter
`λ`, the damping increasing with the flip weight `1-α(λ) = (1-√(1-λ))/2`. -/
theorem phaseDampCNOTChannel_eq_phaseDampKrausTilde {lam : ℝ} (h0 : 0 ≤ lam) (ρ : H →ₗ[ℂ] H) :
    phaseDampCNOTChannel b (1 - phaseFlipProb lam) ρ =
      ∑ k, phaseDampKrausTilde b lam k ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampKrausTilde b lam k) := by
  have hp0 : 0 ≤ 1 - phaseFlipProb lam := one_sub_phaseFlipProb_nonneg h0
  have hp1 : 1 - phaseFlipProb lam ≤ 1 := by linarith [phaseFlipProb_nonneg lam]
  rw [phaseDampCNOTChannel_eq_phaseFlipChannel, phaseFlipChannel_eq_operatorSum b hp0 hp1,
    Fin.sum_univ_two]
  simp only [phaseDampKrausTilde, Matrix.cons_val_zero, Matrix.cons_val_one,
    phaseDampKrausZeroTilde, phaseDampKrausOneTilde, qubitPauliZ, sub_sub_cancel]

end AxQM.Concrete
