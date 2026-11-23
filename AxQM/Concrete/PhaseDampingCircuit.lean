/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingCircuit
import ToMathlib.Analysis.InnerProductSpace.OperatorSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Concrete: circuit model for phase damping (N&C Exercise 8.26, Figure 8.15)

This file works, at the level of raw operators on a two-dimensional complex inner product space (a
qubit), through Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Exercise 8.26**
(p. 385). A *principal system* (control) and an *environment* (target) prepared in `|0⟩` interact
through the **controlled-`Rᵧ(θ)`** gate of Figure 8.15,

`U = P₀ ⊗ I + P₁ ⊗ Rᵧ(θ)`,

where `Rᵧ(θ) = cos(θ/2) I + sin(θ/2)(σ₊ - σ₋)` is the y-rotation on the environment and
`P₀ = |0⟩⟨0|`, `P₁ = |1⟩⟨1|` are the computational-basis projectors on the system. This is the
*same* controlled-`Rᵧ` gate as the amplitude-damping circuit of Exercise 8.20 — phase damping is
that circuit with the CNOT dropped — so `Rᵧ(θ)` (`qubitRotY`) and `U` (`ampDampCRy`, unitary by
`adjoint_ampDampCRy_comp_self`) are **reused** from `Concrete/AmplitudeDampingCircuit.lean`, not
redefined. Tracing out the environment yields the operation `E_θ(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`,
whose operation elements `Eₖ = ⟨k| U |0⟩` are

`E₀ = diag(1, cos(θ/2))`,   `E₁ = diag(0, sin(θ/2))`.

Choosing `θ` so that `sin²(θ/2) = λ` (equivalently `θ = 2 arcsin √λ`, which realizes any
`λ ∈ [0,1]`), and using `√(1-λ) = cos(θ/2)`, `√λ = sin(θ/2)` on `0 ≤ θ ≤ π`, these become exactly
the **phase-damping** elements `E₀ = diag(1,√(1-λ))`, `E₁ = diag(0,√λ)` of N&C eqs. (8.127)–(8.128).
Thus for appropriate `θ` the Figure 8.15 circuit models the phase-damping channel.

## Setting

Everything here is stated for bare `LinearMap`s, `TensorProduct`, an
`OrthonormalBasis`, and the abstract partial trace / operator-sum infrastructure. The circuit's
induced operation and its operation elements quantify over raw operators `Eₖ`. Compare Exercise 8.4
(`AxQM/Concrete/ControlledFlipOperatorSum.lean`). The statement of Exercise 8.26 is in
`AxQM/NC/Ch8/Exercise8_26.lean`.

## Design

The qubit is an *arbitrary* two-dimensional complex inner product space `H` with a chosen
computational basis `b`. Because phase damping *is* the amplitude-damping circuit with the CNOT
dropped, the gate machinery is reused wholesale from `Concrete/AmplitudeDampingCircuit.lean`: the
`y`-rotation `qubitRotY` (`= cos(θ/2) I + sin(θ/2)(σ₊ - σ₋)`, unitary) and the controlled-`Rᵧ` gate
`ampDampCRy` (`= P₀ ⊗ I + P₁ ⊗ Rᵧ(θ)`, unitary by `adjoint_ampDampCRy_comp_self`) — no circuit gate
is redefined here. The reduction to the operation elements is an application of the operator-sum
infrastructure (`LinearMap.krausOp`, `partialTraceRight_conj_eq_sum_krausOp`): packaging
`ρ ↦ U(ρ ⊗ |0⟩⟨0|)U†` as the dilation `V = U(· ⊗ |0⟩)`, the operation elements are `Eₖ = krausOp b V
k`. The phase-damping target `E₀` is literally amplitude damping's `E₀` (`ampDampKrausZero`, N&C eq.
8.108 vs. 8.127 — the same diagonal operator), reused here; only `E₁ = √λ P₁`
(`phaseDampingKrausOne`, vs. amplitude damping's `√γ |0⟩⟨1|`) is genuinely new. The operation
elements satisfy `∑ₖ Eₖ† Eₖ = I` for every `θ` (trace preservation).
-/

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-! ### The phase-damping operation elements and channel (N&C eqs. 8.127–8.128) -/

/-- The **first phase-damping operation element** `E₀ = diag(1, √(1-λ)) = |0⟩⟨0| + √(1-λ)|1⟩⟨1|`
(N&C eq. 8.127). This is the *same* diagonal operator as amplitude damping's `E₀` (eq. 8.108), so it
is defined by reuse of `ampDampKrausZero`; only the second element differs between the two channels.
-/
def phaseDampingKrausZero (lam : ℝ) : H →ₗ[ℂ] H := ampDampKrausZero b lam

/-- The **second phase-damping operation element** `E₁ = diag(0, √λ) = √λ |1⟩⟨1|` (N&C eq. 8.128):
unlike amplitude damping's `√λ |0⟩⟨1|`, it does *not* move `|1⟩` to `|0⟩` (no energy is lost); it
only scales the excited amplitude, dephasing the coherences. -/
def phaseDampingKrausOne (lam : ℝ) : H →ₗ[ℂ] H := (Real.sqrt lam : ℂ) • qubitProj b 1

/-- `E₀` is self-adjoint (it is amplitude damping's self-adjoint `E₀`). -/
@[simp] theorem adjoint_phaseDampingKrausZero (lam : ℝ) :
    LinearMap.adjoint (phaseDampingKrausZero b lam) = phaseDampingKrausZero b lam :=
  adjoint_ampDampKrausZero b lam

/-- `E₁ = √λ P₁` is self-adjoint (`√λ` real, `P₁† = P₁`). -/
@[simp] theorem adjoint_phaseDampingKrausOne (lam : ℝ) :
    LinearMap.adjoint (phaseDampingKrausOne b lam) = phaseDampingKrausOne b lam := by
  rw [phaseDampingKrausOne, LinearMap.adjoint_smul, adjoint_qubitProj, RCLike.star_def,
    Complex.conj_ofReal]

/-- The **phase-damping channel** `E(ρ) = E₀ ρ E₀† + E₁ ρ E₁†`, the target of the Figure 8.15
circuit model. -/
def phaseDampingChannel (lam : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  phaseDampingKrausZero b lam ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampingKrausZero b lam)
    + phaseDampingKrausOne b lam ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampingKrausOne b lam)

/-! ### The controlled-`Rᵧ` interaction and its dilation -/

/-- The **dilation** `V = U(· ⊗ |0⟩) : H →ₗ H ⊗ H` of the Figure 8.15 circuit: prepare the
environment in `|0⟩`, then apply the controlled-`Rᵧ(θ)` interaction `U = P₀ ⊗ I + P₁ ⊗ Rᵧ(θ)`. The
phase-damping circuit is the amplitude-damping circuit (Exercise 8.20) with the CNOT dropped, so its
interaction *is* the controlled-`Rᵧ` gate `ampDampCRy` of `Concrete/AmplitudeDampingCircuit.lean`
(which builds on the `y`-rotation `qubitRotY` and is unitary by `adjoint_ampDampCRy_comp_self`) — no
independent gate is introduced here. Its operation elements `krausOp b V k` are the circuit's Kraus
operators. -/
def phaseDampingCircuitDilation (θ : ℝ) : H →ₗ[ℂ] H ⊗[ℂ] H :=
  ampDampCRy b θ ∘ₗ LinearMap.embedRight b 0

/-- The **circuit operation** `E_θ(ρ) = tr_env(V ρ V†)` induced by the Figure 8.15 circuit. -/
def phaseDampingCircuitOperation (θ : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b
    (phaseDampingCircuitDilation b θ ∘ₗ ρ ∘ₗ LinearMap.adjoint (phaseDampingCircuitDilation b θ))

/-! ### The circuit's operation elements -/

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **First operation element** `E₀ = ⟨0| U |0⟩ = |0⟩⟨0| + cos(θ/2)|1⟩⟨1| = diag(1, cos(θ/2))`. -/
theorem krausOp_phaseDampingCircuitDilation_zero (θ : ℝ) :
    LinearMap.krausOp b (phaseDampingCircuitDilation b θ) 0
      = qubitProj b 0 + (Real.cos (θ / 2) : ℂ) • qubitProj b 1 := by
  ext x
  simp only [LinearMap.krausOp_apply, phaseDampingCircuitDilation, LinearMap.comp_apply,
    LinearMap.embedRight_apply, ampDampCRy, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, qubitRotY_apply_zero, map_add, LinearMap.restrictRight_tmul,
    inner_add_right, inner_smul_right, b.inner_eq_ite, LinearMap.smul_apply, qubitProj_apply]
  simp

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **Second operation element** `E₁ = ⟨1| U |0⟩ = sin(θ/2)|1⟩⟨1| = diag(0, sin(θ/2))`. -/
theorem krausOp_phaseDampingCircuitDilation_one (θ : ℝ) :
    LinearMap.krausOp b (phaseDampingCircuitDilation b θ) 1
      = (Real.sin (θ / 2) : ℂ) • qubitProj b 1 := by
  ext x
  simp only [LinearMap.krausOp_apply, phaseDampingCircuitDilation, LinearMap.comp_apply,
    LinearMap.embedRight_apply, ampDampCRy, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, qubitRotY_apply_zero, map_add, LinearMap.restrictRight_tmul,
    inner_add_right, inner_smul_right, b.inner_eq_ite, LinearMap.smul_apply, qubitProj_apply]
  simp

/-- The complexified Pythagorean identity `cos²(θ/2) + sin²(θ/2) = 1`, with the real coefficients
cast to `ℂ` in the `a * a` shape produced by `smul_smul`. Used to collapse
`cos²(θ/2) P₁ + sin²(θ/2) P₁` to `P₁` in the completeness relation. -/
theorem ofReal_cos_mul_cos_add_sin_mul_sin (θ : ℝ) :
    (Real.cos (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)
      + (Real.sin (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  norm_cast
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

/-- **Completeness / trace preservation:** `E₀† E₀ + E₁† E₁ = I` for every `θ`. Here
`E₀† E₀ = P₀ + cos²(θ/2) P₁` and `E₁† E₁ = sin²(θ/2) P₁`, summing to `P₀ + P₁ = I` via
`cos² + sin² = 1`. So the circuit operation is a genuine (trace-preserving) quantum operation. -/
theorem sum_adjoint_krausOp_phaseDampingCircuitDilation (θ : ℝ) :
    ∑ k, LinearMap.adjoint (LinearMap.krausOp b (phaseDampingCircuitDilation b θ) k) ∘ₗ
        LinearMap.krausOp b (phaseDampingCircuitDilation b θ) k = LinearMap.id := by
  rw [Fin.sum_univ_two, krausOp_phaseDampingCircuitDilation_zero,
    krausOp_phaseDampingCircuitDilation_one]
  have hcos : LinearMap.adjoint (qubitProj b 0 + (Real.cos (θ / 2) : ℂ) • qubitProj b 1)
      = qubitProj b 0 + (Real.cos (θ / 2) : ℂ) • qubitProj b 1 := by
    rw [map_add, LinearMap.adjoint_smul, adjoint_qubitProj, adjoint_qubitProj, RCLike.star_def,
      Complex.conj_ofReal]
  rw [hcos, LinearMap.adjoint_smul, adjoint_qubitProj, RCLike.star_def, Complex.conj_ofReal]
  simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul,
    qubitProj_comp_qubitProj, Fin.isValue, Fin.reduceEq, ↓reduceIte, smul_zero, add_zero, zero_add,
    smul_smul]
  rw [add_assoc, ← add_smul, ofReal_cos_mul_cos_add_sin_mul_sin, one_smul, sum_qubitProj]

/-! ### The circuit models phase damping for appropriate `θ` -/

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- For `0 ≤ θ ≤ π` the circuit's first operation element is exactly the phase-damping `E₀` with
`λ = sin²(θ/2)`: `√(1-λ) = √(cos²(θ/2)) = cos(θ/2)`. -/
theorem krausOp_phaseDampingCircuitDilation_zero_eq (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    LinearMap.krausOp b (phaseDampingCircuitDilation b θ) 0
      = phaseDampingKrausZero b (Real.sin (θ / 2) ^ 2) := by
  have hc : Real.sqrt (1 - Real.sin (θ / 2) ^ 2) = Real.cos (θ / 2) := by
    rw [show (1 : ℝ) - Real.sin (θ / 2) ^ 2 = Real.cos (θ / 2) ^ 2 from by
      have := Real.sin_sq_add_cos_sq (θ / 2); linarith]
    exact Real.sqrt_sq (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)
  rw [krausOp_phaseDampingCircuitDilation_zero, phaseDampingKrausZero, ampDampKrausZero, hc]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- For `0 ≤ θ ≤ π` the circuit's second operation element is exactly the phase-damping `E₁` with
`λ = sin²(θ/2)`: `√λ = √(sin²(θ/2)) = sin(θ/2)`. -/
theorem krausOp_phaseDampingCircuitDilation_one_eq (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    LinearMap.krausOp b (phaseDampingCircuitDilation b θ) 1
      = phaseDampingKrausOne b (Real.sin (θ / 2) ^ 2) := by
  have hs : Real.sqrt (Real.sin (θ / 2) ^ 2) = Real.sin (θ / 2) :=
    Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  rw [krausOp_phaseDampingCircuitDilation_one, phaseDampingKrausOne, hs]

/-- **Exercise 8.26 (headline).** For `0 ≤ θ ≤ π` the Figure 8.15 circuit operation equals the
phase-damping channel with `λ = sin²(θ/2)`. Proof: expand the induced operation as the operator sum
`∑ₖ Eₖ ρ Eₖ†` and identify `E₀`, `E₁` with the phase-damping operation elements. -/
theorem phaseDampingCircuitOperation_eq_phaseDampingChannel (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) (ρ : H →ₗ[ℂ] H) :
    phaseDampingCircuitOperation b θ ρ = phaseDampingChannel b (Real.sin (θ / 2) ^ 2) ρ := by
  rw [phaseDampingCircuitOperation, LinearMap.partialTraceRight_conj_eq_sum_krausOp,
    Fin.sum_univ_two, krausOp_phaseDampingCircuitDilation_zero_eq b θ hθ0 hθπ,
    krausOp_phaseDampingCircuitDilation_one_eq b θ hθ0 hθπ, phaseDampingChannel,
    adjoint_phaseDampingKrausZero, adjoint_phaseDampingKrausOne]

/-- **Exercise 8.26 (θ chosen appropriately).** For *any* phase-damping parameter `λ ∈ [0,1]` there
is an angle `θ ∈ [0,π]` — namely `θ = 2 arcsin √λ` — for which the Figure 8.15 circuit realizes the
phase-damping channel with parameter `λ`. This is the exercise's "provided `θ` is chosen
appropriately". -/
theorem phaseDampingCircuit_models_phaseDamping (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi ∧
      ∀ ρ : H →ₗ[ℂ] H, phaseDampingCircuitOperation b θ ρ = phaseDampingChannel b lam ρ := by
  have hsqrt_le : Real.sqrt lam ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]; exact Real.sqrt_le_sqrt h1
  have harcsin_nonneg : 0 ≤ Real.arcsin (Real.sqrt lam) :=
    Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)
  refine ⟨2 * Real.arcsin (Real.sqrt lam), by linarith, ?_, fun ρ => ?_⟩
  · have := Real.arcsin_le_pi_div_two (Real.sqrt lam); linarith
  · have hθ0 : 0 ≤ 2 * Real.arcsin (Real.sqrt lam) := by linarith
    have hθπ : 2 * Real.arcsin (Real.sqrt lam) ≤ Real.pi := by
      have := Real.arcsin_le_pi_div_two (Real.sqrt lam); linarith
    rw [phaseDampingCircuitOperation_eq_phaseDampingChannel b _ hθ0 hθπ ρ]
    congr 2
    rw [show 2 * Real.arcsin (Real.sqrt lam) / 2 = Real.arcsin (Real.sqrt lam) from by ring,
      Real.sin_arcsin (by linarith [Real.sqrt_nonneg lam]) hsqrt_le, Real.sq_sqrt h0]

end AxQM.Concrete

end
