/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingChannel
import ToMathlib.Analysis.InnerProductSpace.OperatorSum
import ToMathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Concrete: the Figure 8.13 circuit models amplitude damping (N&C Exercise 8.20)

This file works, at the level of raw operators on an arbitrary two-dimensional complex inner
product space `H` (a qubit) with a chosen computational orthonormal basis `b : OrthonormalBasis
(Fin 2) ℂ H`, through Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Exercise
8.20** (p. 380–381): show that the **Figure 8.13 circuit** models the amplitude-damping quantum
operation, with `sin²(θ/2) = γ`.

## The circuit (Figure 8.13)

The circuit couples the principal qubit (the *system*, the left/first tensor factor) to an
*environment* qubit (the right/second factor) prepared in `|0⟩`, through two gates:

* a **controlled `R_y(θ)`** — `ampDampCRy b θ = P₀ ⊗ I + P₁ ⊗ R_y(θ)` — the system controls a
  `y`-axis rotation of the environment;
* a **CNOT** — `ampDampCNOT b = I ⊗ P₀ + X ⊗ P₁` — the environment controls a bit-flip of the
  system.

Applied in this order, `U = CNOT ∘ CRy` (`ampDampCircuit b θ`), the circuit sends the initial
product state `|ψ⟩ ⊗ |0⟩` to `U (|ψ⟩ ⊗ |0⟩)`; tracing out the environment gives the quantum
operation `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`. Reading off the operation elements `Eₖ = ⟨k|U|0⟩`
(N&C eqs. 8.9–8.10) gives, for `0 ≤ θ ≤ π`,

`E₀ = |0⟩⟨0| + cos(θ/2) |1⟩⟨1| = diag(1, √(1-γ))`,   `E₁ = sin(θ/2) |0⟩⟨1| = √γ σ₋`,

**exactly the amplitude-damping operation elements** of N&C eq. 8.108 with `γ = sin²(θ/2)`
(`Concrete.ampDampKrausZero`, `Concrete.ampDampKrausOne` of
`Concrete/AmplitudeDampingChannel.lean`, since `√(1 - sin²(θ/2)) = cos(θ/2)` and
`√(sin²(θ/2)) = sin(θ/2)` on `[0, π]`). The headline
`ampDampCircuit_reduced_eq_ampDampChannel` is therefore

`tr_env(U (ρ ⊗ |0⟩⟨0|) U†) = E_AD(ρ)`   with `γ = sin²(θ/2)`,

which is what the exercise asks. The circuit is genuinely a *unitary* dilation: each gate is
unitary (`adjoint_ampDampCRy_comp_self`, `adjoint_ampDampCNOT_comp_self`), hence so is the whole
circuit (`adjoint_ampDampCircuit_comp_self`).

## Contents

* `qubitRotYGen b`, `qubitRotY b θ` — the `y`-rotation generator `G = |1⟩⟨0| - |0⟩⟨1|` and the
  single-qubit rotation `R_y(θ) = cos(θ/2) I + sin(θ/2) G`, with its action on `|0⟩`
  (`qubitRotY_apply_zero`) and unitarity `R_y(θ)† R_y(θ) = I` (`adjoint_qubitRotY_comp_self`).
* `ampDampCRy b θ`, `ampDampCNOT b` — the controlled-`R_y` and CNOT gates, each unitary.
* `ampDampCircuit b θ = CNOT ∘ CRy` — the Figure 8.13 unitary, with
  `adjoint_ampDampCircuit_comp_self`.
* `ampDampCircuitDilation b θ = U (· ⊗ |0⟩)` — the dilation `V`, and its operation elements
  `krausOp_ampDampCircuitDilation_zero`/`_one`: `E₀ = ampDampKrausZero b (sin²(θ/2))`,
  `E₁ = ampDampKrausOne b (sin²(θ/2))`.
* `ampDampCircuitChannel b θ ρ = tr_env(V ρ V†)`, with **the answer**
  `ampDampCircuit_reduced_eq_ampDampChannel : ampDampCircuitChannel b θ ρ = ampDampChannel b
  (sin²(θ/2)) ρ` (for `0 ≤ θ ≤ π`).

## Related items

The development uses bare `LinearMap`s on an inner product space, `TensorProduct`, an
`OrthonormalBasis`, `InnerProductSpace.rankOne`, and the abstract partial trace of
`ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract`. The operation elements
`Eₖ = ⟨k|U|0⟩` and the operator-sum reduced dynamics are stated at the level of operators.
Compare the operator-sum circuits of Exercises 8.4 (`AxQM/Concrete/ControlledFlipOperatorSum.lean`)
and 8.5 (`AxQM/Concrete/SpinFlipOperatorSum.lean`). The statement of Exercise 8.20 is in
`AxQM/NC/Ch8/Exercise8_20.lean`.

## Design

The qubit is an *arbitrary* two-dimensional complex inner product space `H` with a chosen
computational basis `b`, so the model holds for every qubit; the gates reuse the abstract-qubit
projectors `Concrete.qubitProj`, bit-flip `Concrete.qubitFlip`, and lowering operator
`Concrete.qubitLower` of `Concrete/QubitBasisOperators.lean`, and the amplitude-damping operation
elements/channel of `Concrete/AmplitudeDampingChannel.lean`. The reduction to the two operation
elements is a direct application of the operator-sum infrastructure
`ToMathlib.Analysis.InnerProductSpace.OperatorSum` (`LinearMap.krausOp`,
`partialTraceRight_conj_eq_sum_krausOp`): the dilation is `V = U(· ⊗ |0⟩)`, and the only genuine
work is computing `krausOp b V 0` and `krausOp b V 1`. The identification with amplitude damping
uses `√(1 - sin²(θ/2)) = cos(θ/2)` and `√(sin²(θ/2)) = sin(θ/2)`, valid precisely on `0 ≤ θ ≤ π`
— exactly N&C's physical range, where `γ = sin²(θ/2)` ranges over `[0,1]`.
-/

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-! ### The single-qubit `y`-rotation `R_y(θ)` -/

/-- The **`y`-rotation generator** `G = σ₊ - σ₋ = |1⟩⟨0| - |0⟩⟨1|`: the anti-self-adjoint operator
with `G² = -I`, so that `R_y(θ) = cos(θ/2) I + sin(θ/2) G` is a genuine rotation. -/
noncomputable def qubitRotYGen : H →ₗ[ℂ] H :=
  (InnerProductSpace.rankOne ℂ (b 1) (b 0) : H →ₗ[ℂ] H)
    - (InnerProductSpace.rankOne ℂ (b 0) (b 1) : H →ₗ[ℂ] H)

/-- The single-qubit **`y`-axis rotation** `R_y(θ) = exp(-iθY/2) = cos(θ/2) I + sin(θ/2) G`
(N&C §4.2), with `G = |1⟩⟨0| - |0⟩⟨1|` the rotation generator. It sends
`|0⟩ ↦ cos(θ/2)|0⟩ + sin(θ/2)|1⟩` and `|1⟩ ↦ -sin(θ/2)|0⟩ + cos(θ/2)|1⟩`. -/
noncomputable def qubitRotY (θ : ℝ) : H →ₗ[ℂ] H :=
  (Real.cos (θ / 2) : ℂ) • LinearMap.id + (Real.sin (θ / 2) : ℂ) • qubitRotYGen b

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `G |0⟩ = |1⟩`: the generator raises the ground state. -/
@[simp] theorem qubitRotYGen_apply_zero : qubitRotYGen b (b 0) = b 1 := by
  simp only [qubitRotYGen, LinearMap.sub_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, b.inner_eq_ite]
  simp

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The action of `R_y(θ)` on the ground state: `R_y(θ)|0⟩ = cos(θ/2)|0⟩ + sin(θ/2)|1⟩`. -/
@[simp] theorem qubitRotY_apply_zero (θ : ℝ) :
    qubitRotY b θ (b 0) = (Real.cos (θ / 2) : ℂ) • b 0 + (Real.sin (θ / 2) : ℂ) • b 1 := by
  rw [qubitRotY, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.id_apply, qubitRotYGen_apply_zero]

/-- The generator is anti-self-adjoint: `G† = -G` (`adjoint_rankOne` swaps the two rank-ones). -/
theorem adjoint_qubitRotYGen : LinearMap.adjoint (qubitRotYGen b) = - qubitRotYGen b := by
  rw [qubitRotYGen, map_sub, ← ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace,
    ← ContinuousLinearMap.adjoint_toLinearMap_of_completeSpace, InnerProductSpace.adjoint_rankOne,
    InnerProductSpace.adjoint_rankOne, neg_sub]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `G² = -I`: the cross terms `σ₊σ₋ = P₁`, `σ₋σ₊ = P₀` combine to `-(P₀ + P₁) = -I` and the
diagonal terms `σ₊² = σ₋² = 0` vanish. -/
theorem qubitRotYGen_comp_self : qubitRotYGen b ∘ₗ qubitRotYGen b = - LinearMap.id := by
  have h : qubitRotYGen b ∘ₗ qubitRotYGen b = -(qubitProj b 0 + qubitProj b 1) := by
    simp only [qubitRotYGen, qubitProj, LinearMap.comp_sub, LinearMap.sub_comp,
      ← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.rankOne_comp_rankOne,
      ContinuousLinearMap.toLinearMap_zero, b.inner_eq_ite,
      Fin.isValue, Fin.reduceEq, ↓reduceIte, one_smul, zero_smul]
    abel
  rw [h, sum_qubitProj]

/-- The adjoint of `R_y(θ)` is `R_y(θ)† = cos(θ/2) I - sin(θ/2) G` (real coefficients are
conjugation-fixed; `G† = -G`). -/
theorem adjoint_qubitRotY (θ : ℝ) :
    LinearMap.adjoint (qubitRotY b θ)
      = (Real.cos (θ / 2) : ℂ) • LinearMap.id - (Real.sin (θ / 2) : ℂ) • qubitRotYGen b := by
  have hc : star ((Real.cos (θ / 2) : ℝ) : ℂ) = ((Real.cos (θ / 2) : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  have hs : star ((Real.sin (θ / 2) : ℝ) : ℂ) = ((Real.sin (θ / 2) : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [qubitRotY, map_add, LinearMap.adjoint_smul, LinearMap.adjoint_smul, LinearMap.adjoint_id,
    adjoint_qubitRotYGen, hc, hs, smul_neg, sub_eq_add_neg]

/-- `R_y(θ)` is **unitary**: `R_y(θ)† R_y(θ) = I`. From `(cos I - sin G)(cos I + sin G) =
cos² I - sin² G² = (cos² + sin²) I = I`, using `G² = -I` and `cos² + sin² = 1`. -/
theorem adjoint_qubitRotY_comp_self (θ : ℝ) :
    LinearMap.adjoint (qubitRotY b θ) ∘ₗ qubitRotY b θ = LinearMap.id := by
  rw [adjoint_qubitRotY, qubitRotY]
  simp only [LinearMap.sub_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.id_comp, LinearMap.comp_id, qubitRotYGen_comp_self, smul_neg]
  match_scalars
  · linear_combination Complex.cos_sq_add_sin_sq (↑θ / 2)
  · ring

/-! ### The Figure 8.13 gates and circuit -/

/-- The **controlled-`R_y(θ)`** gate `P₀ ⊗ I + P₁ ⊗ R_y(θ)` (N&C Fig. 8.13): the system (left
factor) controls a `y`-rotation of the environment (right factor). -/
noncomputable def ampDampCRy (θ : ℝ) : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H :=
  TensorProduct.map (qubitProj b 0) LinearMap.id
    + TensorProduct.map (qubitProj b 1) (qubitRotY b θ)

/-- The **CNOT** gate `I ⊗ P₀ + X ⊗ P₁` (N&C Fig. 8.13): the environment (right factor) controls a
bit-flip of the system (left factor). -/
noncomputable def ampDampCNOT : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H :=
  TensorProduct.map LinearMap.id (qubitProj b 0)
    + TensorProduct.map (qubitFlip b) (qubitProj b 1)

/-- `CNOT` is self-adjoint: each summand is a tensor of self-adjoints. -/
theorem adjoint_ampDampCNOT : LinearMap.adjoint (ampDampCNOT b) = ampDampCNOT b := by
  rw [ampDampCNOT, map_add, TensorProduct.adjoint_map, TensorProduct.adjoint_map,
    adjoint_qubitProj, adjoint_qubitProj, adjoint_qubitFlip, LinearMap.adjoint_id]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `CNOT` is an involution: `CNOT² = I`. Cross terms vanish (`P₀ P₁ = P₁ P₀ = 0`); the diagonal
terms use `X² = I`, `Pᵢ² = Pᵢ`, and `P₀ + P₁ = I`. -/
theorem ampDampCNOT_comp_self : ampDampCNOT b ∘ₗ ampDampCNOT b = LinearMap.id := by
  rw [ampDampCNOT, LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, qubitProj_comp_qubitProj, qubitProj_comp_qubitProj,
    qubitProj_comp_qubitProj, qubitProj_comp_qubitProj]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, LinearMap.comp_id, LinearMap.id_comp,
    TensorProduct.map_zero_right, add_zero, zero_add]
  rw [qubitFlip_comp_qubitFlip, ← TensorProduct.map_add_right, sum_qubitProj, TensorProduct.map_id]

/-- `CNOT` is unitary: `CNOT† CNOT = I`. Immediate from self-adjointness and involutivity. -/
theorem adjoint_ampDampCNOT_comp_self : LinearMap.adjoint (ampDampCNOT b) ∘ₗ ampDampCNOT b
    = LinearMap.id := by
  rw [adjoint_ampDampCNOT, ampDampCNOT_comp_self]

/-- The controlled-`R_y` adjoint is `P₀ ⊗ I + P₁ ⊗ R_y(θ)†`. -/
theorem adjoint_ampDampCRy (θ : ℝ) :
    LinearMap.adjoint (ampDampCRy b θ)
      = TensorProduct.map (qubitProj b 0) LinearMap.id
        + TensorProduct.map (qubitProj b 1) (LinearMap.adjoint (qubitRotY b θ)) := by
  rw [ampDampCRy, map_add, TensorProduct.adjoint_map, TensorProduct.adjoint_map,
    adjoint_qubitProj, adjoint_qubitProj, LinearMap.adjoint_id]

/-- The controlled-`R_y` gate is **unitary**: `CRy† CRy = I`. The cross terms vanish
(`P₀ P₁ = P₁ P₀ = 0`); the diagonal terms use `Pᵢ² = Pᵢ`, `R_y(θ)† R_y(θ) = I`, and
`P₀ + P₁ = I`. -/
theorem adjoint_ampDampCRy_comp_self (θ : ℝ) :
    LinearMap.adjoint (ampDampCRy b θ) ∘ₗ ampDampCRy b θ = LinearMap.id := by
  rw [adjoint_ampDampCRy, ampDampCRy, LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, qubitProj_comp_qubitProj, qubitProj_comp_qubitProj,
    qubitProj_comp_qubitProj, qubitProj_comp_qubitProj]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, LinearMap.comp_id, LinearMap.id_comp,
    TensorProduct.map_zero_left, add_zero, zero_add]
  rw [adjoint_qubitRotY_comp_self, ← TensorProduct.map_add_left, sum_qubitProj,
    TensorProduct.map_id]

/-- The **Figure 8.13 circuit** unitary `U = CNOT ∘ CRy(θ)`: prepare the environment in `|0⟩`, apply
the controlled rotation, then the CNOT. -/
noncomputable def ampDampCircuit (θ : ℝ) : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H :=
  ampDampCNOT b ∘ₗ ampDampCRy b θ

/-- The circuit is **unitary**: `U† U = I`, from the unitarity of its two gates. -/
theorem adjoint_ampDampCircuit_comp_self (θ : ℝ) :
    LinearMap.adjoint (ampDampCircuit b θ) ∘ₗ ampDampCircuit b θ = LinearMap.id := by
  have hcnot : LinearMap.adjoint (ampDampCNOT b) ∘ₗ (ampDampCNOT b ∘ₗ ampDampCRy b θ)
      = ampDampCRy b θ := by
    rw [← LinearMap.comp_assoc, adjoint_ampDampCNOT_comp_self, LinearMap.id_comp]
  rw [ampDampCircuit, LinearMap.adjoint_comp, LinearMap.comp_assoc, hcnot,
    adjoint_ampDampCRy_comp_self]

/-! ### Operation elements and the reduced channel -/

/-- The **dilation** `V = U (· ⊗ |0⟩) : H →ₗ H ⊗ H`: prepare the environment in `|0⟩`, then apply
the Figure 8.13 unitary. Its operation elements `krausOp b V k` are the Kraus operators of the
modelled channel. -/
noncomputable def ampDampCircuitDilation (θ : ℝ) : H →ₗ[ℂ] H ⊗[ℂ] H :=
  ampDampCircuit b θ ∘ₗ LinearMap.embedRight b 0

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- The circuit's action on the initial product basis state `x ⊗ |0⟩`:
`U (x ⊗ |0⟩) = ⟨0|x⟩ |00⟩ + cos(θ/2)⟨1|x⟩ |10⟩ + sin(θ/2)⟨1|x⟩ |01⟩`. This is the single tensor
computation the operation elements are read off from. -/
theorem ampDampCircuit_apply_tmul_zero (θ : ℝ) (x : H) :
    ampDampCircuit b θ (x ⊗ₜ[ℂ] b 0)
      = (inner ℂ (b 0) x) • (b 0 ⊗ₜ[ℂ] b 0)
        + ((Real.cos (θ / 2) : ℂ) * inner ℂ (b 1) x) • (b 1 ⊗ₜ[ℂ] b 0)
        + ((Real.sin (θ / 2) : ℂ) * inner ℂ (b 1) x) • (b 0 ⊗ₜ[ℂ] b 1) := by
  have hcry : ampDampCRy b θ (x ⊗ₜ[ℂ] b 0)
      = (inner ℂ (b 0) x) • (b 0 ⊗ₜ[ℂ] b 0)
        + (inner ℂ (b 1) x)
          • (b 1 ⊗ₜ[ℂ] ((Real.cos (θ / 2) : ℂ) • b 0 + (Real.sin (θ / 2) : ℂ) • b 1)) := by
    simp only [ampDampCRy, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
      qubitProj_apply, qubitRotY_apply_zero, TensorProduct.smul_tmul']
  -- `CNOT` on the three basis states reached by the initial `env = |0⟩` column.
  have e00 : ampDampCNOT b (b 0 ⊗ₜ[ℂ] b 0) = b 0 ⊗ₜ[ℂ] b 0 := by
    simp only [ampDampCNOT, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
      qubitProj_apply, qubitFlip_apply_zero, b.inner_eq_ite, Fin.isValue, ↓reduceIte, Fin.reduceEq,
      one_smul, zero_smul, TensorProduct.tmul_zero, add_zero]
  have e10 : ampDampCNOT b (b 1 ⊗ₜ[ℂ] b 0) = b 1 ⊗ₜ[ℂ] b 0 := by
    simp only [ampDampCNOT, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
      qubitProj_apply, qubitFlip_apply_one, b.inner_eq_ite, Fin.isValue, ↓reduceIte, Fin.reduceEq,
      one_smul, zero_smul, TensorProduct.tmul_zero, add_zero]
  have e11 : ampDampCNOT b (b 1 ⊗ₜ[ℂ] b 1) = b 0 ⊗ₜ[ℂ] b 1 := by
    simp only [ampDampCNOT, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
      qubitProj_apply, qubitFlip_apply_one, b.inner_eq_ite, Fin.isValue, ↓reduceIte, Fin.reduceEq,
      one_smul, zero_smul, TensorProduct.tmul_zero, zero_add]
  rw [ampDampCircuit, LinearMap.comp_apply, hcry, map_add, map_smul, map_smul,
    TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, map_add, map_smul,
    map_smul, e00, e10, e11]
  module

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **The first operation element is `E₀`** of amplitude damping: `E₀ = ⟨0|U|0⟩ =
|0⟩⟨0| + cos(θ/2)|1⟩⟨1| = ampDampKrausZero b (sin²(θ/2))`, for `0 ≤ θ ≤ π` (so
`√(1 - sin²(θ/2)) = cos(θ/2)`). -/
theorem krausOp_ampDampCircuitDilation_zero (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    LinearMap.krausOp b (ampDampCircuitDilation b θ) 0
      = ampDampKrausZero b (Real.sin (θ / 2) ^ 2) := by
  have hcos : (0 : ℝ) ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsqrt : (Real.sqrt (1 - Real.sin (θ / 2) ^ 2) : ℂ) = (Real.cos (θ / 2) : ℂ) := by
    rw [← Real.cos_sq', Real.sqrt_sq hcos]
  ext x
  rw [LinearMap.krausOp_apply, ampDampCircuitDilation, LinearMap.comp_apply,
    LinearMap.embedRight_apply, ampDampCircuit_apply_tmul_zero]
  simp only [map_add, map_smul, LinearMap.restrictRight_tmul, b.inner_eq_ite, ampDampKrausZero,
    hsqrt, LinearMap.add_apply, LinearMap.smul_apply, qubitProj_apply, Fin.isValue, ↓reduceIte,
    Fin.reduceEq]
  module

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **The second operation element is `E₁`** of amplitude damping: `E₁ = ⟨1|U|0⟩ =
sin(θ/2)|0⟩⟨1| = ampDampKrausOne b (sin²(θ/2))`, for `0 ≤ θ ≤ π` (so `√(sin²(θ/2)) = sin(θ/2)`). -/
theorem krausOp_ampDampCircuitDilation_one (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    LinearMap.krausOp b (ampDampCircuitDilation b θ) 1
      = ampDampKrausOne b (Real.sin (θ / 2) ^ 2) := by
  have hsin : (0 : ℝ) ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsqrt : (Real.sqrt (Real.sin (θ / 2) ^ 2) : ℂ) = (Real.sin (θ / 2) : ℂ) := by
    rw [Real.sqrt_sq hsin]
  ext x
  rw [LinearMap.krausOp_apply, ampDampCircuitDilation, LinearMap.comp_apply,
    LinearMap.embedRight_apply, ampDampCircuit_apply_tmul_zero]
  simp only [map_add, map_smul, LinearMap.restrictRight_tmul, b.inner_eq_ite, ampDampKrausOne,
    hsqrt, LinearMap.smul_apply, qubitLower, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  module

/-- The **quantum operation modelled by the circuit**, in dilation form `E(ρ) = tr_env(V ρ V†)`
(the operator-sum route to `tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`). -/
noncomputable def ampDampCircuitChannel (θ : ℝ) (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b
    (ampDampCircuitDilation b θ ∘ₗ ρ ∘ₗ LinearMap.adjoint (ampDampCircuitDilation b θ))

omit [CompleteSpace H] in
/-- **N&C Exercise 8.20 (the answer):** the Figure 8.13 circuit models amplitude damping with
`γ = sin²(θ/2)`. Tracing the environment out of the circuit's closed evolution returns exactly the
amplitude-damping channel `E_AD` of `Concrete/AmplitudeDampingChannel.lean` at `γ = sin²(θ/2)`:

`tr_env(U (ρ ⊗ |0⟩⟨0|) U†) = E_AD(ρ)`,   for `0 ≤ θ ≤ π`.

The operation elements `Eₖ = ⟨k|U|0⟩` are `E₀ = diag(1, cos(θ/2))` and `E₁ = sin(θ/2)|0⟩⟨1|`
(`krausOp_ampDampCircuitDilation_zero`/`_one`), matching N&C eq. 8.108 with
`cos(θ/2) = √(1-γ)`, `sin(θ/2) = √γ`; the result is the operator-sum identity
`partialTraceRight_conj_eq_sum_krausOp` combined with these identifications. -/
theorem ampDampCircuit_reduced_eq_ampDampChannel (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (ρ : H →ₗ[ℂ] H) :
    ampDampCircuitChannel b θ ρ = ampDampChannel b (Real.sin (θ / 2) ^ 2) ρ := by
  rw [ampDampCircuitChannel, LinearMap.partialTraceRight_conj_eq_sum_krausOp, Fin.sum_univ_two,
    krausOp_ampDampCircuitDilation_zero b θ hθ0 hθπ, krausOp_ampDampCircuitDilation_one b θ hθ0 hθπ,
    ampDampChannel]

/-- **Trace preservation (a genuine quantum operation).** The circuit's operation elements satisfy
the completeness relation `∑ₖ Eₖ† Eₖ = I` (N&C eq. 8.114 context), inherited from
`ampDampKraus_completeness` since `E₀, E₁` are the amplitude-damping operation elements at
`γ = sin²(θ/2) ∈ [0,1]`. -/
theorem sum_adjoint_krausOp_ampDampCircuitDilation (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ∑ k, LinearMap.adjoint (LinearMap.krausOp b (ampDampCircuitDilation b θ) k) ∘ₗ
        LinearMap.krausOp b (ampDampCircuitDilation b θ) k = LinearMap.id := by
  rw [Fin.sum_univ_two, krausOp_ampDampCircuitDilation_zero b θ hθ0 hθπ,
    krausOp_ampDampCircuitDilation_one b θ hθ0 hθπ]
  refine ampDampKraus_completeness b _ (sq_nonneg _) ?_
  rw [← Real.sin_sq_add_cos_sq (θ / 2)]
  nlinarith [sq_nonneg (Real.cos (θ / 2))]

end AxQM.Concrete

end
