/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QubitBasisOperators
import ToMathlib.Analysis.InnerProductSpace.OperatorSum

/-!
# Concrete: operator-sum representation of the controlled-flip channel (N&C Exercise 8.4)

This file works, at the level of raw operators on a two-dimensional complex inner product space (a
qubit), through Nielsen & Chuang, *Quantum Computation and Quantum Information*, **Exercise 8.4**
(p. 361). A single-qubit *principal system* interacts with a single-qubit *environment* through the
unitary

`U = P₀ ⊗ I + P₁ ⊗ X`   (N&C eq. 8.16),

where `X` is the Pauli bit-flip on the environment and `P₀ = |0⟩⟨0|`, `P₁ = |1⟩⟨1|` are the
computational-basis projectors on the system. With the environment prepared in `|0⟩`, the
resulting quantum operation is

`E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`   (N&C eq. 8.6),

and the exercise asks for its **operator-sum representation**. The operation elements
`Eₖ = ⟨eₖ| U |e₀⟩` are exactly the projectors `E₀ = P₀`, `E₁ = P₁`, so

`E(ρ) = P₀ ρ P₀ + P₁ ρ P₁`   (N&C eq. 8.7),

with the completeness relation `E₀† E₀ + E₁† E₁ = P₀ + P₁ = I` (N&C eq. 8.14) certifying that `E`
is a trace-preserving quantum operation. Physically `E` is the completely dephasing (decoherence)
channel: it measures the system in the computational basis and discards the result. (`U` is the
controlled-`X` — CNOT — of N&C Fig. 8.4, with the principal system the control and the environment
the target.)

## Setting

The statement is in terms of linear maps on an inner product space, tensor products, an
orthonormal basis and the abstract partial trace of
`ToMathlib.Analysis.InnerProductSpace.PartialTraceAbstract`. Compare Problem 8.1
(`AxQM/Concrete/AmplitudeDampingMasterEquation.lean`). The statement of Exercise 8.4 is in
`AxQM/NC/Ch8/Exercise8_4.lean`.

## Design

The ambient qubit is an *arbitrary* two-dimensional complex inner product space `H` with a chosen
computational orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`; the projectors `qubitProj` and
the bit-flip `qubitFlip` (and their algebra) are the reusable abstract-qubit operators of
`AxQM.Concrete.QubitBasisOperators` — themselves coercions of Mathlib's
`InnerProductSpace.rankOne`. Making everything relative to `b` keeps the statement valid for every
qubit while driving the proofs entirely by the orthonormality of `b`.

The reduction to the two projectors is an application of the reusable operator-sum infrastructure
`ToMathlib.Analysis.InnerProductSpace.OperatorSum` (`LinearMap.krausOp`,
`partialTraceRight_conj_eq_sum_krausOp`): packaging `ρ ↦ U (ρ ⊗ |0⟩⟨0|) U†` as a single dilation
isometry `V = U(· ⊗ |0⟩) : H →ₗ H ⊗ H`, the operation elements are `Eₖ = krausOp b V k`, and the
only work is to compute `E₀ = P₀`, `E₁ = P₁`. `U` is self-adjoint and involutive
(`controlledFlip_comp_self`), hence unitary — the "unitary interaction" the exercise premises — and
the completeness relation is proved directly from `P₀ + P₁ = I`.
-/

open scoped TensorProduct InnerProductSpace

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H] (b : OrthonormalBasis (Fin 2) ℂ H)

/-- The **controlled-flip interaction** `U = P₀ ⊗ I + P₁ ⊗ X` (N&C eq. 8.16): a CNOT with the
principal system controlling the environment's bit-flip. -/
noncomputable def controlledFlip : H ⊗[ℂ] H →ₗ[ℂ] H ⊗[ℂ] H :=
  TensorProduct.map (qubitProj b 0) LinearMap.id + TensorProduct.map (qubitProj b 1) (qubitFlip b)

/-- `U` is self-adjoint: each summand `Pᵢ ⊗ (·)` is a tensor of self-adjoints. -/
theorem adjoint_controlledFlip : LinearMap.adjoint (controlledFlip b) = controlledFlip b := by
  rw [controlledFlip, map_add, TensorProduct.adjoint_map, TensorProduct.adjoint_map,
    adjoint_qubitProj, adjoint_qubitProj, adjoint_qubitFlip, LinearMap.adjoint_id]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- `U` is an involution: `U² = I`. The cross terms vanish (`P₀ P₁ = P₁ P₀ = 0`), the diagonal
terms use `Pᵢ² = Pᵢ` and `X² = I`, and `P₀ + P₁ = I` recombines them. -/
theorem controlledFlip_comp_self : controlledFlip b ∘ₗ controlledFlip b = LinearMap.id := by
  rw [controlledFlip, LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, qubitProj_comp_qubitProj, qubitProj_comp_qubitProj,
    qubitProj_comp_qubitProj, qubitProj_comp_qubitProj]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, LinearMap.id_comp, LinearMap.comp_id,
    TensorProduct.map_zero_left, add_zero, zero_add]
  rw [qubitFlip_comp_qubitFlip, ← TensorProduct.map_add_left, sum_qubitProj, TensorProduct.map_id]

/-- `U` is unitary: `U† U = I`. Immediate from self-adjointness and involutivity. -/
theorem adjoint_controlledFlip_comp_self :
    LinearMap.adjoint (controlledFlip b) ∘ₗ controlledFlip b = LinearMap.id := by
  rw [adjoint_controlledFlip, controlledFlip_comp_self]

/-- The **dilation** `V = U (· ⊗ |0⟩) : H →ₗ H ⊗ H`: prepare the environment in `|0⟩`, then apply
the interaction `U`. Its operation elements `krausOp b V k` are the Kraus operators of `E`. -/
noncomputable def controlledFlipDilation : H →ₗ[ℂ] H ⊗[ℂ] H :=
  controlledFlip b ∘ₗ LinearMap.embedRight b 0

/-- The **quantum operation** of Exercise 8.4, in environment form `E(ρ) = tr_env(V ρ V†)`
with `V ρ V† = U (ρ ⊗ |0⟩⟨0|) U†` (see `dephasingOperation_eq_envModel`). -/
noncomputable def dephasingOperation (ρ : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.partialTraceRight b
    (controlledFlipDilation b ∘ₗ ρ ∘ₗ LinearMap.adjoint (controlledFlipDilation b))

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **The first operation element is `P₀`:** `E₀ = ⟨0| U |0⟩ = P₀`. -/
theorem krausOp_controlledFlipDilation_zero :
    LinearMap.krausOp b (controlledFlipDilation b) 0 = qubitProj b 0 := by
  ext x
  simp only [LinearMap.krausOp_apply, controlledFlipDilation, LinearMap.comp_apply,
    LinearMap.embedRight_apply, controlledFlip, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, qubitFlip_apply_zero, map_add, LinearMap.restrictRight_tmul,
    b.inner_eq_ite]
  simp

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- **The second operation element is `P₁`:** `E₁ = ⟨1| U |0⟩ = P₁`. -/
theorem krausOp_controlledFlipDilation_one :
    LinearMap.krausOp b (controlledFlipDilation b) 1 = qubitProj b 1 := by
  ext x
  simp only [LinearMap.krausOp_apply, controlledFlipDilation, LinearMap.comp_apply,
    LinearMap.embedRight_apply, controlledFlip, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, qubitFlip_apply_zero, map_add, LinearMap.restrictRight_tmul,
    b.inner_eq_ite]
  simp

/-- **Operator-sum representation (N&C eq. 8.7):** the quantum operation of Exercise 8.4 is
`E(ρ) = P₀ ρ P₀ + P₁ ρ P₁`, the completely dephasing channel. The operation elements are the
projectors (`krausOp_controlledFlipDilation_zero`/`_one`), so this is a direct application of the
operator-sum identity `partialTraceRight_conj_eq_sum_krausOp` followed by `Pᵢ† = Pᵢ`. -/
theorem dephasingOperation_eq_operatorSum (ρ : H →ₗ[ℂ] H) :
    dephasingOperation b ρ =
      qubitProj b 0 ∘ₗ ρ ∘ₗ qubitProj b 0 + qubitProj b 1 ∘ₗ ρ ∘ₗ qubitProj b 1 := by
  unfold dephasingOperation
  rw [LinearMap.partialTraceRight_conj_eq_sum_krausOp, Fin.sum_univ_two,
    krausOp_controlledFlipDilation_zero, krausOp_controlledFlipDilation_one,
    adjoint_qubitProj, adjoint_qubitProj]

/-- **Completeness relation (N&C eq. 8.14):** the operation elements satisfy `∑ₖ Eₖ† Eₖ = I`,
here `P₀† P₀ + P₁† P₁ = P₀ + P₁ = I`, certifying `E` is trace preserving. -/
theorem sum_adjoint_krausOp_controlledFlipDilation :
    ∑ k, LinearMap.adjoint (LinearMap.krausOp b (controlledFlipDilation b) k) ∘ₗ
        LinearMap.krausOp b (controlledFlipDilation b) k = LinearMap.id := by
  rw [Fin.sum_univ_two, krausOp_controlledFlipDilation_zero, krausOp_controlledFlipDilation_one,
    adjoint_qubitProj, adjoint_qubitProj, qubitProj_comp_qubitProj b 0 0,
    qubitProj_comp_qubitProj b 1 1]
  simp only [Fin.isValue, ↓reduceIte]
  exact sum_qubitProj b

omit [CompleteSpace H] in
/-- `embed₀ ρ embed₀† = ρ ⊗ |0⟩⟨0|`: conjugating by the environment-preparation embedding realizes
the product state `ρ ⊗ |0⟩⟨0|`. -/
theorem embedRight_comp_comp_adjoint (ρ : H →ₗ[ℂ] H) :
    LinearMap.embedRight b 0 ∘ₗ ρ ∘ₗ LinearMap.adjoint (LinearMap.embedRight b 0)
      = TensorProduct.map ρ (qubitProj b 0) := by
  rw [LinearMap.adjoint_embedRight]
  refine TensorProduct.ext' fun x y => ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictRight_tmul, map_smul,
    LinearMap.embedRight_apply, TensorProduct.map_tmul, qubitProj_apply,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul]

omit [CompleteSpace H] in
/-- **Environment-model form (N&C eq. 8.6):** `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`, exhibiting
`dephasingOperation` as the quantum operation of the process "prepare the environment in `|0⟩`,
apply `U`, discard the environment". -/
theorem dephasingOperation_eq_envModel (ρ : H →ₗ[ℂ] H) :
    dephasingOperation b ρ =
      LinearMap.partialTraceRight b
        (controlledFlip b ∘ₗ TensorProduct.map ρ (qubitProj b 0)
          ∘ₗ LinearMap.adjoint (controlledFlip b)) := by
  unfold dephasingOperation
  congr 1
  rw [controlledFlipDilation, LinearMap.adjoint_comp, ← embedRight_comp_comp_adjoint]
  simp only [LinearMap.comp_assoc]

end AxQM.Concrete
