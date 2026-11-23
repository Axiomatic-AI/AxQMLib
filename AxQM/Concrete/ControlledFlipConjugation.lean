/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ControlledFlipOperatorSum

/-!
# Concrete: the ±-basis conjugation of the controlled-flip gate (toward N&C Exercise 8.28)

This file works, at the level of raw
operators on an arbitrary two-dimensional complex inner product space `H` (a qubit) with a chosen
computational orthonormal basis `b : OrthonormalBasis (Fin 2) ℂ H`, toward Nielsen & Chuang,
*Quantum Computation and Quantum Information*, **Exercise 8.28** (p. 386): a single controlled-`NOT`
gate models phase damping when the environment starts in a suitable *mixed* state.

The gate is the **controlled-flip** `U = P₀ ⊗ I + P₁ ⊗ X` of N&C eq. 8.16 — the CNOT with the
**system** (left qubit) controlling a bit-flip of the **environment** (right qubit) — already
defined and proved unitary as `AxQM.Concrete.controlledFlip` in
`Concrete/ControlledFlipOperatorSum.lean` (Exercise 8.4). This file adds the genuinely-new
structural fact that Exercise 8.28 turns on: **how conjugation by `U` acts in the `±` basis of the
environment**.

Working with the projectors `P₊ = |+⟩⟨+| = ½(I + X)` and `P₋ = |-⟩⟨-| = ½(I - X)` (the `±1`
eigenprojectors of the environment bit-flip `X`, from `Concrete/QubitBasisOperators`), the results
are:

* `controlledFlip_conj_plusProj`:  `U (ρ ⊗ P₊) U† = ρ ⊗ P₊` — the `|+⟩` environment is fixed;
* `controlledFlip_conj_minusProj`: `U (ρ ⊗ P₋) U† = (Z ρ Z) ⊗ P₋` — the `|-⟩` environment feeds
  a Pauli-`Z` back onto the system.

Physically, in the `±` basis the CNOT acts as a *controlled-`Z` from environment to system* via
phase kickback: `|+⟩` gives no kick (identity), `|-⟩` gives a `Z`. Averaging over a mixture of `|+⟩`
and `|-⟩` is exactly what produces the phase-flip = phase-damping channel; that channel identity is
assembled in `Concrete/PhaseDampingCNOTModel.lean` (Exercise 8.28, part 2).

Each two-sided conjugation is factored through the two **single-sided** actions
`U ∘ (A ⊗ P±)` and `(A ⊗ P±) ∘ U` (each a one-`U` computation via `TensorProduct.ext'`), so the
conjugation itself is a two-line rewrite using the existing self-adjointness
`adjoint_controlledFlip`.

Compare the parent gate (Exercise 8.4) and the analogous amplitude-damping circuit
(Exercise 8.20).
-/

open scoped TensorProduct InnerProductSpace

namespace AxQM.Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

variable (b : OrthonormalBasis (Fin 2) ℂ H)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- Action of the controlled-flip on a pure tensor: `U (x ⊗ y) = P₀x ⊗ y + P₁x ⊗ Xy`. -/
theorem controlledFlip_tmul (x y : H) :
    controlledFlip b (x ⊗ₜ[ℂ] y)
      = qubitProj b 0 x ⊗ₜ[ℂ] y + qubitProj b 1 x ⊗ₜ[ℂ] qubitFlip b y := by
  simp [controlledFlip, TensorProduct.map_tmul]

/-! ### The controlled-flip acting on `A ⊗ P₊` and `A ⊗ P₋` (single-sided) -/

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- Left-composing `U` with `A ⊗ |+⟩⟨+|` changes nothing: `U ∘ (A ⊗ P₊) = A ⊗ P₊`.
The environment factor `|+⟩` is a `+1`-eigenvector of `X`, so the controlled flip is invisible. -/
theorem controlledFlip_comp_map_plusProj (A : H →ₗ[ℂ] H) :
    controlledFlip b ∘ₗ TensorProduct.map A (qubitPlusProj b)
      = TensorProduct.map A (qubitPlusProj b) := by
  refine TensorProduct.ext' fun x y ↦ ?_
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, controlledFlip_tmul,
    qubitFlip_qubitPlusProj_apply, ← TensorProduct.add_tmul, qubitProj_add_apply]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- Right-composing `U` with `A ⊗ |+⟩⟨+|` changes nothing: `(A ⊗ P₊) ∘ U = A ⊗ P₊`. -/
theorem map_plusProj_comp_controlledFlip (A : H →ₗ[ℂ] H) :
    TensorProduct.map A (qubitPlusProj b) ∘ₗ controlledFlip b
      = TensorProduct.map A (qubitPlusProj b) := by
  refine TensorProduct.ext' fun x y ↦ ?_
  rw [LinearMap.comp_apply, controlledFlip_tmul, map_add, TensorProduct.map_tmul,
    TensorProduct.map_tmul, ← LinearMap.comp_apply (qubitPlusProj b), qubitPlusProj_comp_qubitFlip,
    ← TensorProduct.add_tmul, ← LinearMap.map_add, qubitProj_add_apply, TensorProduct.map_tmul]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- Left-composing `U` with `A ⊗ |-⟩⟨-|` inserts a `Z` on the system:
`U ∘ (A ⊗ P₋) = (Z A) ⊗ P₋`. The environment factor `|-⟩` picks up the `X`-eigenvalue `-1`,
i.e. a phase kick `Z` on the system. -/
theorem controlledFlip_comp_map_minusProj (A : H →ₗ[ℂ] H) :
    controlledFlip b ∘ₗ TensorProduct.map A (qubitMinusProj b)
      = TensorProduct.map (qubitPauliZ b ∘ₗ A) (qubitMinusProj b) := by
  refine TensorProduct.ext' fun x y ↦ ?_
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, controlledFlip_tmul,
    qubitFlip_qubitMinusProj_apply, TensorProduct.tmul_neg, TensorProduct.map_tmul,
    LinearMap.comp_apply, qubitPauliZ_apply, TensorProduct.sub_tmul, sub_eq_add_neg]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
/-- Right-composing `U` with `A ⊗ |-⟩⟨-|` inserts a `Z` on the system:
`(A ⊗ P₋) ∘ U = (A Z) ⊗ P₋`. -/
theorem map_minusProj_comp_controlledFlip (A : H →ₗ[ℂ] H) :
    TensorProduct.map A (qubitMinusProj b) ∘ₗ controlledFlip b
      = TensorProduct.map (A ∘ₗ qubitPauliZ b) (qubitMinusProj b) := by
  refine TensorProduct.ext' fun x y ↦ ?_
  rw [LinearMap.comp_apply, controlledFlip_tmul, map_add, TensorProduct.map_tmul,
    TensorProduct.map_tmul, qubitMinusProj_qubitFlip_apply, TensorProduct.tmul_neg,
    TensorProduct.map_tmul, LinearMap.comp_apply, qubitPauliZ_apply, LinearMap.map_sub,
    TensorProduct.sub_tmul, sub_eq_add_neg]

/-! ### The full ±-basis conjugation of the controlled-flip -/

/-- **Conjugating `ρ ⊗ |+⟩⟨+|` by the controlled-flip leaves it fixed:**
`U (ρ ⊗ P₊) U† = ρ ⊗ P₊`. -/
theorem controlledFlip_conj_plusProj (ρ : H →ₗ[ℂ] H) :
    controlledFlip b ∘ₗ TensorProduct.map ρ (qubitPlusProj b)
        ∘ₗ LinearMap.adjoint (controlledFlip b)
      = TensorProduct.map ρ (qubitPlusProj b) := by
  rw [adjoint_controlledFlip, map_plusProj_comp_controlledFlip, controlledFlip_comp_map_plusProj]

/-- **Conjugating `ρ ⊗ |-⟩⟨-|` by the controlled-flip turns `ρ` into `Z ρ Z`:**
`U (ρ ⊗ P₋) U† = (Z ρ Z) ⊗ P₋`. This is the phase kickback that yields the phase flip. -/
theorem controlledFlip_conj_minusProj (ρ : H →ₗ[ℂ] H) :
    controlledFlip b ∘ₗ TensorProduct.map ρ (qubitMinusProj b)
        ∘ₗ LinearMap.adjoint (controlledFlip b)
      = TensorProduct.map (qubitPauliZ b ∘ₗ ρ ∘ₗ qubitPauliZ b) (qubitMinusProj b) := by
  rw [adjoint_controlledFlip, map_minusProj_comp_controlledFlip, controlledFlip_comp_map_minusProj]

end AxQM.Concrete
