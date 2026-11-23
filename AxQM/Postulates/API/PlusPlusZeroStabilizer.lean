/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliMeasurement
import AxQM.Postulates.API.CompositeState
import AxQM.Postulates.API.CnotPauliPropagation

/-!
# The product state `|+⟩|+⟩|0⟩` is the unique common `+1` eigenstate of `X₁, X₂, Z₃`

This lemma says the three-qubit product state `|+⟩|+⟩|0⟩` on
`qubit ⊗ (qubit ⊗ qubit)` is the **unique** common `+1` eigenstate — up to a global phase — of the
three disjoint single-qubit Pauli operators `X₁` (on the first qubit), `X₂` (on the second) and
`Z₃` (on the third). "Up to a global phase" is rendered, as everywhere in the library, as the
equality of density operators `PureState.toState` (which erases the phase).

It is the completeness half of a stabilizer verification: measuring `X₁, X₂, Z₃` and post-selecting
the all-`+1` outcome prepares exactly `|+⟩|+⟩|0⟩`. Nielsen & Chuang Exercise 10.72 uses it, via the
Toffoli conjugation, to show the Toffoli-ancilla stabilizer generators pin `|Θ_T⟩`
(`AxQM/NC/Ch10/Exercise10_72_ToffoliAncilla.lean`, `toffoliAncilla_eq_of_stabilized`).

## Proof

The joint `+1` eigenprojector of the three disjoint Paulis is the tensor product of the single-qubit
`+1` eigenprojectors `P₊(X) = |+⟩⟨+|` and `P₊(Z) = |0⟩⟨0|`
(`pauliXObservable_projPlus_rankOne`, `pauliZObservable_projPlus_rankOne`); that tensor product is
the rank-one projector `|Θ⟩⟨Θ|` onto `Θ = |+⟩|+⟩|0⟩`, recognised through the density operator
factoring over the tensor product (`PureState.toState_op`, `PureState.toState_tmul`,
`State.tmul_op`). Each `Pᵢ` fixing a state `φ` makes its projector `½(1 + Pᵢ)` fix `φ` too, so the
composite `|Θ⟩⟨Θ|` fixes `φ`; hence `φ` is a scalar multiple of `Θ`, of unit modulus since both are
unit vectors, so the density operators coincide (`PureState.toState_eq_of_vec_eq_smul`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **`|+⟩|+⟩|0⟩` is the unique common `+1` eigenstate of `X₁, X₂, Z₃`** (up to a global phase). Any
pure state `φ` on `qubit ⊗ (qubit ⊗ qubit)` fixed by `X` on the first qubit, `X` on the second, and
`Z` on the third equals `|+⟩|+⟩|0⟩` up to a global phase (`φ.toState = (|+⟩|+⟩|0⟩).toState`, the
density-operator equality that erases the phase). The three single-qubit `+1` eigenprojectors are
`P₊(X) = |+⟩⟨+|` and `P₊(Z) = |0⟩⟨0|` (`pauliXObservable_projPlus_rankOne`,
`pauliZObservable_projPlus_rankOne`); their tensor product is the rank-one projector `|Θ⟩⟨Θ|` onto
`Θ = |+⟩|+⟩|0⟩`, recognised via the density operator factoring over the tensor product
(`PureState.toState_op`, `PureState.toState_tmul`, `State.tmul_op`). Each `Pᵢ` fixing `φ` makes its
projector `½(1 + Pᵢ)` fix `φ` too, so the composite `|Θ⟩⟨Θ|` fixes `φ`; hence `φ` is a scalar
multiple of `Θ`, of unit modulus since both are unit vectors, so the density operators coincide
(`PureState.toState_eq_of_vec_eq_smul`). -/
theorem qubitPlusPlusZero_eq_of_stabilized
    (φ : PureState (qubit ⊗ (qubit ⊗ qubit)))
    (hX1 : (pauliXGate.onLeft (qubit ⊗ qubit)).HasEigenstate 1 φ)
    (hX2 : ((pauliXGate.onLeft qubit).onRight qubit).HasEigenstate 1 φ)
    (hZ3 : ((pauliZGate.onRight qubit).onRight qubit).HasEigenstate 1 φ) :
    φ.toState = (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)).toState := by
  -- The three stabilizer conditions as "single-qubit Pauli ⊗ identity fixes φ.vec".
  have e1 : (TensorProduct.mapL pauliXObservable.op
      (1 : (qubit.space ⊗[ℂ] qubit.space) →L[ℂ] (qubit.space ⊗[ℂ] qubit.space))) φ.vec
      = φ.vec := by
    have h : (pauliXGate.onLeft (qubit ⊗ qubit)).op φ.vec = (1 : ℂ) • φ.vec := hX1
    rwa [Evolution.onLeft_op, pauliXGate_op, ← pauliXObservable_op, one_smul] at h
  have e2 : (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
      (TensorProduct.mapL pauliXObservable.op (1 : qubit.space →L[ℂ] qubit.space))) φ.vec
      = φ.vec := by
    have h : ((pauliXGate.onLeft qubit).onRight qubit).op φ.vec = (1 : ℂ) • φ.vec := hX2
    rwa [Evolution.onRight_op, Evolution.onLeft_op, pauliXGate_op, ← pauliXObservable_op,
      one_smul] at h
  have e3 : (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
      (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) pauliZObservable.op)) φ.vec
      = φ.vec := by
    have h : ((pauliZGate.onRight qubit).onRight qubit).op φ.vec = (1 : ℂ) • φ.vec := hZ3
    rwa [Evolution.onRight_op, Evolution.onRight_op, pauliZGate_op, ← pauliZObservable_op,
      one_smul] at h
  -- Each single-qubit `+1` eigenprojector `½(1 + P)`, tensored with identities, fixes φ.vec.
  -- Stated over the generic tensor-product space, so the rewrites are not blocked by the bundled
  -- `(qubit ⊗ qubit ⊗ qubit).space` instances; each `pᵢ` closes by `exact`, up to defeq.
  have hfix : ∀ (Q : qubit.space ⊗[ℂ] (qubit.space ⊗[ℂ] qubit.space) →L[ℂ]
        qubit.space ⊗[ℂ] (qubit.space ⊗[ℂ] qubit.space))
      (w : qubit.space ⊗[ℂ] (qubit.space ⊗[ℂ] qubit.space)),
      Q w = w → ((2⁻¹ : ℂ) • (1 + Q)) w = w := by
    intro Q w hw
    simp only [smul_apply, add_apply,
      one_apply_eq_self, hw]
    module
  have p1 : (TensorProduct.mapL pauliXObservable.projPlus
      (1 : (qubit.space ⊗[ℂ] qubit.space) →L[ℂ] (qubit.space ⊗[ℂ] qubit.space))) φ.vec
      = φ.vec := by
    rw [Observable.projPlus, TensorProduct.mapL_smul_left, TensorProduct.mapL_add_left,
      TensorProduct.mapL_one]
    exact hfix _ _ e1
  have p2 : (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
      (TensorProduct.mapL pauliXObservable.projPlus (1 : qubit.space →L[ℂ] qubit.space))) φ.vec
      = φ.vec := by
    rw [Observable.projPlus, TensorProduct.mapL_smul_left, TensorProduct.mapL_add_left,
      TensorProduct.mapL_one, TensorProduct.mapL_smul_right, TensorProduct.mapL_add_right,
      TensorProduct.mapL_one]
    exact hfix _ _ e2
  have p3 : (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
      (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) pauliZObservable.projPlus)) φ.vec
      = φ.vec := by
    rw [Observable.projPlus, TensorProduct.mapL_smul_right, TensorProduct.mapL_add_right,
      TensorProduct.mapL_one, TensorProduct.mapL_smul_right, TensorProduct.mapL_add_right,
      TensorProduct.mapL_one]
    exact hfix _ _ e3
  -- The joint `+1` eigenprojector is the rank-one projector `|Θ⟩⟨Θ|` onto `Θ = |+⟩|+⟩|0⟩`.
  have hrank : (InnerProductSpace.rankOne ℂ (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)).vec)
      (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)).vec
      = TensorProduct.mapL pauliXObservable.projPlus
          (TensorProduct.mapL pauliXObservable.projPlus pauliZObservable.projPlus) := by
    rw [← PureState.toState_op, PureState.toState_tmul, PureState.toState_tmul,
      State.tmul_op, State.tmul_op]
    simp only [PureState.toState_op, ← pauliXObservable_projPlus_rankOne,
      ← pauliZObservable_projPlus_rankOne]
    rfl
  -- `φ.vec` is fixed by the joint projector `|Θ⟩⟨Θ|` (composite of the three factor projectors).
  have hfix : (InnerProductSpace.rankOne ℂ (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)).vec)
      (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)).vec φ.vec = φ.vec := by
    rw [hrank]
    -- Factor the joint projector into the three commuting single-factor projectors and peel them.
    have hop : TensorProduct.mapL pauliXObservable.projPlus
          (TensorProduct.mapL pauliXObservable.projPlus pauliZObservable.projPlus)
        = (TensorProduct.mapL pauliXObservable.projPlus
              (1 : (qubit.space ⊗[ℂ] qubit.space) →L[ℂ] (qubit.space ⊗[ℂ] qubit.space))).comp
            ((TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
                (TensorProduct.mapL pauliXObservable.projPlus
                  (1 : qubit.space →L[ℂ] qubit.space))).comp
              (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
                (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
                  pauliZObservable.projPlus))) := by
      simp only [← ContinuousLinearMap.mul_def, ← TensorProduct.mapL_mul, mul_one, one_mul]
    rw [hop]
    -- `comp` application is definitionally nested application; peel the three projectors.
    change (TensorProduct.mapL pauliXObservable.projPlus
          (1 : (qubit.space ⊗[ℂ] qubit.space) →L[ℂ] (qubit.space ⊗[ℂ] qubit.space)))
        ((TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
            (TensorProduct.mapL pauliXObservable.projPlus (1 : qubit.space →L[ℂ] qubit.space)))
          ((TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space)
              (TensorProduct.mapL (1 : qubit.space →L[ℂ] qubit.space) pauliZObservable.projPlus))
            φ.vec)) = φ.vec
    rw [p3, p2, p1]
  rw [InnerProductSpace.rankOne_apply] at hfix
  -- `φ = c • Θ` with `‖c‖ = 1` (both unit vectors), so the density operators coincide.
  refine PureState.toState_eq_of_vec_eq_smul ?_ hfix.symm
  have hc := congrArg norm hfix
  rwa [norm_smul, (qubitPlus ⊗ (qubitPlus ⊗ qubitBasis 0)).normalized, mul_one,
    φ.normalized] at hc

end AxQM
