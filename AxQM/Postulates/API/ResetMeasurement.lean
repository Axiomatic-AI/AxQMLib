/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qubit
import AxQM.Postulates.API.ProjectiveMeasurement

/-!
# The reset measurement `{|0⟩⟨0|, |0⟩⟨1|}` (Nielsen & Chuang, Exercise 11.15)

The generalized measurement on a qubit with operators `M₀ = |0⟩⟨0|` and `M₁ = |0⟩⟨1|`
(N&C Exercise 11.15, p. 515), given as the `Measurement` structure carrying the operators
together with the completeness proof `M₀† M₀ + M₁† M₁ = I`. The
physics worked in Exercise 11.15 (its unread-measurement channel resets every state to `|0⟩⟨0|`,
strictly decreasing entropy) is stated in `AxQM/NC/Ch11/Exercise11_15.lean`.

Both operators send everything onto the computational ket `|0⟩`, so uniformly
`Mᵢ = |0⟩⟨i| = rankOne |0⟩ |i⟩`; hence they are recorded with a single `op i` formula.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The reset measurement `{M₀ = |0⟩⟨0|, M₁ = |0⟩⟨1|}` (N&C Exercise 11.15).** Uniformly
`Mᵢ = |0⟩⟨i| = rankOne |0⟩ |i⟩`. The completeness relation `Σᵢ Mᵢ† Mᵢ = |0⟩⟨0| + |1⟩⟨1| = I` is the
resolution of the identity in the computational basis (`OrthonormalBasis.sum_rankOne_eq_id`), each
term simplifying by `Mᵢ† Mᵢ = |i⟩⟨0|·|0⟩⟨i| = ⟨0|0⟩ · |i⟩⟨i| = |i⟩⟨i|`. `M₁ = |0⟩⟨1|` is not
self-adjoint, so this is a genuine *generalized* measurement, not a projective one. -/
def resetMeasurement : Measurement (Fin 2) qubit where
  op i := rankOne ℂ (qubitBasis 0).vec (qubitBasis i).vec
  complete := by
    set b : OrthonormalBasis (Fin 2) ℂ qubit.space := EuclideanSpace.basisFun (Fin 2) ℂ with hb
    have hbv : ∀ i, (qubitBasis i).vec = b i := fun i => by
      rw [qubitBasis_vec]; exact (EuclideanSpace.basisFun_apply (Fin 2) ℂ i).symm
    have h00 : (inner ℂ (b 0) (b 0) : ℂ) = 1 := by simp
    simp only [hbv, adjoint_rankOne, rankOne_comp_rankOne, h00, one_smul]
    rw [b.sum_rankOne_eq_id, ContinuousLinearMap.one_def]

/-- The measurement operators of `resetMeasurement` are `Mᵢ = |0⟩⟨i| = rankOne |0⟩ |i⟩`. -/
theorem resetMeasurement_op (i : Fin 2) :
    resetMeasurement.op i = rankOne ℂ (qubitBasis 0).vec (qubitBasis i).vec := rfl

end AxQM
