/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ReflectionQubit
import AxQM.Postulates.API.ThreeQubitBitFlipCode

/-!
# The density matrix of a single-qubit superposition

This file identifies the density operator of a general
single-qubit pure state `a|0⟩ + b|1⟩` (`qubitSuperposition`) with the concrete outer-product matrix
`|v⟩⟨v| = Concrete.outerSelf ![a, b]` promoted through `Matrix.toEuclideanCLM`. It is the qubit
analogue of `blochPureState_toState_op`, phrased for the amplitude parametrisation rather than the
Bloch-angle one, and is used in ensemble computations such as Nielsen & Chuang's
Exercise 12.4 (`AxQM/NC/Ch12/Exercise12_4.lean`).
-/

open Complex Matrix

namespace AxQM

/-- The plain-coordinate vector `WithLp.ofLp (a•|0⟩ + b•|1⟩)` of a two-amplitude qubit superposition
is `![a, b]`. A normalisation lemma feeding `qubitSuperposition_toState_op`; stated at
the `EuclideanSpace ℂ (Fin 2)` type so the `WithLp.ofLp`/`EuclideanSpace.single` simp set fires. -/
private theorem ofLp_qubitAmplitude (a b : ℂ) :
    WithLp.ofLp (a • EuclideanSpace.single 0 1 + b • EuclideanSpace.single 1 1
      : EuclideanSpace ℂ (Fin 2)) = ![a, b] := by
  funext i
  fin_cases i <;> simp [EuclideanSpace.single]

/-- **The density operator of `a|0⟩ + b|1⟩` is
`Matrix.toEuclideanCLM (Concrete.outerSelf ![a, b])`.**
For amplitudes `a, b : ℂ` with `‖a‖² + ‖b‖² = 1`, the rank-one projector `|ψ⟩⟨ψ|` of the qubit
superposition `qubitSuperposition a b h` is the concrete `2 × 2` outer product `![a, b]·![a, b]†`
promoted to the qubit space. Proof: unfold `.toState.op` to the rank-one operator
(`PureState.toState_op`), apply the general rank-one/outer-product bridge
(`rankOne_self_eq_toEuclideanCLM_outerSelf`), and evaluate the underlying coordinate vector with
`ofLp_qubitAmplitude`. -/
theorem qubitSuperposition_toState_op (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    (qubitSuperposition a b h).toState.op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.outerSelf ![a, b]) := by
  have hV : (qubitSuperposition a b h).vec.ofLp = ![a, b] := ofLp_qubitAmplitude a b
  rw [PureState.toState_op]
  refine (rankOne_self_eq_toEuclideanCLM_outerSelf (qubitSuperposition a b h).vec).trans ?_
  rw [hV]

/-- **The transition amplitude between two single-qubit superpositions is `⟨ψ|φ⟩ = ā·c + b̄·d`.**
For `ψ = a|0⟩ + b|1⟩` and `φ = c|0⟩ + d|1⟩`, the Hilbert-space inner product `⟪ψ.vec, φ.vec⟫`
evaluates to `conj a · c + conj b · d`, by expanding over the computational basis
(`qubitSuperposition_vec`) and using its orthonormality (`qubitBasis_inner_qubitBasis`). Used
for reading off qubit overlaps from amplitudes (e.g. the SIC overlaps of
`AxQM/NC/Ch12/Exercise12_4.lean`). -/
theorem qubitSuperposition_inner (a b c d : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1)
    (h' : ‖c‖ ^ 2 + ‖d‖ ^ 2 = 1) :
    inner ℂ (qubitSuperposition a b h).vec (qubitSuperposition c d h').vec
      = (starRingEnd ℂ) a * c + (starRingEnd ℂ) b * d := by
  rw [qubitSuperposition_vec, qubitSuperposition_vec]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    qubitBasis_inner_qubitBasis]
  norm_num
  ring

end AxQM
