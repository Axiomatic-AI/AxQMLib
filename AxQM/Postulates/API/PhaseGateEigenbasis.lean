/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.AxisAngleGateValues
import AxQM.Postulates.API.PhaseFlipCode

/-!
# The phase gate `S` and Pauli `Z` on the `X`- and `Y`-eigenstates

The single-qubit phase gate `S = diag(1, i)` and the Pauli `Z` gate act cleanly on the four
non-computational eigenstates `|±⟩ = (|0⟩ ± |1⟩)/√2` (`qubitPlus`, `qubitMinus`) and
`|±i⟩ = (|0⟩ ± i|1⟩)/√2` (`qubitPlusI`, `qubitMinusI`):

* `S` rotates the `X`-eigenbasis into the `Y`-eigenbasis and back a quarter turn further:
  `S|+⟩ = |+i⟩`, `S|−⟩ = |−i⟩`, `S|+i⟩ = |−⟩`, `S|−i⟩ = |+⟩` (so `S⁴ = 1` on the Bloch equator).
* `Z` swaps the `X`-eigenstates: `Z|+⟩ = |−⟩`, `Z|−⟩ = |+⟩`.

These are the `PureState`-level (`evolvePure`) truth tables, each proved at the underlying vector
level by `PureState.ext`. The two `Z` tables are a lift of the operator truth tables
`pauliZGate_op_qubitPlus`/`pauliZGate_op_qubitMinus` (`AxQM/Postulates/API/PhaseFlipCode.lean`); the
four `S` tables go through `sGate_op` on the concrete unit vectors
`Concrete.xPlus`/`xMinus`/`yPlus`/`yMinus`.

They are the single-qubit input to the two-qubit `SWAP`-conjugation identity of the
five-two-qubit-gate Fredkin construction (`AxQM/Core/FredkinFiveGateSwapIdentity.lean`, N&C
Exercise 4.25.4).
-/

open scoped InnerProductSpace

namespace AxQM

/-- **The phase gate sends `|+⟩` to `|+i⟩`:** `S|+⟩ = |+i⟩`. The `X`-eigenstate `(|0⟩ + |1⟩)/√2`
maps to the `Y`-eigenstate `(|0⟩ + i|1⟩)/√2` because `S` fixes `|0⟩` and multiplies `|1⟩` by `i`. -/
theorem sGate_evolvePure_qubitPlus : sGate.evolvePure qubitPlus = qubitPlusI := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, sGate_op, qubitPlus_vec, qubitPlusI_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.sMatrix)
        (WithLp.toLp 2 Concrete.xPlus)).ofLp = (WithLp.toLp 2 Concrete.yPlus).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.sMatrix, Concrete.xPlus, Concrete.yPlus, Matrix.mulVec, dotProduct, mul_comm]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **The phase gate sends `|−⟩` to `|−i⟩`:** `S|−⟩ = |−i⟩`. The sign-flipped companion of
`sGate_evolvePure_qubitPlus`: `S` fixes `|0⟩` and multiplies the `−|1⟩` component by `i`. -/
theorem sGate_evolvePure_qubitMinus : sGate.evolvePure qubitMinus = qubitMinusI := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, sGate_op, qubitMinus_vec, qubitMinusI_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.sMatrix)
        (WithLp.toLp 2 Concrete.xMinus)).ofLp = (WithLp.toLp 2 Concrete.yMinus).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.sMatrix, Concrete.xMinus, Concrete.yMinus, Matrix.mulVec, dotProduct, mul_comm]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **The phase gate sends `|+i⟩` to `|−⟩`:** `S|+i⟩ = |−⟩`. Continuing the quarter-turn on the
Bloch equator (`S² = Z`): the `Y`-eigenstate `(|0⟩ + i|1⟩)/√2` maps to `(|0⟩ − |1⟩)/√2` since
`S` multiplies the `i|1⟩` component by a further `i`, giving `i² = −1`. -/
theorem sGate_evolvePure_qubitPlusI : sGate.evolvePure qubitPlusI = qubitMinus := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, sGate_op, qubitPlusI_vec, qubitMinus_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.sMatrix)
        (WithLp.toLp 2 Concrete.yPlus)).ofLp = (WithLp.toLp 2 Concrete.xMinus).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.sMatrix, Concrete.yPlus, Concrete.xMinus, Matrix.mulVec, dotProduct]
    ring_nf
    simp [Complex.I_sq]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **The phase gate sends `|−i⟩` to `|+⟩`:** `S|−i⟩ = |+⟩`. The `Y`-eigenstate
`(|0⟩ − i|1⟩)/√2` maps to `(|0⟩ + |1⟩)/√2` since `S` multiplies the `−i|1⟩` component by `i`,
giving `−i² = 1`. -/
theorem sGate_evolvePure_qubitMinusI : sGate.evolvePure qubitMinusI = qubitPlus := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, sGate_op, qubitMinusI_vec, qubitPlus_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.sMatrix)
        (WithLp.toLp 2 Concrete.yMinus)).ofLp = (WithLp.toLp 2 Concrete.xPlus).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases j <;>
      simp [Concrete.sMatrix, Concrete.yMinus, Concrete.xPlus, Matrix.mulVec, dotProduct]
    ring_nf
    simp [Complex.I_sq]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **The Pauli-`Z` gate sends `|+⟩` to `|−⟩`:** `Z|+⟩ = |−⟩`, at the `PureState` level. `Z` fixes
`|0⟩` and flips the sign of `|1⟩`, exchanging the two `X`-eigenstates. A mechanical lift of the
operator truth table `pauliZGate_op_qubitPlus`. -/
theorem pauliZGate_evolvePure_qubitPlus : pauliZGate.evolvePure qubitPlus = qubitMinus := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, pauliZGate_op_qubitPlus]

/-- **The Pauli-`Z` gate sends `|−⟩` to `|+⟩`:** `Z|−⟩ = |+⟩`, at the `PureState` level. The
inverse direction of `pauliZGate_evolvePure_qubitPlus`; `Z` is its own inverse on the equator. A
mechanical lift of the operator truth table `pauliZGate_op_qubitMinus`. -/
theorem pauliZGate_evolvePure_qubitMinus : pauliZGate.evolvePure qubitMinus = qubitPlus := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, pauliZGate_op_qubitMinus]

end AxQM
