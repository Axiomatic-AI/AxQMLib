/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QftHadamardEvolution
import AxQM.Postulates.API.PiEighthGate
import AxQM.Postulates.API.HadamardRotation
import AxQM.Concrete.Rotation
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# The reachable single-qubit rotations on a register wire
(N&C Exercise 4.43, four-gate bridge — register-side ingredients)

The four-gate universality bridge (Exercise 4.43) must exhibit the *abstract* reachable gate set of
`Concrete.exists_phase_smul_mem_closure_reachableCircuits` as circuits of the grounded
`H, S, CNOT, Toffoli` gates. Its single-qubit stage
(`AxQM/Postulates/API/FourGateReachableRotation.lean`) showed each reachable rotation *matrix*
`g ∈ Concrete.reachableRotations θ` is the operator of a reachable rotation *gate*
`E ∈ reachableRotationGates θ` — a finite `{H, S}`-composition around the measurement-realised
`R_z(θ)`. But the reachable gate set uses those rotations placed on an individual **wire** of the
`m`-qubit register, via `Concrete.singleQubitOnWire enc j g`. This file supplies the *register-side*
ingredients that let the tower re-expression (`AxQM/Core/FourGateReachableWireTower.lean`)
identify such a wire gate with the grounded rotation gate placed on that wire — exactly mirroring
the QFT Hadamard layer's `qftHadamardEvolution` / `AxQM/Core/QftTowerHadamard.lean` development.

## What is formalised

For the `z`- and `x`-axis reachable rotations (the generators of `Concrete.reachableRotations θ`):

* `rotZWireEvolution n t θ` / `rotXWireEvolution n t θ` — the rotation `R_z(θ)` / `R_x(θ)` placed on
  wire `t` of the `2ⁿ`-level register, as a named `Evolution (qudit (2ⁿ))`: the `quditGate`
  promotion of the gate matrix `singleQubitOnWire finFunctionFinEquiv t (rotZ θ)` (resp. `rotX θ`).
  The direct analogue of `qftHadamardEvolution n t`, with the Hadamard block replaced by a
  reachable rotation.
* `rotZWireEvolution_evolvePure_quditBasis` / `rotXWireEvolution_evolvePure_quditBasis` — their
  **computational-basis action**: on `|finFunctionFinEquiv f⟩` the wire-`t` component is mixed
  through the rotation's column, `∑_z (rotZ θ) z (f t) · |finFunctionFinEquiv (update f t z)⟩`.
  Instances of the reusable bridge `quditGate_singleQubitOnWire_evolvePure_quditBasis` at
  `G = rotZ θ` (resp. `rotX θ`).
* `rotZGate_evolvePure_qubitBasis_sum` / `rotXGate_evolvePure_qubitBasis_sum` — the **single-qubit
  companions**: the one-qubit gate `rotZGate θ` (resp. `rotXGate θ`) acts on a basis state `|z⟩` as
  its rotation-matrix column, `rotZGate θ |z⟩ = ∑_w (rotZ θ) w z · |w⟩`. The `d = 2` case of the
  column action `Matrix.toEuclideanCLM_apply_single`, read through `rotZGate_op` (resp.
  `rotXGate_op`). These are the single-wire factors the tower re-expression matches the register
  superposition against.

-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The reachable `z`-rotation on a register wire.** The rotation `R_z(θ)` placed on wire `t` of
the `2ⁿ`-level register, as a named `Evolution (qudit (2ⁿ))`: the `quditGate` promotion of the gate
matrix `singleQubitOnWire finFunctionFinEquiv t (rotZ θ)` (unitary, so `quditGate` applies). Its
It is used in the tower re-expression (`AxQM/Core/FourGateReachableWireTower.lean`); its basis
action is `rotZWireEvolution_evolvePure_quditBasis`. The direct analogue of
`qftHadamardEvolution n t` with the Hadamard block replaced by `R_z(θ)`. -/
def rotZWireEvolution (n : ℕ) (t : Fin n) (θ : ℝ) : Evolution (qudit (2 ^ n)) :=
  quditGate (singleQubitOnWire_mem_unitaryGroup finFunctionFinEquiv t (rotZ_mem_unitaryGroup θ))

/-- **The reachable `x`-rotation on a register wire.** The rotation `R_x(θ)` placed on wire `t` of
the `2ⁿ`-level register, as a named `Evolution (qudit (2ⁿ))`: the `quditGate` promotion of
`singleQubitOnWire finFunctionFinEquiv t (rotX θ)`. The `x`-axis counterpart of
`rotZWireEvolution`; its basis action is `rotXWireEvolution_evolvePure_quditBasis`. -/
def rotXWireEvolution (n : ℕ) (t : Fin n) (θ : ℝ) : Evolution (qudit (2 ^ n)) :=
  quditGate (singleQubitOnWire_mem_unitaryGroup finFunctionFinEquiv t (rotX_mem_unitaryGroup θ))

/-- **The wire-`t` `z`-rotation mixes wire `t` through the `R_z(θ)` column.**
`rotZWireEvolution n t θ |finFunctionFinEquiv f⟩ = ∑_z (rotZ θ) z (f t) · |finFunctionFinEquiv
(update f t z)⟩`: the bit-string `f` addressing the wires has its wire-`t` component rotated, the
two branches carrying amplitudes `(rotZ θ) z (f t)`. The instance of the reusable bridge
`quditGate_singleQubitOnWire_evolvePure_quditBasis` at `G = rotZ θ`, `enc = finFunctionFinEquiv`. -/
theorem rotZWireEvolution_evolvePure_quditBasis (n : ℕ) (t : Fin n) (θ : ℝ) (f : Fin n → Fin 2) :
    ((rotZWireEvolution n t θ).evolvePure (quditBasis (finFunctionFinEquiv f))).vec
      = ∑ z : Fin 2, rotZ θ z (f t) •
          (quditBasis (finFunctionFinEquiv (Function.update f t z))).vec :=
  quditGate_singleQubitOnWire_evolvePure_quditBasis finFunctionFinEquiv t
    (rotZ_mem_unitaryGroup θ) f

/-- **The wire-`t` `x`-rotation mixes wire `t` through the `R_x(θ)` column.**
`rotXWireEvolution n t θ |finFunctionFinEquiv f⟩ = ∑_z (rotX θ) z (f t) · |finFunctionFinEquiv
(update f t z)⟩`. The `x`-axis instance of `quditGate_singleQubitOnWire_evolvePure_quditBasis`. -/
theorem rotXWireEvolution_evolvePure_quditBasis (n : ℕ) (t : Fin n) (θ : ℝ) (f : Fin n → Fin 2) :
    ((rotXWireEvolution n t θ).evolvePure (quditBasis (finFunctionFinEquiv f))).vec
      = ∑ z : Fin 2, rotX θ z (f t) •
          (quditBasis (finFunctionFinEquiv (Function.update f t z))).vec :=
  quditGate_singleQubitOnWire_evolvePure_quditBasis finFunctionFinEquiv t
    (rotX_mem_unitaryGroup θ) f

/-- **The qubit `z`-rotation acts as its matrix column.** On a computational-basis state `|z⟩` the
one-qubit gate `rotZGate θ` produces the superposition `∑_w (rotZ θ) w z · |w⟩`. The `d = 2` case of
the column action `Matrix.toEuclideanCLM_apply_single`, read through `rotZGate_op` and
`qubitBasis_vec`. The single-wire factor the tower re-expression of the wire `z`-rotation
(`AxQM/Core/FourGateReachableWireTower.lean`) matches the register superposition
`rotZWireEvolution_evolvePure_quditBasis` against. -/
theorem rotZGate_evolvePure_qubitBasis_sum (θ : ℝ) (z : Fin 2) :
    ((rotZGate θ).evolvePure (qubitBasis z)).vec
      = ∑ w : Fin 2, rotZ θ w z • (qubitBasis w).vec := by
  rw [Evolution.evolvePure_vec, rotZGate_op, qubitBasis_vec]
  refine (Matrix.toEuclideanCLM_apply_single (rotZ θ) z).trans (Finset.sum_congr rfl fun w _ => ?_)
  exact congrArg (rotZ θ w z • ·) (qubitBasis_vec w).symm

/-- **The qubit `x`-rotation acts as its matrix column.** On `|z⟩` the one-qubit gate `rotXGate θ`
produces `∑_w (rotX θ) w z · |w⟩`. The `x`-axis counterpart of `rotZGate_evolvePure_qubitBasis_sum`,
read through `rotXGate_op`. -/
theorem rotXGate_evolvePure_qubitBasis_sum (θ : ℝ) (z : Fin 2) :
    ((rotXGate θ).evolvePure (qubitBasis z)).vec
      = ∑ w : Fin 2, rotX θ w z • (qubitBasis w).vec := by
  rw [Evolution.evolvePure_vec, rotXGate_op, qubitBasis_vec]
  refine (Matrix.toEuclideanCLM_apply_single (rotX θ) z).trans (Finset.sum_congr rfl fun w _ => ?_)
  exact congrArg (rotX θ w z • ·) (qubitBasis_vec w).symm

end

end AxQM
