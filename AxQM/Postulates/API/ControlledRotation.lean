/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardABC
import AxQM.Postulates.API.HadamardRotation
import AxQM.Concrete.RotationDecompositionXY

/-!
# AxQM.Postulates.API — gate-level rotation algebra for controlled rotations

Gate-level lifts of the concrete single-qubit rotation identities, used to assemble
the controlled rotation gates of Nielsen & Chuang §4.3 (Exercise 4.23). Each lemma promotes a matrix
identity from `Concrete/` to the corresponding `Evolution qubit` gate through the `⋆`-algebra
isomorphism `Matrix.toEuclideanCLM` (multiplicative and sending `1 ↦ 1`), so the reasoning about
controlled rotations can stay entirely at the gate level.

## What is formalised

The `R_y` and `R_z` gate families each get the same three algebra lemmas — the group law
(`rotYGate_comp`/`rotZGate_comp`, images of `Concrete.rotY_mul_rotY`/`rotZ_mul_rotZ`), the identity
value at `0` (`rotYGate_zero`/`rotZGate_zero`), and the `X`-conjugation
(`pauliXGate_comp_rotYGate_comp_pauliXGate`/`pauliXGate_comp_rotZGate_comp_pauliXGate`, images of
`Concrete.pauliX_mul_rotY_mul_pauliX`/`pauliX_mul_rotZ_mul_pauliX`, N&C Exercise 4.7). In addition:

* `hadamardGate_comp_rotZGate_comp_hadamardGate` — the Hadamard basis change
  `H · R_z(θ) · H = R_x(θ)` at the gate level (image of `Concrete.hadamardC_mul_rotZ_mul_hadamardC`,
  since `H Z H = X`). This is what lets controlled-`R_x` be built from controlled-`R_z`.
* `controlledUnitary_rotZGate` — the reduced controlled-`R_z` construction
  `C(R_z(θ)) = (1 ⊗ R_z(θ/2)) · CNOT · (1 ⊗ R_z(-θ/2)) · CNOT`, the `R_z` analogue of
  `controlledUnitary_rotYGate`, obtained from `controlledUnitary_cnot_conj_cnot`. It is the helper
  behind the controlled-`R_x` construction (N&C Exercise 4.23, `NC/Ch4/Exercise4_23.lean`).

The `R_y`/`R_z` algebra is the reason the reduction to two single-qubit gates works for these axes:
with `A = R_a(θ/2)`, `B = R_a(-θ/2)`, `A · B = R_a(0) = I` and
`A · X · B · X = R_a(θ/2) · (X R_a(-θ/2) X) = R_a(θ/2) R_a(θ/2) = R_a(θ)`, so
`controlledUnitary_cnot_conj_cnot` yields `C(R_a(θ))` from just `A`, `B` and two `CNOT`s. (The same
does not hold for `R_x`, which commutes with `X`; controlled-`R_x` instead goes through the Hadamard
basis change above.)

## Design notes

* **Proof shape.** `Evolution.ext` reduces each gate equation to its underlying operators; `comp_op`
  turns `Evolution.comp` into `ContinuousLinearMap.comp`. The concrete matrix identity is pulled
  through `Matrix.toEuclideanCLM` with `map_mul`/`map_one`; the residual
  `ContinuousLinearMap.comp` vs `*` gap closes by `rfl` (they are definitionally the algebra
  product).
-/

noncomputable section

namespace AxQM

/-- **The `y`-rotation gates form a one-parameter group:** `R_y(a) · R_y(b) = R_y(a + b)` as gates
on the qubit. The gate-level image of `Concrete.rotY_mul_rotY` under `Matrix.toEuclideanCLM`. -/
theorem rotYGate_comp (a b : ℝ) : (rotYGate a).comp (rotYGate b) = rotYGate (a + b) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, rotYGate_op]
  rw [← Concrete.rotY_mul_rotY a b, map_mul]
  rfl

/-- **`R_y(0)` is the identity gate.** The gate-level image of `Concrete.rotY_zero`. -/
theorem rotYGate_zero : rotYGate 0 = Evolution.id := by
  apply Evolution.ext
  rw [rotYGate_op, Concrete.rotY_zero, map_one]
  rfl

/-- **Conjugating `R_y(θ)` by `X` negates its angle:** `X · R_y(θ) · X = R_y(-θ)` at the gate level
(Nielsen & Chuang, Exercise 4.7). The gate-level image of `Concrete.pauliX_mul_rotY_mul_pauliX`. -/
theorem pauliXGate_comp_rotYGate_comp_pauliXGate (θ : ℝ) :
    pauliXGate.comp ((rotYGate θ).comp pauliXGate) = rotYGate (-θ) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, pauliXGate_op, rotYGate_op]
  rw [← Concrete.pauliX_mul_rotY_mul_pauliX θ, map_mul, map_mul, mul_assoc]
  rfl

/-- **The `z`-rotation gates form a one-parameter group:** `R_z(a) · R_z(b) = R_z(a + b)` as gates
on the qubit. The gate-level image of `Concrete.rotZ_mul_rotZ` under `Matrix.toEuclideanCLM`. -/
theorem rotZGate_comp (a b : ℝ) : (rotZGate a).comp (rotZGate b) = rotZGate (a + b) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, rotZGate_op]
  rw [← Concrete.rotZ_mul_rotZ a b, map_mul]
  rfl

/-- **`R_z(0)` is the identity gate.** The gate-level image of `Concrete.rotZ_zero`. -/
theorem rotZGate_zero : rotZGate 0 = Evolution.id := by
  apply Evolution.ext
  rw [rotZGate_op, Concrete.rotZ_zero, map_one]
  rfl

/-- **Conjugating `R_z(θ)` by `X` negates its angle:** `X · R_z(θ) · X = R_z(-θ)` at the gate level
(Nielsen & Chuang, Exercise 4.7). The gate-level image of `Concrete.pauliX_mul_rotZ_mul_pauliX`. -/
theorem pauliXGate_comp_rotZGate_comp_pauliXGate (θ : ℝ) :
    pauliXGate.comp ((rotZGate θ).comp pauliXGate) = rotZGate (-θ) := by
  apply Evolution.ext
  simp only [Evolution.comp_op, pauliXGate_op, rotZGate_op]
  rw [← Concrete.pauliX_mul_rotZ_mul_pauliX θ, map_mul, map_mul, mul_assoc]
  rfl

/-- **The Hadamard basis change `H · R_z(θ) · H = R_x(θ)`** at the gate level: since `H Z H = X`,
conjugating a `z`-rotation by the Hadamard gate turns it into the corresponding `x`-rotation. The
gate-level image of `Concrete.hadamardC_mul_rotZ_mul_hadamardC`. It converts the controlled-`R_z`
construction into a controlled-`R_x` construction (N&C Exercise 4.23). -/
theorem hadamardGate_comp_rotZGate_comp_hadamardGate (θ : ℝ) :
    hadamardGate.comp ((rotZGate θ).comp hadamardGate) = rotXGate θ := by
  apply Evolution.ext
  simp only [Evolution.comp_op, hadamardGate_op, rotZGate_op, rotXGate_op]
  rw [← Concrete.hadamardC_mul_rotZ_mul_hadamardC θ, map_mul, map_mul, mul_assoc]
  rfl

/-- **The reduced controlled-`R_z` construction** (the `R_z` analogue of
`controlledUnitary_rotYGate`, N&C Exercise 4.23):
`C(R_z(θ)) = (1 ⊗ R_z(θ/2)) · CNOT · (1 ⊗ R_z(-θ/2)) · CNOT`, using two single-qubit gates and two
`CNOT`s (`R_z`, like `R_y`, has its axis perpendicular to `X`). Obtained by instantiating
`controlledUnitary_cnot_conj_cnot` at `V = R_z(θ/2)`, `W = R_z(-θ/2)` and collapsing
`R_z(θ/2) · X · R_z(-θ/2) · X` to `R_z(θ)`. This is the helper behind the controlled-`R_x`
construction. -/
theorem controlledUnitary_rotZGate (θ : ℝ) :
    controlledUnitary (rotZGate θ)
      = (((rotZGate (θ / 2)).onRight qubit).comp cnotGate).comp
          (((rotZGate (-(θ / 2))).onRight qubit).comp cnotGate) := by
  have hVW : (rotZGate (θ / 2)).comp (rotZGate (-(θ / 2))) = Evolution.id := by
    rw [rotZGate_comp, add_neg_cancel, rotZGate_zero]
  rw [controlledUnitary_cnot_conj_cnot (rotZGate (θ / 2)) (rotZGate (-(θ / 2))) hVW]
  congr 1
  rw [pauliXGate_comp_rotZGate_comp_pauliXGate, neg_neg, rotZGate_comp, add_halves]

end AxQM
