/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FourGateReachableWire
import AxQM.Concrete.CollectorZRotation

/-!
# Faithfulness of the Figure-4.19 collector `Z`-rotation as a register `Evolution`

Nielsen & Chuang **Problem 4.3(3)** — "implement `exp(-i h_g g Δ)` using `O(n)` one- and two-qubit
gates" — applies, after the `CNOT` parity fan computes the support parity onto the collector wire
`c`, a single-qubit `z`-rotation on the collector (Figure 4.19). That gate is the register
`Evolution` `rotZWireEvolution n c θ` (`Postulates/API/FourGateReachableWire.lean`), already
carrying the one-single-qubit-gate budget `rotZWireEvolution_circuitBudget`
(`Core/CnotFanEvolutionBudget.lean`). This file pins down its **operator**.

## What is formalised

* `rotZWireEvolution_op_eq_exp_smul_zGenPauli` — **faithfulness**: the operator of the collector
  `z`-rotation is exactly the Figure-4.19 collector rotation `exp(s · P_{Z_c})` of the matrix
  cascade (`Concrete/PauliStringParityCascade.lean`), reindexed from bit strings `Fin n → Fin 2`
  to the flat register `Fin (2ⁿ)` along `finFunctionFinEquiv` and promoted through
  `Matrix.toEuclideanCLM`, with scalar `s = (−θ/2) i`:

  `(rotZWireEvolution n c θ).op`
  `= Matrix.toEuclideanCLM ((exp((−θ/2) i • pauliString (zGenPauli c))).submatrix e⁻¹ e⁻¹)`.

  The operator is `Matrix.toEuclideanCLM (singleQubitOnWire e c (rotZ θ))` (`quditGate_op`);
  rewriting `rotZ θ = exp((−θ/2) i • Z)` (`Concrete.rotZ_eq_exp_smul_pauliZ`) and undoing the
  single-wire placement `Concrete.exp_smul_pauliString_zGenPauli_submatrix_eq_singleQubitOnWire`
  turns it into the reindexed collector exponential. The reindex `.submatrix e⁻¹ e⁻¹` is the
  same one `cnotFanIntoEvolution_op` uses, so this and the fan faithfulness compose under
  `Matrix.toEuclideanCLM`'s `map_mul` / `Matrix.submatrix_mul_equiv` to assemble the whole
  Figure-4.19 circuit `V† · (Z-rotation) · V` at the operator level (the part-(3) statement, in
  `AxQM/Postulates/API/PauliStringExpCircuit.lean`).

Compare `CnotFanEvolution` (the fan faithfulness it composes with) and `FourGateReachableWire`
(where `rotZWireEvolution` is defined). Physically `θ = 2 h_g Δ` gives the
`s = -i h_g Δ` of the collector rotation.
-/

open scoped InnerProductSpace

namespace AxQM

noncomputable section

/-- **Faithfulness of the collector `z`-rotation.** The operator of the register `z`-rotation
`rotZWireEvolution n c θ` on the collector wire `c` is exactly the Figure-4.19 collector rotation
`exp(s · P_{Z_c})` of the parity cascade (`Concrete/PauliStringParityCascade.lean`), reindexed from
bit strings `Fin n → Fin 2` to the flat register `Fin (2ⁿ)` along `finFunctionFinEquiv` and promoted
through `Matrix.toEuclideanCLM`, with `s = (−θ/2) i` (so `θ = 2 h_g Δ` realises `s = -i h_g Δ`):

`(rotZWireEvolution n c θ).op`
`= Matrix.toEuclideanCLM ((exp((−θ/2) i • pauliString (zGenPauli c))).submatrix
    finFunctionFinEquiv.symm finFunctionFinEquiv.symm)`.

By `quditGate_op` the operator is `Matrix.toEuclideanCLM (singleQubitOnWire finFunctionFinEquiv c
(rotZ θ))`; `Concrete.rotZ_eq_exp_smul_pauliZ` rewrites the block `rotZ θ = exp((−θ/2) i • Z)` and
`Concrete.exp_smul_pauliString_zGenPauli_submatrix_eq_singleQubitOnWire` undoes the single-wire
placement to the reindexed collector exponential. This is the collector-rotation companion of the
fan faithfulness `cnotFanIntoEvolution_op`. -/
theorem rotZWireEvolution_op_eq_exp_smul_zGenPauli (n : ℕ) (c : Fin n) (θ : ℝ) :
    (rotZWireEvolution n c θ).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n))
          ((NormedSpace.exp ((((-(θ / 2) : ℝ) : ℂ) * Complex.I) •
              Concrete.pauliString (Concrete.zGenPauli c))).submatrix
            finFunctionFinEquiv.symm finFunctionFinEquiv.symm) := by
  rw [rotZWireEvolution, quditGate_op]
  congr 1
  rw [Concrete.exp_smul_pauliString_zGenPauli_submatrix_eq_singleQubitOnWire,
    ← Concrete.rotZ_eq_exp_smul_pauliZ]

end

end AxQM
