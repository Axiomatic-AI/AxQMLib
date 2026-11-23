/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.HadamardABC

/-!
# Nielsen & Chuang, Exercise 4.12 — `A`, `B`, `C`, `α` for the Hadamard gate

*(N&C p. 176.)*

Give A,B,C and alpha for the Hadamard gate in the ABC decomposition.

The exercise asks for the explicit witnesses of the ABC decomposition (Corollary 4.2,
`U = e^{iα} A X B X C` with `A B C = I`) applied to the Hadamard gate `H`. Feeding the Hadamard's
Z–Y parameters `(α, β, γ, δ) = (π/2, 0, π/2, π)` into Corollary 4.2's witnesses
`A = R_z(β) R_y(γ/2)`, `B = R_y(-γ/2) R_z(-(δ+β)/2)`, `C = R_z((δ-β)/2)` and simplifying
`R_z(0) = I` gives the answer:

`α = π/2`,  `A = R_y(π/4)`,  `B = R_y(-π/4) R_z(-π/2)`,  `C = R_z(π/2)`.

## The physics: what the theorem states

Corollary 4.2 is the key to controlled operations precisely because the ABC product reproduces `U`
*as a gate* — the phase `e^{iα}` being physically unobservable. The theorem of this file is exactly
that channel statement for the Hadamard:

* `hadamardGate_evolve_eq_hadamardABCGate_evolve` — for every state `ρ` of the qubit,
  `H.evolve ρ = (A X B X C).evolve ρ`, i.e. the Hadamard gate and its ABC gate product induce the
  *same* state evolution `ρ ↦ U ρ U†`, where `A = R_y(π/4)`, `B = R_y(-π/4) R_z(-π/2)`,
  `C = R_z(π/2)`, `X = pauliXGate`.

The global phase `α = π/2` (the "give `α`" part of the answer), which cancels in the channel, is
recorded at the operator level by `hadamardGate_op_eq_expPiDivTwo_smul_hadamardABCGate`
(`AxQM/Postulates/API/HadamardABC.lean`).

## Where the pieces live

The witnesses and the underlying identities are in:

* **`AxQM.Concrete.hadamardWitnessA/B/C`**, **`hadamardWitnessA_mul_B_mul_C_eq_one`**
  (`A B C = I`) and **`hadamardC_eq_expPiDivTwo_smul_hadamardABC`** (`H = e^{iπ/2} • (A X B X C)`)
  (`AxQM/Concrete/HadamardABC.lean`) — the pure `2 × 2` matrix answer, built on the ABC
  decomposition (Corollary 4.2, `AxQM/Concrete/ABCDecomposition.lean`) and the Hadamard rotation
  identity of Exercise 4.4 (`AxQM/Concrete/HadamardRotation.lean`).
* **`AxQM.rotYGate`** and
  **`hadamardGate_op_eq_expPiDivTwo_smul_hadamardABCGate`**
  (`AxQM/Postulates/API/HadamardABC.lean`) — the `y`-rotation gate as `Evolution qubit`, and the
  operator form `H = e^{iπ/2} • (A X B X C)`.
* **`Evolution.evolve_eq_of_op_eq_phase_smul`** (`AxQM/Postulates/API/Evolution.lean`, valid
  for any gate and also used for Exercises 4.3/4.4) — the reusable lemma that a
  unit-modulus global phase leaves the induced channel unchanged; the theorem below is that lemma
  applied to the operator identity with `c = e^{iπ/2}` (`‖e^{iπ/2}‖ = 1`).
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.12.** The ABC decomposition of the Hadamard gate: with
`α = π/2`, `A = R_y(π/4)`, `B = R_y(-π/4) R_z(-π/2)`, `C = R_z(π/2)`, the Hadamard gate `H` equals
its ABC gate product `A X B X C` *as a quantum operation* — for every state `ρ` of the qubit, `H`
and the product induce the identical state evolution `ρ ↦ U ρ U†`. (The companion relation
`A B C = I` is `Concrete.hadamardWitnessA_mul_B_mul_C_eq_one`.) The global phase `e^{iπ/2}` relating
the two operators (`hadamardGate_op_eq_expPiDivTwo_smul_hadamardABCGate`) has unit modulus, so it
cancels in the conjugation defining `Evolution.evolve` (`Evolution.evolve_eq_of_op_eq_phase_smul`);
this is why `α` is physically unobservable and why Corollary 4.2 is the key to controlled `H`. -/
theorem hadamardGate_evolve_eq_hadamardABCGate_evolve (ρ : State qubit) :
    hadamardGate.evolve ρ
      = (((((rotYGate (Real.pi / 4)).comp pauliXGate).comp
          ((rotYGate (-(Real.pi / 4))).comp (rotZGate (-(Real.pi / 2))))).comp pauliXGate).comp
          (rotZGate (Real.pi / 2))).evolve ρ :=
  Evolution.evolve_eq_of_op_eq_phase_smul hadamardGate _
    (Complex.norm_exp_ofReal_mul_I _)
    hadamardGate_op_eq_expPiDivTwo_smul_hadamardABCGate ρ

end AxQM
