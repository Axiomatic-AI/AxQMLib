/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschControlledReachable
import AxQM.Concrete.MultiControlledSingleQubit

/-!
# Concrete: the Deutsch gate placed on register wires (matrix level, N&C Ex 4.44)

Every statement is about matrices — the multiply-controlled single-qubit wire gate
`mcCtrlSingleQubit`, the `2 × 2` matrices `rotX`, `pauliX`, `iRxMat`, and the Deutsch target orbit
`deutschTargetOrbit`.

## Placing `G` on the wires of a register

The universality of the Deutsch gate `G = C²(iR_x(πα))` (Nielsen & Chuang, Exercise 4.44) is
assembled — following Exercise 4.43 — from a **matrix-level** register development: any register
unitary decomposes into single-qubit gates on wires (`singleQubitOnWire`) and `CNOT`/`Toffoli`
(`Concrete/ReachableCircuits.lean`, `Concrete/DeutschReachableCircuits.lean`), each approximated up
to a global phase. The abstract *density core*
(`exists_phase_smul_mem_closure_deutschReachableCircuits`) states this over an *abstract* gate set;
the gates that set collects are reached by iterating the actual gate `G` placed on register wires.

The elementary object in that realisation is `G` **placed on three wires** of an `m`-qubit register:
two control wires `a, b` and a target wire `j`. This is exactly the two-control instance of the
existing subset-controlled single-qubit wire gate
`mcCtrlSingleQubit enc S j Ũ` (`Concrete/MultiControlledSingleQubit.lean`) at `S = {a, b}` — it
applies `Ũ` to wire `j` when both control wires are `|1⟩`, so `mcCtrlSingleQubit enc {a, b} j
(iR_x(πα))` is the matrix of `G` placed with controls `a, b` and target `j`. This file therefore
does **not** introduce a bespoke placement object; it reuses `mcCtrlSingleQubit`, inheriting its
full `*`-homomorphism-on-the-block algebra
`mcCtrlSingleQubit_{one,mul,conjTranspose,mem_unitaryGroup}`,
its `continuous_mcCtrlSingleQubit`, and — for the ancilla compression — its reduction
machinery (`mcCtrlSingleQubit_mulVec_of_ctrl`/`_of_not_ctrl`,
`mcCtrlSingleQubit_pauliX_eq_permGate`).

Fixing the two controls at `|1⟩` runs `G`'s single-qubit orbit `(iR_x(πα))^k` on the target wire,
and — the point of Exercise 4.44's argument — a doubly-controlled single-qubit gate on wires is the
shape that realises **both** dense single-qubit axes from `G`, at two different wire assignments:

* the **dense `x`-axis** — controls on two ancilla wires held at `|1⟩`, target on the data wire —
  runs `(iR_x(πα))^k` on the data wire, dense in the `x`-rotations for irrational `α`;
* the **phase gate `S`** — one control on an ancilla held at `|1⟩`, the *other control on the data
  wire*, target on a throwaway ancilla — where the controlled global phase `i · I` on the target
  becomes `S` on the data-wire control.

What this file contributes is the **block-level density from `G`**: the placement of every
`x`-rotation `R_x(β)`, the scalar `i · I`, and the Pauli `X` lies in the closure of the placed
Deutsch iterates. The subsequent ancilla-compression bridge consumes these to identify the
compressed placements with the single-qubit / reversible generators the density core needs.

## The construction and results

Fix an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of the `m`-bit strings as the `d = 2 ^ m` basis
indices, two control wires `a b : Fin m`, and a target wire `j : Fin m`.

* `deutschWirePlacedReachable enc a b j α` — the placed Deutsch iterates
  `{mcCtrlSingleQubit enc {a, b} j (iⁿ R_x(nπα))}`, the image of the target orbit `⟨iR_x(πα)⟩`
  (`deutschTargetOrbit`) under the placement `mcCtrlSingleQubit enc {a, b} j`; its forward members
  are the actual gate powers (`mcCtrlSingleQubit_iRxMat_pow_mem_deutschWirePlacedReachable`).
* `mcCtrlSingleQubit_rotX_mem_closure_deutschWirePlacedReachable` /
  `mcCtrlSingleQubit_iScalar_mem_closure_deutschWirePlacedReachable` /
  `mcCtrlSingleQubit_pauliX_mem_closure_deutschWirePlacedReachable` — **block-level density from
  `G`** (`α` irrational): the placements of `R_x(β)`, `i · I` and `X` each lie in the closure of the
  placed Deutsch iterates. Each is a one-line transport of the corresponding `2 × 2` orbit-closure
  fact (`rotX_mem_closure_cyclic_iRx` / `iScalar_mem_closure_cyclic_iRx` /
  `pauliX_mem_closure_cyclic_iRx`, `Concrete/DeutschGateDensity.lean`) through the continuous
  placement `continuous_mcCtrlSingleQubit`, mirroring
  `sMatrixKron_mem_closure_deutschControlledReachableMats`
  (`Concrete/DeutschControlledReachable.lean`).
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The placed reachable set of the Deutsch gate.** The Deutsch iterates
`{mcCtrlSingleQubit enc {a, b} j (iⁿ R_x(nπα))}` placed with controls `a, b` and target `j`, i.e.
the image of the target orbit `⟨iR_x(πα)⟩` (`deutschTargetOrbit`) under the two-control placement
`mcCtrlSingleQubit enc {a, b} j`. Its forward members are the actual gate powers
(`mcCtrlSingleQubit_iRxMat_pow_mem_deutschWirePlacedReachable`). -/
noncomputable def deutschWirePlacedReachable (enc : (Fin m → Fin 2) ≃ Fin d) (a b j : Fin m)
    (α : ℝ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  mcCtrlSingleQubit enc {a, b} j '' deutschTargetOrbit α

/-- **The `k`-th placed gate power is reachable:** the placement of `(iR_x(πα))^k` lies in
`deutschWirePlacedReachable enc a b j α`. Grounds the placed reachable set in the actual gate `G`:
its members are obtained by iterating `G` placed with controls `a, b` and target `j`. -/
theorem mcCtrlSingleQubit_iRxMat_pow_mem_deutschWirePlacedReachable
    (enc : (Fin m → Fin 2) ≃ Fin d) (a b j : Fin m) (α : ℝ) (k : ℕ) :
    mcCtrlSingleQubit enc {a, b} j (iRxMat (Real.pi * α) ^ k)
      ∈ deutschWirePlacedReachable enc a b j α :=
  Set.mem_image_of_mem _ (iRxMat_pow_mem_deutschTargetOrbit α k)

/-- **The placed `x`-rotations are densely reachable from `G`** (Nielsen & Chuang, Exercise 4.44,
matrix level). When `α` is irrational, the placement of every `x`-rotation `R_x(β)` lies in the
closure of the placed Deutsch iterates `deutschWirePlacedReachable enc a b j α`. A one-line
transport of the `2 × 2` density `rotX_mem_closure_cyclic_iRx` (`Concrete/DeutschGateDensity.lean`)
through the continuous placement `continuous_mcCtrlSingleQubit`, mirroring
`sMatrixKron_mem_closure_deutschControlledReachableMats`. -/
theorem mcCtrlSingleQubit_rotX_mem_closure_deutschWirePlacedReachable {α : ℝ} (hα : Irrational α)
    (enc : (Fin m → Fin 2) ≃ Fin d) (a b j : Fin m) (β : ℝ) :
    mcCtrlSingleQubit enc {a, b} j (rotX β)
      ∈ closure (deutschWirePlacedReachable enc a b j α) :=
  image_closure_subset_closure_image (continuous_mcCtrlSingleQubit enc {a, b} j)
    (Set.mem_image_of_mem _ (rotX_mem_closure_cyclic_iRx hα β))

/-- **The placed global phase `i · I` is densely reachable from `G`** (Nielsen & Chuang, Exercise
4.44, matrix level). When `α` is irrational, the placement of `i · I` lies in the closure of the
placed Deutsch iterates. Physically this is the `x`-independent limit that (through the
data-wire-as-control placement) becomes the **phase gate `S`** — the second dense single-qubit axis.
A one-line transport of the `2 × 2` density `iScalar_mem_closure_cyclic_iRx` through the continuous
placement `continuous_mcCtrlSingleQubit`. -/
theorem mcCtrlSingleQubit_iScalar_mem_closure_deutschWirePlacedReachable {α : ℝ} (hα : Irrational α)
    (enc : (Fin m → Fin 2) ≃ Fin d) (a b j : Fin m) :
    mcCtrlSingleQubit enc {a, b} j (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      ∈ closure (deutschWirePlacedReachable enc a b j α) :=
  image_closure_subset_closure_image (continuous_mcCtrlSingleQubit enc {a, b} j)
    (Set.mem_image_of_mem _ (iScalar_mem_closure_cyclic_iRx hα))

/-- **The placed Pauli `X` is densely reachable from `G`** (Nielsen & Chuang, Exercise 4.44, matrix
level). When `α` is irrational, the placement of `X` lies in the closure of the placed Deutsch
iterates. Physically this is what makes the placed `G` reach the reversible gates
(`CNOT`/`Toffoli`): `X = i · R_x(π)` is densely reachable on the target, so its placement is a
limit of placed Deutsch iterates. A one-line transport of the `2 × 2` density
`pauliX_mem_closure_cyclic_iRx` through the continuous placement `continuous_mcCtrlSingleQubit`. -/
theorem mcCtrlSingleQubit_pauliX_mem_closure_deutschWirePlacedReachable {α : ℝ} (hα : Irrational α)
    (enc : (Fin m → Fin 2) ≃ Fin d) (a b j : Fin m) :
    mcCtrlSingleQubit enc {a, b} j pauliX ∈ closure (deutschWirePlacedReachable enc a b j α) :=
  image_closure_subset_closure_image (continuous_mcCtrlSingleQubit enc {a, b} j)
    (Set.mem_image_of_mem _ (pauliX_mem_closure_cyclic_iRx hα))

end AxQM.Concrete
