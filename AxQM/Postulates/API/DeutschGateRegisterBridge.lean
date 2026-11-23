/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeutschGateMatrix
import AxQM.Concrete.DeutschRegisterBridge

/-!
# The base three-wire register placement of the Deutsch gate (N&C Ex 4.44)

The universality reduction of the Deutsch gate `G = C²(iR_x(πα))` (Nielsen & Chuang, Exercise 4.44)
realises `G` on the wires of a register through the wire-addressed matrix gate
`Concrete.mcCtrlSingleQubit enc S j g` (see `AxQM/Concrete/DeutschWirePlacement.lean` and
`AxQM/Concrete/DeutschCompressedUniversality.lean`). To state
the result for the gate itself, the register placement must be tied back to the Deutsch gate
`deutschGate α = ccontrolledUnitary (iRxGate (πα))`.

This file supplies that tie for the **base register** of three wires (`Fin 3`, `d = 8`). Two bridges
already exist:

* `ccontrolledUnitary_congr_threeQuditIso_op` (`Postulates/API/DeutschGateMatrix.lean`) — the
  physical doubly-controlled gate transported to the eight-level register `qudit 8` is the explicit
  matrix `C²(M2)`: `(Evolution.congr threeQuditIso (ccontrolledUnitary U)).op =
  toEuclideanCLM (ccontrolledMatFin8 M2)` when `U.op = toEuclideanCLM M2`.
* `Concrete.ccontrolledMatFin8_eq_mcCtrlSingleQubit` (`Concrete/DeutschRegisterBridge.lean`) — that
  same matrix `C²(M2)` *is* the two-control single-qubit wire gate placing `M2` on wire `2` with
  controls `{0, 1}` of the canonical three-wire encoding `finThreeRegEnc`.

Chaining them (through `Evolution.ext`, an evolution being determined by its operator) identifies
the **reachability-family placement** `quditGate (mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 M2)` — a
`quditGate`-promoted register gate, the exact shape the reachability development iterates — with the
**physical gate** `ccontrolledUnitary U` transported to `qudit 8`. At `U = iRxGate (πα)` (matrix
`iRxMat (πα)`, `iRxGate_op`) this is `deutschGate α` transported: the base-register placement is the
Deutsch gate itself, on three wires. The general register embedding onto arbitrary wires of a
larger register is in `AxQM/Postulates/API/DeutschGateTensorSplit.lean`.

`deutschGate` itself is defined in `AxQM/NC/Ch4/Exercise4_44.lean`, so it is named in its unfolded
form `ccontrolledUnitary (iRxGate (πα))` (definitionally `deutschGate α`).
-/

namespace AxQM

open Matrix Concrete

/-- **The base three-wire register placement of a doubly-controlled gate is that gate transported to
`qudit 8`.** For a single-qubit evolution `U` with matrix `M2` (`U.op = toEuclideanCLM M2`), the
doubly-controlled gate `C²(U)` transported along the register identification `threeQuditIso` to the
eight-level register equals the reachability-family placement of `M2` on wire `2` with controls
`{0, 1}`:

  `Evolution.congr threeQuditIso (ccontrolledUnitary U)
    = quditGate (mcCtrlSingleQubit_mem_unitaryGroup finThreeRegEnc {0, 1} 2 hM2)`.

Both evolutions have the same operator: the left one is `toEuclideanCLM (ccontrolledMatFin8 M2)`
(`ccontrolledUnitary_congr_threeQuditIso_op`), the right one is
`toEuclideanCLM (mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 M2)` (`quditGate_op`), and these matrices
coincide (`ccontrolledMatFin8_eq_mcCtrlSingleQubit`); an evolution is determined by its operator
(`Evolution.ext`). This is the register-model counterpart of the operator–matrix bridge
`ccontrolledUnitary_congr_threeQuditIso_op`: it names the physical gate `ccontrolledUnitary U` as
the `quditGate` register placement the reachability development iterates. -/
theorem congr_threeQuditIso_ccontrolledUnitary_eq_quditGate_mcCtrlSingleQubit
    {U : Evolution qubit} {M2 : Matrix (Fin 2) (Fin 2) ℂ}
    (hM2 : M2 ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hU : U.op = Matrix.toEuclideanCLM (𝕜 := ℂ) M2) :
    Evolution.congr threeQuditIso (ccontrolledUnitary U)
      = quditGate (mcCtrlSingleQubit_mem_unitaryGroup finThreeRegEnc {0, 1} 2 hM2) := by
  apply Evolution.ext
  rw [quditGate_op, ccontrolledUnitary_congr_threeQuditIso_op hU,
    ccontrolledMatFin8_eq_mcCtrlSingleQubit]

/-- **The base three-wire register placement of the Deutsch gate is `deutschGate α` transported to
`qudit 8`** (Nielsen & Chuang, Exercise 4.44). The reachability-family placement of
the Deutsch target `iRxMat (πα)` on wire `2` with controls `{0, 1}` of the canonical three-wire
encoding
equals the physical Deutsch gate `deutschGate α = ccontrolledUnitary (iRxGate (πα))` transported
along `threeQuditIso` to the eight-level register:

  `Evolution.congr threeQuditIso (ccontrolledUnitary (iRxGate (πα)))
    = quditGate (mcCtrlSingleQubit_mem_unitaryGroup finThreeRegEnc {0, 1} 2
        (iRxMat_mem_unitaryGroup (πα)))`.

The instance of the general bridge at `U = iRxGate (πα)`, whose matrix is `iRxMat (πα)`
(`iRxGate_op`). Since `deutschGate α` is definitionally `ccontrolledUnitary (iRxGate (Real.pi * α))`
(`AxQM/NC/Ch4/Exercise4_44.lean`), this reads the Deutsch gate's register placement as
the `quditGate` gate its reachability iterates are powers of — the base case the
register-realisation of `G` builds on. -/
theorem congr_threeQuditIso_deutschGate_eq_quditGate_mcCtrlSingleQubit (α : ℝ) :
    Evolution.congr threeQuditIso (ccontrolledUnitary (iRxGate (Real.pi * α)))
      = quditGate (mcCtrlSingleQubit_mem_unitaryGroup finThreeRegEnc {0, 1} 2
          (iRxMat_mem_unitaryGroup (Real.pi * α))) :=
  congr_threeQuditIso_ccontrolledUnitary_eq_quditGate_mcCtrlSingleQubit
    (iRxMat_mem_unitaryGroup (Real.pi * α)) (iRxGate_op (Real.pi * α))

end AxQM
