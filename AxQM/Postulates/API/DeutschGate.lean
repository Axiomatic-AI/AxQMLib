/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschGateDensity
import AxQM.Postulates.API.ControlledUnitary

/-!
# AxQM.Postulates.API — the Deutsch target gate `iR_x(θ)`

The single-qubit gate underlying Nielsen & Chuang, Exercise 4.44. The three-qubit
Deutsch gate is `G = C²(iR_x(πα))`: the doubly-controlled application of the operation `iR_x(θ)` to
the target qubit. This file packages that operation as a `qubit` `Evolution`.

## What is formalised

* `iRxGate θ` — the **Deutsch target gate** `iR_x(θ) = i · R_x(θ)` as an `Evolution qubit`, its
  operator the concrete matrix `Concrete.iRxMat θ` promoted through `Matrix.toEuclideanCLM`; the
  `Evolution` unitarity obligation is transported from `Concrete.iRxMat_mem_unitaryGroup`. The
  `simp` bridge `iRxGate_op` exposes the operator.
* `iRxGate_pi_eq_pauliXGate` — **`iR_x(π) = X`**: at `θ = π` the target gate is the Pauli-`X` gate.
  Lifting the matrix identity `Concrete.iRxMat_pi` through `Matrix.toEuclideanCLM` (via
  `Evolution.ext`), this makes the Deutsch gate the Toffoli gate `C²(X)` at `α = 1`.

## Design notes

* **Why a dedicated gate (not `Complex.I • rotXGate`).** `Evolution` carries a unitarity proof, so a
  scalar multiple of a gate is not itself an `Evolution` without re-proving unitarity; `iRxGate`
  bundles that proof once (via `Concrete.iRxMat_mem_unitaryGroup`), and reuses the existing concrete
  matrix `Concrete.iRxMat` from `Concrete/DeutschGateDensity.lean` (Exercise 4.44).
-/

noncomputable section

namespace AxQM

/-- The **Deutsch target gate** `iR_x(θ) = i · R_x(θ)` as a closed-system evolution of the `qubit`
(Nielsen & Chuang, Exercise 4.44). Its operator is the concrete matrix `Concrete.iRxMat θ` promoted
through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`; unitarity — the `Evolution` proof
obligation — is transported from `Concrete.iRxMat_mem_unitaryGroup`. The doubly-controlled
application of this gate to the target qubit is the three-qubit Deutsch gate
`deutschGate` (see `NC/Ch4/Exercise4_44.lean`). -/
def iRxGate (θ : ℝ) : Evolution qubit where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.iRxMat θ)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
      (Concrete.iRxMat_mem_unitaryGroup θ)

@[simp]
theorem iRxGate_op (θ : ℝ) :
    (iRxGate θ).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Concrete.iRxMat θ) := rfl

/-- **`iR_x(π) = X`.** At `θ = π` the Deutsch target gate is the Pauli-`X` gate, the image under the
`⋆`-algebra isomorphism `Matrix.toEuclideanCLM` of the matrix identity `Concrete.iRxMat_pi`
(`R_x(π) = -iX`, so `iR_x(π) = i·(-iX) = X`). This is why the Deutsch gate `C²(iR_x(πα))` is the
Toffoli gate `C²(X)` at `α = 1`. -/
theorem iRxGate_pi_eq_pauliXGate : iRxGate Real.pi = pauliXGate := by
  apply Evolution.ext
  rw [iRxGate_op, pauliXGate_op, Concrete.iRxMat_pi]

end AxQM
