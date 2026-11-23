/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumFourierTransform
import AxQM.Postulates.API.QuditGate
import AxQM.Postulates.API.ApproxError
import AxQM.Concrete.QftGateCircuitAllOnes
import AxQM.Concrete.QftGateCircuitEqMatrix
import AxQM.Concrete.QftApproxErrorBound

/-!
# AxQM.Postulates.API — the approximate (imperfect) QFT as a unitary evolution

The physics **wrapper** promoting the concrete perturbed Figure 5.1 QFT circuit
`Concrete.qftGateCircuitPerturbed n Δ` — the ideal gate-level QFT with every controlled-`Rₖ`
performed to precision `Δ` (Nielsen & Chuang, Exercise 5.6) — to a genuine unitary `Evolution` of
the `n`-qubit register `qudit (2ⁿ)`, together with the operator-level form of the coherent-error
lower bound. This is the imperfect transform `V` whose distance from the ideal QFT
`U = qftEvolution (2ⁿ)` the faithful `Ω(n²/p(n))` half of Exercise 5.6 lower-bounds.

## What is formalised

* `qftApproxEvolution n Δ` — the **imperfect QFT as a unitary `Evolution (qudit (2ⁿ))`**, the ideal
  QFT with every controlled-`Rₖ` gate implemented to precision `Δ`. It is the concrete perturbed
  circuit matrix `Concrete.qftGateCircuitPerturbed n Δ` (unitary by
  `Concrete.qftGateCircuitPerturbed_mem_unitaryGroup`) promoted to an `Evolution` through the shared
  matrix-gate constructor `quditGate` — the `Δ`-perturbed twin of `qftEvolution (2ⁿ)`.
* `qftApproxEvolution_op` — its underlying operator is `Matrix.toEuclideanCLM` of the perturbed
  circuit (via `quditGate_op`).
* `qftApproxEvolution_op_allOnes_dist_ge` — **the operator-level `Ω` heart** (N&C Exercise 5.6, `Ω`
  half): on the all-ones computational-basis input `|1…1⟩` the ideal QFT `U` and the imperfect `V`
  are separated by at least the coherent-accumulation bound

  `‖U.op |1…1⟩ − V.op |1…1⟩‖ ≥ (qftControlledRkCount n · Δ)/π = n(n-1)Δ/(2π)`,

  in the small-error regime `0 ≤ qftControlledRkCount n · Δ ≤ π`. This is the concrete distance
  bound `Concrete.qftGateCircuitPerturbed_allOnes_dist_ge` transported to the operator norm: the
  `EuclideanSpace` norm of the operator difference on `|1…1⟩` is exactly the concrete `√(∑ᵢ ‖…‖²)`
  (`EuclideanSpace.norm_eq` + `Matrix.ofLp_toEuclideanCLM`: applying `Matrix.toEuclideanCLM M` to
  the standard basis vector `|1…1⟩` is the matrix column `M *ᵥ |1…1⟩`), with the ideal operator's
  matrix `qftMatrix (2ⁿ)` identified with the gate circuit `qftGateCircuit n`
  (`Concrete.qftGateCircuit_eq_qftMatrix`). Exercise 5.6 (`AxQM/NC/Ch5/Exercise5_6.lean`) lifts this
  (via `Evolution.gateError_apply_le` at the unit input `|1…1⟩`) to the gate error
  `E(U, V) ≥ n(n-1)Δ/(2π)`.
* `qftApproxEvolution_gateError_le` — **the specific-`V` upper bound** (Exercise 5.6, `O` half on
  the coherent realisation): `E(U, V) = ‖U.op − V.op‖ ≤ qftControlledRkCount n · |Δ| = n(n-1)|Δ|/2`.
  Since `Matrix.toEuclideanCLM` is norm-preserving (`Matrix.cstar_norm_def`), the gate error equals
  the
  concrete matrix distance `‖qftGateCircuit n − qftGateCircuitPerturbed n Δ‖`, which
  `Concrete.qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le` (Box 4.1's chaining bound over the
  Figure 5.1 gate factorisation) bounds by `qftControlledRkCount n · |Δ|`. Paired with the `Ω` bound
  above, this is the two-sided `Θ(n²·Δ)` on the one realisation `V`.

## Design notes

* **`quditGate`.** `qftApproxEvolution` is the gate of a unitary matrix, so it is built from the
  constructor `quditGate` of `AxQM/Postulates/API/QuditGate.lean` (as `qftEvolution`, `pauliZGate`,
  … are), not from a bespoke `toEuclideanCLM` bundle.
* **The lower bound.** The bound `E(U,V) ≥ n(n-1)Δ/(2π)` is stated for
  `qftEvolution`/`qftApproxEvolution`/`Evolution.gateError` in `AxQM/NC/Ch5/Exercise5_6.lean`; its
  content is the operator-norm distance on `|1…1⟩`. The bridge from the concrete matrix distance to
  the operator norm is `qftApproxEvolution_op_allOnes_dist_ge` in this file; Exercise 5.6 applies it
  together with `Evolution.gateError_apply_le`.
-/

open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace AxQM

open AxQM.Concrete Matrix

/-- The **approximate (imperfect) quantum Fourier transform on `qudit (2ⁿ)`** as a unitary
`Evolution` (Nielsen & Chuang, Exercise 5.6): the ideal QFT with every controlled-`Rₖ` gate
implemented to precision `Δ`. It is the concrete perturbed circuit matrix
`Concrete.qftGateCircuitPerturbed n Δ` — unitary by
`Concrete.qftGateCircuitPerturbed_mem_unitaryGroup` — promoted to an `Evolution` through the shared
matrix-gate constructor `quditGate`. This is the imperfect transform `V` of Exercise 5.6, the
`Δ`-perturbed twin of `qftEvolution (2ⁿ)`. -/
def qftApproxEvolution (n : ℕ) (Δ : ℝ) : Evolution (qudit (2 ^ n)) :=
  quditGate (qftGateCircuitPerturbed_mem_unitaryGroup n Δ)

/-- The underlying operator of `qftApproxEvolution n Δ` is `Matrix.toEuclideanCLM` of the perturbed
Figure 5.1 circuit (`quditGate_op`). -/
@[simp]
theorem qftApproxEvolution_op (n : ℕ) (Δ : ℝ) :
    (qftApproxEvolution n Δ).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) (qftGateCircuitPerturbed n Δ) :=
  quditGate_op _

/-- **The operator-level all-ones QFT-approximation distance lower bound** (Nielsen & Chuang,
Exercise 5.6, `Ω` half — the operator form of the concrete heart). On the all-ones
computational-basis input `|1…1⟩` (`quditBasis (finFunctionFinEquiv (qftAllOnes n))`), the ideal QFT
`U = qftEvolution (2ⁿ)` and the imperfect transform `V = qftApproxEvolution n Δ` (each
controlled-`Rₖ` shifted by `+Δ`) satisfy

`(qftControlledRkCount n · Δ)/π = n(n-1)Δ/(2π) ≤ ‖U.op |1…1⟩ − V.op |1…1⟩‖`,

valid in the small-error regime `0 ≤ qftControlledRkCount n · Δ ≤ π` (`0 ≤ Δ`, `hreg`). The
`EuclideanSpace` norm of the operator difference on the standard basis vector `|1…1⟩` is exactly the
concrete `√(∑ᵢ ‖…‖²)` of `Concrete.qftGateCircuitPerturbed_allOnes_dist_ge`:
`EuclideanSpace.norm_eq` expands the norm coordinatewise, `Matrix.ofLp_toEuclideanCLM` identifies
each coordinate of `Matrix.toEuclideanCLM M |1…1⟩` with the matrix column `(M *ᵥ |1…1⟩) i`, and
`Concrete.qftGateCircuit_eq_qftMatrix` identifies the ideal operator's matrix `qftMatrix (2ⁿ)` with
the gate circuit `qftGateCircuit n`. Exercise 5.6 lifts this to `E(U, V) ≥ n(n-1)Δ/(2π)` by
`Evolution.gateError_apply_le` at the unit input `|1…1⟩`. -/
theorem qftApproxEvolution_op_allOnes_dist_ge (n : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hreg : (qftControlledRkCount n : ℝ) * Δ ≤ Real.pi) :
    (qftControlledRkCount n : ℝ) * Δ / Real.pi
      ≤ ‖(qftEvolution (2 ^ n)).op (quditBasis (finFunctionFinEquiv (qftAllOnes n))).vec
          - (qftApproxEvolution n Δ).op
              (quditBasis (finFunctionFinEquiv (qftAllOnes n))).vec‖ := by
  set J := finFunctionFinEquiv (qftAllOnes n) with hJ
  have hbridge :
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) (qftGateCircuit n)
            (EuclideanSpace.single J 1)
        - Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) (qftGateCircuitPerturbed n Δ)
            (EuclideanSpace.single J 1)‖
      = Real.sqrt (∑ i, ‖(qftGateCircuit n *ᵥ Pi.single J 1) i
          - (qftGateCircuitPerturbed n Δ *ᵥ Pi.single J 1) i‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
  refine (qftGateCircuitPerturbed_allOnes_dist_ge n Δ hΔ hreg).trans (le_of_eq ?_)
  rw [qftEvolution_op, qftApproxEvolution_op, quditBasis_vec, ← qftGateCircuit_eq_qftMatrix]
  exact hbridge.symm

/-- **The specific-`V` upper bound of Exercise 5.6** (the `O` half on the coherent realisation `V =
qftApproxEvolution n Δ`). The imperfect QFT `V`, obtained by performing every controlled-`Rₖ` gate
to precision `Δ`, differs from the ideal QFT `U = qftEvolution (2ⁿ)` by at most the imprecise-gate
count times the per-gate precision:

`E(U, V) = ‖U.op − V.op‖ ≤ qftControlledRkCount n · |Δ| = n(n-1)|Δ|/2`.

The gate error `E(U,V)` is `‖U.op − V.op‖`, and
`U.op = Matrix.toEuclideanCLM (qftMatrix 2ⁿ) = Matrix.toEuclideanCLM (qftGateCircuit n)`
(`qftEvolution_op`, `Concrete.qftGateCircuit_eq_qftMatrix`), while
`V.op = Matrix.toEuclideanCLM (qftGateCircuitPerturbed n Δ)` (`qftApproxEvolution_op`); since
`Matrix.toEuclideanCLM` is a norm-preserving `⋆`-algebra isomorphism (`Matrix.cstar_norm_def`),
`E(U,V)` equals the concrete `L²`-operator matrix distance
`‖qftGateCircuit n − qftGateCircuitPerturbed n Δ‖`, bounded by `Concrete`'s Box 4.1 chaining bound
`Concrete.qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le`. Paired with the coherent `Ω` lower
bound (`qftApproxEvolution_op_allOnes_dist_ge` → `qftApprox_gateError_ge` in
`AxQM/NC/Ch5/Exercise5_6.lean`) this pins the approximate-QFT error to `Θ(n²·Δ)` on the one
realisation `V` — the two-sided form of Exercise 5.6's `Θ`. -/
theorem qftApproxEvolution_gateError_le (n : ℕ) (Δ : ℝ) :
    (qftEvolution (2 ^ n)).gateError (qftApproxEvolution n Δ)
      ≤ (Concrete.qftControlledRkCount n : ℝ) * |Δ| := by
  have h : (qftEvolution (2 ^ n)).gateError (qftApproxEvolution n Δ)
      = ‖qftGateCircuit n - qftGateCircuitPerturbed n Δ‖ := by
    rw [Matrix.cstar_norm_def, map_sub, Evolution.gateError, qftEvolution_op, qftApproxEvolution_op,
        ← qftGateCircuit_eq_qftMatrix]
    rfl
  rw [h]
  exact qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le n Δ

end AxQM
