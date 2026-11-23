/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.QuantumFourierTransform
import AxQM.Postulates.API.QuditGate
import AxQM.Concrete.QftGateCircuitEqMatrix

/-!
# The QFT as an `Evolution`-gate composition (Nielsen & Chuang, Figure 5.1 / product form 5.4)

The quantum Fourier transform is given as the *monolithic* unitary `qftEvolution (2ⁿ)` (its operator
the matrix `qftMatrix (2ⁿ)`). Problem 5.2 (the measured QFT) needs it instead as a **composition of
wire-addressed gates** — the Figure 5.1 circuit of Hadamards, controlled-`Rₖ` rotations, and a swap
layer — so that the terminal measurement can be deferred gate by gate. This file supplies that
bridge.

The `Concrete` layer already builds the Figure 5.1 circuit as an explicit matrix product
(`Concrete.qftGateCircuit n = (Concrete.qftGateSequence n).reverse.prod`) and certifies it computes
the transform (`Concrete.qftGateCircuit_eq_qftMatrix : qftGateCircuit n = qftMatrix (2ⁿ)`). Here we
**lift that matrix product to the `Evolution` monoid**: each Figure 5.1 gate matrix is unitary
(`Concrete.qftGateSequence_forall_mem_unitaryGroup`), so `quditGate` promotes it to an
`Evolution (qudit (2ⁿ))`, and the sequential composition (the monoid product `Evolution.comp`) of
the promoted gates equals the monolithic `qftEvolution (2ⁿ)`:

* `qftGateEvolutionSequence n` — the time-ordered list of Figure 5.1 gates as `Evolution`s;
* `qftCircuitEvolution n` — their sequential composition (reverse product, so the first-listed gate
  acts first), the QFT *as a circuit*;
* `qftEvolution_eq_qftCircuitEvolution` — **the circuit is the transform**: `qftEvolution (2ⁿ)`
  equals this explicit composition of one- and two-wire gates. This is the postulate-level
  realisation of product form (5.4), the form over which the whole-circuit measured-QFT reduction
  (Problem 5.2) defers each two-wire controlled gate.

`quditGate` (matrix → `Evolution`) intertwines matrix multiplication with `Evolution` composition
onto the operator algebra (`quditGate_op` + `Evolution.op_prod` + multiplicativity of
`Matrix.toEuclideanCLM`), so the proof merely transports the `Concrete` matrix identity across it,
with no re-derivation of the circuit's correctness.

-/

open Matrix

namespace AxQM

noncomputable section

/-- **The Figure 5.1 QFT gates as `Evolution`s**, listed in the order the circuit's operator
composes them (the reverse of Figure 5.1's time order, matching `Concrete.qftGateCircuit`'s reverse
product). Each gate matrix of `Concrete.qftGateSequence n` — the swap layer, and each target's
Hadamard + controlled-`Rₖ` cascade — is unitary (`qftGateSequence_forall_mem_unitaryGroup`), so
`quditGate` promotes it to a unitary `Evolution (qudit (2ⁿ))`. The last entry (the swap layer)
acts first on states; the plain product of this list is `qftCircuitEvolution`. -/
def qftGateEvolutionSequence (n : ℕ) : List (Evolution (qudit (2 ^ n))) :=
  (Concrete.qftGateSequence n).reverse.pmap (fun _ h => quditGate h)
    (fun g hg => Concrete.qftGateSequence_forall_mem_unitaryGroup n g (List.mem_reverse.mp hg))

/-- **The QFT circuit as a single `Evolution`.** The sequential composition (`Evolution`-monoid
product) of the Figure 5.1 gates `qftGateEvolutionSequence n`; since that list is in composition
order, the swap layer acts first on states, matching `Concrete.qftGateCircuit`. This is the quantum
Fourier transform expressed as a circuit of one- and two-wire gates;
`qftEvolution_eq_qftCircuitEvolution` identifies it with the monolithic `qftEvolution (2ⁿ)`. -/
def qftCircuitEvolution (n : ℕ) : Evolution (qudit (2 ^ n)) :=
  (qftGateEvolutionSequence n).prod

/-- Mapping the underlying operator over a list of `quditGate`-promoted unitary matrices recovers
the matrices promoted through `Matrix.toEuclideanCLM`. This is `quditGate_op` applied down the
list — the step turning an `Evolution`-monoid product of the promoted gates into the
operator-algebra product of the matrices. -/
theorem map_op_pmap_quditGate {d : ℕ} [NeZero d] :
    ∀ (l : List (Matrix (Fin d) (Fin d) ℂ))
      (H : ∀ g ∈ l, g ∈ Matrix.unitaryGroup (Fin d) ℂ),
      (l.pmap (fun _ h => quditGate h) H).map Evolution.op
        = l.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d))
  | [], _ => rfl
  | a :: t, H => by
      simp only [List.pmap, List.map_cons, quditGate_op]
      congr 1
      exact map_op_pmap_quditGate t (fun g hg => H g (List.mem_cons_of_mem a hg))

/-- **The operator of the QFT circuit is the Figure 5.1 gate-product matrix.** Its underlying
continuous linear map is `Matrix.toEuclideanCLM (Concrete.qftGateCircuit n)`, because the operator
of an `Evolution`-monoid product is the operator product (`Evolution.op_prod`), each promoted gate's
operator is its matrix through `toEuclideanCLM` (`map_op_pmap_quditGate`), and `toEuclideanCLM` is
multiplicative (`map_list_prod`). -/
theorem qftCircuitEvolution_op (n : ℕ) :
    (qftCircuitEvolution n).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) (Concrete.qftGateCircuit n) := by
  rw [qftCircuitEvolution, Evolution.op_prod, qftGateEvolutionSequence, map_op_pmap_quditGate,
    Concrete.qftGateCircuit]
  exact (map_list_prod (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)))
    (Concrete.qftGateSequence n).reverse).symm

/-- **Problem 5.2 (the QFT is its Figure 5.1 circuit).** The monolithic quantum Fourier transform
`qftEvolution (2ⁿ)` equals the sequential composition `qftCircuitEvolution n` of its Figure 5.1
gates — the wire-addressed Hadamards, the controlled-`Rₖ` rotations, and the swap layer (N&C
product form 5.4). Both operators are `Matrix.toEuclideanCLM (qftMatrix (2ⁿ))`: the circuit's by
`qftCircuitEvolution_op` together with the `Concrete` correctness
`Concrete.qftGateCircuit_eq_qftMatrix`, the transform's by definition. This is the postulate-level
realisation of the QFT as a circuit — the object over which the measured-QFT reduction defers each
two-wire controlled gate. -/
theorem qftEvolution_eq_qftCircuitEvolution (n : ℕ) :
    qftEvolution (2 ^ n) = qftCircuitEvolution n := by
  apply Evolution.ext
  rw [qftCircuitEvolution_op, Concrete.qftGateCircuit_eq_qftMatrix]
  rfl

end

end AxQM
