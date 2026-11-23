/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftTowerHadamard

/-!
# The base case of the measured-QFT tower induction (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) is assembled by an induction on the tower
depth: the head control wire's Figure 5.1 gates (a Hadamard and the controlled-`Rₖ` cascade it
drives) are peeled off `qftTowerEvolution (n+1)`, its measurement deferred past the cascade
(`qtowerHeadPhaseCascade_measure_*`), and the tail recursion re-enters
`qftTowerEvolution n` on the remaining wires. Every induction needs a base case, and this file
supplies it: at depth `0` the tower QFT is a single one-qubit Hadamard — already a one-wire gate
with nothing to defer.

## What is formalised

* `qftEvolution_two_eq_qftHadamardEvolution` — **the quantum Fourier transform on one qubit is the
  Hadamard gate** (Nielsen & Chuang §5.1: the `2 × 2` DFT is `H`). The register QFT
  `qftEvolution 2` on `qudit 2` equals the Figure 5.1 Hadamard gate `qftHadamardEvolution 1 0` on
  the single wire — both have operator `Matrix.toEuclideanCLM` of the same matrix, since
  `qftMatrix 2 = singleQubitOnWire finFunctionFinEquiv 0 hadamardC` (each is `hadamardC`).
* `qftTowerEvolution_zero` — **the tower QFT at depth `0` is the single-wire Hadamard**,
  `qftTowerEvolution 0 = hadamardGate`. The transported QFT `qftTowerEvolution 0` on the one-wire
  tower `qtower 0 qubit = qubit` is, through the register bridge, the Figure 5.1 Hadamard placed on
  the sole wire — which on a one-wire tower is just `hadamardGate`. This is the base case of the
  outer tower induction: a genuine one-qubit gate, no two-wire gate, so the measured-QFT reduction
  holds trivially at `n = 0`.

## Proof

`qftEvolution_two_eq_qftHadamardEvolution` reduces via `Evolution.ext` to the matrix identity
`qftMatrix 2 = singleQubitOnWire finFunctionFinEquiv 0 hadamardC`, split through `hadamardC`: the
QFT matrix `qftMatrix 2` is `hadamardC` because `qftPrimitiveRoot 2 = e^{πi} = -1`, so its entry
`(1/√2)·(qftPrimitiveRoot 2)^{jk}` is `(1/√2)·(-1)^{jk} = hadamardC k j`; and `singleQubitOnWire`
of a one-wire register is the block itself, its wire-locality guard on `Fin 1` being vacuous and
its bit read `finFunctionFinEquiv.symm i 0 = i`. `qftTowerEvolution_zero` then rewrites the QFT on
the tower through this identity and the Hadamard re-expression
`quditPowTower_congr_qftHadamardEvolution`, whose depth-`0` value
`Evolution.qtowerSingleWire 0 _ hadamardGate` is `hadamardGate` by the base case of
`Evolution.qtowerSingleWire`.

-/

open Matrix

noncomputable section

namespace AxQM

open Concrete

/-- **The quantum Fourier transform on one qubit is the Hadamard gate** (Nielsen & Chuang §5.1: the
`2 × 2` discrete Fourier transform `F₂` is the Hadamard `H`). The register QFT `qftEvolution 2` on
the two-level register `qudit 2` equals the Figure 5.1 Hadamard gate `qftHadamardEvolution 1 0` —
the single-wire Hadamard on the one-qubit register. Both operators are `Matrix.toEuclideanCLM` of
the same `2 × 2` matrix `hadamardC`: the QFT kernel `(1/√2)·(qftPrimitiveRoot 2)^{jk}` is
`(1/√2)·(-1)^{jk}` since `qftPrimitiveRoot 2 = e^{πi} = -1`, and `singleQubitOnWire` on a one-wire
register is its block. This is the depth-`0` fact the tower QFT base case `qftTowerEvolution_zero`
rewrites through. -/
theorem qftEvolution_two_eq_qftHadamardEvolution :
    qftEvolution 2 = qftHadamardEvolution 1 0 := by
  have hroot : qftPrimitiveRoot 2 = -1 := by
    rw [qftPrimitiveRoot,
      show (2 * (Real.pi : ℂ) * Complex.I / (2 : ℕ)) = (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_pi_mul_I]
  have hqft : qftMatrix 2 = hadamardC := by
    ext k j
    rw [qftMatrix, hroot, hadamardC_apply]
    push_cast
    rw [mul_comm (k : ℕ) (j : ℕ)]
  have hsymm : ∀ i : Fin 2, finFunctionFinEquiv.symm i (0 : Fin 1) = i := by
    intro i
    apply Fin.ext
    rw [finFunctionFinEquiv_symm_apply_val]
    simp [Nat.mod_eq_of_lt i.isLt]
  have hwire : singleQubitOnWire finFunctionFinEquiv (0 : Fin 1) hadamardC = hadamardC := by
    ext i i'
    rw [singleQubitOnWire_apply, ite_eq_left (fun x hx => absurd (Fin.fin_one_eq_zero x) hx),
      hsymm i, hsymm i']
  apply Evolution.ext
  rw [qftEvolution_op, qftHadamardEvolution, quditGate_op, hqft, hwire]

/-- **The tower QFT at depth `0` is the single-wire Hadamard**:
`qftTowerEvolution 0 = hadamardGate`.
The quantum Fourier transform transported onto the one-wire control tower `qtower 0 qubit = qubit`
(through the register bridge `quditPowTower 0`) is a single one-qubit Hadamard — the QFT on one
qubit (`qftEvolution_two_eq_qftHadamardEvolution`) re-expressed on the tower as the Hadamard on the
sole wire (`quditPowTower_congr_qftHadamardEvolution`), which on a one-wire tower is `hadamardGate`
itself (`Evolution.qtowerSingleWire 0 _ g = g`). This is the base case of the outer tower induction
assembling the measured-QFT reduction (Problem 5.2): at `n = 0` the whole circuit is already a
genuine one-qubit gate on the single measured wire, with no two-wire gate to defer. -/
theorem qftTowerEvolution_zero : qftTowerEvolution 0 = hadamardGate := by
  have h : qftTowerEvolution 0 = Evolution.congr (quditPowTower 0) (qftHadamardEvolution 1 0) := by
    rw [qftTowerEvolution]; congr 1; exact qftEvolution_two_eq_qftHadamardEvolution
  rw [h, quditPowTower_congr_qftHadamardEvolution]
  rfl

end AxQM
