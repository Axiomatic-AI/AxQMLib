/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.SingleQubitWire
import AxQM.Concrete.Hadamard
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.QftGateCount
import ToMathlib.Algebra.BigOperators.Fin

/-!
# Concrete: the gate-level Figure 5.1 quantum-Fourier-transform circuit

Nielsen & Chuang, §5.1, p. 219, Figure 5.1, give the **efficient circuit for the quantum Fourier
transform** on `n` qubits: process the wires in turn, applying to wire `t` one Hadamard followed by
a cascade of *controlled-`Rₖ`* phase rotations from the later wires, and finish with swap gates that
reverse the wire order. The gate

```
  Rₖ = diag(1, e^{2πi/2^k})                                   (5.11)
```

is a one-qubit phase rotation, and the controlled-`Rₖ` acting between two wires is the diagonal
controlled phase `|0⟩⟨0|⊗I + |1⟩⟨1|⊗Rₖ`.

This file assembles that circuit as an explicit **matrix product** over the raw `2ⁿ`-dimensional
register `Fin (2ⁿ)`, reusing the wire-gate framework already in `Concrete/` — `singleQubitOnWire`
(uncontrolled one-qubit gate, `AxQM/Concrete/SingleQubitWire.lean`), `mcCtrlSingleQubit` (controlled
one-qubit gate, `AxQM/Concrete/MultiControlledSingleQubit.lean`), and `permGate` (the swap
permutation, `AxQM/Concrete/PermutationGate.lean`) — under the little-endian bit encoding
`finFunctionFinEquiv : (Fin n → Fin 2) ≃ Fin (2ⁿ)`
(`k = ∑ₗ kₗ 2ˡ`), the same encoding as the product representation `Concrete.qftMatrix_apply_prod`.

## What is formalised

* `qftRk k` — the phase matrix `Rₖ = diag(1, e^{2πi/2^k})` (eq. 5.11), and
  `qftRk_mem_unitaryGroup` — it is unitary (its lone off-`1` entry is a unit-modulus phase).
* `qftHadamardGate n t`, `qftControlledGate n t c` — the two elementary gates on the `n`-qubit
  register: the Hadamard on wire `t`, and the controlled-`R_{(c-t)+1}` from control wire `c` onto
  target wire `t` (a control at distance `d = c - t` carries `R_{d+1}`, so the nearest control
  `c = t+1` carries `R₂`, matching Figure 5.1's `R₂ … R_{n-t}` cascade).
* `qftTargetControls n t` — the later wires `t+1, …, n-1` that control target `t`
  (`length_qftTargetControls`: there are `n-1-t` of them); `qftBlock n t` — target `t`'s block
  (Hadamard, then its controlled gates); `qftBitReversal n` — the wire-reversing permutation of the
  swap layer.
* `qftGateSequence n` — the full ordered gate list of Figure 5.1: the wire-reversal (swap) layer,
  then every target's block in order `t = 0, 1, …, n-1`; and
  `qftGateCircuit n = (qftGateSequence n).reverse.prod` — the circuit as a `2ⁿ × 2ⁿ` matrix. The
  list is in **circuit/time order** (the gate applied first is written first); the matrix is the
  product of the *reversed* list so that, read as an operator, the first-listed gate acts first
  (`(g₁ :: … :: gₘ).reverse.prod = gₘ * … * g₁`). **Endianness — why the swap layer comes first.**
  Under the little-endian encoding `finFunctionFinEquiv` (`k = ∑ₗ kₗ 2ˡ`, wire `0` the *least*
  significant), the blocks process wire `0` first with its controls drawn from the *higher* wires,
  so wire `0` plays the most-significant role and the block cascade builds the QFT's phases in
  reverse-bit order. Placing the wire-reversal **before** the blocks (rather than after, as in a
  big-endian drawing of Figure 5.1) is exactly what makes the resulting matrix equal to the
  little-endian `qftMatrix 2ⁿ` — the identity `qftGateCircuit 2 = qftMatrix 4` is certified in
  `AxQM/Concrete/QftGateCircuitCorrectness.lean` (general `n` in
  `AxQM/Concrete/QftGateCircuitEqMatrix.lean`). The swap layer's *position* is
  immaterial to Exercise 5.6: the perturbable controlled-`Rₖ` gates (`qftControlledGates`) and their
  count are unchanged; only the parameter-free swap moves to the input end.
* `qftGateCircuit_mem_unitaryGroup` — the circuit is **unitary**: every factor (Hadamard, controlled
  phase, swap permutation) is unitary, so their product is (`Submonoid.list_prod_mem`). This is
  N&C's remark that the circuit "proves that the quantum Fourier transform is unitary, since each
  gate in the circuit is unitary."
* `qftControlledGates n` — the controlled-`Rₖ` gates of the circuit (the `qftBlock` cascades,
  concatenated), and `length_qftControlledGates` — there are exactly `qftControlledRkCount n =
  n(n-1)/2` of them. These are the only gates carrying a continuous phase parameter, hence the ones
  implemented to finite precision in Exercise 5.6; the Hadamards and swaps are parameter-free.

## Why this file exists (Exercise 5.6)

The faithful `Ω(n²/p(n))` lower bound of Exercise 5.6 (perturbing the controlled-`Rₖ` gates to
precision `Δ = 1/p(n)` costs error `Θ(n²/p(n))`) requires the Figure 5.1 circuit as a *formal*
object whose `Rₖ` gates one can individually perturb — the postulate-level `qftEvolution` is the
matrix-derived transform, monolithic, with no exposed gate structure. This file supplies that
object: the gate product `qftGateCircuit`, its unitarity, and the identification of its `n(n-1)/2`
perturbable controlled gates (`qftControlledGates`). That `qftGateCircuit n = qftMatrix 2ⁿ` (the
circuit computes the transform, N&C eqs. 5.12–5.18, via the product representation
`qftMatrix_apply_eq_prod_wirePhase`) is proved in `AxQM/Concrete/QftGateCircuitEqMatrix.lean`; the
perturbation and the coherent lower bound build on that. This is the general-`n` gate-level
counterpart of the two-qubit `qftFour_eq_prod`.

## Setting

Every statement is about complex matrices (`Matrix`, `Matrix.unitaryGroup`), the encoding
equivalence `finFunctionFinEquiv`, permutations, and the gate-count function
`qftControlledRkCount`, alongside the matrix `qftMatrix` and the gate count it consumes.
-/

namespace AxQM.Concrete

open Matrix

/-- **The `Rₖ` phase gate** `Rₖ = diag(1, e^{2πi/2^k})` (Nielsen & Chuang eq. 5.11): the one-qubit
phase rotation whose controlled version is the QFT circuit's conditional rotation. -/
noncomputable def qftRk (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (2 * Real.pi * Complex.I / 2 ^ k)]

/-- **`Rₖ` is unitary.** It is diagonal with entries `1` and the unit-modulus phase `e^{2πi/2^k}`;
concretely `conj(e^{2πi/2^k})·e^{2πi/2^k} = e^{-z}·e^{z} = 1` because the exponent `z = 2πi/2^k` is
purely imaginary (`conj z = -z`). -/
theorem qftRk_mem_unitaryGroup (k : ℕ) : qftRk k ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hz : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 2 ^ k)
      = -(2 * Real.pi * Complex.I / 2 ^ k) := by
    simp only [map_div₀, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal, map_pow]; ring
  have hφ : (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I / 2 ^ k))
      * Complex.exp (2 * Real.pi * Complex.I / 2 ^ k) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add, hz, neg_add_cancel, Complex.exp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qftRk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hφ]

/-- **The Hadamard gate on wire `t`** of the `n`-qubit register — the parameter-free gate that
opens each block of Figure 5.1 (`singleQubitOnWire` with the complex Hadamard `hadamardC`). -/
noncomputable def qftHadamardGate (n : ℕ) (t : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  singleQubitOnWire finFunctionFinEquiv t hadamardC

/-- **The controlled-`Rₖ` gate from control wire `c` onto target wire `t`** (Figure 5.1's
conditional rotation): apply `R_{(c-t)+1}` to wire `t` when wire `c` is `1`. A control at distance
`d = c - t` carries `R_{d+1}`, so the nearest control `c = t+1` carries `R₂`, and the cascade over
`c = t+1, …, n-1` reproduces the `R₂ … R_{n-t}` rotations N&C apply to wire `t`. -/
noncomputable def qftControlledGate (n : ℕ) (t c : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  mcCtrlSingleQubit finFunctionFinEquiv {c} t (qftRk ((c : ℕ) - (t : ℕ) + 1))

/-- **The control wires of target `t`:** the later wires `t+1, …, n-1`, obtained by dropping the
first `t+1` wires of `List.finRange n`. -/
def qftTargetControls (n : ℕ) (t : Fin n) : List (Fin n) :=
  (List.finRange n).drop ((t : ℕ) + 1)

/-- Target `t` has `n - 1 - t` control wires — the `n - t` wires above `t` less the wire `t` itself
(`List.length_drop` on `List.finRange`). -/
theorem length_qftTargetControls (n : ℕ) (t : Fin n) :
    (qftTargetControls n t).length = n - 1 - (t : ℕ) := by
  rw [qftTargetControls, List.length_drop, List.length_finRange]; omega

/-- **The controlled-`Rₖ` cascade of target `t`'s block:** the controlled gates from each of `t`'s
control wires, in order. Concatenated over all targets, these are the circuit's `qftControlledGates`
(the perturbable gates of Exercise 5.6). -/
noncomputable def qftBlockControlledGates (n : ℕ) (t : Fin n) :
    List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  (qftTargetControls n t).map (qftControlledGate n t)

/-- **Target `t`'s Figure-5.1 block:** the Hadamard on wire `t`, followed by its controlled-`Rₖ`
cascade. -/
noncomputable def qftBlock (n : ℕ) (t : Fin n) : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  qftHadamardGate n t :: qftBlockControlledGates n t

/-- **The wire-reversal permutation** realised by the swap layer at the end of Figure 5.1: it
reverses the order of the `n` wires (`f ↦ f ∘ Fin.rev`). -/
def qftBitReversal (n : ℕ) : Equiv.Perm (Fin n → Fin 2) :=
  Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))

/-- **The full ordered gate list of the Figure 5.1 QFT circuit:** the wire-reversal (swap) gate,
then each target's block in order `t = 0, 1, …, n-1`. The list is in **circuit/time order** — the
gate applied first appears first, so the swap layer acts first. Under the little-endian encoding
(`finFunctionFinEquiv`, wire `0` least significant) the blocks process wire `0` first with controls
from the higher wires; applying the wire reversal at the *input* (rather than the output, as a
big-endian drawing of Figure 5.1 would) is what lands the circuit on the little-endian
`qftMatrix 2ⁿ` (the module docstring's endianness note; certified `qftGateCircuit 2 = qftMatrix 4`
in `AxQM/Concrete/QftGateCircuitCorrectness.lean`). The controlled-`Rₖ` gates — Exercise 5.6's
entire content — are unaffected by the swap's position. -/
noncomputable def qftGateSequence (n : ℕ) : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  permGate finFunctionFinEquiv (qftBitReversal n) :: (List.finRange n).flatMap (qftBlock n)

/-- **The gate-level Figure 5.1 QFT circuit** as a `2ⁿ × 2ⁿ` matrix: the product of
`qftGateSequence` in reverse, so that as an operator the first-listed gate acts first
(`(g₁ :: … :: gₘ).reverse.prod = gₘ * … * g₁`). Reusing the wire-gate framework, this is a fully
explicit unitary computing the quantum Fourier transform (its equality to `qftMatrix 2ⁿ` is the
next step of the Exercise 5.6 arc). -/
noncomputable def qftGateCircuit (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (qftGateSequence n).reverse.prod

/-- **Every gate of the Figure 5.1 QFT circuit is unitary** (Nielsen & Chuang, p. 219: "each gate in
the circuit is unitary"): the swap permutation (`permGate_mem_unitaryGroup`), the Hadamards
(`singleQubitOnWire_mem_unitaryGroup`, `hadamardC_mem_unitaryGroup`), and the controlled rotations
(`mcCtrlSingleQubit_mem_unitaryGroup`, `qftRk_mem_unitaryGroup`). This is the reusable per-factor
obligation: the circuit's own unitarity (`qftGateCircuit_mem_unitaryGroup`) and the chaining bound
of Exercise 5.6 (`qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le`) both consume it. -/
theorem qftGateSequence_forall_mem_unitaryGroup (n : ℕ) :
    ∀ g ∈ qftGateSequence n, g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  intro g hg
  rw [qftGateSequence, List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact permGate_mem_unitaryGroup _ _
  · rw [List.mem_flatMap] at hg
    obtain ⟨t, _, hgt⟩ := hg
    rw [qftBlock, List.mem_cons] at hgt
    rcases hgt with rfl | hmap
    · exact singleQubitOnWire_mem_unitaryGroup _ _ hadamardC_mem_unitaryGroup
    · rw [qftBlockControlledGates, List.mem_map] at hmap
      obtain ⟨c, _, rfl⟩ := hmap
      exact mcCtrlSingleQubit_mem_unitaryGroup _ _ _ (qftRk_mem_unitaryGroup _)

/-- **The QFT circuit is unitary** (Nielsen & Chuang, p. 219): the reverse product of the gate list
`qftGateSequence`, whose every factor is unitary (`qftGateSequence_forall_mem_unitaryGroup`), lies
in the unitary group (`Submonoid.list_prod_mem`). -/
theorem qftGateCircuit_mem_unitaryGroup (n : ℕ) :
    qftGateCircuit n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  Submonoid.list_prod_mem _ fun g hg =>
    qftGateSequence_forall_mem_unitaryGroup n g (List.mem_reverse.mp hg)

/-- **The controlled-`Rₖ` gates of the QFT circuit:** every block's controlled cascade, concatenated
over the targets `t = 0, …, n-1`. These are exactly the gates carrying a continuous phase parameter
(the Hadamards and the swap are parameter-free), hence the ones Exercise 5.6 implements to finite
precision `Δ`. -/
noncomputable def qftControlledGates (n : ℕ) : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  (List.finRange n).flatMap (qftBlockControlledGates n)

/-- **The QFT circuit has `n(n-1)/2` controlled-`Rₖ` gates** (Nielsen & Chuang, Figure 5.1 count):
`(qftControlledGates n).length = qftControlledRkCount n`. Target `t` contributes its `n-1-t`
controls (`length_qftTargetControls`), and `∑_{t<n} (n-1-t) = ∑_{t<n} t = n(n-1)/2` by reflecting
the Gauss sum (`Finset.sum_range_reflect`, `qftControlledRkCount_eq_sum`). This is the `Θ(n²)`
count of imprecise gates underlying Exercise 5.6's `Θ(n²/p(n))`. -/
theorem length_qftControlledGates (n : ℕ) :
    (qftControlledGates n).length = qftControlledRkCount n := by
  rw [qftControlledGates, List.length_flatMap, qftControlledRkCount_eq_sum]
  simp only [qftBlockControlledGates, List.length_map, length_qftTargetControls]
  rw [← List.ofFn_eq_map, List.sum_ofFn, Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n,
    Finset.sum_range_reflect (fun i => i) n]

end AxQM.Concrete
