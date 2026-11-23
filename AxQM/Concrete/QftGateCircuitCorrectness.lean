/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QftGateCircuit
import AxQM.Concrete.QuantumFourierTransform

/-!
# Concrete: the QFT circuit's controlled-`Rₖ` cascade is a diagonal phase gate (N&C eqs. 5.5–5.6)

Building toward the correctness of the gate-level Figure 5.1 circuit
(`Concrete.qftGateCircuit n = qftMatrix 2ⁿ`, N&C eqs. 5.12–5.18), this file establishes the first
structural step: **the controlled-`Rₖ` rotations acting on a wire are simultaneously diagonal in the
computational basis, so a whole block's cascade collapses to a single diagonal phase gate** — the
map (N&C eqs. 5.5–5.6) that appends the binary-fraction tail `0.j_{t+1}…j_{n-1}` to the phase of
wire `t`.

Each Figure 5.1 conditional rotation `qftControlledGate n t c` applies `Rₖ = diag(1, e^{2πi/2ᵏ})`
(itself diagonal) to target wire `t` conditioned on control wire `c`, so it is *control-diagonal*:
it multiplies the basis state `|enc x⟩` by the phase `e^{2πi/2^{c-t+1}}` exactly when both `x_c = 1`
and `x_t = 1`, and by `1` otherwise. Because diagonal matrices commute and their product is the
pointwise product of their diagonals, the target-`t` cascade `qftBlockControlledGates n t` — the
rotations from all of `t`'s control wires — is again a single diagonal gate, whose phase on
`|enc x⟩` is the product over the active controls, `∏_{c > t, x_c = 1} e^{2πi/2^{c-t+1}}` (present
only when `x_t = 1`).

The general fact that a subset-controlled *diagonal* single-qubit gate is diagonal
(`mcCtrlSingleQubit_diagonal`, generalising `mcCtrlSingleQubit_smul_one_eq_diagonal` from a global
phase `z • 1` to an arbitrary diagonal block) lives with the rest of the `mcCtrlSingleQubit` family
in `AxQM/Concrete/MultiControlledSingleQubit.lean`; this file consumes it.

## What is formalised

* `diagonal_map_prod` — a list-indexed family of diagonal matrices multiplies to the diagonal of the
  entrywise list product of the diagonals (general `Matrix` algebra).
* `qftRk_eq_diagonal` — `Rₖ = diagonal ![1, e^{2πi/2ᵏ}]`.
* `qftTargetControls_lt` — a target's control wires all lie strictly above it.
* `qftControlledGate_eq_diagonal` — the Figure 5.1 controlled rotation from `c` onto `t` (`t ≠ c`)
  is the diagonal gate `diag(fun i => if x_c = 1 then ![1, e^{2πi/2^{c-t+1}}] (x_t) else 1)`.
* `qftBlockControlledGates_prod_eq_diagonal` — target `t`'s whole controlled cascade is the single
  diagonal phase gate `diag(fun i => if x_t = 1 then ∏_{c ∈ controls, x_c = 1} e^{2πi/2^{c-t+1}}
  else 1)`.

Composing this cascade with the block-opening Hadamard, then the
inter-block interleave and the final bit reversal, identifies the circuit with `qftMatrix 2ⁿ`.

## Setting

Every statement is about complex matrices (`Matrix`, `Matrix.diagonal`), the encoding
equivalence `finFunctionFinEquiv`, and the circuit objects of `AxQM/Concrete/QftGateCircuit.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **A product of diagonal matrices built from a list is diagonal**, with the entrywise list
product of their diagonals: `∏_{c ∈ l} diagonal (g c) = diagonal (fun i => ∏_{c ∈ l} g c i)` — the
list-product form of the fact that `Matrix.diagonal` is a multiplicative homomorphism. -/
theorem diagonal_map_prod {ι : Type*} (l : List ι) (g : ι → Fin d → ℂ) :
    (l.map fun c => Matrix.diagonal (g c)).prod
      = Matrix.diagonal fun i => (l.map fun c => g c i).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    rw [List.map_cons, List.prod_cons]

/-- **The `Rₖ` phase gate is diagonal**: `qftRk k = diagonal ![1, e^{2πi/2ᵏ}]` (N&C eq. 5.11 in
diagonal form). -/
theorem qftRk_eq_diagonal (k : ℕ) :
    qftRk k = Matrix.diagonal ![1, Complex.exp (2 * Real.pi * Complex.I / 2 ^ k)] := by
  rw [qftRk, Matrix.diagonal_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The control wires of target `t` all lie strictly above `t`.** If `c` controls target `t` in
the Figure 5.1 circuit (`c ∈ qftTargetControls n t`, the wires `t+1, …, n-1`), then `t < c`; in
particular `t ≠ c`, so `t` is not among its own controls. -/
theorem qftTargetControls_lt {n : ℕ} {t c : Fin n} (hc : c ∈ qftTargetControls n t) :
    (t : ℕ) < (c : ℕ) := by
  rw [qftTargetControls, List.mem_iff_getElem] at hc
  obtain ⟨k, hk, hck⟩ := hc
  rw [List.getElem_drop, List.getElem_finRange] at hck
  have h2 := congrArg Fin.val hck
  simp only [Fin.val_cast] at h2
  omega

/-- **Each Figure 5.1 conditional rotation is a diagonal phase gate.** For `t ≠ c`, the
controlled-`Rₖ` gate from control wire `c` onto target wire `t` is
`diagonal (fun i => if x_c = 1 ∧ x_t = 1 then e^{2πi/2^{c-t+1}} else 1)`: it multiplies `|enc x⟩` by
the rotation phase `e^{2πi/2^{c-t+1}}` exactly when both the control bit `x_c` and the target bit
`x_t` are `1`, and by `1` otherwise (`mcCtrlSingleQubit_diagonal` on the diagonal block `Rₖ`). -/
theorem qftControlledGate_eq_diagonal (n : ℕ) (t c : Fin n) (htc : t ≠ c) :
    qftControlledGate n t c = Matrix.diagonal fun i =>
      if finFunctionFinEquiv.symm i c = 1 ∧ finFunctionFinEquiv.symm i t = 1
      then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) else 1 := by
  rw [qftControlledGate, qftRk_eq_diagonal,
    mcCtrlSingleQubit_diagonal _ (by simpa using htc)]
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  simp only [Finset.mem_singleton, forall_eq]
  by_cases hc : finFunctionFinEquiv.symm i c = 1
  · rw [ite_eq_left hc]
    generalize finFunctionFinEquiv.symm i t = v
    fin_cases v <;> simp [hc]
  · rw [ite_eq_right hc]
    simp [hc]

/-- **Target `t`'s controlled-`Rₖ` cascade is a single diagonal phase gate** (N&C eqs. 5.5–5.6).
The product of all of target `t`'s conditional rotations is the diagonal gate whose phase on
`|enc x⟩` is the product, over `t`'s control wires `c`, of `e^{2πi/2^{c-t+1}}` for each active
control (`x_c = 1`) when the target bit `x_t = 1` is set — collapsing the whole rotation cascade of
Figure 5.1's block to one diagonal matrix. Every factor is diagonal
(`qftControlledGate_eq_diagonal`, each control wire lying above `t` by `qftTargetControls_lt`), and
diagonals multiply pointwise (`diagonal_map_prod`). -/
theorem qftBlockControlledGates_prod_eq_diagonal (n : ℕ) (t : Fin n) :
    (qftBlockControlledGates n t).prod = Matrix.diagonal fun i =>
      ((qftTargetControls n t).map fun c =>
        if finFunctionFinEquiv.symm i c = 1 ∧ finFunctionFinEquiv.symm i t = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) else 1).prod := by
  rw [qftBlockControlledGates,
    List.map_congr_left fun c hc => qftControlledGate_eq_diagonal n t c
      (Fin.ne_of_val_ne (ne_of_lt (qftTargetControls_lt hc))),
    diagonal_map_prod]

/-!
## Correctness certificate: the two-qubit circuit computes the transform

Beyond the structural cascade lemma above, we certify that the gate circuit actually *equals* the
Fourier matrix in the smallest nontrivial case, `n = 2`: `qftGateCircuit 2 = qftMatrix 4`. Under the
little-endian encoding this is the two-qubit circuit — the wire reversal, then `H₀`, the controlled
`R₂` from wire `1` onto wire `0`, and `H₁` — reproducing `Fₖⱼ = ½·iʲᵏ` exactly. The computation
proceeds by rewriting each of the four elementary gates to its explicit `4 × 4` matrix and
multiplying.

This is the certificate that fixes the *endianness convention* of `qftGateSequence`: the wire
reversal is applied **first** (`qftGateSequence = swap :: blocks`), which is precisely what lands
the circuit on the little-endian `qftMatrix 4` — applying it last would instead give `P·qftMatrix·P`
(the transform conjugated by the bit reversal). The general-`n` identity
`qftGateCircuit n = qftMatrix 2ⁿ` (N&C eqs. 5.12–5.18) is proved in
`AxQM/Concrete/QftGateCircuitEqMatrix.lean`, built on this cascade lemma and the product
representation `qftMatrix_apply_eq_prod_wirePhase`. -/

/-- **The little-endian basis-decode table on `Fin (2²)`:** bit `j` of index `i` is
`![![0, 0], ![1, 0], ![0, 1], ![1, 1]] i j` — i.e. `0 ↦ (0,0), 1 ↦ (1,0), 2 ↦ (0,1), 3 ↦ (1,1)`
(wire `0` least significant). A finite decidable table shared by the two-qubit gate-literal proofs
below, replacing the per-gate inline decode facts. Stated in the fully-applied
`finFunctionFinEquiv.symm i j` form and over `Fin (2 ^ 2)` (the register index type produced by
`singleQubitOnWire`) so that it matches those goals; it is applied through `simp only` (the default
simp set otherwise pre-empts the rewrite). -/
private theorem finFunctionFinEquiv_symm_fin_four (i : Fin (2 ^ 2)) (j : Fin 2) :
    finFunctionFinEquiv.symm i j = ![![0, 0], ![1, 0], ![0, 1], ![1, 1]] i j := by
  decide +revert

/-- The Hadamard on wire `0` of the two-qubit register as an explicit `4 × 4` matrix (block-diagonal
over the wire-`1` value, in the little-endian basis order `00, 10, 01, 11`). -/
private theorem qftHadamardGate_two_zero :
    qftHadamardGate 2 0 = (Real.sqrt 2 : ℂ)⁻¹ •
      !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1] := by
  rw [qftHadamardGate]; ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [singleQubitOnWire_apply, Fin.forall_fin_two, finFunctionFinEquiv_symm_fin_four];
      simp [hadamardC])

/-- The Hadamard on wire `1` of the two-qubit register as an explicit `4 × 4` matrix. -/
private theorem qftHadamardGate_two_one :
    qftHadamardGate 2 1 = (Real.sqrt 2 : ℂ)⁻¹ •
      !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] := by
  rw [qftHadamardGate]; ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [singleQubitOnWire_apply, Fin.forall_fin_two, finFunctionFinEquiv_symm_fin_four];
      simp [hadamardC])

/-- The controlled-`R₂` gate from wire `1` onto wire `0` as an explicit `4 × 4` matrix: the diagonal
phase gate multiplying the `|11⟩` amplitude by `e^{2πi/4} = i`. -/
private theorem qftControlledGate_two :
    qftControlledGate 2 0 1 = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, Complex.I] := by
  have hI : Complex.exp
      (2 * Real.pi * Complex.I / 2 ^ (((1 : Fin 2) : ℕ) - ((0 : Fin 2) : ℕ) + 1)) = Complex.I := by
    rw [show (((1 : Fin 2) : ℕ) - ((0 : Fin 2) : ℕ) + 1) = 2 from by decide,
      show (2 * (Real.pi : ℂ) * Complex.I / 2 ^ 2) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I]
    simp
  rw [qftControlledGate_eq_diagonal 2 0 1 (by decide)]
  simp only [hI]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.diagonal_apply, finFunctionFinEquiv_symm_fin_four]; simp)

/-- The two-qubit wire-reversal (swap) gate as an explicit `4 × 4` permutation matrix: it swaps the
basis states `|10⟩` and `|01⟩` (indices `1` and `2`). -/
private theorem qftBitReversal_two_permGate :
    permGate finFunctionFinEquiv (qftBitReversal 2)
      = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := by
  -- The reversal permutation of the basis indices is `0 ↦ 0, 1 ↦ 2, 2 ↦ 1, 3 ↦ 3`.
  have hσ : ∀ k : Fin 4, finFunctionFinEquiv (qftBitReversal 2 (finFunctionFinEquiv.symm k))
      = ![0, 2, 1, 3] k := by decide
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permGate_apply, hσ]

/-- The two-qubit gate circuit as the ordered matrix product `H₁ · R₂ · H₀ · swap` (the wire
reversal applied first, per `qftGateSequence`). -/
private theorem qftGateCircuit_two_eq_prod :
    qftGateCircuit 2 = qftHadamardGate 2 1 * qftControlledGate 2 0 1 * qftHadamardGate 2 0
      * permGate finFunctionFinEquiv (qftBitReversal 2) := by
  rw [qftGateCircuit, qftGateSequence]
  have h : (List.finRange 2).flatMap (qftBlock 2)
      = [qftHadamardGate 2 0, qftControlledGate 2 0 1, qftHadamardGate 2 1] := by
    simp [List.finRange, qftBlock, qftBlockControlledGates, qftTargetControls, List.flatMap]
  rw [h]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]

/-- **The two-qubit gate circuit computes the quantum Fourier transform:**
`qftGateCircuit 2 = qftMatrix 4` (Nielsen & Chuang §5.1, the `n = 2` case of the circuit
correctness). Rewriting each of the four elementary gates to its explicit `4 × 4` matrix, the
ordered product `H₁ · R₂ · H₀ · swap` (wire reversal first) reproduces `Fₖⱼ = ½·iʲᵏ` exactly — the
Fourier matrix, not its bit-reversal conjugate. This certifies the swap-first convention of
`qftGateSequence` and is the base case of `qftGateCircuit n = qftMatrix 2ⁿ`. -/
theorem qftGateCircuit_two_eq_qftMatrix : qftGateCircuit 2 = qftMatrix 4 := by
  -- `½ = (√2)⁻¹ · (√2)⁻¹`, the two Hadamard normalisations combining.
  have hsqrt : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  -- The four elementary gates (integer/`i` parts) multiply to the Fourier matrix's `iʲᵏ` table.
  have hprod : (!![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] : Matrix (Fin 4) (Fin 4) ℂ)
      * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, Complex.I]
      * !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]
      * !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]
      = !![1, 1, 1, 1;
          1, Complex.I, -1, -Complex.I;
          1, -1, 1, -1;
          1, -Complex.I, -1, Complex.I] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  -- `qftMatrix 4` in the same explicit form: `½ · iʲᵏ`.
  have hR : qftMatrix 4 = (2 : ℂ)⁻¹ •
      !![1, 1, 1, 1;
        1, Complex.I, -1, -Complex.I;
        1, -1, 1, -1;
        1, -Complex.I, -1, Complex.I] := by
    have hroot : qftPrimitiveRoot 4 = Complex.I := by
      rw [qftPrimitiveRoot, Nat.cast_ofNat, show (2 * (Real.pi : ℂ) * Complex.I / 4)
        = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
      simp
    have h4 : (Real.sqrt 4 : ℂ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qftMatrix, hroot, h4, Matrix.smul_apply, pow_succ, Complex.I_mul_I]
  rw [qftGateCircuit_two_eq_prod, qftHadamardGate_two_one, qftControlledGate_two,
    qftHadamardGate_two_zero, qftBitReversal_two_permGate, hR]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hsqrt, hprod]

end AxQM.Concrete
