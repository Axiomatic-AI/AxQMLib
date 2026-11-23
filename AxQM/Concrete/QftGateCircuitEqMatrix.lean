/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QftGateCircuitState
import AxQM.Concrete.QftProductRepresentation

/-!
# Concrete: the Figure 5.1 QFT circuit computes the transform (`qftGateCircuit n = qftMatrix 2ⁿ`)

This file completes the correctness of the gate-level Figure 5.1 quantum-Fourier-transform circuit,
Nielsen & Chuang eqs. 5.12–5.18: the explicit gate product `Concrete.qftGateCircuit n` **equals**
the Fourier matrix `qftMatrix 2ⁿ`. It closes the arc begun in `AxQM/Concrete/QftGateCircuit.lean`
(the circuit as a matrix product), `AxQM/Concrete/QftGateCircuitCorrectness.lean` (each
controlled-`Rₖ` cascade is diagonal; the `n = 2` certificate), and
`AxQM/Concrete/QftGateCircuitState.lean` (the block sequence maps a basis input to the product state
`qftPartialState`).

## The remaining step

`AxQM/Concrete/QftGateCircuitState.lean` proved `qftBlocksProd_mulVec_basis`: the block sequence
(Hadamards + controlled-`Rₖ` cascades, **without** the swap layer) sends `|enc a⟩` to the explicit
product state `qftPartialState n a n = (1/√2ⁿ) ∏ₜ (qftBlockPhase n a t)^{kₜ}`. Two things remain to
match this to `qftMatrix`:

* **The bit-reversal.** `qftGateSequence` applies the wire-reversal permutation **first**
  (`qftGateCircuit = (blocks).reverse.prod · P`, the swap-first convention fixed by the `n = 2`
  certificate), so on `|enc jbits⟩` the blocks act on `a = qftBitReversal n jbits` (bits read in
  reverse, `a s = jbits (Fin.rev s)`). `permGate_mulVec_single` turns the swap into that reindex.
* **The reversal identity** `qftBlockPhase_qftBitReversal`: the circuit's block phase on the
  reversed input equals the matrix's wire phase, `qftBlockPhase n (qftBitReversal n jbits) t =
  qftWirePhase n (finFunctionFinEquiv jbits) t`. Its two-line heart is that the block phase
  accumulates the binary fraction `0.jₜ₋₁…j₀` on wire `t` from the *low* input bits, while the
  matrix's wire phase `e^{2πi j 2ᵗ/2ⁿ}` is `2πi`-periodic in the *high* bits — so, factor by factor
  under the `Fin.rev` reindex, the two agree (the discarded high-bit factors are `e^{2πi·ℤ} = 1`).

`qftBlockPhase_eq_prod` and `qftWirePhase_eq_prod` rewrite each phase as a single `Finset.univ`
product of unit-modulus exponentials, and the identity is then a per-factor `Fin.rev` matching.
Feeding these into `qftBlocksProd_mulVec_basis` and matching the normalisation
(`(1/√2)ⁿ = 1/√2ⁿ`, `sqrt_two_pow_inv`) gives, column by column,
`qftGateCircuit n *ᵥ |j⟩ = qftMatrix 2ⁿ *ᵥ |j⟩` (`qftGateCircuit_mulVec_basis`), hence the matrix
equality `qftGateCircuit_eq_qftMatrix`.

## Why this file exists (Exercise 5.6)

The faithful `Ω(n²/p(n))` lower bound of Exercise 5.6 perturbs the circuit's controlled-`Rₖ` gates,
and needs the identification of the gate product with the transform to compare the perturbed circuit
against the ideal `qftEvolution`. This file supplies exactly that identification; the reversal
identity and the `blocks · swap` decomposition (`qftGateCircuit_eq_blocks_mul_perm`) are the
reusable hooks the perturbation argument builds on.

## Setting

Every statement is about complex matrices/vectors (`Matrix`, `Matrix.mulVec`, `Pi.single`,
`qftMatrix`, `qftGateCircuit`), the encoding equivalence `finFunctionFinEquiv`, permutations, and
the phase scalars of the circuit.
-/

open scoped Matrix

namespace AxQM.Concrete

open Matrix Finset

/-- Both values of `Fin 2` are `0` or `1` — the case split used in the phase algebra below. -/
private theorem fin_two_eq_zero_or_one' (x : Fin 2) : x = 0 ∨ x = 1 := by decide +revert

/-- **The Hadamard sign as a phase** (Nielsen & Chuang eq. 5.6, wire `t`'s own contribution):
`(-1)^{v} = e^{2πi·v/2}` for a bit `v : Fin 2`. The `s = t` factor of the block phase, matching the
distance-`0` control convention `2^{(t-t)+1} = 2`. -/
theorem neg_one_pow_eq_exp (v : Fin 2) :
    (-1 : ℂ) ^ (v : ℕ)
      = Complex.exp (2 * Real.pi * Complex.I * (v : ℕ) / 2 ^ (1 : ℕ)) := by
  have hv : (v : ℕ) = 0 ∨ (v : ℕ) = 1 := by have := v.isLt; omega
  rcases hv with h | h <;> rw [h]
  · simp
  · rw [pow_one, show (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) / 2 ^ (1 : ℕ))
        = Real.pi * Complex.I from by push_cast; ring, Complex.exp_pi_mul_I]

/-- Target `t`'s control wires form a duplicate-free list (a sublist of `List.finRange n`). -/
theorem qftTargetControls_nodup (n : ℕ) (t : Fin n) : (qftTargetControls n t).Nodup := by
  rw [qftTargetControls]; exact (List.nodup_finRange n).drop

/-- **Target `t`'s control wires, as a `Finset`, are the wires strictly above `t`:**
`(qftTargetControls n t).toFinset = {c | t < c}`. Used to turn the block's controlled-`Rₖ` cascade
(a list product) into a `Finset` product for the reversal identity. -/
theorem qftTargetControls_toFinset (n : ℕ) (t : Fin n) :
    (qftTargetControls n t).toFinset
      = Finset.univ.filter (fun c : Fin n => (t : ℕ) < (c : ℕ)) := by
  ext c
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [qftTargetControls, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.getElem_drop, List.getElem_finRange]; simp only [Fin.val_cast]; omega
  · intro h
    refine ⟨(c : ℕ) - (t + 1), ?_, ?_⟩
    · rw [List.length_drop, List.length_finRange]; omega
    · rw [List.getElem_drop, List.getElem_finRange]; apply Fin.ext
      simp only [Fin.val_cast]; omega

/-- **The block phase as a single `Finset.univ` product of unit-modulus phases** (Nielsen & Chuang
eqs. 5.5–5.6). Uniting the block-opening Hadamard (wire `t`, `s = t`) and the controlled-`Rₖ`
cascade (`s > t`), every wire `s ≥ t` contributes the factor `e^{2πi·aₛ/2^{s-t+1}}`, and the wires
`s < t` contribute `1`:
`qftBlockPhase n a t = ∏ₛ (if t ≤ s then e^{2πi·aₛ/2^{s-t+1}} else 1)`. -/
theorem qftBlockPhase_eq_prod (n : ℕ) (a : Fin n → Fin 2) (t : Fin n) :
    qftBlockPhase n a t
      = ∏ s : Fin n, (if (t : ℕ) ≤ (s : ℕ)
          then Complex.exp (2 * Real.pi * Complex.I * (a s : ℕ) / 2 ^ ((s : ℕ) - (t : ℕ) + 1))
          else 1) := by
  rw [← Finset.prod_filter]
  rw [show (Finset.univ.filter (fun s : Fin n => (t : ℕ) ≤ (s : ℕ)))
        = insert t (Finset.univ.filter (fun s : Fin n => (t : ℕ) < (s : ℕ))) from by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega]
  rw [Finset.prod_insert (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)]
  rw [qftBlockPhase]
  congr 1
  · rw [Nat.sub_self, zero_add]
    exact neg_one_pow_eq_exp (a t)
  · rw [← List.prod_toFinset _ (qftTargetControls_nodup n t), qftTargetControls_toFinset]
    apply Finset.prod_congr rfl
    intro c _
    rcases fin_two_eq_zero_or_one' (a c) with h | h <;> rw [h] <;> simp

/-- **The wire phase as a single `Finset.univ` product** over the input bits (Nielsen & Chuang eq.
5.4). Expanding `j = ∑ₛ jbitsₛ 2ˢ` in the output-phase exponent factorises `qftWirePhase` over the
input wires: `qftWirePhase n (finFunctionFinEquiv jbits) t = ∏ₛ e^{2πi·jbitsₛ·2^{s+t}/2ⁿ}`. -/
theorem qftWirePhase_eq_prod (n : ℕ) (jbits : Fin n → Fin 2) (t : Fin n) :
    qftWirePhase n (finFunctionFinEquiv jbits) t
      = ∏ s : Fin n, Complex.exp
          (2 * Real.pi * Complex.I * ((jbits s : ℕ) * 2 ^ ((s : ℕ) + (t : ℕ)))
            / (2 ^ n : ℕ)) := by
  rw [qftWirePhase, ← Complex.exp_sum]
  congr 1
  have hj : (((finFunctionFinEquiv jbits : Fin (2 ^ n)) : ℕ) : ℂ)
      = ∑ s, ((jbits s : ℕ) : ℂ) * 2 ^ (s : ℕ) := by
    rw [finFunctionFinEquiv_apply_val]; push_cast; ring
  rw [hj, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  rw [pow_add]
  push_cast
  ring

/-- **The wire-reversal permutation reverses the bit string:** `qftBitReversal n jbits s =
jbits (Fin.rev s)` — the swap layer sends wire `s` to wire `Fin.rev s = n-1-s`. -/
theorem qftBitReversal_apply (n : ℕ) (jbits : Fin n → Fin 2) (s : Fin n) :
    qftBitReversal n jbits s = jbits (Fin.rev s) := by
  simp only [qftBitReversal, Equiv.arrowCongr_apply, Function.comp_apply,
    Equiv.refl_apply, Fin.revPerm_symm, Fin.revPerm_apply]

/-- **The reversal identity** (Nielsen & Chuang eqs. 5.4–5.6, the heart of Figure 5.1's
correctness): the Figure 5.1 block phase acquired by wire `t` on the **reversed** input
`qftBitReversal n jbits`
equals the quantum-Fourier-transform matrix's single-qubit output phase on wire `t`,
`qftBlockPhase n (qftBitReversal n jbits) t = qftWirePhase n (finFunctionFinEquiv jbits) t`.

Both phases are products over the `n` wires of unit-modulus exponentials (`qftBlockPhase_eq_prod`,
`qftWirePhase_eq_prod`). Reindexing the block product by `Fin.rev`, the block's factor for wire
`Fin.rev s'` (present only when `t ≤ n-1-s'`, i.e. `s' + t < n`) is `e^{2πi·jbitsₛ'/2^{n-s'-t}}`,
which equals the wire's factor `e^{2πi·jbitsₛ'·2^{s'+t}/2ⁿ}` in that same range; and when
`s' + t ≥ n` the block factor is `1` while the wire factor is `e^{2πi·(integer)} = 1` by
`2πi`-periodicity (`Complex.exp_nat_mul_two_pi_mul_I`). So the two agree factor by factor. -/
theorem qftBlockPhase_qftBitReversal (n : ℕ) (jbits : Fin n → Fin 2) (t : Fin n) :
    qftBlockPhase n (qftBitReversal n jbits) t
      = qftWirePhase n (finFunctionFinEquiv jbits) t := by
  rw [qftBlockPhase_eq_prod, qftWirePhase_eq_prod, ← Equiv.prod_comp Fin.revPerm]
  apply Finset.prod_congr rfl
  intro s' _
  rw [Fin.revPerm_apply, qftBitReversal_apply, Fin.rev_rev, Fin.val_rev]
  by_cases h : (s' : ℕ) + (t : ℕ) < n
  · rw [ite_eq_left (by omega)]
    congr 1
    rw [show (n - ((s' : ℕ) + 1)) - (t : ℕ) + 1 = n - (s' : ℕ) - (t : ℕ) from by omega]
    have hpow : (((2 : ℕ) ^ n : ℕ) : ℂ)
        = 2 ^ ((s' : ℕ) + (t : ℕ)) * 2 ^ (n - (s' : ℕ) - (t : ℕ)) := by
      push_cast; rw [← pow_add]; congr 1; omega
    rw [hpow]
    field_simp
  · rw [ite_eq_right (by omega)]
    symm
    have h2 : ((2 : ℂ) ^ ((s' : ℕ) + (t : ℕ)))
        = 2 ^ n * 2 ^ ((s' : ℕ) + (t : ℕ) - n) := by
      rw [← pow_add]; congr 1; omega
    rw [show (2 * Real.pi * Complex.I * ((jbits s' : ℕ) * 2 ^ ((s' : ℕ) + (t : ℕ)))
            / (((2 : ℕ) ^ n : ℕ) : ℂ))
          = (((jbits s' : ℕ) * 2 ^ ((s' : ℕ) + (t : ℕ) - n) : ℕ) : ℂ)
            * (2 * Real.pi * Complex.I) from by
        push_cast
        rw [h2]
        field_simp]
    exact Complex.exp_nat_mul_two_pi_mul_I _

/-- **The full product state at `m = n`** — the amplitude of `qftPartialState n a n`. Once every
block has acted, the pinned condition is vacuous and the phase product runs over all wires:
`qftPartialState n a n i = (1/√2)ⁿ · ∏ₛ (qftBlockPhase n a s)^{kₛ}` with `k = enc.symm i`. -/
theorem qftPartialState_full (n : ℕ) (a : Fin n → Fin 2) (i : Fin (2 ^ n)) :
    qftPartialState n a n i
      = (Real.sqrt 2 : ℂ)⁻¹ ^ n
        * ∏ s : Fin n, qftBlockPhase n a s ^ (finFunctionFinEquiv.symm i s : ℕ) := by
  rw [qftPartialState, ite_eq_left (fun s hs => absurd hs (Nat.not_le.mpr s.isLt)),
    Finset.filter_true_of_mem (fun s _ => s.isLt)]

/-- The `n`-fold Hadamard normalisation equals the transform's `1/√2ⁿ`:
`(1/√2)ⁿ = 1/√(2ⁿ)`. -/
theorem sqrt_two_pow_inv (n : ℕ) :
    (Real.sqrt 2 : ℂ)⁻¹ ^ n = (Real.sqrt ((2 : ℕ) ^ n) : ℂ)⁻¹ := by
  rw [inv_pow, ← Complex.ofReal_pow]
  congr 2
  have hsq : ((Real.sqrt 2) ^ n) ^ 2 = ((2 : ℕ) ^ n : ℝ) := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]; push_cast; ring
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-- **The Figure 5.1 gate list factors as blocks-then-swap** (the swap-first convention):
`qftGateCircuit n = (∏ blocks) · P`, where `P = permGate finFunctionFinEquiv (qftBitReversal n)` is
the wire-reversal and `∏ blocks = ((List.finRange n).flatMap (qftBlock n)).reverse.prod`. The
operator reads with the swap acting first (rightmost). Reusable for the perturbed (`Ω`) circuit,
whose blocks alone carry the perturbed `Rₖ` gates. -/
theorem qftGateCircuit_eq_blocks_mul_perm (n : ℕ) :
    qftGateCircuit n
      = ((List.finRange n).flatMap (qftBlock n)).reverse.prod
        * permGate finFunctionFinEquiv (qftBitReversal n) := by
  rw [qftGateCircuit, qftGateSequence, List.reverse_cons, List.prod_append, List.prod_singleton]

/-- **The circuit and the matrix agree on every basis column** (Nielsen & Chuang eqs. 5.12–5.18):
`qftGateCircuit n *ᵥ |enc jbits⟩ = qftMatrix 2ⁿ *ᵥ |enc jbits⟩`. The swap sends `|enc jbits⟩` to the
reversed input (`permGate_mulVec_single`); the block sequence maps it to the product state
`qftPartialState` (`qftBlocksProd_mulVec_basis`); and, entry by entry, that product state matches
column `enc jbits` of `qftMatrix` via the reversal identity `qftBlockPhase_qftBitReversal` (the
phases) and `sqrt_two_pow_inv` (the normalisation). -/
theorem qftGateCircuit_mulVec_basis (n : ℕ) (jbits : Fin n → Fin 2) :
    qftGateCircuit n *ᵥ Pi.single (finFunctionFinEquiv jbits) 1
      = qftMatrix (2 ^ n) *ᵥ Pi.single (finFunctionFinEquiv jbits) 1 := by
  rw [qftGateCircuit_eq_blocks_mul_perm, ← Matrix.mulVec_mulVec, permGate_mulVec_single,
    qftBlocksProd_mulVec_basis]
  funext i
  rw [qftPartialState_full, Matrix.mulVec_single_one, Matrix.col_apply]
  conv_rhs => rw [show i = finFunctionFinEquiv (finFunctionFinEquiv.symm i) from
    (Equiv.apply_symm_apply _ _).symm, qftMatrix_apply_eq_prod_wirePhase]
  rw [sqrt_two_pow_inv]
  congr 1
  · norm_cast
  · exact Finset.prod_congr rfl fun s _ => by rw [qftBlockPhase_qftBitReversal]

/-- **The gate-level Figure 5.1 circuit computes the quantum Fourier transform:**
`qftGateCircuit n = qftMatrix 2ⁿ` (Nielsen & Chuang §5.1, eqs. 5.12–5.18). Two matrices agreeing on
every standard-basis column are equal, and `qftGateCircuit_mulVec_basis` supplies exactly that
column-by-column agreement. This is the general-`n` correctness of the circuit, of which
`qftGateCircuit_two_eq_qftMatrix` was the `n = 2` certificate; it is the object the faithful
`Ω(n²/p(n))` half of Exercise 5.6 perturbs. -/
theorem qftGateCircuit_eq_qftMatrix (n : ℕ) : qftGateCircuit n = qftMatrix (2 ^ n) := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [show j = finFunctionFinEquiv (finFunctionFinEquiv.symm j) from
    (Equiv.apply_symm_apply _ _).symm]
  exact qftGateCircuit_mulVec_basis n _

end AxQM.Concrete
