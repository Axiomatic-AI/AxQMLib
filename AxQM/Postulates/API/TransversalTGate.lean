/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CatVerification
import AxQM.Concrete.SXCorrectionMatrix

/-!
# AxQM.Postulates.API — the transversal `T` gate on the cat ancilla

This file concerns the **"slight modification"** of the fault-tolerant measurement procedure that
Nielsen & Chuang use for the observable `M = e^{-iπ/4}SX` (§10.6.3, p. 491, Exercise 10.71). To
perform the controlled-`M` of Figure 10.28 for this `M`, N&C apply transversal controlled-`ZSX`
(the Clifford part) *followed by seven `T` gates applied transversally to the ancilla qubits* —
supplying the non-Clifford scalar `e^{-iπ/4}` as a **controlled relative phase** between the two
branches of the cat ancilla.

This file formalises that phase gadget at general qubit count on the register `bitReg ι` of
`Postulates/API/CSSCode.lean` (its computational basis `regBasis`, the cat ancilla `catVec ι`):

* `transversalTGate ι` — the **transversal `T` gate** `T^{⊗n}`, the diagonal operator on `regBasis`
  with entry `(T₁₁)^{|w|}` (Hamming weight `|w| = ∑ᵢ wᵢ`) on `|w⟩`. It is `T` applied to every qubit
  (each `T = diag(1, T₁₁)` contributes `T₁₁` per set bit), defined via the same
  `OrthonormalBasis.diagonalOperator` construction as the Pauli phase string `Z^u`. Unitary because
  every entry has unit modulus (`‖T₁₁‖ = 1`, `Concrete.norm_tMatrix_one_one`).
* `transversalTGate_op_catVec` — the **phase-gadget action on the cat**: `T^{⊗n}|cat⟩ = |0…0⟩ +
  (T₁₁)^{n} |1…1⟩`. The all-zeros branch is untouched (weight `0`); the all-ones branch acquires the
  relative phase `(T₁₁)^{n}`. This *is* the controlled relative phase of the slight modification.
* `transversalTGate_op_catVec_seven` — its Steane-code instance (`ι = Fin 7`): `T^{⊗7}|cat⟩ = |0…0⟩
  + e^{-iπ/4}|1…1⟩`, since `(T₁₁)^{7} = e^{-iπ/4}` (`Concrete.tMatrix_one_one_pow_seven`) — **the
  seven ancilla `T` gates supply exactly `M`'s scalar** `e^{-iπ/4}` as the relative phase on the
  active (`|1…1⟩`) cat branch. This is why the modification uses *seven* `T`s (one per Steane qubit)
  and why the phase cannot be folded into the per-qubit correction: it is a relative phase between
  cat branches, not a per-qubit factor.

The cat-verification framework is in `AxQM/Postulates/API/CatVerification.lean`. The `Fin 7`
consequence is cited in `AxQM/NC/Ch10/Exercise10_71.lean` as the operator-level realisation of the
seven-`T`-gate phase gadget.
-/

open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- **The transversal `T` gate `T^{⊗n}`** on the register `bitReg ι`: the diagonal operator on the
computational basis `regBasis` with entry `(T₁₁)^{|w|}` on `|w⟩`, where `|w| = ∑ᵢ (wᵢ)` is the
Hamming weight and `T₁₁ = e^{iπ/4}` is the nontrivial diagonal entry of the π/8 gate
(`Concrete.tMatrix`). This is the π/8 gate applied bitwise to every qubit — each `T = diag(1, T₁₁)`
contributes a factor `T₁₁` for each set bit — the seven-`T` phase gadget of Exercise 10.71's slight
modification, at general qubit count. Unitary because each entry has unit modulus
(`Concrete.norm_tMatrix_one_one`). -/
def transversalTGate : Evolution (bitReg ι) where
  op := (regBasis ι).diagonalOperator fun w => (Concrete.tMatrix 1 1) ^ (∑ i, (w i).val)
  unitary := (regBasis ι).diagonalOperator_mem_unitary _ fun w => by
    rw [norm_pow, Concrete.norm_tMatrix_one_one, one_pow]

/-- **Action of the transversal `T` gate on a computational-basis ket:** `T^{⊗n}|w⟩ = (T₁₁)^{|w|}
|w⟩`, the diagonal phase `(T₁₁)^{|w|}` with `|w| = ∑ᵢ (wᵢ)` the Hamming weight. The
`diagonalOperator_apply_self` computation behind the phase gadget's action on the cat ancilla. -/
theorem transversalTGate_op_regBasis (w : ι → ZMod 2) :
    (transversalTGate ι).op (regBasis ι w)
      = (Concrete.tMatrix 1 1) ^ (∑ i, (w i).val) • regBasis ι w :=
  (regBasis ι).diagonalOperator_apply_self _ w

/-- **The transversal `T` gate applies a controlled relative phase to the cat ancilla:**
`T^{⊗n}|cat⟩ = |0…0⟩ + (T₁₁)^{n}|1…1⟩`. The all-zeros branch `|0…0⟩` (weight `0`) is left unchanged,
while the all-ones branch `|1…1⟩` (weight `n = #ι`) acquires the phase `(T₁₁)^{n}`: transversal `T`
turns the `+`-cat into a cat with **relative phase** `(T₁₁)^{n}` between its two branches. This is
the controlled relative phase of the fault-tolerant measurement's slight modification (N&C p. 491).
Both corners follow from `transversalTGate_op_regBasis`, with weights `∑ᵢ (0ᵢ) = 0` and
`∑ᵢ (1ᵢ) = #ι`. -/
theorem transversalTGate_op_catVec [Nonempty ι] :
    (transversalTGate ι).op (catVec ι)
      = regBasis ι 0 + (Concrete.tMatrix 1 1) ^ (Fintype.card ι) • regBasis ι 1 := by
  have h0 : (∑ i : ι, ((0 : ι → ZMod 2) i).val) = 0 := by simp
  have h1 : (∑ i : ι, ((1 : ι → ZMod 2) i).val) = Fintype.card ι := by
    have hv : ((1 : ZMod 2)).val = 1 := by decide
    simp only [Pi.one_apply, hv, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [catVec, map_add, transversalTGate_op_regBasis, transversalTGate_op_regBasis, h0, h1,
    pow_zero, one_smul]

/-- **The seven ancilla `T` gates supply `M`'s scalar `e^{-iπ/4}`** (the Steane-code instance,
`ι = Fin 7`): `T^{⊗7}|cat⟩ = |0…0⟩ + e^{-iπ/4}|1…1⟩`. On the seven-qubit Steane cat ancilla the
transversal `T` gadget applies the relative phase `(T₁₁)^{7} = e^{-iπ/4}`
(`Concrete.tMatrix_one_one_pow_seven`) — **exactly the scalar of `M = e^{-iπ/4}SX`** — on the active
`|1…1⟩` branch and nothing on the `|0…0⟩` branch. This is the operator-level content of Exercise
10.71's slight modification: the non-Clifford phase of `M` is applied to the *ancilla* as a
controlled relative phase between the cat branches, not folded into the per-qubit transversal
correction. Immediate from `transversalTGate_op_catVec` with `#(Fin 7) = 7`. -/
theorem transversalTGate_op_catVec_seven :
    (transversalTGate (Fin 7)).op (catVec (Fin 7))
      = regBasis (Fin 7) 0
        + Complex.exp (-(Real.pi / 4 : ℝ) * Complex.I) • regBasis (Fin 7) 1 := by
  rw [transversalTGate_op_catVec, Fintype.card_fin, Concrete.tMatrix_one_one_pow_seven]

end AxQM
