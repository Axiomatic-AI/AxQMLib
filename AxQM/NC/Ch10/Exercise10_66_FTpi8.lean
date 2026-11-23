/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PiEighthGateCircuit

/-!
# Nielsen & Chuang, Exercise 10.66 (Fault-tolerant π/8 gate construction)

*(N&C §10.6.3, p. 487.)*

Using TX=exp(-ipi/4)SX and TU=UT, derive the pi/8 gate circuit of Fig 10.25.

## What the exercise asks, and how it is formalised

The exercise is a **circuit derivation**: push the final `T` of the "swap-then-`T`" circuit leftward
through the swap gadget of Exercise 10.65 using the two named commutation relations, until it lands
on the ancilla preparation and turns `H|0⟩` into the Fig. 10.25 ancilla
`|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2`. The verifiable content is the two relations, the ancilla identity
they produce, and the correctness of the resulting circuit — all equalities of concrete `2 × 2` /
`4 × 4` complex matrices and `Fin n → ℂ` column vectors.

**Read critically (N&C erratum).** The relation printed in the exercise, `TX = exp(−iπ/4) SX`, is
*false* as a bare matrix product (the top-right entries `1` and `exp(−iπ/4) = (1−i)/√2` differ). The
relation the derivation actually needs — and the one the main text states correctly on p. 486,
`THZHT† = TXT† = e^{−iπ/4}SX` — is the **conjugation** `T X T† = exp(−iπ/4) SX`. The formalisation
proves the correct conjugation form *and* records the disproof of the printed product form.

## The formalisation

All declarations live in `AxQM/Concrete/PiEighthGateCircuit.lean`
(`AxQM.Concrete` namespace), built on the π/8 gate `tMatrix`, its conjugation lemma
`tMatrix_conj_pauliX`, the phase gate `sMatrix`, Hadamard `hadamardC`, CNOT `cnotMatrix`, the kets
`ket`, and the `1/√2` bridges `invSqrt2` / `exp_(neg_)pi_div_four_mul_I`.

**The correction gate.**
* `sxMatrix` / `sxMatrix_eq` — `SX = S·X = !![0, 1; i, 0]` (eq. 10.120), the classically-controlled
  correction of Fig. 10.25.

**The two commutation relations (the engine of the derivation).**
* `tMatrix_conj_pauliX_eq_expNeg_smul_sxMatrix` — **relation 1, correct form**:
  `T X T† = exp(−iπ/4) • SX`.
* `tMatrix_mul_pauliX_eq_expNeg_smul_sxMatrix_mul` — its **leftward-move** form
  `T X = exp(−iπ/4) • (SX · T)`, the rule that pushes `T` left of the classically-controlled `X`.
* `tMatrix_mul_pauliX_ne_expNeg_smul_sxMatrix` — **the printed relation is false**:
  `T X ≠ exp(−iπ/4) • SX` as a bare product (the erratum above).
* `tCtrl` / `tCtrl_mul_cnotMatrix_comm` — **relation 2** `TU = UT`: `T ⊗ I` (T on the control qubit)
  commutes with the CNOT, `tCtrl · CNOT = CNOT · tCtrl`.

**The ancilla and the derived circuit's correctness.**
* `tMatrix_apply_one_one_mul_self` — `T₁₁ · T₁₁ = i` (`T₁₁ = e^{iπ/4}`), the fact behind the `SX`
  correction.
* `thetaVec` / `tMatrix_mulVec_hadamardC_mulVec_ket_zero` — the Fig. 10.25 ancilla
  `|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2` (eq. 10.118), reconstructed by the moved-left `T`, as
  `T (H|0⟩) = |Θ⟩`.
* `kron2` / `piEighthCircuitOut` — the two-qubit state `CNOT (|Θ⟩ ⊗ |ψ⟩)` after the Fig. 10.25 CNOT
  (eq. 10.119), with `|Θ⟩` as control and `|ψ⟩ = a|0⟩ + b|1⟩` as target.
* `piEighthCircuitOut_measure_zero` / `piEighthCircuitOut_measure_one` — **the derived circuit
  implements the π/8 gate**: measuring the data qubit leaves the ancilla wire holding `T|ψ⟩` up to a
  nonzero scalar in either outcome — directly for `0`, and after the `SX` correction for `1`.
-/
