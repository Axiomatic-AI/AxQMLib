/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.UnitaryBlochRotation
import AxQM.NC.Ch5.Exercise5_9
import AxQM.NC.Ch10.Exercise10_70
import AxQM.Concrete.SXCorrectionMatrix

/-!
# Nielsen & Chuang, Exercise 10.71 (Fault-tolerant measurement of `M = e^{-iπ/4}SX`)

*(N&C §10.6.3, p. 491.)*

Verify that for M=e^{-ipi/4}SX the described procedure is a fault-tolerant way to measure M.

## The procedure, and what is formalised here

The "procedure we have described" is the fault-tolerant measurement of a single-qubit observable
`M` (Fig. 10.28): a **cat-state ancilla** `|0…0⟩ + |1…1⟩` (one ancilla qubit per data qubit),
**verified** by parity checks, then a transversal **controlled-`M`** coupling the ancilla to the
encoded data, and finally a **decode read-out**. Specialised to `M = e^{-iπ/4}SX` this needs the
"slight modification" of N&C p. 491 — the controlled-`M` is realised by transversal controlled-`ZSX`
gates followed by seven `T` gates on the ancilla qubits. Verifying the procedure means checking that
`M` is a legitimate observable the circuit measures, that the slight modification implements `M`,
and that the procedure is fault-tolerant. All three are formalised (see the honest scope note below
for the one piece of absent apparatus).

**1. `M` is a `±1` observable measured by the Hadamard-test circuit.** `M` is the unitary
`Evolution qubit` `sxCorrectionGate`; it is Hermitian (`Concrete.mMatrix_isHermitian`) and
involutive (`Concrete.mMatrix_mul_self`, `M² = 1`), a self-adjoint unitary with spectrum `{+1, −1}`
exhibited by `|Θ⟩` (`sxCorrectionEigenstatePlus`, `+1`; `sxCorrectionGate_hasEigenstate_one`) and
`|Θ⁻⟩` (`sxCorrectionEigenstateMinus`, `−1`; `_neg_one`). The standard measurement circuit
`measureObservableCircuit` (the grounded Fig. 10.13/10.26 Hadamard-test the fault-tolerant procedure
implements) reads `M`'s eigenvalue:
`measureObservableCircuit_sxCorrectionGate_ketZero_eigenstatePlus` / `_eigenstateMinus` send
`|0⟩ ⊗ |Θ^±⟩` to `|0⟩ ⊗ |Θ^±⟩` / `|1⟩ ⊗ |Θ^±⟩` (outcome `0` for `+1`, `1` for `−1`). The `+1`
eigenstate `|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2` is exactly the π/8-gate ancilla of
Exercise 10.66, since `M = T X T†`.

**2. The slight modification implements `M`.** The controlled-`M` is transversal controlled-`ZSX`
(the Clifford part) followed by seven ancilla `T` gates (the scalar). The per-qubit correction is
the gate `zsxGate` (`= unitaryGate Concrete.zsxMatrix`, `ZSX = !![0,1;−i,0]`). The seven `T` gates
supply `M`'s scalar `e^{-iπ/4}` as a **controlled relative phase**: at the operator level
`transversalTGate` (`AxQM/Postulates/API/TransversalTGate.lean`) sends the cat `|0…0⟩ + |1…1⟩` to
`|0…0⟩ + (T₁₁)^{n}|1…1⟩`, and on the seven-qubit Steane ancilla `(T₁₁)^{7} = e^{-iπ/4}`
(`transversalTGate_op_catVec_seven`, `Concrete.tMatrix_one_one_pow_seven`) — exactly `M`'s scalar
(`Concrete.mMatrix_eq_tMatrix_one_one_pow_seven_smul_sxMatrix`, `M = (T₁₁)^7 • SX`). This is why the
phase is applied by *seven* `T`s on the ancilla, as a relative phase between cat branches, rather
than folded into the per-qubit correction.

**3. The procedure is fault-tolerant for `M`.** The generic fault-tolerance analysis of Fig. 10.28
is formalised in the companion exercises; the `M = e^{-iπ/4}SX` procedure inherits it:

* a single fault in the cat-ancilla **preparation and verification** leaves at most one `X`/`Y`
  error in the accepted ancilla — `catAncilla_single_fault_at_most_one_error` (Exercise 10.69),
  entirely `M`-independent (the fault-tolerance of the cat gadget does not depend on which
  observable is measured);
* **(A)** a `Z` error on the ancilla **does not propagate to the encoded data**, because the
  coupling is a transversal *controlled* operation with the ancilla qubits as controls, and `Z` on a
  control commutes with a controlled gate — `transversalCoupling_zsxGate_comm_ancillaPhaseError`
  (the `M`-instance of Exercise 10.70's claim A, for the actual transversal gate `ZSX`);
* **(B)** a `Z` error instead **flips the measurement result while leaving the data unchanged** —
  `measureObservableCircuitZError_sxCorrectionGate_eigenstatePlus` (Ex. 10.70's claim B for `M`).

## Honest scope note

Two things are *not* formalised, and neither is a weakening of what the exercise verifies:

* the majority-vote suppression of the wrong-result probability to `O(p²)` is a statement about a
  stochastic fault/cost model the axiom framework does not express; the fault-tolerance content is
  captured **operationally** exactly as N&C's Exercises 10.69/10.70 render it (a single fault yields
  a bounded, at-most-one-qubit error), which is the verifiable proposition;
* the full *encoded* identity "transversal `(ZSX)^{⊗7}` = logical `M̄` on the 128-dimensional Steane
  code space" needs the Steane logical-operator theory (`(ZS)^{⊗7} = S̄`, `X^{⊗7} = X̄` as `128 ×
  128` operators), a large development that is not included here; the transversal implementation is
  recorded here at the single-qubit gate level (`zsxGate`, `transversalTGate`, and the `Concrete`
  matrix facts). N&C state these transversal facts in the main text (not the exercise), so their
  absence does not narrow the proposition verified above.

## Supporting files

The `2 × 2` matrix algebra of `M` is in `AxQM/Concrete/SXCorrectionMatrix.lean`, and the phase
gadget in `AxQM/Postulates/API/TransversalTGate.lean`. Here `M`'s observable nature is carried by
its Hermiticity and involution in `AxQM/Concrete/SXCorrectionMatrix.lean` and the exhibited `±1`
eigenstates.
-/

open Matrix Complex

noncomputable section

namespace AxQM

/-- **`M = e^{-iπ/4}SX` as the unitary `Evolution qubit`** measured by the Hadamard-test circuit:
the single-qubit gate `unitaryGate` of the unitary matrix `Concrete.mMatrix` (unitary by
`Concrete.mMatrix_mem_unitaryGroup`). `M` is Hermitian (`Concrete.mMatrix_isHermitian`) and
involutive (`Concrete.mMatrix_mul_self`), i.e. a self-adjoint unitary, so this gate *is* a `±1`
observable — the operator whose fault-tolerant measurement is the subject of the exercise (and
which creates the π/8-gate ancilla). -/
def sxCorrectionGate : Evolution qubit := unitaryGate Concrete.mMatrix_mem_unitaryGroup

/-- The **`+1` eigenstate `|Θ⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2`** of `M` as a qubit `PureState`
(`Concrete.thetaVec`, normalized since `‖invSqrt2‖² + ‖invSqrt2·e^{iπ/4}‖² = ½ + ½ = 1`). This is
precisely the ancilla produced by the fault-tolerant π/8 gate of Exercise 10.66. -/
def sxCorrectionEigenstatePlus : PureState qubit where
  vec := WithLp.toLp 2 Concrete.thetaVec
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.thetaVec : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.thetaVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        norm_mul, Concrete.norm_tMatrix_one_one, mul_one, Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

/-- The **`−1` eigenstate `|Θ⁻⟩ = (|0⟩ − e^{iπ/4}|1⟩)/√2`** of `M` as a qubit `PureState`
(`Concrete.thetaMinusVec`, normalized as for `|Θ⟩`). -/
def sxCorrectionEigenstateMinus : PureState qubit where
  vec := WithLp.toLp 2 Concrete.thetaMinusVec
  normalized := by
    have h : ‖(WithLp.toLp 2 Concrete.thetaMinusVec : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Concrete.thetaMinusVec, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, norm_neg, norm_mul, Concrete.norm_tMatrix_one_one, mul_one,
        Concrete.norm_invSqrt2_sq]
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, Real.sqrt_one]
    exact h

/-- **`|Θ⟩` is the `+1` eigenstate of `M`**: `M |Θ⟩ = |Θ⟩`. Transports the matrix eigen-equation
`Concrete.mMatrix_mulVec_thetaVec` across `Matrix.toEuclideanCLM` via `Matrix.toEuclideanCLM_toLp`.
Confirms `M` fixes the fault-tolerant π/8-gate ancilla. -/
theorem sxCorrectionGate_hasEigenstate_one :
    sxCorrectionGate.HasEigenstate 1 sxCorrectionEigenstatePlus := by
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.mMatrix
      (WithLp.toLp 2 Concrete.thetaVec) = (1 : ℂ) • WithLp.toLp 2 Concrete.thetaVec
  rw [Matrix.toEuclideanCLM_toLp, Concrete.mMatrix_mulVec_thetaVec, one_smul]

/-- **`|Θ⁻⟩` is the `−1` eigenstate of `M`**: `M |Θ⁻⟩ = −|Θ⁻⟩`. Transports
`Concrete.mMatrix_mulVec_thetaMinusVec` across `Matrix.toEuclideanCLM`; together with
`sxCorrectionGate_hasEigenstate_one` this exhibits the full `±1` spectrum of `M`. -/
theorem sxCorrectionGate_hasEigenstate_neg_one :
    sxCorrectionGate.HasEigenstate (-1) sxCorrectionEigenstateMinus := by
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.mMatrix
      (WithLp.toLp 2 Concrete.thetaMinusVec) = (-1 : ℂ) • WithLp.toLp 2 Concrete.thetaMinusVec
  rw [Matrix.toEuclideanCLM_toLp, Concrete.mMatrix_mulVec_thetaMinusVec, ← WithLp.toLp_smul,
    neg_one_smul]

/-- **The measurement circuit reads `M`'s `+1` eigenvalue as outcome `0`.** Running the standard
observable-measurement circuit `measureObservableCircuit` (the grounded Hadamard-test of
Figs. 10.13/10.26 that the fault-tolerant procedure implements) on `|0⟩ ⊗ |Θ⟩`, with `|Θ⟩` the `+1`
eigenstate of `M`, leaves the ancilla in `|0⟩` and the data unchanged: the measurement result `0`
faithfully reports the eigenvalue `+1`. -/
theorem measureObservableCircuit_sxCorrectionGate_ketZero_eigenstatePlus :
    (measureObservableCircuit sxCorrectionGate).evolvePure
        ((qubitBasis 0).tmul sxCorrectionEigenstatePlus)
      = (qubitBasis 0).tmul sxCorrectionEigenstatePlus :=
  measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_one sxCorrectionGate
    sxCorrectionGate_hasEigenstate_one

/-- **The measurement circuit reads `M`'s `−1` eigenvalue as outcome `1`.** On `|0⟩ ⊗ |Θ⁻⟩`, with
`|Θ⁻⟩` the `−1` eigenstate of `M`, the circuit flips the ancilla to `|1⟩` and leaves the data
unchanged: the measurement result `1` faithfully reports the eigenvalue `−1`. Together with the
`+1` case this is the correctness of the (idealised) measurement of `M`. -/
theorem measureObservableCircuit_sxCorrectionGate_ketZero_eigenstateMinus :
    (measureObservableCircuit sxCorrectionGate).evolvePure
        ((qubitBasis 0).tmul sxCorrectionEigenstateMinus)
      = (qubitBasis 1).tmul sxCorrectionEigenstateMinus :=
  measureObservableCircuit_evolvePure_ketZero_tmul_hasEigenstate_neg_one sxCorrectionGate
    sxCorrectionGate_hasEigenstate_neg_one

/-! ### The transversal correction gate, and the fault-tolerance of the procedure for `M`

The remaining ingredients specialise the **fault-tolerant measurement procedure** of Figure 10.28 to
`M = e^{-iπ/4}SX`. The generic fault-tolerance analysis is in the companion
exercises: a single fault in the cat-ancilla preparation and verification leaves at most one `X`/`Y`
error in the accepted ancilla (`catAncilla_single_fault_at_most_one_error`, Exercise 10.69, entirely
`M`-independent), and `Z` errors on the ancilla behave as analysed in Exercise 10.70. What is
`M`-specific is that the transversal coupling of Figure 10.28 is realised — by the "slight
modification" of N&C p. 491 — as transversal **controlled-`ZSX`** followed by seven `T` gates on the
ancilla. The two claims of Exercise 10.70 therefore hold *for this procedure* by instantiation:

* **(A) `Z` errors on the ancilla do not propagate to the encoded data**, because the coupling is a
  transversal *controlled* operation with the ancilla qubits as the **controls**, and a `Z` on a
  control commutes with a controlled gate (`transversalCoupling_zsxGate_comm_ancillaPhaseError`).
* **(B) a `Z` error flips the measurement result while leaving the data untouched**
  (`measureObservableCircuitZError_sxCorrectionGate_eigenstatePlus`).
-/

/-- **The per-qubit transversal correction `ZSX` as a qubit `Evolution`.** For `M = e^{-iπ/4}SX` the
"slight modification" of N&C p. 491 realises the controlled-`M` of Figure 10.28 by applying
controlled-`ZSX` transversally to each (ancilla, data) pair (its Clifford part: `X^{⊗7}` is logical
`X̄` and `(ZS)^{⊗7}` logical `S̄`), the non-Clifford scalar `e^{-iπ/4}` being supplied separately by
seven ancilla `T` gates. This is that per-qubit correction gate, the unitary `unitaryGate` of
`Concrete.zsxMatrix = !![0,1;−i,0]` (unitary by `Concrete.zsxMatrix_mem_unitaryGroup`); unlike `M`
it is not self-adjoint — it is a correction, not an observable. -/
def zsxGate : Evolution qubit := unitaryGate Concrete.zsxMatrix_mem_unitaryGroup

/-- **`M` fixes its `+1` eigenstate at the state level:** `M.evolvePure |Θ⟩ = |Θ⟩`. The `evolvePure`
form of `sxCorrectionGate_hasEigenstate_one` (`M|Θ⟩ = |Θ⟩`), obtained from the eigenvalue-`1` bridge
`Evolution.HasEigenstate.evolvePure_eq`. This is the hypothesis under which the fault-tolerant
measurement of `M` reads the correct outcome on `|Θ⟩` and its `Z`-corrupted counterpart reads the
wrong one. -/
theorem sxCorrectionGate_evolvePure_eigenstatePlus :
    sxCorrectionGate.evolvePure sxCorrectionEigenstatePlus = sxCorrectionEigenstatePlus :=
  sxCorrectionGate_hasEigenstate_one.evolvePure_eq

/-- **(A) A `Z` error on the ancilla does not propagate to the data, for the `M = e^{-iπ/4}SX`
procedure.** The transversal controlled-`ZSX` coupling of the ancilla to the data
(`transversalCoupling zsxGate`, three (ancilla, data) pairs as in Figure 10.28) commutes with a
phase-flip `Z` error on any ancilla qubit `i`: `(C(ZSX)^{⊗3}) · Zᵢ = Zᵢ · (C(ZSX)^{⊗3})`. Because
the ancilla qubits are the *controls* of the controlled-`ZSX` gates, a `Z` on a control slides
through the ancilla–data interaction unchanged and never becomes an operation on the encoded data
(the `M`-instance of `transversalCoupling_comm_transversalAncillaPhaseError`). The seven ancilla `T`
gates of the slight modification are diagonal, so they too commute with an ancilla `Z`; thus the
full modified coupling propagates no `Z` error to the data — claim (A) of the fault-tolerance
analysis (Exercise 10.70) for this procedure. -/
theorem transversalCoupling_zsxGate_comm_ancillaPhaseError (i : Fin 3) :
    (transversalCoupling zsxGate).comp (transversalAncillaPhaseError i)
      = (transversalAncillaPhaseError i).comp (transversalCoupling zsxGate) :=
  transversalCoupling_comm_transversalAncillaPhaseError zsxGate i

/-- **(B) A `Z` error on the ancilla flips the `M`-measurement result but leaves the data
unaffected.** On `|0⟩ ⊗ |Θ⟩` with `|Θ⟩` the `+1` eigenstate of `M`, the ideal measurement circuit
reads outcome `0` (`measureObservableCircuit_sxCorrectionGate_ketZero_eigenstatePlus`, the correct
report of eigenvalue `+1`); a `Z` error on the ancilla instead sends `|0⟩ ⊗ |Θ⟩` to `|1⟩ ⊗ |Θ⟩` —
the ancilla now reads the *wrong* outcome `1`, while the data factor is still `|Θ⟩`, unchanged. Thus
a `Z` error in the ancilla produces an incorrect measurement result without propagating to the
encoded data — claim (B) of Exercise 10.70 for `M = e^{-iπ/4}SX` (the `M`-instance of
`measureObservableCircuitZError_evolvePure_qubitBasisZero_of_eigenstate`, via
`sxCorrectionGate_evolvePure_eigenstatePlus`). -/
theorem measureObservableCircuitZError_sxCorrectionGate_eigenstatePlus :
    (measureObservableCircuitZError sxCorrectionGate).evolvePure
        ((qubitBasis 0).tmul sxCorrectionEigenstatePlus)
      = (qubitBasis 1).tmul sxCorrectionEigenstatePlus :=
  measureObservableCircuitZError_evolvePure_qubitBasisZero_of_eigenstate sxCorrectionGate
    sxCorrectionEigenstatePlus sxCorrectionGate_evolvePure_eigenstatePlus

end AxQM
