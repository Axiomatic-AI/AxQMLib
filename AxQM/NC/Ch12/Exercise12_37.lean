/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EPRLocalMeasurement
import AxQM.NC.Ch4.Exercise4_1

/-!
# Nielsen & Chuang, Exercise 12.37 — measuring one EPR qubit collapses the other

*(N&C p. 598.)*

Show measuring one EPR qubit in X (resp Z) collapses other into X (Z) eigenstate.

## The formalisation

The EPR pair is the maximally entangled Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` (`bellPhiPlus`), a pure
state of `qubit ⊗ qubit`. "Measure the first qubit in the `X` (resp. `Z`) basis" is the projective
(sign) measurement of the observable `X ⊗ I` (resp. `Z ⊗ I`), packaged as the named measurements
`eprMeasureFirstX` / `eprMeasureFirstZ` (`AxQM/Postulates/API/EPRLocalMeasurement.lean`): its `±1`
eigenprojectors are `|+⟩⟨+| ⊗ I`, `|-⟩⟨-| ⊗ I` (resp. `|0⟩⟨0| ⊗ I`, `|1⟩⟨1| ⊗ I`) — exactly a
first-qubit basis measurement.

Each statement below is stated with `Measurement.postMeasurement` (Postulate 4, collapse) and
`Measurement.bornProb` (Postulate 3, the Born rule), the measured observable being built into the
two named measurements. The two claims of the exercise are:

* **Collapse.** When the outcome is possible, the joint post-measurement state is the *product*
  state whose second factor is the eigenstate labeled by the outcome:
  - `X` basis: outcome `+1` → `|+⟩ ⊗ |+⟩`, outcome `−1` → `|-⟩ ⊗ |-⟩`
    (`eprMeasureFirstX_postMeasurement_zero` / `_one`);
  - `Z` basis: outcome `+1` → `|0⟩ ⊗ |0⟩`, outcome `−1` → `|1⟩ ⊗ |1⟩`
    (`eprMeasureFirstZ_postMeasurement_zero` / `_one`).
  Since the joint state factorises as `ψ ⊗ ψ` with `ψ` a genuine `±1` eigenstate of the Pauli
  observable (`qubitPlus_hasEigenstate_pauliX`, …), the **second qubit is left in the corresponding
  `X` (resp. `Z`) eigenstate** — the content the exercise asks for.
* **Randomness.** Each outcome occurs with probability exactly `½`
  (`eprMeasureFirstX_bornProb` / `eprMeasureFirstZ_bornProb`): the collapsed eigenstate is uniformly
  random, matching N&C's "random qubits".

## Design decisions

* **Statement shape.** The collapse is a full equality of the post-measurement `State` with a
  product state `(ψ ⊗ ψ).toState`, not a weaker up-to-phase or reduced-state claim: because `|Φ⁺⟩`
  is maximally entangled, projecting the first qubit onto a definite `X`/`Z` eigenstate leaves the
  joint state a genuine product, so "the second qubit is in eigenstate `ψ`" is captured exactly by
  the factorisation. The `X` and `Z` cases are instances of one shared computation on `|Φ⁺⟩`
  (`postMeasPlus_tmul_id_bellPhiPlus` etc. in the API file), keyed only on the diagonalisation
  `bellVec = |ψp⟩⊗|ψp⟩ + |ψm⟩⊗|ψm⟩` — the basis-independence of the maximally entangled state (N&C
  Exercise 12.36), trivial for the computational basis and `bellVec_eq_plusMinus` for the `X` basis.
* **Possibility hypothesis.** Each collapse theorem takes `hp : bornProb ≠ 0` (the outcome is
  possible) — the hypothesis under which `Measurement.postMeasurement` is defined; it is discharged
  by the companion `bornProb = ½` theorems, which certify the statements are not vacuous.
* **Deliberately out of scope.** The concluding paragraph ("using the results of Section 10.5.8,
  conclude that Alice's measurements of `H₁`, `H₂⊥`, `Z̄` result in a random codeword …") is an
  informal application of this collapse fact to the CSS-code QKD reduction of §12.6.6; it introduces
  no new verifiable proposition beyond the collapse formalised here, so it is not separately
  formalised.

## Declaration map

The formalisation is the collection below (not one monolithic theorem): the exercise's two
claims — the `X`/`Z` collapse and the uniform randomness of the outcome — are each captured by named
`theorem`s, and the collapse computation is a family of `theorem`s/`def`s in
`AxQM/Postulates/API/`.

*Collapse computation — `AxQM/Postulates/API/EPRLocalMeasurement.lean`.* One
computation keyed on an arbitrary single-qubit `±1` observable `A` (`A² = I`) with eigenstates
`ψp`/`ψm` diagonalising the Bell vector (`hbell : bellVec = ψp⊗ψp + ψm⊗ψm` — the basis-independence
of the maximally entangled state, N&C Ex 12.36):
* `tmul_id_op_bellVec` — `(A⊗I)|β⟩ = ψp⊗ψp − ψm⊗ψm` (the eigenvalue action);
* `projPlus_tmul_id_bellPhiPlus`, `projMinus_tmul_id_bellPhiPlus` — `P±|Φ⁺⟩ = (√2)⁻¹·ψ±⊗ψ±`;
* `projPlus_tmul_id_bellPhiPlus_ne_zero`, `projMinus_tmul_id_bellPhiPlus_ne_zero` — the outcome is
  possible (these discharge the `hp : bornProb ≠ 0` hypotheses of the collapse headlines);
* `postMeasPlus_tmul_id_bellPhiPlus`, `postMeasMinus_tmul_id_bellPhiPlus` — the collapse is exactly
  the product eigenstate `ψ±⊗ψ±` (the normalisation scalar divides out, no residual phase);
* `bornProb_signMeasurement_plus_tmul_id_bellPhiPlus`,
  `bornProb_signMeasurement_minus_tmul_id_bellPhiPlus` — each outcome has probability
  `‖P±|Φ⁺⟩‖² = ½`;
* `bellVec_eq_plusMinus` — the `X`-basis instance of `hbell` (`bellVec = |+⟩⊗|+⟩ + |-⟩⊗|-⟩`);
* the two named measurements `eprMeasureFirstX`, `eprMeasureFirstZ : Measurement (Fin 2) (qubit ⊗
  qubit)` — the sign measurements of `X ⊗ I` / `Z ⊗ I`, i.e. "measure the first qubit in the `X`
  (resp. `Z`) basis";
* (private `module` helpers `two_inv_smul_add_diag`/`two_inv_smul_sub_diag` bridge the tensor-space
  `Module ℂ` instance diamond — see that file's design note).

*Reused single-qubit Pauli eigenstates — `NC/Ch4/Exercise4_1.lean` (imported).* The `hp`/`hm`
eigenstate witnesses fed to the engine: `qubitPlus_hasEigenstate_pauliX` /
`qubitMinus_hasEigenstate_pauliX` (the `X` basis `{|+⟩, |-⟩}`) and
`qubitBasis_zero_hasEigenstate_pauliZ` / `qubitBasis_one_hasEigenstate_pauliZ` (the `Z` basis
`{|0⟩, |1⟩}`).

*This file (`AxQM/NC/Ch12/Exercise12_37.lean`) — the statements of the exercise.*
* Collapse, `Z` basis: `eprMeasureFirstZ_postMeasurement_zero` (`+1 → |0⟩⊗|0⟩`),
  `eprMeasureFirstZ_postMeasurement_one` (`−1 → |1⟩⊗|1⟩`);
* Collapse, `X` basis: `eprMeasureFirstX_postMeasurement_zero` (`+1 → |+⟩⊗|+⟩`),
  `eprMeasureFirstX_postMeasurement_one` (`−1 → |-⟩⊗|-⟩`);
* Randomness: `eprMeasureFirstZ_bornProb`, `eprMeasureFirstX_bornProb` (every outcome `= ½`, so the
  collapsed eigenstate is uniformly random and the collapse headlines are non-vacuous).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-! ### `Z`-basis measurement of the first qubit -/

/-- **Nielsen & Chuang, Exercise 12.37 (`Z` basis, outcome `+1`).** Measuring the first qubit of the
EPR pair `|Φ⁺⟩` in the `Z` basis and obtaining `+1` (outcome `0`) collapses the joint state to the
product `|0⟩ ⊗ |0⟩`: the second qubit is left in the `Z` eigenstate `|0⟩`. -/
theorem eprMeasureFirstZ_postMeasurement_zero
    (hp : eprMeasureFirstZ.bornProb bellPhiPlus.toState 0 ≠ 0) :
    eprMeasureFirstZ.postMeasurement bellPhiPlus.toState 0 hp
      = (qubitBasis 0 ⊗ qubitBasis 0).toState := by
  unfold eprMeasureFirstZ
  have h1 := Observable.postMeasurement_signMeasurement_plus
    (pauliZObservable.tmul (Observable.id qubit))
    (Observable.tmul_op_mul_self pauliZObservable_op_mul_self (by simp [Observable.id_op]))
    bellPhiPlus
    (projPlus_tmul_id_bellPhiPlus_ne_zero qubitBasis_zero_hasEigenstate_pauliZ
      qubitBasis_one_hasEigenstate_pauliZ rfl) hp
  rw [h1, postMeasPlus_tmul_id_bellPhiPlus qubitBasis_zero_hasEigenstate_pauliZ
      qubitBasis_one_hasEigenstate_pauliZ rfl]

/-- **Nielsen & Chuang, Exercise 12.37 (`Z` basis, outcome `−1`).** Measuring the first qubit of
`|Φ⁺⟩` in the `Z` basis and obtaining `−1` (outcome `1`) collapses the joint state to `|1⟩ ⊗ |1⟩`:
the second qubit is left in the `Z` eigenstate `|1⟩`. -/
theorem eprMeasureFirstZ_postMeasurement_one
    (hp : eprMeasureFirstZ.bornProb bellPhiPlus.toState 1 ≠ 0) :
    eprMeasureFirstZ.postMeasurement bellPhiPlus.toState 1 hp
      = (qubitBasis 1 ⊗ qubitBasis 1).toState := by
  unfold eprMeasureFirstZ
  have h1 := Observable.postMeasurement_signMeasurement_minus
    (pauliZObservable.tmul (Observable.id qubit))
    (Observable.tmul_op_mul_self pauliZObservable_op_mul_self (by simp [Observable.id_op]))
    bellPhiPlus
    (projMinus_tmul_id_bellPhiPlus_ne_zero qubitBasis_zero_hasEigenstate_pauliZ
      qubitBasis_one_hasEigenstate_pauliZ rfl) hp
  rw [h1, postMeasMinus_tmul_id_bellPhiPlus qubitBasis_zero_hasEigenstate_pauliZ
      qubitBasis_one_hasEigenstate_pauliZ rfl]

/-- **Nielsen & Chuang, Exercise 12.37 (`Z`-basis outcomes are uniform).** Each outcome of the
first-qubit `Z` measurement on `|Φ⁺⟩` occurs with probability `½`: the collapse is into a *random*
`Z` eigenstate. This certifies both `Z`-collapse theorems are non-vacuous. -/
theorem eprMeasureFirstZ_bornProb (i : Fin 2) :
    eprMeasureFirstZ.bornProb bellPhiPlus.toState i = 1 / 2 := by
  fin_cases i
  · exact bornProb_signMeasurement_plus_tmul_id_bellPhiPlus pauliZObservable_op_mul_self
      qubitBasis_zero_hasEigenstate_pauliZ qubitBasis_one_hasEigenstate_pauliZ rfl
  · exact bornProb_signMeasurement_minus_tmul_id_bellPhiPlus pauliZObservable_op_mul_self
      qubitBasis_zero_hasEigenstate_pauliZ qubitBasis_one_hasEigenstate_pauliZ rfl

/-! ### `X`-basis measurement of the first qubit -/

/-- **Nielsen & Chuang, Exercise 12.37 (`X` basis, outcome `+1`).** Measuring the first qubit of the
EPR pair `|Φ⁺⟩` in the `X` basis and obtaining `+1` (outcome `0`) collapses the joint state to the
product `|+⟩ ⊗ |+⟩`: the second qubit is left in the `X` eigenstate `|+⟩`. -/
theorem eprMeasureFirstX_postMeasurement_zero
    (hp : eprMeasureFirstX.bornProb bellPhiPlus.toState 0 ≠ 0) :
    eprMeasureFirstX.postMeasurement bellPhiPlus.toState 0 hp
      = (qubitPlus ⊗ qubitPlus).toState := by
  unfold eprMeasureFirstX
  have h1 := Observable.postMeasurement_signMeasurement_plus
    (pauliXObservable.tmul (Observable.id qubit))
    (Observable.tmul_op_mul_self pauliXObservable_op_mul_self (by simp [Observable.id_op]))
    bellPhiPlus
    (projPlus_tmul_id_bellPhiPlus_ne_zero qubitPlus_hasEigenstate_pauliX
      qubitMinus_hasEigenstate_pauliX bellVec_eq_plusMinus) hp
  rw [h1, postMeasPlus_tmul_id_bellPhiPlus qubitPlus_hasEigenstate_pauliX
      qubitMinus_hasEigenstate_pauliX bellVec_eq_plusMinus]

/-- **Nielsen & Chuang, Exercise 12.37 (`X` basis, outcome `−1`).** Measuring the first qubit of
`|Φ⁺⟩` in the `X` basis and obtaining `−1` (outcome `1`) collapses the joint state to `|-⟩ ⊗ |-⟩`:
the second qubit is left in the `X` eigenstate `|-⟩`. -/
theorem eprMeasureFirstX_postMeasurement_one
    (hp : eprMeasureFirstX.bornProb bellPhiPlus.toState 1 ≠ 0) :
    eprMeasureFirstX.postMeasurement bellPhiPlus.toState 1 hp
      = (qubitMinus ⊗ qubitMinus).toState := by
  unfold eprMeasureFirstX
  have h1 := Observable.postMeasurement_signMeasurement_minus
    (pauliXObservable.tmul (Observable.id qubit))
    (Observable.tmul_op_mul_self pauliXObservable_op_mul_self (by simp [Observable.id_op]))
    bellPhiPlus
    (projMinus_tmul_id_bellPhiPlus_ne_zero qubitPlus_hasEigenstate_pauliX
      qubitMinus_hasEigenstate_pauliX bellVec_eq_plusMinus) hp
  rw [h1, postMeasMinus_tmul_id_bellPhiPlus qubitPlus_hasEigenstate_pauliX
      qubitMinus_hasEigenstate_pauliX bellVec_eq_plusMinus]

/-- **Nielsen & Chuang, Exercise 12.37 (`X`-basis outcomes are uniform).** Each outcome of the
first-qubit `X` measurement on `|Φ⁺⟩` occurs with probability `½`: the collapse is into a *random*
`X` eigenstate. This certifies both `X`-collapse theorems are non-vacuous. -/
theorem eprMeasureFirstX_bornProb (i : Fin 2) :
    eprMeasureFirstX.bornProb bellPhiPlus.toState i = 1 / 2 := by
  fin_cases i
  · exact bornProb_signMeasurement_plus_tmul_id_bellPhiPlus pauliXObservable_op_mul_self
      qubitPlus_hasEigenstate_pauliX qubitMinus_hasEigenstate_pauliX bellVec_eq_plusMinus
  · exact bornProb_signMeasurement_minus_tmul_id_bellPhiPlus pauliXObservable_op_mul_self
      qubitPlus_hasEigenstate_pauliX qubitMinus_hasEigenstate_pauliX bellVec_eq_plusMinus

end AxQM
