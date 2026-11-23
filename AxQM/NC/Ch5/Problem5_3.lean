/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.KitaevPhaseEstimation

/-!
# Nielsen & Chuang, Problem 5.3 (Kitaev's algorithm)

Kitaev's algorithm: top qubit measured 0 with prob cos^2(pi phi); iterate U^k to extract bits of
phi.

The circuit is the Hadamard-controlled-`U` circuit
`measureObservableCircuit U = (H ⊗ 1) · C(U) · (H ⊗ 1)` — Postulate 5, an `Evolution` on
`qubit ⊗ S` for an arbitrary target register `S` (`|u⟩` lives in `S`, drawn `/` for a multi-qubit
register). "The top qubit is measured to be `0`" is the outcome `0` of the control-qubit
computational-basis measurement `controlMeasurement S` (Postulate 3), and its probability is
`Measurement.bornProb` (the Born rule).

## What is formalised

* `measureObservableCircuit_bornProb_measure_control_zero` — the main result: on an eigenstate
  input `U|u⟩ = e^{2πiφ}|u⟩`, the control qubit is measured `0` with probability exactly `cos²(πφ)`.
* `measureObservableCircuit_bornProb_measure_control_zero_pow` — the **iteration** (`U → Uᵏ`): the
  same circuit with `Uᵏ` in place of `U` measures the control `0` with probability `cos²(πkφ)`.
  Increasing `k` (e.g. `k = 2ʲ`) sharpens successive bits of `φ` — the sense in which the algorithm
  "obtains as many bits of `φ` as desired" (an alternative to phase estimation). Proved by applying
  the headline to `Uᵏ`, an eigenstate of eigenvalue `e^{2πikφ}` (`Evolution.HasEigenstate.pow`).

## Design notes

* **Fidelity.** The target register `S` is *arbitrary*, matching N&C's `/`-wire
  `|u⟩` (a multi-qubit register in the phase-estimation setting); it is not specialised to a single
  qubit. The eigenvalue is the literal `e^{2πiφ}` (`Complex.exp (2πφ i)`), and the probability the
  literal `cos²(πφ)`, for arbitrary real `φ`. Both statements are full equalities of `bornProb`, not
  bounds or up-to-`ε` surrogates.
* **Reuse of `|u⟩`.** "The state `|u⟩` is unaffected by the circuit" is the *factorisation*
  `measureObservableCircuit_op_qubitBasisZero_tmul_smul`
  (`AxQM/Postulates/API/KitaevPhaseEstimation.lean`): the circuit output on `|0⟩ ⊗ |u⟩` is
  the product state `(½(1+μ) |0⟩ + ½(1−μ) |1⟩) ⊗ |u⟩`, whose right (target) factor is exactly the
  intact `|u⟩` — so `|u⟩` may be reused across iterations. The reuse claim is
  stated there; the Born-rule lemma below consumes it.
* **Proof.** The phase kickback and the control-projector Born probability
  `‖½(1+μ)‖²` are computed in the API file
  (`measureObservableCircuit_controlMeasurement_bornProb_zero_smul`). This file supplies
  the statement and the pure-phase arithmetic `‖½(1+e^{2πiφ})‖² = cos²(πφ)`
  (`|1+e^{iθ}|² = 2+2cos θ`, then the half-angle `cos²(πφ) = (1+cos 2πφ)/2`).
* **The "efficiently … as many bits as desired" claim** is a complexity statement about the number
  of repetitions and bit-extraction; the library has no cost model, so it is not formalised. Its
  formal core — the per-`k` measurement probability `cos²(πkφ)` that the bit-extraction reads — *is*
  captured (`…_pow`).
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Problem 5.3 (Kitaev's algorithm), outcome probability.** With `|u⟩` an
eigenstate of `U` of eigenvalue `e^{2πiφ}`, running the Hadamard-controlled-`U` circuit on
`|0⟩ ⊗ |u⟩` and measuring the control (top) qubit in the computational basis yields outcome `0`
with probability exactly `cos²(πφ)`:
```
        p(0) = cos²(πφ).
```
The target register `S` — where `|u⟩` lives — is arbitrary. Proof: the API Born-rule lemma
`measureObservableCircuit_controlMeasurement_bornProb_zero_smul` gives `p(0) = ‖½(1 + e^{2πiφ})‖²`;
the pure-phase identity `‖½(1 + e^{iθ})‖² = cos²(θ/2)` (from `|1 + e^{iθ}|² = 2 + 2cos θ` and the
half-angle formula) finishes it at `θ = 2πφ`. -/
theorem measureObservableCircuit_bornProb_measure_control_zero (U : Evolution S) (u : PureState S)
    (φ : ℝ) (h : U.HasEigenstate (Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I)) u) :
    (controlMeasurement S).bornProb
        ((measureObservableCircuit U).evolvePure ((qubitBasis 0).tmul u)).toState 0
      = Real.cos (Real.pi * φ) ^ 2 := by
  rw [measureObservableCircuit_controlMeasurement_bornProb_zero_smul U u h]
  -- Now: `‖½(1 + e^{2πiφ})‖² = cos²(πφ)`.  Expand `e^{2πiφ} = cos 2πφ + i sin 2πφ`
  -- (`Complex.exp_ofReal_mul_I_re`/`_im`), take the squared modulus
  -- `‖½(1 + e^{2πiφ})‖² = ¼((1 + cos 2πφ)² + sin² 2πφ)`, and use `sin² + cos² = 1` with the
  -- half-angle `cos²(πφ) = (1 + cos 2πφ)/2`.
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.inv_re, Complex.inv_im,
    Complex.re_ofNat, Complex.im_ofNat]
  rw [Real.cos_sq]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * φ * 2)]

/-- **Nielsen & Chuang, Problem 5.3, the iteration `U → Uᵏ`.** With `|u⟩` an eigenstate of `U` of
eigenvalue `e^{2πiφ}`, running the circuit with `Uᵏ` in place of `U` measures the control `0` with
probability `cos²(πkφ)`. Since `|u⟩` is unaffected (see the factorisation in the API file) it is
reused, and increasing `k` (e.g. through `k = 2ʲ`) sharpens the estimate of `φ` bit by bit — the
alternative to the phase-estimation algorithm. Proof: `|u⟩` is an eigenstate of `Uᵏ` of eigenvalue
`(e^{2πiφ})ᵏ = e^{2πikφ}` (`Evolution.HasEigenstate.pow`), so the first theorem applies with
`φ ↦ kφ`. -/
theorem measureObservableCircuit_bornProb_measure_control_zero_pow (U : Evolution S)
    (u : PureState S) (φ : ℝ) (k : ℕ)
    (h : U.HasEigenstate (Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I)) u) :
    (controlMeasurement S).bornProb
        ((measureObservableCircuit (U ^ k)).evolvePure ((qubitBasis 0).tmul u)).toState 0
      = Real.cos (Real.pi * ((k : ℝ) * φ)) ^ 2 := by
  refine measureObservableCircuit_bornProb_measure_control_zero (U ^ k) u ((k : ℝ) * φ) ?_
  have hz : Complex.exp (((2 * Real.pi * ((k : ℝ) * φ) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I) ^ k := by
    rw [← Complex.exp_natCast_mul]; congr 1; push_cast; ring
  rw [hz]
  exact h.pow k

end AxQM
