/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRControlledNot

/-!
# Nielsen & Chuang, Exercise 7.47 (NMR controlled-`NOT`)

*(N&C §7.7.4, p. 338.)*

NMR controlled-NOT gate: verify the Fig 7.19 circuit is a CNOT up to single-qubit phases; give a
proper CNOT circuit.

## The circuit

The Fig 7.19 (top left) circuit is `nmrCnotCircuit c t`
(in `AxQM/Postulates/API/NMRControlledNot.lean`): a `90°` `y`-pulse on the target spin, one period
`c·t = π/4` of `Z₁Z₂`-coupled evolution
`exp(-i c Z₁Z₂ t)`, then a `90°` `x`-pulse on the target — exactly the building blocks (`R_x`,
`R_y`, free `J`-coupling) of the figure.

## What is proved (the three parts of the exercise)

* **Acts properly on classical inputs** — `nmrCnotCircuit_op_apply_phase`
  (in `AxQM/Postulates/API/NMRControlledNot.lean`):
  `nmrCnotCircuit c t` sends each computational basis state `|a⟩⊗|b⟩` to `(phase)·|a⟩⊗|a⊕b⟩`, the
  correct CNOT permutation of the classical states, each acquiring a unit-modulus scalar.
* **Convertible to a proper CNOT by single-qubit `R_z` rotations** —
  `nmrCnot_globalPhase_correction_eq_cnotGate` below:
  `globalPhase(π/4) ∘ R_z(π/2)₁ ∘ R_z(-π/2)₂ ∘ nmrCnotCircuit c t = cnotGate`, an *exact* gate
  identity — the circuit is the controlled-`NOT` up to the two single-qubit `z`-rotations and a
  global phase.
* **Another circuit realising a proper CNOT** — `properNmrCnot` + `properNmrCnot_evolve_eq_cnotGate`
  below: the `R_z`-corrected circuit (same building blocks) induces the CNOT state channel on every
  input; the residual global phase is physically unobservable.

Both theorems are in terms of `globalPhaseGate`, `rotZGate`,
`Evolution.onLeft`/`onRight`/`comp`/`evolve`, `nmrCnotCircuit` and `cnotGate`; the
circuit, its basis action, and the phase are in `AxQM/Postulates/API/NMRControlledNot.lean`.

## Fidelity

The controlled-`NOT` target is the genuine `cnotGate`; the coupling is the genuine
`Observable.propagator` of the `Z₁Z₂`-coupling Hamiltonian; the pulses are the genuine
`rotX`/`rotY`/`rotZ` gates. No hypotheses beyond `c·t = π/4` (the "one evolution period" `1/2J` of
the figure).
-/

noncomputable section

namespace AxQM

-- The unused-tactic linter misreports the `try nlinarith` below: without it `nlinarith` runs on
-- goals `simp` already closed.
set_option linter.unusedTactic false in
/-- **Exercise 7.47 — the Fig 7.19 circuit is a controlled-`NOT` up to single-qubit `R_z` phases.**
For one coupling period `c·t = π/4`, prefixing the Fig 7.19 circuit `nmrCnotCircuit c t` (a `90°`
`y`-pulse, the `Z₁Z₂` coupling, a `90°` `x`-pulse) with the two single-qubit `z`-rotations
`R_z(π/2)` on the control and `R_z(-π/2)` on the target, and the global phase `e^{iπ/4}`, gives
*exactly* the controlled-`NOT` gate:

`globalPhase(π/4) ∘ R_z(π/2)₁ ∘ R_z(-π/2)₂ ∘ nmrCnotCircuit c t = cnotGate`.

This is the exercise's claim that the circuit "can be turned into a proper controlled-`⊕` gate by
applying additional single qubit `R_z` rotations". Proof: both gates act diagonally-up-to-a-flip on
each computational basis state `|a⟩⊗|b⟩`; the accumulated phase
`e^{iπ/4}·R_z(π/2)ₐₐ·R_z(-π/2)_{a⊕b,a⊕b}·nmrCnotPhase a b` equals `1` in each of the four cases. -/
theorem nmrCnot_globalPhase_correction_eq_cnotGate (c t : ℝ) (h : c * t = Real.pi / 4) :
    (globalPhaseGate (Real.pi / 4)).comp
        (((rotZGate (Real.pi / 2)).onLeft qubit).comp
          (((rotZGate (-(Real.pi / 2))).onRight qubit).comp (nmrCnotCircuit c t)))
      = cnotGate := by
  apply twoQubit_evolution_ext
  intro a b
  apply PureState.ext
  rw [Evolution.evolvePure_vec, Evolution.evolvePure_vec, Evolution.comp_op, Evolution.comp_op,
    Evolution.comp_op, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, PureState.tmul_vec, nmrCnotCircuit_op_apply_phase c t h]
  simp only [map_smul, Evolution.onRight_op_tmul, Evolution.onLeft_op_tmul,
    rotZGate_op_apply_qubitBasis, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    smul_smul]
  rw [cnotGate_op_apply_qubitBasis]
  have hscalar : Complex.exp (↑(Real.pi / 4) * Complex.I) *
      (Concrete.rotZ (-(Real.pi / 2)) (a + b) (a + b) * nmrCnotPhase a b *
        Concrete.rotZ (Real.pi / 2) a a) = 1 := by
    have hep : Complex.exp (↑(Real.pi / 4) * Complex.I)
        = ↑(Real.sqrt 2) / 2 + ↑(Real.sqrt 2) / 2 * Complex.I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
        Real.sin_pi_div_four]; push_cast; ring
    have hea : Complex.exp (-(↑(-(Real.pi / 2)) / 2) * Complex.I)
        = ↑(Real.sqrt 2) / 2 + ↑(Real.sqrt 2) / 2 * Complex.I := by
      rw [show (-(↑(-(Real.pi / 2)) / 2) * Complex.I) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
    have heb : Complex.exp (-(↑(Real.pi / 2) / 2) * Complex.I)
        = ↑(Real.sqrt 2) / 2 - ↑(Real.sqrt 2) / 2 * Complex.I := by
      rw [show (-(↑(Real.pi / 2) / 2) * Complex.I) = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
    have hec : Complex.exp (↑(-(Real.pi / 2)) / 2 * Complex.I)
        = ↑(Real.sqrt 2) / 2 - ↑(Real.sqrt 2) / 2 * Complex.I := by
      rw [show (↑(-(Real.pi / 2)) / 2 * Complex.I) = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
    have hed : Complex.exp (↑(Real.pi / 2) / 2 * Complex.I)
        = ↑(Real.sqrt 2) / 2 + ↑(Real.sqrt 2) / 2 * Complex.I := by
      rw [show (↑(Real.pi / 2) / 2 * Complex.I) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_four, Real.sin_pi_div_four]; push_cast; ring
    fin_cases a <;> fin_cases b <;>
      · simp only [nmrCnotPhase, Fin.isValue, Fin.mk_zero, Fin.mk_one, Fin.reduceAdd,
          Concrete.rotZ_apply_zero_zero, Concrete.rotZ_apply_one_one, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.of_apply, hep, hea, heb, hec, hed]
        rw [Complex.ext_iff]
        refine ⟨?_, ?_⟩ <;>
          (simp; try nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2])
  have hg := globalPhaseGate_op_apply (S := qubit ⊗ qubit) (Real.pi / 4)
    (((Concrete.rotZ (-(Real.pi / 2)) (a + b) (a + b) * nmrCnotPhase a b *
        Concrete.rotZ (Real.pi / 2) a a) • (qubitBasis a).vec) ⊗ₜ[ℂ] (qubitBasis (a + b)).vec)
  have goalGeneric : Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) •
      (((Concrete.rotZ (-(Real.pi / 2)) (a + b) (a + b) * nmrCnotPhase a b *
          Concrete.rotZ (Real.pi / 2) a a) • (qubitBasis a).vec) ⊗ₜ[ℂ] (qubitBasis (a + b)).vec)
        = (qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis (a + b)).vec := by
    rw [TensorProduct.smul_tmul', smul_smul, hscalar, one_smul]
  rw [hg]
  exact goalGeneric

/-- **Exercise 7.47 — another circuit, from the same building blocks, that realises a *proper*
controlled-`NOT`.** The Fig 7.19 circuit followed by the two single-qubit `z`-rotations `R_z(π/2)`
on the control and `R_z(-π/2)` on the target — the *same building blocks* (single-qubit rotations
and one `Z₁Z₂` coupling period), no global phase needed. -/
def properNmrCnot (c t : ℝ) : Evolution (qubit ⊗ qubit) :=
  ((rotZGate (Real.pi / 2)).onLeft qubit).comp
    (((rotZGate (-(Real.pi / 2))).onRight qubit).comp (nmrCnotCircuit c t))

/-- **Exercise 7.47 — the proper controlled-`NOT` circuit realises the CNOT channel.** For one
coupling period `c·t = π/4`, the `R_z`-corrected Fig 7.19 circuit `properNmrCnot c t` induces the
*same state channel* `ρ ↦ U ρ U†` as the genuine controlled-`NOT` gate, on **every** state `ρ`:
the residual global phase `e^{iπ/4}` of the exact gate identity is physically unobservable (it
cancels in the conjugation), so these single-qubit rotations plus one coupling period realise a
proper CNOT — the answer to the second half of the exercise. -/
theorem properNmrCnot_evolve_eq_cnotGate (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (properNmrCnot c t).evolve ρ = cnotGate.evolve ρ := by
  rw [← globalPhaseGate_comp_evolve (Real.pi / 4) (properNmrCnot c t) ρ, properNmrCnot,
    nmrCnot_globalPhase_correction_eq_cnotGate c t h]

end AxQM
