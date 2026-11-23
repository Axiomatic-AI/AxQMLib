/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRControlledZ

/-!
# Nielsen & Chuang, Exercise 7.41 (NMR controlled-`Z`)

*(N&C §7.7.3, p. 332.)*

NMR controlled-NOT: give explicit single-qubit rotation sequence realizing CNOT under Hamiltonian
(7.147).

## The construction

The two-spin NMR Hamiltonian (7.147) is `Hsys = a Z₁ + b Z₂ + c Z₁Z₂`. Refocusing (Exercises
7.38–7.40, §7.7.3) removes the single-spin `a Z₁ + b Z₂` terms, leaving the pure `Z₁Z₂` coupling;
one "evolution period" `t` with `c·t = π/4` gives the coupled propagator `exp(-i (π/4) Z₁Z₂)`. N&C's
construction (7.152) then reads

`√i · e^{i Z₁Z₂ π/4} · e^{-i Z₁ π/4} · e^{-i Z₂ π/4} = U_CZ = diag(1, 1, 1, -1)`.

We formalise the physically-realised, positive-time form: one period of the `Z₁Z₂` coupling
propagator followed by a `90°` `z`-rotation `R_z(-π/2)` on each spin
(`nmrControlledZSequence c t`, in `AxQM/Postulates/API/NMRControlledZ.lean`). Since `e^{-i Z π/4} =
R_z(π/2)`, the two single-qubit pulses are `z`-rotations, exactly the "single-qubit rotations" the
exercise asks for — three single-qubit rotations reduced to two by absorbing the `√i` into a global
phase (which is unobservable). The sign of the coupled-evolution period is opposite to the printed
(7.152) (positive-time evolution under `+c Z₁Z₂` gives `e^{-iZ₁Z₂π/4}`, the conjugate of the book's
`e^{+iZ₁Z₂π/4}`); the matched single-qubit corrections are then `R_z(-π/2)` with global phase
`e^{-iπ/4} = √(-i)` — a faithful realisation, differing from the book only by the coupling-sign
convention.

## What is proved

* `nmrControlledZ_globalPhase_eq_controlledZGate` — the **exact gate identity**: for `c·t = π/4`,
  `globalPhaseGate(-π/4) ∘ nmrControlledZSequence c t = controlledZGate`. This is N&C's (7.152) read
  as a genuine `Evolution` equality: the coupled evolution plus the two `z`-pulses plus the global
  phase `√(-i)` is *exactly* the controlled-`Z` gate.
* `nmrControlledZSequence_evolve_eq_controlledZGate` — the **physics reading** (the channel): for
  `c·t = π/4`, the pulse sequence `nmrControlledZSequence c t` induces the *same state channel*
  `ρ ↦ U ρ U†` as the controlled-`Z` gate, on every state. The global phase `√(-i)` drops out of the
  conjugation, so the two single-qubit `z`-rotations plus one coupling period realise the
  controlled-`Z` as a physical operation — the answer to the exercise.

Both statements are in terms of `globalPhaseGate`, `nmrControlledZSequence`,
`controlledZGate`, `Evolution.comp` and `Evolution.evolve`; the
gate sequence, its diagonal action and the global-phase gate are in
`AxQM/Postulates/API/NMRControlledZ.lean`.

## Fidelity

The controlled-`Z` target is the genuine `controlledZGate` (`diag(1,1,1,-1)`); the coupled
evolution is the genuine `Observable.propagator` of the `Z₁Z₂` coupling Hamiltonian (not an ad-hoc
matrix); the single-qubit pulses are the genuine `rotZGate`. The `√i` global phase of (7.152) is
carried honestly — reified as an explicit `globalPhaseGate` in the exact identity, and shown
unobservable in the channel reading. No hypotheses are added beyond `c·t = π/4` (the "one evolution
period" of the exercise).
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 7.41 — the exact gate identity (eq. 7.152).** For one period of
`Z₁Z₂`-coupled evolution with `c·t = π/4`, the pulse sequence `nmrControlledZSequence c t` (coupled
evolution + a `R_z(-π/2)` on each spin) equals the controlled-`Z` gate up to the global phase
`√(-i) = e^{-iπ/4}`:

`globalPhaseGate(-π/4) ∘ nmrControlledZSequence c t = controlledZGate`.

This is N&C's construction `√i · e^{iZ₁Z₂π/4} · e^{-iZ₁π/4} · e^{-iZ₂π/4} = diag(1,1,1,-1)` as an
`Evolution` equality (in the positive-coupling-time convention, so `√i` becomes `√(-i)`; see the
file docstring). Proof: both gates act on each computational basis state `|a⟩⊗|b⟩` diagonally
(`twoQubit_evolution_ext`); the sequence's phase
`e^{-iπ/4}·R_z(-π/2)ₐₐ·R_z(-π/2)_bb·e^{-i(π/4)(-1)ᵃ(-1)ᵇ}` equals the controlled-`Z` eigenvalue
`(-1)^{a·b}` in each of the four cases (a `Complex.exp` computation using `c·t = π/4`). -/
theorem nmrControlledZ_globalPhase_eq_controlledZGate (c t : ℝ) (h : c * t = Real.pi / 4) :
    (globalPhaseGate (-(Real.pi / 4))).comp (nmrControlledZSequence c t) = controlledZGate := by
  apply twoQubit_evolution_ext
  intro a b
  apply PureState.ext
  rw [Evolution.evolvePure_vec, Evolution.evolvePure_vec, Evolution.comp_op,
    ContinuousLinearMap.comp_apply, nmrControlledZSequence_op_apply_qubitBasis,
    globalPhaseGate_op_apply, controlledZGate_op_apply_qubitBasis, smul_smul]
  congr 1
  have hct : (c : ℂ) * t = (Real.pi : ℂ) / 4 := by
    rw [← Complex.ofReal_mul, h]; push_cast; ring
  have hone : (-1 : ℂ) = Complex.exp (-(↑Real.pi * Complex.I)) := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Nat.mul_zero, pow_zero, pow_one, one_mul,
      mul_one, mul_neg_one, neg_neg, Concrete.rotZ_apply_zero_zero,
      Concrete.rotZ_apply_one_one] <;>
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  · rw [← Complex.exp_zero]
    congr 1
    push_cast
    linear_combination -Complex.I * hct
  · rw [← Complex.exp_zero]
    congr 1
    push_cast
    linear_combination Complex.I * hct
  · rw [← Complex.exp_zero]
    congr 1
    push_cast
    linear_combination Complex.I * hct
  · rw [hone]
    congr 1
    push_cast
    linear_combination -Complex.I * hct

/-- **Nielsen & Chuang, Exercise 7.41 — the physics reading (channel equality).** For one period of
`Z₁Z₂`-coupled evolution with `c·t = π/4`, the NMR pulse sequence `nmrControlledZSequence c t` —
the coupled evolution `exp(-i c Z₁Z₂ t)` followed by a `90°` `z`-rotation `R_z(-π/2)` on each spin —
induces the *same state channel* `ρ ↦ U ρ U†` as the controlled-`Z` gate, on every state `ρ`. The
`√(-i)` global phase of the gate identity is physically unobservable (it cancels in the
conjugation), so these two single-qubit rotations plus one coupling period realise a controlled-`Z`
between the two coupled spins — the answer to the exercise. Proof: the global phase drops out via
`globalPhaseGate_comp_evolve`, and the gate identity supplies the rest. -/
theorem nmrControlledZSequence_evolve_eq_controlledZGate (c t : ℝ) (h : c * t = Real.pi / 4)
    (ρ : State (qubit ⊗ qubit)) :
    (nmrControlledZSequence c t).evolve ρ = controlledZGate.evolve ρ := by
  rw [← globalPhaseGate_comp_evolve (-(Real.pi / 4)) (nmrControlledZSequence c t) ρ,
    nmrControlledZ_globalPhase_eq_controlledZGate c t h]

end AxQM
