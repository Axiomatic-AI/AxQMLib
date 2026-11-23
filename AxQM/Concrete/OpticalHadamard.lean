/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LinearOpticalElement
import AxQM.Concrete.Hadamard

/-!
# Concrete: the optical Hadamard circuit (Nielsen & Chuang, Exercise 7.9)

Nielsen & Chuang, Exercise 7.9 (*Optical Hadamard gate*, p. 292), asks to show that a particular
linear-optical circuit — a phase shifter followed by a beamsplitter — acts as a **Hadamard gate**
on the dual-rail single-photon qubit, i.e.
`|01⟩ → (|01⟩ + |10⟩)/√2` and `|10⟩ → (|01⟩ − |10⟩)/√2`, up to an overall phase.

In the dual-rail encoding a single photon occupies one of two spatial modes, so the logical qubit
lives in the two-mode single-photon space `Fin 2 → ℂ` with the two computational-basis logical
states `|01⟩` (photon in the top mode `0`) and `|10⟩` (photon in the bottom mode `1`) — exactly the
`{|0_L⟩, |1_L⟩}` manifold on which N&C write the beamsplitter and phase shifter as `2 × 2` matrices
(eq. 7.23, 7.35). The two circuit elements are the linear-optical elements of
`AxQM.Concrete.LinearOpticalElement`:

* the **phase shifter** `phaseMode 0 π = diag(e^{iπ}, 1) = diag(-1, 1)` on the top mode (the `π`
  box of N&C's Exercise 7.7), and
* the **beamsplitter** `beamSplitter 0 1 (π/2)`, i.e. N&C's `B(π/4) = !![cos(π/4), −sin(π/4);
  sin(π/4), cos(π/4)]` mixing the two modes (N&C's mixing angle `θ = π/4` is the repo's `rotY`
  half-angle convention `beamSplitter … (2θ)`).

## What is formalised

* `opticalHadamardCircuit` — the circuit matrix `beamSplitter 0 1 (π/2) * phaseMode 0 π` (circuit
  order left-to-right = matrix product right-to-left: the photon meets the phase shifter first).
* `opticalHadamardCircuit_eq_smul_hadamardC` — **the headline**: the circuit equals the Hadamard
  matrix up to the overall phase `e^{iπ}`, `opticalHadamardCircuit = e^{iπ} • hadamardC`. This is
  Exercise 7.9's claim: the circuit *is* a Hadamard gate up to a physically irrelevant global phase.
* `opticalHadamardCircuit_eq_neg_hadamardC` — the same identity with the phase evaluated,
  `opticalHadamardCircuit = -hadamardC`.
* `opticalHadamardCircuit_mulVec_zeroOne` / `_oneZero` — the explicit action on the two dual-rail
  basis states, `|01⟩ ↦ -(√2)⁻¹(|01⟩ + |10⟩)` and `|10⟩ ↦ -(√2)⁻¹(|01⟩ − |10⟩)`, literally N&C's
  stated mapping up to the overall phase `-1 = e^{iπ}`.
* `opticalHadamardCircuit_isLinearOpticalProduct` — the circuit is genuinely a product of
  linear-optical elements (a beamsplitter and a phase shifter), certifying it is the optical circuit
  the exercise draws.

The statement of Exercise 7.9 is in `AxQM/NC/Ch7/Exercise7_9.lean`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The full-pair beamsplitter is its rotation block.** For the only mode pair of a two-mode
system, `p = 0`, `q = 1`, the two-level embedding `twoLevelEmbed 0 1` is the whole matrix, so the
beamsplitter `beamSplitter 0 1 θ` is exactly the real rotation `R_y(θ)`. -/
theorem beamSplitter_zero_one (θ : ℝ) :
    beamSplitter (0 : Fin 2) 1 θ = rotY θ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [beamSplitter, twoLevelEmbed_apply]

/-- **The optical Hadamard circuit of Nielsen & Chuang, Exercise 7.9.** A phase shifter `phaseMode 0
π` on the top mode followed by a beamsplitter `beamSplitter 0 1 (π/2)` (N&C's `B(π/4)`); as a matrix
the circuit is the product `beamSplitter 0 1 (π/2) * phaseMode 0 π` (the photon passes the phase
shifter first, so it is the right factor). -/
noncomputable def opticalHadamardCircuit : Matrix (Fin 2) (Fin 2) ℂ :=
  beamSplitter 0 1 (Real.pi / 2) * phaseMode 0 Real.pi

/-- **Nielsen & Chuang, Exercise 7.9: the optical circuit is a Hadamard gate up to global phase.**
`opticalHadamardCircuit = e^{iπ} • hadamardC`. The beamsplitter contributes the `R_y(π/2)` rotation
`(√2)⁻¹ !![1, -1; 1, 1]` and the phase shifter the diagonal `diag(-1, 1)`; their product is
`-(√2)⁻¹ !![1, 1; 1, -1] = e^{iπ} • H`, the Hadamard up to the overall phase `e^{iπ} = -1`. -/
theorem opticalHadamardCircuit_eq_smul_hadamardC :
    opticalHadamardCircuit = Complex.exp ((Real.pi : ℂ) * Complex.I) • hadamardC := by
  have hsqrt : (Real.sqrt 2 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linarith [h2]
  have hc : Real.cos (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring]; exact Real.cos_pi_div_four
  have hs : Real.sin (Real.pi / 2 / 2) = Real.sqrt 2 / 2 := by
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring]; exact Real.sin_pi_div_four
  rw [opticalHadamardCircuit, beamSplitter_zero_one, rotY_eq, Complex.exp_pi_mul_I, hadamardC]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseMode_apply, Matrix.mul_apply, hc, hs, hsqrt, Matrix.smul_apply,
      Complex.ofReal_inv]

/-- **The optical circuit equals `-H`.** The overall phase `e^{iπ}` of
`opticalHadamardCircuit_eq_smul_hadamardC` evaluated: `opticalHadamardCircuit = -hadamardC`. -/
theorem opticalHadamardCircuit_eq_neg_hadamardC :
    opticalHadamardCircuit = -hadamardC := by
  rw [opticalHadamardCircuit_eq_smul_hadamardC, Complex.exp_pi_mul_I, neg_one_smul]

/-- **Action on the logical `|01⟩` state.** The circuit sends `|01⟩ = ![1, 0]` to
`-(√2)⁻¹ (|01⟩ + |10⟩)`, i.e. `(|01⟩ + |10⟩)/√2` up to the overall phase `-1 = e^{iπ}` — the first
half of N&C's stated Hadamard mapping. -/
theorem opticalHadamardCircuit_mulVec_zeroOne :
    opticalHadamardCircuit *ᵥ ![1, 0] = (-(Real.sqrt 2)⁻¹ : ℂ) • ![1, 1] := by
  rw [opticalHadamardCircuit_eq_neg_hadamardC, hadamardC]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ofReal_inv]

/-- **Action on the logical `|10⟩` state.** The circuit sends `|10⟩ = ![0, 1]` to
`-(√2)⁻¹ (|01⟩ − |10⟩)`, i.e. `(|01⟩ − |10⟩)/√2` up to the overall phase `-1 = e^{iπ}` — the second
half of N&C's stated Hadamard mapping. -/
theorem opticalHadamardCircuit_mulVec_oneZero :
    opticalHadamardCircuit *ᵥ ![0, 1] = (-(Real.sqrt 2)⁻¹ : ℂ) • ![1, -1] := by
  rw [opticalHadamardCircuit_eq_neg_hadamardC, hadamardC]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ofReal_inv]

/-- **The circuit is a genuine linear-optical circuit.** `opticalHadamardCircuit` is the product of
a list of `IsLinearOpticalElement`s — the beamsplitter `beamSplitter 0 1 (π/2)` and the phase
shifter `phaseMode 0 π` — so it is realisable by exactly the two passive optical elements the
exercise draws. -/
theorem opticalHadamardCircuit_isLinearOpticalProduct :
    ∃ L : List (Matrix (Fin 2) (Fin 2) ℂ),
      (∀ V ∈ L, IsLinearOpticalElement V) ∧ L.prod = opticalHadamardCircuit := by
  refine ⟨[beamSplitter 0 1 (Real.pi / 2), phaseMode 0 Real.pi], ?_, ?_⟩
  · intro V hV
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hV
    rcases hV with rfl | rfl
    · exact Or.inl ⟨0, 1, Real.pi / 2, by decide, rfl⟩
    · exact Or.inr ⟨0, Real.pi, rfl⟩
  · simp [opticalHadamardCircuit]

end AxQM.Concrete
