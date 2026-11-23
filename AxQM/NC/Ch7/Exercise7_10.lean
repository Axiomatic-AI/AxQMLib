/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Beamsplitter

/-!
# Nielsen & Chuang, Exercise 7.10 (Mach–Zehnder interferometer)

*(N&C p. 292.)*

Mach-Zehnder interferometer: show identity circuit and compute rotation as function of phase φ.

**The physics (N&C §7.4.2).** A logical qubit is dual-rail encoded as a single photon shared between
two optical modes, `|ψ⟩ = c₀|01⟩ + c₁|10⟩` (`dualRail`). A beamsplitter `B(θ)` mixes the two modes;
on the logical manifold `{|0_L⟩ = |01⟩, |1_L⟩ = |10⟩}` it is the real rotation
`[[cos θ, -sin θ]; [sin θ, cos θ]]` of N&C eq. (7.35), realised on `qubit ⊗ qubit` as the
number-conserving planar rotation `beamSplitterDualRail θ` (an `Evolution`; see
`AxQM/Postulates/API/Beamsplitter.lean`). A Mach–Zehnder interferometer chains two beamsplitters;
the two are *mutually inverse* (the recombining beamsplitter reverses the splitting one), so with
balanced arms and **no** phase shift the circuit is the identity — part 1. Inserting a phase shifter
between them makes the output depend on the phase, converting a phase shift into an observable
rotation of the logical qubit — the interferometer's measuring principle, part 2.

## The formalisation

**Part 1 — the identity circuit.**

* `machZehnderIdentityCircuit θ` — the two-beamsplitter circuit `B(-θ) ∘ B(θ)` (the recombining
  beamsplitter is the inverse of the splitting one; two *identical* `B(θ)` would instead give the
  rotation `B(2θ) ≠ 1`, so the inverse pairing is exactly what makes the interferometer close).
* `machZehnderIdentityCircuit_eq_id` — **part 1**: the circuit *is* the identity `Evolution`,
  `B(-θ) ∘ B(θ) = 1`, immediate from the beamsplitter group law `B(α) ∘ B(β) = B(α+β)` at
  `α + β = 0`. (This is stronger than "acts as the identity on dual-rail states" — it is the
  identity operation on the whole two-qubit space.)

**Part 2 — the rotation performed by the phased circuit.** The interferometer with a phase shifter
`P(φ) = diag(e^{iφ}, 1)` (on the `|01⟩` mode, as in Exercise 7.7) between two balanced `50/50`
beamsplitters (`θ = π/4`):

* `machZehnder φ` — the circuit `B(-π/4) ∘ P(φ) ∘ B(π/4)` as an `Evolution (qubit ⊗ qubit)`.
* `machZehnder_evolvePure_dualRail` — **part 2 (the computed operation)**: it sends
  `c₀|01⟩ + c₁|10⟩` to the dual-rail state with amplitudes
  `½((e^{iφ}+1)c₀ + (1-e^{iφ})c₁),  ½((1-e^{iφ})c₀ + (e^{iφ}+1)c₁)`, the rotation operation as an
  explicit function of the phase `φ`.
* `machZehnder_evolvePure_dualRail_rotX` — **part 2 (the rotation identified)**: the same output
  written as `e^{iφ/2}·R_x(φ)` applied to `(c₀, c₁)`, i.e. the amplitudes are
  `e^{iφ/2}(cos(φ/2)·c₀ - i·sin(φ/2)·c₁)` and `e^{iφ/2}(-i·sin(φ/2)·c₀ + cos(φ/2)·c₁)`. So up to the
  physically-irrelevant global phase `e^{iφ/2}`, the interferometer performs the `x`-axis rotation
  `R_x(φ) = e^{-iφX/2}` by the phase `φ` — the rotation N&C ask for. At `φ = 0` this is
  `R_x(0) = 1`, consistent with part 1.
* `machZehnder_amp_normalized` / `machZehnder_rotX_amp_normalized` — the amplitude normalisation
  conditions (the circuit is unitary, so the output amplitudes are again normalised), needed to
  build the output `dualRail` states.

## Remarks

The circuit is a composite `Evolution` on `qubit ⊗ qubit`, built from the beamsplitter and
phase-shifter `Evolution`s of `AxQM/Postulates/API/`. The theorems are stated for `evolvePure`,
`dualRail`, `beamSplitterDualRail`, `phaseShiftGate.onRight` and `Evolution.id`. The two `private`
half-angle identities `mz_half_cos`/`mz_half_sin` are proof-local scalar identities for the `R_x`
identification.

**Why an `Evolution` on `qubit ⊗ qubit`, not a single-qubit gate.** Following the dual-rail
beamsplitter (`AxQM/Postulates/API/Beamsplitter.lean`): the phase shifter of Exercise 7.7
is an `Evolution` of `qubit ⊗ qubit`, so to compose beamsplitters and phase shifter into one
circuit the beamsplitter must act on that same system. The physical beamsplitter does not preserve
the `qubit ⊗ qubit` truncation on the two-photon `|11⟩`, but N&C (7.35) only specifies its logical
`2 × 2` action on `span{|01⟩, |10⟩}`, faithfully modelled by the number-conserving planar rotation
that fixes the orthogonal complement.
-/

open scoped InnerProductSpace TensorProduct

open Complex

noncomputable section

namespace AxQM

/-! ### Part 1 — two inverse beamsplitters perform the identity -/

/-- The **Exercise 7.10.1 identity circuit**: two beamsplitters `B(-θ)` and `B(θ)` in series, i.e.
`beamSplitterDualRail (-θ) ∘ beamSplitterDualRail θ`. In a Mach–Zehnder interferometer the
recombining beamsplitter is the inverse of the splitting one, so their mixing angles are
opposite. -/
def machZehnderIdentityCircuit (θ : ℝ) : Evolution (qubit ⊗ qubit) :=
  (beamSplitterDualRail (-θ)).comp (beamSplitterDualRail θ)

/-- **Exercise 7.10, part 1: the two-beamsplitter circuit performs the identity operation.**
`B(-θ) ∘ B(θ) = 1`. Immediate from the beamsplitter angle-addition group law
`B(α) ∘ B(β) = B(α+β)` (`beamSplitterDualRail_comp`) at `α + β = 0` together with `B(0) = 1`
(`beamSplitterDualRail_zero`). Two *identical* beamsplitters would instead give `B(2θ)`, a rotation
by `2θ`; the interferometer closes to the identity precisely because its two beamsplitters are
mutually inverse. -/
theorem machZehnderIdentityCircuit_eq_id (θ : ℝ) :
    machZehnderIdentityCircuit θ = Evolution.id := by
  rw [machZehnderIdentityCircuit, beamSplitterDualRail_comp, neg_add_cancel,
    beamSplitterDualRail_zero]

/-! ### Part 2 — the phased interferometer as a rotation by the phase `φ` -/

/-- The **Exercise 7.10.2 Mach–Zehnder circuit**: a phase shifter `P(φ)` on the `|01⟩` mode placed
between two balanced `50/50` beamsplitters `B(π/4)` and `B(-π/4)`, i.e.
`B(-π/4) ∘ P(φ) ∘ B(π/4)` as an `Evolution (qubit ⊗ qubit)` (the photon meets `B(π/4)` first, so it
is the rightmost factor). -/
def machZehnder (φ : ℝ) : Evolution (qubit ⊗ qubit) :=
  (beamSplitterDualRail (-(Real.pi / 4))).comp
    (((phaseShiftGate φ).onRight qubit).comp (beamSplitterDualRail (Real.pi / 4)))

/-- **The output amplitudes of the Mach–Zehnder circuit are normalised.** The circuit is unitary and
the dual-rail codewords are orthonormal, so the rotated amplitudes
`(½((e^{iφ}+1)c₀ + (1-e^{iφ})c₁), ½((1-e^{iφ})c₀ + (e^{iφ}+1)c₁))` again satisfy
`‖·‖² + ‖·‖² = 1`. Reduces through unitarity: the amplitudes are the image of the normalised input
under `(machZehnder φ).op` (the operator-level core `machZehnderDualRail_op_apply_dualRailVec`),
which preserves norm. -/
theorem machZehnder_amp_normalized (φ : ℝ) (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖2⁻¹ * ((Complex.exp ((φ : ℂ) * I) + 1) * c0 + (1 - Complex.exp ((φ : ℂ) * I)) * c1)‖ ^ 2
      + ‖2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * I)) * c0 + (Complex.exp ((φ : ℂ) * I) + 1) * c1)‖ ^ 2
        = 1 := by
  have hop : (machZehnder φ).op (dualRailVec c0 c1)
      = dualRailVec
          (2⁻¹ * ((Complex.exp ((φ : ℂ) * I) + 1) * c0 + (1 - Complex.exp ((φ : ℂ) * I)) * c1))
          (2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * I)) * c0 + (Complex.exp ((φ : ℂ) * I) + 1) * c1)) :=
      by
    rw [machZehnder, Evolution.comp_op, Evolution.comp_op,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact machZehnderDualRail_op_apply_dualRailVec φ c0 c1
  rw [← norm_dualRailVec_sq, ← hop, (machZehnder φ).norm_op_apply, norm_dualRailVec c0 c1 h,
    one_pow]

/-- **Exercise 7.10, part 2 (the computed operation).** The balanced Mach–Zehnder circuit sends the
dual-rail state `c₀|01⟩ + c₁|10⟩` to the state with amplitudes
`½((e^{iφ}+1)c₀ + (1-e^{iφ})c₁)` and `½((1-e^{iφ})c₀ + (e^{iφ}+1)c₁)` — the rotation operation the
circuit performs, as an explicit function of the phase shift `φ`. (The `R_x(φ)` reading of this
matrix is `machZehnder_evolvePure_dualRail_rotX`.) -/
theorem machZehnder_evolvePure_dualRail (φ : ℝ) (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    (machZehnder φ).evolvePure (dualRail c0 c1 h)
      = dualRail
          (2⁻¹ * ((Complex.exp ((φ : ℂ) * I) + 1) * c0 + (1 - Complex.exp ((φ : ℂ) * I)) * c1))
          (2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * I)) * c0 + (Complex.exp ((φ : ℂ) * I) + 1) * c1))
          (machZehnder_amp_normalized φ c0 c1 h) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, dualRail_vec, dualRail_vec, machZehnder, Evolution.comp_op,
    Evolution.comp_op, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact machZehnderDualRail_op_apply_dualRailVec φ c0 c1

/-- Half-angle identity `½(e^{iφ} + 1) = e^{iφ/2}·cos(φ/2)`, the diagonal entry of the `R_x(φ)`
identification (`2cos²(φ/2) = 1 + cos φ`, `2 sin(φ/2)cos(φ/2) = sin φ`). Proof-local scaffolding. -/
private theorem mz_half_cos (φ : ℝ) :
    (2 : ℂ)⁻¹ * (Complex.exp ((φ : ℂ) * I) + 1)
      = Complex.exp (((φ / 2 : ℝ) : ℂ) * I) * (Real.cos (φ / 2) : ℂ) := by
  have dc : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    have hh := Real.cos_two_mul (φ / 2); rw [show 2 * (φ / 2) = φ by ring] at hh; linarith [hh]
  have ds : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    have hh := Real.sin_two_mul (φ / 2); rw [show 2 * (φ / 2) = φ by ring] at hh; linarith [hh]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, dc, ds]
  push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]; ring

/-- Half-angle identity `½(1 - e^{iφ}) = e^{iφ/2}·(-i·sin(φ/2))`, the off-diagonal entry of the
`R_x(φ)` identification (`1 - cos φ = 2 sin²(φ/2)`, `i² = -1`). Proof-local scaffolding. -/
private theorem mz_half_sin (φ : ℝ) :
    (2 : ℂ)⁻¹ * (1 - Complex.exp ((φ : ℂ) * I))
      = Complex.exp (((φ / 2 : ℝ) : ℂ) * I) * (-(I * (Real.sin (φ / 2) : ℂ))) := by
  have dc' : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have hh := Real.cos_two_mul (φ / 2); have hp := Real.sin_sq_add_cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at hh; nlinarith [hh, hp]
  have ds : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    have hh := Real.sin_two_mul (φ / 2); rw [show 2 * (φ / 2) = φ by ring] at hh; linarith [hh]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, dc', ds]
  push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
  linear_combination ((Real.sin (φ / 2) : ℂ) ^ 2) * Complex.I_sq

/-- **The `R_x(φ)` output amplitudes are normalised.** They equal the Mach–Zehnder output amplitudes
(`mz_half_cos`/`mz_half_sin`), which are normalised (`machZehnder_amp_normalized`). -/
theorem machZehnder_rotX_amp_normalized (φ : ℝ) (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    ‖Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
          * ((Real.cos (φ / 2) : ℂ) * c0 - I * (Real.sin (φ / 2) : ℂ) * c1)‖ ^ 2
      + ‖Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
          * (-(I * (Real.sin (φ / 2) : ℂ)) * c0 + (Real.cos (φ / 2) : ℂ) * c1)‖ ^ 2
        = 1 := by
  have e0 : Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
        * ((Real.cos (φ / 2) : ℂ) * c0 - I * (Real.sin (φ / 2) : ℂ) * c1)
      = 2⁻¹ * ((Complex.exp ((φ : ℂ) * I) + 1) * c0 + (1 - Complex.exp ((φ : ℂ) * I)) * c1) := by
    linear_combination -c0 * mz_half_cos φ - c1 * mz_half_sin φ
  have e1 : Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
        * (-(I * (Real.sin (φ / 2) : ℂ)) * c0 + (Real.cos (φ / 2) : ℂ) * c1)
      = 2⁻¹ * ((1 - Complex.exp ((φ : ℂ) * I)) * c0 + (Complex.exp ((φ : ℂ) * I) + 1) * c1) := by
    linear_combination -c0 * mz_half_sin φ - c1 * mz_half_cos φ
  rw [e0, e1]; exact machZehnder_amp_normalized φ c0 c1 h

/-- **Exercise 7.10, part 2 (the rotation identified).** The balanced Mach–Zehnder circuit acts on
the dual-rail qubit as `e^{iφ/2}·R_x(φ)`: it sends `c₀|01⟩ + c₁|10⟩` to the state with amplitudes
`e^{iφ/2}(cos(φ/2)·c₀ - i·sin(φ/2)·c₁)` and `e^{iφ/2}(-i·sin(φ/2)·c₀ + cos(φ/2)·c₁)`. These are
`e^{iφ/2}` times the action on `(c₀, c₁)` of `R_x(φ) = e^{-iφX/2}`, whose matrix is
`[[cos(φ/2), -i sin(φ/2)]; [-i sin(φ/2), cos(φ/2)]]`. So up to the unobservable global phase
`e^{iφ/2}` the interferometer performs the `x`-axis rotation by the phase `φ` — the rotation N&C
ask to compute. At `φ = 0` it reduces to the
identity, consistent with part 1 (`machZehnderIdentityCircuit_eq_id`). -/
theorem machZehnder_evolvePure_dualRail_rotX (φ : ℝ) (c0 c1 : ℂ) (h : ‖c0‖ ^ 2 + ‖c1‖ ^ 2 = 1) :
    (machZehnder φ).evolvePure (dualRail c0 c1 h)
      = dualRail
          (Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
            * ((Real.cos (φ / 2) : ℂ) * c0 - I * (Real.sin (φ / 2) : ℂ) * c1))
          (Complex.exp (((φ / 2 : ℝ) : ℂ) * I)
            * (-(I * (Real.sin (φ / 2) : ℂ)) * c0 + (Real.cos (φ / 2) : ℂ) * c1))
          (machZehnder_rotX_amp_normalized φ c0 c1 h) := by
  rw [machZehnder_evolvePure_dualRail]
  apply PureState.ext
  simp only [dualRail_vec]
  apply dualRailVec_congr
  · linear_combination c0 * mz_half_cos φ + c1 * mz_half_sin φ
  · linear_combination c0 * mz_half_sin φ + c1 * mz_half_cos φ

end AxQM
