/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.NMRBellPrep

/-!
# Nielsen & Chuang, Exercise 7.48 (NMR Bell-state preparation)

*(N&C §7.7.3, p. 338.)*

Verify the bottom-left Fig 7.19 circuit creates the Bell state (|00⟩−|11⟩)/√2.

## The circuit

Reading Figure 7.19 (bottom-left) left to right, the two-spin NMR pulse sequence is

* an `R_x(π/2)` (`90°` `x̂`-rotation) on **each** spin,
* one period of the `Z₁Z₂`-coupled free evolution `exp(-i(π/4) Z₁Z₂)` — the *identical* physical
  box already used for the controlled-`Z`/CNOT circuit of Exercise 7.41 (`c·t = π/4`),
* an `R_y(-π/2)` (`90°` `ŷ`-rotation) on the **second** spin only,

i.e. `nmrBellCircuit c t = (1 ⊗ R_y(-π/2)) · exp(-i(π/4) Z₁Z₂) · (R_x(π/2) ⊗ R_x(π/2))`, defined
as an `Evolution (qubit ⊗ qubit)` in `AxQM/Postulates/API/NMRBellPrep.lean`.

## The verification

Pushing `|00⟩` through the four stages gives, in `AxQM/Postulates/API/NMRBellPrep.lean`, the exact
amplitude identity `nmrBellCircuit_op_qubitBasisZeroZero`:

`nmrBellCircuit c t |00⟩ = e^{-iπ/4} • (bellState 1 0).vec = e^{-iπ/4} (|00⟩ − |11⟩)/√2`,

the advertised Bell state `|β₁₀⟩` up to the (unobservable) global phase `e^{-iπ/4}`. Concretely:
`R_x(π/2)` makes `(|0⟩ − i|1⟩)/√2` on each spin, the coupling box multiplies the four branches by
`(1 ∓ i)/√2` (`+` on `|01⟩,|10⟩`, `−` on `|00⟩,|11⟩`), and `R_y(-π/2)` on the second spin interferes
them — the `|01⟩`/`|10⟩` branches cancel, `|00⟩` and `−|11⟩` survive.

## The formalisation

`nmrBellCircuit_evolvePure_toState` (below) is the exercise's physical claim, stated for
states: the state the circuit prepares from `|00⟩` **is**
the Bell state `|β₁₀⟩`,

`((nmrBellCircuit c t).evolvePure |00⟩).toState = (bellState 1 0).toState`,

i.e. the two density operators coincide. This is exactly "creates the Bell state" in the physically
meaningful sense — the global phase `e^{-iπ/4}` of the amplitude identity washes out of the density
operator (`PureState.toState_eq_of_vec_eq_smul`, since `‖e^{-iπ/4}‖ = 1`), which is why N&C can call
the output *the* Bell state without qualification.

The exact phase-resolved amplitude identity `nmrBellCircuit_op_qubitBasisZeroZero`, together with
the verified per-gate actions it is assembled from (`rotXGate_piDivTwo_op_qubitBasisZero`,
`rotYGate_negPiDivTwo_op_qubitBasis{Zero,One}`, `couplingBox_op_qubitBasis`), is in
`AxQM/Postulates/API/NMRBellPrep.lean` (in terms of `.op` and `.vec`); the theorem above
follows from it.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **Exercise 7.48: the bottom-left Figure 7.19 NMR circuit creates the Bell state `|β₁₀⟩`.**
Applied to the computational input `|00⟩`, the circuit `nmrBellCircuit c t` (an `R_x(π/2)` on each
spin, one `Z₁Z₂`-coupling period with `c·t = π/4`, then `R_y(-π/2)` on the second spin) prepares a
state whose density operator equals that of the Bell state `|β₁₀⟩ = (|00⟩ − |11⟩)/√2`:
`((nmrBellCircuit c t).evolvePure |00⟩).toState = (bellState 1 0).toState`.

The circuit's action on the amplitude is `|00⟩ ↦ e^{-iπ/4}(|00⟩ − |11⟩)/√2`
(`nmrBellCircuit_op_qubitBasisZeroZero`); the global phase `e^{-iπ/4}` (of unit modulus) is
invisible to the density operator, so as physical states the output **is** `|β₁₀⟩` — verifying the
exercise's claim. -/
theorem nmrBellCircuit_evolvePure_toState (c t : ℝ) (h : c * t = Real.pi / 4) :
    ((nmrBellCircuit c t).evolvePure ((qubitBasis 0).tmul (qubitBasis 0))).toState
      = (bellState 1 0).toState := by
  apply PureState.toState_eq_of_vec_eq_smul
    (c := Complex.exp (-(Complex.I * ((Real.pi : ℂ) / 4))))
  · -- the global phase `e^{-iπ/4}` has unit modulus
    simp [Complex.norm_exp]
  · -- the amplitude identity, from `AxQM/Postulates/API/NMRBellPrep.lean`
    rw [Evolution.evolvePure_vec]
    exact nmrBellCircuit_op_qubitBasisZeroZero c t h

end AxQM
