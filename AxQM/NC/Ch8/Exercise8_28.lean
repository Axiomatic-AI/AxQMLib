/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PhaseDampingCNOTModel

/-!
# Nielsen & Chuang, Exercise 8.28 (a single CNOT with a mixed environment models phase damping)

*(N&C p. 386.)*

Show a single CNOT with mixed environment state models phase damping.

## The construction and the result

The gate is the **controlled-flip** `U = P₀ ⊗ I + P₁ ⊗ X` (N&C eq. 8.16) — the CNOT with the system
controlling a bit-flip of the environment, `AxQM.Concrete.controlledFlip` (Exercise 8.4).
Where a *pure* `|0⟩` environment yields the completely dephasing channel (Exercise 8.4), a **mixed**
environment produces phase damping. Prepare the environment in the `±`-basis mixture

`σ_p = (1-p) |+⟩⟨+| + p |-⟩⟨-|`,

a density operator (unit trace), apply `U`, and trace out the environment. Since the CNOT is
invisible on a `|+⟩` environment and kicks back a Pauli `Z` on a `|-⟩` one
(`controlledFlip_conj_plusProj` / `controlledFlip_conj_minusProj`, Exercise 8.28 part 1), the
induced channel on the system is the **phase-flip channel**

`E_p(ρ) = tr_env(U (ρ ⊗ σ_p) U†) = (1-p) ρ + p Z ρ Z`,

which is exactly the phase-flip = phase-damping channel of N&C §8.3.5. In operator-sum form its
elements are the recombined phase-damping operation elements `Ẽ₀ = √(1-p) I`, `Ẽ₁ = √p Z` of N&C
eqs. 8.129–8.130; specializing the mixture weight to `p = 1 - α(λ)` with the phase-flip "no-error"
probability `α(λ) = (1 + √(1-λ))/2 = phaseFlipProb λ` recovers the library's phase-damping operation
elements `phaseDampKrausTilde b λ` verbatim. So a single CNOT with a mixed environment models phase
damping, and — as the exercise stresses — **the amount of damping is fixed by the mixture
probability** (the weight `p = 1 - α(λ)` of the `|-⟩` component that triggers the phase flip).

## The formalisation

The formal content of Exercise 8.28 is pure linear algebra about operators on a two-qubit space
(`LinearMap`, `TensorProduct.map`, `OrthonormalBasis`, the abstract partial trace). Compare the
phase-damping circuit (Exercise 8.26) and the controlled-flip gate it uses (Exercises 8.4 / 8.27).

The formalisation is in `AxQM/Concrete/PhaseDampingCNOTModel.lean`, which uses the gate analysis of
`AxQM/Concrete/ControlledFlipConjugation.lean` (Exercise 8.28 part 1):

* `AxQM.Concrete.phaseDampEnv` — the **mixed environment state**
  `σ_p = (1-p) |+⟩⟨+| + p |-⟩⟨-|`, a valid density operator (`trace_phaseDampEnv`: `tr σ_p = 1`).
* `AxQM.Concrete.phaseDampCNOTChannel` — the **single-CNOT model**
  `E_p(ρ) = tr_env(U (ρ ⊗ σ_p) U†)`.
* `AxQM.Concrete.phaseFlipChannel` — the **phase-flip channel** `(1-p) ρ + p Z ρ Z`.
* `AxQM.Concrete.phaseDampCNOTChannel_eq_phaseFlipChannel` — **the exercise**: the
  single-CNOT model with mixed environment `σ_p` equals the phase-flip channel `(1-p) ρ + p Z ρ Z`.
* `AxQM.Concrete.phaseFlipChannel_eq_operatorSum` — its **operator-sum form** with the
  recombined phase-damping operation elements `Ẽ₀ = √(1-p) I`, `Ẽ₁ = √p Z` (N&C eqs. 8.129–8.130).
* `AxQM.Concrete.phaseDampCNOTChannel_eq_phaseDampKrausTilde` — **"amount of damping set by
  the mixture probability"**: with `p = 1 - phaseFlipProb λ`, the model equals the library's
  phase-damping operation elements `phaseDampKrausTilde b λ`, so it models phase damping of `λ`.
* Supporting trace facts `trace_qubitProj`, `trace_qubitFlip`, `trace_qubitPlusProj`,
  `trace_qubitMinusProj` (each `|i⟩⟨i|` / `|±⟩⟨±|` projector has unit trace, `X` is traceless).

See the module docstring of `AxQM/Concrete/PhaseDampingCNOTModel.lean` for the full argument.
-/
