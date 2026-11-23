/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PhaseDampingCircuit

/-!
# Nielsen & Chuang, Exercise 8.26 (circuit model for phase damping)

*(N&C p. 385, Figure 8.15.)*

Show the Figure 8.15 circuit models phase damping for appropriate θ.

## The circuit and the result

Figure 8.15 is a two-qubit circuit: the input system qubit `ρ_in` (control) and an ancilla
`|0⟩` modelling the environment (target). A **controlled-`Rᵧ(θ)`** gate applies the y-rotation
`Rᵧ(θ)` to the ancilla when the system is `|1⟩`; the ancilla is then traced out to give `ρ_out`.
The interaction is `U = P₀ ⊗ I + P₁ ⊗ Rᵧ(θ)`, and `Eₖ = ⟨k| U |0⟩` gives the operation elements

`E₀ = diag(1, cos(θ/2))`,   `E₁ = diag(0, sin(θ/2))`.

Choosing `θ` with `sin²(θ/2) = λ` (i.e. `θ = 2 arcsin √λ`, realizing any `λ ∈ [0,1]`), and using
`cos(θ/2) = √(1-λ)`, `sin(θ/2) = √λ` on `0 ≤ θ ≤ π`, these are exactly the phase-damping operation
elements `E₀ = diag(1,√(1-λ))`, `E₁ = diag(0,√λ)` of N&C eqs. (8.127)–(8.128). So the circuit models
the phase-damping channel for appropriate `θ` — the content of the exercise. Unlike amplitude
damping (Fig. 8.13), the phase-damping circuit needs **no** subsequent CNOT: no energy is exchanged.

## The formalisation

The formal content of Exercise 8.26 is pure linear algebra about operators on a two-qubit space
(`LinearMap`, `TensorProduct`, `OrthonormalBasis`, the abstract partial trace and operator-sum
infrastructure). Compare the operator-sum channel of Exercise 8.4
(`AxQM/Concrete/ControlledFlipOperatorSum.lean`) and Exercise 8.22.

The formalisation is in `AxQM/Concrete/PhaseDampingCircuit.lean`:

* `phaseDampingKrausZero`, `phaseDampingKrausOne`, `phaseDampingChannel` — the phase-damping
  operation elements `E₀ = diag(1,√(1-λ))`, `E₁ = diag(0,√λ)` (N&C eqs. 8.127–8.128) and the channel
  `E(ρ) = E₀ ρ E₀† + E₁ ρ E₁†` they define.
* `phaseDampingCircuitDilation`, `phaseDampingCircuitOperation` — the circuit's dilation
  `V = U(· ⊗ |0⟩)` and induced operation `E_θ(ρ) = tr_env(V ρ V†)`. The controlled-`Rᵧ`
  interaction `U` reuses `ampDampCRy` (built on the `y`-rotation `qubitRotY`, unitary by
  `adjoint_ampDampCRy_comp_self`) of `AxQM/Concrete/AmplitudeDampingCircuit.lean` — phase damping is
  that Fig. 8.13 circuit with the CNOT dropped.
* `krausOp_phaseDampingCircuitDilation_zero`, `…_one` — **the circuit's operation elements**
  `E₀ = diag(1, cos(θ/2))`, `E₁ = diag(0, sin(θ/2))`; the completeness relation
  `sum_adjoint_krausOp_phaseDampingCircuitDilation` gives `E₀† E₀ + E₁† E₁ = I` for every `θ`.
* `krausOp_phaseDampingCircuitDilation_zero_eq`, `…_one_eq` — for `0 ≤ θ ≤ π`, the circuit's `Eₖ`
  are exactly the phase-damping `Eₖ` with `λ = sin²(θ/2)`.
* `phaseDampingCircuitOperation_eq_phaseDampingChannel` — **the exercise**: for `0 ≤ θ ≤ π`, the
  Figure 8.15 circuit operation equals the phase-damping channel with `λ = sin²(θ/2)`.
* `phaseDampingCircuit_models_phaseDamping` — **"θ chosen appropriately"**: for *any* `λ ∈ [0,1]`
  there is `θ ∈ [0,π]` (namely `θ = 2 arcsin √λ`) realizing phase damping of parameter `λ`.

See the module docstring of `AxQM/Concrete/PhaseDampingCircuit.lean` for the full argument.
-/
