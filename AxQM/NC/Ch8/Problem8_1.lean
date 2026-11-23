/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AmplitudeDampingMasterEquation

/-!
# Nielsen & Chuang, Problem 8.1 (Lindblad form to quantum operation)

Solve the Lindblad differential equation and express ρ(0)→ρ(t) as ΣE_k(t)ρ(0)E_k†(t).

This is the single-qubit spontaneous-emission (amplitude-damping) master equation of §8.4.1,
in the interaction picture. Solving it entrywise gives the amplitude-damped density matrix, and
the map `ρ(0) ↦ ρ(t)` is exactly the amplitude-damping channel with parameter `γ = 1 - e^{-λt}`
and operation elements `E₀(t) = diag(1, √(1-γ))`, `E₁(t) = √γ |0⟩⟨1|` (N&C eqs. 8.145–8.146).

Its formal content is a computation on `2 × 2` complex matrices — the ODE (8.188), its solution
`ρ(t)`, and the operator-sum identity. The map `ρ(0) ↦ ρ(t)` is *not* unitary, so it is not an
instance of the closed-system `Evolution`; it is an operator-sum map `E(ρ) = Σᵢ Eᵢ ρ Eᵢ†` with
`Σᵢ Eᵢ†Eᵢ ≤ I` (N&C Theorem 8.1).

The formalisation is in `AxQM/Concrete/AmplitudeDampingMasterEquation.lean`:

* `AxQM.Concrete.sigmaMinus` / `sigmaPlus` — the lowering / raising operators
  `σ₋ = |0⟩⟨1|`, `σ₊ = |1⟩⟨0|`, with `sigmaPlus_eq_conjTranspose_sigmaMinus` (`σ₊ = σ₋†`).
* `AxQM.Concrete.lindbladGenerator` — the right-hand side of (8.188), with closed form
  `lindbladGenerator_eq`.
* `AxQM.Concrete.dampedRho` — the solution `ρ(t)`, with `dampedRho_zero` the initial
  condition `ρ(0) = ρ₀`.
* `AxQM.Concrete.dampedRho_hasDerivAt` — `ρ(t)` **solves** the master equation
  (`d/dt ρ(t) = lindbladGenerator λ (ρ(t))`, entrywise): the "solve the ODE" half.
* `AxQM.Concrete.krausAmplitudeDampingZero` / `krausAmplitudeDampingOne` — the operation
  elements `E₀(t)`, `E₁(t)`.
* `AxQM.Concrete.dampedRho_eq_kraus` — the operator-sum representation
  `ρ(t) = E₀(t) ρ(0) E₀(t)† + E₁(t) ρ(0) E₁(t)†`: the "express as Σₖ Eₖ ρ Eₖ†" half.
* `AxQM.Concrete.krausAmplitudeDamping_completeness` — the completeness relation
  `E₀† E₀ + E₁† E₁ = I`,
  certifying the map is a genuine (trace-preserving) quantum operation.
-/
