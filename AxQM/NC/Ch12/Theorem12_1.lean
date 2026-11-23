/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Problem12_1

/-!
# N&C Theorem 12.1 — the Holevo bound

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Theorem 12.1, p. 531.

Alice prepares a state `ρₓ` with probability `pₓ` (random variable `X`, ranging over a finite index
`κ`); Bob performs a POVM measurement `m` on that state and obtains an outcome `Y` (ranging over the
`r` outcomes `Fin r`). The **Holevo bound** (eq. (12.6)) states that, for *any* such measurement,

`H(X : Y) ≤ S(ρ) − ∑ₓ pₓ S(ρₓ)`,    where `ρ = ∑ₓ pₓ ρₓ`.

`holevo_bound` is this statement, verbatim: the left-hand side is the classical mutual information
`Real.mutualInfo` of the joint distribution `p(x, y) = pₓ · Tr(Eᵧ ρₓ) = pₓ · m.bornProb (ρₓ) y` of
Alice's preparation `X` and Bob's outcome `Y`; the right-hand side is written out explicitly as
`S(∑ₓ pₓ ρₓ) − ∑ₓ pₓ S(ρₓ)` — the entropy of the average state `State.mix` minus the average of the
component entropies (the Holevo χ quantity `χ`, N&C eq. (12.6), spelled out).

## Statement shape and fidelity

The bound is stated at N&C's full generality: an arbitrary system `Q`, an arbitrary finite ensemble
`{pₓ, ρₓ}` (index `κ`), and an arbitrary finite-outcome measurement `m : Measurement (Fin r) Q`
(`r ≥ 1` via `NeZero`). Bob's "POVM `{Eᵧ}`" is presented as a
`Measurement (Fin r) Q` rather than a bare POVM: every POVM is `m.toPOVM` for some such
measurement, so no generality is lost and no hypothesis is added — the common weakening
(fixing a dimension, adding a
faithfulness/full-rank hypothesis) is avoided. The right-hand side is deliberately unfolded to the
explicit entropy difference `S(ρ) − ∑ₓ pₓ S(ρₓ)` matching the textbook display, rather than
`State.holevoChi`, so the statement reads as N&C's Theorem 12.1 itself.

## Proof route and reuse

N&C's own proof of Theorem 12.1 introduces a tripartite system `P ⊗ Q ⊗ M` and bounds the mutual
information by the quantum data-processing inequality. The direct relative-entropy / data-processing
argument is **not used** in this library: the relative-entropy data-processing inequalities of
`ToMathlib/` all require `IsStrictlyPositive`, but the
Stinespring-dilated state is never full rank, so they do not compose into a channel DPI without a
regularization/continuity development the library lacks. The proof instead follows N&C's
*faithfulness-free* mutual-information / apparatus argument, whose χ-monotonicity engine is
developed in **Problem 12.1** (`AxQM/NC/Ch12/Problem12_1.lean`): Part (1) χ
decreases under discarding a subsystem, Part (2) χ decreases under a quantum operation, Part (3)
the measurement apparatus has `χ_M = H(X : Y)`. Their composition is `holevoBound_of_chi_monotone`
(`H(X : Y) ≤ χ`).

Theorem 12.1 and Problem 12.1 prove the *same* inequality, so `holevo_bound` uses
`holevoBound_of_chi_monotone` from `AxQM/NC/Ch12/Problem12_1.lean` rather than re-proving it. The
proof is one step: unfold the explicit right-hand side to `State.holevoChi`
(`State.holevoChi_def`, definitional), then apply `holevoBound_of_chi_monotone`.
-/

noncomputable section

namespace AxQM

/-- **N&C Theorem 12.1 (the Holevo bound)** (eq. (12.6)). Alice prepares `ρₓ` with probability `pₓ`
(random variable `X` over the finite index `κ`); Bob performs the POVM measurement `m` and obtains
outcome `Y` (over `Fin r`). Then the classical mutual information of the joint distribution
`p(x, y) = pₓ · m.bornProb (ρₓ) y` of `X` and `Y` is bounded by the Holevo χ quantity of Alice's
ensemble:

`H(X : Y) ≤ S(ρ) − ∑ₓ pₓ S(ρₓ)`,    where `ρ = ∑ₓ pₓ ρₓ`,

the right-hand side being the entropy of the average state minus the average of the component
entropies. Holds for any measurement Bob may perform, with no restriction on the ensemble or the
dimension.

The right-hand side is `State.holevoChi p hp hsum ρ` unfolded via `State.holevoChi_def`; the
bound is then the χ-monotonicity result `holevoBound_of_chi_monotone` (N&C Problem 12.1's
alternate proof, shared with this theorem — see the module docstring for the route). -/
theorem holevo_bound {Q : QSystem} {r : ℕ} [NeZero r] {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (ρ : κ → State Q)
    (m : Measurement (Fin r) Q) :
    Real.mutualInfo (fun xy : κ × Fin r => p xy.1 * m.bornProb (ρ xy.1) xy.2)
      ≤ (State.mix p hp hsum ρ).vonNeumannEntropy - ∑ x, p x * (ρ x).vonNeumannEntropy := by
  rw [← State.holevoChi_def p hp hsum ρ]
  exact holevoBound_of_chi_monotone p hp hsum ρ m

end AxQM
