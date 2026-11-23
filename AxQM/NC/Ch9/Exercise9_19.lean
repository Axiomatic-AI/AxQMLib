/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_7

/-!
# Nielsen & Chuang, Exercise 9.19 (Joint concavity of the fidelity)

Prove fidelity jointly concave.

Mixing *both* arguments with the **same** probability distribution `p` never lowers the fidelity
below the `pᵢ`-weighted average of the componentwise fidelities: the two mixtures are at least as
close (fidelity-wise) as the average closeness of their components. This is the discrete Jensen
form of concavity that N&C states in `(9.95)`.

## Statement and proof

N&C's hint is to *use the strong concavity of the fidelity* (Theorem 9.7, `(9.92)`):
`∑ᵢ √(pᵢ qᵢ) F(ρᵢ, σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ qᵢ σᵢ)`. Joint concavity is precisely its diagonal
specialization `q = p`: with equal weights each `√(pᵢ pᵢ) = pᵢ` (as `pᵢ ≥ 0`, `Real.sqrt_mul_self`),
so the `√(pᵢ qᵢ)`-weighted average collapses to the `pᵢ`-weighted average `∑ᵢ pᵢ F(ρᵢ, σᵢ)`.

The statement is

* `AxQM.State.sum_mul_fidelity_le_fidelity_mix` —
  `∑ᵢ pᵢ F(ρᵢ, σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ pᵢ σᵢ)` for a probability distribution `p` and families of
  states `ρ, σ`.

The two
mixtures `State.mix p hp hps ρ` and `State.mix p hp hps σ` reuse the *same* weight data `p`/`hp`/
`hps`, which is the formal content of "the same distribution" in N&C `(9.95)`.

N&C Exercise 9.19, p. 415.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Joint concavity of the fidelity** (Nielsen & Chuang, Exercise 9.19, `(9.95)`): for a
probability distribution `p` over a finite index set and families of states `ρ, σ`,
`∑ᵢ pᵢ F(ρᵢ, σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ pᵢ σᵢ)`.

Mixing both arguments with the *same* distribution `p` never decreases the fidelity below the
`pᵢ`-weighted average of the componentwise fidelities. This is the diagonal `q = p` specialization
of the strong concavity `State.sum_sqrt_mul_fidelity_le_fidelity_mix` (Theorem 9.7): each weight
`√(pᵢ pᵢ) = pᵢ` since `pᵢ ≥ 0` (`Real.sqrt_mul_self`), so the strong-concavity average reduces to
the joint-concavity average. -/
theorem State.sum_mul_fidelity_le_fidelity_mix {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1) (ρ σ : ι → State S) :
    ∑ i, p i * (ρ i).fidelity (σ i)
      ≤ (State.mix p hp hps ρ).fidelity (State.mix p hp hps σ) := by
  calc ∑ i, p i * (ρ i).fidelity (σ i)
      = ∑ i, Real.sqrt (p i * p i) * (ρ i).fidelity (σ i) :=
        Finset.sum_congr rfl fun i _ => by rw [Real.sqrt_mul_self (hp i)]
    _ ≤ (State.mix p hp hps ρ).fidelity (State.mix p hp hps σ) :=
        State.sum_sqrt_mul_fidelity_le_fidelity_mix p p hp hp hps hps ρ σ

end AxQM
