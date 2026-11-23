/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_7

/-!
# Nielsen & Chuang, Exercise 9.20 (Concavity of the fidelity)

Prove fidelity concave in first entry.

Mixing a family of states `{ρᵢ}` in the first argument of the fidelity can only *raise* the
fidelity above the `pᵢ`-weighted average of the componentwise fidelities `F(ρᵢ, σ)`: the mixed
state `∑ᵢ pᵢ ρᵢ` is at least as close to `σ` as the states `ρᵢ` are on average. This is one of the
two one-sided concavity statements N&C record as immediate consequences of the strong concavity of
the fidelity (Theorem 9.7).

## Statement

The first-argument mixture is `AxQM.State.mix` (`∑ᵢ pᵢ ρᵢ`, N&C
mixtures) and the distance is the **fidelity** `AxQM.State.fidelity` (`ρ.fidelity σ =
F(ρ, σ)`, N&C `(9.53)`); the weights `pᵢ` live entirely on the classical probability side.
Compare the sibling Theorem 9.7.

## Proof and design

Exercise 9.20 is the **first-argument specialization** of the strong concavity of the fidelity
(Theorem 9.7, `State.sum_sqrt_mul_fidelity_le_fidelity_mix`,
`∑ᵢ √(pᵢ qᵢ) F(ρᵢ, σᵢ) ≤ F(∑ᵢ pᵢ ρᵢ, ∑ᵢ qᵢ σᵢ)`). Setting the *two* distributions equal
(`q := p`) and the second family constant (`σᵢ := σ`):

* the mixed second argument collapses, `∑ᵢ pᵢ σ = σ` (`State.mix_const`, since `∑ᵢ pᵢ = 1`);
* each weight simplifies, `√(pᵢ pᵢ) = pᵢ` for `pᵢ ≥ 0` (`Real.sqrt_mul_self`),

turning Theorem 9.7 verbatim into `∑ᵢ pᵢ F(ρᵢ, σ) ≤ F(∑ᵢ pᵢ ρᵢ, σ)`, exactly N&C `(9.96)`. This
matches the Theorem 9.7 design note, which records that both the joint concavity (Exercise 9.19)
and this concavity in the first argument follow from that master inequality by specialization; no
separate operator-level work is needed here.

The mirror statement — concavity in the *second* entry — follows by the symmetry of the fidelity
(`State.fidelity_comm`); N&C states it only as a remark, so it is not a separately numbered
statement and is left to the symmetry lemma rather than restated here.

N&C Exercise 9.20, p. 415.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Concavity of the fidelity in the first entry** (Nielsen & Chuang, Exercise 9.20, `(9.96)`):
for a probability distribution `p` over a finite index set, a family of states `ρ` and a fixed
state `σ`,
`∑ᵢ pᵢ F(ρᵢ, σ) ≤ F(∑ᵢ pᵢ ρᵢ, σ)`.

Mixing in the first argument never decreases the fidelity below the `pᵢ`-weighted average of the
componentwise fidelities. The proof specializes the strong concavity of the fidelity
(`State.sum_sqrt_mul_fidelity_le_fidelity_mix`, Theorem 9.7) to equal distributions `q := p` and a
constant second family `σᵢ := σ`: the second mixture collapses by `State.mix_const` and each
weight `√(pᵢ pᵢ)` simplifies to `pᵢ` by `Real.sqrt_mul_self`. -/
theorem State.fidelity_concaveLeft {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (ρ : ι → State S) (σ : State S) :
    ∑ i, p i * (ρ i).fidelity σ ≤ (State.mix p hp hps ρ).fidelity σ := by
  simpa only [Real.sqrt_mul_self, hp, State.mix_const] using
    State.sum_sqrt_mul_fidelity_le_fidelity_mix p p hp hp hps hps ρ (fun _ => σ)

end AxQM
