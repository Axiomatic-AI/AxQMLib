/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Exercise9_17

/-!
# Nielsen & Chuang, Exercise 9.23 (Ensemble average fidelity equal to one)

Show ensemble average fidelity Fbar=1 iff E(rho_j)=rho_j for all j with p_j>0.

A **quantum source** is here modelled as a finite ensemble `{(pⱼ, ρⱼ)}`: a stream of systems
each prepared in the density operator `ρⱼ` with probability `pⱼ` (`pⱼ ≥ 0`, `∑ⱼ pⱼ = 1`). Its
preservation under a noisy channel `E` is measured by the **ensemble average fidelity**
(N&C `(9.127)`)
`F̄ = ∑ⱼ pⱼ F(ρⱼ, E(ρⱼ))²`,
the probability-weighted mean of the squared fidelities between each emitted state and its image.
Since `0 ≤ F ≤ 1`, each term lies in `[0, 1]` and `0 ≤ F̄ ≤ 1`; `F̄ ≈ 1` means the source is, on
average, well preserved.

## Statement and proof

The statements are

* `AxQM.ensembleAvgFidelity` — the quantity `F̄` of `(9.127)`;
* `AxQM.ensembleAvgFidelity_eq_one_iff` — `F̄ = 1 ↔ ∀ j, pⱼ > 0 → E(ρⱼ) = ρⱼ`.

`F̄ = ∑ⱼ pⱼ aⱼ` is a convex combination — weights `pⱼ ≥ 0` summing to `1` — of the terms
`aⱼ := F(ρⱼ, E(ρⱼ))² ∈ [0, 1]`, so each summand is bounded by its weight, `pⱼ aⱼ ≤ pⱼ` (as
`aⱼ ≤ 1`). A sum dominated termwise equals the sum of the bounds `∑ⱼ pⱼ = 1` exactly when it is
termwise saturated, `pⱼ aⱼ = pⱼ` (`Finset.sum_eq_sum_iff_of_le`); cancelling `pⱼ` where `pⱼ > 0`
(`mul_eq_left₀`) this reads `aⱼ = 1` whenever `pⱼ > 0`. Finally `State.fidelity_sq_eq_one_iff`
(the squared form of N&C `(9.60)`, `F(ρⱼ, E(ρⱼ))² = 1 ↔ ρⱼ = E(ρⱼ)`) turns each such `aⱼ = 1`
into `E(ρⱼ) = ρⱼ`.

The channel `E` enters only through the states `E(ρⱼ)`; the equivalence holds for an *arbitrary*
state map `E : State S → State S`, so `E` is left unconstrained (physically it is a
trace-preserving quantum operation).

N&C Exercise 9.23, p. 419.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **ensemble average fidelity** of a channel `E` with respect to a quantum source — a finite
ensemble of density operators `ρ j` prepared with probabilities `p j` (Nielsen & Chuang `(9.127)`):
`F̄ = ∑ⱼ pⱼ F(ρⱼ, E(ρⱼ))²`, the probability-weighted mean of the squared fidelities between each
emitted state and its image under `E`. The squaring of the fidelity is N&C's convention (it makes
`F̄` relate naturally to the entanglement fidelity). Physically `E` is a trace-preserving quantum
operation, but the definition and its properties make sense for any state map `E`. -/
def ensembleAvgFidelity {ι : Type*} [Fintype ι] (p : ι → ℝ) (ρ : ι → State S)
    (E : State S → State S) : ℝ :=
  ∑ j, p j * (ρ j).fidelity (E (ρ j)) ^ 2

/-- **The ensemble average fidelity is at most `1`**: `F̄ = ∑ⱼ pⱼ F(ρⱼ, E(ρⱼ))² ≤ 1` for any
probability weights (`pⱼ ≥ 0`, `∑ⱼ pⱼ = 1`). It is a convex combination of the squared fidelities
`F(ρⱼ, E(ρⱼ))² ∈ [0, 1]` (`State.fidelity_nonneg` / `State.fidelity_le_one`), so it is bounded by
`∑ⱼ pⱼ = 1`. The upper leg of every ensemble-fidelity reliability squeeze. -/
theorem ensembleAvgFidelity_le_one {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hps : ∑ j, p j = 1) (ρ : ι → State S) (E : State S → State S) :
    ensembleAvgFidelity p ρ E ≤ 1 := by
  rw [ensembleAvgFidelity, ← hps]
  exact Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hp j)
    (pow_le_one₀ (State.fidelity_nonneg _ _) (State.fidelity_le_one _ _))

/-- **Exercise 9.23.** The ensemble average fidelity of a channel `E` over a source
`{(pⱼ, ρⱼ)}` (probabilities `pⱼ ≥ 0`, `∑ⱼ pⱼ = 1`) satisfies `F̄ = 1` if and only if `E` fixes
every emitted state carried with positive probability, `E(ρⱼ) = ρⱼ` for all `j` with `pⱼ > 0`.

`F̄` is a convex combination of the terms `F(ρⱼ, E(ρⱼ))² ∈ [0, 1]`; it attains its maximum `1`
exactly when each positively-weighted term is `1`, and `State.fidelity_sq_eq_one_iff` identifies
that with `E(ρⱼ) = ρⱼ`. -/
theorem ensembleAvgFidelity_eq_one_iff {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hps : ∑ j, p j = 1) (ρ : ι → State S) (E : State S → State S) :
    ensembleAvgFidelity p ρ E = 1 ↔ ∀ j, 0 < p j → E (ρ j) = ρ j := by
  -- Each squared fidelity lies in `[0, 1]`.
  have hFle : ∀ j, (ρ j).fidelity (E (ρ j)) ^ 2 ≤ 1 := fun j =>
    pow_le_one₀ (State.fidelity_nonneg _ _) (State.fidelity_le_one _ _)
  -- `F̄ = ∑ⱼ pⱼaⱼ` is a convex combination with each summand `pⱼaⱼ ≤ pⱼ` (as `aⱼ ≤ 1`); such a
  -- sum equals `∑ⱼ pⱼ = 1` exactly when it is termwise saturated, `pⱼaⱼ = pⱼ`, i.e. `aⱼ = 1`
  -- whenever `pⱼ > 0` (`Finset.sum_eq_sum_iff_of_le`); `State.fidelity_sq_eq_one_iff` then reads
  -- `aⱼ = 1` as `ρⱼ = E(ρⱼ)`.
  rw [ensembleAvgFidelity, ← hps,
    Finset.sum_eq_sum_iff_of_le fun j _ => mul_le_of_le_one_right (hp j) (hFle j)]
  exact ⟨fun h j hpj => ((State.fidelity_sq_eq_one_iff (ρ j) (E (ρ j))).mp
      ((mul_eq_left₀ (ne_of_gt hpj)).mp (h j (Finset.mem_univ j)))).symm,
    fun h j _ => by
      rcases (hp j).eq_or_lt with hpj | hpj
      · rw [← hpj]; ring
      · rw [(State.fidelity_sq_eq_one_iff (ρ j) (E (ρ j))).mpr (h j hpj).symm]; ring⟩

end AxQM
