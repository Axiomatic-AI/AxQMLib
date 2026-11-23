/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch9.Theorem9_3

/-!
# Nielsen & Chuang, Exercise 9.8 (Convexity of the trace distance)

Show trace distance convex in first input over state mixtures.

Convexity in the first input is the special case of the **joint convexity** `(9.50)`,
`D(∑ᵢ pᵢ ρᵢ, ∑ᵢ pᵢ σᵢ) ≤ ∑ᵢ pᵢ D(ρᵢ, σᵢ)`, obtained by taking the second family constant,
`σᵢ = σ`. Then `∑ᵢ pᵢ σ = σ` (the weights sum to one), which turns the joint bound into
`(9.51)`. Joint convexity is in turn the `q = p` case of strong convexity (Theorem 9.3), so
Exercise 9.8 is a two-step corollary of the already-formalized `(9.46)`.

## The physics form

The mixture `∑ᵢ pᵢ ρᵢ` is `AxQM.State.mix` (`AxQM/Postulates/API/Mixture.lean`); `D` on states is
`State.traceDistance`.

The reduction `∑ᵢ pᵢ σ = σ` is the lemma `State.mix_const`
(`AxQM/Postulates/API/Mixture.lean`, the mixture of a constant family is that state); the symmetric
"second input" claim uses symmetry of the trace distance (`State.traceDistance_comm`).

## Main statements

* `State.traceDistance_mix_left_convex` — **Exercise 9.8, `(9.51)`**: convexity in the first
  input, `D(∑ᵢ pᵢ ρᵢ, σ) ≤ ∑ᵢ pᵢ D(ρᵢ, σ)`. The joint-convexity bound
  (`State.traceDistance_mix_jointly_convex`) at the constant second family `fun _ => σ`,
  with the mixture collapsed by `State.mix_const`.
* `State.traceDistance_mix_right_convex` — the **second-input** convexity N&C notes follows
  "by symmetry", `D(ρ, ∑ᵢ pᵢ σᵢ) ≤ ∑ᵢ pᵢ D(ρ, σᵢ)`, obtained from the first via
  `State.traceDistance_comm`.

## References

Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information*
(10th anniv. ed.). Cambridge University Press. Exercise 9.8, §9.2.1 (p. 408).

N&C Exercise 9.8, p. 408.
-/

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.8 (Convexity of the trace distance, `(9.51)`).** The trace
distance is convex in its first input: for a probability distribution `p : ι → ℝ` over a finite
index set, a family of states `ρ : ι → State S`, and a fixed state `σ`,
`D(∑ᵢ pᵢ ρᵢ, σ) ≤ ∑ᵢ pᵢ D(ρᵢ, σ)`, i.e.
`(State.mix p hp hpsum ρ).traceDistance σ ≤ ∑ᵢ pᵢ (ρᵢ).traceDistance σ`.

Proof: the special case of joint convexity `(9.50)`
(`State.traceDistance_mix_jointly_convex`) with the second family constant, `σᵢ = σ`; the
mixture `State.mix p hp hpsum (fun _ => σ)` collapses to `σ` by `State.mix_const`. -/
theorem State.traceDistance_mix_left_convex {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (ρ : ι → State S) (σ : State S) :
    (State.mix p hp hpsum ρ).traceDistance σ ≤ ∑ i, p i * (ρ i).traceDistance σ := by
  have h := State.traceDistance_mix_jointly_convex p hp hpsum ρ (fun _ => σ)
  rwa [State.mix_const p hp hpsum σ] at h

/-- Convexity of the trace distance in its **second input**, the claim N&C notes "by symmetry
convexity in the second entry follows from convexity in the first":
`D(ρ, ∑ᵢ pᵢ σᵢ) ≤ ∑ᵢ pᵢ D(ρ, σᵢ)`.

Proof: symmetry of the trace distance (`State.traceDistance_comm`) reduces this to
`State.traceDistance_mix_left_convex` with the roles of the two inputs exchanged. -/
theorem State.traceDistance_mix_right_convex {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (ρ : State S) (σ : ι → State S) :
    ρ.traceDistance (State.mix p hp hpsum σ) ≤ ∑ i, p i * ρ.traceDistance (σ i) := by
  simp only [State.traceDistance_comm ρ]
  exact State.traceDistance_mix_left_convex p hp hpsum σ ρ

end AxQM
