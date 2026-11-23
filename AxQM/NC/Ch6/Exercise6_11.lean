/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SubsetUniformSuperposition
import AxQM.Postulates.API.ContinuousSearchHamiltonian

/-!
# Nielsen & Chuang, Exercise 6.11 (multiple-solution continuous quantum search)

*(N&C p. 261.)*

Guess a Hamiltonian solving the continuous-time search problem for M solutions.

The single-solution continuous-time search of §6.2 evolves the uniform superposition
`|ψ⟩ = N⁻¹ᐟ² ∑_k |k⟩` under `H = |x⟩⟨x| + |ψ⟩⟨ψ|` (N&C eq. 6.18) and, at time `t = π√N/2`, rotates
`|ψ⟩` exactly onto the unique solution `|x⟩` (eqs. 6.20–6.24). The overlap driving the rotation is
`α = ⟨x, ψ⟩ = 1/√N`.

**The guess.** For an `M`-solution problem, replace the single target `|x⟩` by the uniform
superposition over *all* `M` solutions,

`|β⟩ = M⁻¹ᐟ² ∑_{x ∈ T} |x⟩`   (`T` = the set of `M` solutions),

and take exactly the same two-projector Hamiltonian

`H = |β⟩⟨β| + |ψ⟩⟨ψ|`.

The overlap is now `α = ⟨β, ψ⟩ = √(M/N)` (real, positive), so the §6.2 analysis goes through
verbatim: `|ψ⟩` rotates onto `|β⟩` at time `t = π/(2α) = (π/2)√(N/M)`, and because `|β⟩` is
supported entirely on the solutions, a computational-basis measurement of the rotated state returns
one of the `M` solutions with **probability one**. (For `M = 1` this is exactly the single-solution
result, `α = 1/√N`, `t = π√N/2`.)

## The formalisation

The `M`-solution search is the single-solution analysis with `|x⟩ → |β⟩`, so it is *proved by
instantiating* the abstract two-state continuous-search engine of
`AxQM/Postulates/API/ContinuousSearchHamiltonian.lean` (`PureState.searchHamiltonian`,
`searchHamiltonian_reaches_target`, N&C eqs. 6.18–6.24), with `a := |β⟩` the subset uniform
superposition and `α := √(M/N)` the overlap (both from
`AxQM/Postulates/API/SubsetUniformSuperposition.lean`).

* `searchHamiltonianMSolution T hT` — the guessed Hamiltonian `H = |β⟩⟨β| + |ψ⟩⟨ψ|` as an
  `Observable`.
* `searchHamiltonianMSolution_reaches_solution` — evolving `|ψ⟩` under `H` for `t = (π/2)√(N/M)`
  produces the solution state `|β⟩` (up to a global phase): the state coincides with `|β⟩`.
* `searchHamiltonianMSolution_measure_yields_solution` — measuring the rotated state in the
  computational basis returns a solution (an index in `T`) with total probability `1`.

-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {d : ℕ}

/-- **The guessed multiple-solution search Hamiltonian** `H = |β⟩⟨β| + |ψ⟩⟨ψ|` (Nielsen & Chuang,
Exercise 6.11), for a search space `qudit d` (`N = d` items) with solution set `T` (`M = |T|`
solutions): `|β⟩ = subsetUniformSuperposition T hT` is the uniform superposition over the solutions
and `|ψ⟩ = uniformSuperposition d` the uniform superposition over all `N` items. It is the two-state
continuous-search Hamiltonian of §6.2 (eq. 6.18) with the single target `|x⟩` replaced by `|β⟩`. -/
def searchHamiltonianMSolution [NeZero d] (T : Finset (Fin d)) (hT : T.Nonempty) :
    Observable (qudit d) :=
  (subsetUniformSuperposition T hT).searchHamiltonian (uniformSuperposition d)

/-- **The multiple-solution search Hamiltonian rotates `|ψ⟩` onto the solutions.** Evolving the
uniform superposition `|ψ⟩` under `H = |β⟩⟨β| + |ψ⟩⟨ψ|` for time `t = (π/2)√(N/M)` produces the
solution state `|β⟩` (up to a global phase): the density operators coincide,
`(exp(-iHt)|ψ⟩ as a state) = |β⟩`. This is Nielsen & Chuang's continuous-time search (eqs.
6.23–6.24) generalised to `M` solutions — the overlap is `α = ⟨β, ψ⟩ = √(M/N)`, so the observation
time is `t = π/(2α) = (π/2)√(N/M) = O(√(N/M))`, matching the `Ω(√(N/M))` search lower bound
(Exercise 6.17). Proved by instantiating `PureState.searchHamiltonian_reaches_target` (the abstract
two-state engine) at `a := |β⟩`, `α := √(M/N)`. -/
theorem searchHamiltonianMSolution_reaches_solution [NeZero d]
    (T : Finset (Fin d)) (hT : T.Nonempty) :
    (((searchHamiltonianMSolution T hT).propagator 1 0
        (Real.pi / 2 * Real.sqrt ((d : ℝ) / T.card))).evolvePure (uniformSuperposition d)).toState
      = (subsetUniformSuperposition T hT).toState := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hMpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hα : 0 < Real.sqrt ((T.card : ℝ) / d) := Real.sqrt_pos.mpr (div_pos hMpos hd)
  have hoverlap : inner ℂ (subsetUniformSuperposition T hT).vec (uniformSuperposition d).vec
      = (Real.sqrt ((T.card : ℝ) / d) : ℂ) :=
    subsetUniformSuperposition_inner_uniformSuperposition T hT
  have hsM : Real.sqrt (T.card : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hMpos
  have hsd : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hd
  have htime : Real.pi / 2 * Real.sqrt ((d : ℝ) / T.card)
      = Real.pi / (2 * Real.sqrt ((T.card : ℝ) / d)) := by
    rw [Real.sqrt_div (le_of_lt hd), Real.sqrt_div (le_of_lt hMpos)]
    field_simp
  rw [htime]
  exact (subsetUniformSuperposition T hT).searchHamiltonian_reaches_target
    (uniformSuperposition d) hα hoverlap

/-- **Measuring the rotated state returns a solution with probability one.** After evolving `|ψ⟩`
under `H = |β⟩⟨β| + |ψ⟩⟨ψ|` for `t = (π/2)√(N/M)`, a computational-basis measurement returns one of
the `M` solutions (an index in `T`) with total probability `1`: the multiple-solution continuous
search *solves* the search problem. Because the rotated state is `|β⟩` (up to a global phase, which
is invisible to the Born rule; `searchHamiltonianMSolution_reaches_solution`) and `|β⟩` is supported
on the solutions with `p(x) = M⁻¹` for `x ∈ T`
(`bornProb_quditMeasurement_subsetUniformSuperposition`), the probabilities of the `M` solutions sum
to `M · M⁻¹ = 1`. -/
theorem searchHamiltonianMSolution_measure_yields_solution [NeZero d]
    (T : Finset (Fin d)) (hT : T.Nonempty) :
    ∑ x ∈ T, (quditMeasurement d).bornProb
        ((((searchHamiltonianMSolution T hT).propagator 1 0
            (Real.pi / 2 * Real.sqrt ((d : ℝ) / T.card))).evolvePure
          (uniformSuperposition d)).toState) x = 1 := by
  rw [searchHamiltonianMSolution_reaches_solution,
    Finset.sum_congr rfl fun x hx =>
      (bornProb_quditMeasurement_subsetUniformSuperposition T hT x).trans (ite_eq_left hx),
    Finset.sum_const, nsmul_eq_mul,
    mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hT).ne')]

end AxQM
