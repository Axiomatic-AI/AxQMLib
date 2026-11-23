/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SearchOptimality

/-!
# Nielsen & Chuang, Exercise 6.16 (average-case optimality of quantum search)

*(N&C p. 270.)*

Show O(sqrt N) oracle calls still needed when error is averaged uniformly over x (<1/2).

Nielsen & Chuang's §6.6 optimality proof shows that any quantum algorithm solving the search
problem with success probability `≥ 1/2` **for every** marked item `x` needs `Ω(√N)` oracle calls.
This exercise weakens the success criterion to the **uniform average over `x`** and asks for the
same `Ω(√N)` lower bound. It is the strictly harder statement: the average-case hypothesis is
implied by (but does not imply) the worst-case one.

## Where the content lives

The proof is the §6.6 deviation argument (`Dₖ ≤ 4k²` versus `Dₖ ≥ (√Fₖ − √Eₖ)²`), with the
average-case relaxation entering only through the bound `Eₖ < N`. It has two parts:

* **Analytic backbone** (`AxQM/Concrete/`, linear algebra over a generic complex inner-product
  space `H`):
  * `Concrete.searchDeviation_le_four_mul_sq` — **N&C eqs. 6.41–6.46**, `Dₖ ≤ 4k²`;
  * `Concrete.searchQueries_ge_of_averaged_success` / `Concrete.searchQueries_ge_sqrt_div_eight` —
    the assembly (N&C eqs. 6.47–6.52) with the Exercise 6.16 average-case strengthening
    (`qₓ ∈ [0,1] ⇒ √qₓ ≥ qₓ ⇒ Eₖ ≤ 2N − 2∑qₓ < N`), giving `√(2N − 2√N) − √N ≤ 2k` and, for
    `N ≥ 21`, the explicit `√N/8 ≤ k`.

* **Physical (Born-rule) grounding** (`AxQM/Postulates/API/SearchOptimality.lean`):
  * `QuantumSearchProblem` — a register with a marked computational basis; its `oracle` family
    `Oₓ = I − 2|x⟩⟨x|` (`Evolution`), its computational-basis `measurement`, and the with-oracle
    algorithm state `queryState` (`PureState`);
  * `QuantumSearchProblem.sum_bornProb_queryState` — the Born rule (Postulate 3): the averaged
    success probability `∑ₓ p(x | ψˣ_k)` equals the concrete average-case weight `∑ₓ |⟨x|ψˣ_k⟩|²`.

## The formalisation (this file)

Two statements about quantum search
(in terms of `QuantumSearchProblem.measurement`/`queryState` and `Measurement.bornProb`):
for a `k`-query search algorithm whose **uniformly averaged** success probability of
returning the marked item is at least `1/2` (`N/2 ≤ ∑ₓ p(x | ψˣ_k)`, each `p(x | ψˣ_k)` a genuine
`Measurement.bornProb`),

* `search_bornProb_averaged_success_imp_sqrt_bound` — the query bound `√(2N − 2√N) − √N ≤ 2k`; and
* `search_bornProb_averaged_success_imp_queries_ge` — the clean `Ω(√N)` conclusion `√N/8 ≤ k`
  (for `N ≥ 21`).

Only the average-case hypothesis is used, exactly as Exercise 6.16 asks; the constant `1/8` and
threshold `N ≥ 21` are an explicit realisation of `Ω(√N)`.
-/

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem} {N : ℕ}

/-- **Nielsen & Chuang, Exercise 6.16 — the query bound.** For a `k`-query quantum search algorithm
on a register `S` with a marked computational basis (`prob : QuantumSearchProblem S N`), initial
pure state `ψ` and arbitrary unitary schedule `U`, if the **uniformly averaged** success
probability of returning the marked item is at least one half —
`N/2 ≤ ∑ₓ p(x | ψˣ_k)` with each `p(x | ψˣ_k)` the genuine Born probability
`prob.measurement.bornProb (prob.queryState U ψ k x).toState x` of reading item `x` back — then
`√(2N − 2√N) − √N ≤ 2k`.

This is the physical (Born-rule) content of N&C §6.6 under the Exercise 6.16 average-case
criterion: the success weight is a genuine
`Measurement.bornProb` of the with-oracle `PureState`, which the deviation argument
(`Concrete.searchQueries_ge_of_averaged_success`) turns into the query bound via the Born-rule
bridge `QuantumSearchProblem.sum_bornProb_queryState`. -/
theorem search_bornProb_averaged_success_imp_sqrt_bound (prob : QuantumSearchProblem S N)
    (U : ℕ → Evolution S) (ψ : PureState S) (k : ℕ)
    (havg : (N : ℝ) / 2 ≤ ∑ x, prob.measurement.bornProb (prob.queryState U ψ k x).toState x) :
    Real.sqrt (2 * (N : ℝ) - 2 * Real.sqrt N) - Real.sqrt N ≤ 2 * k := by
  rw [prob.sum_bornProb_queryState] at havg
  exact Concrete.searchQueries_ge_of_averaged_success (fun j => (U j).toIsometryEquiv) ψ.vec
    prob.markBasis.orthonormal ψ.normalized k havg

/-- **Nielsen & Chuang, Exercise 6.16 — `O(√N)` oracle calls are still required.** Under the
uniformly averaged success criterion `N/2 ≤ ∑ₓ p(x | ψˣ_k)` (Born probabilities of returning the
marked item), a `k`-query quantum search algorithm needs `k ≥ √N/8` for `N ≥ 21`: `Ω(√N)` oracle
calls remain necessary even when the error is averaged uniformly over `x`, rather than bounded for
every `x`.

The average-case hypothesis is genuinely weaker than N&C's worst-case `|⟨x|ψˣ_k⟩|² ≥ 1/2` for all
`x` (it is implied by it), so this strengthens the §6.6 optimality theorem exactly as the exercise
asks. It is the clean explicit realisation of `search_bornProb_averaged_success_imp_sqrt_bound`:
for `N ≥ 21` one has `√(2N − 2√N) − √N ≥ √N/4`, whence `√N/8 ≤ k`. -/
theorem search_bornProb_averaged_success_imp_queries_ge (prob : QuantumSearchProblem S N)
    (U : ℕ → Evolution S) (ψ : PureState S) (k : ℕ) (hN : 21 ≤ N)
    (havg : (N : ℝ) / 2 ≤ ∑ x, prob.measurement.bornProb (prob.queryState U ψ k x).toState x) :
    Real.sqrt N / 8 ≤ (k : ℝ) := by
  rw [prob.sum_bornProb_queryState] at havg
  exact Concrete.searchQueries_ge_sqrt_div_eight (fun j => (U j).toIsometryEquiv) ψ.vec
    prob.markBasis.orthonormal ψ.normalized k hN havg

end AxQM
