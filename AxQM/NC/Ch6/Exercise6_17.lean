/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SearchLowerBoundMultiSolution

/-!
# Nielsen & Chuang, Exercise 6.17 (optimality of search with multiple solutions)

*(N&C p. 271.)*

Show O(sqrt(N/M)) oracle applications required to find a solution when there are M solutions.

Nielsen & Chuang's §6.6 optimality proof (the Bennett–Bernstein–Brassard–Vazirani hybrid argument)
shows any quantum algorithm solving the *single*-solution search problem needs `Ω(√N)` oracle
calls. This exercise asks for the `M`-solution generalisation: when the search problem has `M`
solutions, `Ω(√(N/M))` oracle applications are still required to find one — a quadratic improvement
over the classical `Θ(N/M)`.

## Where the content lives

The proof sandwiches a **deviation** `Dₖ = ∑_{|s|=M} ‖ψˢ_k − ψ_k‖²` (aggregated over all size-`M`
marked worlds `s`) between two bounds. It has two parts:

* **Analytic backbone** (`AxQM/Concrete/SearchLowerBoundMultiSolution.lean`,
  linear algebra over a generic complex inner-product space `H`):
  * `Concrete.sum_markedProj_normSq_eq` — the marked-weight identity
    `∑_{|s|=M} ‖P_s v‖² = C(N−1, M−1)` (unit `v`);
  * `Concrete.markedDeviation_le` — **part (a)**, the sensitivity bound `Dₖ ≤ 4k²·C(N−1,M−1)`;
  * `Concrete.markedDeviation_ge` — **part (b)**, the success lower bound
    `√(C(N,M)/2) ≤ √Dₖ + √C(N−1,M−1)`;
  * `Concrete.search_lower_bound_multi_solution` — the assembly `k ≥ ½·(√(N/2M) − 1) = Ω(√(N/M))`
    (via `N·C(N−1,M−1) = M·C(N,M)`).

* **Physical (Born-rule) grounding**
  (`AxQM/Postulates/API/SearchLowerBoundMultiSolution.lean`, reusing the `QuantumSearchProblem`
  register of the single-solution grounding):
  * `QuantumSearchProblem.setOracle` — the set oracle `O_s = I − 2 P_s` (`Evolution`), which
    phase-flips every marked item (`setOracle_hasEigenstate_neg_one_of_mem`);
  * `QuantumSearchProblem.setQueryState` — the with-oracle algorithm state `ψˢ_k` (`PureState`);
  * `QuantumSearchProblem.sum_mem_bornProb_setQueryState` — the Born rule (Postulate 3): the
    "find a solution" probability `∑_{y∈s} p(y | ψˢ_k)` equals the concrete marked weight
    `‖P_s ψˢ_k‖²`.

## The formalisation (this file)

The statement is `search_bornProb_multi_solution_imp_queries_ge`, in terms of
`QuantumSearchProblem.measurement`/`setQueryState` and `Measurement.bornProb`. For a `k`-query
search algorithm on a register `S` with a marked computational basis, initial pure state `ψ` and
arbitrary unitary
schedule `U`, if for **every** size-`M` marked world `s` the algorithm *finds a solution* with
probability at least `1/2` — `1/2 ≤ ∑_{y∈s} p(y | ψˢ_k)`, each `p(y | ψˢ_k)` a genuine
`Measurement.bornProb` of reading the marked item `y` back — then

`k ≥ ½·(√(N/(2M)) − 1) = Ω(√(N/M))`.

The `1/2` success threshold ("find a solution with probability ≥ 1/2 for each solution set", the
worst-case criterion of N&C §6.6) and the `Ω(√(N/M))` order match Exercise 6.17, which asks only
for the order. The success weight is a genuine Born probability of the with-oracle `PureState`, so
the physical content is a statement about measurement outcomes; the deviation
argument then turns it into the query bound via the Born-rule bridge
`QuantumSearchProblem.sum_mem_bornProb_setQueryState`.
-/

open scoped InnerProductSpace
open Finset

namespace AxQM

variable {S : QSystem} {N : ℕ}

/-- **Nielsen & Chuang, Exercise 6.17 — `Ω(√(N/M))` oracle applications are required.** For a
`k`-query quantum search algorithm on a register `S` with a marked computational basis
(`prob : QuantumSearchProblem S N`), initial pure state `ψ` and arbitrary unitary schedule `U`, if
for **every** size-`M` marked world `s` the algorithm *finds a solution* with probability at least
one half —
`1/2 ≤ ∑_{y∈s} p(y | ψˢ_k)` with each `p(y | ψˢ_k)` the genuine Born probability
`prob.measurement.bornProb (prob.setQueryState U ψ s k).toState y` of reading the marked item `y`
back — then
`k ≥ ½·(√(N/(2M)) − 1)`.

This is the multiple-solution optimality bound of N&C §6.6: `M` solutions still need `Ω(√(N/M))`
queries. It is the physical (Born-rule) content: the "find
a solution" success weight `∑_{y∈s} p(y | ψˢ_k)` is a genuine sum of `Measurement.bornProb`s of the
with-oracle `PureState`, which the Born-rule bridge
`QuantumSearchProblem.sum_mem_bornProb_setQueryState` turns into the concrete marked weight
`‖P_s ψˢ_k‖²`, whence the deviation sandwich
(`Concrete.search_lower_bound_multi_solution`) gives the query bound. -/
theorem search_bornProb_multi_solution_imp_queries_ge (prob : QuantumSearchProblem S N)
    (U : ℕ → Evolution S) (ψ : PureState S) {M : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) (k : ℕ)
    (hsucc : ∀ s ∈ (univ : Finset (Fin N)).powersetCard M,
        (1 : ℝ) / 2 ≤ ∑ y ∈ s, prob.measurement.bornProb (prob.setQueryState U ψ s k).toState y) :
    (1 / 2 : ℝ) * (Real.sqrt ((N : ℝ) / (2 * M)) - 1) ≤ (k : ℝ) := by
  refine Concrete.search_lower_bound_multi_solution prob.markBasis
    (fun j => (U j).toIsometryEquiv) ψ.normalized hM hMN k (fun s hs => ?_)
  have h := hsucc s hs
  rwa [prob.sum_mem_bornProb_setQueryState] at h

end AxQM
