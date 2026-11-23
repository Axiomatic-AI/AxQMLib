/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringLocality
import AxQM.Postulates.API.PauliTrotter

/-!
# Nielsen & Chuang, Exercise 4.48 — local Hamiltonians have polynomially many terms

Show restricting each H_k to at most c particles bounds L polynomially in n.

Here (eq. 4.97) `H = Σ_{k=1}^{L} Hₖ` is a Hamiltonian on `n` particles, each term `Hₖ` acting on at
most a constant number `c` of them. The exercise's content is a **counting** fact: there are only
polynomially many ways to choose which `≤ c` of the `n` particles a term acts on, so — collecting
the terms by the set of particles they couple — the number of terms `L` is bounded by a polynomial
in `n`.

## The statement

N&C's own local terms are Pauli strings ("two-body interactions such as `XᵢXⱼ` and one-body
Hamiltonians such as `Xᵢ`", §4.7.2). In this library such a term is a `pauliStringHamiltonian g c`
(`AxQM/Postulates/API/PauliTrotter.lean`): the `Observable` (Postulate 2 — a self-adjoint operator)
`c · g` on the `n`-qubit register `qudit (2ⁿ)`, for a Pauli string `g : Fin n → Fin 4` and real
coefficient `c`. The set of particles this term acts on is the support `pauliStringSupport g =
{i | g i ≠ 0}` (`AxQM/Concrete/PauliStringLocality.lean`, where
`pauliString_apply_eq_zero_of_notMem_
support` verifies the string acts as the identity off it), and "the term acts on at most `c`
particles" is `(pauliStringSupport g).card ≤ c`.

* `AxQM.exists_finset_pauliStringHamiltonian_card_le` — for any coefficient assignment
  `h`, the `c`-local Pauli-string Hamiltonian terms `h_g · g` on the `n`-qubit register are all
  contained in a finite set `T` of `Observable`s with `T.card ≤ 4ᶜ · (n + 1)ᶜ`, a polynomial in
  `n`. Hence a Hamiltonian `H = Σ_g h_g g` all of whose terms are `c`-local has at most `4ᶜ (n+1)ᶜ`
  distinct terms — `L` is bounded by a polynomial in `n`.
* `AxQM.exists_polynomial_pauliStringHamiltonian_card_le` — the same as a literal
  `Polynomial ℕ` bound: for fixed locality `c` there is a single polynomial `p` (of degree `c`,
  independent of `n` and of the coefficients) bounding the number of `c`-local term `Observable`s
  by `p.eval n`. This is the literal reading of "`L` is upper bounded by a polynomial in `n`".

## Design notes

* **Combinatorial core.** The proof reduces to the count of subsets of size `≤ c`
  of an `n`-element set (`Concrete.card_finset_card_le_le : … ≤ (n + 1)ᶜ`) and of the `c`-local
  Pauli strings (`Concrete.card_localPauliStrings_le : … ≤ 4ᶜ (n+1)ᶜ`) — pure combinatorics,
  in `AxQM/Concrete/PauliStringLocality.lean`.
  This file states it for `Observable`s on the register
  `qudit (2ⁿ)`, casting the count as a bound on the number of genuine Hamiltonian **term
  operators**. The bound is over the `Observable`s themselves, phrased as an existential
  `∃ T : Finset (Observable …)` so no `DecidableEq (Observable …)` instance is needed in the
  statement.
* **Why the `4ᶜ` factor.** Grouping by particle-subset alone gives `(n+1)ᶜ` supports; within a
  fixed support of `m ≤ c` qubits there are further `4ᵐ ≤ 4ᶜ` Pauli operators (`XᵢXⱼ`, `YᵢYⱼ`, …),
  so the count of distinct term operators carries the extra constant `4ᶜ`. This is still a
  polynomial in `n` (degree `c`, leading coefficient `4ᶜ`), which is all the exercise asks.
* **Fidelity.** N&C ask for a polynomial upper bound on `L`; both theorems provide one, with `n`
  the variable and `c` the fixed locality constant. No dimension is specialised and no hypothesis
  is added beyond `c`-locality of the terms, so the statement is the faithful content of the
  exercise, not a weakening.
-/

open scoped BigOperators

namespace AxQM

/-- **Nielsen & Chuang, Exercise 4.48.** The `c`-local Pauli-string Hamiltonian terms `h_g · g` on
the `n`-qubit register `qudit (2ⁿ)` — those whose Pauli string `g` acts on at most `c` particles
(`(pauliStringSupport g).card ≤ c`) — are all contained in a finite set `T` of `Observable`s whose
cardinality is at most the polynomial `4ᶜ · (n + 1)ᶜ` in the particle count `n`. Consequently any
Hamiltonian `H = Σ_g h_g g` all of whose terms are `c`-local has at most polynomially many distinct
terms `L`, which is exactly the claim of Exercise 4.48. -/
theorem exists_finset_pauliStringHamiltonian_card_le (c n : ℕ) (h : (Fin n → Fin 4) → ℝ) :
    ∃ T : Finset (Observable (qudit (2 ^ n))),
      (∀ g : Fin n → Fin 4, (Concrete.pauliStringSupport g).card ≤ c →
        pauliStringHamiltonian g (h g) ∈ T) ∧
      T.card ≤ 4 ^ c * (n + 1) ^ c := by
  classical
  refine ⟨(Concrete.localPauliStrings c n).image (fun g => pauliStringHamiltonian g (h g)),
    ?_, ?_⟩
  · intro g hg
    exact Finset.mem_image_of_mem _ (Concrete.mem_localPauliStrings.mpr hg)
  · exact Finset.card_image_le.trans (Concrete.card_localPauliStrings_le c n)

/-- **Exercise 4.48, "`L` is upper bounded by a polynomial in `n`".** For a fixed locality bound
`c` there is a single polynomial `p : Polynomial ℕ` (namely `4ᶜ · (X + 1)ᶜ`, of degree `c` and
independent of both the particle count `n` and the coefficients `h`) such that, for every `n` and
every coefficient assignment `h`, the `c`-local Pauli-string Hamiltonian terms on the `n`-qubit
register are contained in a finite set of `Observable`s of cardinality at most `p.eval n`. This is
the literal reading of the exercise: the number of terms `L` is bounded by a polynomial in `n`. -/
theorem exists_polynomial_pauliStringHamiltonian_card_le (c : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (n : ℕ) (h : (Fin n → Fin 4) → ℝ),
      ∃ T : Finset (Observable (qudit (2 ^ n))),
        (∀ g : Fin n → Fin 4, (Concrete.pauliStringSupport g).card ≤ c →
          pauliStringHamiltonian g (h g) ∈ T) ∧
        T.card ≤ p.eval n := by
  refine ⟨Polynomial.C (4 ^ c) * (Polynomial.X + 1) ^ c, fun n h => ?_⟩
  obtain ⟨T, hT, hcard⟩ := exists_finset_pauliStringHamiltonian_card_le c n h
  refine ⟨T, hT, ?_⟩
  simpa using hcard

end AxQM
