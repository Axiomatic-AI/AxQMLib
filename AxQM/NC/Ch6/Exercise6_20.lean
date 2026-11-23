/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BitOracleZeroError

/-!
# Nielsen & Chuang, Exercise 6.20 (`Q₀(OR) ≥ N` by the method of polynomials)

*(N&C p. 274.)*

Show Q0(OR) >= N by building a polynomial representing OR from a zero-error quantum circuit.

`Q₀(F)` is the **zero-error** quantum query complexity — the least number of oracle queries a
quantum computer needs to output either the correct value of `F` with certainty, or (with
probability `< 1/2`) an admission of an inconclusive result, never a wrong value (N&C p. 272).

## The argument (N&C §6.7)

The chapter's *method of polynomials* (eqs. 6.58–6.61) shows that a quantum algorithm making `T`
oracle queries produces output amplitudes `cₖ(X) = ⟨k | ψ(X)⟩` that are polynomials of degree at
most `T` in the oracle bits `X₀, …, X_{N-1}`: each oracle call raises the degree by at most one and
the interleaved unitaries do not raise it at all. Exercise 6.20 turns this, in the zero-error case,
into the lower bound `Q₀(OR) ≥ N`.

Measure the `T`-query output register in the computational basis and let a classical function decode
the outcome as "answer `0`", "answer `1`" or "inconclusive". Zero error forces:

* on every input `X` with `OR(X) = 1`, the algorithm never answers `0`, so the total answer-`0`
  probability `∑_{k ∈ answer0} |cₖ(X)|²` is `0` and hence **every** answer-`0` amplitude vanishes
  there;
* on the unique input `X = 0` with `OR(X) = 0`, it answers `0` with probability `> 1/2`, so some
  answer-`0` amplitude is nonzero at `0`.

The complex amplitude `cₖ` is then a polynomial of total degree `≤ T` over `ℂ` that vanishes at
every Boolean `OR = 1` input and is nonzero at `0`. Then `P(X) = 1 − cₖ(0)⁻¹·cₖ(X)` **represents
OR** and has `deg P ≤ deg cₖ ≤ T`. Since the multilinear representative of OR is unique
(Exercise 6.18) and equals `1 − ∏ₖ(1 − Xₖ)` of total degree `N` (Exercise 6.19), `P` is exactly
that polynomial, so `N = deg P ≤ T`. As this holds for every zero-error `T`-query circuit,
`Q₀(OR) ≥ N`. (The bound is tight: `Q₀(OR) = N`.)

## The formalisation

The method-of-polynomials reduction is proved from the Born rule rather than assumed:

* `AxQM/Concrete/MethodOfPolynomials.lean` — the algebraic backbone
  (`polyQueryState`, `totalDegree_polyQueryState_le`, N&C eqs. 6.58–6.61) and its Boolean-point
  evaluation lemmas.
* `AxQM/Concrete/PolynomialMethodOR.lean` — the OR construction
  (`orZeroErrorPoly`, `orZeroErrorPoly_represents`, uniqueness `eq_of_represents`, and the
  field-generic query lower bound `orZeroError_query_lower_bound_of_totalDegree_le`), with
  `totalDegree_orPoly = N` (Exercise 6.19) and `MvPolynomial.multilinearize` (`ToMathlib`).
* `AxQM/Postulates/API/BitOracleQueryCircuit.lean`,
  `.../BitOracleAmplitudePoly.lean`, `.../BitOracleZeroError.lean` — the physical side:
  the bit-oracle `O_X` as a unitary `Evolution` family, the `T`-query state `ψ(X)` as a `PureState`,
  the amplitude–evaluation bridge `⟨k | ψ(X)⟩ = eval_X(polyQueryState)`
  (`exists_polynomial_queryState_amplitude`), the computational-basis `Measurement`, and the
  amplitude-level reduction `queryState_amplitude_zeroError_lower_bound`.

This file states the Born-rule form of the result, in terms of `QuantumQueryProblem`,
`Measurement.bornProb` and `PureState`.
-/

open scoped InnerProductSpace

namespace AxQM

variable {S : QSystem} {σ ω : Type*}

/-- **Nielsen & Chuang, Exercise 6.20: `Q₀(OR) ≥ N`.** Consider a `T`-query quantum algorithm on a
register `S` with a computational basis `|i,b,j⟩` indexed by `σ × Bool × ω`
(`prob : QuantumQueryProblem S σ ω`), unitary schedule `U`, input pure state `ψ`, and query state
`ψ(X)_T = prob.queryState U ψ X T` against the bit-oracle for `X : σ → Bool`. Measure the output in
the computational basis (`prob.measurement`) and let `answer0` be the outcomes decoded as
"output `0`". If the circuit **computes OR with zero error**, i.e.

* it never outputs `0` when `OR(X) = 1` — the answer-`0` probability
  `∑_{k ∈ answer0} p(k | ψ(X)_T)` is `0` for every `X` with some `Xᵢ = true` (`hnever`), and
* it outputs `0` with probability `> 1/2` on the all-zero input (`hcorrect`),

each `p(k | ψ(X)_T)` being the genuine Born probability
`prob.measurement.bornProb (prob.queryState U ψ X T).toState k` (Postulate 3), then
`Fintype.card σ ≤ T`. Since this bounds the query count `T` of *every* zero-error `T`-query OR
circuit from below by `N = Fintype.card σ`, the zero-error quantum query complexity satisfies
`Q₀(OR) ≥ N`.

The proof reads the two physical hypotheses back to amplitude conditions through the Born-rule
bridge `bornProb_queryState`: an answer-`0` probability of `0` is a sum of squared norms equal to
`0`, so every answer-`0` amplitude vanishes; a probability `> 1/2 > 0` forces some answer-`0`
amplitude to be nonzero. These are exactly the hypotheses of the amplitude-level reduction
`queryState_amplitude_zeroError_lower_bound`, which delivers `N ≤ T` via the method of
polynomials. -/
theorem orZeroError_bornProb_query_lower_bound [Fintype σ] [Fintype ω]
    (prob : QuantumQueryProblem S σ ω) (U : ℕ → Evolution S) (ψ : PureState S) (T : ℕ)
    (answer0 : Finset (σ × Bool × ω))
    (hnever : ∀ X : σ → Bool, (∃ i, X i = true) →
      (∑ k ∈ answer0, prob.measurement.bornProb (prob.queryState U ψ X T).toState k) = 0)
    (hcorrect : 1 / 2 < ∑ k ∈ answer0,
      prob.measurement.bornProb (prob.queryState U ψ (fun _ => false) T).toState k) :
    Fintype.card σ ≤ T := by
  refine prob.queryState_amplitude_zeroError_lower_bound U ψ T answer0 (fun X hX k hk => ?_) ?_
  · -- Answer-`0` probability `0` on an `OR = 1` input ⇒ every answer-`0` amplitude vanishes there.
    have hnonneg : ∀ j ∈ answer0,
        0 ≤ prob.measurement.bornProb (prob.queryState U ψ X T).toState j := fun j _ => by
      rw [prob.bornProb_queryState]; exact sq_nonneg _
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (hnever X hX) k hk
    rw [prob.bornProb_queryState] at hzero
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hzero)
  · -- Answer-`0` probability `> 1/2 > 0` at `X = 0` ⇒ some answer-`0` amplitude is nonzero.
    by_contra hcon
    push Not at hcon
    have hsum : (∑ k ∈ answer0,
        prob.measurement.bornProb (prob.queryState U ψ (fun _ => false) T).toState k) = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [prob.bornProb_queryState, hcon k hk]; simp
    rw [hsum] at hcorrect
    norm_num at hcorrect

end AxQM
