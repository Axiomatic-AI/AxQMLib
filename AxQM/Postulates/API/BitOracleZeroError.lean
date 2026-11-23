/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BitOracleAmplitudePoly
import AxQM.Postulates.API.ProjectiveMeasurement
import AxQM.Concrete.PolynomialMethodOR

/-!
# AxQM.Postulates.API — the zero-error query lower bound (method of polynomials)

The bridge that turns the amplitude–evaluation theorem
(`AxQM/Postulates/API/BitOracleAmplitudePoly.lean`) into the **query lower bound** Nielsen &
Chuang's Exercise 6.20 asks for: any zero-error `T`-query circuit computing OR needs `T ≥ N`. It
supplies the computational-basis `Measurement` of a `QuantumQueryProblem`, the Born-rule bridge
from a measurement probability to a squared amplitude, and the reduction from the physical
zero-error conditions to the pure-algebra lower bound
`Concrete.orZeroError_query_lower_bound_of_totalDegree_le` (over the field `K = ℂ`).

## The reduction

Fix a `QuantumQueryProblem` with unitary schedule `U`, input `ψ` and query count `T`, and a subset
`answer0` of computational-basis outcomes that the algorithm's classical post-processing decodes as
"output `0`" (N&C's step-4 register measurement followed by a classical read-out). The physical
fingerprint of a *zero-error* OR circuit is:

* it **never outputs `0`** on an input with `OR(X) = 1` — the answer-`0` amplitude
  `⟨k | ψ(X)_T⟩` vanishes there for every `k ∈ answer0` (`hnever`);
* it **does output `0`** on the all-zero input — some answer-`0` amplitude `⟨k | ψ(0)_T⟩` is nonzero
  (`hzero`).

By the amplitude–evaluation bridge each `⟨k | ψ(X)_T⟩`, as a function of the oracle string `X`, is a
polynomial `P_k` of total degree `≤ T` in the oracle bits, evaluated at the Boolean point
`boolPoint X`. Fixing the witnessing `k` from `hzero`, `P_k` is a polynomial over the field `ℂ` that
vanishes at every `OR = 1` Boolean input and is nonzero at the all-zero input — exactly the input to
`Concrete.orZeroError_query_lower_bound_of_totalDegree_le`, which multilinearizes `P_k`, matches it
to the unique OR representative `1 − ∏ₖ(1 − Xₖ)` of total degree `N`, and reads off
`N = Fintype.card σ ≤ T`. The pure-algebra reduction is field-generic, so it applies verbatim over
`ℂ`: the *complex* answer-`0` amplitude polynomial is used directly, with no need to pass to a
real/imaginary component.

## Main declarations

* `QuantumQueryProblem.measurement` — the projective computational-basis measurement
  `Measurement.ofOrthonormalBasis prob.basis`, with outcome type `σ × Bool × ω`.
* `QuantumQueryProblem.bornProb_queryState` — the Born-rule bridge: the measurement probability of
  outcome `k` on the query state equals the squared amplitude `‖⟨k | ψ(X)_T⟩‖²` (Postulate 3).
* `QuantumQueryProblem.queryState_amplitude_zeroError_lower_bound` — the amplitude-level reduction:
  the zero-error amplitude conditions force `Fintype.card σ ≤ T`.

The Born-rule statement of Exercise 6.20 (`Q₀(OR) ≥ N`) is in
`AxQM/NC/Ch6/Exercise6_20.lean`.
-/

open scoped InnerProductSpace
open MvPolynomial AxQM.Concrete

noncomputable section

namespace AxQM

variable {S : QSystem} {σ ω : Type*}

namespace QuantumQueryProblem

variable [Fintype σ] [Fintype ω] (prob : QuantumQueryProblem S σ ω)

/-- **The computational-basis measurement** of the query register: the projective `Measurement` in
the basis `|i,b,j⟩`, outcome type `σ × Bool × ω`. Its outcome is N&C's step-4 read-out of the whole
register, from which a classical function decodes the algorithm's answer (`0`, `1`, or
inconclusive). It is `Measurement.ofOrthonormalBasis prob.basis`, and its Born probabilities are
the squared
computational-basis amplitudes (`bornProb_queryState`). -/
def measurement : Measurement (σ × Bool × ω) S := Measurement.ofOrthonormalBasis prob.basis

/-- **The Born rule for the query state** (Postulate 3): the probability of reading the
computational-basis outcome `k` from the `T`-query algorithm state `ψ(X)_T` equals the squared
amplitude `‖⟨k | ψ(X)_T⟩‖²`. Instantiates `Measurement.bornProb_ofOrthonormalBasis_toState` at the
computational-basis measurement and the query `PureState`, the physical link between a measurement
probability and the amplitude polynomials of the method. -/
theorem bornProb_queryState (U : ℕ → Evolution S) (ψ : PureState S) (X : σ → Bool) (T : ℕ)
    (k : σ × Bool × ω) :
    prob.measurement.bornProb (prob.queryState U ψ X T).toState k
      = ‖inner ℂ (prob.basis k) (prob.queryState U ψ X T).vec‖ ^ 2 := by
  rw [measurement, Measurement.bornProb_ofOrthonormalBasis_toState]

/-- **The zero-error query lower bound** (Nielsen & Chuang, Exercise 6.20; amplitude form). Let
`answer0` be the computational-basis outcomes the algorithm decodes as "output `0`". If the
answer-`0` amplitude `⟨k | ψ(X)_T⟩` vanishes at every input `X` with `OR(X) = 1` (`hnever` — never
outputs `0` when the true answer is `1`) and some answer-`0` amplitude is nonzero at the all-zero
input (`hzero` — the circuit does output `0` there), then `Fintype.card σ ≤ T`.

Pick the witnessing `k` from `hzero`; the amplitude `⟨k | ψ(·)_T⟩` is, by
`exists_polynomial_queryState_amplitude`, the evaluation at `boolPoint ·` of a single polynomial `P`
of total degree `≤ T` over `ℂ`. Since `boolPoint` sends a bit-string to its Boolean point and the
all-`false` string to the origin, `hnever`/`hzero` say exactly that `P` vanishes at the `OR = 1`
Boolean inputs and is nonzero at the origin — the hypotheses of the field-generic pure-algebra
reduction `Concrete.orZeroError_query_lower_bound_of_totalDegree_le`, applied over `K = ℂ`. -/
theorem queryState_amplitude_zeroError_lower_bound (U : ℕ → Evolution S) (ψ : PureState S) (T : ℕ)
    (answer0 : Finset (σ × Bool × ω))
    (hnever : ∀ X : σ → Bool, (∃ i, X i = true) →
      ∀ k ∈ answer0, inner ℂ (prob.basis k) (prob.queryState U ψ X T).vec = 0)
    (hzero : ∃ k ∈ answer0,
      inner ℂ (prob.basis k) (prob.queryState U ψ (fun _ => false) T).vec ≠ 0) :
    Fintype.card σ ≤ T := by
  obtain ⟨k, hkmem, hk0⟩ := hzero
  obtain ⟨P, hPdeg, hPeval⟩ := prob.exists_polynomial_queryState_amplitude U ψ T k
  refine orZeroError_query_lower_bound_of_totalDegree_le (c := P) ?_ ?_ hPdeg
  · intro b hb
    have hpt : (fun i => if b i then (1 : ℂ) else 0) = boolPoint b := rfl
    rw [hpt, ← hPeval b]
    exact hnever b hb k hkmem
  · have hpt0 : (fun _ : σ => (0 : ℂ)) = boolPoint (K := ℂ) (fun _ : σ => false) := by
      funext i; simp [boolPoint]
    rw [hpt0, ← hPeval (fun _ => false)]
    exact hk0

end QuantumQueryProblem

end AxQM
