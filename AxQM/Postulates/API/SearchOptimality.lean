/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SearchOptimalityLowerBound
import AxQM.Postulates.API.Reflection
import AxQM.Postulates.API.ProjectiveMeasurement

/-!
# AxQM.Postulates.API — physical grounding of the search-optimality lower bound

Definitions that express the linear algebra of `AxQM/Concrete/SearchOptimalityLowerBound.lean`
(Nielsen & Chuang §6.6 and the average-case strengthening of **Exercise 6.16**) in terms of systems,
pure states, evolutions and measurements (`QSystem`/`PureState`/`Evolution`/`Measurement`). They
supply the vocabulary in which `AxQM/NC/Ch6/Exercise6_16.lean` states the result.

## The physical picture

A quantum-search problem over `N` items is a register `S` equipped with an orthonormal
computational basis `|x⟩` (`x : Fin N`) — the states one searches among:

* the **oracle** for a marked item `x` is the reflection `Oₓ = I − 2|x⟩⟨x|`
  (`reflectionEvolution`, N&C's self-adjoint unitary of §6.6), a genuine `Evolution`;
* a `k`-query **algorithm** interleaves the oracle with an arbitrary unitary schedule `U`,
  producing the pure state `ψˣ_k = U_k Oₓ ⋯ U₁ Oₓ ψ` (`queryState`);
* **success** is reading the marked item back: the projective computational-basis
  `Measurement` returns outcome `x` with Born probability `|⟨x|ψˣ_k⟩|²` (Postulate 3).

The average-case criterion of Exercise 6.16 is that this succeeds *on average over `x`*:
`(1/N)∑ₓ p(x | ψˣ_k) ≥ 1/2`. The lower bound then says `Ω(√N)` oracle calls are still needed.

The `Evolution`-valued unitary schedule is instantiated into the concrete recursion
`Concrete.searchQueryState` (typed over `S.space ≃ₗᵢ[ℂ] S.space`) via the general bridge
`Evolution.toIsometryEquiv` — a search-agnostic `Evolution`↔`≃ₗᵢ` repackaging that is defined next
to its inverse `Evolution.ofLinearIsometryEquiv` in `AxQM/Postulates/API/Evolution.lean`.

## Main declarations

* `searchQueryPureState` — the with-oracle state `ψˣ_k` as a genuine `PureState`, by recursion
  through `Evolution.evolvePure` and the oracle reflection; `searchQueryPureState_vec` is the
  bridge identifying its vector with the concrete `Concrete.searchQueryState`.
* `QuantumSearchProblem` — a register with a marked computational basis, packaging the
  `measurement`, the marked states, the `oracle` family (with `queryState_succ` showing each
  algorithm step reflects by `oracle x`), and the `queryState` definition.
* `QuantumSearchProblem.bornProb_queryState` / `QuantumSearchProblem.sum_bornProb_queryState` —
  the **Born-rule bridge**: the (averaged) success probability `∑ₓ bornProb(...)` equals the
  concrete average-case weight `∑ₓ |⟨x|ψˣ_k⟩|²` that the lower bound constrains.

The averaged Born-rule success bound `⇒ k = Ω(√N)` stated with these definitions is in
`AxQM/NC/Ch6/Exercise6_16.lean`.
-/

open scoped InnerProductSpace
open AxQM.Concrete

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The with-oracle algorithm state as a pure state -/

/-- **The with-oracle search state** `ψˣ_k = U_k Oₓ ⋯ U₁ Oₓ ψ` after `k` oracle queries against
the marked pure state `v`, as a genuine `PureState S`. By recursion on `k`: each step reflects about
`v` (the oracle `Oₓ = reflectionEvolution v`, N&C §6.6) and then applies the unitary `U j`, both via
`Evolution.evolvePure`, so normalization is automatic. The physics counterpart of the concrete
`Concrete.searchQueryState` (N&C eq. 6.38). -/
def searchQueryPureState (U : ℕ → Evolution S) (ψ v : PureState S) : ℕ → PureState S
  | 0 => ψ
  | j + 1 => (U j).evolvePure ((reflectionEvolution v).evolvePure (searchQueryPureState U ψ v j))

/-- **Bridge to the concrete recursion.** The vector of the with-oracle pure state is the concrete
`Concrete.searchQueryState` over the isometry-equiv schedule `Evolution.toIsometryEquiv (U ·)`. Both
recursions apply the same maps: the oracle reflection `x ↦ x − 2⟪v, x⟫ • v` (`reflectionEvolution`
matches `Concrete.searchOracle` for the unit vector `v`) followed by the unitary step. -/
theorem searchQueryPureState_vec (U : ℕ → Evolution S) (ψ v : PureState S) (k : ℕ) :
    (searchQueryPureState U ψ v k).vec
      = searchQueryState (fun j => (U j).toIsometryEquiv) ψ.vec v.vec k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [searchQueryPureState, Evolution.evolvePure_vec, Evolution.evolvePure_vec, ih,
      reflectionEvolution_op_apply, ← searchOracle_apply v.normalized, searchQueryState,
      Evolution.toIsometryEquiv_apply]

/-! ### A quantum-search problem: a register with a marked computational basis -/

/-- **A quantum-search problem** on the register `S` with `N` items: an orthonormal computational
basis `|x⟩` (`x : Fin N`) of `S.space`, the states one searches among. It packages the physical data
of Nielsen & Chuang §6.6 — the marked states, the oracle family `Oₓ`, the computational-basis
`Measurement`, and the with-oracle algorithm state — so that Exercise 6.16
can be stated in terms of states, evolutions and measurements. -/
structure QuantumSearchProblem (S : QSystem) (N : ℕ) where
  /-- The marked computational basis `|x⟩` of the search register. -/
  markBasis : OrthonormalBasis (Fin N) ℂ S.space

namespace QuantumSearchProblem

variable {N : ℕ} (prob : QuantumSearchProblem S N)

/-- The **marked pure state** `|x⟩` for item `x`: the `x`-th computational-basis vector, a unit
vector hence a genuine `PureState`. -/
def markedState (x : Fin N) : PureState S :=
  ⟨prob.markBasis x, prob.markBasis.orthonormal.norm_eq_one x⟩

@[simp]
theorem markedState_vec (x : Fin N) : (prob.markedState x).vec = prob.markBasis x := rfl

/-- The **oracle** `Oₓ = I − 2|x⟩⟨x|` for the marked item `x`: the reflection about `|x⟩`, a genuine
unitary `Evolution` (N&C's self-adjoint oracle of §6.6). -/
def oracle (x : Fin N) : Evolution S := reflectionEvolution (prob.markedState x)

/-- **The oracle phase-flips its marked state** `Oₓ|x⟩ = −|x⟩`: `|x⟩` is an eigenstate of `Oₓ` with
eigenvalue `−1` (the defining action of the search oracle, N&C §6.6). -/
theorem oracle_hasEigenstate_neg_one (x : Fin N) :
    (prob.oracle x).HasEigenstate (-1) (prob.markedState x) :=
  reflectionEvolution_hasEigenstate_neg_one (prob.markedState x)

/-- The **computational-basis measurement**: the projective `Measurement` in the marked basis
`|x⟩`, whose outcome `x` is "the search returned item `x`" (N&C's step-4 measurement). Its Born
probability is `p(x | ρ) = |⟨x|ρ|x⟩|`. -/
def measurement : Measurement (Fin N) S := Measurement.ofOrthonormalBasis prob.markBasis

/-- **The with-oracle algorithm state** `ψˣ_k` for marked item `x` after `k` queries with unitary
schedule `U` from the initial state `ψ`: `searchQueryPureState` about the marked state `|x⟩`. A
genuine `PureState`. -/
def queryState (U : ℕ → Evolution S) (ψ : PureState S) (k : ℕ) (x : Fin N) : PureState S :=
  searchQueryPureState U ψ (prob.markedState x) k

/-- **Each algorithm step is one oracle query followed by a unitary** (N&C eq. 6.38): the
`(k+1)`-st state is obtained from the `k`-th by applying the *named* oracle `Oₓ = prob.oracle x`
and then the schedule unitary `U_k`, `ψˣ_{k+1} = U_k Oₓ ψˣ_k`. This makes explicit that the
reflection the algorithm applies at each step is precisely `prob.oracle x` (they are definitionally
equal, so the proof is `rfl`), so the phase-flip oracle characterized by
`oracle_hasEigenstate_neg_one` is the one driving `queryState`. -/
theorem queryState_succ (U : ℕ → Evolution S) (ψ : PureState S) (k : ℕ) (x : Fin N) :
    prob.queryState U ψ (k + 1) x
      = (U k).evolvePure ((prob.oracle x).evolvePure (prob.queryState U ψ k x)) :=
  rfl

/-- **The Born-rule bridge** (Postulate 3). The probability that measuring the with-oracle state
`ψˣ_k` in the computational basis returns the marked item `x` is `|⟨x|ψˣ_k⟩|²` — the concrete
success weight `‖⟪|x⟩, Concrete.searchQueryState …⟫‖²`. Immediate from the projective Born rule
`Measurement.bornProb_ofOrthonormalBasis_toState` and the bridge `searchQueryPureState_vec`. -/
theorem bornProb_queryState (U : ℕ → Evolution S) (ψ : PureState S) (k : ℕ) (x : Fin N) :
    prob.measurement.bornProb (prob.queryState U ψ k x).toState x
      = ‖(inner ℂ (prob.markBasis x)
          (searchQueryState (fun j => (U j).toIsometryEquiv) ψ.vec (prob.markBasis x) k)
            : ℂ)‖ ^ 2 := by
  rw [measurement, Measurement.bornProb_ofOrthonormalBasis_toState, queryState,
    searchQueryPureState_vec, markedState_vec]

/-- The **averaged success probability** equals the concrete average-case weight
`∑ₓ |⟨x|ψˣ_k⟩|²` — the sum form of `bornProb_queryState`, the exact quantity the concrete lower
bound `Concrete.searchQueries_ge_of_averaged_success` constrains. -/
theorem sum_bornProb_queryState (U : ℕ → Evolution S) (ψ : PureState S) (k : ℕ) :
    ∑ x, prob.measurement.bornProb (prob.queryState U ψ k x).toState x
      = ∑ x, ‖(inner ℂ (prob.markBasis x)
          (searchQueryState (fun j => (U j).toIsometryEquiv) ψ.vec (prob.markBasis x) k)
            : ℂ)‖ ^ 2 :=
  Finset.sum_congr rfl fun x _ => prob.bornProb_queryState U ψ k x

end QuantumSearchProblem

end AxQM
