/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SearchOptimality
import AxQM.Concrete.SearchLowerBoundMultiSolution

/-!
# AxQM.Postulates.API — physical grounding of the multiple-solution search lower bound

Definitions that express the linear algebra of `AxQM/Concrete/SearchLowerBoundMultiSolution.lean`
(Nielsen & Chuang **Exercise 6.17**, the `M`-solution generalisation of the §6.6 optimality proof)
in terms of systems, pure states, evolutions and measurements
(`QSystem`/`PureState`/`Evolution`/`Measurement`). They supply the vocabulary in which
`AxQM/NC/Ch6/Exercise6_17.lean` states the result.

## The physical picture

A search problem with `M` solutions among `N` items is a register `S` with an orthonormal
computational basis `|x⟩` (`x : Fin N`) — reused verbatim as the `QuantumSearchProblem` of the
single-solution grounding (`AxQM/Postulates/API/SearchOptimality.lean`). What changes for `M`
solutions is the *marked set* `s : Finset (Fin N)` of size `M`:

* the **set oracle** for the marked set `s` is the subspace reflection
  `O_s = I − 2 P_s`, where `P_s = ∑_{y∈s}|y⟩⟨y|` projects onto the marked items
  (`QuantumSearchProblem.setOracle`, a genuine unitary `Evolution` — the `M`-item analogue of the
  single-item reflection `Oₓ = I − 2|x⟩⟨x|`). It phase-flips **every** marked item,
  `O_s|y⟩ = −|y⟩` for `y ∈ s` (`setOracle_hasEigenstate_neg_one_of_mem`), i.e. it is the search
  oracle `O|x⟩ = (−1)^{f(x)}|x⟩` marking the `M` solutions;
* a `k`-query **algorithm** interleaves `O_s` with an arbitrary unitary schedule `U`, producing
  the pure state `ψˢ_k = U_{k−1} O_s ⋯ U_0 O_s ψ` (`QuantumSearchProblem.setQueryState`);
* **success** is *finding a solution*: measuring the final state `ψˢ_k` in the computational basis
  returns *some* marked item `y ∈ s`, an event of Born probability
  `∑_{y∈s} p(y | ψˢ_k) = ‖P_s ψˢ_k‖²` (Postulate 3).

## Main declarations

* `QuantumSearchProblem.setOracle` — the set oracle `O_s = I − 2 P_s` as an `Evolution S`.
  Unitarity is bundled and discharged from `P_s` being a star projection (self-adjoint idempotent),
  exactly as for the single-item reflection.
* `QuantumSearchProblem.setQueryState` — the with-oracle state `ψˢ_k` as a genuine `PureState S`,
  by recursion through `Evolution.evolvePure`; `setQueryState_vec` bridges its vector to the
  concrete recursion `Concrete.markedRun`.
* `QuantumSearchProblem.sum_mem_bornProb_setQueryState` — the **Born-rule bridge** (Postulate 3):
  the "find a solution" probability `∑_{y∈s} p(y | ψˢ_k)` equals the concrete marked weight
  `‖P_s ψˢ_k‖²` that the lower bound constrains.

The Born-rule success bound `⇒ k = Ω(√(N/M))` stated with these definitions is in
`AxQM/NC/Ch6/Exercise6_17.lean`.
-/

open scoped InnerProductSpace
open Finset InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A `k`-query algorithm state with a fixed oracle** `O`: the pure state
`U_{k−1} O ⋯ U_0 O ψ` after `k` interleaved (oracle `O`, then unitary `U`) steps from `ψ`, by
recursion through `Evolution.evolvePure` (so normalization is automatic). The search-agnostic
backbone of `QuantumSearchProblem.setQueryState` — the oracle is passed explicitly, keeping the
recursion free of the search-problem data. -/
def searchSetQueryState (U : ℕ → Evolution S) (O : Evolution S) (ψ : PureState S) :
    ℕ → PureState S
  | 0 => ψ
  | k + 1 => (U k).evolvePure (O.evolvePure (searchSetQueryState U O ψ k))

namespace QuantumSearchProblem

variable {N : ℕ} (prob : QuantumSearchProblem S N)

/-! ### The set oracle `O_s = I − 2 P_s` -/

/-- **The set oracle** `O_s = I − 2 P_s` for a marked set `s : Finset (Fin N)`: the reflection
about the marked subspace `span{|y⟩ : y ∈ s}`, as a unitary `Evolution S`. It is the `M`-solution
search oracle (N&C's `O|x⟩ = (−1)^{f(x)}|x⟩`, marking every item in `s`); the single-item
`prob.oracle x` is the special case `s = {x}`. Unitarity is bundled and discharged from the marked
projection `P_s = markedProj markBasis s` being a star projection (self-adjoint idempotent), so
`O_s = I − 2 P_s` is a self-adjoint involution, hence unitary. -/
def setOracle (s : Finset (Fin N)) : Evolution S where
  op := Concrete.markedOracle prob.markBasis s
  unitary := by
    have : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
    set P : S.space →L[ℂ] S.space := Concrete.markedProj prob.markBasis s with hPdef
    have hPP : P * P = P :=
      isIdempotentElem_orthonormalProjector prob.markBasis.orthonormal s
    have hPsa : star P = P :=
      isSelfAdjoint_orthonormalProjector (𝕜 := ℂ) (⇑prob.markBasis) s
    have hop : Concrete.markedOracle prob.markBasis s = 1 - (2 : ℂ) • P := by
      rw [hPdef]; rfl
    rw [hop]
    -- `O_s = I − 2P_s` is unitary because `P_s` is a star projection: apply the structural
    -- Mathlib lemma `IsStarProjection.two_mul_sub_one_mem_unitary` to `1 − P_s` (also a star
    -- projection), rewriting `2·(1 − P_s) − 1 = 1 − 2P_s`.
    have hsp : IsStarProjection P := ⟨hPP, hPsa⟩
    have hu := (isStarProjection_one_sub_iff.mpr hsp).two_mul_sub_one_mem_unitary
    have he : (2 : S.space →L[ℂ] S.space) * (1 - P) - 1 = 1 - (2 : ℂ) • P := by
      rw [two_smul, two_mul]; abel
    rwa [he] at hu

@[simp]
theorem setOracle_op (s : Finset (Fin N)) :
    (prob.setOracle s).op = Concrete.markedOracle prob.markBasis s := rfl

/-- **The set oracle phase-flips every marked item** `O_s|y⟩ = −|y⟩` for `y ∈ s`: each marked basis
state `|y⟩` is an eigenstate of `O_s` with eigenvalue `−1`. This is the defining action of the
search oracle `O|x⟩ = (−1)^{f(x)}|x⟩` (N&C §6.6) marking the `M` solutions: since `P_s|y⟩ = |y⟩`
for `y ∈ s`, one has `O_s|y⟩ = |y⟩ − 2|y⟩ = −|y⟩`. It certifies that `setOracle` is genuinely the
multiple-solution search oracle, not an arbitrary reflection. -/
theorem setOracle_hasEigenstate_neg_one_of_mem {s : Finset (Fin N)} {y : Fin N} (hy : y ∈ s) :
    (prob.setOracle s).HasEigenstate (-1) (prob.markedState y) := by
  change Concrete.markedOracle prob.markBasis s (prob.markBasis y) = (-1 : ℂ) • prob.markBasis y
  rw [Concrete.markedOracle_apply, Concrete.markedProj_apply_mem prob.markBasis hy]
  module

/-! ### The with-oracle algorithm state as a pure state -/

/-- **The with-oracle algorithm state** `ψˢ_k = U_{k−1} O_s ⋯ U_0 O_s ψ` for the marked set `s`
after `k` oracle queries with unitary schedule `U` from the initial state `ψ`, as a genuine
`PureState S`. By recursion on `k`: each step applies the set oracle `O_s = prob.setOracle s` and
then the unitary `U k`, both via `Evolution.evolvePure`, so normalization is automatic. The physics
counterpart of the concrete recursion `Concrete.markedRun`; the search-agnostic backbone
`searchSetQueryState` is instantiated with the named oracle `O_s = prob.setOracle s`. -/
def setQueryState (U : ℕ → Evolution S) (ψ : PureState S) (s : Finset (Fin N)) (k : ℕ) :
    PureState S :=
  searchSetQueryState U (prob.setOracle s) ψ k

/-- **Each algorithm step is one set-oracle query followed by a unitary**: the `(k+1)`-st state is
obtained from the `k`-th by applying the *named* oracle `O_s = prob.setOracle s` and then the
schedule unitary `U k`, `ψˢ_{k+1} = U_k O_s ψˢ_k` (definitionally, so the proof is `rfl`). -/
theorem setQueryState_succ (U : ℕ → Evolution S) (ψ : PureState S) (s : Finset (Fin N)) (k : ℕ) :
    prob.setQueryState U ψ s (k + 1)
      = (U k).evolvePure ((prob.setOracle s).evolvePure (prob.setQueryState U ψ s k)) :=
  rfl

/-- **Bridge to the concrete recursion.** The vector of the with-oracle pure state is the concrete
`Concrete.markedRun` over the isometry-equiv schedule `Evolution.toIsometryEquiv (U ·)`. Both
recursions apply the same maps at each step: the set oracle `O_s` (`setOracle_op` matches
`Concrete.markedOracle`) followed by the unitary step (`Evolution.toIsometryEquiv_apply`). -/
theorem setQueryState_vec (U : ℕ → Evolution S) (ψ : PureState S) (s : Finset (Fin N)) (k : ℕ) :
    (prob.setQueryState U ψ s k).vec
      = Concrete.markedRun prob.markBasis (fun j => (U j).toIsometryEquiv) ψ.vec s k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [setQueryState_succ, Evolution.evolvePure_vec, Evolution.evolvePure_vec, ih, setOracle_op,
      Concrete.markedRun, Evolution.toIsometryEquiv_apply]

/-! ### The Born-rule bridge: "find a solution" probability equals the marked weight -/

/-- **The Born rule for one marked item** (Postulate 3). The probability that measuring the
with-oracle state `ψˢ_k` in the computational basis returns the marked item `y` is `|⟨y|ψˢ_k⟩|²` —
the concrete amplitude weight against the `y`-th basis vector. Immediate from the projective Born
rule `Measurement.bornProb_ofOrthonormalBasis_toState` and the bridge `setQueryState_vec`. -/
theorem bornProb_setQueryState (U : ℕ → Evolution S) (ψ : PureState S) (s : Finset (Fin N))
    (k : ℕ) (y : Fin N) :
    prob.measurement.bornProb (prob.setQueryState U ψ s k).toState y
      = ‖(inner ℂ (prob.markBasis y)
          (Concrete.markedRun prob.markBasis (fun j => (U j).toIsometryEquiv) ψ.vec s k)
            : ℂ)‖ ^ 2 := by
  rw [measurement, Measurement.bornProb_ofOrthonormalBasis_toState, setQueryState_vec]

/-- **The Born-rule "find a solution" bridge** (Postulate 3). The probability that measuring the
with-oracle state `ψˢ_k` in the computational basis returns *some* marked item `y ∈ s` — the event
"the search found a solution" — equals the concrete marked weight `‖P_s ψˢ_k‖²`:
`∑_{y∈s} p(y | ψˢ_k) = ‖P_s ψˢ_k‖²`. This is the exact quantity the concrete lower bound
`Concrete.search_lower_bound_multi_solution` constrains via its success hypothesis. The sum of the
per-item Born probabilities (`bornProb_setQueryState`) is `∑_{y∈s} |⟨y|ψˢ_k⟩|²`, which is
`‖P_s ψˢ_k‖²` by Pythagoras (`Concrete.markedProj_norm_sq`). -/
theorem sum_mem_bornProb_setQueryState (U : ℕ → Evolution S) (ψ : PureState S)
    (s : Finset (Fin N)) (k : ℕ) :
    ∑ y ∈ s, prob.measurement.bornProb (prob.setQueryState U ψ s k).toState y
      = ‖Concrete.markedProj prob.markBasis s
          (Concrete.markedRun prob.markBasis (fun j => (U j).toIsometryEquiv) ψ.vec s k)‖ ^ 2 := by
  rw [Concrete.markedProj_norm_sq]
  exact Finset.sum_congr rfl fun y _ => prob.bornProb_setQueryState U ψ s k y

end QuantumSearchProblem

end AxQM
