/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import ToMathlib.Analysis.InnerProductSpace.PiL2

/-!
# AxQM.Postulates.API — the bit-oracle query circuit

Physical model for the **method of polynomials** (Nielsen & Chuang §6.7, eqs. 6.58–6.61,
Figure 6.10), the tool Exercise 6.20 uses to prove `Q₀(OR) ≥ N`. This file treats the *circuit*
side of the method in terms of `QSystem`/`PureState`/`Evolution`: the bit-oracle
`O_X` as a genuine unitary `Evolution` family, and the `T`-query algorithm state `ψ(X)` as a genuine
`PureState`.

## The physical picture (N&C Figure 6.10)

A quantum query algorithm runs on a register whose computational basis is labelled `|i⟩|b⟩|j⟩` — the
oracle-query index `i` (which bit is asked), a single answer qubit `b`, and a workspace `j`. We
model this register abstractly as any `QSystem S` with an orthonormal computational basis indexed by
`σ × Bool × ω` (`QuantumQueryProblem`), exactly mirroring how Exercise 6.16's
`QuantumSearchProblem` models the search register by an abstract `OrthonormalBasis (Fin N)`. The
index type `σ × Bool × ω` matches the method-of-polynomials development
`AxQM/Concrete/MethodOfPolynomials.lean` verbatim (`σ` the oracle-index type, `Bool` the
answer qubit, `ω` the workspace), so the amplitude–evaluation bridge needs no
reindexing. An abstract register with a computational basis *is* `qudit |σ| ⊗ qubit ⊗ qudit |ω|` up
to the canonical isometry — a concrete instance is provided by e.g. `quditTriplePerm`.

For a bit-string `X : σ → Bool` (the oracle's hidden input), the **bit-oracle**
`O_X : |i⟩|b⟩|j⟩ ↦ |i⟩|b ⊕ Xᵢ⟩|j⟩` (N&C eq. 6.61) is the unitary that permutes the computational
basis by the involution `(i, b, j) ↦ (i, b ⊕ Xᵢ, j)`. Permuting an orthonormal basis is an isometry,
so `O_X` is a genuine `Evolution` — the same construction as `quditTriplePerm`, a classical
reversible circuit realised as a basis-permutation gate. A `T`-query algorithm interleaves this
oracle with an arbitrary unitary schedule `U₀, …, U_T` and applies the result to a fixed input,
giving the query state `ψ(X) = U_T O_X ⋯ O_X U₀ ψ₀` (`queryPureState`).

## Main declarations

* `bitFlip X` / `bitFlipPerm X` — the answer-qubit XOR map `(i, b, j) ↦ (i, b ⊕ Xᵢ, j)` on
  `σ × Bool × ω`, and its packaging as an `Equiv.Perm` (built from its own involutivity).
* `QuantumQueryProblem S σ ω` — a register `S` with a computational basis indexed by `σ × Bool × ω`;
  `basisState p` is the computational-basis vector `|p⟩` as a `PureState`.
* `QuantumQueryProblem.bitOracle X` — the bit-oracle `O_X` as a unitary `Evolution S`
  (`Evolution.ofLinearIsometryEquiv` of the basis permutation), with defining action
  `bitOracle_op_basis : O_X |i,b,j⟩ = |i, b ⊕ Xᵢ, j⟩` at the operator (`.op`) level and
  `bitOracle_evolvePure_basisState` at the pure-state level.
* `queryPureState` / `QuantumQueryProblem.queryState` — the `T`-query algorithm state `ψ(X)` as a
  genuine `PureState`, by `Evolution.evolvePure` recursion (`U₀` first, then each step reflects by
  `O_X` and applies `U_{t+1}`), matching the `Concrete.polyQueryState` schedule convention;
  `queryState_succ` exposes the one-step recursion.

A value of type `Evolution S` or `PureState S` cannot be formed without discharging unitarity /
normalization. Compare `quditTriplePerm` and the `QuantumSearchProblem` of Exercise 6.16. The Born
rule + zero-error argument giving `Q₀(OR) ≥ N` is the subject of
`AxQM/NC/Ch6/Exercise6_20.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem} {σ ω : Type*}

/-! ### The answer-qubit XOR permutation -/

/-- The **answer-qubit XOR map** `(i, b, j) ↦ (i, b ⊕ Xᵢ, j)` on the computational-basis labels
`σ × Bool × ω`, for a bit-string `X : σ → Bool`. It flips the answer qubit `b` by the queried bit
`Xᵢ` and leaves the query index `i` and workspace `j` untouched — the label action of Nielsen &
Chuang's bit-oracle (eq. 6.61). -/
def bitFlip (X : σ → Bool) (p : σ × Bool × ω) : σ × Bool × ω :=
  (p.1, xor p.2.1 (X p.1), p.2.2)

/-- The bit-flip map is an **involution**: applying it twice XORs the answer qubit by `Xᵢ` twice,
returning `b` (`(b ⊕ Xᵢ) ⊕ Xᵢ = b`). This is what makes the bit-oracle a self-inverse unitary. -/
theorem bitFlip_involutive (X : σ → Bool) : Function.Involutive (bitFlip (ω := ω) X) := by
  rintro ⟨i, b, j⟩
  simp only [bitFlip, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The **answer-qubit XOR permutation** `bitFlipPerm X : Equiv.Perm (σ × Bool × ω)`, packaging the
involution `bitFlip X` as a permutation of the computational-basis labels. This is the permutation
the bit-oracle realises on the basis. -/
def bitFlipPerm (X : σ → Bool) : Equiv.Perm (σ × Bool × ω) :=
  (bitFlip_involutive X).toPerm

@[simp]
theorem bitFlipPerm_apply (X : σ → Bool) (p : σ × Bool × ω) :
    bitFlipPerm X p = (p.1, xor p.2.1 (X p.1), p.2.2) := rfl

/-! ### A quantum-query problem: a register with a `σ × Bool × ω` computational basis -/

/-- **A quantum-query problem** on the register `S`: an orthonormal computational basis `|i,b,j⟩` of
`S.space` indexed by `σ × Bool × ω` — the oracle-query index `i`, the single answer qubit `b`, and
the workspace `j` of Nielsen & Chuang's Figure 6.10. It packages the register so the bit-oracle
family and the query state can be stated, mirroring Exercise 6.16's
`QuantumSearchProblem`. -/
structure QuantumQueryProblem (S : QSystem) (σ ω : Type*) [Fintype σ] [Fintype ω] where
  /-- The computational basis `|i,b,j⟩` of the query register, indexed by `σ × Bool × ω`. -/
  basis : OrthonormalBasis (σ × Bool × ω) ℂ S.space

namespace QuantumQueryProblem

variable [Fintype σ] [Fintype ω] (prob : QuantumQueryProblem S σ ω)

/-- The **computational-basis pure state** `|p⟩` for a label `p = (i, b, j)`: the `p`-th basis
vector, a unit vector hence a genuine `PureState`. -/
def basisState (p : σ × Bool × ω) : PureState S :=
  ⟨prob.basis p, prob.basis.orthonormal.norm_eq_one p⟩

@[simp]
theorem basisState_vec (p : σ × Bool × ω) : (prob.basisState p).vec = prob.basis p := rfl

/-! ### The bit-oracle as a unitary evolution -/

/-- **The bit-oracle** `O_X` for the bit-string `X : σ → Bool` (Nielsen & Chuang, eq. 6.61): the
unitary `Evolution` of `S` that permutes the computational basis by `bitFlipPerm X`, sending
`|i,b,j⟩ ↦ |i, b ⊕ Xᵢ, j⟩`. It is `Evolution.ofLinearIsometryEquiv` of the linear isometry
equivalence permuting `prob.basis` by `bitFlipPerm X` (`OrthonormalBasis.equiv`), with unitarity
inherited from that isometry — forming this term *is* the fact that the bit-oracle is a legitimate
quantum operation. -/
def bitOracle (X : σ → Bool) : Evolution S :=
  Evolution.ofLinearIsometryEquiv (prob.basis.equiv prob.basis (bitFlipPerm X))

/-- **The bit-oracle's defining action** on the computational basis (operator/`.vec` level):
`O_X |i,b,j⟩ = |i, b ⊕ Xᵢ, j⟩`, i.e. `(prob.bitOracle X).op (prob.basis p) = prob.basis
(bitFlipPerm X p)`. The oracle realises exactly the permutation `bitFlipPerm X`. -/
theorem bitOracle_op_basis (X : σ → Bool) (p : σ × Bool × ω) :
    (prob.bitOracle X).op (prob.basis p) = prob.basis (bitFlipPerm X p) := by
  rw [bitOracle, Evolution.ofLinearIsometryEquiv_op_apply, OrthonormalBasis.equiv_apply_basis]

/-- **The bit-oracle's action on a computational-basis pure state** (`evolvePure` level):
`O_X |i,b,j⟩ = |i, b ⊕ Xᵢ, j⟩`. The `PureState`-level companion of `bitOracle_op_basis`. -/
theorem bitOracle_evolvePure_basisState (X : σ → Bool) (p : σ × Bool × ω) :
    (prob.bitOracle X).evolvePure (prob.basisState p) = prob.basisState (bitFlipPerm X p) := by
  apply PureState.ext
  simp only [Evolution.evolvePure_vec, basisState_vec, bitOracle_op_basis]

end QuantumQueryProblem

/-! ### The `T`-query algorithm state -/

/-- **The query algorithm state** `ψ_t = U_t O ⋯ O U₀ ψ₀` after `t` oracle queries against the
oracle `O`, with unitary schedule `U : ℕ → Evolution S` and input `ψ`, as a genuine `PureState S`.
By recursion on `t`: `U₀` is applied first (`ψ_0 = U₀ ψ`), then each step applies the oracle `O` and
the next unitary `U_{t+1}`, both via `Evolution.evolvePure`, so normalization is automatic. The
schedule convention (`U₀` before any query) matches the concrete `Concrete.polyQueryState`, so the
two recursions align term-by-term for the amplitude bridge. -/
def queryPureState (O : Evolution S) (U : ℕ → Evolution S) (ψ : PureState S) : ℕ → PureState S
  | 0 => (U 0).evolvePure ψ
  | t + 1 => (U (t + 1)).evolvePure (O.evolvePure (queryPureState O U ψ t))

@[simp]
theorem queryPureState_zero (O : Evolution S) (U : ℕ → Evolution S) (ψ : PureState S) :
    queryPureState O U ψ 0 = (U 0).evolvePure ψ := rfl

/-- **One algorithm step is one oracle query followed by a unitary**: the `(t+1)`-st query state is
obtained from the `t`-th by applying the oracle `O` and then the schedule unitary `U_{t+1}`. -/
theorem queryPureState_succ (O : Evolution S) (U : ℕ → Evolution S) (ψ : PureState S) (t : ℕ) :
    queryPureState O U ψ (t + 1)
      = (U (t + 1)).evolvePure (O.evolvePure (queryPureState O U ψ t)) := rfl

namespace QuantumQueryProblem

variable [Fintype σ] [Fintype ω] (prob : QuantumQueryProblem S σ ω)

/-- **The `T`-query algorithm state** `ψ(X)_t = U_t O_X ⋯ O_X U₀ ψ` for the bit-string `X` after `t`
queries, with unitary schedule `U` and input `ψ`: `queryPureState` driven by the bit-oracle
`prob.bitOracle X`. A genuine `PureState`, the physics counterpart of `Concrete.polyQueryState`. -/
def queryState (U : ℕ → Evolution S) (ψ : PureState S) (X : σ → Bool) (t : ℕ) : PureState S :=
  queryPureState (prob.bitOracle X) U ψ t

/-- **Each algorithm step is one bit-oracle query followed by a unitary**: the `(t+1)`-st query
state applies the *named* bit-oracle `O_X = prob.bitOracle X` then `U_{t+1}` to the `t`-th state.
Makes explicit that the reflection driving `queryState` is precisely the bit-oracle characterized by
`bitOracle_op_basis`. -/
theorem queryState_succ (U : ℕ → Evolution S) (ψ : PureState S) (X : σ → Bool) (t : ℕ) :
    prob.queryState U ψ X (t + 1)
      = (U (t + 1)).evolvePure ((prob.bitOracle X).evolvePure (prob.queryState U ψ X t)) := rfl

end QuantumQueryProblem

end AxQM
