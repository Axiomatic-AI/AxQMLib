/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ContinuousSearchHamiltonian
import AxQM.Postulates.API.SymmetricTrotterError

/-!
# AxQM.Postulates.API — the off-diagonal coupling Hamiltonian `H = |a⟩⟨ψ| + |ψ⟩⟨a|`

The off-diagonal Hamiltonian behind Nielsen & Chuang's **alternative** quantum-search
Hamiltonian (Exercise 6.12, eq. 6.29):

`H = |a⟩⟨ψ| + |ψ⟩⟨a|`   (`|a⟩` the target and `|ψ⟩` the starting state),

the *off-diagonal coupling* of a target pure state `a` and a starting pure state `ψ`, and the
explicit continuous-time evolution it generates. This is the **abstract** engine — a pair of pure
states `a`, `ψ` with a **real overlap** `⟨a, ψ⟩ = α` — that the single-solution search of
Exercise 6.12 instantiates at `a = |x⟩`, `ψ = uniformSuperposition`, `α = 1/√N`.

Contrast with the §6.2 *projector* search Hamiltonian `|a⟩⟨a| + |ψ⟩⟨ψ|`
(`Postulates/API/ContinuousSearchHamiltonian.lean`): both couple the same two states, but the
frequencies differ decisively (below), and *that* difference is the point of Exercise 6.12.

## The mathematics

Working with the real overlap `α = ⟨a, ψ⟩`, the vectors `a ± ψ` are eigenvectors of `H`:

`H (a + ψ) = (1 + α)(a + ψ)`,   `H (a − ψ) = (α − 1)(a − ψ)`

(reality of `α` — via `⟨ψ, a⟩ = conj⟨a, ψ⟩ = α` — is what makes `a ± ψ` eigenvectors). The
eigenvalues `α ± 1` differ from the projector Hamiltonian's `1 ± α` by swapping the roles of `1`
and `α`. Decomposing `ψ = ½(a + ψ) − ½(a − ψ)` and evolving each eigenvector by its phase gives

`exp(−i H t) |ψ⟩ = e^{−iαt} (cos t · |ψ⟩ − i sin t · |a⟩)`.

The rotation frequency is now `1` (not `α`), so `|ψ⟩` reaches `|a⟩` — up to a global phase — at the
**constant** time `t = π/2`, *independent of the overlap* and hence of the register size `N`:
`exp(−iH(π/2))|ψ⟩ = −i e^{−iαπ/2} |a⟩`. This is the `O(1)`-time rotation of Exercise 6.12(1).

## What is formalised

* `PureState.couplingHamiltonian a ψ` — the Hamiltonian `|a⟩⟨ψ| + |ψ⟩⟨a|` as an `Observable`
  (self-adjoint: `(|a⟩⟨ψ|)† = |ψ⟩⟨a|`, so the sum is its own adjoint).
* `PureState.couplingHamiltonian_apply_add` / `_apply_sub` — the eigenvector equations for `a ± ψ`.
* `PureState.couplingHamiltonian_propagator_op_apply` — the closed form of the evolved state, the
  `e^{−iαt}(cos t · ψ − i sin t · a)` above.
* `PureState.couplingHamiltonian_reaches_target` — at the constant time `t = π/2` the evolved state
  equals the target `|a⟩` up to a global phase, *for any real overlap* (no positivity needed): the
  `O(1)`-time rotation.
* `PureState.couplingHamiltonian_op_eq_projector_combination` — `H` as a real-linear combination of
  three projector Hamiltonians, `|a+ψ⟩⟨a+ψ| − |a⟩⟨a| − |ψ⟩⟨ψ|`, the formal content of "how a
  simulation of `H` is performed" (each projector Hamiltonian is simulated by the Exercise 6.7
  circuits, then Trotter-composed).
* `PureState.couplingProjectorHamiltonians` — that decomposition as an ordered list of three
  `Observable`s (the negated projectors `−|a⟩⟨a|`, `−|ψ⟩⟨ψ|` are still self-adjoint), and
  `couplingHamiltonian_op_eq_projectorHamiltonians_sum` re-reads it as `H.op = Σₖ (Hₖ).op`.
* `PureState.couplingSymmTrotterStep` — the concrete symmetric (Strang) Trotter simulation step of
  `H` (N&C eq. 4.106) built from those three projector propagators, and
  `couplingSymmTrotterStep_gateError_pow_le` its Exercise 4.50 / Box 4.1 error bound
  `E(U_Δtᵐ, exp(−2imHΔt)) ≤ m·α·Δt³`: the accuracy of the simulation, quantified. (The literal
  `O(√N)` *oracle-call count* for the search instantiation is an analysis-level resource estimate
  recorded separately as a signed cost model, `Concrete.altSearchSimOracleCalls_isTheta`.)

The statement of Exercise 6.12 (`AxQM/NC/Ch6/Exercise6_12.lean`) uses `couplingHamiltonian`,
`Observable.propagator`, `Evolution.evolvePure` and `PureState.toState`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **The off-diagonal coupling Hamiltonian** `H = |a⟩⟨ψ| + |ψ⟩⟨a|` (Nielsen & Chuang,
Exercise 6.12, eq. 6.29) of a target pure state `a` and a starting pure state `ψ`, as an
`Observable`. It is the sum of the two rank-one operators `|a⟩⟨ψ| = rankOne a.vec ψ.vec` and
`|ψ⟩⟨a| = rankOne ψ.vec a.vec`, which are adjoints of each other (`adjoint_rankOne`), so the sum is
self-adjoint. Evolving `ψ` under `H` rotates it onto `a` in constant time
(`couplingHamiltonian_reaches_target`); this is the "alternative Hamiltonian" whose evolution
Exercise 6.12 analyses. -/
def PureState.couplingHamiltonian (a ψ : PureState S) : Observable S where
  op := rankOne ℂ a.vec ψ.vec + rankOne ℂ ψ.vec a.vec
  selfAdjoint := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, map_add, adjoint_rankOne,
      adjoint_rankOne]
    exact add_comm _ _

/-- The action of the coupling Hamiltonian `H = |a⟩⟨ψ| + |ψ⟩⟨a|` on a vector `v`:
`H v = ⟨ψ, v⟩ |a⟩ + ⟨a, v⟩ |ψ⟩`. -/
theorem PureState.couplingHamiltonian_op_apply (a ψ : PureState S) (v : S.space) :
    (a.couplingHamiltonian ψ).op v
      = (inner ℂ ψ.vec v) • a.vec + (inner ℂ a.vec v) • ψ.vec := by
  simp only [PureState.couplingHamiltonian, add_apply, rankOne_apply]

/-- **The action of the coupling Hamiltonian on the target `|a⟩`.** For pure states `a`, `ψ` with
real overlap `⟨a, ψ⟩ = α`, `H |a⟩ = α |a⟩ + |ψ⟩` (using the Hermitian symmetry
`⟨ψ, a⟩ = conj⟨a, ψ⟩ = α`, which uses the reality of `α`, and `⟨a, a⟩ = 1`). -/
theorem PureState.couplingHamiltonian_apply_left (a ψ : PureState S) {α : ℝ}
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (a.couplingHamiltonian ψ).op a.vec = (α : ℂ) • a.vec + ψ.vec := by
  have hpa : inner ℂ ψ.vec a.vec = (α : ℂ) := by rw [← inner_conj_symm, h, Complex.conj_ofReal]
  rw [PureState.couplingHamiltonian_op_apply, hpa, a.inner_self, one_smul]

/-- **The action of the coupling Hamiltonian on the start `|ψ⟩`.** For pure states `a`, `ψ` with
real overlap `⟨a, ψ⟩ = α`, `H |ψ⟩ = |a⟩ + α |ψ⟩` (using `⟨ψ, ψ⟩ = 1` and `⟨a, ψ⟩ = α`). -/
theorem PureState.couplingHamiltonian_apply_right (a ψ : PureState S) {α : ℝ}
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (a.couplingHamiltonian ψ).op ψ.vec = a.vec + (α : ℂ) • ψ.vec := by
  rw [PureState.couplingHamiltonian_op_apply, ψ.inner_self, h, one_smul]

/-- **The `(α + 1)`-eigenvector of the coupling Hamiltonian.** For pure states `a`, `ψ` with real
overlap `⟨a, ψ⟩ = α`, the vector `a + ψ` is an eigenvector of `H = |a⟩⟨ψ| + |ψ⟩⟨a|` with eigenvalue
`α + 1`: `H (a + ψ) = (α + 1)(a + ψ)`. (Stated as `α + 1` rather than `1 + α` to match the
`c + d` shape of the shared two-state rotation `propagator_op_apply_of_two_state_eigen` at
`(c, d) = (α, 1)`, so this feeds it with no cast reordering.) -/
theorem PureState.couplingHamiltonian_apply_add (a ψ : PureState S) {α : ℝ}
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (a.couplingHamiltonian ψ).op (a.vec + ψ.vec) = ((α + 1 : ℝ) : ℂ) • (a.vec + ψ.vec) := by
  rw [map_add, a.couplingHamiltonian_apply_left ψ h, a.couplingHamiltonian_apply_right ψ h]
  push_cast; module

/-- **The `(α − 1)`-eigenvector of the coupling Hamiltonian.** For pure states `a`, `ψ` with real
overlap `⟨a, ψ⟩ = α`, the vector `a − ψ` is an eigenvector of `H = |a⟩⟨ψ| + |ψ⟩⟨a|` with eigenvalue
`α − 1`: `H (a − ψ) = (α − 1)(a − ψ)`. (The `−1` here — versus the projector Hamiltonian's `1 − α` —
is what changes the rotation frequency from `α` to `1`.) -/
theorem PureState.couplingHamiltonian_apply_sub (a ψ : PureState S) {α : ℝ}
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (a.couplingHamiltonian ψ).op (a.vec - ψ.vec) = ((α - 1 : ℝ) : ℂ) • (a.vec - ψ.vec) := by
  rw [map_sub, a.couplingHamiltonian_apply_left ψ h, a.couplingHamiltonian_apply_right ψ h]
  push_cast; module

/-- **The continuous-time evolution of the coupling Hamiltonian.** For pure states `a`, `ψ` with
real overlap `⟨a, ψ⟩ = α`, the state evolved under `H = |a⟩⟨ψ| + |ψ⟩⟨a|` for time `t` is

`exp(−i H t) |ψ⟩ = e^{−iαt} (cos t · |ψ⟩ − i sin t · |a⟩)`.

This is the two-state rotation `Observable.propagator_op_apply_of_two_state_eigen` at
`(c, d) = (α, 1)`: the eigenvectors `a ± ψ` have eigenvalues `α + 1` and `α − 1`
(`couplingHamiltonian_apply_add` / `_apply_sub`), i.e. `c + d = α + 1` and `c − d = α − 1`, so the
phase rate is `c = α` and the rotation rate is `d = 1`. Note the rotation frequency is `1`, so the
`cos`/`sin` argument is the bare time `t` — exactly the roles of `1` and `α` swapped relative to the
projector Hamiltonian's `cos(αt)`/`sin(αt)`. -/
theorem PureState.couplingHamiltonian_propagator_op_apply (a ψ : PureState S) {α : ℝ} (t : ℝ)
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    ((a.couplingHamiltonian ψ).propagator 1 0 t).op ψ.vec
      = Complex.exp (-(Complex.I * ((α * t : ℝ) : ℂ)))
        • ((Real.cos t : ℂ) • ψ.vec - (Complex.I * (Real.sin t : ℂ)) • a.vec) := by
  have := (a.couplingHamiltonian ψ).propagator_op_apply_of_two_state_eigen a ψ (c := α) (d := 1) t
    (a.couplingHamiltonian_apply_add ψ h) (a.couplingHamiltonian_apply_sub ψ h)
  simpa only [one_mul] using this

/-- **The coupling Hamiltonian rotates `|ψ⟩` onto `|a⟩` in constant time `π/2`.** For pure states
`a`, `ψ` with any real overlap `⟨a, ψ⟩ = α`, evolving `ψ` under `H = |a⟩⟨ψ| + |ψ⟩⟨a|` for the
**constant** time `t = π/2` produces the target state `a` up to a global phase — the density
operators coincide, `((H.propagator 1 0 (π/2)).evolvePure ψ).toState = a.toState`. This is the
two-state landing `Observable.evolvePure_toState_of_two_state_eigen` at `(c, d) = (α, 1)`: the
rotation rate is `d = 1 ≠ 0` (`one_ne_zero`), so the observation time is `π/(2·1) = π/2`, and at
`t = π/2` (`cos t = 0`, `sin t = 1`) the evolution is `−i e^{−iαπ/2} |a⟩` — a unit-modulus phase
times `|a⟩`, invisible to the state. Crucially the observation time `π/2` does **not** depend on `α`
(hence not on the register size `N`) — because the rotation rate `d = 1` is the constant, not `α`;
this is the `O(1)`-time rotation of Nielsen & Chuang, Exercise 6.12(1). No positivity of the overlap
is needed (unlike the projector search, whose time `π/(2α)` requires `α ≠ 0`). -/
theorem PureState.couplingHamiltonian_reaches_target (a ψ : PureState S) {α : ℝ}
    (h : inner ℂ a.vec ψ.vec = (α : ℂ)) :
    (((a.couplingHamiltonian ψ).propagator 1 0 (Real.pi / 2)).evolvePure ψ).toState
      = a.toState := by
  have := (a.couplingHamiltonian ψ).evolvePure_toState_of_two_state_eigen a ψ (c := α) (d := 1)
    one_ne_zero (a.couplingHamiltonian_apply_add ψ h) (a.couplingHamiltonian_apply_sub ψ h)
  simpa only [mul_one] using this

/-- **The coupling Hamiltonian as a combination of projector Hamiltonians** — the formal content of
"how a quantum simulation of `H` is performed" (Nielsen & Chuang, Exercise 6.12(2)). The
off-diagonal `H = |a⟩⟨ψ| + |ψ⟩⟨a|` is the real-linear combination

`H = |a+ψ⟩⟨a+ψ| − |a⟩⟨a| − |ψ⟩⟨ψ|`

of three rank-one projector Hamiltonians (from `(|a⟩+|ψ⟩)(⟨a|+⟨ψ|) = |a⟩⟨a| + H + |ψ⟩⟨ψ|`). Each
summand is a projector Hamiltonian of the kind Exercise 6.7 simulates by an explicit circuit
(`exp(−i|·⟩⟨·|Δt)`), so `exp(−iHt)` is simulated by Trotter-composing those circuits. (The number
of oracle calls this costs — `O(√N)` for the search instantiation — is an analysis-level resource
count recorded as a signed cost model, not derived here; see the `NC/Ch6/Exercise6_12` docstring.)
Proved by applying both sides to an arbitrary vector and expanding `⟨a+ψ, v⟩` bilinearly. -/
theorem PureState.couplingHamiltonian_op_eq_projector_combination (a ψ : PureState S) :
    (a.couplingHamiltonian ψ).op
      = rankOne ℂ (a.vec + ψ.vec) (a.vec + ψ.vec)
        - rankOne ℂ a.vec a.vec - rankOne ℂ ψ.vec ψ.vec := by
  ext v
  simp only [PureState.couplingHamiltonian, add_apply,
    sub_apply, rankOne_apply, inner_add_left]
  module

/-- **A rank-one self-projector `|v⟩⟨v|` is self-adjoint** — the bedrock fact behind every projector
Hamiltonian. `(|v⟩⟨v|)† = |v⟩⟨v|` (`adjoint_rankOne`). -/
theorem isSelfAdjoint_rankOne_self (v : S.space) : IsSelfAdjoint (rankOne ℂ v v) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

/-- **The three projector Hamiltonians simulating the coupling Hamiltonian** (Nielsen & Chuang,
Exercise 6.12(2)). The ordered list of the three rank-one projector Hamiltonians of the
decomposition `H = |a+ψ⟩⟨a+ψ| − |a⟩⟨a| − |ψ⟩⟨ψ|`
(`couplingHamiltonian_op_eq_projector_combination`), each a bona fide `Observable` (self-adjoint
operator): `|a+ψ⟩⟨a+ψ|` and the *negated* projectors `−|a⟩⟨a|`, `−|ψ⟩⟨ψ|` (a negated projector
Hamiltonian is still self-adjoint, and `exp(+i|·⟩⟨·|Δt)` is simulated by the same Exercise 6.7
circuit run at negated time). This is the ordered Hamiltonian decomposition `H = Σₖ Hₖ` that the
symmetric-Trotter simulation of Exercise 4.50 consumes. -/
def PureState.couplingProjectorHamiltonians (a ψ : PureState S) : List (Observable S) :=
  [ ⟨rankOne ℂ (a.vec + ψ.vec) (a.vec + ψ.vec), isSelfAdjoint_rankOne_self _⟩,
    ⟨-rankOne ℂ a.vec a.vec, (isSelfAdjoint_rankOne_self _).neg⟩,
    ⟨-rankOne ℂ ψ.vec ψ.vec, (isSelfAdjoint_rankOne_self _).neg⟩ ]

/-- **The coupling Hamiltonian is the sum of its three projector Hamiltonians.** In the form
`H.op = (Hs.map Observable.op).sum` demanded by the symmetric-Trotter error bound
(`Observable.symmTrotterStep_gateError_pow_le`), for `Hs = couplingProjectorHamiltonians a ψ`. This
just re-reads `couplingHamiltonian_op_eq_projector_combination` as a three-term list sum. -/
theorem PureState.couplingHamiltonian_op_eq_projectorHamiltonians_sum (a ψ : PureState S) :
    (a.couplingHamiltonian ψ).op
      = ((a.couplingProjectorHamiltonians ψ).map Observable.op).sum := by
  rw [couplingHamiltonian_op_eq_projector_combination]
  simp only [PureState.couplingProjectorHamiltonians, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  abel

/-- **The symmetric (Strang) Trotter simulation step of the coupling Hamiltonian** (Nielsen &
Chuang, Exercise 6.12(2), "explain how a quantum simulation of `H` may be performed"). The
palindromic product `Observable.symmTrotterStep` (N&C eq. 4.106) of the propagators of the three
projector Hamiltonians `|a+ψ⟩⟨a+ψ|`, `−|a⟩⟨a|`, `−|ψ⟩⟨ψ|` (`couplingProjectorHamiltonians`), each
of which is simulated by an explicit Exercise 6.7 oracle circuit (Figures 6.4/6.5). Repeated `m`
times with a small time-step `Δt`, this simulates the true evolution `exp(−2imHΔt)` to third order
in `Δt` (`couplingSymmTrotterStep_gateError_pow_le`) — the concrete simulation of the alternative
search Hamiltonian. -/
def PureState.couplingSymmTrotterStep (a ψ : PureState S) (Δt : ℝ) : Evolution S :=
  Observable.symmTrotterStep (a.couplingProjectorHamiltonians ψ) Δt

/-- **The simulation-error bound for the coupling Hamiltonian** (Nielsen & Chuang,
Exercise 6.12(2), via the Exercise 4.50 / Box 4.1 error calculus). Running the symmetric Trotter
step `m` times approximates the exact evolution `exp(−2imHΔt) = H.propagator 1 0 (2mΔt)` of the
coupling Hamiltonian `H = |a⟩⟨ψ| + |ψ⟩⟨a|` with an error growing at most linearly in `m`:
`E(U_Δtᵐ, exp(−2imHΔt)) ≤ m·α·Δt³` for some constant `α ≥ 0` and every `Δt ∈ [0, 1]`, in Box 4.1's
gate-error notation `E(U,V) = ‖U.op − V.op‖` (`Evolution.gateError`, N&C eq. 4.61). This *is* the
formal content of "how a quantum simulation of `H` is performed, and [its accuracy]": it
instantiates the general symmetric-Trotter bound `Observable.symmTrotterStep_gateError_pow_le` at
the three-projector decomposition `couplingHamiltonian_op_eq_projectorHamiltonians_sum`. The bound
quantifies the *accuracy* of the simulation; the literal *number of oracle calls* (`O(√N)` for the
search instantiation) is an analysis-level resource estimate recorded separately as a signed cost
model, `Concrete.altSearchSimOracleCalls_isTheta` (see the `NC/Ch6/Exercise6_12` docstring). The
constant `α` here is the (existentially quantified) third-order per-step constant of Exercise 4.50 —
its dependence on `N` is not exposed by this accuracy bound. -/
theorem PureState.couplingSymmTrotterStep_gateError_pow_le (a ψ : PureState S) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ (m : ℕ) (Δt : ℝ), 0 ≤ Δt → Δt ≤ 1 →
      (a.couplingSymmTrotterStep ψ Δt ^ m).gateError
          ((a.couplingHamiltonian ψ).propagator 1 0 (2 * (m : ℝ) * Δt))
        ≤ (m : ℝ) * α * Δt ^ 3 :=
  Observable.symmTrotterStep_gateError_pow_le (a.couplingHamiltonian ψ)
    (a.couplingProjectorHamiltonians ψ)
    (a.couplingHamiltonian_op_eq_projectorHamiltonians_sum ψ)

end AxQM
