/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution

/-!
# Nielsen & Chuang, Exercise 2.55 (the time-evolution operator is unitary)

Prove U(t1,t2)=exp(-iH(t2-t1)/hbar) is unitary.

Nielsen–Chuang's refined dynamical postulate (Postulate 2′, p. 82) is the Schrödinger
equation `iℏ d|ψ⟩/dt = H|ψ⟩` with a fixed **Hermitian Hamiltonian** `H`. For a
time-independent `H` its solution is `|ψ(t₂)⟩ = U(t₁,t₂)|ψ(t₁)⟩` (eq. 2.90) with the
**time-evolution operator** (eq. 2.91)
`U(t₁,t₂) ≡ exp(-i H (t₂ - t₁) / ℏ)`.
This exercise asks for the fact that ties the continuous-time picture (Postulate 2′) to the
discrete-time unitary picture (N&C Postulate 2 / this library's Postulate 5, `Evolution`):
`U(t₁,t₂)` is unitary. Physically it is why a closed system's evolution conserves total
probability — a Hermitian generator yields a norm-preserving map.

## The declarations

From the Hamiltonian `H` (an `Observable`, a Hermitian operator) the formalisation builds an
`Evolution` (a unitary), using the operators `Observable.op` and `Evolution.op`. It is in
`AxQM/Postulates/API/Evolution.lean` (namespace `AxQM`):

* `Observable.propagator H ℏ t₁ t₂ : Evolution S` — the propagator `U(t₁,t₂)` itself. Since
  an `Evolution` *bundles* its unitarity (`Evolution.unitary`), the
  existence of this term **is** Exercise 2.55: constructing it discharges exactly the proof
  that `U(t₁,t₂)` is unitary.
* `Observable.propagator_op` — its operator, `exp(-i H (t₂ - t₁) / ℏ)` (eq. 2.91), in the
  faithful exponential form.
* `Observable.propagator_op_mem_unitary` — the statement of the exercise:
  `exp(-i H (t₂ - t₁) / ℏ) ∈ unitary (S →L[ℂ] S)`.

## N&C ↦ Lean dictionary and fidelity

* **Hamiltonian `H`** ↦ `H : Observable S`, whose operator `H.op` is a self-adjoint (Hermitian)
  continuous linear operator on the system `S` (`Observable.selfAdjoint`).
* **`U(t₁,t₂) = exp(-i H (t₂ - t₁)/ℏ)`** ↦ `NormedSpace.exp ((-i·(t₂-t₁)/ℏ) • H.op)`, with the
  scalar `-i(t₂-t₁)/ℏ` applied to the operator `H.op` (scalar–operator multiplication commutes
  with N&C's `-iH(t₂-t₁)/ℏ`). All of `ℏ`, `t₁`, `t₂` are kept as free real parameters, exactly
  the shape of eq. 2.91 (no `ℏ = 1` specialisation).
* **"is unitary"** ↦ membership in `unitary (S →L[ℂ] S)`, which unfolds to `U† U = 1 ∧ U U† = 1`
  (`star` = adjoint = `†`), i.e. N&C's `U† U = I`.
* **Proof.** The exponent equals `i • (s • H.op)` with the real scalar `s = -(t₂-t₁)/ℏ`, so it
  is `i` times the self-adjoint operator `s • H.op`; `selfAdjoint.expUnitary` gives that the
  exponential of `i` times a self-adjoint element of the C*-algebra `S →L[ℂ] S` is unitary.
  This is a faithful, non-weakened rendering: the statement holds for an arbitrary Hamiltonian
  on any (finite-dimensional) quantum system, with no restriction on the dimension, `ℏ`, or the
  times.
-/
