/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ReachableCircuits

/-!
# `H, S, CNOT, Toffoli` are universal: every unitary is a limit of reachable circuits (up to phase)

*(N&C Exercise 4.43 — the universality conclusion.)*

This file assembles the §4.5/§4.3 development into Nielsen & Chuang's Exercise 4.43
conclusion: the Hadamard, phase, controlled-`NOT` and Toffoli gates are **universal for quantum
computation** — every unitary on an `m`-qubit register is approximated, to arbitrary accuracy and up
to an (unobservable) global phase, by a circuit built from those four gates.

## The reachable circuit set

The elementary gates the §4.5/§4.3 decomposition bottoms out in — and which the four-gate set
realises — are collected into the **reachable gate set** `reachableGateSet enc θ`:

* the `≤ 2`-control reversible gates `IsToffoliPermGate enc G` (`Toffoli`/`CNOT`/`NOT`), realised
  *exactly* by the four-gate set (`CNOT`, `Toffoli` are members; `NOT = H S² H`);
* the uncontrolled single-qubit gates on a wire `singleQubitOnWire enc j g` whose `2 × 2` block `g`
  is a **reachable rotation** (`g ∈ reachableRotations θ` — a finite product of `R_z(±θ), R_x(±θ)`),
  realised by the Exercise 4.41 circuit for `R_z(θ)` (`cos θ = 3/5`) and Hadamard conjugation for
  `R_x(θ)`.

`reachableCircuits enc θ` is the submonoid these generate — the exact matrix incarnation of "the
circuits assembled from the four gates" (their finite products).

## The universality theorem

* `exists_phase_smul_mem_closure_reachableCircuits` — **the headline**: for the reachability angle
  `θ` (`cos θ = 3/5`), an encoding `enc : (Fin m → Fin 2) ≃ Fin d` with at least one qubit
  (`Nontrivial (Fin m → Fin 2)`), and *any* `U ∈ U(d)`, some global phase `e^{iα}` makes
  `e^{iα} • U` lie in the topological closure of `reachableCircuits enc θ`. Because the ambient
  topology on `Matrix (Fin d) (Fin d) ℂ` is the (finite-dimensional) product topology — where
  closure means entrywise, equivalently operator-norm, approximation — this says exactly that the
  reachable circuits are **dense in `U(d)` up to a global phase**: the universality of
  `H, S, CNOT, Toffoli`. (States are rays, so the residual global phase is physically irrelevant; it
  is genuinely global — not a relative phase — precisely because the §4.3 reduction placed the
  single-qubit gates on *uncontrolled* wires, `singleQubitOnWire_smul`.)

The headline is a one-line instantiation of the **generic** reachable-circuit density
`exists_phase_smul_mem_closure_reachableCircuitsOf` (`Concrete/ReachableCircuits.lean`), which is
the shared §4.5/§4.3 assembly parameterised over an abstract single-qubit gate set `S` (here
`S = reachableRotations θ`, so `reachableCircuits enc θ` is
`reachableCircuitsOf enc ↑(reachableRotations θ)` definitionally). The four-gate-specific input is
just the per-wire single-qubit density
`exists_phase_smul_singleQubitOnWire_mem_closure` (N&C's single-qubit density, eq. 4.81,
`cos θ = 3/5`). The generic assembly chains three pieces:

1. the *exact* decomposition `exists_isToffoliOrSingleQubit_list_prod_eq` writes `U = gates.prod`
   with every factor an `IsToffoliOrSingleQubitGate` (a terminal gate);
2. each terminal gate is, up to a phase, a limit of reachable circuits: a `Toffoli`/`CNOT`/`NOT` is
   *exactly* a generator (phase `0`); a single-qubit wire gate is a limit of `singleQubitOnWire`
   applied to `S`, up to a global phase (the supplied density hypothesis);
3. the per-gate approximations multiply up: the closure of a submonoid is again a submonoid
   (`Submonoid.topologicalClosure`, matrix multiplication being continuous), so a product of
   limits-of-circuits is a limit of circuits, and the individual phases combine into one global
   phase `e^{iΣαⱼ}` (`smul_mul_smul_comm`, `Complex.exp_add`).

## Design: density, not a re-derived error budget

The statement is the topological density `∈ closure` rather than an explicit `∀ ε, ∃ V, ‖·‖ < ε`
bound. In the fixed finite dimension the two are equivalent (`Matrix` carries the product topology
and no ambient norm), and `∈ closure` is the Mathlib-idiomatic way to state density. N&C's
quantitative §4.5.3 error budget (eq. 4.63, "total error ≤ sum of per-gate errors") is formalised
independently as the general chaining inequality `norm_listProd_sub_listProd_le`; it is the accuracy
calculus behind step 3's convergence but is not re-invoked here, since the submonoid-closure route
delivers the density conclusion directly.

The link "`reachableGateSet enc θ` is exactly what `H, S, CNOT, Toffoli` realise" is carried by the
description of the reachable gate set above and the already-grounded circuit
`rzThreeFifthsCircuit` (Exercise 4.41);
this file, like the rest of the matrix-level §4.5/§4.3 development, stays a faithful *reformulation*
over the encoded-basis matrix gates rather than re-bridging each gate to its `Evolution`.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The reachable gate set.** The elementary matrix gates the §4.5/§4.3 universality reduction
bottoms out in, which the `H, S, CNOT, Toffoli` set realises: the `≤ 2`-control reversible gates
(`IsToffoliPermGate` — `Toffoli`/`CNOT`/`NOT`) together with, on every wire `j`, the uncontrolled
single-qubit gates `singleQubitOnWire enc j g` whose block `g` is a reachable rotation
(`g ∈ reachableRotations θ`). -/
noncomputable def reachableGateSet (enc : (Fin m → Fin 2) ≃ Fin d) (θ : ℝ) :
    Set (Matrix (Fin d) (Fin d) ℂ) :=
  {G | IsToffoliPermGate enc G} ∪
    ⋃ j : Fin m,
      singleQubitOnWire enc j '' (reachableRotations θ : Set (Matrix (Fin 2) (Fin 2) ℂ))

/-- **The reachable circuits.** The submonoid of `Matrix (Fin d) (Fin d) ℂ` generated by the
reachable gate set — the finite products of reachable gates, i.e. the matrix incarnation of the
circuits assembled from `H, S, CNOT, Toffoli`. Universality is the statement that its topological
closure fills `U(d)` up to a global phase (`exists_phase_smul_mem_closure_reachableCircuits`). -/
noncomputable def reachableCircuits (enc : (Fin m → Fin 2) ≃ Fin d) (θ : ℝ) :
    Submonoid (Matrix (Fin d) (Fin d) ℂ) :=
  Submonoid.closure (reachableGateSet enc θ)

/-- **Universality of `H, S, CNOT, Toffoli`** (N&C Exercise 4.43). For the reachability angle `θ`
(`cos θ = 3/5`), an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of an `m`-qubit register with at least
one qubit, and *any* unitary `U ∈ U(d)`, some global phase `e^{iα}` makes `e^{iα} • U` a limit of
reachable circuits: `e^{iα} • U ∈ closure ↑(reachableCircuits enc θ)`.

In the finite-dimensional product topology on `Matrix (Fin d) (Fin d) ℂ`, closure is approximation
to arbitrary accuracy, so this is exactly: **the circuits built from `H, S, CNOT, Toffoli` are dense
in `U(d)` up to an (unobservable) global phase**. A one-line instantiation of the generic
reachable-circuit density `exists_phase_smul_mem_closure_reachableCircuitsOf`
(`Concrete/ReachableCircuits.lean`) — the shared §4.5/§4.3 assembly (decompose into terminal gates
via `exists_isToffoliOrSingleQubit_list_prod_eq`, approximate each up to a phase, combine the
phases) — at the four-gate-specific single-qubit density
`exists_phase_smul_singleQubitOnWire_mem_closure` (N&C eq. 4.81, `cos θ = 3/5`). -/
theorem exists_phase_smul_mem_closure_reachableCircuits [Nontrivial (Fin m → Fin 2)]
    {θ : ℝ} (hθ : Real.cos θ = 3 / 5) (enc : (Fin m → Fin 2) ≃ Fin d)
    {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • U
      ∈ closure (↑(reachableCircuits enc θ) : Set (Matrix (Fin d) (Fin d) ℂ)) :=
  exists_phase_smul_mem_closure_reachableCircuitsOf enc
    (exists_phase_smul_singleQubitOnWire_mem_closure hθ enc) hU

end AxQM.Concrete
