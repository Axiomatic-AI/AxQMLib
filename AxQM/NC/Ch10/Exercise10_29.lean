/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Eigenspace.StabilizedSubmodule

/-!
# Nielsen & Chuang, Exercise 10.29 — the stabilized subspace `V_S` is a subspace, and is the
intersection of the eigenvalue-one eigenspaces

*(N&C §10.5.1, p. 454.)*

V_S is a subspace (closed under linear combos) and equals intersection of eigenvalue-1 eigenspaces
of S.

## What the exercise asks, and what is proved

In the stabilizer formalism (N&C §10.5.1), `S` is a subgroup of the Pauli group `Gₙ`, and `V_S` is
defined as the set of `n`-qubit states fixed by *every* element of `S` — the vector space
*stabilized* by `S`. The exercise has two parts:

1. `V_S` is closed under linear combinations of any two of its elements, so it is a subspace.
2. `V_S` equals the intersection, over the operators `M ∈ S`, of the subspaces they fix — that is,
   of the eigenvalue-`1` eigenspaces of the elements of `S`.

Neither part uses the group structure of `S`, nor anything specific to qubits: both hold for the
common fixed-point set of an **arbitrary set of linear endomorphisms of an arbitrary module**. The
formalisation is accordingly in `ToMathlib/LinearAlgebra/Eigenspace/StabilizedSubmodule.lean`.

## Declarations

All in `ToMathlib/LinearAlgebra/Eigenspace/StabilizedSubmodule.lean`. For `S : Set (Module.End R M)`
a set of endomorphisms of a module `M` over a commutative ring `R`:

* `Module.End.stabilizedSubmodule` — the submodule `V_S = {v | ∀ f ∈ S, f v = v}` of vectors fixed
  by every element of `S`. The `Submodule` proof obligations discharged in its construction are
  exactly Exercise 10.29's first claim (closure under `+`, `0`, and scalar multiplication).
* `Module.End.mem_stabilizedSubmodule_iff` — the defining membership characterisation,
  `v ∈ V_S ↔ ∀ f ∈ S, f v = v`.
* `Module.End.smul_add_smul_mem_stabilizedSubmodule` — Exercise 10.29, part 1, stated verbatim: an
  arbitrary linear combination `c • a + d • b` of two elements of `V_S` is again in `V_S`.
* `Module.End.stabilizedSubmodule_eq_iInf_fixedSubmodule` — `V_S` is the intersection of the
  subspaces fixed by each operator in `S` (N&C's first phrasing of part 2).
* `Module.End.stabilizedSubmodule_eq_iInf_eigenspace_one` — Exercise 10.29, part 2: `V_S` is the
  intersection of the eigenvalue-`1` eigenspaces of the elements of `S`.
* `LinearMap.fixedSubmodule_eq_eigenspace_one` — the reusable bridge identifying the two phrasings
  of part 2: the subspace fixed by `f` is its eigenvalue-`1` eigenspace,
  `f.fixedSubmodule = f.eigenspace 1`.

## Faithfulness

* **Both claims, in full generality.** N&C's `V_S` is the set of states fixed by every element of
  `S`; `Module.End.stabilizedSubmodule` is that set, packaged as a `Submodule` (part 1 is the
  submodule proof, re-exposed as `smul_add_smul_mem_stabilizedSubmodule`). Part 2 is
  `stabilizedSubmodule_eq_iInf_eigenspace_one`, with the parenthetical identification of "subspace
  fixed by `M`" with "eigenvalue-`1` eigenspace of `M`" supplied by
  `fixedSubmodule_eq_eigenspace_one` and `stabilizedSubmodule_eq_iInf_fixedSubmodule`.
* **Not a weakening.** Stating the result for an arbitrary `S : Set (Module.End R M)` rather than a
  subgroup of the Pauli group is a *generalisation*, not a restriction: N&C's two claims never use
  that `S` is a subgroup, and the qubit case (`R = ℂ`, `M = ℂ^{2ⁿ}`, `S` a Pauli subgroup) is a
  special instance. A concrete, generator-indexed instantiation over the `n`-qubit register already
  exists as `AxQM.Concrete.stabilizedSubspace`; the general statement here subsumes its
  defining shape (an intersection of `+1`-eigenspaces).
-/
