/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# The submodule stabilized by a set of endomorphisms

Given a set `S` of endomorphisms of a module `M`, the vectors that are fixed by *every* element of
`S` form a submodule of `M`. This file introduces that submodule and records its two basic
descriptions.

## Main definitions

* `Module.End.stabilizedSubmodule S`: the submodule `{v | ∀ f ∈ S, f v = v}` of vectors fixed by
  every endomorphism in `S`.

## Main results

* `Module.End.smul_add_smul_mem_stabilizedSubmodule`: `stabilizedSubmodule S` is closed under linear
  combinations of pairs of its elements — the concrete form of it being a submodule.
* `Module.End.stabilizedSubmodule_eq_iInf_fixedSubmodule`: `stabilizedSubmodule S` is the
  intersection of the fixed submodules of the elements of `S`.
* `LinearMap.fixedSubmodule_eq_eigenspace_one`: the fixed submodule of a single endomorphism is its
  eigenvalue-`1` eigenspace, `f.fixedSubmodule = f.eigenspace 1`.
* `Module.End.stabilizedSubmodule_eq_iInf_eigenspace_one`: `stabilizedSubmodule S` is the
  intersection of the eigenvalue-`1` eigenspaces of the elements of `S`.

The definition and the first two results only need a semiring of scalars; the eigenspace
reformulation needs a commutative ring, as `Module.End.eigenspace` does.

These facts are the abstract content of the stabilizer formalism from quantum information theory
(Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 10.29): for a subgroup
`S` of the Pauli group, the *stabilized subspace* `V_S` is a subspace of the state space, equal to
the intersection of the `+1`-eigenspaces of the elements of `S`. Here we prove the statements in
full generality for an arbitrary *set* of endomorphisms of an arbitrary module, of which the
Pauli-group case is a special instance.
-/

@[expose] public section

namespace Module.End

section Semiring

variable {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- The submodule stabilized by a set `S` of endomorphisms of `M`: the vectors fixed by every
element of `S`. In the stabilizer formalism (Nielsen & Chuang, §10.5.1) this is the vector space
`V_S` stabilized by `S`. -/
def stabilizedSubmodule (S : Set (Module.End R M)) : Submodule R M where
  carrier := {v | ∀ f ∈ S, f v = v}
  add_mem' {a b} ha hb f hf := by rw [map_add, ha f hf, hb f hf]
  zero_mem' f _ := map_zero f
  smul_mem' c a ha f hf := by rw [map_smul, ha f hf]

@[simp]
theorem mem_stabilizedSubmodule_iff {S : Set (Module.End R M)} {v : M} :
    v ∈ stabilizedSubmodule S ↔ ∀ f ∈ S, f v = v := Iff.rfl

/-- An arbitrary linear combination `c • a + d • b` of two elements `a, b` of the stabilized
submodule `V_S` again lies in `V_S`; hence `V_S` is a subspace of `M`. This is the first part of
Nielsen & Chuang, Exercise 10.29. -/
theorem smul_add_smul_mem_stabilizedSubmodule (S : Set (Module.End R M)) {a b : M}
    (ha : a ∈ stabilizedSubmodule S) (hb : b ∈ stabilizedSubmodule S) (c d : R) :
    c • a + d • b ∈ stabilizedSubmodule S :=
  add_mem (Submodule.smul_mem _ c ha) (Submodule.smul_mem _ d hb)

/-- The stabilized submodule `V_S` is the intersection of the fixed submodules of the individual
elements of `S`. -/
theorem stabilizedSubmodule_eq_iInf_fixedSubmodule (S : Set (Module.End R M)) :
    stabilizedSubmodule S = ⨅ f ∈ S, LinearMap.fixedSubmodule f := by
  ext v
  simp only [mem_stabilizedSubmodule_iff, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff]

end Semiring

end Module.End

section CommRing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

namespace LinearMap

/-- The fixed submodule of an endomorphism `f` is its eigenvalue-`1` eigenspace: both consist of the
vectors `v` with `f v = v`. -/
theorem fixedSubmodule_eq_eigenspace_one (f : Module.End R M) :
    LinearMap.fixedSubmodule f = Module.End.eigenspace f 1 := by
  ext v
  rw [LinearMap.mem_fixedSubmodule_iff, Module.End.mem_eigenspace_iff, one_smul]

end LinearMap

namespace Module.End

/-- The stabilized submodule `V_S` is the intersection of the eigenvalue-`1` eigenspaces of the
elements of `S`. This is the second part of Nielsen & Chuang, Exercise 10.29. -/
theorem stabilizedSubmodule_eq_iInf_eigenspace_one (S : Set (Module.End R M)) :
    stabilizedSubmodule S = ⨅ f ∈ S, Module.End.eigenspace f 1 := by
  simp_rw [stabilizedSubmodule_eq_iInf_fixedSubmodule, LinearMap.fixedSubmodule_eq_eigenspace_one]

end Module.End

end CommRing
