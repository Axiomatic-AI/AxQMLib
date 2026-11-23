/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.Kronecker
import ToMathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Concrete: the Kronecker product packed into a single `Fin` index (`kroneckerFin`)

## Why this file

A gate acting on the first factor of a bipartite register and trivially on the second is a Kronecker
product `A ⊗ₖ B` — a matrix on the *product* index `Fin d × Fin e`. To promote it to a `quditGate`
(an `Evolution (qudit (d · e))`, whose matrices are indexed by the flat `Fin (d · e)`), the product
index must be packed into a single `Fin` via the canonical bijection `finProdFinEquiv`. This file
supplies that packed form and its two basic facts — the entrywise formula and unitarity — used by
the **`quditGate`-of-Kronecker bridge** (`AxQM/Postulates/API/QuditKroneckerGate.lean`),
which identifies `quditGate (kroneckerFin A B)` with the tensor product `quditGate A ⊗ quditGate B`
transported along the register-factoring isomorphism `quditProdIso`. That bridge is used in the
Deutsch-gate universality reduction (Nielsen & Chuang, Exercise 4.44): the
`G`-placement matrix on the first three wires of a register factors as `C²(·) ⊗ₖ 1`, so its
`quditGate` is the physical Deutsch gate tensored with the identity on the remaining wires.

## The construction and results

* `kroneckerFin A B` — the Kronecker product `A ⊗ₖ B`, reindexed along `finProdFinEquiv` on both
  axes to a matrix on the flat index `Fin (d · e)`.
* `kroneckerFin_apply` — the entrywise formula on packed indices:
  `kroneckerFin A B (finProdFinEquiv (r₁, c₁)) (finProdFinEquiv (r₂, c₂)) = A r₁ r₂ * B c₁ c₂`.
* `kroneckerFin_mem_unitaryGroup` — the Kronecker product of two unitaries, packed, is unitary
  (`Matrix.kronecker_mem_unitary` + the general `Matrix.reindex_mem_unitaryGroup`).
-/

namespace AxQM.Concrete

open Matrix
open scoped Kronecker

variable {d e : ℕ}

/-- **The Kronecker product packed into a single `Fin` index.** For square matrices `A` on `Fin d`
and `B` on `Fin e`, `kroneckerFin A B` is the Kronecker product `A ⊗ₖ B` — a matrix on the product
index `Fin d × Fin e` — reindexed along the canonical packing bijection `finProdFinEquiv` on both
axes into a matrix on the flat index `Fin (d · e)`. This is the shape a `quditGate` consumes. -/
def kroneckerFin (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin e) (Fin e) ℂ) :
    Matrix (Fin (d * e)) (Fin (d * e)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)

/-- **The entrywise formula for `kroneckerFin` on packed indices.** The entry of `kroneckerFin A B`
at row `finProdFinEquiv (r₁, c₁)` and column `finProdFinEquiv (r₂, c₂)` is the product of the
corresponding entries `A r₁ r₂ * B c₁ c₂`, exactly the Kronecker product's entry read through the
packing bijection. -/
theorem kroneckerFin_apply (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin e) (Fin e) ℂ)
    (r₁ : Fin d) (c₁ : Fin e) (r₂ : Fin d) (c₂ : Fin e) :
    kroneckerFin A B (finProdFinEquiv (r₁, c₁)) (finProdFinEquiv (r₂, c₂)) = A r₁ r₂ * B c₁ c₂ := by
  rw [kroneckerFin, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.kronecker_apply]

/-- **The packed Kronecker product of two unitaries is unitary.** `kroneckerFin A B ∈
unitaryGroup (Fin (d · e)) ℂ` whenever `A`, `B` are unitary — the Kronecker product of unitaries is
unitary (`Matrix.kronecker_mem_unitary`) and reindexing preserves it
(`Matrix.reindex_mem_unitaryGroup`). -/
theorem kroneckerFin_mem_unitaryGroup {A : Matrix (Fin d) (Fin d) ℂ} {B : Matrix (Fin e) (Fin e) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin e) ℂ) :
    kroneckerFin A B ∈ Matrix.unitaryGroup (Fin (d * e)) ℂ :=
  Matrix.reindex_mem_unitaryGroup finProdFinEquiv (Matrix.kronecker_mem_unitary hA hB)

end AxQM.Concrete
