/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerIndependence
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Concrete: Nielsen & Chuang Exercise 10.53 — the encoded `Z` operators are independent

This file formalizes Nielsen & Chuang's
**Exercise 10.53** (§10.5.7, p. 471), that the `k` encoded `Z` operators read off the *standard
form* of a stabilizer code's check matrix are **independent of one another**.

Prove the encoded Z operators (from standard-form check matrix) are independent of one another.

## The setup (standard form, §10.5.7)

For an `[n, k]` stabilizer code, Gaussian elimination puts the check matrix into the **standard
form** (10.111), whose `X`-part has rank `r`; the `n` qubits split into three blocks of sizes
`r`, `n − k − r` and `k`. Nielsen & Chuang then define the `k` **encoded `Z` operators** by the
`k × 2n` check matrix `G_Z = [0 0 0 | A₂ᵀ 0 I]` (their display just above Exercise 10.53): every
encoded `Z` operator is a *pure* product of `Z`'s (its `X`-part vanishes), and its `Z`-part is the
`j`-th row of `[A₂ᵀ 0 I]` — the transpose block `A₂ᵀ` (`k × r`) on the first block of qubits, `0` on
the middle `n − k − r`, and the `k × k` identity `I` on the last `k` ("data") qubits. Here `A₂` is
the `r × k` block appearing as `[I A₁ A₂]` in the top rows of the standard form (10.111); it is an
arbitrary `𝔽₂`-matrix, so the development below is for a *general* standard-form code, not a fixed
example.

## What is proved, and why it is independence

**Independence** of a set of stabilizer/Pauli operators is Nielsen & Chuang's eq. (10.82): dropping
any one of them strictly shrinks the group they generate (`Concrete.IndependentGenerators`). By
**Proposition 10.3** the operators are independent exactly when the rows of their check matrix are
`𝔽₂`-linearly independent — and Nielsen & Chuang's point in this passage is that the identity block
`I` on the data qubits makes the encoded-`Z` rows manifestly independent: reading a row off the last
`k` (data) columns returns the standard basis vector `eⱼ`, and the standard basis is linearly
independent, whatever the `A₂ᵀ 0` blocks are.

We package this faithfully at the operator level:

* `encodedZRow s A₂ j` — the `Z`-support of the `j`-th encoded `Z` operator, the `j`-th row of
  `[A₂ᵀ 0 I]` as a vector `Fin (r + s + k) → ZMod 2` (built with `Fin.append`, `s = n − k − r`).
* `encodedZOp s A₂ j : PauliGroup (r + s + k)` — the operator itself, the pure-`Z` Pauli group
  element with phase `1` and index `zIndexOf (encodedZRow s A₂ j)` (a `Z` on each qubit in the
  support, `I` elsewhere). Its check row is `(0 | encodedZRow s A₂ j)` (`encodedZOp_checkRowHom`).
* `encodedZRow_linearIndependent` — the rows are `𝔽₂`-linearly independent: composing with
  "restrict to the last `k` data qubits" (`LinearMap.funLeft … (Fin.natAdd (r + s))`) sends row `j`
  to `eⱼ = Pi.single j 1` (the identity block, via `Fin.append_right`), and the standard basis
  `Pi.basisFun` is linearly independent, so the rows are too (`LinearIndependent.of_comp`).
* `encodedZOp_checkRow_linearIndependent` — hence the check rows `checkRowHom (encodedZOp s A₂ j)`
  are linearly independent (the `X`-part is uniformly `0`, so this is the row independence again).
* `encodedZOp_independentGenerators` — **Exercise 10.53 itself**: the encoded `Z` operators are
  independent, `IndependentGenerators (encodedZOp s A₂)`. This is the "easy half" of Proposition
  10.3 (`independentGenerators_of_linearIndependent_of_hom`: linearly independent check rows force
  independent generators, using only that the check row `PauliGroup.checkRowHom` is additive — no
  `-I ∉ S` hypothesis is needed for this direction).

These are the statements of Exercise 10.53.
-/

open scoped Matrix

namespace AxQM.Concrete

variable {r k : ℕ}

/-! ### A pure-`Z` Pauli string from a `ZMod 2` support -/

/-- The **pure-`Z` Pauli-string index** with support `w`: `Z` (index `3`) on each qubit `q` where
`w q ≠ 0`, and `I` (index `0`) elsewhere. Its check row is `(0 | w)` (`checkRow_zIndexOf`): an
all-`Z` string has no `X`-part, and its `Z`-part is exactly the support `w`. -/
def zIndexOf {n : ℕ} (w : Fin n → ZMod 2) : Fin n → Fin 4 := fun q => if w q = 0 then 0 else 3

/-- The check row of a pure-`Z` string is `(0 | w)`: the `X`-part vanishes (a product of `Z`'s and
`I`'s has no `X`/`Y` factor) and the `Z`-part is the support `w`. A per-qubit case check on the two
values `0`/`3` of `zIndexOf`. -/
theorem checkRow_zIndexOf {n : ℕ} (w : Fin n → ZMod 2) : checkRow (zIndexOf w) = (0, w) := by
  have h : ∀ x : ZMod 2, pauliBit (if x = 0 then (0 : Fin 4) else 3) = (0, x) := by decide
  refine Prod.ext ?_ ?_ <;> funext q
  · exact congrArg Prod.fst (h (w q))
  · exact congrArg Prod.snd (h (w q))

/-! ### The encoded `Z` operators of a standard-form code -/

/-- The **`Z`-support of the `j`-th encoded `Z` operator**, i.e. the `j`-th row of the `Z`-part
`[A₂ᵀ 0 I]` of the encoded-`Z` check matrix (Nielsen & Chuang §10.5.7): the transpose column
`A₂ᵀ_{j·} = (i ↦ A₂ i j)` on the first `r` qubits, `0` on the middle `s = n − k − r` qubits, and the
standard basis vector `eⱼ = Pi.single j 1` (the identity block) on the last `k` data qubits. -/
def encodedZRow (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) (j : Fin k) :
    Fin (r + s + k) → ZMod 2 :=
  Fin.append (Fin.append (fun i => A₂ i j) (0 : Fin s → ZMod 2)) (Pi.single j 1)

/-- The **`j`-th encoded `Z` operator** of a standard-form `[n, k]` code (Nielsen & Chuang §10.5.7),
as an `n`-qubit Pauli-group element (`n = r + s + k`): the pure product of `Z`'s with phase `1` and
`Z`-support `encodedZRow s A₂ j`. -/
def encodedZOp (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) (j : Fin k) :
    PauliGroup (r + s + k) :=
  ⟨0, zIndexOf (encodedZRow s A₂ j)⟩

/-- Reading the encoded-`Z` rows off the last `k` data qubits returns the standard basis: the
`Z`-support `encodedZRow s A₂ j`, restricted (precomposed with `Fin.natAdd (r + s)`) to the last
`k` qubits, is `eⱼ = Pi.single j 1` — the identity block `I` of `[A₂ᵀ 0 I]`. -/
theorem encodedZRow_comp_natAdd (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) (j : Fin k) :
    (encodedZRow s A₂ j) ∘ (Fin.natAdd (r + s)) = Pi.single j 1 := by
  funext i
  exact Fin.append_right _ _ i

/-- **The encoded-`Z` rows are `𝔽₂`-linearly independent** — the linear-algebra heart of Exercise
10.53. Restriction to the last `k` (data) qubits is the linear map
`LinearMap.funLeft … (Fin.natAdd (r + s))`; it carries row `j` to the standard basis vector
`eⱼ = Pi.single j 1` (`encodedZRow_comp_natAdd`, the identity block `I`), i.e. carries the family of
rows to `Pi.basisFun`, which is linearly independent. Hence the rows themselves are linearly
independent (`LinearIndependent.of_comp`), regardless of the `A₂ᵀ 0` blocks. -/
theorem encodedZRow_linearIndependent (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) :
    LinearIndependent (ZMod 2) (encodedZRow s A₂) := by
  refine LinearIndependent.of_comp (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd (r + s))) ?_
  have hcomp : ⇑(LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd (r + s))) ∘ encodedZRow s A₂
      = ⇑(Pi.basisFun (ZMod 2) (Fin k)) := by
    funext j i
    simp only [Function.comp_apply, LinearMap.funLeft_apply, Pi.basisFun_apply]
    exact congrFun (encodedZRow_comp_natAdd s A₂ j) i
  rw [hcomp]
  exact (Pi.basisFun (ZMod 2) (Fin k)).linearIndependent

/-- The **check row of the `j`-th encoded `Z` operator** is `(0 | encodedZRow s A₂ j)`: it is a
pure-`Z` string, so its `X`-part vanishes and its `Z`-part is the encoded-`Z` row. -/
theorem encodedZOp_checkRowHom (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) (j : Fin k) :
    PauliGroup.checkRowHom (encodedZOp s A₂ j) = (0, encodedZRow s A₂ j) := by
  simp only [PauliGroup.checkRowHom_apply, encodedZOp]
  exact checkRow_zIndexOf _

/-- **The check rows of the encoded `Z` operators are `𝔽₂`-linearly independent** (the hypothesis of
Proposition 10.3 for these operators). Their check rows are `(0 | encodedZRow s A₂ j)`
(`encodedZOp_checkRowHom`), whose second components are linearly independent
(`encodedZRow_linearIndependent`); projecting to the `Z`-part (`LinearMap.snd`) transfers this to
the check rows themselves (`LinearIndependent.of_comp`). -/
theorem encodedZOp_checkRow_linearIndependent (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) :
    LinearIndependent (ZMod 2) (fun j => PauliGroup.checkRowHom (encodedZOp s A₂ j)) := by
  have h : (fun j => PauliGroup.checkRowHom (encodedZOp s A₂ j))
      = fun j => ((0 : Fin (r + s + k) → ZMod 2), encodedZRow s A₂ j) :=
    funext fun j => encodedZOp_checkRowHom s A₂ j
  rw [h]
  refine LinearIndependent.of_comp
    (LinearMap.snd (ZMod 2) (Fin (r + s + k) → ZMod 2) (Fin (r + s + k) → ZMod 2)) ?_
  have hcomp : ⇑(LinearMap.snd (ZMod 2) (Fin (r + s + k) → ZMod 2) (Fin (r + s + k) → ZMod 2)) ∘
      (fun j => ((0 : Fin (r + s + k) → ZMod 2), encodedZRow s A₂ j)) = encodedZRow s A₂ := by
    funext j
    simp only [Function.comp_apply, LinearMap.snd_apply]
  rw [hcomp]
  exact encodedZRow_linearIndependent s A₂

/-- **Nielsen & Chuang, Exercise 10.53.** The `k` encoded `Z` operators of a standard-form `[n, k]`
stabilizer code are **independent of one another** (`IndependentGenerators`, N&C eq. 10.82: dropping
any one strictly shrinks the group generated). This is the "easy half" of Proposition 10.3 applied
to the encoded-`Z` operators: their check rows are linearly independent
(`encodedZOp_checkRow_linearIndependent`, from the identity block `I` of `[A₂ᵀ 0 I]`) and the check
row `PauliGroup.checkRowHom` is additive (`PauliGroup.checkRowHom_mul`), so the operators are
independent — no `-I ∉ S` hypothesis is required for this direction. -/
theorem encodedZOp_independentGenerators (s : ℕ) (A₂ : Matrix (Fin r) (Fin k) (ZMod 2)) :
    IndependentGenerators (encodedZOp s A₂) :=
  independentGenerators_of_linearIndependent_of_hom PauliGroup.checkRowHom
    PauliGroup.checkRowHom_mul (encodedZOp s A₂) (encodedZOp_checkRow_linearIndependent s A₂)

end AxQM.Concrete
