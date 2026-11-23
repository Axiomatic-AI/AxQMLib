/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrix
import AxQM.Concrete.NineQubitCode
import ToMathlib.LinearAlgebra.FiniteDimensional.SpanRangeEq
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete: the nine-qubit Shor code check matrix in standard form (Nielsen & Chuang, Ex 10.57)

This file is a finite `ZMod 2` / `Fin 4` check-matrix computation. It is the second half of
Nielsen & Chuang, **Exercise 10.57** —
*give the check matrices for the five and nine qubit codes in standard form* (N&C §10.5.7, p. 472).
The five-qubit half is `Concrete/FiveQubitStandardForm.lean`; this file is the nine-qubit Shor code.

## The standard form (N&C eq. (10.111))

For an `[n, k]` stabilizer code with `r` the rank of the `X`-part of the check matrix and
`m = n − k − r`, Gaussian elimination (relabeling generators = row swaps, multiplying generators =
row additions, relabeling qubits = column swaps) brings the `(n − k) × 2n` check matrix into the
block **standard form**
```
        r    m    k  ┃  r    m    k
   r  [ I    A₁   A₂ ┃  B    0    C  ]
   m  [ 0    0    0  ┃  D    I    E  ]
```
(eq. (10.111); the left half is the `X`-part, the right half the `Z`-part). The four *fixed* blocks
are the `r × r` identity (top-left `X`), the zero `X`-part of the bottom `m` rows, the zero middle
`Z`-block of the top `r` rows, and the `m × m` identity (bottom-middle `Z`); `A₁, A₂, B, C, D, E`
are free.

## The nine-qubit Shor code (Figure 10.11)

The Shor code `[[9, 1, 3]]` has the eight generators of Figure 10.11 (`shorGenIdx`):
```
g₁ = Z₁Z₂   g₂ = Z₂Z₃   g₃ = Z₄Z₅   g₄ = Z₅Z₆   g₅ = Z₇Z₈   g₆ = Z₈Z₉
g₇ = X₁X₂X₃X₄X₅X₆        g₈ = X₄X₅X₆X₇X₈X₉
```
Here `n = 9`, `k = 1`, and the `X`-part (nonzero only on the two `X`-type rows `g₇, g₈`) has rank
`r = 2`, so `m = n − k − r = 6`: unlike the (full `X`-rank) five-qubit code, the Shor code needs the
full bottom `[0 0 0 | D I E]` block **and** a genuine qubit relabeling — no two of the first columns
carry an `X`-pivot of both `g₇` and `g₈`.

The reduction. The two `X`-pivot columns are original qubits `1` (in `g₇` only) and `7` (in `g₈`
only); the six `Z`-pivot columns are qubits `2,3,4,5,8,9`; the free (`k`) column is qubit `6`.
Relabeling the qubits into the order `(1,7,2,3,4,5,8,9,6)` (`shorStdSwap`) and row-reducing gives
the standard-form generators `shorStdGen`:
```
s₁ = g₇                s₃ = g₁        s₅ = g₃g₄      s₇ = g₅
s₂ = g₈                s₄ = g₁g₂      s₆ = g₄        s₈ = g₅g₆
```
whose check matrix `[[I₂ A₁ A₂ | 0 0 0] ; [0 0 0 | D I₆ E]]` reads (X-part ┃ Z-part), in the
relabeled ordering:
```
   1 0 1 1 1 1 0 0 1 ┃ 0 0 0 0 0 0 0 0 0
   0 1 0 0 1 1 1 1 1 ┃ 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 ┃ 1 0 1 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 ┃ 1 0 0 1 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 ┃ 0 0 0 0 1 0 0 0 1
   0 0 0 0 0 0 0 0 0 ┃ 0 0 0 0 0 1 0 0 1
   0 0 0 0 0 0 0 0 0 ┃ 0 1 0 0 0 0 1 0 0
   0 0 0 0 0 0 0 0 0 ┃ 0 1 0 0 0 0 0 1 0
```
so `A₁ = [[1,1,1,1,0,0],[0,0,1,1,1,1]]`, `A₂ = (1,1)ᵀ`, `B = C = 0` (the top rows are pure `X`),
`D = [[1,0],[1,0],[0,0],[0,0],[0,1],[0,1]]`, `E = (0,0,1,1,0,0)ᵀ`.

## What is proved

* `shorGenIdx`, `shorStdGen` — the Figure-10.11 generators and their standard form,
  as `Fin 9 → Fin 4` Pauli-index strings (`I=0, X=1, Y=2, Z=3`).
* `shorStdGen_xPart_pivot_identity`, `shorStdGen_bottom_xPart_zero`, `shorStdGen_top_zPart_zero`,
  `shorStdGen_zPart_middle_identity` — the certificate that it **is in standard form** (10.111): the
  four fixed blocks — the top-left `I₂`, the zero `X`-part of the bottom six rows, the zero `Z`-part
  of the top two rows (which also witnesses `B = C = 0`), and the bottom-middle `I₆`.
* `shorStdGen_checkRow_span_eq` — the certificate that it is **the same code**: undoing the qubit
  relabeling (`shorStdGenOriginal`), the `𝔽₂`-span of the standard-form check rows equals that of
  the original Figure-10.11 generators' check rows. Since a stabilizer code is exactly the row space
  of its check matrix, this says the standard form (in the relabeled ordering) and the textbook
  generators define the same Shor code.

The "same code" argument reuses the general row-space lemma
`Submodule.span_range_eq_of_le_of_linearIndependent` (span equality from one inclusion plus linear
independence of both sides, via `finrank`) — exactly as for the five-qubit code. The forward
inclusion writes each relabeled standard generator's check row as the `𝔽₂`-sum (Pauli product) of
the originals
(`s₃ = g₁`, `s₄ = g₁g₂`, `s₅ = g₃g₄`, `s₆ = g₄`, `s₇ = g₅`, `s₈ = g₅g₆`, `s₁ = g₇`, `s₂ = g₈`).
-/

open Matrix

open scoped BigOperators

set_option maxRecDepth 4000

namespace AxQM.Concrete

/-! ### The nine-qubit Shor code and its standard form -/

-- The eight Figure-10.11 generators `shorGenIdx : Fin 8 → (Fin 9 → Fin 4)` are the canonical
-- generator data of `AxQM.Concrete.NineQubitCode` (imported above); this file reuses that
-- single source of truth rather than redefining it (both are the identical index vectors).

/-- **The nine-qubit Shor code check matrix in standard form** (Nielsen & Chuang, Exercise 10.57),
as eight `Fin 9 → Fin 4` Pauli-index strings in the relabeled qubit ordering `(1,7,2,3,4,5,8,9,6)`:
```
s₁ = X . X X X X . . X      s₅ = . . . . Z . . . Z
s₂ = . X . . X X X X X      s₆ = . . . . . Z . . Z
s₃ = Z . Z . . . . . .      s₇ = . Z . . . . Z . .
s₄ = Z . . Z . . . . .      s₈ = . Z . . . . . Z .
```
These are the Figure-10.11 generators after the qubit relabeling `shorStdSwap` and Gaussian
elimination to `r = 2`, `m = 6`, `k = 1`: `s₁ = g₇`, `s₂ = g₈`, `s₃ = g₁`, `s₄ = g₁g₂`, `s₅ = g₃g₄`,
`s₆ = g₄`, `s₇ = g₅`, `s₈ = g₅g₆`. The `X`-part of the top two rows is `[I₂ A₁ A₂]` and the `Z`-part
of the bottom six is `[D I₆ E]`. -/
def shorStdGen : Fin 8 → Fin 9 → Fin 4 :=
  ![![1, 0, 1, 1, 1, 1, 0, 0, 1], ![0, 1, 0, 0, 1, 1, 1, 1, 1], ![3, 0, 3, 0, 0, 0, 0, 0, 0],
    ![3, 0, 0, 3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 0, 0, 0, 3], ![0, 0, 0, 0, 0, 3, 0, 0, 3],
    ![0, 3, 0, 0, 0, 0, 3, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 3, 0]]

/-- The **qubit relabeling** of Nielsen & Chuang §10.5.7 that brings the Shor code into standard
form: the column permutation reordering the nine qubits as `(1,7,2,3,4,5,8,9,6)` — the two `X`-pivot
columns (original qubits `1, 7`) first, the six `Z`-pivot columns (`2,3,4,5,8,9`) in the middle, the
single free `k`-column (`6`) last. As a `0`-indexed permutation of `Fin 9` it is the eight-cycle
`(1 2 3 4 5 8 7 6)` (fixing `0`), i.e. it sends each original qubit position to its position in the
standard-form ordering. Composing with `shorStdGen` sends a relabeled standard string back to the
original code by precomposition (`shorStdGenOriginal`). -/
def shorStdSwap : Equiv.Perm (Fin 9) := List.formPerm ([1, 2, 3, 4, 5, 8, 7, 6] : List (Fin 9))

/-- The **standard-form Shor generators translated back to the original qubit ordering**: each
`shorStdGen i` reindexed by the relabeling `shorStdSwap` (precomposition undoes the column swaps).
In the original ordering these are exactly the `𝔽₂`-products of the Figure-10.11 generators
(`s₃ = g₁`, `s₄ = g₁g₂`, …), so they generate the same code — the content of
`shorStdGen_checkRow_span_eq`. -/
def shorStdGenOriginal (i : Fin 8) : Fin 9 → Fin 4 := fun k => shorStdGen i (shorStdSwap k)

/-- **The Shor standard form is in standard form** (N&C eq. (10.111)), fixed block 1 — the top-left
`X`-identity: the `X`-part of the top `r = 2` rows, restricted to the first `r = 2` (pivot) columns,
is the `2 × 2` identity — row `i` has a `1` in pivot column `j` iff `i = j`. -/
theorem shorStdGen_xPart_pivot_identity (i : Fin 8) (j : Fin 9) (hi : i.val ≤ 1) (hj : j.val ≤ 1) :
    (checkRow (shorStdGen i)).1 j = if i.val = j.val then 1 else 0 := by
  revert hi hj; fin_cases i <;> fin_cases j <;> decide

/-- **The Shor standard form is in standard form** (N&C eq. (10.111)), fixed block 2 — the zero
`X`-part of the bottom rows: the bottom `m = 6` rows (the pure-`Z` generators) have vanishing
`X`-part `[0 0 0]`. -/
theorem shorStdGen_bottom_xPart_zero (i : Fin 8) (hi : 2 ≤ i.val) :
    (checkRow (shorStdGen i)).1 = 0 := by
  revert hi; fin_cases i <;> decide

/-- **The Shor standard form is in standard form** (N&C eq. (10.111)), fixed block 3 — the zero
middle `Z`-block of the top rows: the top `r = 2` rows (the pure-`X` generators) have vanishing
`Z`-part. This includes the required middle `0` block `[B 0 C]`, and moreover witnesses `B = C = 0`
for the Shor code (its `X`-type generators carry no `Z`). -/
theorem shorStdGen_top_zPart_zero (i : Fin 8) (hi : i.val ≤ 1) :
    (checkRow (shorStdGen i)).2 = 0 := by
  revert hi; fin_cases i <;> decide

/-- **The Shor standard form is in standard form** (N&C eq. (10.111)), fixed block 4 — the
bottom-middle `Z`-identity: the `Z`-part of the bottom `m = 6` rows, restricted to the middle
`m = 6` columns (indices `2,…,7`), is the `6 × 6` identity — row `i` has a `1` in middle column `j`
iff `i = j`. Together with the three preceding blocks this is the full standard-form shape of the
check matrix. -/
theorem shorStdGen_zPart_middle_identity (i : Fin 8) (j : Fin 9)
    (hi : 2 ≤ i.val) (hj1 : 2 ≤ j.val) (hj2 : j.val ≤ 7) :
    (checkRow (shorStdGen i)).2 j = if i.val = j.val then 1 else 0 := by
  revert hi hj1 hj2; fin_cases i <;> fin_cases j <;> decide

/-- The check-matrix rows of the Figure-10.11 Shor generators are `ZMod 2`-linearly independent (the
eight generators of the `[[9,1]]` code are independent, Proposition 10.3). -/
theorem shorGen_checkRow_linearIndependent :
    LinearIndependent (ZMod 2) (fun i => checkRow (shorGenIdx i)) := by
  rw [Fintype.linearIndependent_iff]; decide

/-- The standard-form check rows of the Shor code (in the original ordering, `shorStdGenOriginal`)
are `ZMod 2`-linearly independent — eight independent generators of the `[[9,1]]` code. -/
theorem shorStdGenOriginal_checkRow_linearIndependent :
    LinearIndependent (ZMod 2) (fun i => checkRow (shorStdGenOriginal i)) := by
  rw [Fintype.linearIndependent_iff]; decide

/-- **Nielsen & Chuang, Exercise 10.57 (nine-qubit Shor code): the standard form defines the same
code.** After undoing the qubit relabeling (`shorStdGenOriginal`), the `𝔽₂`-span of the
standard-form check rows equals the span of the original Figure-10.11 generators' check rows. A
stabilizer code is exactly the row space of its check matrix, so this certifies that the
standard-form check matrix is a check matrix of the Shor code (up to the qubit relabeling
`shorStdSwap` that §10.5.7's column swaps perform).

The forward inclusion writes each relabeled standard generator's check row as the `𝔽₂`-sum (Pauli
product) of the originals — `s₁ = g₇`, `s₂ = g₈`, `s₃ = g₁`, `s₄ = g₁g₂`, `s₅ = g₃g₄`, `s₆ = g₄`,
`s₇ = g₅`, `s₈ = g₅g₆` — and both families are linearly independent, so the inclusion is an equality
(`Submodule.span_range_eq_of_le_of_linearIndependent`). -/
theorem shorStdGen_checkRow_span_eq :
    Submodule.span (ZMod 2) (Set.range (fun i => checkRow (shorStdGenOriginal i)))
      = Submodule.span (ZMod 2) (Set.range (fun i => checkRow (shorGenIdx i))) := by
  refine Submodule.span_range_eq_of_le_of_linearIndependent ?_
    shorGen_checkRow_linearIndependent shorStdGenOriginal_checkRow_linearIndependent
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe]
  fin_cases i
  · exact Submodule.subset_span ⟨6, by decide⟩
  · exact Submodule.subset_span ⟨7, by decide⟩
  · exact Submodule.subset_span ⟨0, by decide⟩
  · change checkRow (shorStdGenOriginal 3) ∈ _
    rw [show checkRow (shorStdGenOriginal 3)
        = checkRow (shorGenIdx 0) + checkRow (shorGenIdx 1) from by decide]
    exact add_mem (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩)
  · change checkRow (shorStdGenOriginal 4) ∈ _
    rw [show checkRow (shorStdGenOriginal 4)
        = checkRow (shorGenIdx 2) + checkRow (shorGenIdx 3) from by decide]
    exact add_mem (Submodule.subset_span ⟨2, rfl⟩) (Submodule.subset_span ⟨3, rfl⟩)
  · exact Submodule.subset_span ⟨3, by decide⟩
  · exact Submodule.subset_span ⟨4, by decide⟩
  · change checkRow (shorStdGenOriginal 7) ∈ _
    rw [show checkRow (shorStdGenOriginal 7)
        = checkRow (shorGenIdx 4) + checkRow (shorGenIdx 5) from by decide]
    exact add_mem (Submodule.subset_span ⟨4, rfl⟩) (Submodule.subset_span ⟨5, rfl⟩)

end AxQM.Concrete
