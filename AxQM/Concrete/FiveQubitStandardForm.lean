/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.FiveQubitCode
import ToMathlib.LinearAlgebra.FiniteDimensional.SpanRangeEq
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete: the five-qubit code check matrix in standard form (Nielsen & Chuang, Exercise 10.57)

This file is a finite `ZMod 2` check-matrix computation. It is the first half of Nielsen &
Chuang, **Exercise 10.57** — *give the check matrices for the five and nine qubit codes in
standard form* (N&C §10.5.7, p. 472).

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
(eq. (10.111); the left half is the `X`-part, the right half the `Z`-part).

## The five-qubit code (Figure 10.12)

The five-qubit code `[[5, 1, 3]]` has the four generators `g₁ = XZZXI`, `g₂ = IXZZX`, `g₃ = XIXZZ`,
`g₄ = ZXIXZ` (`Concrete.fiveQubitGenIdx`). Its `X`-part has **full rank** `r = 4 = n − k`, so
`m = n − k − r = 0`: the standard form has **no** bottom `[0 0 0 | D I E]` block, and the four
qubits `1,2,3,4` are already pivot columns (no qubit swap is needed, unlike the Steane code). Row-
reducing the `X`-part to `[I₄ | A₂]` gives the standard-form generators

* `s₁ = g₁ g₂ g₄ = Y Z I Z Y`, `s₂ = g₂ = I X Z Z X`, `s₃ = g₁ g₂ g₃ g₄ = Z Z X I X`,
  `s₄ = g₂ g₄ = Z I Z Y Y` (`fiveQubitStdGen`),

whose check matrix `[[I₄ A₂ | B C]]` reads (X-part ┃ Z-part), with `A₂ = (1,1,1,1)ᵀ`:
```
   1 0 0 0 1 ┃ 1 1 0 1 1
   0 1 0 0 1 ┃ 0 0 1 1 0
   0 0 1 0 1 ┃ 1 1 0 0 0
   0 0 0 1 1 ┃ 1 0 1 1 1
```

## What is proved

* `fiveQubitStdGen` — the four standard-form generators, as `Fin 5 → Fin 4` Pauli-index strings
  (`I=0, X=1, Y=2, Z=3`): **the check matrix in standard form**.
* `fiveQubitStdGen_xPart_pivot_identity` — the certificate that it **is in standard form**: the
  `X`-part restricted to the first `r = 4` (pivot) columns is the `4 × 4` identity `I₄`.
* `fiveQubitStdGen_checkRow_span_eq` — the certificate that it is **the same code**: the `𝔽₂`-span
  of the standard-form check rows equals that of the original Figure-10.12 generators' check rows
  (no qubit relabeling is needed here). Since a stabilizer code is exactly the row space of its
  check matrix, this says the standard form and the textbook generators define the same five-qubit
  code.

The "same code" argument is the general row-space lemma
`Submodule.span_range_eq_of_le_of_linearIndependent` (span equality from one inclusion plus linear
independence of both sides, via `finrank`), which is pure linear algebra and is reused for the
nine-qubit code.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

/-! ### The five-qubit code in standard form -/

/-- **The five-qubit code check matrix in standard form** (Nielsen & Chuang, Exercise 10.57), as
four `Fin 5 → Fin 4` Pauli-index strings (`I=0, X=1, Y=2, Z=3`):
```
s₁ = Y Z I Z Y      s₃ = Z Z X I X
s₂ = I X Z Z X      s₄ = Z I Z Y Y
```
These are the Figure-10.12 generators after Gaussian elimination of the (full-rank) `X`-part to
`[I₄ | A₂]`, so `r = 4`, `m = 0`, `k = 1` (no `[0 0 0 | D I E]` block, no qubit swap):
`s₁ = g₁g₂g₄`, `s₂ = g₂`, `s₃ = g₁g₂g₃g₄`, `s₄ = g₂g₄`, with `A₂ = (1,1,1,1)ᵀ` the encoded
column. -/
def fiveQubitStdGen : Fin 4 → Fin 5 → Fin 4 :=
  ![![2, 3, 0, 3, 2], ![0, 1, 3, 3, 1], ![3, 3, 1, 0, 1], ![3, 0, 3, 2, 2]]

/-- **The five-qubit standard form is in standard form** (N&C eq. (10.111)): the `X`-part of the
check matrix, restricted to the first `r = 4` (pivot) columns, is the `4 × 4` identity — row `i` has
a `1` in pivot column `j` iff `i = j`. Since `m = n − k − r = 0` there is no middle block and no
bottom `[0 0 0 | D I E]` rows, so this identity block is the full standard-form shape condition on
the `X`-part. -/
theorem fiveQubitStdGen_xPart_pivot_identity (i : Fin 4) (j : Fin 5) (hj : j.val ≤ 3) :
    (checkRow (fiveQubitStdGen i)).1 j = if i.val = j.val then 1 else 0 := by
  revert hj; fin_cases i <;> fin_cases j <;> decide

/-- The standard-form check rows of the five-qubit code are `𝔽₂`-linearly independent (four
independent generators of the `[[5,1]]` code). -/
theorem fiveQubitStdGen_checkRow_linearIndependent :
    LinearIndependent (ZMod 2) (fun i => checkRow (fiveQubitStdGen i)) := by
  rw [Fintype.linearIndependent_iff]; decide

/-- **Nielsen & Chuang, Exercise 10.57 (five-qubit code): the standard form defines the same code.**
The `𝔽₂`-span of the standard-form check rows `fiveQubitStdGen` equals the span of the original
Figure-10.12 generators' check rows. A stabilizer code is exactly the row space of its check matrix,
so this certifies that the standard-form check matrix is a check matrix of the five-qubit code (no
qubit relabeling is required, since the `X`-part already has full rank in the first four columns).

The forward inclusion writes each standard generator's check row as the `𝔽₂`-sum (Pauli product) of
the originals — `s₁ = g₁g₂g₄`, `s₂ = g₂`, `s₃ = g₁g₂g₃g₄`, `s₄ = g₂g₄` — and both families are
linearly independent, so the inclusion is an equality
(`Submodule.span_range_eq_of_le_of_linearIndependent`). -/
theorem fiveQubitStdGen_checkRow_span_eq :
    Submodule.span (ZMod 2) (Set.range (fun i => checkRow (fiveQubitStdGen i)))
      = Submodule.span (ZMod 2) (Set.range (fun i => checkRow (fiveQubitGenIdx i))) := by
  refine Submodule.span_range_eq_of_le_of_linearIndependent ?_
    fiveQubitGen_checkRow_linearIndependent fiveQubitStdGen_checkRow_linearIndependent
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe]
  fin_cases i
  · change checkRow (fiveQubitStdGen 0) ∈ _
    rw [show checkRow (fiveQubitStdGen 0)
        = checkRow (fiveQubitGenIdx 0) + checkRow (fiveQubitGenIdx 1)
          + checkRow (fiveQubitGenIdx 3) from by decide]
    exact add_mem (add_mem (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩))
      (Submodule.subset_span ⟨3, rfl⟩)
  · change checkRow (fiveQubitStdGen 1) ∈ _
    rw [show checkRow (fiveQubitStdGen 1) = checkRow (fiveQubitGenIdx 1) from by decide]
    exact Submodule.subset_span ⟨1, rfl⟩
  · change checkRow (fiveQubitStdGen 2) ∈ _
    rw [show checkRow (fiveQubitStdGen 2)
        = checkRow (fiveQubitGenIdx 0) + checkRow (fiveQubitGenIdx 1)
          + checkRow (fiveQubitGenIdx 2) + checkRow (fiveQubitGenIdx 3) from by decide]
    refine add_mem (add_mem (add_mem (Submodule.subset_span ⟨0, rfl⟩)
      (Submodule.subset_span ⟨1, rfl⟩)) (Submodule.subset_span ⟨2, rfl⟩))
      (Submodule.subset_span ⟨3, rfl⟩)
  · change checkRow (fiveQubitStdGen 3) ∈ _
    rw [show checkRow (fiveQubitStdGen 3)
        = checkRow (fiveQubitGenIdx 1) + checkRow (fiveQubitGenIdx 3) from by decide]
    exact add_mem (Submodule.subset_span ⟨1, rfl⟩) (Submodule.subset_span ⟨3, rfl⟩)

end AxQM.Concrete
