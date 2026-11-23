/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.FiveQubitStandardForm
import AxQM.Concrete.ShorStandardForm

/-!
# Nielsen & Chuang, Exercise 10.57 — five and nine qubit code check matrices in standard form

*(N&C §10.5.7, p. 472.)*

Give the check matrices for the five and nine qubit codes in standard form.

## What the exercise asks

For an `[n, k]` stabilizer code, §10.5.7 puts the `(n − k) × 2n` check matrix into the **standard
form** (eq. (10.111))
```
        r    m    k  ┃  r    m    k
   r  [ I    A₁   A₂ ┃  B    0    C  ]
   m  [ 0    0    0  ┃  D    I    E  ]
```
by relabeling generators (row swaps), multiplying generators (row additions), and relabeling qubits
(column swaps), where `r` is the rank of the `X`-part and `m = n − k − r`. The exercise asks to
carry out this reduction for the two named codes:

* the **five-qubit code** `[[5,1,3]]` (Figure 10.12), and
* the **nine-qubit Shor code** `[[9,1,3]]` (Figure 10.11).

## What is formalised

The content of "the check matrix in standard form" is finite `𝔽₂ = ZMod 2` linear algebra
over the check rows `r(g) = (x | z) ∈ (Fin n → ZMod 2) × (Fin n → ZMod 2)` (`Concrete.checkRow`):
the standard-form matrix, a certificate that it **is** in standard form (the identity/zero blocks of
eq. (10.111)), and a certificate that it is **the same code** (its rows span the same `𝔽₂` subspace
as the textbook generators' check rows, up to the qubit relabeling — a stabilizer code being exactly
the row space of its check matrix). Compare the sibling standard-form items: Exercise 10.53
(`AxQM/Concrete/StandardFormEncodedZ.lean`), Exercise 10.54
(`AxQM/Concrete/StabilizerStandardForm.lean`) and Exercise 10.55
(`AxQM/Concrete/SteaneStandardForm.lean`).

## Faithfulness

Each code's standard-form check matrix is exhibited explicitly and pinned to the actual code by two
theorems: it has the standard-form **shape** of eq. (10.111) (the `X`-pivot identity block, the
`Z`-middle identity block, and the zero blocks), and its rows span the **same code** as the textbook
generators. Nothing is weakened — the standard form is not merely *some* matrix of the required
shape, it is proved to generate the same stabilizer as the Figure-10.11/10.12 generators (up to the
qubit relabeling that §10.5.7's column swaps perform).

## Declarations

**Five-qubit code** (`AxQM/Concrete/FiveQubitStandardForm.lean`, namespace
`AxQM.Concrete`). Here the `X`-part has full rank `r = 4 = n − k`, so
`m = 0` (no bottom block) and no qubit swap is needed:

* `fiveQubitStdGen` — the four standard-form generators
  `s₁ = YZIZY`, `s₂ = IXZZX`, `s₃ = ZZXIX`, `s₄ = ZIZYY`, whose check matrix is `[I₄ A₂ | B C]` with
  `A₂ = (1,1,1,1)ᵀ`.
* `fiveQubitStdGen_xPart_pivot_identity` — **in standard form**: the `X`-part on the first `r = 4`
  columns is `I₄`.
* `fiveQubitStdGen_checkRow_span_eq` — **the same code**: the standard-form check rows and the
  Figure-10.12 generators' check rows span the same `𝔽₂` subspace.
* `Submodule.span_range_eq_of_le_of_linearIndependent` (in
  `ToMathlib/LinearAlgebra/FiniteDimensional/SpanRangeEq.lean`) — the row-space lemma (span
  equality from one inclusion plus linear independence of both sides, via `finrank`); it is pure
  linear algebra naming no check matrix.

**Nine-qubit Shor code** (`AxQM/Concrete/ShorStandardForm.lean`, namespace
`AxQM.Concrete`). Here the `X`-part has rank `r = 2` (only the two `X`-type
generators are nonzero on it), so `m = n − k − r = 6` and — unlike the five-qubit code — the full
bottom `[0 0 0 | D I E]` block **and** a genuine qubit relabeling are both needed:

* `shorGenIdx` — the eight Figure-10.11 generators `Z₁Z₂, Z₂Z₃, Z₄Z₅, Z₅Z₆, Z₇Z₈, Z₈Z₉`,
  `X₁X₂X₃X₄X₅X₆`, `X₄X₅X₆X₇X₈X₉`.
* `shorStdGen` — the eight standard-form generators
  `s₁ = g₇`, `s₂ = g₈`, `s₃ = g₁`, `s₄ = g₁g₂`, `s₅ = g₃g₄`, `s₆ = g₄`, `s₇ = g₅`, `s₈ = g₅g₆`,
  in the relabeled ordering `(1,7,2,3,4,5,8,9,6)` (`shorStdSwap`), whose check matrix is
  `[[I₂ A₁ A₂ | 0 0 0] ; [0 0 0 | D I₆ E]]`.
* `shorStdGen_xPart_pivot_identity`, `shorStdGen_bottom_xPart_zero`, `shorStdGen_top_zPart_zero`,
  `shorStdGen_zPart_middle_identity` — **in standard form**: the four fixed blocks of eq. (10.111)
  (the top-left `I₂`, the zero bottom `X`-part, the zero top `Z`-part, the bottom-middle `I₆`).
* `shorStdGen_checkRow_span_eq` — **the same code**: undoing the relabeling (`shorStdGenOriginal`),
  the standard-form check rows and the Figure-10.11 generators' check rows span the same `𝔽₂`
  subspace.

Both standard forms reuse `Submodule.span_range_eq_of_le_of_linearIndependent`
(`ToMathlib/LinearAlgebra/FiniteDimensional/SpanRangeEq.lean`), the row-space lemma (span equality
from one inclusion plus linear independence of both sides, via `finrank`), which is pure linear
algebra naming no check matrix.

See the module docstrings of `AxQM/Concrete/FiveQubitStandardForm.lean` and
`AxQM/Concrete/ShorStandardForm.lean` for the full rationale and each worked reduction.
-/
