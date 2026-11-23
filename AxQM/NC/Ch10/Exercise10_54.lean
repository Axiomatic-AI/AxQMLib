/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerStandardForm

/-!
# Nielsen & Chuang, Exercise 10.54 — the standard-form encoded `X` operators

*(N&C §10.5.7, p. 471.)*

Prove encoded X operators are independent, commute with generators, and Xbar_j anticommutes only
with Zbar_j.

## What this exercise is, and where it is formalized

For an `[n, k]` stabilizer code in **standard form** (N&C eq. (10.111)), the encoded `X` operators
are the `k` Pauli operators whose `k × 2n` check matrix is `[0 Eᵀ I | Cᵀ 0 0]`. Exercise 10.54 asks
to verify five properties of these operators relative to the stabilizer generators (rows of
`[[I A₁ A₂ | B 0 C], [0 0 0 | D I E]]`) and the encoded `Z` operators (`[0 0 0 | A₂ᵀ 0 I]`):

1. the encoded `X` operators are **independent** of one another;
2. **independent** of the generators;
3. they **commute with the generators**;
4. they **commute with each other**;
5. `X̄ⱼ` **commutes with `Z̄_k` for `k ≠ j`** and **anticommutes with `Z̄ⱼ`**.

This is a statement about the standard-form **check matrix**: "independent" is `𝔽₂`-linear
independence of the `2n`-bit check rows (N&C Proposition 10.3), and "commute / anticommute" is the
vanishing / non-vanishing mod 2 of the twisted inner product `r Λ rᵀ` of the rows — the `Concrete`
`symplecticForm` (eq. (10.84)), the same function whose vanishing is Exercise 10.33's operator
commutation criterion (`pauliString_commute_iff_symplecticForm`). The content is therefore
symplectic linear algebra over `𝔽₂`.

## Declarations

All in `AxQM/Concrete/StabilizerStandardForm.lean`, namespace `AxQM.Concrete`, for
a `StandardFormBlocks r m k` (the six free blocks `A₁ A₂ B C D E` of eq. (10.111), with `n = r + m +
k` and `r` the `X`-rank):

* `StandardFormBlocks`, `blk`, `Cols` — the standard-form data and the blocked column index.
* `genTopRow` / `genMidRow` / `genRow` — the stabilizer generators `[I A₁ A₂ | B 0 C]`,
  `[0 0 0 | D I E]`.
* `encXRow` — the encoded `X` operators `[0 Eᵀ I | Cᵀ 0 0]`; `encZRow` — the encoded `Z` operators
  `[0 0 0 | A₂ᵀ 0 I]`.
* The twisted inner product is the imported `symplecticForm` (eq. (10.84)), reused verbatim on the
  standard-form columns `Cols r m k` (with its `symplecticForm_apply` expansion).
* **Property 3 (commute with the generators):** `symplecticForm_encXRow_genRow` (with the
  pivot/middle cases `symplecticForm_encXRow_genTopRow` / `symplecticForm_encXRow_genMidRow`).
* **Property 4 (commute with each other):** `symplecticForm_encXRow_encXRow`.
* **Property 5 (`X̄ⱼ` vs `Z̄_k`):** `symplecticForm_encXRow_encZRow` (`= δ_{jk}`), with corollaries
  `symplecticForm_encXRow_encZRow_self` (`= 1`, anticommutes with `Z̄ⱼ`) and
  `symplecticForm_encXRow_encZRow_of_ne` (`= 0`, commutes with `Z̄_k`, `k ≠ j`).
* **Properties 1–2 (independence):** `linearIndependent_genRow_encXRow` — the generators (`genRow`)
  and encoded `X` operators (`encXRow`) are **jointly** `𝔽₂`-linearly independent (indexed by
  `(Fin r ⊕ Fin m) ⊕ Fin k`), so `X̄` is independent both of the generators and of one another; its
  corollary `linearIndependent_encXRow` is the pure "independent of one another" statement. This is
  N&C's notion of "independent" via Proposition 10.3 (independent generators ↔ `𝔽₂`-linearly
  independent check rows). The supporting lemma `sum_mul_oneCol` reads an identity block out of a
  coordinate sum.
-/
