/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrixSymplectic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete: the standard-form encoded operators (Nielsen & Chuang, Exercises 10.53–10.54)

This file formalizes the **standard form**
of a stabilizer check matrix (N&C §10.5.7, eq. (10.111)) and the encoded `X`/`Z` operators read off
it (eqs. around (10.111)), and proves the **symplectic (anti)commutation half** of Exercise 10.54.

## The standard form (N&C eq. (10.111))

For an `[n, k]` stabilizer code with `r` the rank of the `X`-part of the check matrix and
`m = n − k − r`, Gaussian elimination brings the `(n − k) × 2n` check matrix into the block form

```
        r    n-k-r  k  |  r    n-k-r  k
   r  [ I    A₁    A₂  |  B     0     C  ]   ← the top r generators
 n-k-r[ 0    0     0   |  D     I     E  ]   ← the bottom n-k-r generators
```

(eq. (10.111); the left half is the `X`-part `r(·)ₓ`, the right half the `Z`-part `r(·)_z`). The
`k` qubits are partitioned as `Fin r ⊕ Fin m ⊕ Fin k`, so a check row is a `2n`-vector
`Cols r m k ⊕ Cols r m k → ZMod 2` — the `X`-bits on `Sum.inl`, the `Z`-bits on `Sum.inr`. N&C then
defines (p. 471) the encoded operators by their check matrices:

* the `k` **encoded `Z`** operators `[0 0 0 | A₂ᵀ 0 I]` (`encZRow`);
* the `k` **encoded `X`** operators `[0 Eᵀ I | Cᵀ 0 0]` (`encXRow`).

## What "commute / anticommute" means here

By Exercise 10.33 (`pauliString_commute_iff_symplecticForm`), two Pauli-group
elements commute iff the **twisted inner product** `r Λ rᵀ` of their check rows vanishes mod 2, with
`Λ = [[0, I], [I, 0]]` (eq. (10.84)); they anticommute iff it is `1`. That twisted product is the
`symplecticForm` of `Concrete/CheckMatrixSymplectic.lean` — defined **once** there over an arbitrary
coordinate index and reused verbatim here on the standard-form columns `Cols r m k` (no parallel
copy). So a claim "the encoded `X` operators commute with the generators / anticommute with `Z̄ⱼ`"
is *literally* a claim about the mod-2 value of `symplecticForm` of the standard-form rows — exactly
the argument N&C gives ("commutativity ... follows from the equation `I × (A₂ᵀ)ᵀ + A₂ = 0`"). Using
`symplecticForm_apply` (its `xᵥ · z_w + zᵥ · x_w` expansion), we prove for the standard-form rows:

* `symplecticForm_encXRow_genRow` — every encoded `X` **commutes with every generator** (`= 0`); the
  top-generator case cancels `C` against `Cᵀ`, the bottom-generator case cancels `E` against `Eᵀ`
  (mod 2).
* `symplecticForm_encXRow_encXRow` — the encoded `X` operators **commute with one another** (`= 0`):
  each carries `Z`-support only in the `Fin r` block and `X`-support only in the `Fin m, Fin k`
  blocks, so the two cross terms vanish.
* `symplecticForm_encXRow_encZRow` — `symplecticForm (X̄ₐ) (Z̄_b) = δ_{ab}` (the `Fin k` identity
  blocks pair up): hence `X̄ⱼ` **anticommutes with `Z̄ⱼ`** (`= 1`,
  `symplecticForm_encXRow_encZRow_self`) and **commutes with `Z̄_k` for `k ≠ j`** (`= 0`,
  `symplecticForm_encXRow_encZRow_of_ne`).

## Exercise 10.54, the independence half

The other half of Exercise 10.54 — that the encoded `X` rows are `𝔽₂`-linearly independent of one
another and of the generators (N&C's notion of "independent", via Proposition 10.3) — is proved here
too. `linearIndependent_genRow_encXRow` shows the generators (`genRow`) and encoded `X` operators
(`encXRow`) form a **jointly** linearly independent family (indexed by `(Fin r ⊕ Fin m) ⊕ Fin k`),
so the encoded `X` operators are independent both of one another and of the generators; the pure
"independent of one another" statement is the corollary `linearIndependent_encXRow`. The proof reads
the three disjoint identity blocks of the standard form in order (pivot `X`-columns, middle
`Z`-columns, encoded `X`-columns), each isolating one block of coefficients.

## Statements

The formalizable content of Exercises 10.53 and 10.54 is symplectic linear algebra over `𝔽₂`; the
declarations here are their statements (as for Exercise 10.33). The connection to actual Pauli
operators is the imported Exercise 10.33 bridge.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {r m k : ℕ}

/-- The `n = r + m + k` **qubit/column index** of a standard-form check matrix, partitioned into the
`r` pivot columns, the `m = n − k − r` middle columns, and the `k` encoded columns (N&C eq.
(10.111)). A single side (`X`- or `Z`-part) of a check row is a function `Cols r m k → ZMod 2`. -/
abbrev Cols (r m k : ℕ) : Type := Fin r ⊕ Fin m ⊕ Fin k

/-- Assemble a vector over the partitioned columns `Cols r m k = Fin r ⊕ Fin m ⊕ Fin k` from its
three blocks `a` (pivot), `b` (middle), `c` (encoded). This is the row-vector counterpart of the
column blocking `[r | n−k−r | k]` used throughout N&C's standard form. -/
def blk (a : Fin r → ZMod 2) (b : Fin m → ZMod 2) (c : Fin k → ZMod 2) : Cols r m k → ZMod 2 :=
  Sum.elim a (Sum.elim b c)

/-- **The dot product of two blocked column-vectors splits blockwise**: `blk a b c ⬝ᵥ blk a' b' c' =
a ⬝ᵥ a' + b ⬝ᵥ b' + c ⬝ᵥ c'`. This is the sum over `Fin r ⊕ Fin m ⊕ Fin k` regrouped by block
(`Fintype.sum_sum_type`), the workhorse for every symplectic computation below. -/
theorem blk_dotProduct (a a' : Fin r → ZMod 2) (b b' : Fin m → ZMod 2)
    (c c' : Fin k → ZMod 2) :
    (blk a b c : Cols r m k → ZMod 2) ⬝ᵥ blk a' b' c' = a ⬝ᵥ a' + b ⬝ᵥ b' + c ⬝ᵥ c' := by
  simp only [blk, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  ring

/-- Dotting the `i`-th row of the identity matrix against `f` evaluates `f` at `i`:
`(1 : Matrix) i ⬝ᵥ f = f i`. A specialisation of `Matrix.one_mulVec` (`1 *ᵥ f = f`), since
`(1 *ᵥ f) i = (1) i ⬝ᵥ f`. -/
theorem oneRow_dotProduct {p : ℕ} (i : Fin p) (f : Fin p → ZMod 2) :
    (1 : Matrix (Fin p) (Fin p) (ZMod 2)) i ⬝ᵥ f = f i :=
  congrFun (Matrix.one_mulVec f) i

/-- Dotting `f` against the `i`-th row of the identity matrix evaluates `f` at `i`:
`f ⬝ᵥ (1 : Matrix) i = f i`. Immediate from `oneRow_dotProduct` by `dotProduct_comm`. -/
theorem dotProduct_oneRow {p : ℕ} (i : Fin p) (f : Fin p → ZMod 2) :
    f ⬝ᵥ (1 : Matrix (Fin p) (Fin p) (ZMod 2)) i = f i := by
  rw [dotProduct_comm]; exact oneRow_dotProduct i f

/-- **The block data of a standard-form check matrix** (Nielsen & Chuang eq. (10.111)) for an
`[n, k]` stabilizer code with `X`-part rank `r` and `m = n − k − r`. The six `𝔽₂`-matrices are the
free blocks of the standard form
`[[I A₁ A₂ | B 0 C], [0 0 0 | D I E]]`; the identity/zero blocks are fixed, so this data determines
the generators (`genRow`) and the encoded operators `[0 Eᵀ I | Cᵀ 0 0]`, `[0 0 0 | A₂ᵀ 0 I]`. -/
structure StandardFormBlocks (r m k : ℕ) where
  /-- Top `X`-block `A₁` (pivot rows against the middle columns). -/
  A₁ : Matrix (Fin r) (Fin m) (ZMod 2)
  /-- Top `X`-block `A₂` (pivot rows against the encoded columns). -/
  A₂ : Matrix (Fin r) (Fin k) (ZMod 2)
  /-- Top `Z`-block `B` (pivot rows against the pivot columns). -/
  B : Matrix (Fin r) (Fin r) (ZMod 2)
  /-- Top `Z`-block `C` (pivot rows against the encoded columns). -/
  C : Matrix (Fin r) (Fin k) (ZMod 2)
  /-- Bottom `Z`-block `D` (middle rows against the pivot columns). -/
  D : Matrix (Fin m) (Fin r) (ZMod 2)
  /-- Bottom `Z`-block `E` (middle rows against the encoded columns). -/
  E : Matrix (Fin m) (Fin k) (ZMod 2)

/-!
### The standard-form generators and encoded operators (N&C eq. (10.111), p. 471)

Each row is a `2n`-vector `Cols r m k ⊕ Cols r m k → ZMod 2`: `X`-part on `Sum.inl`, `Z`-part on
`Sum.inr`, each blocked as `[Fin r | Fin m | Fin k]` via `blk`.
-/

/-- **A top (pivot) generator**, row `i` of `[I A₁ A₂ | B 0 C]` (the first `r` rows of the standard
form (10.111)): `X`-part `(eᵢ, A₁ i, A₂ i)`, `Z`-part `(B i, 0, C i)`. -/
def genTopRow (S : StandardFormBlocks r m k) (i : Fin r) : Cols r m k ⊕ Cols r m k → ZMod 2 :=
  Sum.elim (blk ((1 : Matrix (Fin r) (Fin r) (ZMod 2)) i) (S.A₁ i) (S.A₂ i))
    (blk (S.B i) 0 (S.C i))

/-- **A bottom (middle) generator**, row `i` of `[0 0 0 | D I E]` (the last `n − k − r` rows of the
standard form (10.111)): `X`-part `0`, `Z`-part `(D i, eᵢ, E i)`. -/
def genMidRow (S : StandardFormBlocks r m k) (i : Fin m) : Cols r m k ⊕ Cols r m k → ZMod 2 :=
  Sum.elim (blk 0 0 0)
    (blk (S.D i) ((1 : Matrix (Fin m) (Fin m) (ZMod 2)) i) (S.E i))

/-- **The stabilizer generators** of a standard-form code as a single family indexed by
`Fin r ⊕ Fin m`: the `r` pivot rows `genTopRow` and the `m = n − k − r` middle rows `genMidRow` of
eq. (10.111). -/
def genRow (S : StandardFormBlocks r m k) : Fin r ⊕ Fin m → (Cols r m k ⊕ Cols r m k → ZMod 2) :=
  Sum.elim (genTopRow S) (genMidRow S)

/-- **The `a`-th encoded `X` operator** `X̄ₐ`, row `a` of the `k × 2n` check matrix `[0 Eᵀ I | Cᵀ 0
0]` (N&C p. 471): `X`-part `(0, Eᵀ a, eₐ)`, `Z`-part `(Cᵀ a, 0, 0)`. -/
def encXRow (S : StandardFormBlocks r m k) (a : Fin k) : Cols r m k ⊕ Cols r m k → ZMod 2 :=
  Sum.elim (blk 0 (S.E.transpose a) ((1 : Matrix (Fin k) (Fin k) (ZMod 2)) a))
    (blk (S.C.transpose a) 0 0)

/-- **The `b`-th encoded `Z` operator** `Z̄_b`, row `b` of the `k × 2n` check matrix `[0 0 0 | A₂ᵀ 0
I]` (N&C p. 471): `X`-part `0`, `Z`-part `(A₂ᵀ b, 0, e_b)`. -/
def encZRow (S : StandardFormBlocks r m k) (b : Fin k) : Cols r m k ⊕ Cols r m k → ZMod 2 :=
  Sum.elim (blk 0 0 0)
    (blk (S.A₂.transpose b) 0 ((1 : Matrix (Fin k) (Fin k) (ZMod 2)) b))

/-!
### Exercise 10.54, the symplectic half: (anti)commutation of the encoded `X` operators

The twisted inner product is the imported `symplecticForm` (eq. (10.84)); `symplecticForm_apply`
expands it as `xᵥ · z_w + zᵥ · x_w`. By Exercise 10.33 its vanishing mod 2 is operator commutation
and its value `1` is anticommutation.
-/

/-- **An encoded `X` commutes with a top (pivot) generator** (`symplecticForm = 0`). The one
surviving `X·z` term is `C i a` (`eₐ` against the top row's `Z`-block `C i`) and the one surviving
`z·x` term is `Cᵀ a i = C i a` (`Cᵀ a` against the top row's `X`-pivot `eᵢ`); they cancel mod 2. -/
theorem symplecticForm_encXRow_genTopRow (S : StandardFormBlocks r m k) (a : Fin k) (i : Fin r) :
    symplecticForm (encXRow S a) (genTopRow S i) = 0 := by
  simp only [symplecticForm_apply, encXRow, genTopRow, Sum.elim_comp_inl, Sum.elim_comp_inr,
    blk_dotProduct, zero_dotProduct, dotProduct_zero, add_zero, zero_add, oneRow_dotProduct,
    dotProduct_oneRow]
  rw [Matrix.transpose_apply]
  exact CharTwo.add_self_eq_zero _

/-- **An encoded `X` commutes with a bottom (middle) generator** (`symplecticForm = 0`). The
surviving `X·z` terms are `Eᵀ a i` (`Eᵀ a` against the middle row's `Z`-pivot `eᵢ`) and `E i a`
(`eₐ` against the middle row's `Z`-block `E i`); since `Eᵀ a i = E i a` they cancel mod 2. -/
theorem symplecticForm_encXRow_genMidRow (S : StandardFormBlocks r m k) (a : Fin k) (i : Fin m) :
    symplecticForm (encXRow S a) (genMidRow S i) = 0 := by
  simp only [symplecticForm_apply, encXRow, genMidRow, Sum.elim_comp_inl, Sum.elim_comp_inr,
    blk_dotProduct, zero_dotProduct, dotProduct_zero, add_zero, zero_add, oneRow_dotProduct,
    dotProduct_oneRow]
  rw [Matrix.transpose_apply]
  exact CharTwo.add_self_eq_zero _

/-- **The encoded `X` operators commute with every stabilizer generator** (N&C Ex 10.54): for every
generator `g` (pivot or middle), `symplecticForm (X̄ₐ) g = 0`. -/
theorem symplecticForm_encXRow_genRow (S : StandardFormBlocks r m k) (a : Fin k)
    (g : Fin r ⊕ Fin m) : symplecticForm (encXRow S a) (genRow S g) = 0 := by
  cases g with
  | inl i => rw [genRow, Sum.elim_inl]; exact symplecticForm_encXRow_genTopRow S a i
  | inr i => rw [genRow, Sum.elim_inr]; exact symplecticForm_encXRow_genMidRow S a i

/-- **The encoded `X` operators commute with one another** (N&C Ex 10.54):
`symplecticForm (X̄ₐ) (X̄_{a'}) = 0`. Each `X̄` has `Z`-support confined to the `Fin r` block and
`X`-support to `Fin m, Fin k`, so both cross products `xₐ · z_{a'}` and `zₐ · x_{a'}` vanish. -/
theorem symplecticForm_encXRow_encXRow (S : StandardFormBlocks r m k) (a a' : Fin k) :
    symplecticForm (encXRow S a) (encXRow S a') = 0 := by
  simp only [symplecticForm_apply, encXRow, Sum.elim_comp_inl, Sum.elim_comp_inr, blk_dotProduct,
    zero_dotProduct, dotProduct_zero, add_zero]

/-- **The encoded `X`/`Z` pairing is the Kronecker delta** (N&C Ex 10.54): `symplecticForm (X̄ₐ)
(Z̄_b) = δ_{ab}`, the value `(1 : Matrix) a b`. Only the `Fin k` identity blocks of `X̄ₐ` (its
`X`-part) and `Z̄_b` (its `Z`-part) pair nontrivially, giving `eₐ · e_b`. -/
theorem symplecticForm_encXRow_encZRow (S : StandardFormBlocks r m k) (a b : Fin k) :
    symplecticForm (encXRow S a) (encZRow S b) = (1 : Matrix (Fin k) (Fin k) (ZMod 2)) a b := by
  simp only [symplecticForm_apply, encXRow, encZRow, Sum.elim_comp_inl, Sum.elim_comp_inr,
    blk_dotProduct, zero_dotProduct, dotProduct_zero, add_zero, zero_add, dotProduct_oneRow]

/-- **`X̄ⱼ` anticommutes with `Z̄ⱼ`** (N&C Ex 10.54): `symplecticForm (X̄ⱼ) (Z̄ⱼ) = 1`. -/
theorem symplecticForm_encXRow_encZRow_self (S : StandardFormBlocks r m k) (a : Fin k) :
    symplecticForm (encXRow S a) (encZRow S a) = 1 := by
  rw [symplecticForm_encXRow_encZRow]; exact Matrix.one_apply_eq a

/-- **`X̄ⱼ` commutes with `Z̄_k` for `k ≠ j`** (N&C Ex 10.54): `symplecticForm (X̄ⱼ) (Z̄_k) = 0`
when `j ≠ k`. -/
theorem symplecticForm_encXRow_encZRow_of_ne (S : StandardFormBlocks r m k) {a b : Fin k}
    (h : a ≠ b) : symplecticForm (encXRow S a) (encZRow S b) = 0 := by
  rw [symplecticForm_encXRow_encZRow]; exact Matrix.one_apply_ne h

/-!
### Exercise 10.54, the independence half: the encoded `X` rows are `𝔽₂`-linearly independent

N&C's "independent" (Proposition 10.3) is `𝔽₂`-linear independence of the `2n`-bit check rows. We
prove the strong joint statement — the `r + m` generators (`genRow`) **together with** the `k`
encoded `X` operators (`encXRow`) form a linearly independent family indexed by
`(Fin r ⊕ Fin m) ⊕ Fin k` — from which the exercise's two claims follow: the encoded `X` operators
are independent **of one another** (restrict to the `Fin k` summand) and **of the generators** (the
combined family has no nontrivial relation mixing the two blocks).

The proof reads the three disjoint identity blocks of the standard form `[[I A₁ A₂ | B 0 C], [0 0 0
| D I E]]` in order. Given a vanishing `𝔽₂`-combination of the rows, evaluate the coordinate `c`:

* at a **pivot `X`-column** `Fin r` only the top generators contribute (their identity block `I`),
  forcing every top-generator coefficient to `0`;
* at a **middle `Z`-column** `Fin m` only the middle generators contribute (their identity block
  `I`), forcing every middle-generator coefficient to `0`;
* at an **encoded `X`-column** `Fin k` the top generators contribute via `A₂` and the encoded `X`
  operators via their identity block `I`; but the `A₂` term is already zero (top coefficients
  vanish), so every encoded-`X` coefficient is `0`.
-/

/-- **Extracting a coefficient against an identity column**: `∑ i, f i * (1) i j = f j` over `𝔽₂`.
The workhorse for reading a standard-form pivot/identity block out of a coordinate sum. -/
theorem sum_mul_oneCol {p : ℕ} (f : Fin p → ZMod 2) (j : Fin p) :
    ∑ i, f i * (1 : Matrix (Fin p) (Fin p) (ZMod 2)) i j = f j := by
  simp [Matrix.one_apply]

/-- **The stabilizer generators and encoded `X` operators are jointly `𝔽₂`-linearly independent**
(N&C Ex 10.54: the encoded `X` operators are "independent of one another and of the generators").
The `2n`-bit check rows of the `r + m` generators (`genRow`) together with the `k` encoded `X`
operators (`encXRow`) form a linearly independent family indexed by `(Fin r ⊕ Fin m) ⊕ Fin k`. The
argument reads the three disjoint identity blocks of the standard form in order (pivot `X`-columns
kill the top-generator coefficients, middle `Z`-columns the middle-generator coefficients, encoded
`X`-columns the encoded-`X` coefficients — the residual `A₂` term already zero). -/
theorem linearIndependent_genRow_encXRow (S : StandardFormBlocks r m k) :
    LinearIndependent (ZMod 2) (Sum.elim (genRow S) (encXRow S)) := by
  refine Fintype.linearIndependent_iff.mpr (fun g hg => ?_)
  -- The combination vanishes coordinatewise: for every column `c`, `∑ i, g i · (row i) c = 0`.
  have hcol : ∀ c, ∑ i, g i * (Sum.elim (genRow S) (encXRow S) i) c = 0 := by
    intro c
    have h := congrFun hg c
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  -- Pivot `X`-columns isolate the top-generator coefficients.
  have htop : ∀ p, g (Sum.inl (Sum.inl p)) = 0 := by
    intro p
    have h := hcol (Sum.inl (Sum.inl p))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [genRow, genTopRow, genMidRow, encXRow, blk, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply, mul_ite, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h
  -- Middle `Z`-columns isolate the middle-generator coefficients.
  have hmid : ∀ s, g (Sum.inl (Sum.inr s)) = 0 := by
    intro s
    have h := hcol (Sum.inr (Sum.inr (Sum.inl s)))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [genRow, genTopRow, genMidRow, encXRow, blk, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, Matrix.one_apply, mul_ite,
      mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h
  rintro ((p | s) | a)
  · exact htop p
  · exact hmid s
  · -- Encoded `X`-columns isolate the encoded-`X` coefficients; the top-generator `A₂` term is
    -- already zero by `htop`.
    have h := hcol (Sum.inl (Sum.inr (Sum.inr a)))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [genRow, genTopRow, genMidRow, encXRow, blk, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero] at h
    rw [Finset.sum_eq_zero (fun q _ => by rw [htop q, zero_mul]), zero_add, sum_mul_oneCol] at h
    exact h

/-- **The encoded `X` operators are `𝔽₂`-linearly independent of one another** (N&C Ex 10.54): the
`k` encoded `X` check rows `encXRow` form a linearly independent family. A restriction of the joint
independence `linearIndependent_genRow_encXRow` to the encoded-`X` summand `Sum.inr`. -/
theorem linearIndependent_encXRow (S : StandardFormBlocks r m k) :
    LinearIndependent (ZMod 2) (encXRow S) :=
  (linearIndependent_genRow_encXRow S).comp Sum.inr Sum.inr_injective

end AxQM.Concrete
