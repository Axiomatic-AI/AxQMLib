/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.InformationTheory.Coding.LinearCode
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The repetition code, its generator matrix, and a parity-check matrix

The **repetition code** encoding `k` symbols by repeating each of them `r` times is the classical
`[rk, k]` linear code of Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise
10.14 (p. 446). This file writes out the generator matrix that N&C's exercise asks for, and proves
that it does encode `k` symbols by `r`-fold repetition and that the resulting code is genuinely
`k`-dimensional. It also constructs a **parity-check matrix** for the code (N&C p. 447, Exercise
10.17): a matrix whose kernel is the code, and whose rows — being linearly independent — make it a
minimal such matrix.

Following N&C §10.4.1, a generator matrix `G` is an `n × k` matrix and a message `x` (a column
vector) is encoded as `G *ᵥ x`; the code is the span of the columns of `G`, i.e. the range of
`x ↦ G *ᵥ x` (`Matrix.mulVecLin`). The `r`-fold repetition code indexes its `rk` codeword positions
by `Fin k × Fin r`: position `(j, s)` is the `s`-th copy of message symbol `j`. This matches N&C's
ordering — for the `[6, 2]` example (10.54) the two columns are `(1,1,1,0,0,0)` and `(0,0,0,1,1,1)`,
and `G (1,0) = (1,1,1,0,0,0)`, `G (0,1) = (0,0,0,1,1,1)` (eqs. (10.55)–(10.56)).

## Main definitions

* `repetitionGenerator K k r`: the `rk × k` generator matrix `G` with `G (j, s) i = 1` iff `i = j`
  (N&C Exercise 10.14). Its `i`-th column is the indicator of the `r` positions holding copies of
  message symbol `i`.
* `repetitionCode K k r`: the repetition code itself, the span of the columns of the generator
  matrix (`LinearMap.range (repetitionGenerator K k r).mulVecLin`), of type
  `LinearCode K (Fin k × Fin r)`.
* `repetitionParityCheck K k m`: a parity-check matrix `H` for the repetition code with `r = m + 1`
  repetitions (N&C p. 447, Exercise 10.17). It is the `k·m × k(m+1)` matrix whose row `(j, s)`
  imposes "position `(j, s)` equals position `(j, s+1)`", i.e. `H (j, s) (j', s')` is `1` if
  `(j', s') = (j, s)`, `-1` if `(j', s') = (j, s+1)`, and `0` otherwise. Over `ZMod 2` this is the
  all-`0`/`1` matrix N&C describe (there `−1 = 1`); over a general field the signed differences are
  needed for the kernel to come out right (cf. N&C Exercise 10.19).

## Main results

* `repetitionGenerator_mulVec`: encoding repeats each symbol — `(G *ᵥ x) (j, s) = x j`, so the
  message `x` is sent to the word that carries `r` copies of every `x j` (N&C eqs. (10.55)–(10.56)).
* `repetitionGenerator_mulVecLin_injective`: for `r ≥ 1` the encoding is injective, i.e. the columns
  of `G` are linearly independent — exactly N&C's condition (p. 446) for all messages to be uniquely
  encoded.
* `mem_repetitionCode_iff`: for `r ≥ 1` a word is a codeword iff it is constant on each block, i.e.
  the `r` copies of every symbol agree.
* `repetitionCode_finrank`: for `r ≥ 1` the code has dimension `k`. Together with the block length
  `#(Fin k × Fin r) = k * r`, this is the `[rk, k]` claim of Exercise 10.14.
* `repetitionParityCheck_mulVec`: the parity check computes adjacent differences within each block,
  `(H *ᵥ x) (j, s) = x (j, s.castSucc) - x (j, s.succ)`.
* `repetitionParityCheck_ker`: **the parity-check property** — the kernel of `H` is exactly the
  repetition code, `ker (repetitionParityCheck K k m).mulVecLin = repetitionCode K k (m + 1)`. This
  is the sense of N&C's "the code is the kernel of `H`" (eq. (10.57)); it is Exercise 10.17.
* `repetitionParityCheck_rank`, `repetitionParityCheck_row_linearIndependent`: `H` has full row
  rank `k·m = n − k` and hence linearly independent rows — N&C's requirement (p. 447) that a
  parity-check matrix have independent rows so that its kernel has the correct dimension `k`.

## Implementation notes

The coefficients range over an arbitrary field `K`, matching the `LinearCode` development; N&C's
binary code is the case `K = ZMod 2` (and N&C themselves note in Exercise 10.19 that these
constructions extend beyond `ZMod 2`). Injectivity of the encoding — and hence the dimension count —
needs a symbol to actually be repeated, so those results carry the hypothesis `0 < r`; the generator
matrix and its encoding action are stated with no such hypothesis.

The parity-check matrix is indexed by `r = m + 1` (rather than a bare `r` with a `0 < r` side
condition) so that its `k·m` rows — one adjacent-difference constraint per repetition gap in each of
the `k` blocks — and their positions `s.castSucc`, `s.succ : Fin (m + 1)` are available
definitionally, without truncated subtraction. The `[6, 2]` code of (10.54) is the case `k = 2`,
`m = 2`
(`repetitionParityCheck K 2 2`, a parity-check matrix for `repetitionCode K 2 3`), whose four rows
are the two-block analogue of N&C's `[3, 1]` example (10.58).
-/

@[expose] public section

open Matrix

/-- The **generator matrix** of the `[rk, k]` repetition code (Nielsen & Chuang, Exercise 10.14):
the `rk × k` matrix `G` over `K` whose codeword positions are indexed by `Fin k × Fin r` and whose
entry `G (j, s) i` is `1` when `i = j` and `0` otherwise. Its `i`-th column is the indicator of the
`r` positions `(i, ·)` that hold copies of message symbol `i`, so that `G *ᵥ x` repeats each symbol
of `x` exactly `r` times. -/
def repetitionGenerator (K : Type*) [Field K] (k r : ℕ) :
    Matrix (Fin k × Fin r) (Fin k) K :=
  Matrix.of fun p i => if i = p.1 then 1 else 0

variable {K : Type*} [Field K] {k r : ℕ}

/-- The entries of the repetition generator matrix: `G (j, s) i = 1` iff `i = j`. -/
@[simp] theorem repetitionGenerator_apply (p : Fin k × Fin r) (i : Fin k) :
    repetitionGenerator K k r p i = if i = p.1 then 1 else 0 := rfl

/-- **Encoding repeats each symbol** (Nielsen & Chuang, eqs. (10.55)–(10.56)): the repetition
generator matrix sends a message `x : Fin k → K` to the word carrying `r` copies of every symbol:
`(G *ᵥ x) (j, s) = x j`. -/
theorem repetitionGenerator_mulVec (x : Fin k → K) :
    repetitionGenerator K k r *ᵥ x = fun p => x p.1 := by
  funext p
  simp only [mulVec, repetitionGenerator_apply, dotProduct, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **The columns of the repetition generator matrix are linearly independent** (Nielsen & Chuang,
p. 446): when each symbol is repeated at least once (`0 < r`), the encoding map `x ↦ G *ᵥ x` is
injective, so every message is uniquely encoded. The inverse simply reads off any one copy of each
symbol. -/
theorem repetitionGenerator_mulVecLin_injective (hr : 0 < r) :
    Function.Injective (repetitionGenerator K k r).mulVecLin := by
  intro x y h
  funext j
  simpa only [mulVecLin_apply, repetitionGenerator_mulVec] using congrFun h (j, ⟨0, hr⟩)

/-- The **`[rk, k]` repetition code** (Nielsen & Chuang, Exercise 10.14): the linear code whose
codewords are the span of the columns of `repetitionGenerator K k r`, i.e. the range of the encoding
map `x ↦ G *ᵥ x`. Its block length is `#(Fin k × Fin r) = k * r` and, for `0 < r`, its dimension
is `k` (`repetitionCode_finrank`). -/
noncomputable def repetitionCode (K : Type*) [Field K] (k r : ℕ) :
    LinearCode K (Fin k × Fin r) :=
  LinearMap.range (repetitionGenerator K k r).mulVecLin

/-- **A word is a codeword of the repetition code iff it is constant on each block** (`0 < r`): the
`r` copies of every symbol agree, `y (j, s) = y (j, s')`. This is the intrinsic description of the
column span of the generator matrix. -/
theorem mem_repetitionCode_iff (hr : 0 < r) {y : Fin k × Fin r → K} :
    y ∈ repetitionCode K k r ↔ ∀ (j : Fin k) (s s' : Fin r), y (j, s) = y (j, s') := by
  rw [repetitionCode, LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩ j s s'
    simp only [mulVecLin_apply, repetitionGenerator_mulVec]
  · intro h
    refine ⟨fun j => y (j, ⟨0, hr⟩), ?_⟩
    rw [mulVecLin_apply, repetitionGenerator_mulVec]
    funext p
    obtain ⟨j, s⟩ := p
    exact h j ⟨0, hr⟩ s

/-- **The repetition code has dimension `k`** (`0 < r`). With the block length
`#(Fin k × Fin r) = k * r`, this is the `[rk, k]` content of Nielsen & Chuang, Exercise 10.14: the
generator matrix, having `k` linearly independent columns, generates a `k`-dimensional code. -/
theorem repetitionCode_finrank (hr : 0 < r) :
    Module.finrank K (repetitionCode K k r) = k := by
  rw [repetitionCode, LinearMap.finrank_range_of_inj (repetitionGenerator_mulVecLin_injective hr),
    Module.finrank_pi K, Fintype.card_fin]

variable {m : ℕ}

/-- A **parity-check matrix** of the `[k(m+1), k]` repetition code (Nielsen & Chuang, p. 447,
Exercise 10.17): the `k·m × k(m+1)` matrix `H` over `K` whose rows are indexed by `Fin k × Fin m`
and columns by `Fin k × Fin (m + 1)`, with `H (j, s) (j', s')` equal to `1` if `(j', s')` is the
position `(j, s.castSucc)`, `-1` if it is `(j, s.succ)`, and `0` otherwise. Row `(j, s)` therefore
imposes the constraint `x (j, s.castSucc) = x (j, s.succ)`, so that a word lies in `ker H` exactly
when it is constant on each block — i.e. when it is a codeword. Over `ZMod 2` (where `−1 = 1`) this
is the all-`0`/`1` matrix N&C describe. -/
def repetitionParityCheck (K : Type*) [Field K] (k m : ℕ) :
    Matrix (Fin k × Fin m) (Fin k × Fin (m + 1)) K :=
  Matrix.of fun p q =>
    if q.1 = p.1 then (if q.2 = p.2.castSucc then 1 else if q.2 = p.2.succ then -1 else 0)
    else 0

/-- The entries of the repetition parity-check matrix: `H (j, s) (j', s')` is `1` when
`(j', s') = (j, s.castSucc)`, `-1` when `(j', s') = (j, s.succ)`, and `0` otherwise. -/
theorem repetitionParityCheck_apply (p : Fin k × Fin m) (q : Fin k × Fin (m + 1)) :
    repetitionParityCheck K k m p q =
      if q.1 = p.1 then (if q.2 = p.2.castSucc then 1 else if q.2 = p.2.succ then -1 else 0)
      else 0 := rfl

/-- **The parity check computes adjacent differences within each block**: applying `H` to a word
`x` gives, at row `(j, s)`, the difference `x (j, s.castSucc) - x (j, s.succ)` between two
consecutive copies of symbol `j`. -/
theorem repetitionParityCheck_mulVec (x : Fin k × Fin (m + 1) → K) :
    repetitionParityCheck K k m *ᵥ x =
      fun p => x (p.1, p.2.castSucc) - x (p.1, p.2.succ) := by
  funext p
  obtain ⟨j, s⟩ := p
  have hab : (s.castSucc : Fin (m + 1)) ≠ s.succ := Fin.castSucc_lt_succ.ne
  simp only [mulVec, dotProduct, repetitionParityCheck_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · have hterm : ∀ s' : Fin (m + 1),
        (if (j, s').1 = (j, s).1 then
            (if (j, s').2 = ((j, s).2).castSucc then (1 : K)
             else if (j, s').2 = ((j, s).2).succ then -1 else 0)
          else 0) * x (j, s')
        = (if s' = s.castSucc then x (j, s') else 0) - (if s' = s.succ then x (j, s') else 0) := by
      intro s'
      dsimp only
      split_ifs with h1 h2 h3 <;> simp_all
    rw [Finset.sum_congr rfl (fun s' _ => hterm s')]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ s.castSucc (fun s' => x (j, s')),
      Finset.sum_ite_eq' Finset.univ s.succ (fun s' => x (j, s'))]
    simp
  · intro j' _ hj'
    apply Finset.sum_eq_zero
    intro s' _
    simp [hj']
  · simp

/-- **The parity-check property** (Nielsen & Chuang, p. 447, Exercise 10.17): the kernel of the
repetition parity-check matrix is exactly the repetition code with `r = m + 1` repetitions,
`ker (repetitionParityCheck K k m).mulVecLin = repetitionCode K k (m + 1)`. A word is annihilated by
`H` iff consecutive copies of each symbol agree (`repetitionParityCheck_mulVec`), iff it is constant
on every block, iff it is a codeword (`mem_repetitionCode_iff`). This realizes N&C's alternative
definition of a linear code as the kernel of its parity-check matrix (eq. (10.57)). -/
theorem repetitionParityCheck_ker :
    LinearMap.ker (repetitionParityCheck K k m).mulVecLin = repetitionCode K k (m + 1) := by
  ext x
  rw [LinearMap.mem_ker, mulVecLin_apply, repetitionParityCheck_mulVec,
    mem_repetitionCode_iff (Nat.succ_pos m)]
  constructor
  · intro h j s s'
    -- Adjacent copies agree; propagate to all copies of symbol `j` by induction on the position.
    have hadj : ∀ t : Fin m, x (j, t.castSucc) = x (j, t.succ) := by
      intro t
      have := congrFun h (j, t)
      simpa [sub_eq_zero] using this
    have key : ∀ i : Fin (m + 1), x (j, i) = x (j, 0) := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => rw [← hadj i]; exact ih
    rw [key s, key s']
  · intro h
    funext p
    obtain ⟨j, s⟩ := p
    simp only [Pi.zero_apply, sub_eq_zero]
    exact h j s.castSucc s.succ

/-- **The parity-check matrix has full row rank** `k·m = n − k`: since its kernel is the repetition
code (`repetitionParityCheck_ker`), which has dimension `k`, the rank–nullity theorem forces the
rank to be `#(Fin k × Fin (m + 1)) − k = k(m+1) − k = k·m`. -/
theorem repetitionParityCheck_rank :
    (repetitionParityCheck K k m).rank = k * m := by
  have hnull := LinearMap.finrank_range_add_finrank_ker (repetitionParityCheck K k m).mulVecLin
  rw [repetitionParityCheck_ker, repetitionCode_finrank (Nat.succ_pos m),
    Module.finrank_pi K, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Nat.mul_succ] at hnull
  rw [← Matrix.finrank_range_mulVecLin]
  omega

/-- **The rows of the parity-check matrix are linearly independent** (Nielsen & Chuang, p. 447): a
parity-check matrix must have independent rows so that its kernel has the intended dimension `k`.
Here this is a consequence of full row rank (`repetitionParityCheck_rank`): the number of rows
`k·m` equals the rank, so the rows span a space of their own cardinality and are independent. -/
theorem repetitionParityCheck_row_linearIndependent :
    LinearIndependent K (repetitionParityCheck K k m).row := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, Set.finrank, Matrix.finrank_span_range_row, repetitionParityCheck_rank]

end
