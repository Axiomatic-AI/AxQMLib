/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.InformationTheory.Coding.DualCodeCharacterSum

/-!
# Nielsen & Chuang, Exercise 10.25 — the character sum of a linear code and its dual

*(N&C §10.4.2, p. 450.)*

For linear code C: sum_{y in C}(-1)^{x.y} equals |C| if x in C-perp, else 0.

## What the exercise asks, and what is proved

Here `x · y` is the standard dot product of binary words in `ZMod 2` and `(-1)^{x·y}` is read as the
real number `±1`. The claim is that the character sum `∑_{y ∈ C} (-1)^{x·y}` is a **dual-code
indicator**: it equals the number of codewords `|C|` exactly when `x` is orthogonal to every
codeword (`x ∈ C⊥`), and vanishes otherwise. N&C invoke this identity on the very next page to
rewrite the Hadamard-transformed CSS state (10.70) as a sum over `C₂⊥` (10.71) — the classical step
underlying CSS phase-flip correction.

The proof is the classical character-orthogonality argument. Orthogonality of `x` to `C` makes every
summand `1`, giving `|C|`; otherwise `y ↦ (-1)^{x·y}` is a nontrivial group homomorphism `C → ℝˣ`
(the sign map on `ZMod 2` is multiplicative — a feature special to `ZMod 2`), and translating the
summation index by a codeword `y₀` with `x · y₀ = 1` forces the sum to satisfy `(-1)·S = S`, hence
`S = 0`.

The formalisation is in `ToMathlib/InformationTheory/Coding/DualCodeCharacterSum.lean`, alongside
the classical-coding development (`LinearCode`, `DualCode`, `GilbertVarshamov`).

## Declarations

In `ToMathlib/InformationTheory/Coding/DualCodeCharacterSum.lean`; the code-facing results are in
namespace `LinearCode`, specialised to the binary word space `ι → ZMod 2` (`C : LinearCode (ZMod 2)
ι`), with the sum taken over the subtype `↥C` of codewords and `|C| = Nat.card ↥C`:

* `neg_one_pow_zmod2_val_add` — the sign map `a ↦ (-1)^{a.val}` on `ZMod 2` is an
  additive-to-multiplicative homomorphism, `(-1)^{(a+b).val} = (-1)^{a.val} · (-1)^{b.val}`. This is
  the reusable arithmetic fact (special to `ZMod 2`) that makes `y ↦ (-1)^{x·y}` a character.
* `LinearCode.sum_neg_one_pow_dotProduct_of_mem_dual` — the orthogonal case: `x ∈ C⊥` implies
  `∑_{y ∈ C} (-1)^{x·y} = |C|`.
* `LinearCode.sum_neg_one_pow_dotProduct_of_not_mem_dual` — the non-orthogonal case: `x ∉ C⊥`
  implies `∑_{y ∈ C} (-1)^{x·y} = 0`.
* `LinearCode.sum_neg_one_pow_dotProduct` — the exercise as a single indicator statement,
  `∑_{y ∈ C} (-1)^{x·y} = if x ∈ C⊥ then |C| else 0`.

## Faithfulness

* **Statement.** The two directional claims (`_of_mem_dual`, `_of_not_mem_dual`) are exactly N&C's
  two cases, and `sum_neg_one_pow_dotProduct` states them together as the book's "`|C|` if `x ∈ C⊥`,
  else `0`" — the natural single top-level reading — without weakening. The dual code `C⊥` is the
  library's `LinearCode.dual` (orthogonal complement under the dot product, N&C §10.4.1), so
  "`x ∈ C⊥`" is `x ∈ C.dual` verbatim.
* **Binary codes.** N&C's linear codes here are binary (`(-1)^{x·y}` presupposes `x·y ∈ ZMod 2`), so
  specialising `LinearCode` to `K = ZMod 2` is faithful, not a restriction of a broader claim. The
  value `±1` is taken in `ℝ`, matching the textbook; only `2 ≠ 0` in the codomain is used.
* **`|C|`.** The textbook's `|C|` is the number of codewords, `Nat.card ↥C`, exactly the value the
  orthogonal case returns.
-/
