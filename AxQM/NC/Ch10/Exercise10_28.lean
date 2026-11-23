/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HammingCode743

/-!
# Nielsen & Chuang, Exercise 10.28 — the generator of the `[7, 4, 3]` Hamming code

*(N&C §10.4.4, p. 452.)*

Verify the transpose of matrix (10.77) is the generator of the [7,4,3] Hamming code.

## What the exercise asks, and what is proved

N&C recall the `[7, 4, 3]` Hamming code `C` by its **parity-check matrix** (eq. (10.76))
```
H = ⎡ 0 0 0 1 1 1 1 ⎤
    ⎢ 0 1 1 0 0 1 1 ⎥
    ⎣ 1 0 1 0 1 0 1 ⎦
```
whose columns are the binary numerals `1, …, 7`; the code is the kernel `{x | H *ᵥ x = 0}` (eq.
(10.57)). Eq. (10.77) displays the transposed generator `H[C₂] = G[C₁]ᵀ`, a `4 × 7` matrix. "The
transpose of (10.77) is the generator of the Hamming code" means the `7 × 4` matrix `G` (the
transpose of (10.77)) is a **generator matrix** for that code: its columns are independent and their
span is exactly the parity-check code. Concretely, `range (x ↦ G *ᵥ x) = ker (x ↦ H *ᵥ x)`. This is
what is proved (together with `H · G = 0`, column independence, and the code's dimension `4`).

The formalisation is in `AxQM/Concrete/HammingCode743.lean`, alongside the other concrete
instantiations. The matrices `H` and `G` are specific numeric `ZMod 2` matrices (the particular
`[7, 4, 3]` Hamming code).

## Declarations

All in `AxQM/Concrete/HammingCode743.lean`, in namespace `AxQM.Concrete`, over
`ZMod 2`. The general standard-form version is N&C Exercise 10.19
(`Matrix.range_mulVecLin_stdGenerator`); this file is the concrete `[7, 4, 3]` instance, proved
directly since `H` (10.76) has its identity block on columns `{0, 1, 3}` rather than the last three
coordinates:

* `hammingParityCheck` — the parity-check matrix `H` (10.76), a `Matrix (Fin 3) (Fin 7) (ZMod 2)`.
  The Hamming code is `LinearCode.ofParityCheck hammingParityCheck`.
* `hammingCheckC2` — the matrix (10.77), `H[C₂] = G[C₁]ᵀ`, a `Matrix (Fin 4) (Fin 7) (ZMod 2)`.
* `hammingGenerator` — the **generator matrix** `G = hammingCheckC2ᵀ` (the transpose of (10.77)), a
  `Matrix (Fin 7) (Fin 4) (ZMod 2)`.
* `hammingParityCheck_mul_generator` — **`H · G = 0`**: every column of `G` is a codeword.
* `hammingGenerator_mulVecLin_injective` — the columns of `G` are linearly independent (`G` has full
  column rank `4`), witnessed by the left inverse `hammingLeftInverse`.
* `hammingGenerator_isGenerator` — **the exercise itself**: `range hammingGenerator.mulVecLin =
  LinearCode.ofParityCheck hammingParityCheck`. The reverse inclusion uses the explicit
  reconstruction identity `G · L + M · H = 1` (`hammingGenerator_mul_leftInverse_add`).
* `ofParityCheck_hammingParityCheck_finrank` — the code has dimension `4`: it is a `[7, 4]` code
  (the `k` of N&C's `[7, 4, 3]`).

## Faithfulness

* **Statement.** "The code" is `LinearCode.ofParityCheck hammingParityCheck = ker H.mulVecLin` (N&C
  eq. (10.57)); "`G` is the generator" is the code equality `range G.mulVecLin = ker H.mulVecLin`,
  the same generator/parity-check convention as Exercises 10.18/10.19. The matrices `H` (10.76) and
  `hammingCheckC2` (10.77) are transcribed entry-for-entry from the text, and `hammingGenerator` is
  `hammingCheckC2ᵀ` — literally "the transpose of (10.77)". Column independence and dimension `4`
  are proved, so `G` is verified to be a genuine generator matrix, not merely a spanning family.
* **Scope.** The `d = 3` minimum distance of the `[7, 4, 3]` label is a distinct fact (N&C
  Exercise 10.22) and is not part of this exercise, which asks only to verify the generator/parity
  relationship; it is not treated here.
-/
