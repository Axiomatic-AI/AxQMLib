/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringLocality

/-!
# Nielsen & Chuang, Exercise 10.50 — the five-qubit code saturates the quantum Hamming bound

*(N&C §10.5.6, p. 469.)*

Show the five qubit code saturates the quantum Hamming bound (10.51 with equality).

## The quantum Hamming bound (N&C §10.3.4)

For a **non-degenerate** code encoding `k` qubits in `n` qubits and correcting every error on `t`
or fewer qubits, each correctable error must send the code space to an orthogonal `2ᵏ`-dimensional
subspace, and all of these subspaces fit inside the `2ⁿ`-dimensional register. Counting the errors:
there are `∑_{j=0}^{t} C(n, j) · 3ʲ` Pauli errors of weight `≤ t` (choose `j` of the `n` qubits and
one of the three Paulis `X, Y, Z` on each, N&C eq. (10.50)), so

> `(∑_{j=0}^{t} C(n, j) · 3ʲ) · 2ᵏ ≤ 2ⁿ`   (10.51),

the **quantum Hamming bound**. The **five-qubit code** is the `[[5, 1, 3]]` code: it encodes
`k = 1` qubit in `n = 5` qubits with distance `d = 3`, hence corrects `t = ⌊(d−1)/2⌋ = 1`
arbitrary single-qubit error (Exercise 10.49). Substituting `n = 5, k = 1, t = 1`:

> `(C(5,0)·3⁰ + C(5,1)·3¹) · 2¹ = (1 + 15) · 2 = 32 = 2⁵`,

so (10.51) holds **with equality** — the code is *perfect*: its code space and the images of its
`16` correctable errors exactly tile the `32`-dimensional Hilbert space, with no room to spare.

## What is formalised

The left-hand multiplicand of (10.51) — the number of Pauli errors of weight `≤ t` on `n` qubits —
is the count `(Concrete.localPauliStrings t n).card` of Pauli strings `g : Fin n → Fin 4` (with
`0 = I`, `1,2,3 = X,Y,Z`) of support size `≤ t`. Its exact value `∑_{j=0}^{t} C(n, j) · 3ʲ`
(N&C eq. (10.50)) is `Concrete.card_localPauliStrings_eq` (pure Pauli-string combinatorics,
sharpening `Concrete.card_localPauliStrings_le`). This file assembles
that count into the bound and proves the five-qubit saturation:

* `quantumHammingBoundLHS n k t` — the left side of (10.51), `(#errors of weight ≤ t) · 2ᵏ`.
* `quantumHammingBoundLHS_eq` — its closed form `(∑_{j=0}^{t} C(n, j) · 3ʲ) · 2ᵏ`, literally the
  left side of N&C (10.51).
* `QuantumHammingBound n k t` — the bound (10.51) as a proposition,
  `quantumHammingBoundLHS n k t ≤ 2ⁿ`.
* `fiveQubitCode_card_correctableErrors` — there are exactly `16` correctable errors: the identity
  and the `5 · 3 = 15` weight-one Paulis.
* `fiveQubitCode_saturates_quantumHammingBound` — **the exercise**:
  `quantumHammingBoundLHS 5 1 1 = 2⁵`, i.e. (10.51) holds with *equality* for the five-qubit code.
* `fiveQubitCode_satisfies_quantumHammingBound` — the corollary that the bound itself
  (`QuantumHammingBound 5 1 1`) then holds, `le_of_eq` of the saturation.

## Faithfulness

* **Not weakened.** N&C's "satisfies (10.51) with equality" is captured exactly as the equality
  `quantumHammingBoundLHS 5 1 1 = 2⁵`; the general bound `QuantumHammingBound` is stated for all
  `n, k, t`, and `quantumHammingBoundLHS_eq` shows the left side is verbatim N&C's
  `(∑ C(n,j)·3ʲ)·2ᵏ`. Nothing is specialised beyond substituting the code's own parameters.
* **The parameters `(n, k, t) = (5, 1, 1)`** are exactly those of the five-qubit `[[5,1,3]]` code:
  five physical qubits, one logical qubit, and single-error correction (`d = 3 ⟹ t = 1`). These are
  facts about the code stated by N&C (formalised around Exercise 10.49); the exercise asks only for
  the resulting numerical saturation, which this file proves outright.
-/

open scoped BigOperators

namespace AxQM

/-- The left-hand side of the **quantum Hamming bound** (N&C eq. (10.51)) for a code encoding `k`
qubits in `n` qubits and correcting every error on `t` or fewer qubits: the number of correctable
Pauli errors — the Pauli strings of weight `≤ t` on `n` qubits, `Concrete.localPauliStrings t n` —
times the code-space dimension `2ᵏ`. For a non-degenerate code these count the orthogonal
`2ᵏ`-dimensional error subspaces, which must fit inside the `2ⁿ`-dimensional register. -/
def quantumHammingBoundLHS (n k t : ℕ) : ℕ := (Concrete.localPauliStrings t n).card * 2 ^ k

/-- The **quantum Hamming bound** (N&C eq. (10.51)): a non-degenerate code encoding `k` qubits in
`n` qubits and correcting all errors on `≤ t` qubits satisfies
`(number of correctable errors) · 2ᵏ ≤ 2ⁿ`. Stated as a proposition of the code parameters. -/
def QuantumHammingBound (n k t : ℕ) : Prop := quantumHammingBoundLHS n k t ≤ 2 ^ n

/-- The left side of the quantum Hamming bound (10.51) in closed form: `(∑_{j=0}^{t} C(n,j)·3ʲ)·2ᵏ`,
exactly N&C's expression, via the exact Pauli-error count `Concrete.card_localPauliStrings_eq`
(N&C eq. (10.50)). -/
theorem quantumHammingBoundLHS_eq (n k t : ℕ) :
    quantumHammingBoundLHS n k t = (∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j) * 2 ^ k := by
  rw [quantumHammingBoundLHS, Concrete.card_localPauliStrings_eq]

/-- The five-qubit code has exactly `16` correctable single-qubit errors: the identity together with
the `5 · 3 = 15` weight-one Pauli errors (one of `X, Y, Z` on each of the five qubits). Numerically
`C(5,0)·3⁰ + C(5,1)·3¹ = 1 + 15 = 16`. -/
theorem fiveQubitCode_card_correctableErrors :
    (Concrete.localPauliStrings 1 5).card = 16 := by
  rw [Concrete.card_localPauliStrings_eq]; decide

/-- **Nielsen & Chuang, Exercise 10.50.** The five-qubit `[[5,1,3]]` code *saturates* the quantum
Hamming bound (10.51): with `n = 5, k = 1, t = 1` the left side equals the right side,
`quantumHammingBoundLHS 5 1 1 = 16 · 2 = 32 = 2⁵`. So the inequality (10.51) holds with **equality**
— the code is perfect. -/
theorem fiveQubitCode_saturates_quantumHammingBound :
    quantumHammingBoundLHS 5 1 1 = 2 ^ 5 := by
  rw [quantumHammingBoundLHS, fiveQubitCode_card_correctableErrors]
  norm_num

/-- The five-qubit code satisfies the quantum Hamming bound (10.51): `QuantumHammingBound 5 1 1`.
This is `le_of_eq` of the saturation `fiveQubitCode_saturates_quantumHammingBound` — the bound holds
because its two sides are in fact equal. -/
theorem fiveQubitCode_satisfies_quantumHammingBound : QuantumHammingBound 5 1 1 :=
  le_of_eq fiveQubitCode_saturates_quantumHammingBound

end AxQM
