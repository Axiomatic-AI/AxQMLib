/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliAverage

/-!
# Nielsen & Chuang, Exercise 8.17 (`I/2 = (ρ + XρX + YρY + ZρZ)/4` via the Pauli average `E`)

*(N&C p. 379.)*

Verify I/2=(ρ+XρX+YρY+ZρZ)/4 via E(A)=(A+XAX+YAY+ZAZ)/4 and Bloch representation.

Here (8.101) is the identity that recasts the depolarizing channel `E(ρ) = pI/2 + (1−p)ρ` (8.100)
into an operator-sum form (8.102): substituting `I/2 = (ρ + XρX + YρY + ZρZ)/4` gives operation
elements `{√(1−3p/4) I, √(p)/2 X, √(p)/2 Y, √(p)/2 Z}`.

## The verification

The map `E(A) = (A + XAX + YAY + ZAZ)/4` averages `A` over conjugation by the four Pauli matrices
`I, X, Y, Z`. Conjugating a `2 × 2` matrix by `X`, `Y`, `Z` permutes and sign-flips its entries, and
the four contributions cancel off the diagonal while the diagonal entries add to `2 · tr A`:

`A + XAX + YAY + ZAZ = (2 · tr A) · I`,   hence   `E(A) = (tr A / 2) · I`.

The three displays follow by specialising the trace. `tr I = 2` gives `E(I) = I`; the non-identity
Pauli matrices are traceless (`tr X = tr Y = tr Z = 0`), giving `E(X) = E(Y) = E(Z) = 0` — that is
(8.105). Writing a single-qubit density matrix in the **Bloch representation**
`ρ = ½(I + r·σ)`, which has `tr ρ = 1`, gives `E(ρ) = ½ I = I/2` — exactly (8.101). (The identity
in fact holds for every trace-one matrix, so no positivity constraint on the Bloch vector `r` is
needed.)

## The formalisation

The formal content of Exercise 8.17 is pure linear algebra about `2 × 2` complex matrices and the
Pauli matrices (`Matrix`, `Concrete.pauliX/Y/Z`, `Concrete.blochMatrix`). It uses the Pauli matrices
(`AxQM/Concrete/Pauli.lean`) and Bloch matrices (`AxQM/Concrete/BlochMatrix.lean`), including the
traces `pauliX/Y/Z_trace`, `trace_one_fin_two` and `blochMatrix_trace`. Compare Exercises 8.12 and
8.14.

The formalisation is in `AxQM/Concrete/PauliAverage.lean`:

* `AxQM.Concrete.pauliAverage` — the map `E(A) = (A + XAX + YAY + ZAZ)/4`, N&C
  eq. (8.104).
* `AxQM.Concrete.pauliConjSum_eq` — the engine: for every `2 × 2` matrix `A`,
  `A + XAX + YAY + ZAZ = (2 · tr A) • I`.
* `AxQM.Concrete.pauliAverage_eq_trace` — its closed form `E(A) = (½ · tr A) • I`.
* `AxQM.Concrete.pauliAverage_one` — **eq. (8.105)** `E(I) = I`.
* `AxQM.Concrete.pauliAverage_pauliX`, `…_pauliY`, `…_pauliZ` — **eq. (8.105)**
  `E(X) = E(Y) = E(Z) = 0`.
* `AxQM.Concrete.pauliAverage_blochMatrix` — **eq. (8.101)**: for `ρ = blochMatrix r`
  (the Bloch representation `½(I + r·σ)` of a single-qubit density matrix), `E(ρ) = ½ I = I/2`.

See the module docstring of `AxQM/Concrete/PauliAverage.lean` for the full argument.
-/
