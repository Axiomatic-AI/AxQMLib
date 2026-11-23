/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.Pauli

/-!
# Nielsen & Chuang, Exercise 2.36 (The Pauli matrices except `I` are traceless)

Show the Pauli matrices except I have trace zero.

The statement is `2 × 2` complex-matrix arithmetic: the trace (sum of diagonal entries) of each
Pauli matrix `X`, `Y`, `Z` (`pauliX`, `pauliY`, `pauliZ`).

## The declarations

The formalisation is in `AxQM/Concrete/Pauli.lean`, alongside the Pauli-matrix definitions and
their other per-matrix structural facts (Hermitian, unitary, involution):

* `AxQM.Concrete.pauliX_trace` — `tr X = 0`.
* `AxQM.Concrete.pauliY_trace` — `tr Y = 0`.
* `AxQM.Concrete.pauliZ_trace` — `tr Z = 0`.

Each is proved by expanding the trace as the sum of the two diagonal entries (`Fin.sum_univ_two`):
`X` and `Y` have zero diagonals, and `Z`'s diagonal `1, -1` cancels.

The exercise's qualifier "except for `I`" is made honest by the contrasting fact

* `AxQM.Concrete.trace_one_fin_two` — `tr I = 2`,

which shows the identity `σ₀ = I` is genuinely the one Pauli matrix that is *not* traceless. (The
non-vanishing `2 ≠ 0` holds in `ℂ`, so `I` is the sole exception among the four Paulis.)
-/
