/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.GroverPhaseShift

/-!
# Nielsen & Chuang, Exercise 6.1 (the Grover phase shift is `2|0⟩⟨0| − I`)

*(N&C p. 251.)*

Show the unitary operator for the Grover phase shift is 2|0><0| - I.

Step (3) of the Grover iteration (N&C §6.1.2, eq. (6.5)) performs a **conditional phase shift** on
the `n`-qubit register, with every computational basis state except `|0⟩` receiving a phase of `−1`:
`|x⟩ ↦ -(-1)^{δ_{x0}} |x⟩` — i.e. `|0⟩` is fixed and every other basis state is negated. The
exercise is the algebraic identity that this operator equals `2|0⟩⟨0| − I`.

## The formalisation

The statement is pure linear algebra on complex matrices: the diagonal operator, the outer product
`|0⟩⟨0|`, the identity, and unitarity. It is formalised in
`AxQM/Concrete/GroverPhaseShift.lean`, for an arbitrary register dimension `N = d + 1`
(indices `Fin (d + 1)`; the identity holds for every `N ≥ 1`, not only powers of two):

* `AxQM.Concrete.groverPhaseShift` — the operator of (6.5), the diagonal matrix
  `diag(1, −1, …, −1)` that fixes `|0⟩` and negates every other basis state.
* `AxQM.Concrete.groverPhaseShift_mulVec_stdVec` — its action `|x⟩ ↦ -(-1)^{δ_{x0}} |x⟩`,
  reproducing (6.5) verbatim: this is what makes the matrix *the* conditional phase shift.
* `AxQM.Concrete.groverPhaseShift_eq_two_ketBraZero_sub_one` — **Exercise 6.1**:
  `groverPhaseShift = 2|0⟩⟨0| − I`, with `|0⟩⟨0|` the outer product of `|0⟩` with its conjugate
  transpose (`Matrix.vecMulVec (stdVec 0) (star (stdVec 0))`).
* `AxQM.Concrete.groverPhaseShift_mem_unitaryGroup` — it is a *unitary* operator, as the
  exercise's phrasing asserts (a real `±1` diagonal, hence a Hermitian involution).
-/
