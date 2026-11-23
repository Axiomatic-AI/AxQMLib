/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HadamardTGate

/-!
# Nielsen & Chuang, Exercise 4.14 (`H T H = R_x(π/4)` up to a global phase)

*(N&C p. 177.)*

Show HTH=R_x(pi/4) up to a global phase.

Here `T` is the π/8 gate `T = diag(1, e^{iπ/4})` (eq. 4.2), `H` is the Hadamard gate (eq. 2.54),
and `R_x(θ) = exp(-iθX/2)` is the `x̂`-axis rotation (eq. 4.4). The identity holds up to the
unit-modulus global phase `e^{iπ/8}`:

`H T H = e^{iπ/8} R_x(π/4)`.

The statement is a `2 × 2` complex-matrix identity — the concrete Hadamard matrix, the concrete
π/8-gate matrix, and the concrete rotation `R_x`.

## The formalisation

The identity is in `AxQM/Concrete/HadamardTGate.lean`:

* `AxQM.Concrete.hadamardC_mul_tMatrix_mul_hadamardC` — **Exercise 4.14 itself**:
  `H T H = e^{iπ/8} • R_x(π/4)`.

The "up to a global phase" clause is captured by an **exact** matrix identity with the explicit
unit-modulus scalar `e^{iπ/8}` (the same idiom as Exercise 4.3's `T = e^{iπ/8} • R_z(π/4)`), not a
weakened statement. The proof composes two already-formalised facts: Exercise 4.3
(`Concrete.tMatrix_eq_expPiDivEight_smul_rotZ`, `T = e^{iπ/8} • R_z(π/4)`) and the Hadamard
conjugation lemma (`Concrete.hadamardC_mul_rotZ_mul_hadamardC`, `H R_z(θ) H = R_x(θ)`, from
Exercise 4.10) — `H T H = e^{iπ/8} (H R_z(π/4) H) = e^{iπ/8} R_x(π/4)` — exactly N&C's own
argument that `T = R_z(π/4)` up to phase and that `H` carries `R_z(θ)` to `R_x(θ)`.
-/
