/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HadamardRyRx

/-!
# Nielsen & Chuang, Exercise 7.31 (Hadamard gate from `R_y` and `R_x` rotations)

Construct a Hadamard gate from R_y and R_x rotations.

The exercise appears in §7.6.3 (ion-trap quantum computation, p. 319), where the available
single-qubit gates are the coordinate rotations `R_x(θ) = exp(−iθX/2)` and
`R_y(θ) = exp(−iθY/2)` (written `exp(−iθS_x)`, `exp(−iθS_y)` there, with spin operators
`S_x = X/2`, `S_y = Y/2`); by Theorem 4.1 these generate every single-qubit gate up to a global
phase. A closed-form construction of the Hadamard is

`H = e^{iπ/2} R_x(π) R_y(π/2)`  (global phase `e^{iπ/2} = i`).

The statement is a pure `2 × 2` complex-matrix identity between the
Hadamard matrix `H = (1/√2)[[1,1],[1,-1]]` and a product of the rotation operators
`R_x`, `R_y` (times a phase).

## The formalisation

The construction is in `AxQM/Concrete/HadamardRyRx.lean`, using the rotation
operators `rotX`/`rotY` (`AxQM/Concrete/Rotation.lean`, eqs. 4.4–4.5) and the complex Hadamard
matrix `hadamardC` (`AxQM/Concrete/Hadamard.lean`, eq. 2.85):

* `AxQM.Concrete.rotX_pi_mul_rotY_pi_div_two` — the computational core: the rotation
  product `R_x(π) R_y(π/2) = (√2)⁻¹ !![-i, -i; -i, i]` (` = -i H`).
* `AxQM.Concrete.hadamardC_eq_expPiDivTwo_smul_rotX_rotY` — **Exercise 7.31 itself**:
  `H = e^{iπ/2} • (R_x(π) R_y(π/2))`.

The identity is verified entrywise from the explicit forms of `R_x(π) = -iX` and `R_y(π/2)`, not
asserted; the global phase `e^{iπ/2} = i` is physically unobservable, so the product is the Hadamard
gate.

Compare the closely related `R_x`–`R_z` decomposition of Exercise 4.4: its matrix core is in
`AxQM/Concrete/HadamardRotation.lean`, and `AxQM/NC/Ch4/Exercise4_4.lean` has the theorem
`hadamardGate_evolve_eq_rotXGate_rotZGate_rotXGate_evolve` lifting the matrix identity to an
equality of state evolutions.
-/
