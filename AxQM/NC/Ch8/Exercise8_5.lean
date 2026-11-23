/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SpinFlipOperatorSum

/-!
# Nielsen & Chuang, Exercise 8.5 (Spin flips)

*(N&C p. 361.)*

Give operator-sum representation for spin-flip interaction U=(X/√2)⊗I+(Y/√2)⊗X.

## The formalisation

As in Exercise 8.4, a single-qubit principal system interacts with a single-qubit environment
prepared in `|0⟩`, through the unitary `U` above (the first tensor factor acting on the system, the
second on the environment), and the environment is then discarded. The resulting quantum operation
is `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)` (N&C eq. 8.9), and the exercise asks for its operator-sum
representation `E(ρ) = Σₖ Eₖ ρ Eₖ†` with operation elements `Eₖ = ⟨eₖ|U|e₀⟩` (N&C eqs. 8.9–8.10).

Reading `Eₖ = ⟨k|U|0⟩` off `U` (the environment matrix element at `|0⟩`) gives

`E₀ = X/√2`,   `E₁ = Y/√2`,

so the **answer** is the operator-sum representation

`E(ρ) = ½ XρX + ½ YρY`,

the equal-weight bit-and-phase mixture — a genuine (trace-preserving) quantum operation, with the
completeness relation `E₀† E₀ + E₁† E₁ = ½ X² + ½ Y² = I` (N&C eq. 8.14) certifying it preserves
trace. The statement is `AxQM.Concrete.spinFlipChannel_eq_kraus`.

## Supporting results

The formal content of Exercise 8.5 is a computation on concrete `2 × 2` / `4 × 4` complex matrices:
the named unitary `U` built from the Pauli matrices, the reduced dynamics
`tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`, and the operator-sum identity. The output map `E` is a mixing
channel — it is *not* unitary, so it is not an instance of the closed-system `Evolution`. Compare
Problem 8.1 (amplitude damping) and Exercise 8.4 (`AxQM/Concrete/ControlledFlipOperatorSum.lean`).

The formalisation uses the following results.

* Mathlib and `ToMathlib/`: the Kronecker mixed-product rule
  `Matrix.mul_kronecker_mul` (`(A ⊗ₖ B)(C ⊗ₖ D) = (AC) ⊗ₖ (BD)`), which folds each three-fold
  matrix product into a single Kronecker product, and `Matrix.IsHermitian.mem_unitaryGroup`, by
  which a Hermitian involution is unitary.

* `AxQM/Concrete/Pauli.lean`: the single-qubit Pauli matrices
  `Concrete.pauliX`, `Concrete.pauliY`, `Concrete.pauliI`, with the algebra used here —
  `pauliX_mul_self`/`pauliY_mul_self` (`X² = Y² = I`), `pauliX_isHermitian`/`pauliY_isHermitian`,
  and the anticommutation `pauliX_anticomm_pauliY` (`XY + YX = 0`).

* `AxQM/Concrete/PauliOuterProduct.lean`: the computational-basis
  outer products `Concrete.ketBra i j = |i⟩⟨j|`, providing the environment state `|0⟩⟨0|` and the
  matrix elements arising under conjugation.

* `AxQM/Concrete/SpinFlipOperatorSum.lean`:
  * `Concrete.matrixPartialTraceRight` — the partial trace over the environment tensor factor, as a
    `ℂ`-linear map; `matrixPartialTraceRight_kronecker` (`tr_env (M ⊗ₖ N) = tr(N) • M`) fixes it as
    the genuine partial trace.
  * `Concrete.spinFlipScale` — the amplitude `1/√2`; `spinFlipScale_mul_self` (`(1/√2)² = 1/2`),
    `spinFlipScale_star` (real, hence conjugation-fixed).
  * `Concrete.spinFlipU` — the interaction unitary `U = (X/√2) ⊗ I + (Y/√2) ⊗ X` (eq. 8.17);
    `spinFlipU_isHermitian`, `spinFlipU_mul_self` (`U² = I` via `{X, Y} = 0`), and
    `spinFlipU_mem_unitaryGroup` (`U` is unitary — so `E` is a genuine reduced dynamics of a closed
    two-qubit evolution).
  * `Concrete.spinFlipKraus` — the operation elements `E₀ = X/√2`, `E₁ = Y/√2`;
    `spinFlipKraus_eq_matrixElement` derives them as the environment matrix elements `⟨k|U|0⟩` of
    `U` (eq. 8.10), so they are read off `U` as N&C prescribes rather than posited; and
    `spinFlipKraus_completeness` is `Σₖ Eₖ† Eₖ = I` (eq. 8.14, trace preservation).
  * `Concrete.spinFlipChannel` — the quantum operation `E(ρ) = tr_env(U (ρ ⊗ |0⟩⟨0|) U†)`, with:
    * `Concrete.spinFlipChannel_eq_kraus` — **the answer the exercise asks for:** the operator-sum
      representation `E(ρ) = Σₖ Eₖ ρ Eₖ†`, proved for an *arbitrary* `ρ` (the physical reduced
      dynamics equals the sum, not merely a computation of the operation elements);
    * `Concrete.spinFlipChannel_eq` — the explicit closed form `E(ρ) = ½ XρX + ½ YρY`.

See the module docstring of `AxQM/Concrete/SpinFlipOperatorSum.lean` for the full argument.
-/
