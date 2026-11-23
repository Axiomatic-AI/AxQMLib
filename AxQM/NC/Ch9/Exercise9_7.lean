/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StateDifference

/-!
# Nielsen & Chuang, Exercise 9.7 (`ρ − σ = Q − S`, positive on orthogonal supports)

Show any states rho-sigma = Q-S with Q,S positive on orthogonal supports.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 9.7 (p. 405).

This is the operator form of the **Jordan–Hahn decomposition**: any self-adjoint operator is the
difference of two positive operators with orthogonal supports. N&C use it immediately in the
proof of Theorem 9.1 (to get `|ρ − σ| = Q + S`), and it recurs throughout Chapter 9.

## Where the formalisation lives

The statement is formalised for general operators and for states:

* **General operator decomposition — `ToMathlib/Analysis/InnerProductSpace/PosNegPart.lean`.**
  `ContinuousLinearMap.exists_isPositive_sub_of_isSelfAdjoint`: a self-adjoint operator `A` on a
  complex Hilbert space is `Q - R` with `Q, R` positive, `Q * R = 0`, and `range Q ⟂ range R`
  (witnesses `A⁺`, `A⁻`). Supporting lemmas `isPositive_posPart` / `isPositive_negPart`
  (`A⁺`, `A⁻` are positive operators) and `isOrtho_range_of_isSelfAdjoint_of_mul_eq_zero`
  (vanishing product ⇒ orthogonal supports).

* **State-difference specialisation — `AxQM/Postulates/API/StateDifference.lean`.**
  `AxQM.State.exists_isPositive_sub_op_sub`: for any states `ρ σ`, there exist positive
  operators `Q R` with `ρ.op − σ.op = Q − R`, `Q * R = 0`, and `range Q ⟂ range R` — Exercise 9.7
  as stated, obtained by applying the operator decomposition to the self-adjoint `ρ.op − σ.op`.
-/
