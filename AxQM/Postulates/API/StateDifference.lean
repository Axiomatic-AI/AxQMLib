/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.PosNegPart

/-!
# AxQM — the positive/negative decomposition of a state difference (N&C Ex 9.7)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 9.7 (p. 405):

Any difference of states ρ − σ splits as Q − S with Q, S positive and supported on orthogonal
subspaces.

The difference `ρ.op − σ.op` of two density operators is self-adjoint (each is a positive,
hence self-adjoint, operator), so the general operator Jordan–Hahn decomposition
`ContinuousLinearMap.exists_isPositive_sub_of_isSelfAdjoint`
(`ToMathlib/Analysis/InnerProductSpace/PosNegPart.lean`) applies verbatim: the positive and
negative parts `(ρ.op − σ.op)⁺` and `(ρ.op − σ.op)⁻` are the required positive operators, their
product is `0`, and their ranges (supports) are orthogonal.

The statement is about the density operators `.op` and uses operator/submodule notions
(`IsPositive`, `LinearMap.range`, `Submodule.IsOrtho`). The witnesses `Q, S` are bare positive
operators (not trace one), so the decomposition is inherently a statement about the underlying
operators.

## Main statements

* `State.exists_isPositive_sub_op_sub` — N&C Exercise 9.7: for any states `ρ σ`, there exist
  positive operators `Q R` with `ρ.op − σ.op = Q − R`, `Q * R = 0`, and `range Q ⟂ range R`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Nielsen & Chuang, Exercise 9.7.** For any states `ρ` and `σ` of the system `S`, the
difference of their density operators decomposes as `ρ.op − σ.op = Q − R` with `Q` and `R`
positive operators supported on orthogonal subspaces: `Q * R = 0` and `range Q ⟂ range R`.

The difference `ρ.op − σ.op` is self-adjoint (a difference of positive operators), so this is a
direct instance of the operator positive/negative-part decomposition
`ContinuousLinearMap.exists_isPositive_sub_of_isSelfAdjoint`; the witnesses are the positive and
negative parts `(ρ.op − σ.op)⁺`, `(ρ.op − σ.op)⁻`. (N&C name the two operators `Q` and `S`; here
the second is `R`, `S` being the ambient system.) -/
theorem State.exists_isPositive_sub_op_sub (ρ σ : State S) :
    ∃ Q R : S →L[ℂ] S, Q.IsPositive ∧ R.IsPositive ∧ ρ.op - σ.op = Q - R ∧ Q * R = 0 ∧
      LinearMap.range (Q : S →ₗ[ℂ] S) ⟂ LinearMap.range (R : S →ₗ[ℂ] S) :=
  ContinuousLinearMap.exists_isPositive_sub_of_isSelfAdjoint (ρ.op - σ.op)
    (ρ.isPositive_op.isSelfAdjoint.sub σ.isPositive_op.isSelfAdjoint)

end AxQM
