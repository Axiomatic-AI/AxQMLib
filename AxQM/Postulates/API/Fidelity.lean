/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.TraceNorm
import ToMathlib.Analysis.InnerProductSpace.Polar

/-!
# AxQM — the fidelity (Nielsen & Chuang §9.2.2)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, §9.2.2
(equation `(9.53)`, p. 409) define the **fidelity** between two states `ρ` and
`σ` as
```
F(ρ, σ) ≡ tr √(√ρ σ √ρ),
```
the trace of the positive square root of `√ρ · σ · √ρ`. It is a second measure
of distance between quantum states (alongside the trace distance,
`State.traceDistance`) and — as N&C develop across §9.2.2 — underlies a genuine
metric (the angle `A(ρ,σ) = arccos F(ρ,σ)`).

`State.fidelity` formalises this notion: it takes two states and returns the real number `re tr √(√ρ
σ √ρ)`. (The operand `√ρ σ √ρ` is positive semidefinite, so the trace of its CFC square root is a
nonnegative real; the `re` merely extracts it from `ℂ`, exactly as `State.traceOfPow` does for
`tr(ρᵏ)`.) The Nielsen–Chuang Chapter 9 fidelity statements (e.g. Uhlmann's theorem, Thm 9.4) are
stated with `fidelity`.

## Design: the trace-norm form

N&C's defining formula `(9.53)` is not manifestly symmetric, and connecting it
to the operator machinery (Uhlmann's theorem, unitary invariance) is far cleaner
through the equivalent **Schatten-1 / trace-norm** form
```
F(ρ, σ) = ‖√ρ √σ‖₁            (State.fidelity_eq_traceNorm)
```
which N&C themselves use (their `(9.71)`, `tr|√ρ√σ| = tr √(ρ^{1/2}σρ^{1/2})`).
We take `(9.53)` as the *definition* (faithful to the textbook) and prove the
trace-norm identity: `√ρ σ √ρ = A A†` with `A = √ρ √σ`, so
its CFC square root is `|A†|`, whose trace is `‖A†‖₁ = ‖A‖₁`. All the elementary
fidelity facts below (symmetry, nonnegativity, `F(ρ,ρ) = 1`) then reduce to
trace-norm lemmas.

## Main definitions

* `State.fidelity` — the fidelity `tr √(√ρ σ √ρ)` of N&C `(9.53)`.

## Main statements

* `State.adjoint_cfc_sqrt_op` — `(√ρ.op)† = √ρ.op`, self-adjointness of the CFC root.
* `State.adjoint_cfc_sqrt_op_mul` — `(√ρ √σ)† = √σ √ρ`.
* `State.fidelity_eq_traceNorm` — the trace-norm form `F(ρ, σ) = ‖√ρ √σ‖₁`.
* `State.fidelity_comm` — symmetry, `F(ρ, σ) = F(σ, ρ)`.
* `State.fidelity_nonneg` — `0 ≤ F(ρ, σ)`.
* `State.fidelity_self` — `F(ρ, ρ) = 1`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- The **fidelity** between two states `ρ` and `σ` of the system `S`,
Nielsen & Chuang `(9.53)`: `F(ρ, σ) ≡ tr √(√ρ σ √ρ)`, the trace of the positive
square root of `√ρ · σ · √ρ`. Since that operator is positive semidefinite its
CFC square root has a nonnegative real trace, which `re` extracts (as for
`State.traceOfPow`). -/
noncomputable def State.fidelity (ρ σ : State S) : ℝ :=
  RCLike.re ((LinearMap.trace ℂ S.space)
    ↑(cfc Real.sqrt (cfc Real.sqrt ρ.op * σ.op * cfc Real.sqrt ρ.op)))

/-- The **CFC square root of a state's density operator is self-adjoint**,
`(√ρ.op)† = √ρ.op`. A one-line specialisation of Mathlib's `IsSelfAdjoint.cfc`
(a real-valued functional-calculus image is self-adjoint) via `star = adjoint`,
in the `adjoint … = …` spelling the trace-norm manipulations below consume. This
`√ρ` self-adjointness is also needed for the Uhlmann factorisation
`M M† = ρ ⇔ M = √ρ U`. -/
theorem State.adjoint_cfc_sqrt_op (ρ : State S) :
    adjoint (cfc Real.sqrt ρ.op) = cfc Real.sqrt ρ.op := by
  rw [← star_eq_adjoint]; exact IsSelfAdjoint.cfc

/-- The **adjoint of the product `√ρ √σ` is `√σ √ρ`**: `adjoint` is a
`*`-antihomomorphism (`star_mul`) and each CFC square root is self-adjoint
(`State.adjoint_cfc_sqrt_op`). The load-bearing algebraic step shared by the
trace-norm bridge (where `A† = √σ √ρ`) and the symmetry proof. -/
theorem State.adjoint_cfc_sqrt_op_mul (ρ σ : State S) :
    adjoint (cfc Real.sqrt ρ.op * cfc Real.sqrt σ.op)
      = cfc Real.sqrt σ.op * cfc Real.sqrt ρ.op := by
  rw [← star_eq_adjoint, star_mul, star_eq_adjoint, star_eq_adjoint,
    ρ.adjoint_cfc_sqrt_op, σ.adjoint_cfc_sqrt_op]

/-- The **trace-norm form** of the fidelity: `F(ρ, σ) = ‖√ρ √σ‖₁`, the trace norm
of `√ρ √σ` (N&C `(9.71)`). Writing `A := √ρ √σ`, the operand of `(9.53)` is
`√ρ σ √ρ = A A†` (using `√σ √σ = σ` and self-adjointness of the CFC square roots),
so its CFC square root is `|A†|`; then `re tr|A†| = ‖A†‖₁ = ‖A‖₁`. This trace-norm
form is the shape used to prove symmetry, the bounds `0 ≤ F ≤ 1`, and Uhlmann's
theorem. -/
theorem State.fidelity_eq_traceNorm (ρ σ : State S) :
    ρ.fidelity σ = (cfc Real.sqrt ρ.op * cfc Real.sqrt σ.op).traceNorm := by
  set A : S.space →L[ℂ] S.space := cfc Real.sqrt ρ.op * cfc Real.sqrt σ.op with hA
  -- `A† = √σ √ρ`.
  have hadjA : adjoint A = cfc Real.sqrt σ.op * cfc Real.sqrt ρ.op := by
    rw [hA]; exact State.adjoint_cfc_sqrt_op_mul ρ σ
  -- `√σ √σ = σ`.
  have hσ : cfc Real.sqrt σ.op * cfc Real.sqrt σ.op = σ.op :=
    cfc_real_sqrt_mul_self_of_nonneg σ.isDensity.nonneg
  -- The operand of (9.53) factors as `A A†`.
  have hop : cfc Real.sqrt ρ.op * σ.op * cfc Real.sqrt ρ.op = A * adjoint A := by
    have hfac : A * adjoint A
        = cfc Real.sqrt ρ.op * (cfc Real.sqrt σ.op * cfc Real.sqrt σ.op) * cfc Real.sqrt ρ.op := by
      rw [hA, hadjA]; simp only [mul_assoc]
    rw [hfac, hσ]
  -- `cfc √ (A A†) = |A†|`, and `re tr|A†| = ‖A†‖₁ = ‖A‖₁`.
  have hcomp : A.comp (adjoint A) = A * adjoint A := rfl
  have habs : cfc Real.sqrt (A * adjoint A) = (adjoint A).absoluteValue := by
    rw [absoluteValue_eq_cfc_sqrt, adjoint_adjoint, hcomp]
  rw [State.fidelity, hop, habs,
    ← traceNorm_eq_re_trace_of_isPositive (absoluteValue_isPositive _),
    traceNorm_absoluteValue, traceNorm_adjoint]

/-- The fidelity is **symmetric**, `F(ρ, σ) = F(σ, ρ)`: through the trace-norm
bridge, `‖√ρ √σ‖₁ = ‖(√ρ √σ)†‖₁ = ‖√σ √ρ‖₁` (`ContinuousLinearMap.traceNorm_adjoint`
and self-adjointness of the CFC square roots). This symmetry is opaque in the
defining formula `(9.53)` but transparent here — one of N&C's motivations for the
trace-norm form. -/
theorem State.fidelity_comm (ρ σ : State S) : ρ.fidelity σ = σ.fidelity ρ := by
  rw [State.fidelity_eq_traceNorm, State.fidelity_eq_traceNorm,
    ← traceNorm_adjoint (cfc Real.sqrt σ.op * cfc Real.sqrt ρ.op),
    State.adjoint_cfc_sqrt_op_mul σ ρ]

/-- The fidelity is **nonnegative**, `0 ≤ F(ρ, σ)`; immediate from the trace-norm
bridge and `ContinuousLinearMap.traceNorm_nonneg`. -/
theorem State.fidelity_nonneg (ρ σ : State S) : 0 ≤ ρ.fidelity σ := by
  rw [State.fidelity_eq_traceNorm]
  exact traceNorm_nonneg _

/-- The fidelity of a state with **itself is one**, `F(ρ, ρ) = 1`: through the
bridge, `‖√ρ √ρ‖₁ = ‖ρ‖₁ = 1`. Here `cfc_real_sqrt_mul_self_of_nonneg` gives
`√ρ √ρ = ρ`, and a density operator has unit trace norm — its trace norm is the
real part of its trace (`traceNorm_eq_re_trace_of_isPositive`, as `ρ.op` is
positive), which is `1` (`State.trace_op_eq_one`). -/
theorem State.fidelity_self (ρ : State S) : ρ.fidelity ρ = 1 := by
  rw [State.fidelity_eq_traceNorm, cfc_real_sqrt_mul_self_of_nonneg ρ.isDensity.nonneg,
    traceNorm_eq_re_trace_of_isPositive ρ.isPositive_op, ρ.trace_op_eq_one, RCLike.one_re]

end AxQM
