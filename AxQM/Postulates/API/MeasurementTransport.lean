/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import ToMathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.Order.Star.Basic

/-!
# Transporting a measurement's effects across a coisometry (the simulating POVM)

The measurement-simulation step of **Nielsen & Chuang, Proposition 12.14** builds, from a
measurement `mB` that Bob performs on his factor `T`, a measurement Alice performs on her factor `S`
that reproduces Bob's statistics.  N&C's recipe identifies Alice's and Bob's Schmidt bases through a
partial isometry `W : T → S` (`InnerProductSpace.crossSynthesis`, sending Bob's Schmidt vectors to
Alice's) and gives Alice the operators "with the same matrix" — concretely the transported effects
`W Mⱼ† Mⱼ W†` on Alice's system.

This file records the **operator-valued measure** side of that recipe, in full generality for an
arbitrary *coisometry* `W` (any operator whose `W W†` is an orthogonal projector — a star
projection).  Given Bob's measurement `mB` on `T` and such a `W : T → S`,

`Measurement.transportPOVM mB W hW : POVM (Option ι) ℂ S`

is the POVM on Alice's system `S` whose effects are

* `Eⱼ = W Mⱼ† Mⱼ W†`  for each of Bob's outcomes `j` (`elements (some j)`), and
* the **completeness caveat** `E★ = 1 − W W†` for the extra outcome `none` (`elements none`).

Its validity is exactly the two identities behind N&C's construction:

* each `Eⱼ ≥ 0` because conjugation preserves positivity (`IsPositive.conj_adjoint`), and the caveat
  `1 − W W†` is positive because `W W†` is a star projection (`IsStarProjection.one_sub_nonneg`);
* the effects sum to `1` because `∑ⱼ W Mⱼ† Mⱼ W† = W (∑ⱼ Mⱼ† Mⱼ) W† = W W†` (Bob's completeness),
  and the caveat supplies the missing `1 − W W†`.

The caveat outcome is what makes the transported family a *genuine* POVM when `W` is not surjective
(Alice's Schmidt support is a proper subspace, `W W† ≠ 1`) — the dimension-mismatch case a naive
transport of `Mⱼ` mishandles.  Alice's simulating measurement is then the square-root measurement
`Measurement.ofPOVM (transportPOVM mB W hW)` (`Postulates.API.SquareRootMeasurement`); its outcome
`some j` carries `√Eⱼ`, and the caveat outcome `none` never fires on the state whose reduced
operator lives on Alice's Schmidt support (a zero-probability outcome), as used in
the `bobMeasure` closure case of Proposition 12.14 (`AxQM/NC/Ch12/Proposition12_14.lean`).
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S T : QSystem}

/-- **The transported ("simulating") POVM of a measurement across a coisometry.**  Given a
measurement `mB` on `T` and an operator `W : T → S` whose `W W†` is a star projection (a coisometry
onto a subspace of `S`), this is the POVM on Alice's system `S` with effects `W Mⱼ† Mⱼ W†` for each
of `mB`'s outcomes `j` (`some j`) together with the completeness caveat `1 − W W†` (`none`).  This
is the operator-valued measure realising Nielsen & Chuang's Proposition 12.14 measurement
simulation: `W` is the Schmidt-basis identification `InnerProductSpace.crossSynthesis`, and the
effects are the transported "same matrix in the identified basis" operators `Mⱼ` of N&C's recipe.
Each effect is positive (`IsPositive.conj_adjoint`; the caveat by
`IsStarProjection.one_sub_nonneg`) and the effects sum to `1` (`∑ⱼ W Mⱼ† Mⱼ W† = W W†`, using
`mB`'s completeness, plus the caveat `1 − W W†`). -/
def Measurement.transportPOVM (mB : Measurement ι T) (W : T →L[ℂ] S)
    (hW : IsStarProjection (W.comp (adjoint W))) : POVM (Option ι) ℂ S where
  elements
    | some j => W.comp (((adjoint (mB.op j)).comp (mB.op j)).comp (adjoint W))
    | none => 1 - W.comp (adjoint W)
  isPositive
    | some j => (ContinuousLinearMap.isPositive_adjoint_comp_self (mB.op j)).conj_adjoint W
    | none => (ContinuousLinearMap.nonneg_iff_isPositive).mp hW.one_sub_nonneg
  sum_eq_one := by
    simp only [Fintype.sum_option, ← ContinuousLinearMap.comp_finsetSum,
      ← ContinuousLinearMap.finsetSum_comp, mB.complete, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
    abel

@[simp]
theorem Measurement.transportPOVM_elements_some (mB : Measurement ι T) (W : T →L[ℂ] S)
    (hW : IsStarProjection (W.comp (adjoint W))) (j : ι) :
    (mB.transportPOVM W hW).elements (some j)
      = W.comp (((adjoint (mB.op j)).comp (mB.op j)).comp (adjoint W)) := rfl

@[simp]
theorem Measurement.transportPOVM_elements_none (mB : Measurement ι T) (W : T →L[ℂ] S)
    (hW : IsStarProjection (W.comp (adjoint W))) :
    (mB.transportPOVM W hW).elements none = 1 - W.comp (adjoint W) := rfl

end AxQM
