/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import ToMathlib.Analysis.InnerProductSpace.CFC
import ToMathlib.Analysis.InnerProductSpace.Uhlmann

/-!
# The square-root measurement realising a POVM (the `POVM → Measurement` bridge)

A `Measurement ι S` stores *measurement operators* `Mᵢ` together with the
completeness relation `∑ᵢ Mᵢ† Mᵢ = 1`; its induced POVM `toPOVM` has effects `Eᵢ = Mᵢ† Mᵢ`
(`Measurement.toPOVM`).  Going the other way — realising a *given* POVM `{Eᵢ}` (positive effects
summing to `1`) as an actual measurement — requires choosing measurement operators `Mᵢ` with
`Mᵢ† Mᵢ = Eᵢ`.  The **canonical** such choice is `Mᵢ = √Eᵢ`, the operator square root
(`cfc Real.sqrt Eᵢ`): it is self-adjoint (`(√Eᵢ)† = √Eᵢ`) and squares back to the effect
(`√Eᵢ · √Eᵢ = Eᵢ` for `Eᵢ ≥ 0`), so `Mᵢ† Mᵢ = Eᵢ` and completeness `∑ᵢ √Eᵢ† √Eᵢ = ∑ᵢ Eᵢ = 1`
transports directly from the POVM.  This is the **square-root (or "pretty-good") measurement**
of `{Eᵢ}`.

`Measurement.ofPOVM` records this bridge, the partial inverse of `Measurement.toPOVM`
(`toPOVM (ofPOVM P) = P`).  It is the missing constructor needed to turn a family of positive
effects back into a postulate `Measurement`, used in the achievability half of the
**Holevo–Schumacher–Westmoreland theorem** (`χ(E) = C⁽¹⁾(E)`, Nielsen & Chuang Theorem 12.8) to
build the pretty-good decoding POVM `{Eₘ}` (N&C eq. (12.78)) as a genuine measurement, and to
supply the "junk" element `√(1 − ∑ Eₘ)` completing a sub-code's POVM after expurgation.

## What this file provides

* `AxQM.Measurement.ofPOVM` — the square-root measurement `Mᵢ = √Eᵢ` of a POVM `P`.
* `AxQM.Measurement.ofPOVM_op` — its operators, `(ofPOVM P).op i = √(P.elements i)`.
* `AxQM.Measurement.toPOVM_ofPOVM` — the round-trip `(ofPOVM P).toPOVM = P`: the
  square-root measurement induces exactly the POVM it was built from.
* `AxQM.Measurement.ofPOVM_bornProb` / `ofPOVM_bornProb_eq_re_trace` — its Born rule is the
  POVM Born rule, `p(i) = P.toPMF ρ = re tr(Eᵢ ρ)`.

The other `Measurement` constructors are in `Postulates.API.MeasurementModel`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **The operator square root squares back through the adjoint**: for a positive operator `A ≥ 0`
on a complex Hilbert space, `(√A)† √A = A`, where `√A = cfc Real.sqrt A`.  Since `√A` is
self-adjoint (`adjoint_cfc_real_sqrt`) this is `√A · √A = A`, the C⋆-algebra square-root identity
`cfc_real_sqrt_mul_self_of_nonneg`.  The completeness datum of the square-root measurement
`Measurement.ofPOVM`. -/
private theorem cfc_real_sqrt_adjoint_comp_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    (ContinuousLinearMap.adjoint (cfc Real.sqrt A)).comp (cfc Real.sqrt A) = A := by
  rw [ContinuousLinearMap.adjoint_cfc_real_sqrt, ← ContinuousLinearMap.mul_def,
    cfc_real_sqrt_mul_self_of_nonneg hA]

variable {ι : Type*} [Fintype ι] {S : QSystem}

/-- **The square-root ("pretty-good") measurement realising a POVM** `P` on the system `S`: the
measurement whose operators are the operator square roots of the POVM's effects,
`Mᵢ = √Eᵢ = cfc Real.sqrt (P.elements i)`.  Completeness `∑ᵢ Mᵢ† Mᵢ = ∑ᵢ Eᵢ = 1` holds because each
`√Eᵢ` is self-adjoint and `√Eᵢ · √Eᵢ = Eᵢ` (`cfc_real_sqrt_adjoint_comp_self`), reducing the sum to
the POVM's own `∑ᵢ Eᵢ = 1`.  This is the canonical partial inverse of `Measurement.toPOVM`
(`toPOVM_ofPOVM`), turning a family of positive effects back into a postulate `Measurement`. -/
def Measurement.ofPOVM (P : POVM ι ℂ S.space) : Measurement ι S where
  op i := cfc Real.sqrt (P.elements i)
  complete :=
    calc ∑ i, (ContinuousLinearMap.adjoint (cfc Real.sqrt (P.elements i))).comp
            (cfc Real.sqrt (P.elements i))
        = ∑ i, P.elements i :=
          Finset.sum_congr rfl fun i _ =>
            cfc_real_sqrt_adjoint_comp_self
              ((ContinuousLinearMap.nonneg_iff_isPositive).mpr (P.isPositive i))
      _ = 1 := P.sum_eq_one

@[simp]
theorem Measurement.ofPOVM_op (P : POVM ι ℂ S.space) (i : ι) :
    (Measurement.ofPOVM P).op i = cfc Real.sqrt (P.elements i) := rfl

/-- **Round-trip**: the square-root measurement of a POVM induces exactly that POVM,
`(ofPOVM P).toPOVM = P`.  Each induced effect is `(√Eᵢ)† √Eᵢ = Eᵢ`
(`cfc_real_sqrt_adjoint_comp_self`), so the two POVMs agree on all effects (`POVM.ext`).  Thus
`Measurement.ofPOVM` is a genuine section of `Measurement.toPOVM`. -/
@[simp]
theorem Measurement.toPOVM_ofPOVM (P : POVM ι ℂ S.space) :
    (Measurement.ofPOVM P).toPOVM = P := by
  refine POVM.ext (funext fun i => ?_)
  rw [Measurement.toPOVM_elements, Measurement.ofPOVM_op]
  exact cfc_real_sqrt_adjoint_comp_self
    ((ContinuousLinearMap.nonneg_iff_isPositive).mpr (P.isPositive i))

/-- **Born rule of the square-root measurement**: measuring `ofPOVM P` on a state `ρ` gives outcome
`i` with the POVM's own Born probability, `(ofPOVM P).bornProb ρ i = P.toPMF ρ`.  Immediate from the
round-trip `toPOVM_ofPOVM`, since `bornProb` is by definition the induced POVM's `toPMF`. -/
theorem Measurement.ofPOVM_bornProb (P : POVM ι ℂ S.space) (ρ : State S) (i : ι) :
    (Measurement.ofPOVM P).bornProb ρ i = P.toPMF ρ.op i := by
  rw [Measurement.bornProb, Measurement.toPOVM_ofPOVM]

/-- **Born rule of the square-root measurement, trace form**: `p(i) = re tr(Eᵢ ρ)`, the standard
POVM Born rule for the effect `Eᵢ = P.elements i`.  Combines `ofPOVM_bornProb` with the POVM Born
rule `POVM.toPMF_eq`. -/
theorem Measurement.ofPOVM_bornProb_eq_re_trace (P : POVM ι ℂ S.space) (ρ : State S) (i : ι) :
    (Measurement.ofPOVM P).bornProb ρ i
      = RCLike.re ((LinearMap.trace ℂ S.space)
          ((P.elements i).comp ρ.op : S.space →ₗ[ℂ] S.space)) := by
  rw [Measurement.ofPOVM_bornProb, POVM.toPMF_eq]

end AxQM
