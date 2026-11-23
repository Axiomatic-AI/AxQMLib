/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Purity
import AxQM.Postulates.API.Fidelity
import AxQM.Postulates.API.TraceDistance
import AxQM.Postulates.API.HSOverlap
import ToMathlib.Analysis.InnerProductSpace.TraceNorm
import ToMathlib.Analysis.InnerProductSpace.OperatorSum
import ToMathlib.Analysis.InnerProductSpace.PowersStormer
import ToMathlib.Analysis.InnerProductSpace.DensitySubunital

/-!
# AxQM.Postulates.API — the quantum affinity of two states

The **quantum affinity** `A(ρ, σ) = re tr(√ρ √σ)` of two density operators (`√· = cfc Real.sqrt`),
a distinguishability measure in the *fidelity family*: like the fidelity `F(ρ, σ) = tr √(√ρ σ √ρ)`
(`State.fidelity`) it is built from the operator square roots, and for commuting states coincides
with it (the Bhattacharyya coefficient `∑ᵢ √(pᵢ qᵢ)`). Always `A(ρ, σ) ≤ F(ρ, σ)` and `A(ρ, ρ) = 1`.

Where the Hilbert–Schmidt overlap `tr(ρ σ)` (`State.hsOverlap`) is the *purity-metric*
distinguishability resource, the affinity is the *fidelity-metric* one: it is the pairwise quantity
governing a **multi-state discrimination measurement**'s error — the pretty-good / square-root
measurement error is controlled by the **sum** `∑_{i ≠ j} A(ρᵢ, ρⱼ)`, not a union bound. This makes
it the resource behind the *linear* sample count in the Ettinger–Høyer–Knill hidden-subgroup
identification (Nielsen & Chuang, Problem 5.5), where a union bound would force a *quadratic* count.

* `State.affinity ρ σ` — `re tr(√ρ √σ)`. `State.affinity_self` records `A(ρ, ρ) = 1`,
  `State.affinity_comm` the symmetry.
* `State.affinity_nonneg` / `State.affinity_le_one` — the affinity lies in `[0, 1]`, a bona-fide
  distinguishability measure (`0 ≤ A` is `re tr` of a product of positives; `A ≤ 1` is
  `0 ≤ tr((√ρ − √σ)²)`).
* `State.affinity_le_fidelity` — `A(ρ, σ) ≤ F(ρ, σ)`: the real trace of `√ρ √σ` is bounded by its
  trace norm `F`. The affinity is therefore the *sharper* fidelity-family resource — the quantity
  the Ettinger–Høyer–Knill discrimination **sum** is taken over.
* `State.one_sub_affinity_le_traceDistance` — `1 - A(ρ, σ) ≤ D(ρ, σ)`: the **operational meaning**
  of the affinity (the fidelity-family Fuchs–van de Graaf lower bound). Via the Powers–Størmer
  inequality (`ContinuousLinearMap.re_trace_sub_mul_self_le_traceNorm_mul_self_sub_mul_self`),
  `2(1 - A(ρ, σ)) = ‖√ρ - √σ‖₂² ≤ ‖ρ - σ‖₁ = 2 D(ρ, σ)`. So a small affinity forces a large trace
  distance: two states with `A(ρ, σ) ≤ δ` are `(1 - δ)`-distinguishable by a single measurement
  (`State.classicalTraceDist_bornProb_le`). This is why the affinity is the operational
  distinguishability resource of the hidden-subgroup identification (Nielsen & Chuang, Problem 5.5):
  the exponentially small `m`-copy affinity `A(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 2^{-m/2}` of distinct
  candidate subgroups makes their reduced states nearly perfectly distinguishable.
-/

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace AxQM

variable {S : QSystem}

/-- The **quantum affinity** `A(ρ, σ) = tr(√ρ √σ)` of two states `ρ σ`, as a real number
(`re tr(√ρ.op √σ.op)`, with `√· = cfc Real.sqrt ·` the operator square root). A fidelity-family
distinguishability measure: `A(ρ, ρ) = tr ρ = 1` (`State.affinity_self`), `A(ρ, σ) ≤ F(ρ, σ)`, and
for commuting states it is the Bhattacharyya coefficient `∑ᵢ √(pᵢ qᵢ)`. It is the pairwise quantity
controlling the error of a pretty-good / square-root multi-state discrimination measurement. -/
def State.affinity (ρ σ : State S) : ℝ :=
  RCLike.re (LinearMap.trace ℂ S
    ((cfc Real.sqrt ρ.op * cfc Real.sqrt σ.op : S →L[ℂ] S) : S →ₗ[ℂ] S))

/-- The **self-affinity is one**: `A(ρ, ρ) = tr(√ρ √ρ) = tr ρ = 1`. Uses
`cfc_real_sqrt_mul_self_of_nonneg` (`√ρ √ρ = ρ`, since `ρ.op ≥ 0`) and `State.trace_op_eq_one`. -/
@[simp]
theorem State.affinity_self (ρ : State S) : ρ.affinity ρ = 1 := by
  have hpos : (0 : S →L[ℂ] S) ≤ ρ.op :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr ρ.isPositive_op
  rw [State.affinity, cfc_real_sqrt_mul_self_of_nonneg hpos, State.trace_op_eq_one]
  simp

/-- **Symmetry of the affinity**: `A(ρ, σ) = A(σ, ρ)`, from the cyclicity of the trace
`tr(√ρ √σ) = tr(√σ √ρ)` (`LinearMap.trace_mul_comm`). -/
theorem State.affinity_comm (ρ σ : State S) : ρ.affinity σ = σ.affinity ρ := by
  rw [State.affinity, State.affinity, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm]

/-- **The affinity is nonnegative**: `0 ≤ A(ρ, σ)`. The affinity is `re tr(√ρ √σ)` with the operator
square roots `√ρ = cfc Real.sqrt ρ.op ≥ 0`, `√σ ≥ 0` positive, so nonnegativity is the real part of
the trace of a product of two positive operators
(`ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg`, via `tr(AB) = tr(√B A √B)`). Together with
`State.affinity_le_one` this places the affinity in `[0, 1]`, a bona-fide distinguishability
measure. -/
theorem State.affinity_nonneg (ρ σ : State S) : 0 ≤ ρ.affinity σ := by
  rw [State.affinity]
  exact ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg
    (cfc_real_sqrt_nonneg ρ.op) (cfc_real_sqrt_nonneg σ.op)

/-- **The affinity is at most one**: `A(ρ, σ) ≤ 1`. The self-adjoint difference `√ρ − √σ` has a
positive square, so `0 ≤ tr((√ρ − √σ)²)`; expanding and using `√ρ √ρ = ρ`, `√σ √σ = σ`
(`cfc_real_sqrt_mul_self_of_nonneg`), `tr ρ = tr σ = 1` (`State.trace_op_eq_one`), and the trace
cyclicity `tr(√σ √ρ) = tr(√ρ √σ)` gives `0 ≤ 2 − 2 A(ρ, σ)`. With `State.affinity_nonneg` this is
the standard `0 ≤ A ≤ 1` range of a fidelity-family distinguishability measure. -/
theorem State.affinity_le_one (ρ σ : State S) : ρ.affinity σ ≤ 1 := by
  set a : S →L[ℂ] S := cfc Real.sqrt ρ.op with ha_def
  set b : S →L[ℂ] S := cfc Real.sqrt σ.op with hb_def
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg (cfc_real_sqrt_nonneg ρ.op)
  have hsb : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg (cfc_real_sqrt_nonneg σ.op)
  -- `0 ≤ (√ρ − √σ)²` (square of a self-adjoint operator is positive).
  have hXX : (0 : S →L[ℂ] S) ≤ (a - b) * (a - b) := by
    have hX : IsSelfAdjoint (a - b) := hsa.sub hsb
    simpa [hX.star_eq] using star_mul_self_nonneg (a - b)
  have hre : 0 ≤ RCLike.re
      (LinearMap.trace ℂ S (((a - b) * (a - b) : S →L[ℂ] S) : S →ₗ[ℂ] S)) := by
    simpa using ContinuousLinearMap.re_trace_mul_nonneg_of_nonneg hXX (zero_le_one)
  -- `√ρ √ρ = ρ`, `√σ √σ = σ`, hence their traces are `1`.
  have hpρ : (0 : S →L[ℂ] S) ≤ ρ.op :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr ρ.isPositive_op
  have hpσ : (0 : S →L[ℂ] S) ≤ σ.op :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr σ.isPositive_op
  have haa : a * a = ρ.op := by rw [ha_def]; exact cfc_real_sqrt_mul_self_of_nonneg hpρ
  have hbb : b * b = σ.op := by rw [hb_def]; exact cfc_real_sqrt_mul_self_of_nonneg hpσ
  -- The affinity is the real trace of `√ρ √σ = a b`.
  have haff : ρ.affinity σ =
      RCLike.re (LinearMap.trace ℂ S ((a * b : S →L[ℂ] S) : S →ₗ[ℂ] S)) := by
    rw [State.affinity, ha_def, hb_def]
  -- Expand `(a − b)² = a² − ab − ba + b²`, distribute the trace, take the real part.
  have hexp : (a - b) * (a - b) = a * a - a * b - (b * a) + b * b := by noncomm_ring
  have hcomm : LinearMap.trace ℂ S ((b * a : S →L[ℂ] S) : S →ₗ[ℂ] S)
      = LinearMap.trace ℂ S ((a * b : S →L[ℂ] S) : S →ₗ[ℂ] S) := by
    rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
        LinearMap.trace_mul_comm]
  rw [hexp] at hre
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_add, map_sub,
      map_add] at hre
  rw [hcomm, haa, hbb, State.trace_op_eq_one, State.trace_op_eq_one] at hre
  simp only [RCLike.one_re] at hre
  rw [haff]
  linarith

/-- **The affinity is dominated by the fidelity**: `A(ρ, σ) ≤ F(ρ, σ)` (Nielsen & Chuang, eq. 9.53
sense: the affinity is the *real trace* of `√ρ √σ`, the fidelity its *trace norm*, and the real
trace of any operator is bounded by its trace norm). Formally `F(ρ, σ) = ‖√ρ √σ‖₁`
(`State.fidelity_eq_traceNorm`), and pairing `√ρ √σ` with the contraction `1` in the variational
characterization of the trace norm (`re_hsPairing_le_traceNorm_of_opNorm_le_one`, with
`hsPairing T 1 = tr T`) gives `re tr(√ρ √σ) ≤ ‖√ρ √σ‖₁`. This is why the affinity — never larger
than the fidelity — is the sharper resource for the Ettinger–Høyer–Knill discrimination sum. -/
theorem State.affinity_le_fidelity (ρ σ : State S) : ρ.affinity σ ≤ ρ.fidelity σ := by
  rw [State.affinity, State.fidelity_eq_traceNorm]
  have hadj : (1 : S →L[ℂ] S).adjoint = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hW : ‖(1 : S →L[ℂ] S)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h := (cfc Real.sqrt ρ.op * cfc Real.sqrt σ.op).re_hsPairing_le_traceNorm_of_opNorm_le_one hW
  rw [ContinuousLinearMap.hsPairing_eq, hadj] at h
  simpa [Module.End.one_eq_id] using h

/-- **The Hilbert–Schmidt overlap is dominated by the affinity**: `⟨ρ, σ⟩_HS ≤ A(ρ, σ)`, i.e.
`re tr(ρ σ) ≤ re tr(√ρ √σ)`. Both density operators satisfy `ρ.op ≤ 1`, `σ.op ≤ 1`
(`ContinuousLinearMap.IsDensityOp.le_one`), so the general sub-unital operator inequality
`ContinuousLinearMap.re_trace_mul_le_re_trace_cfc_sqrt_mul` (each of `ρ.op, σ.op` is below its own
square root, `A ≤ √A` for `0 ≤ A ≤ 1`) applies directly. Together with `State.affinity_le_fidelity`
(`A ≤ F`) this orders the three distinguishability quantities of the near-orthogonality analysis,
`⟨ρ, σ⟩_HS ≤ A(ρ, σ) ≤ F(ρ, σ)`: the Hilbert–Schmidt (purity-metric) overlap is the smallest, the
fidelity the largest. In the Ettinger–Høyer–Knill hidden-subgroup problem (Nielsen & Chuang, Problem
5.5) this is why the affinity — never below the overlap — is the safe pairwise resource the
discrimination *sum* is taken over: a bound on the affinity sum bounds the overlap sum a
fortiori. -/
theorem State.hsOverlap_le_affinity (ρ σ : State S) : ρ.hsOverlap σ ≤ ρ.affinity σ := by
  rw [State.hsOverlap, State.affinity]
  exact ContinuousLinearMap.re_trace_mul_le_re_trace_cfc_sqrt_mul
    ((ContinuousLinearMap.nonneg_iff_isPositive).mpr ρ.isPositive_op)
    (ContinuousLinearMap.IsDensityOp.le_one ρ.isDensity)
    ((ContinuousLinearMap.nonneg_iff_isPositive).mpr σ.isPositive_op)
    (ContinuousLinearMap.IsDensityOp.le_one σ.isDensity)

/-- **The operational meaning of the affinity**: `1 - A(ρ, σ) ≤ D(ρ, σ)` (the fidelity-family
Fuchs–van de Graaf lower bound). The affinity `A(ρ, σ) = re tr(√ρ √σ)` is related to the operator
Hilbert–Schmidt distance of the square roots by `‖√ρ - √σ‖₂² = tr((√ρ - √σ)²) = 2 - 2 A(ρ, σ)`
(using `√ρ √ρ = ρ`, `√σ √σ = σ`, `tr ρ = tr σ = 1`, and trace cyclicity), and the **Powers–Størmer
inequality** (`ContinuousLinearMap.re_trace_sub_mul_self_le_traceNorm_mul_self_sub_mul_self`) bounds
this by the trace-norm distance of the states, `‖√ρ² - √σ²‖₁ = ‖ρ - σ‖₁ = 2 D(ρ, σ)`. Dividing by
`2` gives
`1 - A(ρ, σ) ≤ D(ρ, σ)`.

This is the sense in which the affinity is a *distinguishability resource*: a small affinity forces
a large trace distance, and by `State.classicalTraceDist_bornProb_le` two states are distinguishable
by a single measurement with error at most `1 - D(ρ, σ) ≤ A(ρ, σ)`. In the Ettinger–Høyer–Knill
hidden-subgroup problem (Nielsen & Chuang, Problem 5.5) the `m`-copy coset reduced states of
distinct candidate subgroups have exponentially small affinity
`A(σ_K^{⊗m}, σ_{K'}^{⊗m}) ≤ 2^{-m/2}`, so this
bound makes them nearly perfectly distinguishable (trace distance `≥ 1 - 2^{-m/2}`). -/
theorem State.one_sub_affinity_le_traceDistance (ρ σ : State S) :
    1 - ρ.affinity σ ≤ ρ.traceDistance σ := by
  set a : S →L[ℂ] S := cfc Real.sqrt ρ.op with ha_def
  set b : S →L[ℂ] S := cfc Real.sqrt σ.op with hb_def
  have hpρ : (0 : S →L[ℂ] S) ≤ ρ.op :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr ρ.isPositive_op
  have hpσ : (0 : S →L[ℂ] S) ≤ σ.op :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr σ.isPositive_op
  have haa : a * a = ρ.op := by rw [ha_def]; exact cfc_real_sqrt_mul_self_of_nonneg hpρ
  have hbb : b * b = σ.op := by rw [hb_def]; exact cfc_real_sqrt_mul_self_of_nonneg hpσ
  -- Powers–Størmer at `√ρ, √σ`: `re tr((√ρ − √σ)²) ≤ ‖√ρ² − √σ²‖₁ = ‖ρ − σ‖₁`.
  have hps := ContinuousLinearMap.re_trace_sub_mul_self_le_traceNorm_mul_self_sub_mul_self
    (cfc_real_sqrt_nonneg ρ.op) (cfc_real_sqrt_nonneg σ.op)
  rw [← ha_def, ← hb_def, haa, hbb] at hps
  -- The affinity is `re tr(√ρ √σ) = re tr(a b)`.
  have haff : ρ.affinity σ = RCLike.re (LinearMap.trace ℂ S ((a * b : S →L[ℂ] S) : S →ₗ[ℂ] S)) := by
    rw [State.affinity, ha_def, hb_def]
  -- Expand `(√ρ − √σ)² = ρ − √ρ√σ − √σ√ρ + σ`, distribute the trace, take the real part.
  have hexp : (a - b) * (a - b) = a * a - a * b - (b * a) + b * b := by noncomm_ring
  have hcomm : LinearMap.trace ℂ S ((b * a : S →L[ℂ] S) : S →ₗ[ℂ] S)
      = LinearMap.trace ℂ S ((a * b : S →L[ℂ] S) : S →ₗ[ℂ] S) := by
    rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul,
        LinearMap.trace_mul_comm]
  rw [hexp] at hps
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_add, map_sub,
      map_add] at hps
  rw [hcomm, haa, hbb, State.trace_op_eq_one, State.trace_op_eq_one] at hps
  simp only [RCLike.one_re] at hps
  -- `2 − 2 A(ρ, σ) ≤ ‖ρ − σ‖₁ = 2 D(ρ, σ)`, hence `1 − A(ρ, σ) ≤ D(ρ, σ)`.
  rw [haff, State.traceDistance_eq]
  linarith

end AxQM
