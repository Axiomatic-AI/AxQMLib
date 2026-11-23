/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
public import Mathlib.Topology.MetricSpace.Algebra
public import ToMathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The logarithm as a limit of powers: the `x log x` variant

Extends `Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto` with the analogous limit for
`p⁻¹ * (x ^ (p + 1) - x) → x * log x`, obtained from `tendstoLocallyUniformlyOn_rpow_sub_one_log`
by multiplying by `x`.
-/

public section

open scoped Topology
open Real Filter Set

open Set in
/-- `p⁻¹ * (x ^ (p + 1) - x)` tends uniformly to `x * log x` on compact subsets of `Ioi 0` as
`p` tends to zero. Follows from `tendstoLocallyUniformlyOn_rpow_sub_one_log` via the identity
`p⁻¹ * (x ^ (p + 1) - x) = x * (p⁻¹ * (x ^ p - 1))`. -/
lemma Real.tendstoLocallyUniformlyOn_rpow_succ_sub_self_mul_log :
    TendstoLocallyUniformlyOn (fun (p : ℝ) (x : ℝ) => p⁻¹ * (x ^ (p + 1) - x))
      (fun x => x * log x) (𝓝[>] 0) (Ioi 0) :=
  (((tendstoLocallyUniformlyOn_const_fn id).mul₀
    tendstoLocallyUniformlyOn_rpow_sub_one_log continuousOn_id
    (Real.continuousOn_log.mono fun _ hx ↦ hx.ne')).congr
    fun p x hx ↦ by
      simp only [Pi.mul_apply, id]
      rw [Real.rpow_add_one hx.ne']; ring)

lemma tendsto_rpow_succ_sub_self_mul_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun p => p⁻¹ * (x ^ (p + 1) - x)) (𝓝[>] 0) (𝓝 (x * log x)) :=
  TendstoLocallyUniformlyOn.tendsto_at
    Real.tendstoLocallyUniformlyOn_rpow_succ_sub_self_mul_log (by grind)
