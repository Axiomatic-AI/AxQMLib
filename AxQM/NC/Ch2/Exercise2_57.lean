/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CascadedMeasurement

/-!
# Nielsen & Chuang, Exercise 2.57 (cascaded measurements are single measurements)

Show cascaded measurements {L_l} then {M_m} equal single measurement N_lm=M_m L_l.

The general measurement postulate (Postulate 3 / §2.2.3) gives `Measurement`, and the single
measurement `{N₍ₗ,ₘ₎}` is `Measurement.cascade` (in `AxQM/Postulates/API/CascadedMeasurement.lean`):
forming `L.cascade M` discharges the completeness obligation `∑₍ₗ,ₘ₎ N₍ₗ,ₘ₎† N₍ₗ,ₘ₎ = 1`, so
its mere well-formedness *is* the fact that the composite is a legitimate single measurement.

"Physically equivalent" is then made precise by two theorems here, about the Born probability
(`bornProb`, Postulate 3) and the state update (`postMeasurement`, Postulate 4):

* `cascade_bornProb` — the joint outcome probability factorizes as `p(l, m) = p(l) · p(m ∣ l)`:
  the cascade's Born probability for outcome `(l, m)` equals the probability of `l` under `L`
  times the probability of `m` under `M` *in the state left by `L`'s outcome `l`*. This is the
  chained probability of the two-step process, and it is exactly the single measurement's
  probability for the joint outcome.
* `cascade_postMeasurement` — the post-measurement states agree: collapsing under the single
  measurement `N` for outcome `(l, m)` yields the same `State` as collapsing under `L` (outcome
  `l`) and then under `M` (outcome `m`). Equality of `State`s is equality of density operators
  (`State.ext`).

Together these say the two procedures assign identical probabilities and identical
post-measurement states to every joint outcome — i.e. they are physically indistinguishable.

Both theorems are hypothesized on `L`'s outcome `l` being possible (`hl : L.bornProb ρ l ≠ 0`),
which is exactly what is needed for the intermediate state `L.postMeasurement ρ l hl` (Postulate 4
collapse) to be defined; the state theorem additionally assumes `M`'s outcome `m` is then possible
(`hm`), from which the joint outcome's possibility for `N` is derived via `cascade_bornProb`.

The theorems are stated for `Measurement`, `State`, `bornProb`, `postMeasurement` and `cascade`;
the construction and its bridges (`cascade`, `cascade_op`, `postOp_cascade`) are in
`AxQM/Postulates/API/CascadedMeasurement.lean`. The general operator-algebra facts they rest on
(`ContinuousLinearMap.postOp_smul`, `postState_smul` — the post-measurement operation is linear in
`ρ`, and the collapse is invariant under rescaling `ρ`) are in
`ToMathlib/Analysis/InnerProductSpace/PostMeasurement.lean`, beside `postOp`/`postState`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {κ μ : Type*} [Fintype κ] [Fintype μ] {S : QSystem}

/-- **Cascaded measurements: probabilities chain (N&C Exercise 2.57).** The Born probability of
the single cascade measurement `L.cascade M` for the joint outcome `(l, m)` equals the probability
`p(l)` of outcome `l` under `L` times the probability `p(m ∣ l)` of outcome `m` under `M` computed
in the post-measurement state `L.postMeasurement ρ l` — the chained probability
`p(l, m) = p(l) · p(m ∣ l)` of measuring `L` and then `M`. -/
theorem cascade_bornProb (L : Measurement κ S) (M : Measurement μ S) (ρ : State S)
    (l : κ) (m : μ) (hl : L.bornProb ρ l ≠ 0) :
    (L.cascade M).bornProb ρ (l, m)
      = L.bornProb ρ l * M.bornProb (L.postMeasurement ρ l hl) m := by
  have hp : RCLike.re (LinearMap.trace ℂ S
      (ContinuousLinearMap.postOp L.op ρ.op l : S →ₗ[ℂ] S)) ≠ 0 := by
    rw [← Measurement.bornProb_eq_re_trace_postOp]; exact hl
  -- `p(m ∣ l)`, unfolded: measuring `M` on `Eₗ(ρ)/p(l)` gives `Tr(Mₘ Lₗ ρ Lₗ† Mₘ†) / p(l)`.
  have key : M.bornProb (L.postMeasurement ρ l hl) m
      = (RCLike.re (LinearMap.trace ℂ S (ContinuousLinearMap.postOp L.op ρ.op l : S →ₗ[ℂ] S)))⁻¹
        * RCLike.re (LinearMap.trace ℂ S
            (ContinuousLinearMap.postOp M.op (ContinuousLinearMap.postOp L.op ρ.op l) m
              : S →ₗ[ℂ] S)) := by
    rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.postMeasurement_op,
      ContinuousLinearMap.postState, ContinuousLinearMap.postOp_smul,
          ContinuousLinearMap.toLinearMap_smul,
      map_smul, smul_eq_mul]
    simp
  rw [Measurement.bornProb_eq_re_trace_postOp (L.cascade M), Measurement.postOp_cascade,
    Measurement.bornProb_eq_re_trace_postOp L, key, mul_inv_cancel_left₀ hp]

/-- **Cascaded measurements: states chain (N&C Exercise 2.57).** The post-measurement `State` of
the single cascade measurement `L.cascade M` for the joint outcome `(l, m)` equals the state
obtained by collapsing first under `L` (outcome `l`) and then under `M` (outcome `m`):
`N₍ₗ,ₘ₎ ρ N₍ₗ,ₘ₎† / p(l, m) = Mₘ (Lₗ ρ Lₗ† / p(l)) Mₘ† / p(m ∣ l)`. Together with `cascade_bornProb`
this is the physical equivalence of the cascade and the sequential procedure. -/
theorem cascade_postMeasurement (L : Measurement κ S) (M : Measurement μ S) (ρ : State S)
    (l : κ) (m : μ) (hl : L.bornProb ρ l ≠ 0)
    (hm : M.bornProb (L.postMeasurement ρ l hl) m ≠ 0) :
    (L.cascade M).postMeasurement ρ (l, m)
        (by rw [cascade_bornProb L M ρ l m hl]; exact mul_ne_zero hl hm)
      = M.postMeasurement (L.postMeasurement ρ l hl) m hm := by
  have hp : RCLike.re (LinearMap.trace ℂ S
      (ContinuousLinearMap.postOp L.op ρ.op l : S →ₗ[ℂ] S)) ≠ 0 := by
    rw [← Measurement.bornProb_eq_re_trace_postOp]; exact hl
  apply State.ext
  simp only [Measurement.postMeasurement_op]
  -- The sequential M-collapse is fed `Eₗ(ρ)/p(l)`, a nonzero rescaling of `Eₗ(ρ)`; the collapse is
  -- invariant under that rescaling (`postState_smul`), so it reduces to collapsing on `Eₗ(ρ)`,
  -- and the cascade collapse on `ρ` unfolds through `postOp_cascade` to exactly the same operator.
  have hLunfold : ContinuousLinearMap.postState L.op ρ.op l
      = ((RCLike.re (LinearMap.trace ℂ S
            (ContinuousLinearMap.postOp L.op ρ.op l : S →ₗ[ℂ] S)))⁻¹ : ℂ)
          • ContinuousLinearMap.postOp L.op ρ.op l := rfl
  rw [hLunfold, ← Complex.ofReal_inv,
    ContinuousLinearMap.postState_smul M.op (ContinuousLinearMap.postOp L.op ρ.op l) m
      (inv_ne_zero hp),
    ContinuousLinearMap.postState, ContinuousLinearMap.postState, Measurement.postOp_cascade]

end AxQM
