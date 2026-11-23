/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.StateSpace
import ToMathlib.Analysis.InnerProductSpace.Adjoint
import ToMathlib.Analysis.InnerProductSpace.PostMeasurement
import ToMathlib.Analysis.InnerProductSpace.POVM

/-!
# AxQM — Postulates 3 & 4: measurement, the Born rule, and collapse

A **measurement** on a system `S` is a finite family of
*measurement operators* `Mᵢ` with the completeness relation `∑ᵢ Mᵢ† Mᵢ = 1`
(Nielsen–Chuang Postulate 3 / §2.2.3). This is the faithful general measurement — it
carries enough information for **both** the outcome probabilities (P3) and the state
update (P4), unlike a bare POVM (which records only the effects `Eᵢ = Mᵢ† Mᵢ`).

* `toPOVM` — the induced POVM (effects `Mᵢ† Mᵢ`), used for the Born rule.
* `bornProb` (P3) — outcome probability `Tr(Mᵢ ρ Mᵢ†)`; `bornProb_nonneg`,
  `sum_bornProb_eq_one`.
* `postMeasurement` (P4) — the normalized post-measurement `State`
  `Mᵢ ρ Mᵢ† / p(i)`, a genuine state when the outcome is possible.

The measurement operators are `Measurement.op`. (`QSystem` bundles finite-dimensionality
and hence completeness, so no per-section instance bookkeeping is needed.)
-/

open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **Postulate 3 (measurement).** A **measurement** on the system `S` with outcome
set `ι` is a family of measurement operators `Mᵢ` satisfying the completeness
relation `∑ᵢ Mᵢ† Mᵢ = 1`. -/
structure Measurement (ι : Type*) [Fintype ι] (S : QSystem) where
  /-- The measurement operators. -/
  op : ι → (S →L[ℂ] S)
  /-- Completeness: `∑ᵢ Mᵢ† Mᵢ = 1`. -/
  complete : ∑ i, (adjoint (op i)).comp (op i) = 1

variable {ι : Type*} [Fintype ι] {S : QSystem}

namespace Measurement

/-- The **induced POVM**: outcome `i` has effect `Eᵢ = Mᵢ† Mᵢ`. Used
for the Born rule; positivity from `isPositive_adjoint_comp_self`, completeness
from the measurement's `complete` field. -/
def toPOVM (m : Measurement ι S) : POVM ι ℂ S where
  elements i := (adjoint (m.op i)).comp (m.op i)
  isPositive i := ContinuousLinearMap.isPositive_adjoint_comp_self (m.op i)
  sum_eq_one := m.complete

@[simp]
theorem toPOVM_elements (m : Measurement ι S) (i : ι) :
    m.toPOVM.elements i = (adjoint (m.op i)).comp (m.op i) := rfl

/-- The **projective measurement in an orthonormal basis** `b`: outcome `i` has measurement
operator the rank-one projector `Mᵢ = |bᵢ⟩⟨bᵢ|`. Completeness `∑ᵢ Mᵢ† Mᵢ = 1` is the
resolution of the identity (`OrthonormalBasis.sum_rankOne_eq_id`) composed with the
idempotence of each self-adjoint projector. The `Measurement` counterpart of
`POVM.ofOrthonormalBasis` (its induced POVM is `toPOVM_ofOrthonormalBasis`). -/
def ofOrthonormalBasis (b : OrthonormalBasis ι ℂ S) : Measurement ι S where
  op i := rankOne ℂ (b i) (b i)
  complete := by
    rw [ContinuousLinearMap.one_def, ← b.sum_rankOne_eq_id]
    exact Finset.sum_congr rfl fun i _ ↦ adjoint_rankOne_comp_self (b.orthonormal.1 i)

@[simp]
theorem ofOrthonormalBasis_op (b : OrthonormalBasis ι ℂ S) (i : ι) :
    (ofOrthonormalBasis b).op i = rankOne ℂ (b i) (b i) := rfl

/-- The POVM induced by the projective measurement `ofOrthonormalBasis b` is the rank-one
POVM `POVM.ofOrthonormalBasis b`: the measurement is *projective*, so each effect
`Eᵢ = Mᵢ† Mᵢ = Mᵢ = |bᵢ⟩⟨bᵢ|`. -/
theorem toPOVM_ofOrthonormalBasis (b : OrthonormalBasis ι ℂ S) :
    (ofOrthonormalBasis b).toPOVM = POVM.ofOrthonormalBasis b := by
  refine POVM.ext (funext fun i ↦ ?_)
  rw [toPOVM_elements, ofOrthonormalBasis_op, POVM.ofOrthonormalBasis_elements]
  exact adjoint_rankOne_comp_self (b.orthonormal.1 i)

/-- **Born rule (P3).** The probability of outcome `i` when measuring `m` on state
`ρ`: `Tr(Mᵢ ρ Mᵢ†) = Tr(Eᵢ ρ)`. -/
def bornProb (m : Measurement ι S) (ρ : State S) (i : ι) : ℝ := m.toPOVM.toPMF ρ.op i

/-- Born probabilities are non-negative. -/
theorem bornProb_nonneg (m : Measurement ι S) (ρ : State S) (i : ι) :
    0 ≤ m.bornProb ρ i :=
  m.toPOVM.toPMF_nonneg ρ.isPositive_op i

/-- **Born rule normalization.** The outcome probabilities sum to one. -/
theorem sum_bornProb_eq_one (m : Measurement ι S) (ρ : State S) :
    ∑ i, m.bornProb ρ i = 1 :=
  m.toPOVM.sum_toPMF_eq_one ρ.isDensity

/-- Each outcome probability is at most one — it is bounded by the total mass `1`. -/
theorem bornProb_le_one (m : Measurement ι S) (ρ : State S) (i : ι) :
    m.bornProb ρ i ≤ 1 :=
  m.sum_bornProb_eq_one ρ ▸
    Finset.single_le_sum (fun j _ ↦ m.bornProb_nonneg ρ j) (Finset.mem_univ i)

/-- The Born probability in post-measurement-operation form: `p(i) = re Tr(Mᵢ ρ Mᵢ†)`.
Bridges the POVM-effect form (`bornProb`) to the state-update normalization
(`ContinuousLinearMap.postOp`) via trace-cyclicity. -/
theorem bornProb_eq_re_trace_postOp (m : Measurement ι S) (ρ : State S) (i : ι) :
    m.bornProb ρ i =
      RCLike.re (LinearMap.trace ℂ S (ContinuousLinearMap.postOp m.op ρ.op i : S →ₗ[ℂ] S)) := by
  rw [bornProb, POVM.toPMF_eq, ContinuousLinearMap.trace_postOp]
  rfl

/-- **Postulate 4 (state update / collapse).** The normalized post-measurement
state for outcome `i`, when that outcome is possible (`bornProb ≠ 0`):
`ρ ↦ Mᵢ ρ Mᵢ† / p(i)`. A genuine `State`, since the normalized conjugation is again
a density operator. -/
def postMeasurement (m : Measurement ι S) (ρ : State S) (i : ι)
    (hp : m.bornProb ρ i ≠ 0) : State S where
  op := ContinuousLinearMap.postState m.op ρ.op i
  isDensity :=
    ContinuousLinearMap.postState_isDensityOp m.op ρ.isDensity i
      (by rw [← bornProb_eq_re_trace_postOp]; exact hp)

@[simp]
theorem postMeasurement_op (m : Measurement ι S) (ρ : State S) (i : ι)
    (hp : m.bornProb ρ i ≠ 0) :
    (m.postMeasurement ρ i hp).op = ContinuousLinearMap.postState m.op ρ.op i := rfl

end Measurement

end AxQM
