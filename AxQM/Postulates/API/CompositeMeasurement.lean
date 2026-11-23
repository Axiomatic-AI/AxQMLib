/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Measurement
import AxQM.Postulates.Composite

/-!
# AxQM — measuring one factor of a composite system

The **measurement on the right factor** `Measurement.onRight`: given a measurement `m`
on a system `T` (outcomes `ι`), the composite system `S ⊗ T` carries the measurement whose
operators act as `m` on `T` and trivially on `S`,

  `Nᵢ = 1_S ⊗ Mᵢ`   (Nielsen–Chuang §2.2.8; measuring a subsystem of a composite).

This is the `Measurement` counterpart of `Evolution.onRight` (`1 ⊗ V`): the reusable way to lift a
measurement of one component to the joint system, leaving the other component untouched.
Completeness `∑ᵢ Nᵢ† Nᵢ = 1` reduces to `m`'s completeness slot-by-slot: `∑ᵢ (1 ⊗ Mᵢ)† (1 ⊗ Mᵢ) =
1 ⊗ (∑ᵢ Mᵢ† Mᵢ) = 1 ⊗ 1 = 1`, via `TensorProduct.mapL_adjoint_comp_self` and
`TensorProduct.mapL_one_sum_right`.

The mirror construction `Measurement.onLeft` measures the *left* component instead
(`Nᵢ = Mᵢ ⊗ 1_T`), completeness reducing the same way through `TensorProduct.mapL_sum_left`. Either
lift is needed whenever an item measures a subsystem of a composite while keeping the other factor
(e.g. Problem 8.2, where Alice measures the first two of three systems).

These are used for any item that measures a subsystem of a composite (e.g. measuring the reference
of a purification, Exercise 2.82(2)/(3)).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {T : QSystem}

namespace Measurement

/-- **Measurement on the right factor** `Nᵢ = 1_S ⊗ Mᵢ` (Nielsen–Chuang §2.2.8): lift a measurement
`m` of the system `T` to the composite `S ⊗ T`, acting with `m` on `T` and identity on `S`.
Completeness `∑ᵢ Nᵢ† Nᵢ = 1` follows from `m.complete` slot-by-slot: each summand is
`(1 ⊗ Mᵢ)† (1 ⊗ Mᵢ) = 1 ⊗ (Mᵢ† Mᵢ)` (`TensorProduct.mapL_adjoint_comp_self`), and the sum pulls
into the right slot (`TensorProduct.mapL_one_sum_right`) as `1 ⊗ (∑ᵢ Mᵢ† Mᵢ) = 1 ⊗ 1 = 1`. -/
def onRight (m : Measurement ι T) (S : QSystem) : Measurement ι (S ⊗ T) where
  op i := TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i)
  complete := by
    have key : ∀ i, (adjoint (TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i))).comp
        (TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i))
        = TensorProduct.mapL (1 : S →L[ℂ] S) ((adjoint (m.op i)).comp (m.op i)) := by
      intro i
      rw [TensorProduct.mapL_adjoint_comp_self]
      congr 1
      rw [one_def, adjoint_id, id_comp]
    calc ∑ i, (adjoint (TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i))).comp
            (TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i))
        = ∑ i, TensorProduct.mapL (1 : S →L[ℂ] S) ((adjoint (m.op i)).comp (m.op i)) :=
          Finset.sum_congr rfl fun i _ => key i
      _ = TensorProduct.mapL (1 : S →L[ℂ] S) (∑ i, (adjoint (m.op i)).comp (m.op i)) :=
          (TensorProduct.mapL_one_sum_right _).symm
      _ = TensorProduct.mapL (1 : S →L[ℂ] S) 1 := by rw [m.complete]
      _ = 1 := TensorProduct.mapL_one

@[simp]
theorem onRight_op (m : Measurement ι T) (S : QSystem) (i : ι) :
    (m.onRight S).op i = TensorProduct.mapL (1 : S →L[ℂ] S) (m.op i) := rfl

/-- **Measurement on the left factor** `Nᵢ = Mᵢ ⊗ 1_T` (Nielsen–Chuang §2.2.8): lift a measurement
`m` of the system `S` to the composite `S ⊗ T`, acting with `m` on `S` and identity on `T` — the
mirror image of `onRight`, for measuring the *left* component of a composite. Completeness
`∑ᵢ Nᵢ† Nᵢ = 1` follows from `m.complete` slot-by-slot: each summand is
`(Mᵢ ⊗ 1)† (Mᵢ ⊗ 1) = (Mᵢ† Mᵢ) ⊗ 1` (`TensorProduct.mapL_adjoint_comp_self`), and the sum pulls
into the left slot (`TensorProduct.mapL_sum_left`) as `(∑ᵢ Mᵢ† Mᵢ) ⊗ 1 = 1 ⊗ 1 = 1`. -/
def onLeft {S : QSystem} (m : Measurement ι S) (T : QSystem) : Measurement ι (S ⊗ T) where
  op i := TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T)
  complete := by
    have key : ∀ i, (adjoint (TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T))).comp
        (TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T))
        = TensorProduct.mapL ((adjoint (m.op i)).comp (m.op i)) (1 : T →L[ℂ] T) := by
      intro i
      rw [TensorProduct.mapL_adjoint_comp_self]
      congr 1
      rw [one_def, adjoint_id, id_comp]
    calc ∑ i, (adjoint (TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T))).comp
            (TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T))
        = ∑ i, TensorProduct.mapL ((adjoint (m.op i)).comp (m.op i)) (1 : T →L[ℂ] T) :=
          Finset.sum_congr rfl fun i _ => key i
      _ = TensorProduct.mapL (∑ i, (adjoint (m.op i)).comp (m.op i)) (1 : T →L[ℂ] T) :=
          (TensorProduct.mapL_sum_left _ _).symm
      _ = TensorProduct.mapL (1 : S →L[ℂ] S) (1 : T →L[ℂ] T) := by rw [m.complete]
      _ = 1 := TensorProduct.mapL_one

@[simp]
theorem onLeft_op {S : QSystem} (m : Measurement ι S) (T : QSystem) (i : ι) :
    (m.onLeft T).op i = TensorProduct.mapL (m.op i) (1 : T →L[ℂ] T) := rfl

/-- The lifted measurement operator `m.onLeft T` acts on the left factor: for a pure tensor
`x ⊗ₜ y` on `S ⊗ T` its operator for outcome `i` is `(Mᵢ x) ⊗ₜ y` (identity on the right factor). -/
theorem onLeft_op_tmul {S : QSystem} (m : Measurement ι S) (T : QSystem) (i : ι) (x : S.space)
    (y : T.space) : (m.onLeft T).op i (x ⊗ₜ[ℂ] y) = (m.op i) x ⊗ₜ[ℂ] y := by
  rw [Measurement.onLeft_op]; erw [TensorProduct.mapL_apply, TensorProduct.map_tmul]
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, one_apply_eq_self]

/-- The lifted measurement operator `m.onRight T` acts on the right factor: for a pure tensor
`x ⊗ₜ y` on `T ⊗ S` its operator for outcome `i` is `x ⊗ₜ (Mᵢ y)` (identity on the left factor). -/
theorem onRight_op_tmul {S : QSystem} (m : Measurement ι S) (T : QSystem) (i : ι) (x : T.space)
    (y : S.space) : (m.onRight T).op i (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] (m.op i) y := by
  rw [Measurement.onRight_op]; erw [TensorProduct.mapL_apply, TensorProduct.map_tmul]
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, one_apply_eq_self]

end Measurement

end AxQM
