/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeutschGateReachable
import AxQM.Postulates.API.AxisAngleGateValues
import AxQM.Postulates.API.Swap
import AxQM.Postulates.API.CnotPauliPropagation

/-!
# AxQM.Postulates.API — the phase gate `S` from the once-controlled Deutsch gate

The *universality* half of Nielsen & Chuang, Exercise 4.44 — the
**second rotation axis**. The three-qubit Deutsch gate `G = C²(iR_x(πα))` supplies, on its target,
a dense family of `x`-rotations (`ccontrolledUnitary_rotXGate_op_mem_closure_deutschReachableOps`,
`DeutschGateReachable.lean`). One abelian axis is not enough for single-qubit universality; the
second axis is the **phase gate** `S = diag(1, i)`, and this file shows `S` is reachable from `G`.

## The mechanism

Fixing *one* of the two controls of `G` at `|1⟩` leaves the **once-controlled** Deutsch gate
`C(iR_x(πα))` on the remaining control–target pair. Iterating it runs the orbit
`C((iR_x(πα))^k) = C(iᵏ · R_x(kπα))`, and — exactly as for the doubly-controlled case — the target
content is dense. The new phenomenon is the accumulated **phase** `iᵏ`: at `iᵏ = i` and `R_x = I`
the target operation is the scalar `i · I`, and

> a controlled scalar `i · I` is the phase gate `S` on the control: `C(i · I) = S ⊗ I`

because `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ (i · I) = (|0⟩⟨0| + i·|1⟩⟨1|) ⊗ I = S ⊗ I`. So the reachability of
`i · I` (the concrete density fact `Concrete.iScalar_mem_closure_cyclic_iRx`) lifts to the
reachability of `S ⊗ I`: iterating the once-controlled `G` approximates `S ⊗ I` to arbitrary
accuracy. Since `S` conjugates the `x`-axis to the (perpendicular) `y`-axis
(`Concrete.sMatrix_mul_rotX_mul_conjTranspose`), the dense `x`-rotations together with `S` give a
second dense axis — hence, by the Euler decomposition, every single-qubit unitary up to a global
phase (`Concrete.exists_phase_smul_mem_closure_of_forall_rotX_sMatrix`).

## What is formalised

* `sGate_op_eq_rankOne_add` — the **spectral form** of `S` at the operator level:
  `S = |0⟩⟨0| + i · |1⟩⟨1|` (the image of `Concrete.sMatrix_eq_outerSelf_add` under
  `Matrix.toEuclideanCLM`, via `toEuclideanCLM_outerSelf_ket`).
* `sGate_onLeft_op_eq_controlledOp` — the **`S ⊗ I` identity**: `(S ⊗ I).op` (the phase gate on the
  control, identity on the target) equals `controlledOp (i · I)`, the once-controlled `i · I`. This
  is what makes "reach `i · I`" mean "reach `S`".
* `controlledUnitary_iRxGate_pow_op` / `_mem` and `deutschControlledReachableOps` — the
  **once-controlled reachable operator set** `{C(iⁿ · R_x(nπα)) : n ∈ ℤ}` and the fact that its
  non-negative members are the forward gate powers `(C(iR_x(πα))^k).op` (mirroring the
  doubly-controlled `deutschReachableOps`). The gate is written in the unfolded form
  `controlledUnitary (iRxGate (πα))`, definitionally the once-controlled Deutsch gate.
* `sGate_onLeft_op_mem_closure_deutschControlledReachableOps` — **the S-extraction**
  (`α` irrational): `S ⊗ I` lies in the closure of the once-controlled Deutsch gate's iterates. The
  physics incarnation of `Concrete.iScalar_mem_closure_cyclic_iRx`, transported by continuity of the
  controlled embedding, exactly as the density lift transports the concrete `x`-rotation density.

## Design notes

* **Hypothesis.** It is exactly `Irrational α`. `S ⊗ I` is a genuine *closure* limit (no
  exact iterate equals it: an exact iterate `iⁿ R_x(nπα)` would need `iⁿ = i` and
  `nπα ≡ 0 (mod 2π)`, forcing `n = 0` by irrationality — contradicting `iⁿ = i`).
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

noncomputable section

namespace AxQM

/-! ### The phase gate `S` as a controlled global phase -/

/-- **Spectral form of the phase gate `S` at the operator level:** `S = |0⟩⟨0| + i · |1⟩⟨1|`. The
qubit-space image of the concrete matrix identity `Concrete.sMatrix_eq_outerSelf_add` under the
`⋆`-algebra map `Matrix.toEuclideanCLM` (which respects addition and scalar multiplication), via
`toEuclideanCLM_outerSelf_ket` (`|i⟩⟨i|` as a matrix maps to the rank-one projector `|i⟩⟨i|`). -/
theorem sGate_op_eq_rankOne_add :
    sGate.op = InnerProductSpace.rankOne ℂ (qubitBasis 0).vec (qubitBasis 0).vec
        + Complex.I • InnerProductSpace.rankOne ℂ (qubitBasis 1).vec (qubitBasis 1).vec := by
  rw [sGate_op, Concrete.sMatrix_eq_outerSelf_add, map_add, map_smul,
    toEuclideanCLM_outerSelf_ket, toEuclideanCLM_outerSelf_ket]
  rfl

/-- **The phase gate `S` on the control is the controlled global phase `i · I`:**
`(S ⊗ I).op = controlledOp (i · I)`. Both are the block operator
`|0⟩⟨0| ⊗ I + i · (|1⟩⟨1| ⊗ I)`: `S ⊗ I` from the spectral form `S = |0⟩⟨0| + i·|1⟩⟨1|`
(`sGate_op_eq_rankOne_add`), and `controlledOp (i · I)` because `toEuclideanCLM (i • 1) = i · I`.
This is the identity that turns the reachability of `i · I` into the reachability of `S`. -/
theorem sGate_onLeft_op_eq_controlledOp :
    (sGate.onLeft qubit).op = controlledOp (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = Complex.I • (1 : qubit.space →L[ℂ] qubit.space) := by
    rw [map_smul, map_one]; rfl
  rw [Evolution.onLeft_op]
  unfold controlledOp
  rw [h1, sGate_op_eq_rankOne_add,
    TensorProduct.mapL_add_left, TensorProduct.mapL_smul_left, TensorProduct.mapL_smul_right]

/-! ### The once-controlled reachable operator set of the Deutsch gate, and the phase gate -/

/-- **The reachable operator set of the once-controlled Deutsch gate.** The operators of the integer
iterates of the once-controlled Deutsch gate `C(iR_x(πα))` on its target, in the closed form of the
cyclic subgroup `⟨iR_x(πα)⟩ = {iⁿ · R_x(nπα) : n ∈ ℤ}` controlled onto the control–target pair. The
non-negative iterates are the forward gate powers (`controlledUnitary_iRxGate_pow_op_mem`). The
single-controlled counterpart of `deutschReachableOps`. -/
def deutschControlledReachableOps (α : ℝ) :
    Set ((qubit ⊗ qubit).space →L[ℂ] (qubit ⊗ qubit).space) :=
  Set.range fun n : ℤ => controlledOp (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
      (Complex.I ^ n • Concrete.rotX (n • (Real.pi * α))))

/-- **The `k`-th power of the once-controlled Deutsch gate is the controlled `iᵏ · R_x(kπα)`.**
Combines `controlledUnitary_pow`, `Evolution.op_pow`, and `Concrete.iRxMat_pow`
(`(iR_x(θ))ᵏ = iᵏ · R_x(kθ)`) through `Matrix.toEuclideanCLM`. -/
theorem controlledUnitary_iRxGate_pow_op (α : ℝ) (k : ℕ) :
    ((controlledUnitary (iRxGate (Real.pi * α))) ^ k).op
      = controlledOp (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
          (Complex.I ^ k • Concrete.rotX (↑k * (Real.pi * α)))) := by
  rw [← controlledUnitary_pow, controlledUnitary_op_eq, Evolution.op_pow, iRxGate_op]
  congr 1
  rw [← Concrete.iRxMat_pow]
  exact (map_pow (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2))
    (Concrete.iRxMat (Real.pi * α)) k).symm

/-- **The forward once-controlled Deutsch-gate iterates are reachable:**
`(C(iR_x(πα))^k).op ∈ deutschControlledReachableOps α`. Grounds the reachable set in the actual
once-controlled gate. -/
theorem controlledUnitary_iRxGate_pow_op_mem (α : ℝ) (k : ℕ) :
    ((controlledUnitary (iRxGate (Real.pi * α))) ^ k).op ∈ deutschControlledReachableOps α := by
  refine ⟨(k : ℤ), ?_⟩
  rw [controlledUnitary_iRxGate_pow_op]
  simp only [zpow_natCast, zsmul_eq_mul, Int.cast_natCast]

/-- **The S-extraction (Nielsen & Chuang, Exercise 4.44).** When `α` is irrational, the phase gate
on the control, `S ⊗ I`, lies in the closure of the once-controlled Deutsch gate's iterates:
iterating `C(iR_x(πα))` approximates `S ⊗ I` to arbitrary accuracy.

The physics incarnation of the concrete fact `Concrete.iScalar_mem_closure_cyclic_iRx`
(`i · I ∈ closure ⟨iR_x(πα)⟩`): the controlled embedding `controlledOp ∘ Matrix.toEuclideanCLM` is
continuous, so it carries the matrix closure into the operator closure
(`image_closure_subset_closure_image`), sending the concrete orbit onto the reachable set and the
target `i · I` onto `(S ⊗ I).op` (`sGate_onLeft_op_eq_controlledOp`). This is the second rotation
axis of the Deutsch gate's single-qubit universality. -/
theorem sGate_onLeft_op_mem_closure_deutschControlledReachableOps {α : ℝ} (hα : Irrational α) :
    (sGate.onLeft qubit).op ∈ closure (deutschControlledReachableOps α) := by
  have hcont : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ =>
      controlledOp (S := qubit) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M) :=
    (continuous_controlledOp (S := qubit)).comp Matrix.continuous_toEuclideanCLM
  have hx := image_closure_subset_closure_image hcont
    (Set.mem_image_of_mem _ (Concrete.iScalar_mem_closure_cyclic_iRx hα))
  rw [← Set.range_comp] at hx
  rw [sGate_onLeft_op_eq_controlledOp]
  exact hx

end AxQM

end
