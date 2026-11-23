/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite

/-!
# AxQM.Postulates.API — functoriality of the tensor product of gates

The tensor product `⊗` of `Evolution`s respects composition and
identities — it is a monoidal functor. These are the gate-level lifts of `TensorProduct.mapL_comp`
and `TensorProduct.mapL_one`, complementing the single-factor homomorphisms `Evolution.onLeft_comp`
and `Evolution.onRight_comp`. Their
proofs open a gate to its underlying operator (`Evolution.tmul_op`, `Evolution.comp_op`) and
apply the `TensorProduct.mapL` algebra.

## What is formalised

* `Evolution.tmul_comp` — `(a ⊗ c) · (b ⊗ d) = (a·b) ⊗ (c·d)`: composing two product gates composes
  their factors.
* `Evolution.id_tmul_id` — `1 ⊗ 1 = 1`: the tensor of the identity gates is the identity gate.
* `Evolution.onLeft_comp_onRight` — `(U ⊗ 1) · (1 ⊗ V) = U ⊗ V`: a local unitary on both factors
  factors as an Alice-only gate after a Bob-only gate (and hence, via `Evolution.evolve_comp`, so
  does the corresponding evolution), the reusable "peel a local `U ⊗ V`" step of the Proposition
  12.14 reduction.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The tensor product of gates is functorial for composition:** `(a ⊗ c) · (b ⊗ d) =
(a·b) ⊗ (c·d)`. The operator-level content is `TensorProduct.mapL_comp`. -/
theorem Evolution.tmul_comp (a b : Evolution S) (c d : Evolution T) :
    (a ⊗ c).comp (b ⊗ d) = (a.comp b) ⊗ (c.comp d) := by
  ext1
  simp only [Evolution.comp_op, Evolution.tmul_op]
  exact (TensorProduct.mapL_comp a.op b.op c.op d.op).symm

/-- **The tensor of two identity gates is the identity:** `1 ⊗ 1 = 1`. The operator-level content is
`TensorProduct.mapL_one`. -/
theorem Evolution.id_tmul_id :
    ((Evolution.id : Evolution S) ⊗ (Evolution.id : Evolution T)) = Evolution.id := by
  ext1
  simp only [Evolution.tmul_op, Evolution.id_op]
  exact TensorProduct.mapL_one

/-- **A local unitary on both factors is an Alice gate after a Bob gate:** `(U ⊗ 1) · (1 ⊗ V) =
U ⊗ V`, i.e. `(U.onLeft T).comp (V.onRight S) = U ⊗ V`. The disjoint-factor gates `U ⊗ 1` and
`1 ⊗ V` compose to the product gate `U ⊗ V` (a special case of `Evolution.tmul_comp` with the
trivial factor being the identity). Combined with `Evolution.evolve_comp` this peels a local unitary
`U ⊗ V` into an Alice round `U ⊗ 1` and a Bob round `1 ⊗ V` — the reusable step behind the
Proposition 12.14 LOCC reduction (`OneWayLOCC.prepend_bobMeasure_of_swapSymmetric`). -/
theorem Evolution.onLeft_comp_onRight (U : Evolution S) (V : Evolution T) :
    (U.onLeft T).comp (V.onRight S) = U ⊗ V := by
  rw [Evolution.onLeft, Evolution.onRight, Evolution.tmul_comp, Evolution.comp_id,
    Evolution.id_comp]

end AxQM
