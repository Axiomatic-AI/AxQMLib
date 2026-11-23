/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Swap

/-!
# Linearity lemmas for the `SWAP` gate

Dedicated rewrite lemmas for the action of `Evolution.swap` on the additive/scalar structure of a
bipartite vector, plus the `SWAP`-naturality of a single-factor operator. These are proved here — in
a module that imports **only** `Swap` — because the generic `map_add` / `map_smul` / `map_zero`
lemmas fail to fire on the *concrete* `Evolution.swap.op` once heavier instance-carrying modules
(e.g. the `EuclideanSpace` machinery pulled in by the Schmidt / measurement API) are in scope
(an instance-diamond limitation of the discrimination tree). Proved once here as named lemmas, they
rewrite cleanly wherever imported, exactly like the hand-written `Evolution.swap_op_tmul`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- Linearity of `SWAP` on a scalar multiple: `SWAP (c • x) = c • SWAP x`. -/
theorem Evolution.swap_op_smul (c : ℂ) (x : (S ⊗ S).space) :
    (Evolution.swap (S := S)).op (c • x) = c • (Evolution.swap (S := S)).op x := map_smul _ _ _

/-- **Naturality of `SWAP` under a left-embedded operator.** On `S ⊗ S`, swapping the two factors
after applying `A` to the *left* factor equals applying `A` to the *right* factor after swapping:
`SWAP ((A ⊗ 1) v) = (1 ⊗ A) (SWAP v)`. This is the continuous-linear form of the naturality of the
factor swap; proved on elementary tensors (`SWAP(Aa ⊗ b) = b ⊗ Aa = (1 ⊗ A)(b ⊗ a)`) and extended
by linearity. -/
theorem Evolution.swap_op_mapL (A : S.space →L[ℂ] S.space) (v : S.space ⊗[ℂ] S.space) :
    (Evolution.swap (S := S)).op (TensorProduct.mapL A 1 v)
      = TensorProduct.mapL 1 A ((Evolution.swap (S := S)).op v) := by
  have key : (Evolution.swap (S := S)).op.comp (TensorProduct.mapL A 1)
      = (TensorProduct.mapL 1 A).comp (Evolution.swap (S := S)).op := by
    apply ContinuousLinearMap.coe_injective
    apply TensorProduct.ext'
    intro a b
    change (Evolution.swap (S := S)).op (TensorProduct.mapL A 1 (a ⊗ₜ[ℂ] b))
        = TensorProduct.mapL 1 A ((Evolution.swap (S := S)).op (a ⊗ₜ[ℂ] b))
    simp only [TensorProduct.mapL_tmul, one_apply_eq_self, Evolution.swap_op_tmul]
    rfl
  exact DFunLike.congr_fun key v

end AxQM
