/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Composite

/-!
# AxQM.Postulates.API — the density operator of a product pure state

A single derived bridge relating the two ways of forming composite states from pure
components. The pure-state tensor `PureState.tmul` (`ψ ⊗ φ`, N&C §2.2.8) and the
density-state tensor `State.tmul` (`ρ ⊗ σ`) are linked through the vector→operator bridge
`PureState.toState` (`|·⟩⟨·|`):

* `PureState.toState_tmul` — `|ψ ⊗ φ⟩⟨ψ ⊗ φ| = |ψ⟩⟨ψ| ⊗ |φ⟩⟨φ|`, i.e. forming the density
  operator of a product pure state commutes with the tensor product.

The proof unfolds `State.op` and `PureState.vec` to the rank-one projector
`InnerProductSpace.rankOne`. The identity is used for composite-state reasoning (marginals of
product states, purity of reduced states, …).

The key step is the general fact
`InnerProductSpace.rankOne_tmul_self` (`|u ⊗ v⟩⟨u ⊗ v| = mapL |u⟩⟨u| |v⟩⟨v|`), which is in
`ToMathlib/Analysis/InnerProductSpace/TensorProduct.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **The density operator of a product pure state is the product of the factor density
operators**: `|ψ ⊗ φ⟩⟨ψ ⊗ φ| = |ψ⟩⟨ψ| ⊗ |φ⟩⟨φ|`. The `toState` bridge commutes with the
tensor product, connecting the pure-state tensor `PureState.tmul` with the density-state
tensor `State.tmul`. The key step is `InnerProductSpace.rankOne_tmul_self`. -/
theorem PureState.toState_tmul (ψ : PureState S) (φ : PureState T) :
    (ψ ⊗ φ).toState = ψ.toState ⊗ φ.toState := by
  apply State.ext
  rw [PureState.toState_op, State.tmul_op, PureState.toState_op, PureState.toState_op,
    PureState.tmul_vec]
  exact InnerProductSpace.rankOne_tmul_self ψ.vec φ.vec

end AxQM
