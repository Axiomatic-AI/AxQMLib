/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Observable
import AxQM.Postulates.API.Qubit

/-!
# AxQM.Postulates.API — the Bell state Φ⁺

The maximally entangled two-qubit **Bell state** `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, a `PureState` of the
composite system `qubit ⊗ qubit`. This is the canonical entangled state of Nielsen & Chuang §1.3.6 /
§2.3, used throughout Chapter 2 (superdense coding, the EPR/Bell exercises).

* `bellVec` — the *unnormalised* vector `|00⟩ + |11⟩` in the tensor-product space
  `qubit.space ⊗[ℂ] qubit.space`.
* `bellVec_inner_self` — `⟨β|β⟩ = 2`; the squared norm, from which normalisation follows.
* `bellPhiPlus` — the normalised Bell state `(√2)⁻¹ • (|00⟩ + |11⟩)`, a `PureState (qubit ⊗ qubit)`.

## Design notes

`bellVec` is entangled — it is **not** a `PureState.tmul` of single-qubit states — so it is built
directly from the tensor of computational-basis vectors and normalised by hand.

The underlying space `(qubit ⊗ qubit).space` is *definitionally* the raw tensor product
`TensorProduct ℂ qubit.space qubit.space`, but the two present different heads, and the two families
of lemmas want different heads:

* the **inner-product expansion** lemmas (`TensorProduct.inner_tmul`, `inner_add_left/right`) fire
  on the raw tensor head, so `bellVec_inner_self` restates the goal over it with
  `change (@inner ℂ (TensorProduct ℂ qubit.space qubit.space) _ …)` before rewriting;
* the **scalar-factoring** lemmas (`norm_smul`, `inner_smul_left/right`, `map_smul`) fire on the
  composite `(qubit ⊗ qubit).space` head, whose `Inner`/`Module`/`Norm` instances are the
  `…toInner`/`…toModule` forms those lemmas expect.

The normalising scalar is written `(Real.sqrt 2 : ℂ)⁻¹` — an explicit `ℂ` scalar — so the smul is a
genuine `ℂ`-action and the `ℂ`-linearity lemmas fire; the spelling `(↑(Real.sqrt 2))⁻¹` instead
elaborates to a *real* scalar acting through the `ℝ`-scalar tower, which those lemmas do not match.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- The **unnormalised Bell vector** `|00⟩ + |11⟩` in the two-qubit space
`qubit.space ⊗[ℂ] qubit.space`. Its norm is `√2` (`bellVec_inner_self`); the normalised state is
`bellPhiPlus`. -/
def bellVec : (qubit ⊗ qubit).space :=
  (qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis 0).vec + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis 1).vec

/-- **The squared norm of the unnormalised Bell vector is `2`:** `⟨β|β⟩ = 2`. Because `|00⟩` and
`|11⟩` are orthonormal (`qubitBasis_inner_qubitBasis` and `TensorProduct.inner_tmul`), the cross
terms vanish and `⟨(|00⟩ + |11⟩)|(|00⟩ + |11⟩)⟩ = ⟨00|00⟩ + ⟨11|11⟩ = 1 + 1 = 2`. -/
theorem bellVec_inner_self : (inner ℂ bellVec bellVec : ℂ) = 2 := by
  change (@inner ℂ (TensorProduct ℂ qubit.space qubit.space) _ bellVec bellVec : ℂ) = 2
  rw [bellVec, inner_add_left, inner_add_right, inner_add_right,
    TensorProduct.inner_tmul, TensorProduct.inner_tmul,
    TensorProduct.inner_tmul, TensorProduct.inner_tmul]
  simp only [qubitBasis_inner_qubitBasis]
  norm_num

/-- The **Bell state** `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, the maximally entangled pure state of the
composite system `qubit ⊗ qubit`. The underlying unit vector is `(√2)⁻¹ • bellVec`; it is
normalised because `‖bellVec‖ = √2` (from `bellVec_inner_self`). -/
def bellPhiPlus : PureState (qubit ⊗ qubit) where
  vec := (Real.sqrt 2 : ℂ)⁻¹ • bellVec
  normalized := by
    have hb : ‖bellVec‖ = Real.sqrt 2 := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), bellVec_inner_self]; norm_num
    rw [norm_smul, hb, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_mul_cancel₀ (by positivity)]

/-- The underlying unit vector of the Bell state `|Φ⁺⟩` is `(√2)⁻¹ • (|00⟩ + |11⟩)`. A `simp` lemma
exposing the vector for expectation computations. -/
@[simp]
theorem bellPhiPlus_vec : bellPhiPlus.vec = (Real.sqrt 2 : ℂ)⁻¹ • bellVec := rfl

end AxQM
