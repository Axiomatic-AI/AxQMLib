/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Mixture

/-!
# AxQM.Postulates.API — mixing versus tensoring (the linearity cloning obstruction)

Two facts about how the binary mixture `State.mixPair` interacts with the
tensor product `State.tmul`, used by Nielsen & Chuang **Problem 12.4** (linearity forbids
cloning):

* `State.mixPair_tmul` — tensoring a fixed state onto a binary mixture distributes,
  `(p ρ₁ + (1 − p) ρ₂) ⊗ σ = p (ρ₁ ⊗ σ) + (1 − p) (ρ₂ ⊗ σ)`. The two-outcome companion of
  `State.mix_tmul`.
* `State.mixPair_tmul_self_ne_tmul_mixPair` — for a **nontrivial** mixture (`0 < p < 1`) of two
  **distinct** states `ρ₁ ≠ ρ₂`, the mixture of the self-tensors differs from the self-tensor of the
  mixture:
  ```
  p (ρ₁ ⊗ ρ₁) + (1 − p) (ρ₂ ⊗ ρ₂)  ≠  (p ρ₁ + (1 − p) ρ₂) ⊗ (p ρ₁ + (1 − p) ρ₂).
  ```
  This is the algebraic heart of the linearity no-cloning argument: at the operator level the two
  sides differ by exactly `p (1 − p) · (ρ₁.op − ρ₂.op) ⊗ (ρ₁.op − ρ₂.op)`, which is nonzero because
  `ρ₁ ≠ ρ₂` makes `ρ₁.op − ρ₂.op ≠ 0` and the tensor square of a nonzero operator is nonzero
  (`TensorProduct.mapL_self_ne_zero`).

Both are proved through the density operator `.op` and `TensorProduct.mapL`, as is their
sibling `State.mix_tmul`. They are used in `AxQM/NC/Ch12/Problem12_4.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Tensoring a fixed state onto a binary mixture distributes**:
`(p ρ₁ + (1 − p) ρ₂) ⊗ σ = p (ρ₁ ⊗ σ) + (1 − p) (ρ₂ ⊗ σ)`. The two-outcome companion of
`State.mix_tmul`: `TensorProduct.mapL` is linear in its left argument (`mapL_add_left`,
`mapL_smul_left`), so it commutes with the binary convex combination defining `State.mixPair`. -/
theorem State.mixPair_tmul {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ₁ ρ₂ : State S) (σ : State T) :
    (State.mixPair hp0 hp1 ρ₁ ρ₂).tmul σ
      = State.mixPair hp0 hp1 (ρ₁.tmul σ) (ρ₂.tmul σ) := by
  apply State.ext
  rw [State.tmul_op, State.mixPair_op, State.mixPair_op, State.tmul_op, State.tmul_op,
    TensorProduct.mapL_add_left, TensorProduct.mapL_smul_left, TensorProduct.mapL_smul_left]
  rfl

/-- The **convex-combination "variance gap"** of the tensor-square map `X ↦ mapL X X`: for a scalar
`c`, the weighted average of the self-tensors minus the self-tensor of the weighted average equals
`c (1 − c)` times the self-tensor of the difference,
```
c • mapL A A + (1 − c) • mapL B B − mapL (cA + (1−c)B) (cA + (1−c)B)
  = c (1 − c) • mapL (A − B) (A − B).
```
Stated with an abstract scalar field `𝕜` so the `module` tactic can normalise the linear combination
(it does not fire on the concrete `ℂ` coercion forms). File-local scaffolding for the cloning
obstruction below. -/
private theorem mapL_convexCombo_sub {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (c : 𝕜) (A B : E →L[𝕜] E) :
    c • TensorProduct.mapL A A + (1 - c) • TensorProduct.mapL B B
      - TensorProduct.mapL (c • A + (1 - c) • B) (c • A + (1 - c) • B)
      = (c * (1 - c)) • TensorProduct.mapL (A - B) (A - B) := by
  simp only [TensorProduct.mapL_add_left, TensorProduct.mapL_add_right,
    TensorProduct.mapL_smul_left, TensorProduct.mapL_smul_right,
    TensorProduct.mapL_sub_left, TensorProduct.mapL_sub_right]
  module

/-- **The mixture of self-tensors is not the self-tensor of the mixture**, for a nontrivial mixture
of distinct states. If `0 < p < 1` and `ρ₁ ≠ ρ₂` then
```
p (ρ₁ ⊗ ρ₁) + (1 − p) (ρ₂ ⊗ ρ₂)  ≠  (p ρ₁ + (1 − p) ρ₂) ⊗ (p ρ₁ + (1 − p) ρ₂).
```
The algebraic core of Nielsen & Chuang Problem 12.4. At the operator level the two sides differ by
`p (1 − p) • (ρ₁.op − ρ₂.op) ⊗ (ρ₁.op − ρ₂.op)` (`mapL_convexCombo_sub`); the scalar `p (1 − p)` is
nonzero for `0 < p < 1`, and the operator `ρ₁.op − ρ₂.op` is nonzero because `ρ₁ ≠ ρ₂`
(`State.ext`), so its tensor square is nonzero (`TensorProduct.mapL_self_ne_zero`). -/
theorem State.mixPair_tmul_self_ne_tmul_mixPair {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {ρ₁ ρ₂ : State S} (hne : ρ₁ ≠ ρ₂) :
    State.mixPair hp0.le hp1.le (ρ₁.tmul ρ₁) (ρ₂.tmul ρ₂)
      ≠ (State.mixPair hp0.le hp1.le ρ₁ ρ₂).tmul (State.mixPair hp0.le hp1.le ρ₁ ρ₂) := by
  intro heq
  have hAB : ρ₁.op - ρ₂.op ≠ 0 := sub_ne_zero.mpr fun h => hne (State.ext h)
  have hkey : TensorProduct.mapL (ρ₁.op - ρ₂.op) (ρ₁.op - ρ₂.op) ≠ 0 :=
    TensorProduct.mapL_self_ne_zero hAB
  -- push the equality of states down to their density operators
  have hop : (p : ℂ) • TensorProduct.mapL ρ₁.op ρ₁.op
        + ((1 - p : ℝ) : ℂ) • TensorProduct.mapL ρ₂.op ρ₂.op
      = TensorProduct.mapL ((p : ℂ) • ρ₁.op + ((1 - p : ℝ) : ℂ) • ρ₂.op)
          ((p : ℂ) • ρ₁.op + ((1 - p : ℝ) : ℂ) • ρ₂.op) := by
    have h := congrArg State.op heq
    rwa [State.mixPair_op, State.tmul_op, State.tmul_op, State.tmul_op, State.mixPair_op] at h
  push_cast at hop
  -- the variance-gap identity forces the scaled tensor square to vanish
  have hid := mapL_convexCombo_sub (p : ℂ) ρ₁.op ρ₂.op
  rw [hop, sub_self] at hid
  have hc : (p : ℂ) * (1 - (p : ℂ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ne_of_gt hp0)
      (by rw [sub_ne_zero]; exact_mod_cast (ne_of_lt hp1).symm)
  exact smul_ne_zero hc hkey hid.symm

end AxQM
