/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerSingleWireGate

/-!
# Tensor multilinearity of the tower product state on one wire (N&C Problem 5.2 support)

The tower product state `towerProd n ψ = ψ 0 ⊗ ⋯ ⊗ ψ n` on `qtower n qubit`
(`Core/QtowerSingleWireGate`) is multilinear in its wires: a scalar multiple placed on one wire's
factor factors out of the whole product. This file records that fact as a reusable `.vec`-level
lemma, the wire-locality counterpart of the single-wire gate action `qtowerSingleWire_evolvePure_*`.

It is needed wherever a *diagonal* single-wire gate — a phase gate acting on a basis wire — is read
on a computational tower state: such a gate sends the wire to a scalar multiple of itself, and this
lemma pulls that scalar out of the whole product (e.g. the head-controlled phase cascade of the
measured-QFT reduction, `Core/QtowerHeadPhaseControl`).

## What is formalised

* `towerProd_vec_update_smul` — replacing wire `i` of `towerProd m ψ` by a scalar multiple
  `χ = s • ψᵢ` scales the whole product's state vector by `s`:

    `χ.vec = s • (ψ i).vec  →  (towerProd m (update ψ i χ)).vec = s • (towerProd m ψ).vec`.

  By recursion on the tower, the head wire peeled with `PureState.tmul_vec` and the scalar pulled
  through the tensor product (`TensorProduct.smul_tmul'` on the head, `TensorProduct.tmul_smul` on a
  later wire).

* `towerProd_vec_update_sum_smul` — the **sum form**: replacing wire `i` by a `Fin 2`-superposition
  `χ = ∑_z c z • φ z` distributes as the corresponding superposition of the updated products:

    `χ.vec = ∑_z c z • (φ z).vec  →
       (towerProd m (update ψ i χ)).vec = ∑_z c z • (towerProd m (update ψ i (φ z))).vec`.

  This is the two-term linearity a **non-diagonal** single-wire gate needs: such a gate sends a
  basis wire to a superposition of two basis states, and this lemma distributes that superposition
  over the whole product. Same recursion as the scalar form, the sum pushed through the tensor
  product termwise (`TensorProduct.sum_tmul`/`tmul_sum`). Consumed by every non-diagonal single-wire
  gate's tower re-expression — the Hadamard (`Core/QftTowerHadamard`), the reachable rotations
  (`Core/FourGateReachableWireTower`), and the Problem 4.3(3) basis-change gate
  (`Core/PauliDiagWireTower`).

The statement is an equation of vectors `PureState.vec`; it has no `PureState`-level form, since a
scalar multiple of a unit vector is not itself a `PureState`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Tensor multilinearity of the tower product state on one wire.** Replacing wire `i` of a
product state `towerProd m ψ` by a scalar multiple `χ = s • ψᵢ` scales the whole product's state
vector by `s`:

  `χ.vec = s • (ψ i).vec  →  (towerProd m (Function.update ψ i χ)).vec = s • (towerProd m ψ).vec`.

By recursion on the tower: the head wire (`i = 0`) is peeled with `PureState.tmul_vec` and the
scalar pulled out of the left factor (`TensorProduct.smul_tmul'`); a later wire (`i = i'+1`)
recurses on the tail and pulls the scalar out of the right factor (`TensorProduct.tmul_smul`). It is
the
`.vec`-level wire-locality of `towerProd`, the reusable ingredient for reading a diagonal
single-wire gate (a phase on a basis wire) on a computational tower state. -/
theorem towerProd_vec_update_smul : ∀ (m : ℕ) (ψ : Fin (m + 1) → PureState qubit)
    (i : Fin (m + 1)) (s : ℂ) (χ : PureState qubit), χ.vec = s • (ψ i).vec →
    (towerProd m (Function.update ψ i χ)).vec = s • (towerProd m ψ).vec
  | 0, ψ, i, s, χ, h => by
      obtain rfl := Fin.fin_one_eq_zero i
      rw [towerProd_zero, towerProd_zero, Function.update_self]
      exact h
  | m + 1, ψ, i, s, χ, h => by
      revert h
      refine Fin.cases ?_ ?_ i
      · intro h
        rw [towerProd_succ, towerProd_succ, Function.update_self, Fin.tail_update_zero,
          PureState.tmul_vec, PureState.tmul_vec, h]
        exact (TensorProduct.smul_tmul' _ _ _).symm
      · intro i' h
        rw [towerProd_succ, towerProd_succ, Function.update_of_ne (Fin.succ_ne_zero i').symm,
          Fin.tail_update_succ, PureState.tmul_vec, PureState.tmul_vec,
          towerProd_vec_update_smul m (Fin.tail ψ) i' s χ h]
        exact TensorProduct.tmul_smul _ _ _

/-- **Tensor multilinearity of the tower product state on one wire, sum form.** Replacing wire `i`
of a product state `towerProd m ψ` by a `Fin 2`-superposition `χ = ∑_z c z • φ z` distributes as the
superposition of the updated products:

  `χ.vec = ∑_z c z • (φ z).vec  →
     (towerProd m (update ψ i χ)).vec = ∑_z c z • (towerProd m (update ψ i (φ z))).vec`.

The two-term counterpart of `towerProd_vec_update_smul` (a single scalar): a **non-diagonal**
single-wire gate sends a basis wire to a superposition of two basis states, and this lemma
distributes that superposition over the whole product. Same recursion as the scalar form — the head
wire (`i = 0`) peeled with `PureState.tmul_vec` and the sum pushed out of the left factor
(`TensorProduct.sum_tmul` / `smul_tmul'`); a later wire (`i = i'+1`) recurses on the tail and pushes
the sum out of the right factor (`TensorProduct.tmul_sum` / `tmul_smul`). The reusable ingredient
for reading a non-diagonal single-wire gate (Hadamard, a reachable rotation, the Problem 4.3(3)
basis-change gate) on a computational tower state. -/
theorem towerProd_vec_update_sum_smul : ∀ (m : ℕ) (ψ : Fin (m + 1) → PureState qubit)
    (i : Fin (m + 1)) (c : Fin 2 → ℂ) (φ : Fin 2 → PureState qubit) (χ : PureState qubit),
    χ.vec = ∑ z, c z • (φ z).vec →
    (towerProd m (Function.update ψ i χ)).vec
      = ∑ z, c z • (towerProd m (Function.update ψ i (φ z))).vec := by
  intro m
  induction m with
  | zero =>
      intro ψ i c φ χ h
      obtain rfl := Fin.fin_one_eq_zero i
      simp only [towerProd_zero, Function.update_self]
      exact h
  | succ N ih =>
      intro ψ i c φ χ h
      refine Fin.cases ?_ ?_ i
      · rw [towerProd_succ, Function.update_self, Fin.tail_update_zero, PureState.tmul_vec, h,
          TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [towerProd_succ, Function.update_self, Fin.tail_update_zero, PureState.tmul_vec]
        exact (TensorProduct.smul_tmul' (c z) (φ z).vec _).symm
      · intro i'
        rw [towerProd_succ, Function.update_of_ne (Fin.succ_ne_zero i').symm,
          Fin.tail_update_succ, PureState.tmul_vec, ih (Fin.tail ψ) i' c φ χ h,
          TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [towerProd_succ, Function.update_of_ne (Fin.succ_ne_zero i').symm,
          Fin.tail_update_succ, PureState.tmul_vec]
        exact TensorProduct.tmul_smul (c z) (ψ 0).vec _

end AxQM
