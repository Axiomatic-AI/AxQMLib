/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.MultiControlledNotBasis
import AxQM.Postulates.API.TensorPowSplit
import AxQM.Postulates.API.Associator
import AxQM.Postulates.API.SystemIsoComm
import AxQM.Postulates.PiTensorState

/-!
# The `qtower ↔ tensor-power` structural bridge (N&C Exercise 4.29)

Nielsen & Chuang, Exercise 4.29 (p. 184), asks for a no-work-qubit `O(n²)` circuit implementing
`Cⁿ(X)`. The grounded `Cⁿ(X) = mcCtrl n pauliXGate` lives on the **right-nested** control
tower `qtower n qubit = qubit ⊗ (qubit ⊗ (⋯ ⊗ qubit))`
(`AxQM/Core/MultiControlledReduction.lean`), while the `SWAP`-network wire-permutation gate
`Evolution.permWires` — the gate for placing a `Toffoli`/`CNOT` on *non-contiguous* wires — lives on
the **symmetric** register `qubit ^⊗ₛ (n+1)` (the `n+1`-fold `PiTensorProduct`,
`AxQM/Postulates/API/WirePermutation.lean`). Transporting a wire permutation onto the grounded gate
therefore needs a structural isomorphism connecting the two registers.

## What is formalised

* `qtowerQubitTensorPow n` — the **bridge** `qtower n qubit ≃ₛ qubit ^⊗ₛ (n+1)`, built by induction
  on `n`: the base `qtower 0 qubit = qubit ≃ₛ qubit ^⊗ₛ 1` is `QSystem.tensorPowOne`, and each step
  reassociates the peeled head control through `QSystem.tensorPowSuccHead` after applying
  the isomorphism to the `n`-fold tail (`QSystem.Iso.tmul` with the identity on the head qubit).
* `qtowerQubitTensorPow_congr_towerKet` — the **basis correspondence**: the bridge carries the
  `(n+1)`-qubit computational tower basis state `towerKet n b` to the symmetric product basis state
  `⨂ᵢ |b i⟩` (`PureState.piTensor fun i => qubitBasis (b i)`). This is what lets the effect of a
  wire-addressed gate on a basis input — read off on `qubit ^⊗ₛ (n+1)` via
  `Evolution.permWires_op_tprod` — be pulled back to the grounded `qtower` register.
* `qtowerQubitTensorPow_symm_congr_piTensor` — the **backward** basis correspondence: the inverse
  bridge carries `⨂ᵢ |b i⟩` back to `towerKet n b`, the `.symm` companion of the previous lemma (via
  the `PureState.congr` roundtrip). This is the placement-dictionary direction consumed when a gate
  computed on the symmetric register is transported onto the grounded `qtower`.

## Design notes

* **The pieces on the symmetric side.** `Evolution.permWires` (the wire permutation as an
  `Evolution`) and `QSystem.tensorPowSuccHead` (the head-peel `S ^⊗ₛ (n+1) ≃ₛ S ⊗ S ^⊗ₛ n`) are
  assembled here into the qtower-specific bridge and its basis dictionary, which lets the wire
  permutation be transported onto `qtower n qubit` (`Evolution.congr`) for the `Cᵏ(X)`-block
  `Toffoli` reduction.
* **Why the recursion matches definitionally.** `qtower (n+1) qubit = qubit ⊗ qtower n qubit`
  *definitionally* (peeling the outer control is the defining equation of `qtower` on its `ℕ`
  argument), so the successor isomorphism `(Iso.refl qubit).tmul (bridge n)` — of type
  `qubit ⊗ qtower n qubit ≃ₛ qubit ⊗ qubit ^⊗ₛ (n+1)` — type-checks against the expected domain
  `qtower (n+1) qubit` with no `cast`. (This is unlike the `qtower m (qubit ⊗ S) = qtower (m+1) S`
  rearrangement of Exercise 4.30, which is only *propositional*.)
* **Proof of the basis correspondence.** By `PureState.ext` it reduces to the equation of state
  vectors `(bridge n).toIsometry (towerKet n b).vec = ⨂ᵢ (qubitBasis (b i)).vec`, proved by
  induction: the step peels the head wire with `PureState.tmul_vec`, applies
  `QSystem.Iso.tmul_toIsometry_tmul` and the inductive hypothesis to the tail, then re-cons's the
  head with `QSystem.tensorPowSuccHead_symm_toIsometry_tmul_tprod`, closing with
  `Fin.cons_self_tail`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The `qtower ↔ tensor-power` bridge** `qtower n qubit ≃ₛ qubit ^⊗ₛ (n+1)`: the system
isomorphism identifying the right-nested `(n+1)`-qubit control tower `qtower n qubit` with the
symmetric `(n+1)`-fold power `qubit ^⊗ₛ (n+1)`. Built by induction on `n` — the base
`qtower 0 qubit = qubit ≃ₛ qubit ^⊗ₛ 1` is `QSystem.tensorPowOne`, and each successor step tensors
the identity on the head qubit with the tail bridge and reassociates through the head-peel iso
`QSystem.tensorPowSuccHead`. Its action on the computational basis is
`qtowerQubitTensorPow_congr_towerKet`. -/
def qtowerQubitTensorPow : (n : ℕ) → (qtower n qubit).Iso (qubit ^⊗ₛ (n + 1))
  | 0 => qubit.tensorPowOne
  | n + 1 =>
      ((QSystem.Iso.refl qubit).tmul (qtowerQubitTensorPow n)).trans
        (QSystem.tensorPowSuccHead qubit (n + 1)).symm

/-- Base unfolding of the bridge: the single-qubit tower is the one-factor collapse. -/
@[simp] theorem qtowerQubitTensorPow_zero :
    qtowerQubitTensorPow 0 = qubit.tensorPowOne := rfl

/-- Step unfolding of the bridge: tensor the identity on the head control with the tail bridge, then
reassociate through the head-peel iso. -/
theorem qtowerQubitTensorPow_succ (n : ℕ) :
    qtowerQubitTensorPow (n + 1)
      = ((QSystem.Iso.refl qubit).tmul (qtowerQubitTensorPow n)).trans
          (QSystem.tensorPowSuccHead qubit (n + 1)).symm := rfl

/-- **Basis correspondence for the bridge.** The `qtower ↔ tensor-power` bridge carries the
`(n+1)`-qubit computational tower basis state `towerKet n b` (the right-nested product
`|b 0⟩ ⊗ ⋯ ⊗ |b n⟩` on `qtower n qubit`) to the symmetric product basis state `⨂ᵢ |b i⟩` on
`qubit ^⊗ₛ (n+1)`. This is the dictionary between the two registers' computational bases, so a
gate's action on a basis input computed on `qubit ^⊗ₛ (n+1)` (e.g. a wire permutation via
`Evolution.permWires_op_tprod`) transports to the grounded `qtower` register. -/
theorem qtowerQubitTensorPow_congr_towerKet (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    PureState.congr (qtowerQubitTensorPow n) (towerKet n b)
      = PureState.piTensor (fun i => qubitBasis (b i)) := by
  -- Reduce to the equation of state vectors and induct there.
  -- The `succ` step uses that `qtower (k+1) qubit = qubit ⊗ qtower k qubit` *definitionally*, so a
  -- `change` peels the head-wire isometry chain into its two `QSystem.Iso` factors with no `cast`.
  suffices key : ∀ (m : ℕ) (c : Fin (m + 1) → Fin 2),
      (qtowerQubitTensorPow m).toIsometry (towerKet m c).vec
        = ⨂ₜ[ℂ] i, (qubitBasis (c i)).vec by
    apply PureState.ext
    rw [PureState.congr_vec, PureState.piTensor_vec]
    exact key n b
  intro m
  induction m with
  | zero =>
      intro c
      rw [qtowerQubitTensorPow_zero, towerKet_zero]
      erw [QSystem.tensorPowOne_toIsometry_apply]
      congr 1
      funext i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      rfl
  | succ k ih =>
      intro c
      rw [towerKet_succ, PureState.tmul_vec]
      -- `qtowerQubitTensorPow (k+1)` is definitionally `((refl qubit).tmul (bridge k)).trans
      -- (tensorPowSuccHead qubit (k+1)).symm`; apply its two isometry factors in turn.
      change (QSystem.tensorPowSuccHead qubit (k + 1)).symm.toIsometry
          (((QSystem.Iso.refl qubit).tmul (qtowerQubitTensorPow k)).toIsometry
            ((qubitBasis (c 0)).vec ⊗ₜ[ℂ] (towerKet k (fun i => c i.succ)).vec))
          = ⨂ₜ[ℂ] i, (qubitBasis (c i)).vec
      rw [QSystem.Iso.tmul_toIsometry_tmul, ih (fun i => c i.succ),
        QSystem.Iso.symm_toIsometry, QSystem.tensorPowSuccHead_symm_toIsometry_tmul_tprod]
      congr 1
      funext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · rw [Fin.cons_zero]
        rfl
      · rw [Fin.cons_succ]

/-- **Backward basis correspondence for the bridge.** The *inverse* bridge
`(qtowerQubitTensorPow n).symm` carries the symmetric product basis state `⨂ᵢ |b i⟩` on
`qubit ^⊗ₛ (n+1)` back to the `(n+1)`-qubit computational tower basis state `towerKet n b` on
`qtower n qubit`. The `.symm` companion of `qtowerQubitTensorPow_congr_towerKet`, obtained from it
by the `PureState.congr` roundtrip cancellation `PureState.congr_symm_congr`. This is the
wire-addressed **placement dictionary** direction: a gate's action on a basis input on the symmetric
register (e.g. a wire permutation) is pulled back to the grounded `qtower` register through it. -/
theorem qtowerQubitTensorPow_symm_congr_piTensor (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    PureState.congr (qtowerQubitTensorPow n).symm (PureState.piTensor fun i => qubitBasis (b i))
      = towerKet n b := by
  rw [← qtowerQubitTensorPow_congr_towerKet n b, PureState.congr_symm_congr]

end AxQM
