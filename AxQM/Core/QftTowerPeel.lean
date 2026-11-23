/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftTowerHeadLayer
import AxQM.Core.QtowerWirePermutation
import AxQM.Core.EvolutionTowerBasisExt

/-!
# The Figure 5.1 head-layer peel of the tower QFT (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) is assembled by an induction over the tower
depth whose one step *peels* the head control wire's Figure 5.1 gates off `qftTowerEvolution (n+1)`
and recurses on the tail. The head layer's state-level action is
`qftHeadLayer_evolvePure_towerKet`: the head Hadamard and head control cascade send
`towerKet (n+1) b` to `|+_θ⟩ ⊗ towerKet n (Fin.tail b)` with `θ` the **last** output wire's phase.
This file closes the peel: it exhibits `qftTowerEvolution (n+1)` as the composite

  `qftTowerEvolution (n+1) = Φ ∘ (qftTowerEvolution n on the tail) ∘ qftHeadLayer n`,

`Φ` the cyclic wire permutation `(finRotate (n+2)).symm` that routes the head-produced last wire
back into position — the recursive circuit structure of Figure 5.1.

## The peel and its permutation

Read on a computational tower ket `towerKet (n+1) b`, the three factors compose to a product state
whose wires must be matched against the product form (N&C eq. 5.4, `qftTowerEvolution_evolvePure_
towerKet_towerProd`). The head layer deposits the *last* output wire's phased-plus state on the head
wire and leaves the tail computational; the tail QFT
`(qftTowerEvolution n).onRight qubit` turns the tail into its product form, whose wires carry the
first `n+1` output phases (`qftTowerWirePhase_castSucc_qubitPhasePlus`). So after the
head layer and the tail QFT wire `0` holds output wire `n+1` and wire `j+1` holds output wire `j` —
one cyclic shift away from the product form. The permutation `Φ = (finRotate (n+2)).symm` closes
that shift: its action moves the factor on wire `finRotate (n+2) i` to wire `i`, i.e. output wire
`i` to wire `i`.

## What is formalised

* `qtowerQubitTensorPow_congr_towerProd` / `qtowerQubitTensorPow_symm_congr_piTensor_towerProd` —
  the forward/backward `qtower ↔ tensor-power` bridge dictionary at the level of an **arbitrary**
  product state `towerProd n φ` (the basis-input `qtowerQubitTensorPow_congr_towerKet` /
  `qtowerQubitTensorPow_symm_congr_piTensor` are the special case `φ i = |b i⟩`): it carries
  `towerProd n φ` to the symmetric product state `⨂ₚ i, φ i` and back.
* `qtowerPermWires_evolvePure_towerProd` — the tower wire-permutation gate's action on a product
  state: `qtowerPermWires σ (towerProd n φ) = towerProd n (φ ∘ σ⁻¹)` (the arbitrary-factor
  generalisation of `qtowerPermWires_evolvePure_towerKet`, which permutes basis wires).
* `qftTowerEvolution_succ_eq_qftHeadLayer_peel` — **the peel identity**:
  `qftTowerEvolution (n+1) = qtowerPermWires (finRotate (n+2)).symm · (qftTowerEvolution n).onRight
  qubit · qftHeadLayer n`, the recursive Figure 5.1 structure of the tower QFT.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {n : ℕ}

/-- **The `qtower ↔ tensor-power` bridge on a product state.** The bridge `qtowerQubitTensorPow n`
carries the right-nested product state `towerProd n φ` on `qtower n qubit` to the symmetric product
state `⨂ₚ i, φ i` on `qubit ^⊗ₛ (n+1)`. This is `qtowerQubitTensorPow_congr_towerKet` (which
handles the computational-basis case `φ i = |b i⟩`) generalised to an **arbitrary** per-wire pure
state `φ i`; the proof is the same tower induction, the head-peel iso
`qtower (k+1) qubit = qubit ⊗ qtower k qubit` handled definitionally by `change`. It lets the
wire-permutation action be read off a general product input. -/
theorem qtowerQubitTensorPow_congr_towerProd (n : ℕ) (φ : Fin (n + 1) → PureState qubit) :
    PureState.congr (qtowerQubitTensorPow n) (towerProd n φ) = PureState.piTensor fun i => φ i := by
  suffices key : ∀ (m : ℕ) (ψ : Fin (m + 1) → PureState qubit),
      (qtowerQubitTensorPow m).toIsometry (towerProd m ψ).vec = ⨂ₜ[ℂ] i, (ψ i).vec by
    apply PureState.ext
    rw [PureState.congr_vec, PureState.piTensor_vec]
    exact key n φ
  intro m
  induction m with
  | zero =>
      intro ψ
      rw [qtowerQubitTensorPow_zero, towerProd_zero]
      erw [QSystem.tensorPowOne_toIsometry_apply]
      congr 1
      funext i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      rfl
  | succ k ih =>
      intro ψ
      rw [towerProd_succ, PureState.tmul_vec]
      change (QSystem.tensorPowSuccHead qubit (k + 1)).symm.toIsometry
          (((QSystem.Iso.refl qubit).tmul (qtowerQubitTensorPow k)).toIsometry
            ((ψ 0).vec ⊗ₜ[ℂ] (towerProd k (Fin.tail ψ)).vec))
          = ⨂ₜ[ℂ] i, (ψ i).vec
      rw [QSystem.Iso.tmul_toIsometry_tmul, ih (Fin.tail ψ),
        QSystem.Iso.symm_toIsometry, QSystem.tensorPowSuccHead_symm_toIsometry_tmul_tprod]
      congr 1
      funext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;>
        simp [QSystem.Iso.refl_toIsometry, Fin.tail]

/-- **Backward `qtower ↔ tensor-power` bridge on a product state.** The inverse bridge
`(qtowerQubitTensorPow n).symm` carries the symmetric product state `⨂ₚ i, φ i` back to the
right-nested tower product state `towerProd n φ`. The `.symm` companion of
`qtowerQubitTensorPow_congr_towerProd`, and the arbitrary-factor generalisation of the basis-input
`qtowerQubitTensorPow_symm_congr_piTensor`; obtained from the forward bridge by the
`PureState.congr` roundtrip cancellation `PureState.congr_symm_congr`. This is the
placement-dictionary direction the product-state wire-permutation action consumes. -/
theorem qtowerQubitTensorPow_symm_congr_piTensor_towerProd (n : ℕ)
    (φ : Fin (n + 1) → PureState qubit) :
    PureState.congr (qtowerQubitTensorPow n).symm (PureState.piTensor fun i => φ i)
      = towerProd n φ := by
  rw [← qtowerQubitTensorPow_congr_towerProd n φ, PureState.congr_symm_congr]

/-- **The tower wire-permutation gate on a product state.** Applying `Evolution.qtowerPermWires σ`
to the product state `towerProd n φ` yields `towerProd n (fun i => φ (σ⁻¹ i))`: the factor on wire
`j` is moved to wire `σ j`. This is the arbitrary-factor generalisation of
`qtowerPermWires_evolvePure_towerKet` (which permutes basis wires `|b j⟩`), obtained by transporting
`towerProd n φ` to the symmetric product state through the backward bridge dictionary
`qtowerQubitTensorPow_symm_congr_piTensor_towerProd`, applying the product-state permutation action
`Evolution.permWires_evolvePure_piTensor`, and folding back. -/
theorem qtowerPermWires_evolvePure_towerProd (σ : Equiv.Perm (Fin (n + 1)))
    (φ : Fin (n + 1) → PureState qubit) :
    (Evolution.qtowerPermWires σ).evolvePure (towerProd n φ)
      = towerProd n fun i => φ (σ.symm i) := by
  erw [Evolution.qtowerPermWires, ← qtowerQubitTensorPow_symm_congr_piTensor_towerProd n φ,
    Evolution.congr_evolvePure_congr, Evolution.permWires_evolvePure_piTensor]
  exact qtowerQubitTensorPow_symm_congr_piTensor_towerProd n _

/-- **The tail QFT of the head-layer peel.** The `n`-tower quantum Fourier transform
`qftTowerEvolution n` lifted onto the `(n+1)`-tower as a gate acting on the tail wires `1 … n+1`
only (the head wire `0` idle), i.e. `(qftTowerEvolution n).onRight qubit` retyped through the
definitional head-peel `qtower (n+1) qubit = qubit ⊗ qtower n qubit`. This is the recursive call of
the Figure 5.1 peel `qftTowerEvolution_succ_eq_qftHeadLayer_peel`. -/
def qftTailEvolution (n : ℕ) : Evolution (qtower (n + 1) qubit) :=
  (qftTowerEvolution n).onRight qubit

/-- **Problem 5.2 (the Figure 5.1 head-layer peel).** The transported quantum Fourier transform on
the `(n+1)`-tower factors as its Figure 5.1 head layer, then the QFT on the tail wires, then a
cyclic wire permutation:

  `qftTowerEvolution (n+1)
     = qtowerPermWires (finRotate (n+2)).symm · qftTailEvolution n · qftHeadLayer n`.

Read on a computational tower ket `towerKet (n+1) b` and matched against the product form (N&C
eq. 5.4): the head layer produces `|+_{θ}⟩ ⊗ towerKet n (Fin.tail b)` with `θ` the **last** output
wire's phase (`qftHeadLayer_evolvePure_towerKet`); the tail QFT `qftTailEvolution n` turns the tail
into its product form, whose wire `j` carries output wire `j`'s phase
(`qftTowerWirePhase_castSucc_qubitPhasePlus`). So after the two the head wire holds output wire
`n+1` and wire `j+1` holds output wire `j` — the cyclic permutation
`(finRotate (n+2)).symm` (whose action sends the factor on wire `finRotate (n+2) i` to wire `i`)
routes each output wire `i` back to wire `i`, reproducing the product form
`qftTowerEvolution_evolvePure_towerKet_towerProd`. This is the recursive circuit structure of Figure
5.1: peel the head control wire's gates, recurse on the tail. -/
theorem qftTowerEvolution_succ_eq_qftHeadLayer_peel (n : ℕ) :
    qftTowerEvolution (n + 1)
      = Evolution.qtowerPermWires (finRotate (n + 2)).symm
        * qftTailEvolution n
        * qftHeadLayer n := by
  apply Evolution.ext_towerKet
  intro b
  rw [qftTowerEvolution_evolvePure_towerKet_towerProd]
  simp only [Evolution.mul_def, Evolution.evolvePure_comp, qftTailEvolution]
  rw [qftHeadLayer_evolvePure_towerKet]
  erw [Evolution.mul_def, Evolution.evolvePure_comp, Evolution.onRight_evolvePure]
  rw [qftTowerEvolution_evolvePure_towerKet_towerProd]
  -- Repackage the head-plus-tail product `|+_θ⟩ ⊗ towerProd n (…)` as a single `towerProd (n+1)`.
  rw [← towerProd_cons, qtowerPermWires_evolvePure_towerProd, Equiv.symm_symm]
  -- Match wire by wire: the permuted head-plus-tail factor on wire `i` is output wire `i`'s phase.
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => rw [finRotate_last, Fin.cons_zero]
  | cast j =>
      rw [finRotate_apply, Fin.coeSucc_eq_succ, Fin.cons_succ,
        qftTowerWirePhase_castSucc_qubitPhasePlus]

/-- **Problem 5.2 (the head-layer peel at the state level).** The evolve-level twin of the
operator-level peel `qftTowerEvolution_succ_eq_qftHeadLayer_peel`: applying the transported quantum
Fourier transform on the `(n+1)`-tower to a state `ρ` factors as the head layer, then the tail QFT,
then the cyclic wire permutation, each applied in turn:

  `(qftTowerEvolution (n+1)).evolve ρ
     = (qtowerPermWires (finRotate (n+2)).symm).evolve
         ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ))`.

Immediate from the operator-level peel by unfolding the `Evolution`-monoid product into sequential
state evolution (`Evolution.mul_def`, `Evolution.evolve_comp`). This is the form the measured-QFT
outer induction reads before deferring the terminal measurement past each layer. -/
theorem qftTowerEvolution_succ_evolve_peel (ρ : State (qtower (n + 1) qubit)) :
    (qftTowerEvolution (n + 1)).evolve ρ
      = (Evolution.qtowerPermWires (finRotate (n + 2)).symm).evolve
          ((qftTailEvolution n).evolve ((qftHeadLayer n).evolve ρ)) := by
  rw [qftTowerEvolution_succ_eq_qftHeadLayer_peel]
  simp only [Evolution.mul_def, Evolution.evolve_comp]

end AxQM
