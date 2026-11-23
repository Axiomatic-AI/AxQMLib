/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftTowerCircuit
import AxQM.Core.QtowerPhaseGradient
import AxQM.Core.QtowerComposeRight
import AxQM.Postulates.API.InverseQuantumFourierTransform
import AxQM.Postulates.API.ControlledControlledUnitary

/-!
# The inverse-QFT readout on the control register (N&C §5.2, Figure 5.2, last stage)

The final stage of the phase-estimation circuit (N&C Figure 5.2) applies the **inverse quantum
Fourier transform to the `t`-qubit control register**, leaving the target register alone. Run on the
phase-gradient superposition `⊗_w |+_{2^w·θ}⟩ ⊗ |u⟩` produced by the controlled powers
(`AxQM/Core/QtowerPhaseGradient.lean`), it reads the eigenphase `θ/2π` back into the control
register.

The obstacle this file removes is **structural**. The phase-estimation stages live on the nested
control register `qtower t S` (`t` control qubits wrapping the target `S`), whereas the tower
quantum Fourier transform `qftTowerEvolution` (`AxQM/Core/QftRegisterBridge.lean`) lives on the
*pure* qubit tower `qtower n qubit` — it has no room for a separate target. Applying it to the
control register requires first **separating the control qubits from the target**,
`qtower (n+1) S ≃ₛ (qtower n qubit) ⊗ S`
(the two registers are the same up to reassociation, but *not* definitionally — the `qtower`
recursion peels a different number of wires on each side). This file supplies that split, transports
the phase gradient across it, and assembles the inverse-QFT readout gate.

## What is formalised

* `qtowerSplitControl n S` — the **control–target split** `qtower (n+1) S ≃ₛ (qtower n qubit) ⊗ S`:
  it pulls the target `S` out from the bottom of the `(n+1)`-control register to a trailing factor,
  gathering the `n+1` control qubits into the pure tower `qtower n qubit`. Built by induction on `n`
  through the associator `QSystem.assoc`, exactly as the sibling module-factoring bridge
  `qtowerComposeRight` (this is its specialisation reorganised so the split qubit lands *inside* the
  control tower rather than in the base).
* `towerPhaseGrad θ n` — the **standalone phase gradient** `⊗_w |+_{2^w·θ}⟩` on the pure control
  tower `qtower n qubit` (all `n+1` wires phased-plus, no target): the control-register content of
  the phase gradient once the target is stripped off.
* `qtowerSplitControl_congr_qtowerPhaseGrad` — the **phase-gradient dictionary**: the split carries
  the nested phase gradient to the standalone one tensored with the untouched target,
  `qtowerSplitControl n S (qtowerPhaseGrad θ (n+1) u) = (towerPhaseGrad θ n) ⊗ u`;
  `qtowerSplitControl_congr_qtowerKet` is its computational-basis analogue
  (`qtowerKet (n+1) b u ↦ (towerKet n b) ⊗ u`).
* `qftTowerInverseEvolution n` — the **inverse tower QFT** `Evolution.congr (quditPowTower n)
  (qftInverseEvolution (2^{n+1}))` on `qtower n qubit`, the register-tower transport of the inverse
  QFT (Ex 5.5); `qftTowerInverseEvolution_evolvePure_towerKet` reads its action on a basis ket.
* `qtowerControlInverseQft n S` — the **inverse-QFT readout gate** on the phase-estimation register
  `qtower (n+1) S`: the inverse tower QFT applied to the control qubits (through the split), the
  identity on the target `S`. This is Figure 5.2's final box.
* `qtowerControlInverseQft_evolvePure_qtowerPhaseGrad` — the **readout action**: the gate carries
  the phase gradient to `qftTowerInverseEvolution n (towerPhaseGrad θ n) ⊗ u` (through the split),
  reducing the readout of the *nested* phase estimation to the inverse tower QFT of the *standalone*
  control gradient, with the target `u` untouched. That the standalone image is the
  computational-basis estimate `|m⟩` (the product representation, eq. 5.4, exact for a dyadic
  `θ = 2πm/2^{n+1}`) is proved in `AxQM/Core/QftTowerProductRep.lean`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S : QSystem}

/-! ### The control–target split of the phase-estimation register -/

/-- **The control–target split** `qtower (n+1) S ≃ₛ (qtower n qubit) ⊗ S`: separate the `n+1`
control qubits (gathered into the pure tower `qtower n qubit`) from the target `S`, pulled out to a
trailing factor. Built by induction on `n`: the base `qtower 1 S = qubit ⊗ S = (qtower 0 qubit) ⊗ S`
is the identity, and each step tensors the identity on the peeled head control with the tail split
and reassociates the new control past the target through `QSystem.assoc`. Its action on the
phase-estimation states is `qtowerSplitControl_congr_qtowerPhaseGrad` /
`qtowerSplitControl_congr_qtowerKet`. -/
def qtowerSplitControl : (n : ℕ) → (S : QSystem) → (qtower (n + 1) S).Iso ((qtower n qubit) ⊗ S)
  | 0, S => QSystem.Iso.refl (qubit ⊗ S)
  | (n + 1), S =>
      ((QSystem.Iso.refl qubit).tmul (qtowerSplitControl n S)).trans
        (QSystem.assoc qubit (qtower n qubit) S)

/-- Base unfolding of the control–target split: with a single control qubit the register is already
`qubit ⊗ S`, so the split is the identity. -/
@[simp] theorem qtowerSplitControl_zero (S : QSystem) :
    qtowerSplitControl 0 S = QSystem.Iso.refl (qubit ⊗ S) := rfl

/-- Step unfolding of the control–target split: tensor the identity on the peeled head control with
the tail split, then reassociate the new control past the target through `QSystem.assoc`. -/
theorem qtowerSplitControl_succ (n : ℕ) (S : QSystem) :
    qtowerSplitControl (n + 1) S
      = ((QSystem.Iso.refl qubit).tmul (qtowerSplitControl n S)).trans
          (QSystem.assoc qubit (qtower n qubit) S) := rfl

/-! ### The standalone phase gradient on the pure control tower -/

/-- **The standalone phase gradient** `⊗_w |+_{2^w·θ}⟩` on the pure control tower `qtower n qubit`:
all `n+1` wires in the phased-plus state, the outermost (most significant) wire carrying weight
`2^n`, the innermost weight `2^0`. This is the control-register content of the phase gradient
`qtowerPhaseGrad θ (n+1) u` once the target `u` is stripped off
(`qtowerSplitControl_congr_qtowerPhaseGrad`). -/
def towerPhaseGrad (θ : ℝ) : (n : ℕ) → PureState (qtower n qubit)
  | 0 => qubitPhasePlus ((2 : ℝ) ^ 0 * θ)
  | (n + 1) => qubitPhasePlus ((2 : ℝ) ^ (n + 1) * θ) ⊗ towerPhaseGrad θ n

/-- Base unfolding of the standalone phase gradient: a single wire carries the phase `2^0·θ`. -/
@[simp] theorem towerPhaseGrad_zero (θ : ℝ) :
    towerPhaseGrad θ 0 = qubitPhasePlus ((2 : ℝ) ^ 0 * θ) := rfl

/-- Step unfolding of the standalone phase gradient: peel the outermost (most significant) wire
`|+_{2^{n+1}·θ}⟩`. -/
theorem towerPhaseGrad_succ (θ : ℝ) (n : ℕ) :
    towerPhaseGrad θ (n + 1)
      = qubitPhasePlus ((2 : ℝ) ^ (n + 1) * θ) ⊗ towerPhaseGrad θ n := rfl

/-! ### The split carries the phase-estimation states to control ⊗ target -/

/-- **Phase-gradient dictionary for the control–target split.** The split
`qtower (n+1) S ≃ₛ (qtower n qubit) ⊗ S` carries the nested phase gradient
`qtowerPhaseGrad θ (n+1) u` (the `n+1` phased-plus control wires wrapping the target `u`) to the
standalone phase gradient `towerPhaseGrad θ n` on the pure control tower, tensored with the
untouched target `u`:

`qtowerSplitControl n S (qtowerPhaseGrad θ (n+1) u) = (towerPhaseGrad θ n) ⊗ u`.

Proved by `PureState.ext` and induction on `n` on state vectors: the step peels the outermost
phased-plus wire (`qtowerPhaseGrad_succ`, `PureState.tmul_vec`), pushes the tail through the split
by the inductive hypothesis (`QSystem.Iso.tmul_toIsometry_tmul`), and reassociates the head wire
past the target through the associator (`assoc_toIsometry_tmul_tmul`). -/
theorem qtowerSplitControl_congr_qtowerPhaseGrad (θ : ℝ) (n : ℕ) (u : PureState S) :
    PureState.congr (qtowerSplitControl n S) (qtowerPhaseGrad θ (n + 1) u)
      = (towerPhaseGrad θ n).tmul u := by
  suffices key : ∀ (m : ℕ) (v : PureState S),
      (qtowerSplitControl m S).toIsometry (qtowerPhaseGrad θ (m + 1) v).vec
        = (towerPhaseGrad θ m).vec ⊗ₜ[ℂ] v.vec by
    apply PureState.ext
    rw [PureState.congr_vec, PureState.tmul_vec]
    exact key n u
  intro m
  induction m with
  | zero =>
      intro v
      erw [qtowerSplitControl_zero, qtowerPhaseGrad_succ, qtowerPhaseGrad_zero, towerPhaseGrad_zero,
        PureState.tmul_vec]
      rfl
  | succ k ih =>
      intro v
      rw [qtowerPhaseGrad_succ, PureState.tmul_vec]
      change (QSystem.assoc qubit (qtower k qubit) S).toIsometry
          (((QSystem.Iso.refl qubit).tmul (qtowerSplitControl k S)).toIsometry
            ((qubitPhasePlus ((2 : ℝ) ^ (k + 1) * θ)).vec ⊗ₜ[ℂ]
              (qtowerPhaseGrad θ (k + 1) v).vec))
          = (towerPhaseGrad θ (k + 1)).vec ⊗ₜ[ℂ] v.vec
      rw [QSystem.Iso.tmul_toIsometry_tmul, ih v, assoc_toIsometry_tmul_tmul, towerPhaseGrad_succ,
        PureState.tmul_vec]
      rfl

/-- **Computational-basis dictionary for the control–target split.** The split carries the
phase-estimation input `qtowerKet (n+1) b u` (the control register in the computational-basis state
`b`, wrapping the target `u`) to the pure tower basis ket `towerKet n b` tensored with the untouched
target `u`:

`qtowerSplitControl n S (qtowerKet (n+1) b u) = (towerKet n b) ⊗ u`.

The computational-basis companion of `qtowerSplitControl_congr_qtowerPhaseGrad`, proved the same way
(the control wires are basis kets `qubitBasis (b i)` rather than phased-plus states). -/
theorem qtowerSplitControl_congr_qtowerKet (n : ℕ) (b : Fin (n + 1) → Fin 2) (u : PureState S) :
    PureState.congr (qtowerSplitControl n S) (qtowerKet (n + 1) b u)
      = (towerKet n b).tmul u := by
  suffices key : ∀ (m : ℕ) (c : Fin (m + 1) → Fin 2) (v : PureState S),
      (qtowerSplitControl m S).toIsometry (qtowerKet (m + 1) c v).vec
        = (towerKet m c).vec ⊗ₜ[ℂ] v.vec by
    apply PureState.ext
    rw [PureState.congr_vec, PureState.tmul_vec]
    exact key n b u
  intro m
  induction m with
  | zero =>
      intro c v
      erw [qtowerSplitControl_zero, qtowerKet_succ, qtowerKet_zero, towerKet_zero,
        PureState.tmul_vec]
      rfl
  | succ k ih =>
      intro c v
      rw [qtowerKet_succ, PureState.tmul_vec]
      change (QSystem.assoc qubit (qtower k qubit) S).toIsometry
          (((QSystem.Iso.refl qubit).tmul (qtowerSplitControl k S)).toIsometry
            ((qubitBasis (c 0)).vec ⊗ₜ[ℂ] (qtowerKet (k + 1) (Fin.tail c) v).vec))
          = (towerKet (k + 1) c).vec ⊗ₜ[ℂ] v.vec
      rw [QSystem.Iso.tmul_toIsometry_tmul, ih (Fin.tail c) v, assoc_toIsometry_tmul_tmul,
        towerKet_succ, PureState.tmul_vec]
      rfl

/-! ### The inverse-QFT readout gate -/

/-- **The inverse tower QFT** on the pure control register `qtower n qubit`: the inverse quantum
Fourier transform `qftInverseEvolution (2^{n+1})` (Ex 5.5) of the single `2^{n+1}`-level register,
transported onto the `(n+1)`-qubit tower along the register bridge `quditPowTower n`. The
`Evolution` undoing `qftTowerEvolution n`. -/
def qftTowerInverseEvolution (n : ℕ) : Evolution (qtower n qubit) :=
  Evolution.congr (quditPowTower n) (qftInverseEvolution (2 ^ (n + 1)))

/-- **The inverse tower QFT read on a computational-basis ket.** By the reader
`quditPowTower_congr_evolvePure_towerKet` at `U = qftInverseEvolution (2^{n+1})`, the inverse tower
QFT acts on `towerKet n b` as the transport of the single-register inverse QFT's action on the
register ket `|finFunctionFinEquiv (b ∘ Fin.rev)⟩` — so on the computational basis it genuinely
performs the inverse quantum Fourier transform, wire bits reversed by `Fin.rev`. -/
theorem qftTowerInverseEvolution_evolvePure_towerKet (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    (qftTowerInverseEvolution n).evolvePure (towerKet n b)
      = PureState.congr (quditPowTower n)
          ((qftInverseEvolution (2 ^ (n + 1))).evolvePure
            (quditBasis (finFunctionFinEquiv (fun i => b i.rev)))) :=
  quditPowTower_congr_evolvePure_towerKet n (qftInverseEvolution (2 ^ (n + 1))) b

/-- **The inverse-QFT readout gate** on the phase-estimation register `qtower (n+1) S`: the inverse
tower QFT `qftTowerInverseEvolution n` applied to the `n+1` control qubits — through the
control–target split `qtowerSplitControl n S` — and the identity on the target `S`. This is the
final box of N&C Figure 5.2, the inverse quantum Fourier transform on the control register that
reads the eigenphase back into the estimate register. Its action on the phase gradient is
`qtowerControlInverseQft_evolvePure_qtowerPhaseGrad`. -/
def qtowerControlInverseQft (n : ℕ) (S : QSystem) : Evolution (qtower (n + 1) S) :=
  Evolution.congr (qtowerSplitControl n S).symm ((qftTowerInverseEvolution n).onLeft S)

/-- The nested phase gradient rewritten through the split: `qtowerPhaseGrad θ (n+1) u` is the
transport (back along the split) of the standalone phase gradient tensored with the target. The
`.symm` companion of `qtowerSplitControl_congr_qtowerPhaseGrad`. -/
theorem qtowerPhaseGrad_eq_congr_qtowerSplitControl_symm (θ : ℝ) (n : ℕ) (u : PureState S) :
    qtowerPhaseGrad θ (n + 1) u
      = PureState.congr (qtowerSplitControl n S).symm ((towerPhaseGrad θ n).tmul u) := by
  rw [← qtowerSplitControl_congr_qtowerPhaseGrad θ n u, PureState.congr_symm_congr]

/-- **The inverse-QFT readout acts on the control register.** The readout gate
`qtowerControlInverseQft n S` carries the phase gradient `qtowerPhaseGrad θ (n+1) u` to the inverse
tower QFT of the *standalone* control gradient tensored with the untouched target `u` (transported
back along the split):

`qtowerControlInverseQft n S (qtowerPhaseGrad θ (n+1) u)
    = (split⁻¹) ((qftTowerInverseEvolution n (towerPhaseGrad θ n)) ⊗ u)`.

So the readout of the *nested* phase estimation reduces to the inverse tower QFT of the standalone
gradient on the pure control tower — the target register is untouched (`Evolution.onLeft`), and the
control–target split intertwines the two (`Evolution.congr_evolvePure_congr`). That the standalone
image is the computational-basis estimate `|m⟩` for a dyadic `θ = 2πm/2^{n+1}` (the product
representation, eq. 5.4) is proved in `AxQM/Core/QftTowerProductRep.lean`. -/
theorem qtowerControlInverseQft_evolvePure_qtowerPhaseGrad (θ : ℝ) (n : ℕ) (u : PureState S) :
    (qtowerControlInverseQft n S).evolvePure (qtowerPhaseGrad θ (n + 1) u)
      = PureState.congr (qtowerSplitControl n S).symm
          (((qftTowerInverseEvolution n).evolvePure (towerPhaseGrad θ n)).tmul u) := by
  rw [qtowerPhaseGrad_eq_congr_qtowerSplitControl_symm, qtowerControlInverseQft,
    Evolution.congr_evolvePure_congr, Evolution.onLeft_evolvePure]

end AxQM
