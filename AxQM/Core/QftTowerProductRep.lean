/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QtowerControlQft
import AxQM.Core.QftTowerBasis
import AxQM.Postulates.API.QuditPhaseGradient

/-!
# The product representation of the phase gradient (N&C Problem 5.1, eq. 5.4)

Kitaev's QFT-over-`Z_p` circuit (Problem 5.1) loads a linear **phase gradient** onto the control
register and then reads it out with an inverse QFT (N&C Figure 5.2). The phase-loading stage
produces the standalone gradient `towerPhaseGrad θ n = ⊗_w |+_{2ᵂ·θ}⟩` on the pure control tower
`qtower n qubit` — a *product* over the `n+1` control wires, each a phased-plus state
(`AxQM/Core/QtowerControlQft.lean`). The readout is the inverse tower QFT `qftTowerInverseEvolution
n`, which lives on the *single* `2ⁿ⁺¹`-level register `qudit (2ⁿ⁺¹)` transported onto the tower
along the register bridge `quditPowTower n` (`AxQM/Core/QftRegisterBridge.lean`).

This file proves the **product representation** identifying the wire-by-wire
product `towerPhaseGrad θ n` with the single-register phase gradient
`quditPhaseGrad θ (2ⁿ⁺¹) = (1/√2ⁿ⁺¹) ∑ₖ e^{iθk} |k⟩` (`AxQM/Postulates/API/QuditPhaseGradient.lean`)
transported through the bridge. This is exactly N&C's eq. (5.4): expanding each phased-plus factor
`|+_{2ᵂθ}⟩ = (|0⟩ + e^{i2ᵂθ}|1⟩)/√2` and multiplying out reconstitutes the single sum
`(1/√2ⁿ⁺¹) ∑ₖ e^{iθk} |k⟩`, because the wire bits `b` of the register index `k = ∑_w 2^{n-w} b_w`
turn the product of per-wire phases `∏_w e^{i2^{n-w}θ b_w}` into the single phase `e^{iθk}`.

## What is formalised

* `towerPhaseGrad_eq_congr_quditPhaseGrad` — the **product representation** (eq. 5.4):
  `towerPhaseGrad θ n = Φₙ (quditPhaseGrad θ (2ⁿ⁺¹))` (`Φₙ = PureState.congr (quditPowTower n)`),
  for every real slope `θ`. The per-wire product IS the single-register phase gradient, read
  through the register bridge. Proved by matching inner products against the computational basis:
  on the qudit side the amplitude is `⟨j|φ_θ⟩ = (1/√2ⁿ⁺¹)e^{iθj}`
  (`quditPhaseGrad_inner_quditBasis`), and on the tower side the per-wire product amplitude is
  `(1/√2)ⁿ⁺¹ e^{iθ·Σ_w 2^{n-w} b_w}`,
  with the binary expansion `j = Σ_w 2^{n-w} b_w` making the two phases agree.
* `qftTowerInverseEvolution_evolvePure_towerPhaseGrad` — the **readout reduced through the bridge**:
  `qftTowerInverseEvolution n (towerPhaseGrad θ n)
      = Φₙ (qftInverseEvolution (2ⁿ⁺¹) (quditPhaseGrad θ (2ⁿ⁺¹)))`. The inverse tower QFT of the
  phase gradient is the transport of the single-register inverse QFT applied to the single-register
  phase gradient — the frequency estimate the circuit reads out.
* `qftTowerInverseEvolution_evolvePure_towerPhaseGrad_dyadic` — the **exact dyadic readout**: at a
  *dyadic* slope `θ = 2πM/2ⁿ⁺¹` the phase gradient is exactly the Fourier image `F|M⟩`, so the
  inverse QFT recovers `|M⟩` on the nose and the readout is the computational-basis estimate
  `towerKet n (i ↦ (bits M) i.rev)` — a genuine basis ket. This is the sense in which the circuit
  *performs the quantum Fourier transform*: for a frequency `M/2ⁿ⁺¹` with a finite `(n+1)`-bit
  binary expansion the phase-estimation readout is exact. (For a prime dimension `p`, `ℓ/p` is
  *never* dyadic, so the Problem 5.1 readout is only a finite-precision estimate — its accuracy is
  analysed in `AxQM/NC/Ch5/Problem5_1.lean`.)

The single-wire amplitude `⟨c|+_ψ⟩` is the lemma `qubitPhasePlus_inner_qubitBasis`
(`AxQM/Postulates/API/PhasedPlus.lean`).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The binary-expansion identity behind the product representation.** For `j : Fin (2ⁿ⁺¹)` with
little-endian bits `bits = finFunctionFinEquiv.symm j`, the big-endian weighted sum of the reversed
bits recovers `j`: `Σ_{i} 2^{n-i} · (bits j)(i.rev) = j`. Reindexing `i ↦ i.rev` sends the tower
weight `2^{n-i}` on wire `i.rev` to the register weight `2^i` on bit `i`, so the sum collapses to
the little-endian expansion `j = Σ_i (bits j)(i) · 2^i`. -/
private theorem sum_two_pow_sub_rev_bits (n : ℕ) (j : Fin (2 ^ (n + 1))) :
    ∑ i : Fin (n + 1), 2 ^ (n - (i : ℕ)) * (finFunctionFinEquiv.symm j i.rev : ℕ)
      = (j : ℕ) := by
  have hj : (j : ℕ)
      = ∑ i : Fin (n + 1), (finFunctionFinEquiv.symm j i : ℕ) * 2 ^ (i : ℕ) := by
    conv_lhs => rw [← Equiv.apply_symm_apply finFunctionFinEquiv j, finFunctionFinEquiv_apply]
  rw [hj, ← Equiv.sum_comp (Fin.revPerm)
    (fun i : Fin (n + 1) => 2 ^ (n - (i : ℕ)) * (finFunctionFinEquiv.symm j i.rev : ℕ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.revPerm_apply, Fin.rev_rev, mul_comm]
  congr 2
  have := i.isLt
  rw [Fin.val_rev]
  omega

/-- **Product representation of the phase gradient (N&C Problem 5.1, eq. 5.4).** The wire-by-wire
product phase gradient `towerPhaseGrad θ n = ⊗_w |+_{2ᵂθ}⟩` on the pure control tower equals the
single-register phase gradient `quditPhaseGrad θ (2ⁿ⁺¹) = (1/√2ⁿ⁺¹) ∑ₖ e^{iθk} |k⟩` transported
onto the tower along the register bridge `quditPowTower n`:

`towerPhaseGrad θ n = PureState.congr (quditPowTower n) (quditPhaseGrad θ (2ⁿ⁺¹))`.

This is the identity that multiplying out the per-wire phased-plus factors reconstitutes the single
Fourier sum. Proved by comparing amplitudes against the computational basis: transporting to the
`qudit (2ⁿ⁺¹)` side, both `⟨j|·⟩` equal `(1/√2ⁿ⁺¹)e^{iθj}` — the qudit side directly
(`quditPhaseGrad_inner_quditBasis`), the tower as the product `(1/√2)ⁿ⁺¹ e^{iθ·Σ_w 2^{n-w} b_w}`
of per-wire amplitudes (a `TensorProduct.inner_tmul` induction over the wires), with the binary
expansion `Σ_w 2^{n-w} b_w = j` (`sum_two_pow_sub_rev_bits`) matching the two phases. -/
theorem towerPhaseGrad_eq_congr_quditPhaseGrad (θ : ℝ) (n : ℕ) :
    towerPhaseGrad θ n
      = PureState.congr (quditPowTower n) (quditPhaseGrad θ (2 ^ (n + 1))) := by
  -- Tower amplitude: the product of per-wire amplitudes over the `m+1` wires. The single-wire
  -- amplitude `⟨c | +_ψ⟩ = (1/√2)·e^{iψc}` is `qubitPhasePlus_inner_qubitBasis`.
  have tower : ∀ (m : ℕ) (b : Fin (m + 1) → Fin 2),
      inner ℂ (towerKet m b).vec (towerPhaseGrad θ m).vec
        = (Concrete.invSqrt2 : ℂ) ^ (m + 1)
          * Complex.exp ((θ : ℂ) * Complex.I
              * ((∑ i : Fin (m + 1), 2 ^ (m - (i : ℕ)) * (b i : ℕ) : ℕ) : ℕ)) := by
    intro m
    induction m with
    | zero =>
        intro b
        rw [towerKet_zero, towerPhaseGrad_zero, pow_zero, one_mul]
        change @inner ℂ qubit.space _ _ _ = _
        rw [qubitPhasePlus_inner_qubitBasis]
        have hs : (∑ i : Fin (0 + 1), 2 ^ (0 - (i : ℕ)) * (b i : ℕ)) = (b 0 : ℕ) := by simp
        rw [hs, pow_succ, pow_zero, one_mul]
    | succ m ih =>
        intro b
        rw [towerKet_succ, towerPhaseGrad_succ, PureState.tmul_vec, PureState.tmul_vec]
        change @inner ℂ (TensorProduct ℂ qubit.space (qtower m qubit).space) _ _ _ = _
        rw [TensorProduct.inner_tmul, qubitPhasePlus_inner_qubitBasis, ih (fun i => b i.succ),
          mul_mul_mul_comm, ← pow_succ', ← Complex.exp_add]
        -- Peel the leading wire off the big-endian phase sum (a ℕ identity).
        have hE : (∑ i : Fin (m + 2), 2 ^ (m + 1 - (i : ℕ)) * (b i : ℕ))
            = 2 ^ (m + 1) * (b 0 : ℕ)
              + ∑ i : Fin (m + 1), 2 ^ (m - (i : ℕ)) * ((fun i => b i.succ) i : ℕ) := by
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Nat.sub_zero]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Fin.val_succ]
          congr 2
          omega
        rw [hE]
        congr 2
        push_cast
        ring
  -- ONB of the qudit register, identified with the computational basis states.
  have hext : PureState.congr (quditPowTower n).symm (towerPhaseGrad θ n)
      = quditPhaseGrad θ (2 ^ (n + 1)) := by
    apply PureState.ext
    set b : OrthonormalBasis (Fin (2 ^ (n + 1))) ℂ (qudit (2 ^ (n + 1))).space :=
      EuclideanSpace.basisFun (Fin (2 ^ (n + 1))) ℂ with hb_def
    have hb : ∀ j, b j = (quditBasis j).vec := fun j =>
      (EuclideanSpace.basisFun_apply (Fin (2 ^ (n + 1))) ℂ j).trans (quditBasis_vec j).symm
    -- The two vectors have equal coordinates in the ONB.
    rw [← b.sum_repr' (PureState.congr (quditPowTower n).symm (towerPhaseGrad θ n)).vec,
      ← b.sum_repr' (quditPhaseGrad θ (2 ^ (n + 1))).vec]
    refine Finset.sum_congr rfl fun j _ => ?_
    -- Move the transport off the tower factor (`PureState.inner_congr_symm`).
    rw [hb, PureState.inner_congr_symm (quditPowTower n) (quditBasis j) (towerPhaseGrad θ n),
      quditPowTower_congr_quditBasis, tower, quditPhaseGrad_inner_quditBasis]
    -- Normalisation `(1/√2)ⁿ⁺¹ = (√2ⁿ⁺¹)⁻¹` and phase `Σ_w 2^{n-w} b_w = j`.
    have hnorm : (Concrete.invSqrt2 : ℂ) ^ (n + 1)
        = (Real.sqrt ((2 ^ (n + 1) : ℕ) : ℝ) : ℂ)⁻¹ := by
      rw [Concrete.invSqrt2, Concrete.sqrt_two_pow_inv]; norm_num
    rw [hnorm, sum_two_pow_sub_rev_bits]
  rw [← hext, PureState.congr_congr_symm]

/-- **The inverse-QFT readout of the phase gradient, reduced through the register bridge.** The
inverse tower QFT `qftTowerInverseEvolution n` applied to the phase gradient `towerPhaseGrad θ n`
is the transport (along the bridge `quditPowTower n`) of the single-register inverse QFT
`qftInverseEvolution (2ⁿ⁺¹)` on the single-register phase gradient `quditPhaseGrad θ (2ⁿ⁺¹)`:

`qftTowerInverseEvolution n (towerPhaseGrad θ n)
    = PureState.congr (quditPowTower n) (qftInverseEvolution (2ⁿ⁺¹) (quditPhaseGrad θ (2ⁿ⁺¹)))`.

Immediate from the product representation `towerPhaseGrad_eq_congr_quditPhaseGrad` and the fact that
`qftTowerInverseEvolution n = Evolution.congr (quditPowTower n) (qftInverseEvolution (2ⁿ⁺¹))` is the
transported inverse QFT (`Evolution.congr_evolvePure_congr`). This is the frequency estimate the
circuit's readout stage produces. -/
theorem qftTowerInverseEvolution_evolvePure_towerPhaseGrad (θ : ℝ) (n : ℕ) :
    (qftTowerInverseEvolution n).evolvePure (towerPhaseGrad θ n)
      = PureState.congr (quditPowTower n)
          ((qftInverseEvolution (2 ^ (n + 1))).evolvePure (quditPhaseGrad θ (2 ^ (n + 1)))) := by
  rw [towerPhaseGrad_eq_congr_quditPhaseGrad, qftTowerInverseEvolution,
    Evolution.congr_evolvePure_congr]

/-- **The exact dyadic readout: the circuit performs the QFT for dyadic frequencies.** At a
*dyadic* slope `θ = 2πM/2ⁿ⁺¹` (an integer `M : Fin (2ⁿ⁺¹)`), the phase gradient
`towerPhaseGrad (2πM/2ⁿ⁺¹) n` is exactly the Fourier image `F|M⟩ = qftFourierImage (2ⁿ⁺¹) M`, so the
inverse tower QFT recovers the computational-basis frequency estimate exactly:

`qftTowerInverseEvolution n (towerPhaseGrad (2πM/2ⁿ⁺¹) n) = towerKet n (i ↦ (bits M) i.rev)`,

a genuine basis ket (`bits M = finFunctionFinEquiv.symm M`, the binary digits of `M`, big-endian
reversed by `Fin.rev`). This is precisely "the circuit performs the quantum Fourier transform":
when the frequency `M/2ⁿ⁺¹` has an exact `(n+1)`-bit binary expansion, phase estimation reads it out
on the nose. Proved from the reduced readout `qftTowerInverseEvolution_evolvePure_towerPhaseGrad`,
the dyadic identity `quditPhaseGrad (2πM/2ⁿ⁺¹) (2ⁿ⁺¹) = F|M⟩` (`quditPhaseGrad_eq_qftFourierImage`),
the QFT round-trip `F⁻¹F|M⟩ = |M⟩` (`Evolution.evolvePure_adjoint_evolvePure`), and the bridge
dictionary `Φₙ|M⟩ = towerKet n (bits M rev)` (`quditPowTower_congr_quditBasis`). For a *prime*
dimension `p`, `ℓ/p` is never dyadic, so the Problem 5.1 readout is only a finite-precision
estimate. -/
theorem qftTowerInverseEvolution_evolvePure_towerPhaseGrad_dyadic (n : ℕ)
    (M : Fin (2 ^ (n + 1))) :
    (qftTowerInverseEvolution n).evolvePure
        (towerPhaseGrad (2 * Real.pi * (M : ℕ) / (2 ^ (n + 1) : ℕ)) n)
      = towerKet n (fun i => finFunctionFinEquiv.symm M i.rev) := by
  rw [qftTowerInverseEvolution_evolvePure_towerPhaseGrad,
    ← quditPhaseGrad_eq_qftFourierImage, ← qftEvolution_evolvePure_quditBasis,
    ← qftInverseEvolution_adjoint (2 ^ (n + 1)),
    Evolution.evolvePure_adjoint_evolvePure', quditPowTower_congr_quditBasis]

end AxQM
