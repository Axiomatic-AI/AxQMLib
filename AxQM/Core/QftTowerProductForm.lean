/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftTowerCircuit
import AxQM.Core.QtowerSingleWireGate
import AxQM.Postulates.API.PhasedPlus

/-!
# The tower QFT as a product of per-wire phased-plus states (N&C Problem 5.2)

Nielsen & Chuang's **product form of the quantum Fourier transform** (eq. 5.4) reads the transform
on a computational-basis input as a *tensor product of single-qubit states*: each output wire
carries a phased-plus state `|+_θ⟩ = (|0⟩ + e^{iθ}|1⟩)/√2`, its relative phase the binary
fraction the QFT appends to that wire. This file transports that product form onto the tower
`qtower n qubit` on which the measured-QFT reduction (Problem 5.2) reads the circuit gate by gate.

The outer tower induction that assembles the whole-circuit reduction peels the head control wire's
Figure 5.1 gates (a Hadamard and its controlled-`Rₖ` cascade) off `qftTowerEvolution (n+1)` and
recurses on the tail. The peel's content is an `Evolution` identity checked on every
computational tower ket `towerKet n b` (`Evolution.ext_towerKet`), and *both* sides of that check
are read against this product form — the transported QFT on the left, the composed head-and-tail
gates on the right. This basis-state reading is the shared computational core of the peel.

## What is formalised

* `qftTowerWirePhase n b i` — the **per-wire QFT phase** wire `i` of the tower acquires on input
  `towerKet n b`: `2π · J · 2^{i.rev} / 2^{n+1}` with `J = finFunctionFinEquiv (b ∘ Fin.rev)`
  the little-endian register index the bridge sends `towerKet n b` to. The `Fin.rev`s reconcile the
  big-endian register bridge with the little-endian wire indexing of the Figure 5.1 gates.
* `qftTowerEvolution_evolvePure_towerKet_towerProd` — **the product form on the tower**: the
  transported QFT sends `towerKet n b` to the tower product state
  `towerProd n (fun i => qubitPhasePlus (qftTowerWirePhase n b i))` — a phased-plus state on every
  wire, no entanglement (N&C eq. 5.4 read on the tower).

## Proof

The tower reader `qftTowerEvolution_evolvePure_towerKet` presents the left side as
the transport of the monolithic register QFT's action on `|J⟩`, and
`qftEvolution_evolvePure_quditBasis` expands it as the Fourier superposition
`∑_K (1/√2^{n+1}) e^{2πi J K / 2^{n+1}} |K⟩`. Re-indexing
the register sum over wire bit-strings `kbits` (`finFunctionFinEquiv`) turns the exponential into a
product over wires (`Complex.exp_sum`), transports each ket to `towerKet n (kbits ∘ Fin.rev)` (the
bridge dictionary `quditPowTower_congr_quditBasis_apply`), and — after the endianness re-index
`kbits ↦ kbits ∘ Fin.rev` — matches the multilinear expansion of the tower product state
`towerProd n (fun i => qubitPhasePlus …)` term by term, the per-wire coefficient
`invSqrt2 · e^{iθ_i}^{bit}` agreeing with the QFT's product coefficient. The all-wire multilinear
expansion of `towerProd` into the computational basis (the input to the match) is proved inline by
induction on the tower, the tensor bilinearity of `PureState.tmul` distributing the per-wire
superpositions — the all-wire generalisation of the single-wire multilinearity the Figure 5.1
Hadamard re-expression uses.

-/

open scoped InnerProductSpace TensorProduct
open Matrix

noncomputable section

namespace AxQM

/-- **The per-wire QFT phase.** On input `towerKet n b`, the transported quantum Fourier transform
leaves wire `i` of the tower in the phased-plus state `(|0⟩ + e^{iθ}|1⟩)/√2` with angle
`θ = qftTowerWirePhase n b i = 2π · J · 2^{i.rev} / 2^{n+1}`, where
`J = (finFunctionFinEquiv (fun m => b m.rev) : Fin (2^{n+1}))` is the little-endian register index
the bridge `quditPowTower n` identifies `towerKet n b` with. The `Fin.rev`s reconcile the big-endian
register bridge with the little-endian `finFunctionFinEquiv` wire indexing of the Figure 5.1 gates,
the same `Fin.rev` bookkeeping the tower reader carries. -/
def qftTowerWirePhase (n : ℕ) (b : Fin (n + 1) → Fin 2) (i : Fin (n + 1)) : ℝ :=
  2 * Real.pi * ((finFunctionFinEquiv (fun m => b m.rev) : Fin (2 ^ (n + 1))) : ℕ)
    * (2 ^ (i.rev : ℕ)) / (2 ^ (n + 1))

/-- **Problem 5.2 (the tower QFT is a product of per-wire phased-plus states — N&C eq. 5.4).** The
transported quantum Fourier transform `qftTowerEvolution n` sends the computational tower ket
`towerKet n b` to the tower product state

  `towerProd n (fun i => qubitPhasePlus (qftTowerWirePhase n b i))`,

a phased-plus state `(|0⟩ + e^{iθ_i}|1⟩)/√2` on every wire `i`, `θ_i = qftTowerWirePhase n b i`,
and no entanglement between wires — Nielsen & Chuang's product form (eq. 5.4) read on the qubit
tower. This is the shared basis-state reading the outer tower induction (Problem 5.2) matches both
the transported QFT and the composed head-and-tail Figure 5.1 gates against. -/
theorem qftTowerEvolution_evolvePure_towerKet_towerProd (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    (qftTowerEvolution n).evolvePure (towerKet n b)
      = towerProd n (fun i => qubitPhasePlus (qftTowerWirePhase n b i)) := by
  -- **All-wire multilinear expansion of a tower product state**:
  -- if each wire's state `φ i` expands with coefficients `c i`, the tower product `towerProd N φ`
  -- expands over the whole computational tower basis with product coefficients. By induction on the
  -- tower, distributing the head wire's superposition through the tensor product
  -- (`PureState.tmul_vec` bilinearity) — the all-wire generalisation of the single-wire
  -- multilinearity the Figure 5.1 Hadamard re-expression uses.
  have towerProd_vec_eq_sum : ∀ (N : ℕ) (c : Fin (N + 1) → Fin 2 → ℂ)
      (φ : Fin (N + 1) → PureState qubit),
      (∀ i, (φ i).vec = ∑ z, c i z • (qubitBasis z).vec) →
      (towerProd N φ).vec = ∑ k : Fin (N + 1) → Fin 2, (∏ i, c i (k i)) • (towerKet N k).vec := by
    intro N
    induction N with
    | zero =>
        intro c φ hφ
        rw [towerProd_zero, hφ 0]
        refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2))
          (fun k => (∏ i, c i (k i)) • (towerKet 0 k).vec)
          (fun z => c 0 z • (qubitBasis z).vec) (fun k => ?_)).symm
        rw [Fin.prod_univ_one, towerKet_eq_towerProd, towerProd_zero]
        rfl
    | succ N ih =>
        intro c φ hφ
        rw [towerProd_succ, PureState.tmul_vec, hφ 0,
          ih (fun i => c i.succ) (Fin.tail φ) (fun i => hφ i.succ), TensorProduct.sum_tmul,
          ← (Fin.consEquiv fun _ : Fin (N + 2) => Fin 2).sum_comp
            (fun k => (∏ i, c i (k i)) • (towerKet (N + 1) k).vec),
          Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k' _ => ?_
        simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
          towerKet_succ, PureState.tmul_vec]
        rw [TensorProduct.smul_tmul_smul]
        rfl
  -- The per-wire computational-basis coefficient of the phased-plus output on wire `i`:
  -- `invSqrt2 · (e^{iθ_i})^z`, so `c i 0 = invSqrt2` and `c i 1 = invSqrt2 · e^{iθ_i}`.
  set c : Fin (n + 1) → Fin 2 → ℂ := fun i z =>
    Concrete.invSqrt2 * Complex.exp ((qftTowerWirePhase n b i : ℂ) * Complex.I) ^ (z : ℕ)
    with hc_def
  have hc : ∀ i : Fin (n + 1),
      (qubitPhasePlus (qftTowerWirePhase n b i)).vec = ∑ z, c i z • (qubitBasis z).vec := by
    intro i
    rw [qubitPhasePlus_vec, Fin.sum_univ_two, hc_def]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
    rw [smul_add, smul_smul]
  apply PureState.ext
  rw [towerProd_vec_eq_sum n c (fun i => qubitPhasePlus (qftTowerWirePhase n b i)) hc,
    qftTowerEvolution_evolvePure_towerKet, qftEvolution_evolvePure_quditBasis,
    PureState.congr_vec, qftFourierImage_vec, map_sum]
  -- Re-index the register sum `∑ x` over wire bit-strings `k`, `x = enc (k ∘ rev)`, so the two
  -- `Fin.rev`s in the bridge dictionary and the wire indexing cancel and `x ↦ towerKet n k`.
  refine (Fintype.sum_equiv
    ((Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))).trans finFunctionFinEquiv)
    _ _ (fun k => ?_)).symm
  have hEk : ((Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))).trans finFunctionFinEquiv) k
      = finFunctionFinEquiv (fun i => k i.rev) := by
    rw [Equiv.trans_apply]
    congr 1
  rw [hEk, map_smul, ← PureState.congr_vec, quditPowTower_congr_quditBasis_apply]
  simp only [Fin.rev_rev]
  congr 1
  -- The scalar identity: the product of per-wire coefficients is the QFT's Fourier coefficient.
  simp only [hc_def, ← Complex.exp_natCast_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Complex.exp_sum]
  congr 1
  · -- The `(1/√2)ⁿ⁺¹` normalisation is the register `1/√(2ⁿ⁺¹)` (`Concrete.sqrt_two_pow`).
    rw [Concrete.invSqrt2, inv_pow, ← Complex.ofReal_pow, Nat.cast_pow, Nat.cast_ofNat,
      (Concrete.sqrt_two_pow (n + 1)).symm]
  · -- The wire phases sum to the Fourier phase `2π·J·K / 2ⁿ⁺¹` because the register index
    -- `K = ∑ᵢ kᵢ 2^{i.rev}` expands over the wires.
    congr 1
    have hK : (((finFunctionFinEquiv (fun i => k i.rev) : Fin (2 ^ (n + 1))) : ℕ) : ℂ)
        = ∑ i, ((k i : ℕ) : ℂ) * 2 ^ (i.rev : ℕ) := by
      rw [finFunctionFinEquiv_apply_val]
      push_cast
      exact Fintype.sum_equiv Fin.revPerm (fun l => ((k l.rev : ℕ) : ℂ) * 2 ^ (l : ℕ))
        (fun i => ((k i : ℕ) : ℂ) * 2 ^ (i.rev : ℕ)) (fun l => by simp [Fin.rev_rev])
    rw [hK, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [qftTowerWirePhase]
    push_cast
    ring

end AxQM
