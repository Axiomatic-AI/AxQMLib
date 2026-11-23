/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QftControlledEvolution
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Core.EvolutionTowerBasisExt
import AxQM.Core.QtowerCtrlWireGate

/-!
# The QFT controlled-`Rₖ` gate re-expressed as a controlled single-wire gate on the tower (N&C
Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) reads the Figure 5.1 QFT circuit on the
`(n+1)`-qubit control tower `qtower n qubit` as a product of *transported* Figure 5.1 gates
(`qftTowerEvolution_eq_map_congr_prod`). To defer the terminal per-wire measurement
past that product gate by gate, each transported gate must be re-expressed as an honest
**wire-addressed tower `Evolution`**. This file does so for a Figure 5.1 **controlled-`Rₖ`**
rotation — the last of the circuit's three gate shapes, and its only **two-wire** gate (the swap
layer is done in `QftTowerSwap`, the Hadamards in `QftTowerHadamard`).

## What is formalised

* `quditPowTower_congr_qftControlledEvolution` — **the transported Figure 5.1 controlled-`Rₖ` from
  control wire `c` onto target wire `t` (`t < c`) is the controlled single-wire phase gate on the
  tower wire pair `(c.rev, t.rev)`.** Transporting the register controlled-`Rₖ` gate
  `qftControlledEvolution (n+1) t c` (`Postulates/API`) onto the tower through the register bridge
  `quditPowTower n` equals the controlled single-wire gate that applies the one-qubit phase gate
  `P(2π/2^{(c-t)+1})` to tower wire `t.rev` gated on tower wire `c.rev`:

    `Evolution.congr (quditPowTower n) (qftControlledEvolution (n+1) t c)`
      `= Evolution.qtowerCtrlWire n c.rev t.rev (phaseShiftGate (2π/2^{(c-t)+1}))`.

  So the QFT circuit's conditional rotation — a two-wire gate — is, on the grounded control tower,
  precisely a **controlled one-qubit phase gate** touching only the two wires `c.rev` (control) and
  `t.rev` (target). The QFT drives target `t` from the *later* wires `c > t`, and the register
  bridge reverses the wire order (`Fin.rev`), so on the tower the control lands *above* its target,
  `c.rev < t.rev` — exactly the configuration `Evolution.qtowerCtrlWire` is built for. After
  deferring the terminal measurement of the control wire this becomes a classically-controlled
  single-wire gate (the per-gate reduction), so the two-wire gate leaves the tower.

## Proof

Via the transported-gate re-expression combinator `quditPowTower_congr_eq_of_evolvePure_towerKet`:
it suffices to check, for every bit-string `b`, that the controlled tower gate
sends `towerKet n b` to the transport of the register gate's action on
`|finFunctionFinEquiv (b ∘ Fin.rev)⟩`. Both gates are **diagonal** (unlike the Hadamard), so both
sides reduce to a phase times `towerKet n b`; the phase agrees branch by branch on the control bit
`b c.rev`:

* the left side: `qtowerCtrlWire_evolvePure_towerKet` (`c.rev < t.rev`, via `Fin.rev_lt_rev`) fires
  `phaseShiftGate φ` on wire `t.rev` when `b c.rev = 1`, and the scalar multilinearity of the tower
  product state in wire `t.rev` (the inline `smul_update`) pulls the phase gate's eigenvalue
  `[1, e^{iφ}]_{b t.rev}` (`phaseShiftGate_op_apply_qubitBasis`) out of the product, leaving
  `towerKet n b`;
* the right side: `qftControlledEvolution_evolvePure_quditBasis` gives the register phase
  `[1, e^{2πi/2ᵏ}]_{b t.rev}` when `b c.rev = 1`, whose transport is pushed through the bridge
  isometry (`map_smul`) and read by the binary-expansion dictionary
  `quditPowTower_congr_quditBasis_apply` — the `Fin.rev`s aligning the wire orderings, collapsing by
  `Fin.rev_rev`.

The two phases agree because `e^{iφ} = e^{2πi/2ᵏ}` for `φ = 2π/2ᵏ` (a cast identity, `hphase`).

The controlled-`Rₖ` gate and its basis action are in
`AxQM/Postulates/API/QftControlledEvolution.lean`; the tower gates used are in `QtowerCtrlWireGate`
and `EvolutionTowerBasisExt`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **The transported Figure 5.1 controlled-`Rₖ` is the controlled single-wire phase gate on the
tower.** For `t < c` (the QFT drives target `t` from a later control wire `c`), transporting the
register controlled-`Rₖ` gate `qftControlledEvolution (n+1) t c` from the `2ⁿ⁺¹`-level register onto
the `(n+1)`-qubit control tower via the register bridge `quditPowTower n` yields exactly the
controlled single-wire gate applying the one-qubit phase gate `P(2π/2^{(c-t)+1})` to tower wire
`t.rev` gated on tower wire `c.rev`,

  `Evolution.congr (quditPowTower n) (qftControlledEvolution (n+1) t c)`
    `= Evolution.qtowerCtrlWire n c.rev t.rev (phaseShiftGate (2π/2^{(c-t)+1}))`.

This re-expresses the QFT circuit's only two-wire gate as an honest wire-addressed tower gate — a
controlled one-qubit phase gate on the wire pair `(c.rev, t.rev)`, `c.rev < t.rev` after the
register bridge's `Fin.rev`, touching no other wire — the third of the three Figure 5.1 gate shapes
the whole-circuit measured-QFT reduction (Problem 5.2) defers the terminal measurement past. Proved
through the combinator `quditPowTower_congr_eq_of_evolvePure_towerKet`: both gates are diagonal, so
the controlled tower gate (via `qtowerCtrlWire_evolvePure_towerKet` and the inline scalar
multilinearity `smul_update` of the tower product state in one wire) and the transported register
gate (via
`qftControlledEvolution_evolvePure_quditBasis`, the bridge isometry, and the dictionary
`quditPowTower_congr_quditBasis_apply`) send `towerKet n b` to the same phased basis state, the
phases agreeing by `e^{iφ} = e^{2πi/2ᵏ}`. -/
theorem quditPowTower_congr_qftControlledEvolution (n : ℕ) (t c : Fin (n + 1)) (htc : t < c) :
    Evolution.congr (quditPowTower n) (qftControlledEvolution (n + 1) t c)
      = Evolution.qtowerCtrlWire n c.rev t.rev
          (phaseShiftGate (2 * Real.pi / 2 ^ ((c : ℕ) - (t : ℕ) + 1))) := by
  set φ : ℝ := 2 * Real.pi / 2 ^ ((c : ℕ) - (t : ℕ) + 1) with hφ
  have hrev : c.rev < t.rev := Fin.rev_lt_rev.mpr htc
  have hne : t ≠ c := ne_of_lt htc
  -- Scalar multilinearity of the tower product state in one wire: pulling a wire's phase out of the
  -- product. The single-scalar companion of the Hadamard re-expression's two-term multilinearity.
  have smul_update : ∀ (N : ℕ) (ψ : Fin (N + 1) → PureState qubit) (i : Fin (N + 1)) (z : ℂ)
      (ρ χ : PureState qubit), χ.vec = z • ρ.vec →
      (towerProd N (Function.update ψ i χ)).vec
        = z • (towerProd N (Function.update ψ i ρ)).vec := by
    intro N
    induction N with
    | zero =>
        intro ψ i z ρ χ h
        obtain rfl := Fin.fin_one_eq_zero i
        simp only [towerProd_zero, Function.update_self]
        exact h
    | succ N ih =>
        intro ψ i z ρ χ h
        refine Fin.cases ?_ ?_ i
        · rw [towerProd_succ, Function.update_self, Fin.tail_update_zero, PureState.tmul_vec, h,
            towerProd_succ, Function.update_self, Fin.tail_update_zero, PureState.tmul_vec]
          exact (TensorProduct.smul_tmul' z ρ.vec _).symm
        · intro i'
          rw [towerProd_succ, Function.update_of_ne (Fin.succ_ne_zero i').symm,
            Fin.tail_update_succ, PureState.tmul_vec, ih (Fin.tail ψ) i' z ρ χ h, towerProd_succ,
            Function.update_of_ne (Fin.succ_ne_zero i').symm, Fin.tail_update_succ,
            PureState.tmul_vec]
          exact TensorProduct.tmul_smul z (ψ 0).vec _
  -- Phase identification `e^{iφ} = e^{2πi/2ᵏ}` for `φ = 2π/2ᵏ`.
  have hphase : Complex.exp ((φ : ℂ) * Complex.I)
      = Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) := by
    rw [hφ]; congr 1; push_cast; ring
  apply quditPowTower_congr_eq_of_evolvePure_towerKet
  intro b
  apply PureState.ext
  rw [qtowerCtrlWire_evolvePure_towerKet n c.rev t.rev hrev _ b, PureState.congr_vec,
    qftControlledEvolution_evolvePure_quditBasis (n + 1) t c hne (fun i => b i.rev)]
  by_cases hbc : b c.rev = 1
  · -- Control wire is `|1⟩`: both sides carry the phase on the target wire.
    rw [ite_eq_left hbc, ite_eq_left hbc]
    have hz : ((phaseShiftGate φ).evolvePure (qubitBasis (b t.rev))).vec
        = ![(1 : ℂ), Complex.exp ((φ : ℂ) * Complex.I)] (b t.rev) • (qubitBasis (b t.rev)).vec := by
      rw [Evolution.evolvePure_vec, phaseShiftGate_op_apply_qubitBasis]
    have hupd : Function.update (fun j => qubitBasis (b j)) t.rev (qubitBasis (b t.rev))
        = fun j => qubitBasis (b j) :=
      Function.update_eq_self t.rev _
    rw [smul_update n (fun j => qubitBasis (b j)) t.rev _ (qubitBasis (b t.rev)) _ hz,
      hupd, ← towerKet_eq_towerProd, map_smul, ← PureState.congr_vec,
      quditPowTower_congr_quditBasis_apply, hphase]
    simp only [Fin.rev_rev]
  · -- Control wire is `|0⟩`: both sides are the untouched basis state.
    rw [ite_eq_right hbc, ite_eq_right hbc, one_smul, ← PureState.congr_vec,
      quditPowTower_congr_quditBasis_apply]
    simp only [Fin.rev_rev]

end AxQM
