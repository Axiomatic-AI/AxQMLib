/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QftHadamardEvolution
import AxQM.Postulates.API.Qudit
import AxQM.Concrete.MultiControlledSingleQubitSpareReduction

/-!
# Single-qubit phase gates on a register wire

The phase layer `D = diagPhase θ` of the computable-phase-shift circuit (Nielsen & Chuang
Problem 4.1) is, in the textbook construction, **`n` single-qubit phase gates** — one on each wire
of the `n`-qubit ancilla register. This file supplies the register-side ingredient that makes that
gate count a genuine object: the single-qubit phase gate `P(φ) = diag(1, e^{iφ})` placed on one
wire of the `2ⁿ`-level register, as a named `Evolution (qudit (2ⁿ))`, together with its
computational-basis action.

* `phaseWireEvolution n t φ` — the phase gate `P(φ)` on wire `t` of `qudit (2ⁿ)`: the `quditGate`
  promotion of `Concrete.singleQubitOnWire finFunctionFinEquiv t (Concrete.phaseGate e^{iφ})`. The
  direct analogue of `rotZWireEvolution n t θ` with the `z`-rotation replaced by a **phase** gate;
  because a phase gate is diagonal, its wire embedding is diagonal in the computational basis, so
  its action carries **no** off-diagonal branch (unlike a rotation).
* `phaseWireEvolution_evolvePure_quditBasis` — its **diagonal basis action**
  `P(φ)ₜ |f⟩ = (e^{iφ})^{f t} · |f⟩`: the gate leaves the basis ket unchanged and multiplies it by
  the phase `e^{iφ}` exactly when wire `t` carries a `1`. This is the single-wire factor the
  phase-gradient decomposition of `diagPhase` (Problem 4.1's phase layer) is assembled from.

It reuses the single-wire-gate machinery of `AxQM/Postulates/API/FourGateReachableWire.lean`
(`rotZWireEvolution`) and `AxQM/Postulates/API/QftHadamardEvolution.lean`.
-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The single-qubit phase gate `P(φ) = diag(1, e^{iφ})` on a register wire.** Placed on wire
`t` of the `2ⁿ`-level register, as a named `Evolution (qudit (2ⁿ))`: the `quditGate` promotion of
the gate matrix `Concrete.singleQubitOnWire finFunctionFinEquiv t (Concrete.phaseGate e^{iφ})`
(unitary, since `|e^{iφ}| = 1`). The direct analogue of `rotZWireEvolution n t θ` with the
`z`-rotation block replaced by the phase gate `P(φ)`; its diagonal basis action is
`phaseWireEvolution_evolvePure_quditBasis`. This is the single-wire factor the phase layer of the
computable-phase-shift circuit (N&C Problem 4.1) is decomposed into. -/
def phaseWireEvolution (n : ℕ) (t : Fin n) (φ : ℝ) : Evolution (qudit (2 ^ n)) :=
  quditGate (singleQubitOnWire_mem_unitaryGroup finFunctionFinEquiv t
    (Concrete.phaseGate_exp_mem_unitaryGroup φ))

/-- **The wire-`t` phase gate acts diagonally, scaling by `e^{iφ}` when wire `t` is set.**
`phaseWireEvolution n t φ |finFunctionFinEquiv f⟩ = (e^{iφ})^{f t} · |finFunctionFinEquiv f⟩`:
the phase gate `P(φ)` on wire `t` leaves the computational-basis ket `|f⟩` unchanged and multiplies
it by `e^{iφ}` exactly when the wire-`t` bit `f t` is `1` (and by `1` when it is `0`). Because
`P(φ) = diag(1, e^{iφ})` is diagonal, the two-term column superposition of the general single-wire
bridge `quditGate_singleQubitOnWire_evolvePure_quditBasis` collapses to a single diagonal term. -/
theorem phaseWireEvolution_evolvePure_quditBasis (n : ℕ) (t : Fin n) (φ : ℝ) (f : Fin n → Fin 2) :
    ((phaseWireEvolution n t φ).evolvePure (quditBasis (finFunctionFinEquiv f))).vec
      = Complex.exp ((φ : ℂ) * Complex.I) ^ (f t : ℕ) •
          (quditBasis (finFunctionFinEquiv f)).vec := by
  rw [phaseWireEvolution,
    quditGate_singleQubitOnWire_evolvePure_quditBasis finFunctionFinEquiv t
      (Concrete.phaseGate_exp_mem_unitaryGroup φ) f,
    Fin.sum_univ_two]
  rcases (show f t = 0 ∨ f t = 1 by omega) with hft | hft <;>
  · have h : Function.update f t (f t) = f := Function.update_eq_self t f
    rw [hft] at h ⊢
    rw [h]
    simp only [Concrete.phaseGate, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.val_zero, Fin.val_one,
      pow_zero, pow_one]
    module

/-- **A product of single-wire phase gates acts by the product of the per-wire phases.** For any
list `l` of wires and per-wire angles `φ`, the composed circuit `∏_{t ∈ l} P(φ t)ₜ` scales the
computational-basis ket `|f⟩` by `∏_{t ∈ l} (e^{iφ t})^{f t}` — the phases of the wires carrying a
`1` multiply, leaving `|f⟩` fixed. This is the **phase-gradient** identity underlying Problem 4.1's
`n`-gate phase layer: each of the `n` single-qubit phase gates contributes one factor, and on the
ancilla index `f(x)` they multiply to the total computable phase. (`Evolution` is only a `Monoid`,
so the composed circuit is the `List.prod` over an ordering of the wires; the gates are diagonal and
so in fact commute.) Proved by induction on `l`: each factor is diagonal on `|f⟩`
(`phaseWireEvolution_evolvePure_quditBasis`), so it commutes past the accumulated scalar
(`map_smul`) and multiplies in its own phase. -/
theorem phaseWireEvolution_listProd_op_quditBasis (n : ℕ) (φ : Fin n → ℝ) (l : List (Fin n))
    (f : Fin n → Fin 2) :
    ((l.map (fun t => phaseWireEvolution n t (φ t))).prod).op
        (quditBasis (finFunctionFinEquiv f)).vec
      = (l.map (fun t => Complex.exp ((φ t : ℂ) * Complex.I) ^ (f t : ℕ))).prod •
          (quditBasis (finFunctionFinEquiv f)).vec := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, one_smul]; rfl
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Evolution.mul_def,
      Evolution.comp_op, ContinuousLinearMap.comp_apply, ih, map_smul, ← Evolution.evolvePure_vec,
      phaseWireEvolution_evolvePure_quditBasis, smul_smul, mul_comm]

/-- **The phase-gradient layer** `∏_{t<n} P(φ t)ₜ` — the composition of the `n` single-qubit phase
gates `P(φ t)` on wires `t = 0, …, n-1` of the `2ⁿ`-level register, in wire order. This is the
`n`-gate object the phase layer `D` of the computable-phase-shift circuit (Nielsen & Chuang
Problem 4.1) is built from: literally `n` single-qubit phase gates, one on each ancilla wire, so
the `n` of the exercise's `2T + n` gate count is exactly `phaseGradientLayer`'s factor count.
(`Evolution` is only a `Monoid`, so the layer is the `List.prod` over `List.finRange n`; the factors
are diagonal, hence commute, so the ordering is immaterial — recorded in
`phaseGradientLayer_op_apply_quditBasis`, which is symmetric in the wires.) -/
def phaseGradientLayer (n : ℕ) (φ : Fin n → ℝ) : Evolution (qudit (2 ^ n)) :=
  ((List.finRange n).map (fun t => phaseWireEvolution n t (φ t))).prod

/-- **The phase-gradient layer acts diagonally, by the product of the per-wire phases.**
`phaseGradientLayer n φ |f⟩ = (∏_{t} (e^{iφ t})^{f t}) · |f⟩`: the `n`-gate layer leaves the
computational-basis ket `|f⟩ = |finFunctionFinEquiv f⟩` fixed and scales it by the product of the
phases `e^{iφ t}` over exactly the wires `t` carrying a `1`. This is the `List.finRange n`
instance of the phase-gradient product law `phaseWireEvolution_listProd_op_quditBasis`, with the
list product rewritten as the (order-independent) `Finset` product `∏ t, …` over all wires. It is
the diagonal eigenvalue that identifies `phaseGradientLayer` with a `diagPhase` layer once the
per-wire angles are summed against the bit-decomposition of the index. -/
theorem phaseGradientLayer_op_apply_quditBasis (n : ℕ) (φ : Fin n → ℝ) (f : Fin n → Fin 2) :
    (phaseGradientLayer n φ).op (quditBasis (finFunctionFinEquiv f)).vec
      = (∏ t, Complex.exp ((φ t : ℂ) * Complex.I) ^ (f t : ℕ)) •
          (quditBasis (finFunctionFinEquiv f)).vec := by
  rw [phaseGradientLayer, phaseWireEvolution_listProd_op_quditBasis n φ (List.finRange n) f,
    ← List.ofFn_eq_map, List.prod_ofFn]

end

end AxQM
