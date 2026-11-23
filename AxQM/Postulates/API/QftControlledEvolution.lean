/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditGate
import AxQM.Concrete.QftGateCircuitCorrectness
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# The Figure 5.1 controlled-`Rₖ` gate as an `Evolution`, and its basis action (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) reads the Figure 5.1 QFT circuit on the
`(n+1)`-qubit control tower `qtower n qubit` as a **product of wire-addressed tower gates**
(`qftTowerEvolution_eq_map_congr_prod`), so each transported Figure 5.1 gate must be re-expressed as
such a tower gate. The Figure 5.1 gates come in three shapes — the wire-reversal **swap** layer
(`QftSwapEvolution`), the **Hadamards** (`QftHadamardEvolution`), and the **controlled-`Rₖ`**
rotations, the circuit's only **two-wire** gate. This file supplies the register-side ingredient the
*controlled-`Rₖ`* re-expression needs: the conditional rotation as a named `Evolution` on the single
`2ⁿ`-level register, with its action on the computational basis computed.

Unlike the Hadamard — which sends a basis ket to a *superposition* — the controlled-`Rₖ` gate is
**diagonal** (`Rₖ = diag(1, e^{2πi/2ᵏ})`), so it sends a basis ket to a *phased* basis ket: it
multiplies `|f⟩` by the phase `e^{2πi/2ᵏ}` exactly when both the control wire `c` and the target
wire `t` carry a `1`, and fixes it otherwise. Its computational-basis action is therefore a single
scalar, not a two-term sum, and the tower re-expression (`AxQM/Core/QftTowerControlled.lean`)
matches it against the phase gate `phaseShiftGate (2π/2ᵏ)` placed on the target of the controlled
tower gate `Evolution.qtowerCtrlWire`.

## What is formalised

* `qftControlledEvolution n t c` — the **Figure 5.1 controlled-`Rₖ` gate from control wire `c` onto
  target wire `t` as an `Evolution`** on `qudit (2ⁿ)`: the `quditGate` promotion of the Concrete
  gate matrix `qftControlledGate n t c = mcCtrlSingleQubit finFunctionFinEquiv {c} t Rₖ`,
  `Rₖ = qftRk ((c-t)+1)` (the conditional rotation of `Concrete.qftGateSequence`). It is unitary (a
  controlled unitary block), so `quditGate` applies.
* `qftControlledEvolution_evolvePure_quditBasis` — its **computational-basis action** (for `t ≠ c`):
  the gate is diagonal, so it multiplies `|finFunctionFinEquiv f⟩` by the phase
  `[1, e^{2πi/2^{(c-t)+1}}]_{f t}` when the control bit `f c` is `1`, and fixes it otherwise:

    `qftControlledEvolution n t c |ff f⟩`
      `= (if f c = 1 then [1, e^{2πi/2ᵏ}]_{f t} else 1) • |ff f⟩`.

  Read off from `mcCtrlSingleQubit_diagonal` (the `Rₖ` block is `Matrix.diagonal ![1, e^{2πi/2ᵏ}]`
  via `qftRk_eq_diagonal`), the column action of `Matrix.toEuclideanCLM` on a standard basis vector,
  and the singleton control condition `∀ k ∈ {c}, f k = 1 ↔ f c = 1`. This is the register-side
  action the tower re-expression (`AxQM/Core/QftTowerControlled.lean`) reads through the register
  bridge `quditPowTower`.

-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **The Figure 5.1 controlled-`Rₖ` gate from control wire `c` onto target wire `t` as an
`Evolution`** on `qudit (2ⁿ)`: the `quditGate` promotion of the Concrete gate matrix
`qftControlledGate n t c = mcCtrlSingleQubit finFunctionFinEquiv {c} t (qftRk ((c-t)+1))` — the
conditional rotation `R_{(c-t)+1}` of `Concrete.qftGateSequence`, applying the phase `Rₖ` to wire
`t` when wire `c` is `|1⟩`. It is unitary (a controlled unitary block, `mcCtrlSingleQubit` of the
unitary `qftRk`), so `quditGate` applies. It is used in `AxQM/Core/QftTowerControlled.lean`; its
basis action is `qftControlledEvolution_evolvePure_quditBasis`. -/
def qftControlledEvolution (n : ℕ) (t c : Fin n) : Evolution (qudit (2 ^ n)) :=
  quditGate (mcCtrlSingleQubit_mem_unitaryGroup finFunctionFinEquiv {c} t
    (qftRk_mem_unitaryGroup ((c : ℕ) - (t : ℕ) + 1)))

/-- **The controlled-`Rₖ` gate multiplies a basis ket by a control-and-target phase.** For `t ≠ c`
(the control and target are distinct wires), the diagonal gate `qftControlledEvolution n t c` acts
on the computational-basis ket `|finFunctionFinEquiv f⟩` as

  `qftControlledEvolution n t c |ff f⟩
     = (if f c = 1 then ![1, e^{2πi/2^{(c-t)+1}}] (f t) else 1) • |ff f⟩`:

when the control bit `f c` is `1` it multiplies by the `Rₖ` diagonal entry `[1, e^{2πi/2ᵏ}]_{f t}`
(so by `e^{2πi/2ᵏ}` precisely when the target bit `f t` is also `1`), and otherwise fixes the ket.
Read off from `mcCtrlSingleQubit_diagonal` — the `Rₖ` block is `Matrix.diagonal ![1, e^{2πi/2ᵏ}]`
(`qftRk_eq_diagonal`), so the gate is `Matrix.diagonal` with entry
`if ∀ k ∈ {c}, f k = 1 then [1, e^{2πi/2ᵏ}]_{f t} else 1` at index `|ff f⟩` — through the column
action `Matrix.toEuclideanCLM_apply_single` and the singleton control condition
`∀ k ∈ {c}, f k = 1 ↔ f c = 1` (`Finset.forall_mem_singleton`). This is the register-side action the
tower re-expression reads through the register bridge `quditPowTower`; the two-wire structure
survives on the tower as `Evolution.qtowerCtrlWire`. -/
theorem qftControlledEvolution_evolvePure_quditBasis (n : ℕ) (t c : Fin n) (hne : t ≠ c)
    (f : Fin n → Fin 2) :
    ((qftControlledEvolution n t c).evolvePure (quditBasis (finFunctionFinEquiv f))).vec
      = (if f c = 1 then
          ![(1 : ℂ), Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1))] (f t)
        else 1) • (quditBasis (finFunctionFinEquiv f)).vec := by
  have hts : t ∉ ({c} : Finset (Fin n)) := by simpa using hne
  rw [Evolution.evolvePure_vec]
  simp only [qftControlledEvolution, quditGate_op, quditBasis_vec]
  rw [qftRk_eq_diagonal, mcCtrlSingleQubit_diagonal finFunctionFinEquiv hts]
  refine (Matrix.toEuclideanCLM_apply_single _ (finFunctionFinEquiv f)).trans ?_
  rw [Finset.sum_eq_single (finFunctionFinEquiv f)
      (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ hj, zero_smul])
      (fun h => absurd (Finset.mem_univ _) h),
    Matrix.diagonal_apply_eq]
  simp only [Equiv.symm_apply_apply]
  -- The singleton control condition `∀ k ∈ {c}, f k = 1` is just `f c = 1`; case-split so the two
  -- `ite`s match branch-by-branch (avoiding a `Decidable`-instance mismatch on the conditions).
  have hcond : (∀ k ∈ ({c} : Finset (Fin n)), f k = 1) ↔ f c = 1 := by
    simp only [Finset.mem_singleton, forall_eq]
  by_cases hc : f c = 1
  · rw [ite_eq_left (hcond.mpr hc), ite_eq_left hc]; rfl
  · rw [ite_eq_right (fun h => hc (hcond.mp h)), ite_eq_right hc]; rfl

end

end AxQM
