/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditGate
import AxQM.Postulates.API.HadamardGate
import AxQM.Concrete.QftGateCircuit
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# The Figure 5.1 Hadamard layer as an `Evolution`, and its basis action (N&C Problem 5.2)

The whole-circuit measured-QFT reduction (Problem 5.2) reads the Figure 5.1 QFT circuit on the
`(n+1)`-qubit control tower `qtower n qubit` as a **product of wire-addressed tower gates**
(`qftTowerEvolution_eq_map_congr_prod`), so each transported Figure 5.1 gate must be re-expressed as
such a tower gate. The Figure 5.1 gates come in three shapes — the wire-reversal **swap** layer
(`QftSwapEvolution`), the **Hadamards**, and the **controlled-`Rₖ`** gates. This file supplies the
register-side ingredients the *Hadamard* re-expression needs: the Hadamard on a wire as a named
`Evolution` on the single `2ⁿ`-level register, with its action on the computational basis computed.

Unlike the swap — a basis-permutation gate (basis ket ↦ basis ket) — the Hadamard maps a basis ket
to a **superposition** of two basis kets (the wire is put into `|±⟩`), so its computational-basis
action is a genuine two-term sum, and the tower re-expression (`AxQM/Core/QftTowerHadamard.lean`)
matches it through the tensor multilinearity of the tower product state.

## What is formalised

* `quditGate_singleQubitOnWire_evolvePure_quditBasis` — a **reusable bridge**: the `quditGate`
  promotion of a single-qubit-on-wire gate `singleQubitOnWire enc t G` (an arbitrary one-qubit
  matrix `G` on wire `t`) acts on the computational basis ket `|enc f⟩` as the two-term
  wire-`t`-column superposition

    `quditGate (singleQubitOnWire enc t G) |enc f⟩ = ∑_{z} G z (f t) · |enc (update f t z)⟩`.

  The single-qubit-gate analogue of the permutation bridge
  `quditGate_permGate_evolvePure_quditBasis` (`QftSwapEvolution`): from the column action of
  `Matrix.toEuclideanCLM` on a standard basis vector (`Matrix.toEuclideanCLM_apply_single`) and the
  entry form of `singleQubitOnWire` (`singleQubitOnWire_apply`) — the `enc f`-column of the gate
  is supported on exactly the two rows `enc (Function.update f t z)`, `z : Fin 2`, with value
  `G z (f t)`. Reused by every Figure 5.1 single-qubit wire gate — here the Hadamard layer
  `qftHadamardEvolution`.
* `qftHadamardEvolution n t` — the **Figure 5.1 Hadamard on wire `t` as an `Evolution`** on
  `qudit (2ⁿ)`: the `quditGate` promotion of the Concrete gate matrix
  `qftHadamardGate n t = singleQubitOnWire finFunctionFinEquiv t hadamardC` (the block-opening gate
  of `qftGateSequence`).
* `qftHadamardEvolution_evolvePure_quditBasis` — its **computational-basis action**: it puts wire
  `t` into `|±⟩`, `qftHadamardEvolution n t |finFunctionFinEquiv f⟩ = ∑_z hadamardC z (f t) ·
  |finFunctionFinEquiv (update f t z)⟩`. The instance of the reusable bridge at `G = hadamardC`,
  `enc = finFunctionFinEquiv`. This is the register-side action the tower re-expression
  (`AxQM/Core/QftTowerHadamard.lean`) reads through the register bridge.
* `hadamardGate_evolvePure_qubitBasis_sum` — the **single-qubit companion**: the qubit Hadamard
  `hadamardGate` acts on a computational-basis state `|z⟩` as its Hadamard-matrix column,
  `hadamardGate |z⟩ = ∑_w hadamardC w z · |w⟩` — the `d = 2` case of the same column action. This
  is the single-wire factor the tower re-expression matches the register two-term superposition
  against.

-/

open Matrix

namespace AxQM

noncomputable section

open AxQM.Concrete

/-- **A `quditGate`-promoted single-qubit wire gate acts on the computational basis as a two-term
column superposition.** For an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of the bit-strings, a wire
`t`, and a one-qubit matrix `G`, the gate `quditGate (singleQubitOnWire enc t G)` sends the basis
ket `|enc f⟩` to `∑_{z : Fin 2} G z (f t) · |enc (Function.update f t z)⟩` — it mixes only the two
basis states that agree with `f` off wire `t`, through the column `(G · , f t)` of `G`. The
single-qubit analogue of the permutation bridge `quditGate_permGate_evolvePure_quditBasis`: proved
from the column action of `Matrix.toEuclideanCLM` on a standard basis vector
(`Matrix.toEuclideanCLM_apply_single`) and the entry form `singleQubitOnWire_apply` — the `enc
f`-column is supported on exactly the two rows `enc (Function.update f t z)` (`z : Fin 2`), with
value `G z (f t)`. Reused by every Figure 5.1 single-qubit wire gate. -/
theorem quditGate_singleQubitOnWire_evolvePure_quditBasis {m d : ℕ} [NeZero d]
    (enc : (Fin m → Fin 2) ≃ Fin d) (t : Fin m) {G : Matrix (Fin 2) (Fin 2) ℂ}
    (hG : G ∈ Matrix.unitaryGroup (Fin 2) ℂ) (f : Fin m → Fin 2) :
    ((quditGate (singleQubitOnWire_mem_unitaryGroup enc t hG)).evolvePure
        (quditBasis (enc f))).vec
      = ∑ z : Fin 2, G z (f t) • (quditBasis (enc (Function.update f t z))).vec := by
  rw [Evolution.evolvePure_vec, quditGate_op, quditBasis_vec]
  refine (Matrix.toEuclideanCLM_apply_single (singleQubitOnWire enc t G) (enc f)).trans ?_
  simp only [quditBasis_vec]
  -- The `enc f`-column of `singleQubitOnWire enc t G` vanishes off the two rows
  -- `enc (update f t z)`, `z : Fin 2`; restrict the full sum to that image, then simplify entries.
  have hsupp : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      k ∉ Finset.image (fun z : Fin 2 => enc (Function.update f t z)) Finset.univ →
      singleQubitOnWire enc t G k (enc f) •
        (EuclideanSpace.single k 1 : EuclideanSpace ℂ (Fin d)) = 0 := by
    intro k _ hk
    have hne : ¬ ∀ j, j ≠ t → enc.symm k j = enc.symm (enc f) j := by
      intro hagree
      refine hk (Finset.mem_image.2 ⟨enc.symm k t, Finset.mem_univ _, ?_⟩)
      have hu : Function.update f t (enc.symm k t) = enc.symm k := by
        funext j
        rcases eq_or_ne j t with rfl | hj
        · rw [Function.update_self]
        · have := hagree j hj
          rw [Equiv.symm_apply_apply] at this
          rw [Function.update_of_ne hj, this]
      rw [hu, Equiv.apply_symm_apply]
    rw [singleQubitOnWire_apply, ite_eq_right hne, zero_smul]
  rw [← Finset.sum_subset (Finset.subset_univ _) hsupp,
    Finset.sum_image (by
      intro a _ b _ hab
      have := congrArg (fun x => enc.symm x t) hab
      simpa [Equiv.symm_apply_apply, Function.update_self] using this)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1
  rw [singleQubitOnWire_apply, ite_eq_left]
  · simp only [Equiv.symm_apply_apply, Function.update_self]
  · intro j hj
    simp only [Equiv.symm_apply_apply, Function.update_of_ne hj]

/-- **The Figure 5.1 Hadamard on wire `t` as an `Evolution`** on `qudit (2ⁿ)`: the `quditGate`
promotion of the Concrete gate matrix
`qftHadamardGate n t = singleQubitOnWire finFunctionFinEquiv t hadamardC` — the parameter-free
block-opening gate of `Concrete.qftGateSequence`. It is unitary (a single-qubit wire gate with the
unitary Hadamard block), so `quditGate` applies. It is used in `AxQM/Core/QftTowerHadamard.lean`;
its basis action is `qftHadamardEvolution_evolvePure_quditBasis`. -/
def qftHadamardEvolution (n : ℕ) (t : Fin n) : Evolution (qudit (2 ^ n)) :=
  quditGate (singleQubitOnWire_mem_unitaryGroup finFunctionFinEquiv t hadamardC_mem_unitaryGroup)

/-- **The Hadamard layer puts wire `t` into `|±⟩`.**
`qftHadamardEvolution n t |finFunctionFinEquiv f⟩ = ∑_z hadamardC z (f t) · |finFunctionFinEquiv
(Function.update f t z)⟩`: the bit-string `f` addressing the wires has its wire-`t` component
replaced by the Hadamard superposition, the two branches carrying amplitudes `hadamardC z (f t)`.
The instance of the reusable bridge `quditGate_singleQubitOnWire_evolvePure_quditBasis` at
`G = hadamardC`, `enc = finFunctionFinEquiv`. This is the register-side action the tower
re-expression reads through the register bridge `quditPowTower`. -/
theorem qftHadamardEvolution_evolvePure_quditBasis (n : ℕ) (t : Fin n) (f : Fin n → Fin 2) :
    ((qftHadamardEvolution n t).evolvePure (quditBasis (finFunctionFinEquiv f))).vec
      = ∑ z : Fin 2, hadamardC z (f t) •
          (quditBasis (finFunctionFinEquiv (Function.update f t z))).vec :=
  quditGate_singleQubitOnWire_evolvePure_quditBasis finFunctionFinEquiv t
    hadamardC_mem_unitaryGroup f

/-- **The qubit Hadamard acts as its matrix column.** On a computational-basis state `|z⟩` the
one-qubit Hadamard gate `hadamardGate` produces the superposition `∑_w hadamardC w z · |w⟩`, i.e.
`|±⟩` for `z = 0, 1`. The `d = 2` case of the column action `Matrix.toEuclideanCLM_apply_single`,
read through `hadamardGate_op` and `qubitBasis_vec`. This is the single-wire factor the tower
re-expression of the Figure 5.1 Hadamard (`Core/QftTowerHadamard`) matches the register two-term
superposition `qftHadamardEvolution_evolvePure_quditBasis` against. -/
theorem hadamardGate_evolvePure_qubitBasis_sum (z : Fin 2) :
    (hadamardGate.evolvePure (qubitBasis z)).vec
      = ∑ w : Fin 2, hadamardC w z • (qubitBasis w).vec := by
  rw [Evolution.evolvePure_vec, hadamardGate_op, qubitBasis_vec]
  refine (Matrix.toEuclideanCLM_apply_single hadamardC z).trans (Finset.sum_congr rfl fun w _ => ?_)
  exact congrArg (hadamardC w z • ·) (qubitBasis_vec w).symm

end

end AxQM
