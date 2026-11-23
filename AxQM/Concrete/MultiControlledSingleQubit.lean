/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SingleQubitWire
import AxQM.Concrete.MultiControlledNotGate

/-!
# Concrete: the multiply-controlled single-qubit gate `Cᵏ(Ũ)` (N&C §4.3 / Barenco)

The §4.3 reduction of a controlled single-qubit gate to `H, S, CNOT, Toffoli`, and in particular the
Barenco *no-work-qubit* `Cⁿ(X)` construction (Exercise 4.30 / Barenco *et al.* Lemma 7.5), express a
multiply-controlled gate as a product of *smaller* multiply-controlled gates whose controls are
proper **subsets** of the wires — for `Cⁿ(X) = Cⁿ(V²)` (with `V = √X`),

`Cⁿ(X) = C(V)·Cⁿ⁻¹(X)·C(V†)·Cⁿ⁻¹(X)·Cⁿ⁻¹(V)`,

whose factors are gates controlled on one wire (`C(V)`, `C(V†)`) and on `n − 1` wires
(`Cⁿ⁻¹(X)`, `Cⁿ⁻¹(V)`). The two existing matrix objects are the extremes of the control range:
`ctrlSingleQubit enc j 1 Ũ` is controlled on **every** wire but `j`, and `singleQubitOnWire enc j g`
is controlled on **no** wire. This file supplies the object that interpolates them — the
**subset-controlled single-qubit gate** every Barenco factor is an instance of.

## The construction

Fix an encoding `enc : (Fin m → Fin 2) ≃ Fin d`, a control set `S : Finset (Fin m)`, a target wire
`j`, and a `2 × 2` matrix `Ũ`:

* `AxQM.Concrete.mcCtrlSingleQubit enc S j Ũ` — on the basis state `|enc x⟩` it applies `Ũ`
  to bit `j` of `x` when **every control wire in `S` is `1`**, and fixes `|enc x⟩` otherwise. It is
  the fibrewise gate (`wireGate`) whose `2 × 2` block is `Ũ` on the fibres passing the control
  condition and the identity elsewhere.

## The algebra

Through the general fibrewise-gate lemmas (`wireGate_*`, incl. `wireGate_conjTranspose`, all in
`ControlledSingleQubit.lean`) it is a `*`-homomorphism in the block on a *fixed* control set `S`:

* `mcCtrlSingleQubit_one`, `mcCtrlSingleQubit_mul`, `mcCtrlSingleQubit_conjTranspose`
  — identity/product/adjoint respect the block, so a unitary block gives a unitary gate
  (`mcCtrlSingleQubit_mem_unitaryGroup`).
* `mcCtrlSingleQubit_mulVec_of_ctrl` / `mcCtrlSingleQubit_mulVec_of_not_ctrl` (for `j ∉ S`) — the
  controlled action: `Ũ`-mix the two active components when the controls are satisfied, fix the
  basis state otherwise.

It **interpolates** the two extreme gates:

* `mcCtrlSingleQubit_empty` — with no controls it is `singleQubitOnWire enc j Ũ`.
* `mcCtrlSingleQubit_univ_sdiff` — controlled on all wires but `j` it is the all-`1`-controlled gate
  `ctrlSingleQubit enc j 1 Ũ`.

## The permutation bridge for the `NOT` block

Its Pauli-`X` instance is a *classical reversible* gate — the permutation gate of the combinatorial
multiply-controlled `NOT`:

* `mcCtrlSingleQubit_pauliX_eq_permGate` (for `j ∉ S`) —
  `mcCtrlSingleQubit enc S j pauliX = permGate enc (mcNotPerm S j)`, generalising
  `ctrlSingleQubit_one_pauliX_eq_permGate` (its `S = univ \ {j}` case) to an arbitrary control set.
  This is exactly the bridge that carries every spare-wire `Cⁿ⁻¹(X)` sub-gate of the Barenco
  reduction into the combinatorial `Cⁿ(X)` circuit development (`Concrete/MultiControlledNot*`) —
  through `permGate`'s `*`-homomorphism — hence into a product of `Toffoli`/`CNOT`/`NOT` gates. Its
  entrywise heart is `ctrlSet_pauliX_entry` (in `Concrete/MultiControlledNotGate.lean`), the
  `S`-general form of `ctrlOne_pauliX_entry` — which the all-`1`-controlled special case now
  derives from, so the case analysis is written once.

## Use

These results are reused by the tight-register `Cⁿ(X)` reduction of Exercise 4.43
(`AxQM/NC/Ch4/Exercise4_43.lean`).
-/

open Matrix

namespace AxQM.Concrete

variable {m d : ℕ}

/-- **The multiply-controlled single-qubit gate** `Cᵏ(Ũ)` (`k = |S|`). Relative to an encoding
`enc : (Fin m → Fin 2) ≃ Fin d`, a control set `S`, a target wire `j`, and a `2 × 2` matrix `Ũ`, on
the basis state `|enc x⟩` it applies `Ũ` to bit `j` of `x` when every control wire in `S` is set to
`1`, and acts as the identity otherwise. It is the fibrewise gate whose block is `Ũ` on the
controlled fibres and `1` elsewhere — the object every factor of the Barenco `Cⁿ(X)` reduction is an
instance of. -/
def mcCtrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m)) (j : Fin m)
    (Ũ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  wireGate enc j (fun y => if ∀ k ∈ S, y k = 1 then Ũ else 1)

/-- On a control set `S` with `j ∉ S`, evaluating the control condition at the fibre representative
`(enc.symm i)[j ↦ v]` is the same as evaluating it at `enc.symm i`: bit `j` is not a control. -/
theorem ctrl_update_iff {S : Finset (Fin m)} {j : Fin m} (hj : j ∉ S) (x : Fin m → Fin 2)
    (v : Fin 2) : (∀ k ∈ S, Function.update x j v k = 1) ↔ (∀ k ∈ S, x k = 1) :=
  forall_congr' fun k => imp_congr_right fun hk => by
    have hkj : k ≠ j := fun h => hj (h ▸ hk)
    rw [Function.update_of_ne hkj]

/-- **The block algebra is multiplicative on a fixed control set**:
`mcCtrlSingleQubit enc S j P * mcCtrlSingleQubit enc S j Q = mcCtrlSingleQubit enc S j (P * Q)`. On
each fibre the control condition is fixed, so the two blocks (`if · then P else 1` and its `Q`
analogue) multiply to `if · then P*Q else 1`. -/
theorem mcCtrlSingleQubit_mul (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m)) (j : Fin m)
    (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    mcCtrlSingleQubit enc S j P * mcCtrlSingleQubit enc S j Q
      = mcCtrlSingleQubit enc S j (P * Q) := by
  rw [mcCtrlSingleQubit, mcCtrlSingleQubit, mcCtrlSingleQubit, wireGate_mul]
  congr 1
  funext y
  by_cases h : ∀ k ∈ S, y k = 1
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, mul_one]

/-- **The multiply-controlled gate of the identity block is the identity.** -/
theorem mcCtrlSingleQubit_one (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m)) (j : Fin m) :
    mcCtrlSingleQubit enc S j (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [mcCtrlSingleQubit]
  simp only [ite_self, wireGate_one]

/-- **The multiply-controlled gate commutes with the conjugate transpose**:
`(mcCtrlSingleQubit enc S j Ũ)ᴴ = mcCtrlSingleQubit enc S j Ũᴴ` (via `wireGate_conjTranspose`, using
`1ᴴ = 1`). -/
theorem mcCtrlSingleQubit_conjTranspose (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m))
    (j : Fin m) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    (mcCtrlSingleQubit enc S j Ũ)ᴴ = mcCtrlSingleQubit enc S j Ũᴴ := by
  rw [mcCtrlSingleQubit, mcCtrlSingleQubit, wireGate_conjTranspose]
  congr 1
  funext y
  simp only [apply_ite Matrix.conjTranspose, Matrix.conjTranspose_one]

/-- **A multiply-controlled single-qubit gate with unitary block is unitary.** Follows from the
`*`-homomorphism laws: `(C(Ũ))ᴴ · C(Ũ) = C(Ũᴴ · Ũ) = C(1) = 1`. -/
theorem mcCtrlSingleQubit_mem_unitaryGroup (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m))
    (j : Fin m) {Ũ : Matrix (Fin 2) (Fin 2) ℂ} (hŨ : Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    mcCtrlSingleQubit enc S j Ũ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hŨ ⊢
  rw [Matrix.star_eq_conjTranspose] at hŨ ⊢
  rw [mcCtrlSingleQubit_conjTranspose, mcCtrlSingleQubit_mul, hŨ, mcCtrlSingleQubit_one]

/-- **`mcCtrlSingleQubit enc S j` is continuous** in its `2 × 2` block: each matrix entry is either
the constant `0`, a constant entry of the identity, or a single continuous entry of `Ũ` (the control
condition and the fibre condition do not depend on `Ũ`). The continuity lemma for the whole
fibrewise family — every consumer that transports a closure/limit of `2 × 2` blocks through the
placement (e.g. the Deutsch-gate density transports, `Concrete/DeutschWirePlacement.lean`) cites
it. -/
theorem continuous_mcCtrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m))
    (j : Fin m) :
    Continuous (fun Ũ : Matrix (Fin 2) (Fin 2) ℂ => mcCtrlSingleQubit enc S j Ũ) := by
  apply continuous_matrix
  intro i i'
  simp only [mcCtrlSingleQubit, wireGate, Matrix.of_apply]
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const
  · exact continuous_const

/-- **No controls: the multiply-controlled gate is the uncontrolled single-qubit wire gate.**
`mcCtrlSingleQubit enc ∅ j Ũ = singleQubitOnWire enc j Ũ` — one endpoint of the control range. -/
theorem mcCtrlSingleQubit_empty (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    mcCtrlSingleQubit enc (∅ : Finset (Fin m)) j Ũ = singleQubitOnWire enc j Ũ := by
  rw [singleQubitOnWire_eq_wireGate, mcCtrlSingleQubit]
  congr 1
  funext y
  rw [ite_eq_left (by simp)]

/-- **Every wire but `j` a control: the multiply-controlled gate is the all-`1`-controlled gate.**
`mcCtrlSingleQubit enc (univ \ {j}) j Ũ = ctrlSingleQubit enc j 1 Ũ` — the other endpoint of the
control range. -/
theorem mcCtrlSingleQubit_univ_sdiff (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    mcCtrlSingleQubit enc (Finset.univ \ {j}) j Ũ = ctrlSingleQubit enc j 1 Ũ := by
  rw [ctrlSingleQubit_eq_wireGate, mcCtrlSingleQubit]
  congr 1
  funext y
  by_cases h : ∀ k ∈ Finset.univ \ {j}, y k = 1
  · rw [ite_eq_left h, ite_eq_left]
    intro k hk
    rw [Pi.one_apply]
    exact h k (by simp [hk])
  · rw [ite_eq_right h, ite_eq_right]
    intro hc
    exact h fun k hk => by
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hk
      simpa using hc k hk.2

/-- **The controlled action, controls satisfied.** When every control wire in `S` is `1`
(`j ∉ S`), the gate mixes only the two components differing in bit `j` through `Ũ`. -/
theorem mcCtrlSingleQubit_mulVec_of_ctrl (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)}
    {j : Fin m} (hj : j ∉ S) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin d → ℂ) (i : Fin d)
    (h : ∀ k ∈ S, enc.symm i k = 1) :
    (mcCtrlSingleQubit enc S j Ũ *ᵥ v) i =
      Ũ (enc.symm i j) 0 * v (enc (Function.update (enc.symm i) j 0))
        + Ũ (enc.symm i j) 1 * v (enc (Function.update (enc.symm i) j 1)) := by
  rw [mcCtrlSingleQubit, wireGate_mulVec, ite_eq_left ((ctrl_update_iff hj _ 0).mpr h)]

/-- **The controlled action, controls not satisfied.** When some control wire in `S` is `0`
(`j ∉ S`), the gate fixes the basis state `|enc x⟩` at `i`. -/
theorem mcCtrlSingleQubit_mulVec_of_not_ctrl (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)}
    {j : Fin m} (hj : j ∉ S) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin d → ℂ) (i : Fin d)
    (h : ¬ ∀ k ∈ S, enc.symm i k = 1) :
    (mcCtrlSingleQubit enc S j Ũ *ᵥ v) i = v i := by
  rw [mcCtrlSingleQubit, wireGate_mulVec,
      ite_eq_right (fun hup => h ((ctrl_update_iff hj _ 0).mp hup))]
  rcases (by omega : enc.symm i j = 0 ∨ enc.symm i j = 1) with ha | ha
  · have hself : Function.update (enc.symm i) j 0 = enc.symm i := by
      rw [← ha, Function.update_eq_self]
    rw [ha, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide), hself, Equiv.apply_symm_apply]
    ring
  · have hself : Function.update (enc.symm i) j 1 = enc.symm i := by
      rw [← ha, Function.update_eq_self]
    rw [ha, Matrix.one_apply_ne (by decide), Matrix.one_apply_eq, hself, Equiv.apply_symm_apply]
    ring

/-- Two distinct basis indices agreeing off wire `w` disagree at `w` — from injectivity of the
encoding equivalence `enc`. The single fact the diagonal/fibrewise gate lemmas use to discharge
their off-diagonal (`i ≠ i'`) entry. -/
theorem enc_symm_ne_of_off (enc : (Fin m → Fin 2) ≃ Fin d) {i i' : Fin d} {w : Fin m}
    (hii : i ≠ i') (hoff : ∀ k, k ≠ w → enc.symm i k = enc.symm i' k) :
    enc.symm i w ≠ enc.symm i' w := fun hw =>
  hii (enc.symm.injective (funext fun k => by
    rcases eq_or_ne k w with rfl | hk
    · exact hw
    · exact hoff k hk))

/-- **A subset-controlled diagonal single-qubit gate is diagonal.** For `j ∉ S`,
`mcCtrlSingleQubit enc S j (diagonal w)` multiplies `|enc x⟩` by `w (x_j)` when every control wire
in `S` is set and by `1` otherwise — the diagonal matrix
`diagonal (fun i => if ∀ k ∈ S, x_k = 1 then w (x_j) else 1)`. The general form of the diagonal
block; its global-phase special case is `mcCtrlSingleQubit_smul_one_eq_diagonal` (`z • 1`), and its
`Rₖ` instance makes the quantum-Fourier-transform circuit's conditional rotations simultaneously
diagonal (`Concrete/QftGateCircuitCorrectness.lean`). -/
theorem mcCtrlSingleQubit_diagonal (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)} {j : Fin m}
    (hj : j ∉ S) (w : Fin 2 → ℂ) :
    mcCtrlSingleQubit enc S j (Matrix.diagonal w)
      = Matrix.diagonal fun i => if ∀ k ∈ S, enc.symm i k = 1 then w (enc.symm i j) else 1 := by
  ext i i'
  rw [mcCtrlSingleQubit, wireGate_apply, Matrix.diagonal_apply]
  simp only [ctrl_update_iff hj]
  by_cases hii : i = i'
  · subst hii
    rw [ite_eq_left (fun k _ => rfl), ite_eq_left rfl]
    by_cases hC : ∀ k ∈ S, enc.symm i k = 1
    · rw [ite_eq_left hC, ite_eq_left hC, Matrix.diagonal_apply_eq]
    · rw [ite_eq_right hC, ite_eq_right hC, Matrix.one_apply_eq]
  · rw [ite_eq_right hii]
    by_cases hbits : ∀ k : Fin m, k ≠ j → enc.symm i k = enc.symm i' k
    · rw [ite_eq_left hbits]
      have hjne : enc.symm i j ≠ enc.symm i' j := enc_symm_ne_of_off enc hii hbits
      rw [apply_ite (fun M : Matrix (Fin 2) (Fin 2) ℂ => M (enc.symm i j) (enc.symm i' j)),
        Matrix.diagonal_apply_ne _ hjne, Matrix.one_apply_ne hjne, ite_self]
    · rw [ite_eq_right hbits]

/-- **The multiply-controlled `NOT` matrix is the permutation gate of the classical `mcNot`.**
For `j ∉ S`, `mcCtrlSingleQubit enc S j pauliX = permGate enc (mcNotPerm S j)`: the `S`-controlled
`X` gate (flip target wire `j` of `|enc x⟩` iff every control wire in `S` is `1`) realises, through
the encoding, the bit-string permutation `mcNot S j`. This generalises
`ctrlSingleQubit_one_pauliX_eq_permGate` (the `S = univ \ {j}` case) and is the bridge carrying a
spare-wire `Cⁿ⁻¹(X)` sub-gate of the Barenco reduction into the combinatorial `Cⁿ(X)` circuit
development. -/
theorem mcCtrlSingleQubit_pauliX_eq_permGate (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m))
    {j : Fin m} (hj : j ∉ S) :
    mcCtrlSingleQubit enc S j pauliX = permGate enc (mcNotPerm S hj) := by
  ext i i'
  have hcond : (i = enc (mcNot S j (enc.symm i'))) ↔ (enc.symm i = mcNot S j (enc.symm i')) := by
    rw [Equiv.symm_apply_eq]
  rw [mcCtrlSingleQubit, wireGate_apply, permGate_apply, mcNotPerm_apply]
  simp only [hcond, ctrl_update_iff hj (enc.symm i) 0,
    apply_ite (fun M : Matrix (Fin 2) (Fin 2) ℂ => M (enc.symm i j) (enc.symm i' j)),
    Matrix.one_apply]
  exact ctrlSet_pauliX_entry S hj (enc.symm i) (enc.symm i')

end AxQM.Concrete
