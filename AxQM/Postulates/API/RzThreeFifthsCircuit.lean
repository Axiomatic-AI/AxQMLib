/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.AxisAngleGateValues
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Postulates.API.CnotRotationCommutation

/-!
# AxQM.Postulates.API — the Figure 4.17 measurement-based `R_z(θ)` circuit

The circuit of Nielsen & Chuang's Exercise 4.41: a three-qubit circuit with two
ancilla (control) qubits and one target qubit that, conditioned on both ancillas being measured
`0`, applies the `z`-rotation `R_z(θ)` with `cos θ = 3/5` to the target — and applies `Z` to the
target on every other measurement outcome.

```
|0⟩ ─── H ───●─────────●─── H ───⊙   (measure ancilla 1)
             │         │
|0⟩ ─── H ───●─────────●─── H ───⊙   (measure ancilla 2)
             │         │
|ψ⟩ ─────────⊕─── S ───⊕──────────
```

The two `●─●─⊕` columns are Toffoli gates `C²(X)` (controls = the two ancillas, target = qubit 3),
and `S` is the phase gate on the target.

## What this file establishes (Exercise 4.41)

Feeding the target a computational basis state `|t⟩` keeps all three qubits in the computational
basis throughout (`X`, `S` only permute / phase basis states), which reduces the whole circuit to a
finite computation. This file sets up that computation:

* The circuit as a genuine unitary `Evolution` (`rzThreeFifthsCircuit`), split into the named
  sub-gates `rzThreeFifthsHadamards` (`H ⊗ H ⊗ 1`) and `rzThreeFifthsMiddle` (`T · (1⊗1⊗S) · T`).
* Reusable computational-basis truth tables for the constituent gates: `sGate_op_apply_qubitBasis`
  (`S|i⟩ = iⁱ|i⟩`) and `sThird_op_qubitBasis_vec` (`S` on the third wire, scalar in front); the
  Toffoli truth table at the `op` level is `toffoliGate_op_qubitBasis_vec`, in
  `AxQM/Postulates/API/ControlledControlledUnitary.lean` beside `toffoliGate`.
* **The key structural fact** — `rzThreeFifthsMiddle_evolvePure_qubitBasis_vec` (and its `op` form):
  the middle gate `T · (1⊗1⊗S) · T` is **diagonal in the ancilla-computational basis**, multiplying
  `|a⟩ ⊗ |b⟩ ⊗ |t⟩` by the scalar `iᵗ⁺ᵃᵇ`. The target returns to `|t⟩` because the two Toffolis
  cancel (`(t ⊕ ab) ⊕ ab = t`), and the intervening `S` contributes the phase `i^{t+ab}` (evaluated
  on `|t ⊕ ab⟩`). This diagonalisation is the physical heart of why the interference at the output
  Hadamards yields `cos θ = 3/5`.
* `rzThreeFifthsHadamards_evolvePure_ketZeroZero` — the input Hadamards prepare `|+⟩ ⊗ |+⟩` on the
  ancillas.

## The readings

With the full four-branch action `rzThreeFifthsCircuit(|0,0,t⟩) = ∑_{a',b'} rzThreeFifthsAmp a' b' t
· |a',b',t⟩` in hand, this file reads off Nielsen & Chuang's two claims about the circuit:

* `rzThreeFifthsAmp_apply` — the explicit `4×2` amplitude table, obtained by the finite `iᵗ⁺ᵃᵇ`
  interference sum. The success (`a'=b'=0`) column is `(3+i)/4, (1+3i)/4`; every failure column is
  `± (1-i)/4` up to a sign, `(-1)ᵗ`-alternating.
* `rzThreeFifthsCircuit_success_eq_rotZ` — **on both ancillas measured `0`, the circuit applies
  `R_z(θ)`.** The success (Kraus) operator `M₀₀ : |t⟩ ↦ rzThreeFifthsAmp 0 0 t · |t⟩` equals
  `c · R_z(rzThreeFifthsAngle)` for a scalar `c` with `‖c‖² = 5/8`, where
  `cos rzThreeFifthsAngle = 3/5` (`rzThreeFifthsAngle_cos`). Since `R_z` is unitary, `‖c‖² = 5/8` is
  the (input-independent) probability of the `00` outcome — Nielsen & Chuang's `5/8`.
* `rzThreeFifthsCircuit_failure_eq_pauliZ` — **on any other outcome, the circuit applies `Z`.** Each
  non-`(0,0)` branch operator equals `c · Z` for a scalar with `‖c‖² = 1/8` (so the three failure
  branches carry the complementary `3/8`).

The angle `θ` is pinned to `rzThreeFifthsAngle := arccos (3/5)` (giving `e^{iθ} = (3+4i)/5`, the
ratio of the two `M₀₀` eigenvalues); `c` is left existential because its phase is a
physically-irrelevant global phase and only its magnitude `‖c‖² = 5/8` (the Born probability)
carries content.

## Not formalised here

The statement of Exercise 4.41 (success `= R_z(θ)` and failure `= Z`) is in
`AxQM/NC/Ch4/Exercise4_41.lean`. The book's closing remark (repeated use of the
circuit with `Z = S²` corrections applies `R_z(θ)` with probability approaching `1`) is an informal
repeat-until-success protocol, not a single formalisable proposition, and is not formalised.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **The `S` (phase) gate on a computational basis state:** `S|i⟩ = iⁱ |i⟩`, i.e. `|0⟩` is fixed
and `|1⟩` is multiplied by `i` (`S = diag(1, i)`). -/
theorem sGate_op_apply_qubitBasis (i : Fin 2) :
    sGate.op (qubitBasis i).vec = Complex.I ^ (i : ℕ) • (qubitBasis i).vec := by
  rw [sGate_op, qubitBasis_vec]
  have hof : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) Concrete.sMatrix)
        (EuclideanSpace.single i 1)).ofLp
      = (Complex.I ^ (i : ℕ) • (EuclideanSpace.single i 1 : EuclideanSpace ℂ (Fin 2))).ofLp := by
    rw [Matrix.ofLp_toEuclideanCLM]
    funext j
    fin_cases i <;> fin_cases j <;>
      simp [Concrete.sMatrix, Matrix.mulVec, dotProduct, EuclideanSpace.single]
  exact (WithLp.equiv 2 (Fin 2 → ℂ)).injective hof

/-- **The phase gate `S` on the third (target) qubit** multiplies a computational basis state by
`iᶜ` (`c` = the third-qubit index): `(1⊗1⊗S)|a,b,c⟩ = iᶜ |a,b,c⟩`. The scalar sits in front of the
whole three-qubit vector, so it passes cleanly through the subsequent Toffoli. Mirrors the
library's `phase3_op` for `phaseShiftGate`. -/
theorem sThird_op_qubitBasis_vec (a b c : Fin 2) :
    ((sGate.onRight qubit).onRight qubit).op
        ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis c))).vec
      = Complex.I ^ (c : ℕ) • ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis c))).vec := by
  rw [← Evolution.evolvePure_vec, Evolution.onRight_evolvePure, Evolution.onRight_evolvePure]
  simp only [PureState.tmul_vec, Evolution.evolvePure_vec, sGate_op_apply_qubitBasis,
    TensorProduct.tmul_smul]
  exact TensorProduct.tmul_smul _ _ _

/-- **`H` on each ancilla:** the gate `H ⊗ H ⊗ 1` on `qubit ⊗ (qubit ⊗ qubit)` — a Hadamard on
each of the two control (ancilla) qubits, identity on the target. -/
def rzThreeFifthsHadamards : Evolution (qubit.compose (qubit.compose qubit)) :=
  hadamardGate.tmul (hadamardGate.onLeft qubit)

/-- **The middle gate `T · (1⊗1⊗S) · T`:** two Toffoli gates (controls = the ancillas, target =
qubit 3) sandwiching the phase gate `S` on the target. -/
def rzThreeFifthsMiddle : Evolution (qubit.compose (qubit.compose qubit)) :=
  toffoliGate.comp (((sGate.onRight qubit).onRight qubit).comp toffoliGate)

/-- **The Figure 4.17 circuit** `(H⊗H) · T · (1⊗1⊗S) · T · (H⊗H)` on `qubit ⊗ (qubit ⊗ qubit)`:
two ancilla (control) qubits and one target, Hadamards on the ancillas at both ends. -/
def rzThreeFifthsCircuit : Evolution (qubit.compose (qubit.compose qubit)) :=
  rzThreeFifthsHadamards.comp (rzThreeFifthsMiddle.comp rzThreeFifthsHadamards)

/-- **The middle gate is diagonal in the ancilla-computational basis:**
`T · (1⊗1⊗S) · T` sends `|a⟩ ⊗ |b⟩ ⊗ |t⟩` to `i^{t + ab} · |a⟩ ⊗ |b⟩ ⊗ |t⟩`. The target returns
to `|t⟩` because the two Toffolis cancel (`(t ⊕ ab) ⊕ ab = t`), and the middle `S` contributes the
phase `i^{t + ab}` (evaluated on `|t ⊕ ab⟩`). -/
theorem rzThreeFifthsMiddle_evolvePure_qubitBasis_vec (a b t : Fin 2) :
    (rzThreeFifthsMiddle.evolvePure ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis t)))).vec
      = Complex.I ^ ((t + a * b : Fin 2) : ℕ)
        • ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis t))).vec := by
  rw [Evolution.evolvePure_vec, rzThreeFifthsMiddle]
  simp only [Evolution.comp_op, ContinuousLinearMap.comp_apply]
  rw [toffoliGate_op_qubitBasis_vec, sThird_op_qubitBasis_vec, map_smul,
    toffoliGate_op_qubitBasis_vec,
    show (t + a * b) + a * b = t by fin_cases a <;> fin_cases b <;> fin_cases t <;> rfl]

/-- **The middle gate is diagonal in the ancilla-computational basis** (`Evolution.op` form):
`(T · (1⊗1⊗S) · T)|a,b,t⟩ = i^{t+ab} |a,b,t⟩`.  The `.op`-on-`.vec` restatement of
`rzThreeFifthsMiddle_evolvePure_qubitBasis_vec`, for use inside operator-level computations. -/
theorem rzThreeFifthsMiddle_op_qubitBasis_vec (a b t : Fin 2) :
    rzThreeFifthsMiddle.op ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis t))).vec
      = Complex.I ^ ((t + a * b : Fin 2) : ℕ)
        • ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis t))).vec := by
  rw [← Evolution.evolvePure_vec, rzThreeFifthsMiddle_evolvePure_qubitBasis_vec]

/-- **The input Hadamards prepare `|+⟩ ⊗ |+⟩` on the ancillas:** with both ancillas in `|0⟩` and
the target in `|t⟩`, the gate `H ⊗ H ⊗ 1` produces `|+⟩ ⊗ |+⟩ ⊗ |t⟩`. -/
theorem rzThreeFifthsHadamards_evolvePure_ketZeroZero (t : Fin 2) :
    rzThreeFifthsHadamards.evolvePure ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t)))
      = qubitPlus.tmul (qubitPlus.tmul (qubitBasis t)) := by
  rw [rzThreeFifthsHadamards, Evolution.tmul_evolvePure, hadamardGate_evolvePure_qubitBasis_zero,
    Evolution.onLeft_evolvePure, hadamardGate_evolvePure_qubitBasis_zero]

/-! ### The full four-branch action on `|0⟩ ⊗ |0⟩ ⊗ |t⟩` -/

/-- **`H` on a computational basis state, in binary superposition form:**
`H|a⟩ = (1/√2)(|0⟩ + (-1)ᵃ |1⟩)`. The uniform statement of `H|0⟩ = |+⟩`, `H|1⟩ = |-⟩` that carries
the interference sign `(-1)ᵃ` explicitly, so the two ancilla Hadamards distribute with matching
signs. -/
theorem hadamardGate_evolvePure_qubitBasis_vec_binary (a : Fin 2) :
    (hadamardGate.evolvePure (qubitBasis a)).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec + (-1 : ℂ) ^ (a : ℕ) • (qubitBasis 1).vec) := by
  match a with
  | 0 =>
    rw [hadamardGate_evolvePure_qubitBasis_zero, qubitPlus_vec_eq_smul_add]
    simp only [Fin.val_zero, pow_zero, one_smul]
  | 1 =>
    rw [hadamardGate_evolvePure_qubitBasis_one, qubitMinus_vec_eq_smul_sub]
    rw [sub_eq_add_neg]
    simp only [Fin.val_one, pow_one, neg_one_smul]

/-- **`H` on each ancilla, on a computational basis input** (`PureState.tmul` form):
`(H ⊗ H ⊗ 1)|a,b,t⟩ = (H|a⟩) ⊗ (H|b⟩) ⊗ |t⟩`. -/
theorem rzThreeFifthsHadamards_evolvePure_qubitBasis (a b t : Fin 2) :
    rzThreeFifthsHadamards.evolvePure ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis t)))
      = (hadamardGate.evolvePure (qubitBasis a)).tmul
          ((hadamardGate.evolvePure (qubitBasis b)).tmul (qubitBasis t)) := by
  rw [rzThreeFifthsHadamards, Evolution.tmul_evolvePure, Evolution.onLeft_evolvePure]

/-- **The middle gate followed by the output Hadamards, on a computational basis input:**
`(H⊗H⊗1)·(T·(1⊗1⊗S)·T)|a,b,t⟩ = iᵗ⁺ᵃᵇ · ((H|a⟩) ⊗ (H|b⟩) ⊗ |t⟩)`. Combines the diagonal middle
action (`rzThreeFifthsMiddle_op_qubitBasis_vec`) with the factorwise output Hadamards; the workhorse
pushed through the four ancilla histories of `|+⟩ ⊗ |+⟩`. -/
theorem rzThreeFifthsMiddleHadamards_op_qubitBasis_vec (a b t : Fin 2) :
    rzThreeFifthsHadamards.op (rzThreeFifthsMiddle.op
        ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis t))).vec)
      = Complex.I ^ ((t + a * b : Fin 2) : ℕ) •
          ((hadamardGate.evolvePure (qubitBasis a)).tmul
            ((hadamardGate.evolvePure (qubitBasis b)).tmul (qubitBasis t))).vec := by
  rw [rzThreeFifthsMiddle_op_qubitBasis_vec, map_smul, ← Evolution.evolvePure_vec,
    rzThreeFifthsHadamards_evolvePure_qubitBasis]

/-- **The input Hadamards output expanded over the four ancilla histories:**
`|+⟩ ⊗ |+⟩ ⊗ |t⟩ = (1/√2)² ∑_{a,b} |a⟩ ⊗ |b⟩ ⊗ |t⟩` (in `PureState.tmul` form). The starting point
for pushing the diagonal middle gate through by linearity. The inner `|+⟩ ⊗ |t⟩` is distributed on
the clean two-qubit tensor first; the `change` then re-ascribes it at the raw
`qubit.space ⊗ qubit.space` head so `TensorProduct.tmul_add`/`tmul_smul` fire on the outer tensor
(they do not unify against the composite domain otherwise). -/
theorem rzThreeFifthsInput_expand (t : Fin 2) :
    (qubitPlus.tmul (qubitPlus.tmul (qubitBasis t))).vec
      = ∑ a : Fin 2, ∑ b : Fin 2, Concrete.invSqrt2 ^ 2 •
          ((qubitBasis a).tmul ((qubitBasis b).tmul (qubitBasis t))).vec := by
  rw [PureState.tmul_vec, PureState.tmul_vec]
  have hinner : qubitPlus.vec ⊗ₜ[ℂ] (qubitBasis t).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis t).vec
          + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis t).vec) := by
    rw [qubitPlus_vec_eq_smul_add, ← TensorProduct.smul_tmul', TensorProduct.add_tmul]
  rw [hinner, qubitPlus_vec_eq_smul_add]
  change (Concrete.invSqrt2 • ((qubitBasis 0).vec + (qubitBasis 1).vec) : qubit.space) ⊗ₜ[ℂ]
      (Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis t).vec
        + (qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis t).vec) : qubit.space ⊗[ℂ] qubit.space) = _
  rw [← TensorProduct.smul_tmul', TensorProduct.add_tmul]
  simp only [TensorProduct.tmul_smul, TensorProduct.tmul_add, Fin.sum_univ_two, sq,
    PureState.tmul_vec, smul_add, smul_smul]
  rfl

/-- **The output Hadamards expanded over the four output-ancilla outcomes:**
`(H|a⟩) ⊗ (H|b⟩) ⊗ |t⟩ = (1/√2)² ∑_{a',b'} (-1)^{a·a'} (-1)^{b·b'} |a'⟩ ⊗ |b'⟩ ⊗ |t⟩`. Same nested
distribution as `rzThreeFifthsInput_expand`, but carrying the interference signs `(-1)^{a·a'}` from
each Hadamard (`hadamardGate_evolvePure_qubitBasis_vec_binary`). -/
theorem rzThreeFifthsHadamardTwo_expand (a b t : Fin 2) :
    ((hadamardGate.evolvePure (qubitBasis a)).tmul
        ((hadamardGate.evolvePure (qubitBasis b)).tmul (qubitBasis t))).vec
      = ∑ a' : Fin 2, ∑ b' : Fin 2,
          (Concrete.invSqrt2 ^ 2 *
              ((-1 : ℂ) ^ ((a : ℕ) * (a' : ℕ)) * (-1 : ℂ) ^ ((b : ℕ) * (b' : ℕ))))
            • ((qubitBasis a').tmul ((qubitBasis b').tmul (qubitBasis t))).vec := by
  rw [PureState.tmul_vec, PureState.tmul_vec, hadamardGate_evolvePure_qubitBasis_vec_binary a,
    hadamardGate_evolvePure_qubitBasis_vec_binary b]
  have hinner : (Concrete.invSqrt2 • ((qubitBasis 0).vec + (-1 : ℂ) ^ (b : ℕ) • (qubitBasis 1).vec))
        ⊗ₜ[ℂ] (qubitBasis t).vec
      = Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis t).vec
          + (-1 : ℂ) ^ (b : ℕ) • ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis t).vec)) := by
    rw [← TensorProduct.smul_tmul', TensorProduct.add_tmul, TensorProduct.smul_tmul']
  rw [hinner]
  change (Concrete.invSqrt2 • ((qubitBasis 0).vec + (-1 : ℂ) ^ (a : ℕ) • (qubitBasis 1).vec)
        : qubit.space) ⊗ₜ[ℂ]
      (Concrete.invSqrt2 • ((qubitBasis 0).vec ⊗ₜ[ℂ] (qubitBasis t).vec
        + (-1 : ℂ) ^ (b : ℕ) • ((qubitBasis 1).vec ⊗ₜ[ℂ] (qubitBasis t).vec))
        : qubit.space ⊗[ℂ] qubit.space) = _
  rw [← TensorProduct.smul_tmul', TensorProduct.add_tmul, ← TensorProduct.smul_tmul']
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul, smul_smul, smul_add,
    Fin.sum_univ_two, sq, Fin.val_zero, Fin.val_one, Nat.mul_zero, pow_zero, one_mul, mul_one]
  change (Concrete.invSqrt2 * Concrete.invSqrt2) •
        ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t))).vec
      + (Concrete.invSqrt2 * (Concrete.invSqrt2 * (-1) ^ (b : ℕ))) •
        ((qubitBasis 0).tmul ((qubitBasis 1).tmul (qubitBasis t))).vec
      + ((Concrete.invSqrt2 * ((-1) ^ (a : ℕ) * Concrete.invSqrt2)) •
          ((qubitBasis 1).tmul ((qubitBasis 0).tmul (qubitBasis t))).vec
        + (Concrete.invSqrt2 * ((-1) ^ (a : ℕ) * (Concrete.invSqrt2 * (-1) ^ (b : ℕ)))) •
          ((qubitBasis 1).tmul ((qubitBasis 1).tmul (qubitBasis t))).vec) = _
  module

/-- **The interference amplitude on the ancilla outcome `|a'⟩ ⊗ |b'⟩`** in the four-branch action
of the Figure 4.17 circuit on `|0⟩ ⊗ |0⟩ ⊗ |t⟩`: the sum over the two ancilla "histories" `(a, b)`
of the middle-gate phase `iᵗ⁺ᵃᵇ` (a Fin-2/XOR exponent) weighted by the Hadamard interference signs
`(-1)^{a·a'} (-1)^{b·b'}`, normalised by `(1/√2)⁴ = 1/4`. Reading off `rzThreeFifthsAmp 0 0 t` gives
the success operator `M₀₀`, and the other three `(a', b')` give the failure branches. -/
def rzThreeFifthsAmp (a' b' t : Fin 2) : ℂ :=
  Concrete.invSqrt2 ^ 4 * ∑ a : Fin 2, ∑ b : Fin 2,
    Complex.I ^ ((t + a * b : Fin 2) : ℕ) *
      ((-1 : ℂ) ^ ((a : ℕ) * (a' : ℕ)) * (-1 : ℂ) ^ ((b : ℕ) * (b' : ℕ)))

/-- **The full four-branch action of the Figure 4.17 circuit on `|0⟩ ⊗ |0⟩ ⊗ |t⟩`:**
`rzThreeFifthsCircuit(|0,0,t⟩) = ∑_{a',b'} rzThreeFifthsAmp a' b' t · |a',b',t⟩`.
The target index stays `t` (the middle gate is diagonal and the output Hadamards act only on the
ancillas), so the whole output lives in `span{|a',b',t⟩}` and is read off branch by branch: the
`|0,0⟩`-ancilla (success) branch, and the three others. -/
theorem rzThreeFifthsCircuit_evolvePure_ketZeroZero_qubitBasis (t : Fin 2) :
    (rzThreeFifthsCircuit.evolvePure
        ((qubitBasis 0).tmul ((qubitBasis 0).tmul (qubitBasis t)))).vec
      = ∑ a' : Fin 2, ∑ b' : Fin 2,
          rzThreeFifthsAmp a' b' t
            • ((qubitBasis a').tmul ((qubitBasis b').tmul (qubitBasis t))).vec := by
  rw [Evolution.evolvePure_vec, rzThreeFifthsCircuit]
  simp only [Evolution.comp_op, ContinuousLinearMap.comp_apply]
  rw [← Evolution.evolvePure_vec, rzThreeFifthsHadamards_evolvePure_ketZeroZero,
    rzThreeFifthsInput_expand]
  -- Both circuit operators are `ContinuousLinearMap`s, so `map_add`/`map_smul` push them through
  -- the (composite-`.space`-headed) branch sum directly; then read each branch off by linearity.
  simp only [Fin.sum_univ_two, map_add, map_smul, rzThreeFifthsMiddleHadamards_op_qubitBasis_vec,
    rzThreeFifthsHadamardTwo_expand, rzThreeFifthsAmp, smul_smul]
  module

/-! ### Reading off `R_z(θ)` on success and `Z` on failure -/

/-- **The `4×2` amplitude table of the Figure 4.17 circuit on `|0⟩ ⊗ |0⟩ ⊗ |t⟩`.** Evaluating
the interference sum
`rzThreeFifthsAmp a' b' t = (1/√2)⁴ ∑_{a,b} iᵗ⁺ᵃᵇ (-1)^{a·a'} (-1)^{b·b'}` at each of
the eight `(a',b',t)`:

* the **success** column `(a',b') = (0,0)` is `(3+i)/4` on `|0⟩` and `(1+3i)/4` on `|1⟩` — the
  operator `M₀₀`;
* each **failure** column is `± (1-i)/4`, alternating in sign with `t` (`= (1-i)/4 · (-1)ᵗ` for
  `(0,1)`/`(1,0)`, and `(-1+i)/4 · (-1)ᵗ` for `(1,1)`) — an operator proportional to `Z`.

Each phase `iᵗ⁺ᵃᵇ` uses the `Fin 2` (mod-2) exponent, so the `(1,1)`, `t=1` history contributes
`i⁰ = 1`, not `i²`; this is exactly the interference that yields `cos θ = 3/5`. -/
theorem rzThreeFifthsAmp_apply :
    rzThreeFifthsAmp 0 0 0 = (3 + Complex.I) / 4 ∧
    rzThreeFifthsAmp 0 0 1 = (1 + 3 * Complex.I) / 4 ∧
    rzThreeFifthsAmp 0 1 0 = (1 - Complex.I) / 4 ∧
    rzThreeFifthsAmp 0 1 1 = (-1 + Complex.I) / 4 ∧
    rzThreeFifthsAmp 1 0 0 = (1 - Complex.I) / 4 ∧
    rzThreeFifthsAmp 1 0 1 = (-1 + Complex.I) / 4 ∧
    rzThreeFifthsAmp 1 1 0 = (-1 + Complex.I) / 4 ∧
    rzThreeFifthsAmp 1 1 1 = (1 - Complex.I) / 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [rzThreeFifthsAmp, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Concrete.invSqrt2_sq]
    simp only [Fin.sum_univ_two, Fin.isValue, Fin.reduceAdd, Fin.val_zero, Fin.val_one,
      pow_zero, pow_one, mul_zero, mul_one]
    norm_num [Complex.ext_iff]

/-- **The rotation angle `θ` of Exercise 4.41:** `θ = arccos (3/5)`, so `cos θ = 3/5` (Nielsen &
Chuang's value) and `sin θ = 4/5`, hence `e^{iθ} = (3 + 4i)/5`. -/
def rzThreeFifthsAngle : ℝ := Real.arccos (3 / 5)

/-- `cos θ = 3/5` for the Exercise-4.41 angle — the value Nielsen & Chuang state for the applied
`R_z(θ)`. -/
theorem rzThreeFifthsAngle_cos : Real.cos rzThreeFifthsAngle = 3 / 5 := by
  rw [rzThreeFifthsAngle, Real.cos_arccos] <;> norm_num

/-- `e^{iθ} = (3 + 4i)/5` for the Exercise-4.41 angle (the ratio of the two `M₀₀` eigenvalues, and
the quantity `e^{iθ} = (3+4i)/5` that Exercise 4.42 shows makes `θ` an irrational multiple of `2π`).
Follows from `cos θ = 3/5`, `sin θ = 4/5` via `Complex.exp_mul_I`. -/
theorem rzThreeFifthsAngle_exp_mul_I :
    Complex.exp (↑rzThreeFifthsAngle * Complex.I) = 3 / 5 + 4 / 5 * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, rzThreeFifthsAngle_cos,
    rzThreeFifthsAngle, Real.sin_arccos, show (1 : ℝ) - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- The squared modulus of a quarter-scaled Gaussian rational: `‖(x + y·i)/4‖² = (x²+y²)/16`. The
shared engine of the `5/8` and `1/8` branch probabilities below (each amplitude is a Gaussian
integer over `4`). -/
private theorem norm_ofReal_add_mul_I_div_four_sq (x y : ℝ) :
    ‖((x : ℂ) + (y : ℂ) * Complex.I) / 4‖ ^ 2 = (x ^ 2 + y ^ 2) / 16 := by
  rw [Complex.norm_div, Complex.norm_add_mul_I, show ((4 : ℂ)) = ((4 : ℝ) : ℂ) by norm_num,
    Complex.norm_real, div_pow, Real.sq_sqrt (by positivity)]
  norm_num

/-- **Exercise 4.41, success branch: the circuit applies `R_z(θ)` with `cos θ = 3/5`.** When both
ancillas are measured `0`, the (unnormalised) action on the target is the diagonal operator
`M₀₀ : |t⟩ ↦ rzThreeFifthsAmp 0 0 t · |t⟩`; this theorem exhibits a scalar `c` with
`M₀₀ = c · R_z(θ)` for `θ = rzThreeFifthsAngle` (`cos θ = 3/5`, see `rzThreeFifthsAngle_cos`).

Because `R_z(θ)` is unitary, `‖c‖² = 5/8` is precisely the (input-independent) Born probability
of the `00` outcome — Nielsen & Chuang's `5/8` — and, after renormalising the post-measurement
state, the operation applied to the target is exactly the unitary `R_z(θ)`. The scalar `c` is
existential because its phase is a physically-irrelevant global phase; only `‖c‖²` carries content.
The identity is stated on each computational basis vector `|t⟩`, which (the two spanning `M₀₀` and
`c · R_z(θ)`) determines the operators. -/
theorem rzThreeFifthsCircuit_success_eq_rotZ :
    ∃ c : ℂ, ‖c‖ ^ 2 = 5 / 8 ∧ ∀ t : Fin 2,
      rzThreeFifthsAmp 0 0 t • (qubitBasis t).vec
        = c • (rotZGate rzThreeFifthsAngle).op (qubitBasis t).vec := by
  obtain ⟨e000, e001, _, _, _, _, _, _⟩ := rzThreeFifthsAmp_apply
  refine ⟨(3 + Complex.I) / 4 * Complex.exp (↑rzThreeFifthsAngle / 2 * Complex.I), ?_, ?_⟩
  · rw [norm_mul, mul_pow, show ‖Complex.exp (↑rzThreeFifthsAngle / 2 * Complex.I)‖ = 1 by
        rw [Complex.norm_exp]; simp, one_pow, mul_one,
      show (3 + Complex.I) = ((3 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_ofReal_add_mul_I_div_four_sq]
    norm_num
  · intro t
    rw [rotZGate_op_apply_qubitBasis, smul_smul]
    refine congrArg (· • (qubitBasis t).vec) ?_
    match t with
    | 0 =>
      rw [e000, Concrete.rotZ_apply_zero_zero, mul_assoc, ← Complex.exp_add, neg_mul,
        add_neg_cancel, Complex.exp_zero, mul_one]
    | 1 =>
      rw [e001, Concrete.rotZ_apply_one_one, mul_assoc, ← Complex.exp_add,
        show ↑rzThreeFifthsAngle / 2 * Complex.I + ↑rzThreeFifthsAngle / 2 * Complex.I
          = ↑rzThreeFifthsAngle * Complex.I by ring, rzThreeFifthsAngle_exp_mul_I]
      rw [Complex.ext_iff]; constructor <;> simp <;> ring

/-- **A diagonal operator with computational-basis eigenvalues `(c, -c)` is `c · Z`:** if `f 0 = c`
and `f 1 = -c` then `f t • |t⟩ = c • Z|t⟩` for each `t`. The reusable engine behind the failure
branches below — each is a diagonal operator `|t⟩ ↦ f t • |t⟩` with `f 1 = -f 0`, hence `∝ Z`. -/
theorem smul_qubitBasis_eq_smul_pauliZ_op {c : ℂ} {f : Fin 2 → ℂ}
    (h0 : f 0 = c) (h1 : f 1 = -c) (t : Fin 2) :
    f t • (qubitBasis t).vec = c • pauliZGate.op (qubitBasis t).vec := by
  rw [pauliZGate_op_apply_qubitBasis, smul_smul]
  refine congrArg (· • (qubitBasis t).vec) ?_
  match t with
  | 0 => rw [h0]; simp
  | 1 => rw [h1, Fin.val_one]; ring

/-- **Exercise 4.41, failure branches: any other outcome applies `Z`.** For every ancilla outcome
`(a',b') ≠ (0,0)`, the (unnormalised) action on the target
`M_{a'b'} : |t⟩ ↦ rzThreeFifthsAmp a' b' t · |t⟩` equals `c · Z` for a scalar `c` with
`‖c‖² = 1/8`. So each of the three failure branches applies the Pauli `Z` (after renormalising),
each with Born probability `1/8` (totalling the complementary `3/8`). -/
theorem rzThreeFifthsCircuit_failure_eq_pauliZ (a' b' : Fin 2) (h : ¬ (a' = 0 ∧ b' = 0)) :
    ∃ c : ℂ, ‖c‖ ^ 2 = 1 / 8 ∧ ∀ t : Fin 2,
      rzThreeFifthsAmp a' b' t • (qubitBasis t).vec
        = c • pauliZGate.op (qubitBasis t).vec := by
  obtain ⟨_, _, e010, e011, e100, e101, e110, e111⟩ := rzThreeFifthsAmp_apply
  have hnorm1 : ‖(1 - Complex.I) / 4‖ ^ 2 = 1 / 8 := by
    rw [show (1 - Complex.I) = ((1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_ofReal_add_mul_I_div_four_sq]
    norm_num
  have hnorm2 : ‖(-1 + Complex.I) / 4‖ ^ 2 = 1 / 8 := by
    rw [show (-1 + Complex.I) = ((-1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_ofReal_add_mul_I_div_four_sq]
    norm_num
  match a', b', h with
  | 0, 0, h => exact absurd ⟨rfl, rfl⟩ h
  | 0, 1, _ => exact ⟨rzThreeFifthsAmp 0 1 0, by rw [e010]; exact hnorm1,
      smul_qubitBasis_eq_smul_pauliZ_op rfl (by rw [e011, e010]; ring)⟩
  | 1, 0, _ => exact ⟨rzThreeFifthsAmp 1 0 0, by rw [e100]; exact hnorm1,
      smul_qubitBasis_eq_smul_pauliZ_op rfl (by rw [e101, e100]; ring)⟩
  | 1, 1, _ => exact ⟨rzThreeFifthsAmp 1 1 0, by rw [e110]; exact hnorm2,
      smul_qubitBasis_eq_smul_pauliZ_op rfl (by rw [e111, e110]; ring)⟩

end AxQM
