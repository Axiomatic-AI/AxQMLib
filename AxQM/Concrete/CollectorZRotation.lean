/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringParityCascade
import AxQM.Concrete.SingleQubitWire
import AxQM.Concrete.Rotation

/-!
# Concrete: the Figure-4.19 collector `Z`-rotation as a single-wire gate

This is the **third step** of Nielsen & Chuang
**Problem 4.3(3)** — "implement `exp(-i h_g g Δ)` using `O(n)` one- and two-qubit gates" — closing
the gap between the *matrix-level* collector rotation of the Figure-4.19 parity cascade and the
*single-qubit `z`-rotation gate* that circuit actually applies to the collector wire.

## The construction (N&C §4.7.3, Figure 4.19)

`Concrete/PauliStringParityCascade.lean` reduces the diagonalised (all-`Z`-on-support) exponential
to `exp(s · P_a) = V† · exp(s · P_{Z_c}) · V`, where the middle factor `exp(s · P_{Z_c})` —
`exp(s • pauliString (zGenPauli c))` — is the collector rotation, a phase depending only on the
collector's bit. Physically `s = -i h_g Δ`, so this factor is a single-qubit `z`-rotation
`R_z(2 h_g Δ)` on wire `c`. This file makes that identification precise.

## What is proved

* `exp_smul_diagonal` — a general helper: `exp(s • diagonal v) = diagonal (fun i ↦ exp(s · vᵢ))` for
  a complex diagonal matrix (`Matrix.exp_diagonal` composed with `Pi.coe_exp`).
* `pauliString_zGenPauli_eq_diagonal` — the single-`Z` string `P_{Z_c}` is diagonal, `+1` where the
  collector bit is `0` and `−1` where it is `1` (the general-wire form of the wire-`0`
  `pauliString_zGenPauli_zero_eq_diagonal`).
* `pauliZ_eq_diagonal` / `rotZ_eq_exp_smul_pauliZ` — the `2 × 2` facts `Z = diagonal ![1, −1]` and
  `R_z(θ) = exp((−θ/2) i • Z)` (the latter is the definition `rotZ = rotAxis ![0,0,1]` unfolded
  through `pauliDot_axisZ`).
* `exp_smul_pauliString_zGenPauli_submatrix_eq_singleQubitOnWire` — **the bridge**: reindexed to the
  flat `2ⁿ`-level register along `finFunctionFinEquiv`, the collector exponential is exactly the
  `2 × 2` gate `exp(s • Z)` placed on wire `c` (`e := finFunctionFinEquiv`),
  `(exp(s • P_{Z_c})).submatrix e⁻¹ e⁻¹ = singleQubitOnWire e c (exp(s • Z))`.
  Both sides are diagonal (`P_{Z_c}` and `Z` are), so the proof is a diagonal-vector comparison via
  `singleQubitOnWire_diagonal` and `Matrix.submatrix_diagonal_equiv`.

Chaining this with `rotZ_eq_exp_smul_pauliZ` (at `s = (−θ/2) i`) exhibits the register `z`-rotation
`singleQubitOnWire e c (rotZ θ)` — the one single-qubit gate the collector carries — as the
reindexed Figure-4.19 collector rotation; the `Evolution`-level faithfulness of that identification
is `rotZWireEvolution_op_eq_exp_smul_zGenPauli` (`Postulates/API/CollectorZRotationEvolution.lean`).
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-- **Exponential of a scalar-multiplied complex diagonal matrix.** `exp(s • diagonal v)` is the
diagonal matrix of pointwise complex exponentials `fun i ↦ exp(s · vᵢ)`. Pushes the scalar into the
diagonal (`Matrix.diagonal_smul`), applies `Matrix.exp_diagonal`, and evaluates the resulting
`Pi`-exponential pointwise (`Pi.coe_exp`, `Complex.exp_eq_exp_ℂ`). -/
theorem exp_smul_diagonal {m : Type*} [Fintype m] [DecidableEq m] (s : ℂ) (v : m → ℂ) :
    NormedSpace.exp (s • Matrix.diagonal v)
      = Matrix.diagonal (fun i => Complex.exp (s * v i)) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Complex.exp_eq_exp_ℂ, Pi.coe_exp, Pi.smul_apply, smul_eq_mul]

/-- **The single-`Z` Pauli string `Z_c` is diagonal.** `pauliString (zGenPauli c)` — `Z` on the
collector wire `c`, identity elsewhere — is the diagonal matrix whose entry at a bit string `i` is
`+1` when the collector bit `i c` is `0` and `−1` when it is `1`. The general-wire form of
`pauliString_zGenPauli_zero_eq_diagonal` (wire `0`): every off-support factor `pauli 0 = I` is
diagonal and the collector factor `pauli 3 = Z` is diagonal, so the whole product vanishes off the
diagonal and equals the collector's `Z` entry on it. -/
theorem pauliString_zGenPauli_eq_diagonal (c : Fin n) :
    pauliString (zGenPauli c) = Matrix.diagonal (fun i => if i c = 0 then (1 : ℂ) else -1) := by
  ext i j
  rw [pauliString_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c)]
    have hrest : ∀ k ∈ Finset.univ.erase c, pauli (zGenPauli c k) (i k) (i k) = 1 := by
      intro k hk
      rw [zGenPauli_apply, ite_eq_right (Finset.ne_of_mem_erase hk)]; simp [pauli]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const_one, mul_one, zGenPauli_apply,
        ite_eq_left rfl]
    rcases (show i c = 0 ∨ i c = 1 by omega) with h | h <;> rw [h] <;> simp [pauli, pauliZ]
  · rw [ite_eq_right hij]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hij
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    by_cases hkc : k = c
    · subst hkc
      rw [zGenPauli_apply, ite_eq_left rfl]
      rcases (show i k = 0 ∨ i k = 1 by omega) with h1 | h1 <;>
        rcases (show j k = 0 ∨ j k = 1 by omega) with h2 | h2 <;> simp_all [pauli, pauliZ]
    · rw [zGenPauli_apply, ite_eq_right hkc]; simp [pauli, hk]

/-- **The Pauli `Z` matrix as a diagonal.** `Z = diagonal ![1, −1]`, entry `+1` at bit `0` and `−1`
at bit `1`. The `2 × 2` companion of `pauliString_zGenPauli_eq_diagonal`. -/
theorem pauliZ_eq_diagonal :
    pauliZ = Matrix.diagonal (fun z => if z = 0 then (1 : ℂ) else -1) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauliZ]

/-- **The `z`-rotation is the exponential of `−(θ/2) i • Z`.** `R_z(θ) = exp((−θ/2) i • Z)`,
Nielsen & Chuang eq. 4.6 read as the definition `rotZ = rotAxis ![0,0,1]` (an exponential of
`(−θ/2) i • (ẑ·σ)`) with `ẑ·σ = Z` (`pauliDot_axisZ`). The scalar `s = (−θ/2) i` is exactly the
`s = -i h_g Δ` of the Figure-4.19 collector rotation at `θ = 2 h_g Δ`. -/
theorem rotZ_eq_exp_smul_pauliZ (θ : ℝ) :
    rotZ θ = NormedSpace.exp ((((-(θ / 2) : ℝ) : ℂ) * Complex.I) • pauliZ) := by
  rw [rotZ, rotAxis, pauliDot_axisZ]

/-- **The Figure-4.19 collector rotation is a single-wire `Z`-exponential.** Reindexed to the flat
`2ⁿ`-level register along `e = finFunctionFinEquiv`, the collector exponential
`exp(s • pauliString (zGenPauli c))` — the middle factor `exp(s · P_{Z_c})` of the parity collapse
`pauliString_exp_smul_conj_cnotFanInto` — is exactly the `2 × 2` gate `exp(s • Z)` placed on wire
`c`:
`(exp(s • P_{Z_c})).submatrix e⁻¹ e⁻¹ = singleQubitOnWire e c (exp(s • Z))`.

Both sides are diagonal: `pauliString (zGenPauli c)` and `pauliZ` are diagonal
(`pauliString_zGenPauli_eq_diagonal`, `pauliZ_eq_diagonal`), so `exp_smul_diagonal` turns each
exponential into a diagonal of pointwise complex exponentials; `Matrix.submatrix_diagonal_equiv` and
`singleQubitOnWire_diagonal` then reindex both to `diagonal (fun i ↦ exp(s · (Z-value of bit c of
e⁻¹ i)))`. The reindex `.submatrix e⁻¹ e⁻¹` is the same `finFunctionFinEquiv.symm` reindex that
`pauliStringStd` / `kronFamilyStd` / `cnotFanIntoEvolution_op` use, so this chains directly into the
register faithfulness of the parity fan. -/
theorem exp_smul_pauliString_zGenPauli_submatrix_eq_singleQubitOnWire (c : Fin n) (s : ℂ) :
    (NormedSpace.exp (s • pauliString (zGenPauli c))).submatrix
        finFunctionFinEquiv.symm finFunctionFinEquiv.symm
      = singleQubitOnWire finFunctionFinEquiv c (NormedSpace.exp (s • pauliZ)) := by
  rw [pauliString_zGenPauli_eq_diagonal, exp_smul_diagonal, Matrix.submatrix_diagonal_equiv,
    pauliZ_eq_diagonal, exp_smul_diagonal, singleQubitOnWire_diagonal]
  rfl

end AxQM.Concrete
