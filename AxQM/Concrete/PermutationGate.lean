/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Group.End
import ToMathlib.LinearAlgebra.UnitaryGroup

/-!
# Concrete: the encoding-carried permutation gate `permGate`

The `n`-qubit universality argument (Nielsen & Chuang §4.3/§4.5.2) realises a two-level unitary as a
circuit whose backbone is a family of **classical reversible gates** — the multiply-controlled
`NOT`, the single-wire `NOT`, the basis transpositions of the Gray-code walk, `CNOT`, `Toffoli`.
Each of these acts on the computational basis `|enc x⟩` (`enc : (Fin m → Fin 2) ≃ Fin d` an encoding
of the `m`-bit strings as the `d`-dimensional register) by a *permutation of the bit-strings*
`σ : Equiv.Perm (Fin m → Fin 2)`: `|enc x⟩ ↦ |enc (σ x)⟩`. This file provides the matrix realising
that action, `permGate enc σ`, and its algebra.

`permGate enc σ` is defined as **Mathlib's permutation matrix** `Equiv.Perm.permMatrix` of the
conjugated permutation `(enc.permCongr σ)⁻¹` of `Fin d`; carrying `enc` and `σ` explicitly (and
using the inverse of `enc.permCongr σ`) fixes the **forward** convention
`permGate enc σ *ᵥ |enc x⟩ = |enc (σ x)⟩`, so `permGate enc` is a genuine `*`-homomorphism (not the
anti-homomorphism `permMatrix` is directly). Defining it *as* a `permMatrix` — rather than by hand
from `0/1` entries — reuses the whole `Equiv.Perm.permMatrix` API: the algebra below is derived from
`Matrix.permMatrix_one`/`_mul`/`conjTranspose_permMatrix` and `Equiv.permCongr_mul` in a few
rewrites, and the operator-norm bounds `Matrix.permMatrix_l2_opNorm_le`/`_eq` (each `‖·‖ = 1`) come
for free — exactly the per-gate norm bound the §4.5.3 error-chaining calculus will need.

## Contents

* `permGate enc σ` — `(enc.permCongr σ)⁻¹.permMatrix ℂ`; `permGate_apply` is its entry form,
  `(permGate enc σ) i i' = 1` iff `i = enc (σ (enc.symm i'))`, so its forward action on a basis
  vector is `permGate enc σ *ᵥ |enc x⟩ = |enc (σ x)⟩`.
* `permGate_one` / `permGate_mul` — `permGate enc` is a `*`-homomorphism
  (`permGate enc 1 = 1`, `permGate enc σ * permGate enc τ = permGate enc (σ * τ)`).
* `permGate_conjTranspose` / `permGate_mem_unitaryGroup` — the adjoint is the gate of the inverse
  permutation, so every `permGate` is unitary.

Everything is stated for raw complex matrices and an `Equiv.Perm`.
-/

open Matrix

namespace AxQM.Concrete

variable {m d : ℕ}

/-- **The encoding-carried permutation gate.** For an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of
the `m`-bit strings as the `d`-dimensional register and a permutation `σ` of the bit-strings,
`permGate enc σ` is Mathlib's permutation matrix of the conjugated permutation `(enc.permCongr σ)⁻¹`
of `Fin d`: the `d × d` matrix sending the basis state `|enc x⟩` to `|enc (σ x)⟩`. It is the matrix
realising a classical reversible gate (`NOT`, `CNOT`, `Toffoli`, multiply-controlled `NOT`, basis
transposition) whose action on bit-strings is `σ`. -/
def permGate (enc : (Fin m → Fin 2) ≃ Fin d) (σ : Equiv.Perm (Fin m → Fin 2)) :
    Matrix (Fin d) (Fin d) ℂ :=
  (enc.permCongr σ)⁻¹.permMatrix ℂ

/-- `enc.permCongr` sends the identity permutation to the identity (it is a monoid homomorphism,
`Equiv.permCongrHom`). -/
theorem permCongr_one (enc : (Fin m → Fin 2) ≃ Fin d) :
    enc.permCongr (1 : Equiv.Perm (Fin m → Fin 2)) = 1 :=
  map_one (Equiv.permCongrHom enc)

/-- `enc.permCongr` commutes with taking inverses (it is a monoid homomorphism,
`Equiv.permCongrHom`). -/
theorem permCongr_inv (enc : (Fin m → Fin 2) ≃ Fin d) (σ : Equiv.Perm (Fin m → Fin 2)) :
    enc.permCongr σ⁻¹ = (enc.permCongr σ)⁻¹ :=
  map_inv (Equiv.permCongrHom enc) σ

/-- **The entry form of the permutation gate.** `(permGate enc σ) i i' = 1` exactly when
`i = enc (σ (enc.symm i'))` (and `0` otherwise); equivalently its forward action on the basis is
`permGate enc σ *ᵥ |enc x⟩ = |enc (σ x)⟩`. -/
@[simp] theorem permGate_apply (enc : (Fin m → Fin 2) ≃ Fin d) (σ : Equiv.Perm (Fin m → Fin 2))
    (i i' : Fin d) :
    permGate enc σ i i' = if i = enc (σ (enc.symm i')) then 1 else 0 := by
  simp only [permGate, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_some_iff]
  refine if_congr ?_ rfl rfl
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, Equiv.permCongr_apply]

/-- `permGate enc 1 = 1`: the identity permutation gives the identity matrix. -/
@[simp] theorem permGate_one (enc : (Fin m → Fin 2) ≃ Fin d) :
    permGate enc (1 : Equiv.Perm (Fin m → Fin 2)) = 1 := by
  simp only [permGate, permCongr_one, inv_one, Matrix.permMatrix_one]

/-- **`permGate enc` is multiplicative**: `permGate enc σ * permGate enc τ = permGate enc (σ * τ)`.
Composing the gates (rightmost first) composes the bit-string permutations,
`(σ * τ) x = σ (τ x)`. Derived from `Matrix.permMatrix_mul` (an anti-homomorphism) and
`Equiv.permCongr_mul`, with `mul_inv_rev` absorbing the order reversal. -/
theorem permGate_mul (enc : (Fin m → Fin 2) ≃ Fin d) (σ τ : Equiv.Perm (Fin m → Fin 2)) :
    permGate enc σ * permGate enc τ = permGate enc (σ * τ) := by
  simp only [permGate]
  rw [← Matrix.permMatrix_mul, ← _root_.mul_inv_rev, ← Equiv.permCongr_mul]

/-- **The adjoint of a permutation gate is the gate of the inverse permutation.**
`(permGate enc σ)ᴴ = permGate enc σ⁻¹`, from `Matrix.conjTranspose_permMatrix`. -/
@[simp] theorem permGate_conjTranspose (enc : (Fin m → Fin 2) ≃ Fin d)
    (σ : Equiv.Perm (Fin m → Fin 2)) :
    (permGate enc σ)ᴴ = permGate enc σ⁻¹ := by
  simp only [permGate]
  rw [Matrix.conjTranspose_permMatrix, permCongr_inv]

/-- **Every permutation gate is unitary.** A permutation matrix is unitary
(`star (permMatrix ρ) = permMatrix ρ⁻¹` and `permMatrix ρ * permMatrix ρ⁻¹ = permMatrix 1 = 1`). -/
theorem permGate_mem_unitaryGroup (enc : (Fin m → Fin 2) ≃ Fin d)
    (σ : Equiv.Perm (Fin m → Fin 2)) :
    permGate enc σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  simp only [permGate]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

/-- **A permutation gate sends a basis state to a basis state:**
`permGate enc σ *ᵥ |enc x⟩ = |enc (σ x)⟩` — the forward action recorded in `permGate`'s definition,
on the standard basis vectors. This is the column form of `permGate_apply`: the `j = enc x` column
of `permGate enc σ` is the indicator of `enc (σ x)`. -/
theorem permGate_mulVec_single (enc : (Fin m → Fin 2) ≃ Fin d)
    (σ : Equiv.Perm (Fin m → Fin 2)) (x : Fin m → Fin 2) :
    permGate enc σ *ᵥ Pi.single (enc x) 1 = Pi.single (enc (σ x)) 1 := by
  funext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, permGate_apply, Equiv.symm_apply_apply,
    Pi.single_apply]

end AxQM.Concrete
