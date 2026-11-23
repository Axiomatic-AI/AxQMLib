/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CSSCode

/-!
# Pauli strings stabilize CSS coset states

This file records the general **stabilizer** facts for the CSS coset states of
`AxQM.Postulates.API.CSSCode`: for a binary code `C₂ = LinearCode (ZMod 2) ι` and a
codeword register `bitReg ι`, when do the local Pauli strings `X^v` (`bitString v`) and `Z^u`
(`phaseString u`) fix the standard coset state `|x + C₂⟩` (`cssStdState C₂ x`)?

The two conditions are exactly the classical-coding ones behind a CSS stabilizer:

* **`X^v` stabilizes `|x + C₂⟩` when `v ∈ C₂`.** Translating the register by a codeword `v ∈ C₂`
  permutes the coset `x + C₂` onto itself, so `X^v |x + C₂⟩ = |x + v + C₂⟩ = |x + C₂⟩`
  (`cssStdState_add_mem` + `bitString_op_cssStdState_vec`).
* **`Z^u` stabilizes `|x + C₂⟩` when `u ⊥ x` and `u ⊥ C₂`.** The diagonal sign `Z^u` multiplies
  `|x + y⟩` by `(-1)^{u·(x+y)}`; if `u · x = 0` and `u · y = 0` for every `y ∈ C₂` then every
  sign is `+1`, so `Z^u |x + C₂⟩ = |x + C₂⟩` (`phaseString_op_cssStdState_eq_self`).

Both are also stated in the `Evolution.HasEigenstate 1` form (`U |ψ⟩ = |ψ⟩`, N&C's
"eigenvalue-one eigenstate" characterisation of stabilization), e.g.
`(bitString v).HasEigenstate 1 (cssStdState C₂ x)`. These are the ingredients behind the
Steane-code stabilizer generators of Nielsen & Chuang, Exercise 10.32
(`AxQM.NC.Ch10.Exercise10_32`).
-/

namespace AxQM

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]

/-- **Coset invariance of the standard CSS state.** Shifting the coset representative by a codeword
`v ∈ C₂` leaves the standard coset state unchanged, `|x + v + C₂⟩ = |x + C₂⟩`: translation by
`v ∈ C₂` is a bijection of `C₂`, so it merely reindexes the uniform superposition over the coset.
This is the state-level form of "`cssStdState C₂ x` depends only on the coset `x + C₂`". -/
theorem cssStdState_add_mem {v : ι → ZMod 2} (hv : v ∈ C₂) (x : ι → ZMod 2) :
    cssStdState C₂ (x + v) = cssStdState C₂ x := by
  apply PureState.ext
  rw [cssStdState_vec, cssStdState_vec]
  congr 1
  rw [← Equiv.sum_comp (Equiv.addLeft (⟨v, hv⟩ : ↥C₂))
    (fun y : ↥C₂ => regBasis ι (x + (↑y : ι → ZMod 2)))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  congr 1
  simp only [Equiv.coe_addLeft, Submodule.coe_add]
  abel

/-- **Action of the bit-flip string on a standard CSS state**: `X^v |x + C₂⟩ = |x + v + C₂⟩`.
Applying `bitString v` translates every basis ket `|x + y⟩` of the superposition to `|x + y + v⟩`,
which is the standard coset state at representative `x + v`. -/
theorem bitString_op_cssStdState_vec (v x : ι → ZMod 2) :
    (bitString v).op (cssStdState C₂ x).vec = (cssStdState C₂ (x + v)).vec := by
  rw [cssStdState_vec, Evolution.op_smul_sum, cssStdState_vec]
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [bitString_op_regBasis, add_right_comm]

/-- **`X^v` fixes `|x + C₂⟩` when `v ∈ C₂`** (in terms of state vectors): `X^v |x + C₂⟩ = |x + C₂⟩`.
Combines the translation action `bitString_op_cssStdState_vec` with coset invariance
`cssStdState_add_mem`. -/
theorem bitString_op_cssStdState_eq_self {v : ι → ZMod 2} (hv : v ∈ C₂) (x : ι → ZMod 2) :
    (bitString v).op (cssStdState C₂ x).vec = (cssStdState C₂ x).vec := by
  rw [bitString_op_cssStdState_vec, cssStdState_add_mem C₂ hv]

/-- **`X^v` stabilizes `|x + C₂⟩` when `v ∈ C₂`.** The eigenvalue-one form: the bit-flip
string of a codeword `v ∈ C₂` is an eigenvalue-`1` eigenstate on the standard coset state. This is
the CSS X-type stabilizer condition (a stabilizer generator has X's on a dual-code word). -/
theorem bitString_hasEigenstate_one_cssStdState {v : ι → ZMod 2} (hv : v ∈ C₂) (x : ι → ZMod 2) :
    (bitString v).HasEigenstate 1 (cssStdState C₂ x) := by
  change (bitString v).op (cssStdState C₂ x).vec = (1 : ℂ) • (cssStdState C₂ x).vec
  rw [one_smul, bitString_op_cssStdState_eq_self C₂ hv]

/-- **`Z^u` fixes `|x + C₂⟩` when `u ⊥ x` and `u ⊥ C₂`** (in terms of state vectors): if `u · x = 0`
and `u · y = 0` for every `y ∈ C₂`, then the diagonal sign string `Z^u` acts as the identity on
`|x + C₂⟩`. Each ket `|x + y⟩` gets the sign `(-1)^{u·(x+y)} = (-1)^{u·x + u·y} = (-1)^0 = +1`. -/
theorem phaseString_op_cssStdState_eq_self {u x : ι → ZMod 2}
    (hux : u ⬝ᵥ x = 0) (huy : ∀ y ∈ C₂, u ⬝ᵥ y = 0) :
    (phaseString u).op (cssStdState C₂ x).vec = (cssStdState C₂ x).vec := by
  rw [cssStdState_vec, Evolution.op_smul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [phaseString_op_regBasis]
  have hxy : u ⬝ᵥ (x + (↑y : ι → ZMod 2)) = 0 := by
    rw [dotProduct_add, hux, huy _ y.2, add_zero]
  rw [hxy, ZMod.val_zero, pow_zero, one_smul]

/-- **`Z^u` stabilizes `|x + C₂⟩` when `u ⊥ x` and `u ⊥ C₂`.** The eigenvalue-one form: a
phase-flip string whose support word `u` is orthogonal to the representative `x` and to every
codeword of `C₂` is an eigenvalue-`1` eigenstate on the standard coset state. This is the CSS
Z-type stabilizer condition. -/
theorem phaseString_hasEigenstate_one_cssStdState {u x : ι → ZMod 2}
    (hux : u ⬝ᵥ x = 0) (huy : ∀ y ∈ C₂, u ⬝ᵥ y = 0) :
    (phaseString u).HasEigenstate 1 (cssStdState C₂ x) := by
  change (phaseString u).op (cssStdState C₂ x).vec = (1 : ℂ) • (cssStdState C₂ x).vec
  rw [one_smul, phaseString_op_cssStdState_eq_self C₂ hux huy]

/-- **`Z^u` stabilizes `|x + C₂⟩` when `u ∈ C₁⊥` and `C₂ ≤ C₁`** (the dual-code form). For a
supercode `C₂ ≤ C₁`, a phase-flip string `Z^u` whose support word `u` lies in the dual `C₁⊥` fixes
every codeword `|x + C₂⟩` with representative `x ∈ C₁`: from `u ∈ C₁⊥` and `x ∈ C₁` we get `u ⊥ x`,
and from `C₂ ⊆ C₁` we get `u ⊥ C₂`, so `phaseString_hasEigenstate_one_cssStdState` applies. This is
the Z-type stabilizer condition of the CSS check matrix (Nielsen & Chuang, Eq. (10.106)): the
phase-flip generators come from `H(C₁)`, whose row space is `C₁⊥`, and they fix the `CSS(C₁, C₂)`
codewords. It is the dual companion of the X-type `bitString_hasEigenstate_one_cssStdState`. -/
theorem phaseString_hasEigenstate_one_cssStdState_of_mem_dual {C₁ : LinearCode (ZMod 2) ι}
    (hsub : C₂ ≤ C₁) {u x : ι → ZMod 2} (hu : u ∈ C₁.dual) (hx : x ∈ C₁) :
    (phaseString u).HasEigenstate 1 (cssStdState C₂ x) := by
  refine phaseString_hasEigenstate_one_cssStdState C₂ ?_ ?_
  · rw [dotProduct_comm]
    exact LinearCode.mem_dual_iff.mp hu x hx
  · intro y hy
    rw [dotProduct_comm]
    exact LinearCode.mem_dual_iff.mp hu y (hsub hy)

/-- **Action of `X^v` on a standard CSS state** (pure-state form):
`X^v |x + C₂⟩ = |x + v + C₂⟩`. The `evolvePure` lift of the identity
`bitString_op_cssStdState_vec`: translating by `v` moves the coset representative `x` to `x + v`.
When `v ∈ C₂` this fixes the codeword (`bitString_hasEigenstate_one_cssStdState`); when `v ∉ C₂` it
is the **coset swap** by which the logical `X̄ = X^{𝟙}` exchanges the two logical codewords of a CSS
code (Nielsen & Chuang, Exercise 10.52). -/
theorem bitString_evolvePure_cssStdState (v x : ι → ZMod 2) :
    (bitString v).evolvePure (cssStdState C₂ x) = cssStdState C₂ (x + v) := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, bitString_op_cssStdState_vec]

/-- **`X^v` swaps the two logical cosets of a CSS code** (pure-state form): when
`v ⊕ 𝟙 ∈ C₂`, the bit-flip string `X^v` translates the standard coset state `|x + C₂⟩` to
`|(x ⊕ 𝟙) + C₂⟩`. It combines the raw translation `bitString_evolvePure_cssStdState`
(`X^v : |x + C₂⟩ ↦ |x + v + C₂⟩`) with coset invariance `cssStdState_add_mem` (`x + v` and `x + 𝟙`
name the same coset, their difference `v + 𝟙 ∈ C₂`). This is the general logical-`X̄` codeword swap
of a CSS code: the `v = 𝟙` case is the uniform `X̄ = X₁…Xₙ` of (10.107); any other representative
`v` with `v ⊕ 𝟙 ∈ C₂` (e.g. the standard-form `X̄`, N&C Exercise 10.55) gives the *same* swap. -/
theorem bitString_evolvePure_cssStdState_swap {v : ι → ZMod 2} (hv : v + 1 ∈ C₂)
    (x : ι → ZMod 2) :
    (bitString v).evolvePure (cssStdState C₂ x) = cssStdState C₂ (x + 1) := by
  rw [bitString_evolvePure_cssStdState]
  have hx : x + v = (x + 1) + (v + 1) := by
    have h2 : (1 : ι → ZMod 2) + 1 = 0 := by
      funext i; simp only [Pi.add_apply, Pi.one_apply, Pi.zero_apply]; decide
    rw [add_add_add_comm, h2, add_zero]
  rw [hx, cssStdState_add_mem C₂ hv]

/-- **Action of `Z^u` on a standard CSS state when `u ⊥ C₂`** (in terms of state vectors): if `u` is
orthogonal to every codeword of `C₂`, the diagonal string `Z^u` multiplies `|x + C₂⟩` by the
*uniform* sign `(-1)^{u·x}`. Each ket `|x + y⟩` picks up `(-1)^{u·(x+y)} = (-1)^{u·x + u·y} =
(-1)^{u·x}` because `u·y = 0`, so the sign is constant across the superposition and factors out.
Generalises `phaseString_op_cssStdState_eq_self` (the `u·x = 0`, sign `+1` special case). -/
theorem phaseString_op_cssStdState_vec_smul {u : ι → ZMod 2} (x : ι → ZMod 2)
    (huy : ∀ y ∈ C₂, u ⬝ᵥ y = 0) :
    (phaseString u).op (cssStdState C₂ x).vec
      = (-1 : ℂ) ^ (u ⬝ᵥ x).val • (cssStdState C₂ x).vec := by
  rw [cssStdState_vec, Evolution.op_smul_sum, smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [phaseString_op_regBasis, dotProduct_add, huy _ y.2, add_zero]

/-- **`Z^u` acts as the sign `(-1)^{u·x}` on `|x + C₂⟩` when `u ⊥ C₂`.** The eigenstate form:
if `u` is orthogonal to every codeword of `C₂`, then `Z^u` is an eigenvalue-`(-1)^{u·x}` eigenstate
on the standard coset state. Generalises `phaseString_hasEigenstate_one_cssStdState` (the `u ⊥ x`,
eigenvalue `+1` special case) to the sign that distinguishes the two logical cosets — the mechanism
by which `Z̄ = Z^{𝟙}` acts as logical `Z` on a CSS code (Nielsen & Chuang, Exercise 10.52). -/
theorem phaseString_hasEigenstate_cssStdState {u : ι → ZMod 2} (x : ι → ZMod 2)
    (huy : ∀ y ∈ C₂, u ⬝ᵥ y = 0) :
    (phaseString u).HasEigenstate ((-1 : ℂ) ^ (u ⬝ᵥ x).val) (cssStdState C₂ x) :=
  phaseString_op_cssStdState_vec_smul C₂ x huy

end AxQM
