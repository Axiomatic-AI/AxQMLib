/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CSSStabilizerSubgroup

/-!
# Concrete: the elements `X^v Z^u` of the CSS stabilizer and its genuineness `-I ∉ S`

This file continues the formalisation of
**Nielsen & Chuang, Exercise 10.51** — *the check matrix (10.106) is the stabilizer of the CSS code
`CSS(C₁, C₂)`, and Theorem 10.8 gives `t`-qubit correction* (p. 470). Where
`AxQM/Concrete/CSSStabilizerSubgroup.lean` assembled the `X`-type / `Z`-type generators into the
abelian subgroup `cssStabilizer C₁ C₂ = ⟨X^v (v ∈ C₂), Z^u (u ∈ C₁⊥)⟩`, this file pins down
**what its elements are**
and uses that to prove the stabilizer is **genuine** — `-I ∉ S` — the standing
hypothesis of Nielsen & Chuang Proposition 10.3 / Theorem 10.8 that the code
projector, distance, and correction all need.

## The element normal form (`mem_cssStabilizer_iff`)

Because `C₂ ≤ C₁`, every `X`-type generator commutes *exactly* (not merely up to sign) with every
`Z`-type generator — the check-matrix condition `v ⬝ᵥ u = 0` makes them commute in the group, with
no residual phase (`xPauli_commute_zPauli`). Together with the involutivity of the generators
(`xPauli_mul_self`, `zPauli_mul_self`) and the group laws
`X^v X^{v'} = X^{v+v'}` (`xPauli_mul_xPauli`), `Z^u Z^{u'} = Z^{u+u'}` (`zPauli_mul_zPauli`), this
forces **every** element of `S` into the normal form

`p = X^v Z^u`   with `v ∈ C₂`, `u ∈ C₁⊥`   (`mem_cssStabilizer_iff`).

Concretely `S` is the explicit subgroup `cssStabSet` (underlying set
`{X^v Z^u : v ∈ C₂, u ∈ C₁⊥}`); the two descriptions coincide because that set already contains
the generators and is closed under group operations. This normal form is the workhorse for the
normalizer / distance analysis and the code-space dimension, which both reason about stabilizer
elements through their `(v, u)` data.

## Genuineness (`negOne_notMem_cssStabilizer`)

`-I = i²·I` is the phase-`2`, string-`0` element `(2, 0)`. If it lay in `S` it would equal some
`X^v Z^u`; comparing the underlying Pauli strings gives `X^v Z^u = I` as a *string*, and since at a
qubit `X^v Z^u` acts as `I` only when `vₖ = uₖ = 0` (the product index `pauliMul` of an `X`-bit and
a `Z`-bit vanishes only for `0, 0`), this forces `v = 0` and `u = 0`. But then `X^0 Z^0 = I` has
phase `0 ≠ 2`, a contradiction. So `-I ∉ S`: the CSS check matrix (10.106) defines a **genuine**
stabilizer code, exactly as N&C require before invoking Theorem 10.8.

-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The generators at the zero support are the identity -/

/-- **`X^0 = I` as a Pauli string**: the `X`-type string of the zero support vector is the identity
Pauli string. Every check bit is `if 0 = 1 then 1 else 0 = 0`. -/
@[simp]
theorem xString_zero : xString (0 : Fin n → ZMod 2) = 0 := by
  funext k; simp only [xString, Pi.zero_apply, ite_eq_right (by decide : ¬ (0 : ZMod 2) = 1)]

/-- **`Z^0 = I` as a Pauli string**: the `Z`-type string of the zero support vector is the identity
Pauli string. -/
@[simp]
theorem zString_zero : zString (0 : Fin n → ZMod 2) = 0 := by
  funext k; simp only [zString, Pi.zero_apply, ite_eq_right (by decide : ¬ (0 : ZMod 2) = 1)]

/-- **`X^0 = 1` in the Pauli group**: the `X`-type generator at the zero support is the group
identity (phase `0`, identity string). -/
@[simp]
theorem xPauli_zero : xPauli (0 : Fin n → ZMod 2) = 1 :=
  PauliGroup.ext PauliGroup.one_phase.symm
    (by rw [xPauli]; exact xString_zero.trans PauliGroup.one_idx.symm)

/-- **`Z^0 = 1` in the Pauli group**: the `Z`-type generator at the zero support is the group
identity. -/
@[simp]
theorem zPauli_zero : zPauli (0 : Fin n → ZMod 2) = 1 :=
  PauliGroup.ext PauliGroup.one_phase.symm
    (by rw [zPauli]; exact zString_zero.trans PauliGroup.one_idx.symm)

/-! ### Multiplying two generators of the same type -/

/-- **Product index of two `X`-type strings**: `X^v ⊙ X^{v'} = X^{v+v'}`. At each qubit both factors
are `X`-bits (`0` or `1`), and `pauliMul` of two such is again an `X`-bit, `1` exactly when the bits
differ — i.e. the mod-`2` sum. -/
theorem pauliMulIndex_xString_xString (v v' : Fin n → ZMod 2) :
    pauliMulIndex (xString v) (xString v') = xString (v + v') := by
  funext k
  have h : ∀ a b : ZMod 2,
      pauliMul (if a = 1 then (1 : Fin 4) else 0) (if b = 1 then (1 : Fin 4) else 0)
        = if a + b = 1 then (1 : Fin 4) else 0 := by decide
  simpa only [pauliMulIndex, xString, Pi.add_apply] using h (v k) (v' k)

/-- **Two `X`-type strings multiply with no phase**: `phasePow (X^v) (X^{v'}) = 0`, since the
single-qubit product `σ_a σ_b` of two `X`-bit Paulis carries no `iˢ` factor. -/
theorem phasePow_xString_xString (v v' : Fin n → ZMod 2) :
    phasePow (xString v) (xString v') = 0 := by
  refine Finset.sum_eq_zero (fun k _ => ?_)
  have h : ∀ a b : ZMod 2,
      singlePhasePow (if a = 1 then (1 : Fin 4) else 0) (if b = 1 then (1 : Fin 4) else 0) = 0 := by
    decide
  simpa only [xString] using h (v k) (v' k)

/-- **The `X`-type generators multiply additively in the group**: `X^v X^{v'} = X^{v+v'}`. The index
is `X^{v+v'}` (`pauliMulIndex_xString_xString`) and the phase is `0`
(`phasePow_xString_xString`), so the two Pauli-group elements agree. -/
theorem xPauli_mul_xPauli (v v' : Fin n → ZMod 2) : xPauli v * xPauli v' = xPauli (v + v') := by
  refine PauliGroup.ext ?_ ?_
  · simp only [PauliGroup.mul_phase, xPauli, phasePow_xString_xString, add_zero]
  · rw [PauliGroup.mul_idx]; exact pauliMulIndex_xString_xString v v'

/-- **Product index of two `Z`-type strings**: `Z^u ⊙ Z^{u'} = Z^{u+u'}`, the mod-`2` sum. -/
theorem pauliMulIndex_zString_zString (u u' : Fin n → ZMod 2) :
    pauliMulIndex (zString u) (zString u') = zString (u + u') := by
  funext k
  have h : ∀ a b : ZMod 2,
      pauliMul (if a = 1 then (3 : Fin 4) else 0) (if b = 1 then (3 : Fin 4) else 0)
        = if a + b = 1 then (3 : Fin 4) else 0 := by decide
  simpa only [pauliMulIndex, zString, Pi.add_apply] using h (u k) (u' k)

/-- **Two `Z`-type strings multiply with no phase**: `phasePow (Z^u) (Z^{u'}) = 0`. -/
theorem phasePow_zString_zString (u u' : Fin n → ZMod 2) :
    phasePow (zString u) (zString u') = 0 := by
  refine Finset.sum_eq_zero (fun k _ => ?_)
  have h : ∀ a b : ZMod 2,
      singlePhasePow (if a = 1 then (3 : Fin 4) else 0) (if b = 1 then (3 : Fin 4) else 0) = 0 := by
    decide
  simpa only [zString] using h (u k) (u' k)

/-- **The `Z`-type generators multiply additively in the group**: `Z^u Z^{u'} = Z^{u+u'}`. -/
theorem zPauli_mul_zPauli (u u' : Fin n → ZMod 2) : zPauli u * zPauli u' = zPauli (u + u') := by
  refine PauliGroup.ext ?_ ?_
  · simp only [PauliGroup.mul_phase, zPauli, phasePow_zString_zString, add_zero]
  · rw [PauliGroup.mul_idx]; exact pauliMulIndex_zString_zString u u'

/-! ### The generators are involutions -/

/-- **`X^v` is an involution**: `X^v X^v = 1`. In characteristic `2` the support sum `v + v = 0`, so
`X^v X^v = X^{v+v} = X^0 = 1`. -/
theorem xPauli_mul_self (v : Fin n → ZMod 2) : xPauli v * xPauli v = 1 := by
  rw [xPauli_mul_xPauli, show v + v = 0 from funext fun k => CharTwo.add_self_eq_zero (v k),
    xPauli_zero]

/-- **`Z^u` is an involution**: `Z^u Z^u = 1`. -/
theorem zPauli_mul_self (u : Fin n → ZMod 2) : zPauli u * zPauli u = 1 := by
  rw [zPauli_mul_zPauli, show u + u = 0 from funext fun k => CharTwo.add_self_eq_zero (u k),
    zPauli_zero]

/-- **The inverse of `X^v` is `X^v`** (it is an involution). -/
theorem xPauli_inv (v : Fin n → ZMod 2) : (xPauli v)⁻¹ = xPauli v :=
  inv_eq_of_mul_eq_one_left (xPauli_mul_self v)

/-- **The inverse of `Z^u` is `Z^u`** (it is an involution). -/
theorem zPauli_inv (u : Fin n → ZMod 2) : (zPauli u)⁻¹ = zPauli u :=
  inv_eq_of_mul_eq_one_left (zPauli_mul_self u)

/-! ### The CSS stabilizer as the explicit set of `X^v Z^u` -/

/-- **The CSS stabilizer described explicitly** as the subgroup `{X^v Z^u : v ∈ C₂, u ∈ C₁⊥}` of the
Pauli group (for classical codes `C₂ ≤ C₁`). This set really is a subgroup: it contains the
identity `X^0 Z^0 = 1`; it is closed under multiplication, since a `Z`-type factor commutes past an
`X`-type factor (`xPauli_commute_zPauli`, valid as `v' ⬝ᵥ u = 0`) and the same-type generators add
their supports (`xPauli_mul_xPauli`, `zPauli_mul_zPauli`), giving `X^v Z^u · X^{v'} Z^{u'} =
X^{v+v'} Z^{u+u'}`; and it is closed under inverses, since each generator is an involution
(`xPauli_inv`, `zPauli_inv`) and the two commute. Proving `cssStabilizer C₁ C₂ = cssStabSet C₁ C₂`
(`mem_cssStabilizer_iff`) turns membership of the abstract closure into this concrete `(v, u)`
normal form. -/
def cssStabSet (C₁ C₂ : LinearCode (ZMod 2) (Fin n)) (hsub : C₂ ≤ C₁) :
    Subgroup (PauliGroup n) where
  carrier := {p | ∃ v ∈ C₂, ∃ u ∈ C₁.dual, p = xPauli v * zPauli u}
  one_mem' := ⟨0, C₂.zero_mem, 0, C₁.dual.zero_mem, by rw [xPauli_zero, zPauli_zero, mul_one]⟩
  mul_mem' := by
    rintro p q ⟨v, hv, u, hu, rfl⟩ ⟨v', hv', u', hu', rfl⟩
    refine ⟨v + v', C₂.add_mem hv hv', u + u', C₁.dual.add_mem hu hu', ?_⟩
    have hc : zPauli u * xPauli v' = xPauli v' * zPauli u :=
      ((xPauli_commute_zPauli hsub hv' hu).eq).symm
    calc xPauli v * zPauli u * (xPauli v' * zPauli u')
        = xPauli v * (zPauli u * xPauli v') * zPauli u' := by rw [mul_assoc, mul_assoc, mul_assoc]
      _ = xPauli v * (xPauli v' * zPauli u) * zPauli u' := by rw [hc]
      _ = xPauli v * xPauli v' * (zPauli u * zPauli u') := by rw [mul_assoc, mul_assoc, mul_assoc]
      _ = xPauli (v + v') * zPauli (u + u') := by rw [xPauli_mul_xPauli, zPauli_mul_zPauli]
  inv_mem' := by
    rintro p ⟨v, hv, u, hu, rfl⟩
    exact ⟨v, hv, u, hu, by
      rw [_root_.mul_inv_rev, xPauli_inv, zPauli_inv, (xPauli_commute_zPauli hsub hv hu).eq]⟩

/-- **The CSS stabilizer element normal form** (Nielsen & Chuang, Exercise 10.51): for classical
binary codes `C₂ ≤ C₁`, a Pauli-group element lies in `cssStabilizer C₁ C₂` **iff** it is
`X^v Z^u` for some codeword `v ∈ C₂` and dual codeword `u ∈ C₁⊥`. The `←` direction is generator
membership and closure under products; the `→` direction is `Subgroup.closure_le` into the explicit
subgroup `cssStabSet` (whose underlying set is exactly this set of `X^v Z^u`), which contains both
generator families. This is the concrete description of the stabilizer of the check matrix (10.106):
its `X`
part ranges over `C₂` (the row space of `H(C₂⊥)`) and its `Z` part over `C₁⊥` (the row space of
`H(C₁)`). -/
theorem mem_cssStabilizer_iff {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁)
    {p : PauliGroup n} :
    p ∈ cssStabilizer C₁ C₂ ↔ ∃ v ∈ C₂, ∃ u ∈ C₁.dual, p = xPauli v * zPauli u := by
  constructor
  · intro hp
    refine (Subgroup.closure_le (cssStabSet C₁ C₂ hsub)).mpr ?_ hp
    rintro x (⟨v, hv, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact ⟨v, hv, 0, C₁.dual.zero_mem, by rw [zPauli_zero, mul_one]⟩
    · exact ⟨0, C₂.zero_mem, u, hu, by rw [xPauli_zero, one_mul]⟩
  · rintro ⟨v, hv, u, hu, rfl⟩
    exact mul_mem (xPauli_mem_cssStabilizer hv) (zPauli_mem_cssStabilizer hu)

/-! ### The CSS stabilizer is genuine: `-I ∉ S` -/

/-- **The CSS check matrix (10.106) defines a genuine stabilizer: `-I ∉ S`** (Nielsen & Chuang,
Exercise 10.51). For classical binary codes `C₂ ≤ C₁`, the element `-I = (2, 0)` does not lie in
`cssStabilizer C₁ C₂`. If it did, the normal form (`mem_cssStabilizer_iff`) would write it as
`X^v Z^u`; comparing Pauli strings gives `pauliMulIndex (X^v) (Z^u) = 0`, and at each qubit the
product of an `X`-bit and a `Z`-bit is the identity only when both bits vanish, forcing `v = 0` and
`u = 0`. But then `X^0 Z^0 = 1` has phase `0`, whereas `-I` has phase `2` — contradiction. This is
the standing hypothesis `-I ∉ S` of Proposition 10.3 / Theorem 10.8 (needed for the code projector,
the distance bound, and the error-correction argument). -/
theorem negOne_notMem_cssStabilizer {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁) :
    PauliGroup.negOne n ∉ cssStabilizer C₁ C₂ := by
  intro hmem
  obtain ⟨v, hv, u, hu, heq⟩ := (mem_cssStabilizer_iff hsub).mp hmem
  have h0 : pauliMulIndex (xString v) (zString u) = 0 := by
    have h := congrArg PauliGroup.idx heq
    rw [PauliGroup.mul_idx] at h
    have hxv : (xPauli v).idx = xString v := rfl
    have hzu : (zPauli u).idx = zString u := rfl
    have hn0 : (PauliGroup.negOne n).idx = 0 := rfl
    rw [hxv, hzu, hn0] at h
    exact h.symm
  have hiff : ∀ a b : ZMod 2,
      pauliMul (if a = 1 then (1 : Fin 4) else 0) (if b = 1 then (3 : Fin 4) else 0) = 0
        ↔ a = 0 ∧ b = 0 := by decide
  have key : ∀ k, v k = 0 ∧ u k = 0 := by
    intro k
    have hk : pauliMul (xString v k) (zString u k) = 0 := congrFun h0 k
    rw [xString, zString] at hk
    exact (hiff (v k) (u k)).mp hk
  obtain ⟨rfl, rfl⟩ : v = 0 ∧ u = 0 := ⟨funext fun k => (key k).1, funext fun k => (key k).2⟩
  rw [xPauli_zero, zPauli_zero, mul_one] at heq
  have hph := congrArg PauliGroup.phase heq
  rw [PauliGroup.one_phase, show (PauliGroup.negOne n).phase = 2 from rfl] at hph
  exact absurd hph (by decide)

end AxQM.Concrete
