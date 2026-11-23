/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrixSymplectic
import ToMathlib.InformationTheory.Coding.DualCode

/-!
# Concrete: the CSS stabilizer generators `X^v`, `Z^u` and the check-matrix (10.106) commutativity

This file begins the formalisation of
**Nielsen & Chuang, Exercise 10.51** — *the check matrix (10.106) is the stabilizer of the CSS code
`CSS(C₁, C₂)`, and Theorem 10.8 gives `t`-qubit correction* (p. 470). This file builds the
two families of stabilizer generators that make up the CSS check matrix

`[ H(C₂⊥)   0     ]`
`[   0    H(C₁)   ]`      (eq. (10.106))

as honest `n`-qubit Pauli strings and settles their **commutativity** — the condition N&C verifies
by hand (`H(C₂⊥) H(C₁)ᵀ = 0`) to see that the check matrix defines a genuine stabilizer code.

Theorem 10.8 is in `AxQM/Concrete/StabilizerErrorCorrection.lean`.

## The two generator families

A CSS stabilizer generator is a **pure `X`-type** or **pure `Z`-type** Pauli string, built from a
binary support vector:

* `xString v` — the **`X`-type** Pauli string `X^v = X^{v₁} ⊗ ⋯ ⊗ X^{vₙ}`, with an `X` (Pauli
  index `1`) on each qubit `k` where `v k = 1` and the identity (index `0`) elsewhere. Its
  check-matrix row is `(v | 0)` (`checkRow_xString`): all `X`-part, no `Z`-part.
* `zString u` — the **`Z`-type** Pauli string `Z^u = Z^{u₁} ⊗ ⋯ ⊗ Z^{uₙ}`, with a `Z` (Pauli index
  `3`) where `u k = 1`. Its check-matrix row is `(0 | u)` (`checkRow_zString`): all `Z`-part.

The `X`-type rows of the check matrix (10.106) are the rows of `H(C₂⊥)` (a basis of `C₂`), the
`Z`-type rows those of `H(C₁)` (a basis of `C₁⊥`); every generator is one of these two forms.

## Commutativity (the check-matrix condition)

Two Pauli strings commute iff the **binary symplectic pairing** of their check rows vanishes mod `2`
(Exercise 10.33, `pauliString_commute_iff_symplecticForm`). For the CSS generators this pairing is a
plain dot product of the support vectors:

* `symplecticForm_xString_zString` — `⟨r(X^v), r(Z^u)⟩ = v ⬝ᵥ u`: an `X`-type and a `Z`-type string
  pair to the dot product of their supports;
* `symplecticForm_xString_xString`, `symplecticForm_zString_zString` — two `X`-type (resp. two
  `Z`-type) strings always pair to `0`.

Hence (`pauliString_xString_commute_zString_iff`) `X^v` and `Z^u` commute iff `v ⬝ᵥ u = 0`, while
any two `X`-type or any two `Z`-type strings commute unconditionally. The upshot for the CSS check
matrix is `pauliString_xString_commute_zString_of_mem_dual`: for classical codes `C₂ ≤ C₁`, any
`X`-type generator `X^g` (`g ∈ C₂`) commutes with any `Z`-type generator `Z^h` (`h ∈ C₁⊥`), because
`g ∈ C₁`
and `h ∈ C₁⊥` force `g ⬝ᵥ h = 0` — the mod-2 identity `H(C₂⊥) H(C₁)ᵀ = 0` (which reduces to
`H(C₁) G(C₂)ᵀ = 0` since `C₂ ⊆ C₁`). All generators therefore commute, so the check matrix (10.106)
defines a genuine (abelian) stabilizer.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The `X`-type and `Z`-type generator strings -/

/-- The **`X`-type Pauli string** `X^v = X^{v₁} ⊗ ⋯ ⊗ X^{vₙ}` of a binary support vector
`v : Fin n → ZMod 2`: the Pauli string with an `X` (index `1`) on each qubit `k` where `v k = 1`,
and the identity (index `0`) elsewhere. These are the `X`-type stabilizer generators of a CSS
code — the rows of the top block `H(C₂⊥)` of the check matrix (10.106). -/
def xString (v : Fin n → ZMod 2) : Fin n → Fin 4 := fun k => if v k = 1 then 1 else 0

/-- The **`Z`-type Pauli string** `Z^u = Z^{u₁} ⊗ ⋯ ⊗ Z^{uₙ}` of a binary support vector
`u : Fin n → ZMod 2`: the Pauli string with a `Z` (index `3`) on each qubit `k` where `u k = 1`,
and the identity (index `0`) elsewhere. These are the `Z`-type stabilizer generators of a CSS
code — the rows of the bottom block `H(C₁)` of the check matrix (10.106). -/
def zString (u : Fin n → ZMod 2) : Fin n → Fin 4 := fun k => if u k = 1 then 3 else 0

/-- **The check bits of `X^v` at a qubit**: `pauliBit (X^v)ₖ = (vₖ, 0)`. On qubit `k` the string is
`X` (bits `(1,0)`) when `vₖ = 1` and `I` (bits `(0,0)`) when `vₖ = 0`; either way the `X`-bit is
`vₖ` and the `Z`-bit is `0`. A two-element `decide` on `vₖ : ZMod 2`. -/
theorem pauliBit_xString (v : Fin n → ZMod 2) (k : Fin n) : pauliBit (xString v k) = (v k, 0) := by
  have h : ∀ b : ZMod 2, pauliBit (if b = 1 then (1 : Fin 4) else 0) = (b, 0) := by decide
  simpa only [xString] using h (v k)

/-- **The check bits of `Z^u` at a qubit**: `pauliBit (Z^u)ₖ = (0, uₖ)`. On qubit `k` the string is
`Z` (bits `(0,1)`) when `uₖ = 1` and `I` (bits `(0,0)`) when `uₖ = 0`; either way the `X`-bit is `0`
and the `Z`-bit is `uₖ`. -/
theorem pauliBit_zString (u : Fin n → ZMod 2) (k : Fin n) : pauliBit (zString u k) = (0, u k) := by
  have h : ∀ b : ZMod 2, pauliBit (if b = 1 then (3 : Fin 4) else 0) = (0, b) := by decide
  simpa only [zString] using h (u k)

/-- **The check-matrix row of `X^v` is `(v | 0)`**: `r(X^v) = (v, 0)`, all `X`-part and no `Z`-part.
The `X`-block is the support vector `v`, matching the top-left block of the CSS check matrix
(10.106). -/
@[simp]
theorem checkRow_xString (v : Fin n → ZMod 2) : checkRow (xString v) = (v, 0) := by
  ext k <;> simp [checkRow, pauliBit_xString]

/-- **The check-matrix row of `Z^u` is `(0 | u)`**: `r(Z^u) = (0, u)`, all `Z`-part and no `X`-part.
The `Z`-block is the support vector `u`, matching the bottom-right block of the CSS check matrix
(10.106). -/
@[simp]
theorem checkRow_zString (u : Fin n → ZMod 2) : checkRow (zString u) = (0, u) := by
  ext k <;> simp [checkRow, pauliBit_zString]

/-! ### The symplectic pairing of the CSS generators -/

/-- **`X`-type against `Z`-type: the symplectic pairing is the dot product of the supports.**
`⟨r(X^v), r(Z^u)⟩ = v ⬝ᵥ u`. Since `r(X^v) = (v, 0)` and `r(Z^u) = (0, u)`, the twisted inner
product `Σₖ (x_gₖ z_hₖ + z_gₖ x_hₖ)` collapses to `Σₖ vₖ uₖ = v ⬝ᵥ u` (the second summand vanishes,
both operands being `0`). -/
theorem symplecticForm_xString_zString (v u : Fin n → ZMod 2) :
    symplecticForm (checkVec (xString v)) (checkVec (zString u)) = v ⬝ᵥ u := by
  rw [symplecticForm_checkVec_eq_checkSymplectic, checkRow_xString, checkRow_zString,
    checkSymplectic_apply]
  simp only [Pi.zero_apply, mul_zero, add_zero, dotProduct]

/-- **Two `X`-type strings always pair to `0`.** `⟨r(X^v), r(X^v')⟩ = 0`: both check rows have a
zero `Z`-part, so the twisted inner product `Σₖ (vₖ · 0 + 0 · v'ₖ)` vanishes term by term. -/
theorem symplecticForm_xString_xString (v v' : Fin n → ZMod 2) :
    symplecticForm (checkVec (xString v)) (checkVec (xString v')) = 0 := by
  rw [symplecticForm_checkVec_eq_checkSymplectic, checkRow_xString, checkRow_xString,
    checkSymplectic_apply]
  simp

/-- **Two `Z`-type strings always pair to `0`.** `⟨r(Z^u), r(Z^u')⟩ = 0`: both check rows have a
zero `X`-part, so the twisted inner product `Σₖ (0 · u'ₖ + uₖ · 0)` vanishes term by term. -/
theorem symplecticForm_zString_zString (u u' : Fin n → ZMod 2) :
    symplecticForm (checkVec (zString u)) (checkVec (zString u')) = 0 := by
  rw [symplecticForm_checkVec_eq_checkSymplectic, checkRow_zString, checkRow_zString,
    checkSymplectic_apply]
  simp

/-! ### Commutativity of the CSS generators -/

/-- **`X^v` and `Z^u` commute iff `v ⬝ᵥ u = 0`** (the CSS special case of Exercise 10.33). Combining
the commutation criterion `pauliString_commute_iff_symplecticForm` with the pairing
`symplecticForm_xString_zString`: an `X`-type and a `Z`-type generator commute exactly when their
support vectors are orthogonal over `ZMod 2`. -/
theorem pauliString_xString_commute_zString_iff (v u : Fin n → ZMod 2) :
    Commute (pauliString (xString v)) (pauliString (zString u)) ↔ v ⬝ᵥ u = 0 := by
  rw [pauliString_commute_iff_symplecticForm, symplecticForm_xString_zString]

/-- **Any two `X`-type generators commute.** `X^v` and `X^v'` commute unconditionally, since their
symplectic pairing is `0` (`symplecticForm_xString_xString`). -/
theorem pauliString_xString_commute_xString (v v' : Fin n → ZMod 2) :
    Commute (pauliString (xString v)) (pauliString (xString v')) := by
  rw [pauliString_commute_iff_symplecticForm, symplecticForm_xString_xString]

/-- **Any two `Z`-type generators commute.** `Z^u` and `Z^u'` commute unconditionally, since their
symplectic pairing is `0` (`symplecticForm_zString_zString`). -/
theorem pauliString_zString_commute_zString (u u' : Fin n → ZMod 2) :
    Commute (pauliString (zString u)) (pauliString (zString u')) := by
  rw [pauliString_commute_iff_symplecticForm, symplecticForm_zString_zString]

/-- **The CSS check-matrix commutativity condition `H(C₂⊥) H(C₁)ᵀ = 0`** (Nielsen & Chuang,
Exercise 10.51). For classical binary codes `C₂ ≤ C₁`, every `X`-type generator `X^g` with support a
codeword `g ∈ C₂` commutes with every `Z`-type generator `Z^h` with support a dual codeword
`h ∈ C₁⊥`: because `g ∈ C₂ ⊆ C₁` and `h ∈ C₁⊥`, the dot product `g ⬝ᵥ h = 0` (`mem_dual_iff`), so
`pauliString_xString_commute_zString_iff` gives commutation. This is exactly the condition N&C
verifies — `H(C₂⊥) H(C₁)ᵀ = [H(C₁) G(C₂)]ᵀ = 0` because `C₂ ⊆ C₁` — that makes the check matrix
(10.106) define a genuine (abelian) stabilizer code. -/
theorem pauliString_xString_commute_zString_of_mem_dual {C₁ C₂ : LinearCode (ZMod 2) (Fin n)}
    (hsub : C₂ ≤ C₁) {g h : Fin n → ZMod 2} (hg : g ∈ C₂) (hh : h ∈ C₁.dual) :
    Commute (pauliString (xString g)) (pauliString (zString h)) :=
  (pauliString_xString_commute_zString_iff g h).mpr (LinearCode.mem_dual_iff.mp hh g (hsub hg))

end AxQM.Concrete
