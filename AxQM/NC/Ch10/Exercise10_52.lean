/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_32

/-!
# Nielsen & Chuang, Exercise 10.52 — the Steane-code logical operators `Z̄`, `X̄`

*(N&C §10.4.2 / §10.5.6, eq. (10.107), p. 470.)*

Verify by direct operation on codewords that (10.107) operators act as logical Z and X.

Equation (10.107) defines, for the seven-qubit **Steane code** (the CSS code `CSS(C₁, C₂)` built
from the `[7, 4, 3]` Hamming code `C₁ = C` and its dual `C₂ = C⊥`), the encoded operators

`Z̄ ≡ Z₁Z₂Z₃Z₄Z₅Z₆Z₇`,  `X̄ ≡ X₁X₂X₃X₄X₅X₆X₇`.

On the bit-vector register `bitReg (Fin 7)` these are the uniform Pauli strings `Z^{𝟙}` and `X^{𝟙}`
with support word the all-ones vector `𝟙 = 1111111`, i.e. `steaneLogicalZBar = phaseString 1` and
`steaneLogicalXBar = bitString 1`. The logical basis is the pair of Steane codewords of
Exercise 10.32 (`AxQM.NC.Ch10.Exercise10_32`),

* `steaneLogicalZero = |0_L⟩ = |0 + C₂⟩ = (1/√8) ∑_{y ∈ C₂} |y⟩` (eq. (10.78));
* `steaneLogicalOne  = |1_L⟩ = |𝟙 + C₂⟩ = (1/√8) ∑_{y ∈ C₂} |𝟙 + y⟩` (eq. (10.79)).

## What "acts as logical `Z` / `X`" means, and what this file proves

"Act appropriately, as logical `Z` and `X`" means the operators reproduce, on the codeword basis
`{|0_L⟩, |1_L⟩}`, exactly the single-qubit Pauli action on `{|0⟩, |1⟩}`. We verify this by direct
operation on the codeword superpositions:

* **`Z̄ = Z^{𝟙}` acts as logical `Z`** — diagonal with eigenvalue `(-1)^s` on `|s_L⟩`:
  `Z̄|0_L⟩ = |0_L⟩` (`steaneLogicalZBar_hasEigenstate_logicalZero`, eigenvalue `+1`) and
  `Z̄|1_L⟩ = −|1_L⟩` (`steaneLogicalZBar_hasEigenstate_logicalOne`, eigenvalue `−1`). Mechanism:
  `Z^{𝟙}` multiplies each ket `|x + y⟩` by `(-1)^{𝟙·(x+y)}`, and since every dual codeword `y ∈ C₂`
  has **even weight** (`𝟙 · y = 0`, `Concrete.steaneDualCode_dotProduct_one`), the sign is the
  uniform `(-1)^{𝟙·x}` — `+1` for `|0_L⟩` (weight-`0` representative) and `−1` for `|1_L⟩`
  (weight-`7` representative). As a unitary its eigenvalues `±1` are real, so this equally exhibits
  `Z̄`'s Hermitian/diagonal action.
* **`X̄ = X^{𝟙}` acts as logical `X`** — the codeword swap
  `X̄|0_L⟩ = |1_L⟩` (`steaneLogicalXBar_evolvePure_logicalZero`) and
  `X̄|1_L⟩ = |0_L⟩` (`steaneLogicalXBar_evolvePure_logicalOne`). Mechanism: `X^{𝟙}` translates the
  coset representative by `𝟙`, exchanging the cosets `0 + C₂ ↔ 𝟙 + C₂` (with `𝟙 + 𝟙 = 0`).

Together the four action theorems say `Z̄, X̄` realise the logical Pauli pair `Z, X` on the encoded
qubit — the content of Exercise 10.52. (As with the Shor-code companion Exercise 10.48, the
*operational* action on the codewords is what is stated here; the stabilizer-commutation and
independence properties are the separate concern of Exercises 10.53–10.54.)

## Supporting results

The codewords `steaneLogicalZero`, `steaneLogicalOne` and their construction from the classical
dual code `C₂ = steaneDualCode` are those of Exercise 10.32. The two operators are the CSS Pauli
strings `phaseString 1`, `bitString 1` (`AxQM/Postulates/API/CSSCode.lean`), and their action
follows from the general CSS coset-state lemmas in `AxQM/Postulates/API/CSSCodeStabilizer.lean`:
`phaseString_hasEigenstate_cssStdState` (the `Z^u`-as-sign-`(-1)^{u·x}` law, when `u ⊥ C₂`) and
`bitString_evolvePure_cssStdState` (the `X^v`-as-coset-translation law). The even-weight fact
`𝟙 · y = 0` for `y ∈ C₂` is the classical `Concrete.steaneDualCode_dotProduct_one`.

## Fidelity

What is stated is the action of the *physical* logical operators (`Evolution`s) on the *physical*
codewords (`PureState`s), via the relations `Evolution.HasEigenstate` and `Evolution.evolvePure`.
Both operators have type `Evolution (bitReg (Fin 7))`. Nothing is weakened: the operators are
exactly `Z₁…Z₇` and `X₁…X₇` of (10.107) and the codewords are exactly (10.78)/(10.79).
-/

namespace AxQM

open AxQM.Concrete

open scoped Matrix

/-- **The Steane logical-`Z` operator `Z̄ = Z₁Z₂Z₃Z₄Z₅Z₆Z₇`** of Nielsen & Chuang eq. (10.107): the
uniform phase-flip Pauli string `Z^{𝟙}` on the seven-qubit register (`phaseString` at the all-ones
support word `𝟙`), as a unitary `Evolution`. -/
noncomputable def steaneLogicalZBar : Evolution (bitReg (Fin 7)) :=
  phaseString 1

/-- **The Steane logical-`X` operator `X̄ = X₁X₂X₃X₄X₅X₆X₇`** of Nielsen & Chuang eq. (10.107): the
uniform bit-flip Pauli string `X^{𝟙}` on the seven-qubit register (`bitString` at the all-ones
support word `𝟙`), as a unitary `Evolution`. -/
noncomputable def steaneLogicalXBar : Evolution (bitReg (Fin 7)) :=
  bitString 1

/-- **Nielsen & Chuang, Exercise 10.52 (`Z̄` fixes `|0_L⟩`).** The logical-`Z` operator
`Z̄ = Z₁…Z₇` acts as `+1` on the Steane logical zero, `Z̄|0_L⟩ = |0_L⟩`: every ket `|y⟩` (`y ∈ C₂`)
of `|0_L⟩` has even weight, so `Z^{𝟙}` leaves each sign `+1`. This is the logical `Z|0⟩ = |0⟩`. -/
theorem steaneLogicalZBar_hasEigenstate_logicalZero :
    steaneLogicalZBar.HasEigenstate 1 steaneLogicalZero := by
  have h := phaseString_hasEigenstate_cssStdState steaneDualCode
    (u := (1 : Fin 7 → ZMod 2)) (x := 0) (fun y hy => steaneDualCode_dotProduct_one hy)
  have hval : ((1 : Fin 7 → ZMod 2) ⬝ᵥ (0 : Fin 7 → ZMod 2)).val = 0 := by simp
  rw [hval, pow_zero] at h
  exact h

/-- **Nielsen & Chuang, Exercise 10.52 (`Z̄` negates `|1_L⟩`).** The logical-`Z` operator
`Z̄ = Z₁…Z₇` acts as `−1` on the Steane logical one, `Z̄|1_L⟩ = −|1_L⟩`: every ket `|𝟙 + y⟩`
(`y ∈ C₂`) of `|1_L⟩` has odd weight `7 − |y|`, so `Z^{𝟙}` gives the uniform sign `(-1)^{𝟙·𝟙} = −1`.
This is the logical `Z|1⟩ = −|1⟩`. -/
theorem steaneLogicalZBar_hasEigenstate_logicalOne :
    steaneLogicalZBar.HasEigenstate (-1) steaneLogicalOne := by
  have h := phaseString_hasEigenstate_cssStdState steaneDualCode
    (u := (1 : Fin 7 → ZMod 2)) (x := 1) (fun y hy => steaneDualCode_dotProduct_one hy)
  have hval : ((1 : Fin 7 → ZMod 2) ⬝ᵥ (1 : Fin 7 → ZMod 2)).val = 1 := by decide
  rw [hval, pow_one] at h
  exact h

/-- **Nielsen & Chuang, Exercise 10.52 (`X̄` maps `|0_L⟩` to `|1_L⟩`).** The logical-`X` operator
`X̄ = X₁…X₇` sends the Steane logical zero to the logical one, `X̄|0_L⟩ = |1_L⟩`: translating by the
all-ones word `𝟙` carries the coset `0 + C₂` onto `𝟙 + C₂`. This is the logical `X|0⟩ = |1⟩`. -/
theorem steaneLogicalXBar_evolvePure_logicalZero :
    steaneLogicalXBar.evolvePure steaneLogicalZero = steaneLogicalOne := by
  have h := bitString_evolvePure_cssStdState steaneDualCode (1 : Fin 7 → ZMod 2) 0
  rwa [zero_add] at h

/-- **Nielsen & Chuang, Exercise 10.52 (`X̄` maps `|1_L⟩` to `|0_L⟩`).** The logical-`X` operator
`X̄ = X₁…X₇` sends the Steane logical one back to the logical zero, `X̄|1_L⟩ = |0_L⟩`: translating
by `𝟙` again carries the coset `𝟙 + C₂` onto `0 + C₂` (since `𝟙 + 𝟙 = 0`). This is the logical
`X|1⟩ = |0⟩`. -/
theorem steaneLogicalXBar_evolvePure_logicalOne :
    steaneLogicalXBar.evolvePure steaneLogicalOne = steaneLogicalZero := by
  have h := bitString_evolvePure_cssStdState steaneDualCode (1 : Fin 7 → ZMod 2) 1
  rw [show (1 : Fin 7 → ZMod 2) + 1 = 0 from by decide] at h
  exact h

end AxQM
