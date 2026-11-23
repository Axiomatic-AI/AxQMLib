/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CSSCodeStabilizer
import AxQM.Concrete.SteaneCode

/-!
# Nielsen & Chuang, Exercise 10.32 — the Fig 10.6 generators stabilize the Steane codewords

*(N&C §10.5.1, Fig 10.6, p. 456.)*

Verify the six generators of Fig 10.6 stabilize the Steane code codewords.

## What the exercise asks

The **Steane code** is the CSS code `CSS(C₁, C₂)` built from the `[7, 4, 3]` Hamming code
`C₁ = C` and its dual `C₂ = C⊥` (N&C §10.4.2). Its two logical codewords are the standard CSS coset
states over the `7`-qubit register `bitReg (Fin 7)`:

* `steaneLogicalZero = |0_L⟩ = |0 + C₂⟩ = (1/√8) ∑_{y ∈ C₂} |y⟩` (N&C eq. (10.78));
* `steaneLogicalOne  = |1_L⟩ = |𝟙 + C₂⟩ = (1/√8) ∑_{y ∈ C₂} |𝟙 + y⟩` (N&C eq. (10.79)), with coset
  representative the all-ones word `𝟙 = 1111111 ∈ C₁ \ C₂`.

Figure 10.6 lists six stabilizer generators. Writing `hᵢ = hammingParityCheck i` for the `i`-th row
of the parity-check matrix `H` (eq. (10.76)), they are the bit-flip and phase-flip Pauli strings on
those support rows:

| Fig 10.6 | operator      | this file             |
| -------- | ------------- | --------------------- |
| `g₁`     | `I I I X X X X` | `steaneGenX 0 = X^{h₀}` |
| `g₂`     | `I X X I I X X` | `steaneGenX 1 = X^{h₁}` |
| `g₃`     | `X I X I X I X` | `steaneGenX 2 = X^{h₂}` |
| `g₄`     | `I I I Z Z Z Z` | `steaneGenZ 0 = Z^{h₀}` |
| `g₅`     | `I Z Z I I Z Z` | `steaneGenZ 1 = Z^{h₁}` |
| `g₆`     | `Z I Z I Z I Z` | `steaneGenZ 2 = Z^{h₂}` |

(the `X`/`Z` positions of `gᵢ` are exactly the `1`-positions of row `hᵢ`). "Stabilizes" means each
generator fixes each codeword, `g |ψ⟩ = |ψ⟩` — the eigenvalue-`1` eigenstate relation
`Evolution.HasEigenstate 1` (N&C's characterisation of the stabilized subspace `V_S`, §10.5.1).

## What is proved, and how

The verification decomposes into the two CSS stabilizer mechanisms
(`AxQM.Postulates.API.CSSCodeStabilizer`):

* **X-type** `steaneGenX i = X^{hᵢ}`. Translation by `hᵢ ∈ C₂`
  (`Concrete.hammingParityCheck_row_mem_steaneDualCode`) permutes each coset `x + C₂` onto itself,
  so `X^{hᵢ}` fixes `|x + C₂⟩` for *every* representative `x` — hence both `|0_L⟩` and `|1_L⟩`.
* **Z-type** `steaneGenZ i = Z^{hᵢ}`. The diagonal signs are trivial when `hᵢ ⊥ C₂`
  (self-orthogonality, `Concrete.hammingParityCheck_row_dotProduct_steaneDualCode`) and `hᵢ ⊥ x`.
  For `|0_L⟩` (`x = 0`) the latter is automatic; for `|1_L⟩` (`x = 𝟙`) it is the even weight of the
  rows (`Concrete.hammingParityCheck_row_dotProduct_one`).

## Where the ingredients are

What is proved is the stabilization of the codewords (`PureState`s) by the Pauli generators
(`Evolution`s), stated with the relation `Evolution.HasEigenstate`. The classical ingredients — the
dual code `C₂` and the row orthogonality facts — are in `AxQM/Concrete/SteaneCode.lean`; the general
CSS coset-state stabilizer lemmas are in `AxQM/Postulates/API/CSSCodeStabilizer.lean`. The
generators are exactly those of Figure 10.6 and the codewords are exactly (10.78)/(10.79).
-/

namespace AxQM

open AxQM.Concrete

open scoped Matrix

/-- The **Steane logical zero** `|0_L⟩ = |0 + C₂⟩ = (1/√8) ∑_{y ∈ C₂} |y⟩` (Nielsen & Chuang, eq.
(10.78)), the standard CSS coset state over the dual Hamming code `C₂` at representative `0`. -/
noncomputable def steaneLogicalZero : PureState (bitReg (Fin 7)) :=
  cssStdState steaneDualCode 0

/-- The **Steane logical one** `|1_L⟩ = |𝟙 + C₂⟩ = (1/√8) ∑_{y ∈ C₂} |𝟙 + y⟩` (Nielsen & Chuang, eq.
(10.79)), the standard CSS coset state over `C₂` at the all-ones representative `𝟙 = 1111111`, an
element of `C₁ \ C₂`. -/
noncomputable def steaneLogicalOne : PureState (bitReg (Fin 7)) :=
  cssStdState steaneDualCode 1

/-- The three **X-type stabilizer generators** `g₁, g₂, g₃` of Figure 10.6: `steaneGenX i = X^{hᵢ}`
is the bit-flip Pauli string on the `i`-th row `hᵢ` of the Hamming parity-check matrix. -/
noncomputable def steaneGenX (i : Fin 3) : Evolution (bitReg (Fin 7)) :=
  bitString (hammingParityCheck i)

/-- The three **Z-type stabilizer generators** `g₄, g₅, g₆` of Figure 10.6: `steaneGenZ i = Z^{hᵢ}`
is the phase-flip Pauli string on the `i`-th row `hᵢ` of the Hamming parity-check matrix. -/
noncomputable def steaneGenZ (i : Fin 3) : Evolution (bitReg (Fin 7)) :=
  phaseString (hammingParityCheck i)

/-- **The six generators of Figure 10.6**, as a single family `Fin 6 → Evolution`: the three X-type
generators `steaneGenX` followed by the three Z-type generators `steaneGenZ`. -/
noncomputable def steaneStabilizer : Fin 6 → Evolution (bitReg (Fin 7)) :=
  Fin.append steaneGenX steaneGenZ

/-- **X-type generators stabilize `|0_L⟩`.** Each `steaneGenX i = X^{hᵢ}` fixes the Steane logical
zero, since `hᵢ ∈ C₂` translates the coset `C₂` onto itself. -/
theorem steaneGenX_hasEigenstate_one_logicalZero (i : Fin 3) :
    (steaneGenX i).HasEigenstate 1 steaneLogicalZero :=
  bitString_hasEigenstate_one_cssStdState steaneDualCode
    (hammingParityCheck_row_mem_steaneDualCode i) 0

/-- **X-type generators stabilize `|1_L⟩`.** Each `steaneGenX i = X^{hᵢ}` fixes the Steane logical
one, since `hᵢ ∈ C₂` translates the coset `𝟙 + C₂` onto itself. -/
theorem steaneGenX_hasEigenstate_one_logicalOne (i : Fin 3) :
    (steaneGenX i).HasEigenstate 1 steaneLogicalOne :=
  bitString_hasEigenstate_one_cssStdState steaneDualCode
    (hammingParityCheck_row_mem_steaneDualCode i) 1

/-- **Z-type generators stabilize `|0_L⟩`.** Each `steaneGenZ i = Z^{hᵢ}` fixes the Steane logical
zero: `hᵢ ⊥ 0` trivially and `hᵢ ⊥ C₂` by self-orthogonality, so every diagonal sign is `+1`. -/
theorem steaneGenZ_hasEigenstate_one_logicalZero (i : Fin 3) :
    (steaneGenZ i).HasEigenstate 1 steaneLogicalZero :=
  phaseString_hasEigenstate_one_cssStdState steaneDualCode (dotProduct_zero _)
    (fun _ hy => hammingParityCheck_row_dotProduct_steaneDualCode i hy)

/-- **Z-type generators stabilize `|1_L⟩`.** Each `steaneGenZ i = Z^{hᵢ}` fixes the Steane logical
one: `hᵢ ⊥ 𝟙` by even weight and `hᵢ ⊥ C₂` by self-orthogonality, so every diagonal sign is `+1`. -/
theorem steaneGenZ_hasEigenstate_one_logicalOne (i : Fin 3) :
    (steaneGenZ i).HasEigenstate 1 steaneLogicalOne :=
  phaseString_hasEigenstate_one_cssStdState steaneDualCode
    (hammingParityCheck_row_dotProduct_one i)
    (fun _ hy => hammingParityCheck_row_dotProduct_steaneDualCode i hy)

/-- **Nielsen & Chuang, Exercise 10.32 (logical zero).** Every one of the six Figure-10.6 generators
stabilizes the Steane logical zero `|0_L⟩`. -/
theorem steaneStabilizer_hasEigenstate_one_logicalZero (i : Fin 6) :
    (steaneStabilizer i).HasEigenstate 1 steaneLogicalZero := by
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i <;>
    simp only [steaneStabilizer, Fin.append_left, Fin.append_right]
  · exact steaneGenX_hasEigenstate_one_logicalZero j
  · exact steaneGenZ_hasEigenstate_one_logicalZero j

/-- **Nielsen & Chuang, Exercise 10.32 (logical one).** Every one of the six Figure-10.6 generators
stabilizes the Steane logical one `|1_L⟩`. -/
theorem steaneStabilizer_hasEigenstate_one_logicalOne (i : Fin 6) :
    (steaneStabilizer i).HasEigenstate 1 steaneLogicalOne := by
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i <;>
    simp only [steaneStabilizer, Fin.append_left, Fin.append_right]
  · exact steaneGenX_hasEigenstate_one_logicalOne j
  · exact steaneGenZ_hasEigenstate_one_logicalOne j

end AxQM
