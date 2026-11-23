/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_52
import AxQM.Concrete.SteaneStandardForm

/-!
# Nielsen & Chuang, Exercise 10.55 — the `X̄` operator for the standard form of the Steane code

*(N&C §10.5.7, eq. (10.111)/(10.112), p. 471.)*

Find the Xbar operator for the standard form of the Steane code.

## Finding `X̄` (the check-matrix computation)

N&C §10.5.7 puts a stabilizer code into the **standard form** (10.111)
`[I A₁ A₂ | B 0 C ; 0 0 0 | D I E]` and reads off the encoded `X̄` as the operator with check matrix
`[0 Eᵀ I | Cᵀ 0 0]`. For the Steane code (`n = 7`, `k = 1`, rank `r = 3`) N&C brings the check
matrix into the standard form (10.112) by swapping qubits `1↔4`, `3↔4`, `6↔7` and doing row
operations. This check-matrix computation is carried out in `AxQM/Concrete/SteaneStandardForm.lean`:

* the read-offs `E = (1, 1, 0)` and `C = 0` (`Concrete.steaneStd_E`, `Concrete.steaneStd_C`);
* the recipe `[0 Eᵀ I | Cᵀ 0 0]` yields `X̄ = X₄X₅X₇` (`Concrete.steaneStdLogicalX_checkRow`) — the
  `X̄` operator **for the standard form**;
* undoing the swaps carries it back to the original Steane ordering as `X̄ = X₃X₅X₆`
  (`Concrete.steaneStdLogicalXOriginal_eq`, support `0010110`).

The companion `Z̄ = Z₁Z₂Z₇` / original-ordering `Z̄ = Z₂Z₄Z₆` there reproduce N&C's own worked
answer, cross-checking the encoding of (10.112) and the qubit swaps.

## What this file proves (the physical operator acts as logical `X`)

The subject here is the **physical** `X̄` operator and the verification that it is a genuine
logical `X`. `steaneStandardLogicalXBar` is the found operator `X₃X₅X₆` in the original Steane
ordering, as the bit-flip Pauli string `bitString 0010110` (an `Evolution`). It acts on the Steane
codewords `|0_L⟩, |1_L⟩` (from Exercise 10.32) exactly as logical `X`:

* `steaneStandardLogicalXBar_evolvePure_logicalZero`: `X̄|0_L⟩ = |1_L⟩`;
* `steaneStandardLogicalXBar_evolvePure_logicalOne`: `X̄|1_L⟩ = |0_L⟩`.

Mechanism: `bitString 0010110` translates the coset representative by `0010110`, and
`0010110 + 𝟙 = 1101001 = h₀ + h₁ + h₂ ∈ C₂` (the classical
`Concrete.steaneStdLogicalXOriginalSupport_add_one_mem`), so `0010110` and the all-ones word `𝟙`
lie in the same coset of `C₂ = steaneDualCode`. Hence
`X̄` exchanges the two logical cosets `0 + C₂ ↔ 𝟙 + C₂` just as `X^{𝟙} = X₁…X₇` does — so the
standard-form `X̄` and the (10.107) `X̄` of Exercise 10.52 have the **same effect on the codewords**
(`steaneStandardLogicalXBar_evolvePure_logicalZero_eq_logicalXBar` and `…_logicalOne_eq_…`),
differing only by the `X`-stabilizer `X^{1101001}` — the resolution N&C notes for the analogous
`Z̄` discrepancy.

The independence of `X̄` from the stabilizer and its (anti)commutation with the generators / `Z̄`
are the separate concern of Exercise 10.54; this exercise is the *finding* of `X̄` and the
verification of its logical action.

## Fidelity

The classical check-matrix "finding" — the standard-form matrix (10.112), the read-offs, the
recipe, and the swap — is in `AxQM/Concrete/SteaneStandardForm.lean`. The physical content here —
the operator `steaneStandardLogicalXBar : Evolution (bitReg (Fin 7))` and its codeword action — is
stated through `Evolution.evolvePure`. Nothing is weakened: the operator is exactly the `X₃X₅X₆`
produced by the standard-form recipe and the codewords are exactly (10.78)/(10.79).
-/

namespace AxQM

open AxQM.Concrete

open scoped Matrix

/-- **The `X̄` operator for the standard form of the Steane code** (Nielsen & Chuang, Ex 10.55), in
the original qubit ordering: `X̄ = X₃X₅X₆`, the bit-flip Pauli string on the seven-qubit register,
as a unitary `Evolution`. Its support is `Concrete.steaneStdLogicalXOriginalSupport` — the `X`-part
of
the check row of the found operator `X₃X₅X₆`, itself the standard-form recipe `[0 Eᵀ I | Cᵀ 0 0]`
answer `X₄X₅X₇` (`Concrete.steaneStdLogicalX_checkRow`) with the swaps `1↔4, 3↔4, 6↔7` undone
(`Concrete.steaneStdLogicalXOriginal_eq`). So the physical operator is wired *by name* to the
check-matrix derivation, not merely equal to it by eye. -/
noncomputable def steaneStandardLogicalXBar : Evolution (bitReg (Fin 7)) :=
  bitString steaneStdLogicalXOriginalSupport

/-- **Nielsen & Chuang, Exercise 10.55 (`X̄` maps `|0_L⟩` to `|1_L⟩`).** The standard-form
logical-`X` operator `X̄ = X₃X₅X₆` sends the Steane logical zero to the logical one,
`X̄|0_L⟩ = |1_L⟩`: the support word `0010110` lies in the same `C₂`-coset as the all-ones word `𝟙`
(`Concrete.steaneStdLogicalXOriginalSupport_add_one_mem`), so translating the coset `0 + C₂` by it
lands on `𝟙 + C₂`. This is the logical `X|0⟩ = |1⟩`. -/
theorem steaneStandardLogicalXBar_evolvePure_logicalZero :
    steaneStandardLogicalXBar.evolvePure steaneLogicalZero = steaneLogicalOne := by
  rw [steaneStandardLogicalXBar, steaneLogicalZero, steaneLogicalOne,
    bitString_evolvePure_cssStdState_swap steaneDualCode
      steaneStdLogicalXOriginalSupport_add_one_mem 0, zero_add]

/-- **Nielsen & Chuang, Exercise 10.55 (`X̄` maps `|1_L⟩` to `|0_L⟩`).** The standard-form
logical-`X` operator `X̄ = X₃X₅X₆` sends the Steane logical one back to the logical zero,
`X̄|1_L⟩ = |0_L⟩`: translating the coset `𝟙 + C₂` by `0010110` lands on `0 + C₂`, since
`0010110 + 𝟙 ∈ C₂`. This is the logical `X|1⟩ = |0⟩`. -/
theorem steaneStandardLogicalXBar_evolvePure_logicalOne :
    steaneStandardLogicalXBar.evolvePure steaneLogicalOne = steaneLogicalZero := by
  rw [steaneStandardLogicalXBar, steaneLogicalOne, steaneLogicalZero,
    bitString_evolvePure_cssStdState_swap steaneDualCode
      steaneStdLogicalXOriginalSupport_add_one_mem 1,
    show (1 : Fin 7 → ZMod 2) + 1 = 0 from by decide]

/-- **The standard-form `X̄` and the (10.107) `X̄` agree on `|0_L⟩`.** Both the standard-form
`X̄ = X₃X₅X₆` and the uniform `X̄ = X₁…X₇` of Exercise 10.52 send `|0_L⟩` to `|1_L⟩`; they differ
only by the `X`-stabilizer `X^{1101001}` and so have the same effect on Steane code states — the
resolution N&C gives for the analogous `Z̄` discrepancy. -/
theorem steaneStandardLogicalXBar_evolvePure_logicalZero_eq_logicalXBar :
    steaneStandardLogicalXBar.evolvePure steaneLogicalZero
      = steaneLogicalXBar.evolvePure steaneLogicalZero := by
  rw [steaneStandardLogicalXBar_evolvePure_logicalZero, steaneLogicalXBar_evolvePure_logicalZero]

/-- **The standard-form `X̄` and the (10.107) `X̄` agree on `|1_L⟩`.** Both send `|1_L⟩` to `|0_L⟩`,
so the standard-form `X₃X₅X₆` and the uniform `X₁…X₇` have the same action on both Steane
codewords. -/
theorem steaneStandardLogicalXBar_evolvePure_logicalOne_eq_logicalXBar :
    steaneStandardLogicalXBar.evolvePure steaneLogicalOne
      = steaneLogicalXBar.evolvePure steaneLogicalOne := by
  rw [steaneStandardLogicalXBar_evolvePure_logicalOne, steaneLogicalXBar_evolvePure_logicalOne]

end AxQM
