/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrix
import AxQM.Concrete.SteaneCode

/-!
# Concrete: the standard form of the Steane code and its encoded `X̄` (Nielsen & Chuang, Ex 10.55)

This file is a finite `ZMod 2` / `Fin 4` check-matrix computation. It is the classical
"finding" half of Nielsen & Chuang, **Exercise 10.55** — *find the `X̄` operator for the standard
form of the Steane code* (N&C §10.5.7, p. 471).

## The standard form (10.112) and the encoded-operator recipe

N&C §10.5.7 brings the check matrix of an `[n, k]` stabilizer code into the **standard form**
(eq. (10.111))
```
        r        n-k-r    k   ┃   r     n-k-r    k
   ┌─────────────────────────╂───────────────────────┐
 r │    I        A₁       A₂  ┃   B       0       C   │
n-k-r │    0        0        0   ┃   D       I       E   │
   └─────────────────────────╂───────────────────────┘
                (X part)                (Z part)
```
and reads off the **encoded operators** (the paragraph after (10.111)):

* encoded `Z̄` — check matrix `[0 0 0 | A₂ᵀ 0 I]`;
* encoded `X̄` — check matrix `[0 Eᵀ I | Cᵀ 0 0]`.

For the **Steane code** `n = 7`, `k = 1`, and the rank of the `X`-part is `r = 3`, so
`n − k − r = 3`. The swaps of qubits `1↔4`, `3↔4`, `6↔7` and the row operations of §10.5.7 bring the
Steane check matrix (10.83) into the standard form displayed in eq. (10.112). Its rows are
`steaneStdGen` below (`X`-part on the top three generators, `Z`-part on the bottom three).

## What is proved

* `steaneStdGen` — the six standard-form generators (10.112) as `Fin 7 → Fin 4` Pauli-index strings
  (`I=0, X=1, Y=2, Z=3`); `steaneStdLogicalZ = Z₁Z₂Z₇`, `steaneStdLogicalX = X₄X₅X₇`.
* `steaneStd_A2`, `steaneStd_C`, `steaneStd_E` — the **read-offs** `A₂ = (1,1,0)`, `C = 0`,
  `E = (1,1,0)`: the `k`-columns (qubit-`7`) of the `X`-part of the top rows, and the `Z`-part
  of the top and bottom rows respectively. (N&C: *"We read off `A₂ = (1, 1, 0)`."*)
* `steaneStdLogicalZ_checkRow` — the `Z̄` recipe `[0 0 0 | A₂ᵀ 0 I]` applied to (10.112) is the
  check row of `Z̄ = Z₁Z₂Z₇`, reproducing **N&C's own worked answer**.
* `steaneStdLogicalX_checkRow` — **Exercise 10.55**: the `X̄` recipe `[0 Eᵀ I | Cᵀ 0 0]` applied to
  (10.112) is the check row of `X̄ = X₄X₅X₇`. This is the `X̄` operator for the standard form.
* `steaneStdSwap`, `steaneStdLogicalXOriginal_eq`, `steaneStdLogicalZOriginal_eq` — undoing the
  qubit swaps (`1↔4, 3↔4, 6↔7`) translates the standard-form operators back to the **original**
  Steane ordering: `X̄ = X₃X₅X₆` and `Z̄ = Z₂Z₄Z₆` (the latter again reproducing N&C's stated
  original-ordering answer). The original-ordering `X̄` support `0010110` is the one the physical
  operator of `NC/Ch10/Exercise10_55.lean` acts by.

Everything is a finite check over `Fin 7`, `Fin 4`, `ZMod 2` decided by `decide`. The check-matrix
row `checkRow` is the shared representation of `Concrete/CheckMatrix.lean`; the block matrices `A₂`,
`C`, `E` are its `k`-columns.
-/

namespace AxQM.Concrete

/-- The six **standard-form generators** of the Steane code (Nielsen & Chuang eq. (10.112)) as
Pauli-index strings `Fin 7 → Fin 4` (`I=0, X=1, Y=2, Z=3`). The top three rows are `X`-type
(`X`-part `[I A₁ A₂]`, `Z`-part `0`), the bottom three `Z`-type (`X`-part `0`, `Z`-part `[D I E]`):
```
g₁ = X . . . X X X      g₄ = Z . Z Z . . Z
g₂ = . X . X . X X      g₅ = . Z Z . Z . Z
g₃ = . . X X X X .      g₆ = Z Z Z . . Z .
```
This is the Steane check matrix (10.83) after the swaps `1↔4, 3↔4, 6↔7` and the row operations of
§10.5.7 (`I` blocks on `X`-columns `1,2,3` and `Z`-columns `4,5,6`, the rank `r = 3`). -/
def steaneStdGen : Fin 6 → Fin 7 → Fin 4 :=
  ![![1, 0, 0, 0, 1, 1, 1],
    ![0, 1, 0, 1, 0, 1, 1],
    ![0, 0, 1, 1, 1, 1, 0],
    ![3, 0, 3, 3, 0, 0, 3],
    ![0, 3, 3, 0, 3, 0, 3],
    ![3, 3, 3, 0, 0, 3, 0]]

/-- The **standard-form encoded `Z̄`** of the Steane code (Nielsen & Chuang §10.5.7): `Z̄ = Z₁Z₂Z₇`,
the operator with check row `[0 0 0 | A₂ᵀ 0 I]` read off (10.112). N&C's own worked answer. -/
def steaneStdLogicalZ : Fin 7 → Fin 4 := ![3, 3, 0, 0, 0, 0, 3]

/-- The **standard-form encoded `X̄`** of the Steane code (Nielsen & Chuang, **Exercise 10.55**):
`X̄ = X₄X₅X₇`, the operator with check row `[0 Eᵀ I | Cᵀ 0 0]` read off (10.112). -/
def steaneStdLogicalX : Fin 7 → Fin 4 := ![0, 0, 0, 1, 1, 0, 1]

/-- **Read-off `A₂ = (1, 1, 0)`** (Nielsen & Chuang §10.5.7): the `k = 1` column (qubit `7`, index
`6`) of the `X`-part of the top three generators of (10.112). N&C: *"We read off `A₂ = (1, 1, 0)`."*
-/
theorem steaneStd_A2 :
    ((checkRow (steaneStdGen 0)).1 6, (checkRow (steaneStdGen 1)).1 6,
      (checkRow (steaneStdGen 2)).1 6) = ((1 : ZMod 2), 1, 0) := by decide

/-- **Read-off `C = 0`**: the `k = 1` column (qubit `7`) of the `Z`-part of the top three generators
of (10.112) — the top rows are `X`-type, so their `Z`-part vanishes. -/
theorem steaneStd_C :
    ((checkRow (steaneStdGen 0)).2 6, (checkRow (steaneStdGen 1)).2 6,
      (checkRow (steaneStdGen 2)).2 6) = ((0 : ZMod 2), 0, 0) := by decide

/-- **Read-off `E = (1, 1, 0)`**: the `k = 1` column (qubit `7`) of the `Z`-part of the bottom three
generators of (10.112). This is the block that determines the `X̄` recipe. -/
theorem steaneStd_E :
    ((checkRow (steaneStdGen 3)).2 6, (checkRow (steaneStdGen 4)).2 6,
      (checkRow (steaneStdGen 5)).2 6) = ((1 : ZMod 2), 1, 0) := by decide

/-- The `k`-column `A₂` of (10.112), extracted as the `X`-part qubit-`7` column of the top three
rows (`= (1,1,0)` by `steaneStd_A2`). -/
def steaneStdA2 : Fin 3 → ZMod 2 :=
  ![(checkRow (steaneStdGen 0)).1 6, (checkRow (steaneStdGen 1)).1 6,
    (checkRow (steaneStdGen 2)).1 6]

/-- The `k`-column `C` of (10.112), extracted as the `Z`-part qubit-`7` column of the top three rows
(`= 0` by `steaneStd_C`). -/
def steaneStdC : Fin 3 → ZMod 2 :=
  ![(checkRow (steaneStdGen 0)).2 6, (checkRow (steaneStdGen 1)).2 6,
    (checkRow (steaneStdGen 2)).2 6]

/-- The `k`-column `E` of (10.112), extracted as the `Z`-part qubit-`7` column of the bottom three
rows (`= (1,1,0)` by `steaneStd_E`). -/
def steaneStdE : Fin 3 → ZMod 2 :=
  ![(checkRow (steaneStdGen 3)).2 6, (checkRow (steaneStdGen 4)).2 6,
    (checkRow (steaneStdGen 5)).2 6]

/-- The **standard-form encoded-`Z̄` recipe** `[0 0 0 | A₂ᵀ 0 I]` (Nielsen & Chuang §10.5.7),
specialised to the Steane parameters `r = 3`, `n − k − r = 3`, `k = 1`: check row with `X`-part `0`
and `Z`-part `[A₂ᵀ | 0 | 1]`. -/
def encodedZBarCheckRow (A₂ : Fin 3 → ZMod 2) : (Fin 7 → ZMod 2) × (Fin 7 → ZMod 2) :=
  (0, ![A₂ 0, A₂ 1, A₂ 2, 0, 0, 0, 1])

/-- The **standard-form encoded-`X̄` recipe** `[0 Eᵀ I | Cᵀ 0 0]` (Nielsen & Chuang §10.5.7),
specialised to the Steane parameters `r = 3`, `n − k − r = 3`, `k = 1`: check row with `X`-part
`[0 | Eᵀ | 1]` and `Z`-part `[Cᵀ | 0 | 0]`. -/
def encodedXBarCheckRow (E C : Fin 3 → ZMod 2) : (Fin 7 → ZMod 2) × (Fin 7 → ZMod 2) :=
  (![0, 0, 0, E 0, E 1, E 2, 1], ![C 0, C 1, C 2, 0, 0, 0, 0])

/-- **The encoded `Z̄` recipe reproduces `Z₁Z₂Z₇`** (Nielsen & Chuang §10.5.7): the check row
`[0 0 0 | A₂ᵀ 0 I]` built from the read-off `A₂` of (10.112) is exactly the check row of
`steaneStdLogicalZ = Z₁Z₂Z₇`. This is N&C's own worked answer for the encoded `Z`. -/
theorem steaneStdLogicalZ_checkRow :
    checkRow steaneStdLogicalZ = encodedZBarCheckRow steaneStdA2 := by decide

/-- **Nielsen & Chuang, Exercise 10.55.** *The `X̄` operator for the standard form of the Steane
code.* The encoded-`X̄` recipe `[0 Eᵀ I | Cᵀ 0 0]` (§10.5.7), built from the read-offs `E = (1,1,0)`
and `C = 0` of (10.112), is exactly the check row of `steaneStdLogicalX = X₄X₅X₇`. So the `X̄`
operator for the standard form is `X₄X₅X₇`. -/
theorem steaneStdLogicalX_checkRow :
    checkRow steaneStdLogicalX = encodedXBarCheckRow steaneStdE steaneStdC := by decide

/-- The **qubit relabeling** of Nielsen & Chuang §10.5.7 that undoes the swaps bringing the Steane
code into standard form: the composite of the transpositions `1↔4`, `3↔4`, `6↔7` (`0`-indexed
`0↔3`, `2↔3`, `5↔6`). As a permutation `original ↦ standard`, it sends a Pauli string in the
standard ordering back to the original code by precomposition. -/
def steaneStdSwap : Equiv.Perm (Fin 7) :=
  Equiv.swap 5 6 * Equiv.swap 2 3 * Equiv.swap 0 3

/-- **`X̄` in the original Steane ordering** (Nielsen & Chuang, Exercise 10.55): the standard-form
`X̄ = X₄X₅X₇` reindexed by undoing the swaps `steaneStdSwap` (precomposition sends the standard-form
Pauli string back to the original code). -/
def steaneStdLogicalXOriginal : Fin 7 → Fin 4 := fun k => steaneStdLogicalX (steaneStdSwap k)

/-- **`X̄` in the original ordering is `X₃X₅X₆`** (Nielsen & Chuang, Exercise 10.55): undoing the
standard-form swaps carries `X̄ = X₄X₅X₇` back to `X₃X₅X₆` (support `0010110`). -/
theorem steaneStdLogicalXOriginal_eq :
    steaneStdLogicalXOriginal = ![0, 0, 1, 0, 1, 1, 0] := by decide

/-- **`Z̄` in the original Steane ordering** (Nielsen & Chuang §10.5.7): the standard-form
`Z̄ = Z₁Z₂Z₇` reindexed by undoing the swaps `steaneStdSwap`. -/
def steaneStdLogicalZOriginal : Fin 7 → Fin 4 := fun k => steaneStdLogicalZ (steaneStdSwap k)

/-- **`Z̄` in the original ordering is `Z₂Z₄Z₆`** — exactly N&C's stated original-ordering answer,
the cross-check validating the encoding of (10.112) and the swap. -/
theorem steaneStdLogicalZOriginal_eq :
    steaneStdLogicalZOriginal = ![0, 3, 0, 3, 0, 3, 0] := by decide

/-- **The support word of the original-ordering `X̄`**: the `X`-part `(checkRow …).1` of the found
operator `steaneStdLogicalXOriginal = X₃X₅X₆`, i.e. the `ZMod 2` bit vector `0010110`. It is defined
*as* that operator's own check-row support (not an independent transcription), and is the word the
physical bit-flip operator `steaneStandardLogicalXBar` of `NC/Ch10/Exercise10_55.lean` translates
the Steane codewords by. -/
def steaneStdLogicalXOriginalSupport : Fin 7 → ZMod 2 := (checkRow steaneStdLogicalXOriginal).1

/-- **The support word of `X̄` (original ordering) is `0010110`**: the `X`-part of the check row of
`X₃X₅X₆`. -/
theorem steaneStdLogicalXOriginalSupport_eq :
    steaneStdLogicalXOriginalSupport = ![0, 0, 1, 0, 1, 1, 0] := by decide

/-- **The original-ordering `X̄` support `0010110` differs from `𝟙` by a dual codeword**:
`0010110 + 𝟙 = 1101001 = h₀ + h₁ + h₂` is a sum of rows of the Hamming parity-check matrix, hence
lies in `C₂ = steaneDualCode` (a submodule, closed under addition, containing each row
`hammingParityCheck_row_mem_steaneDualCode`). So `X̄ = X₃X₅X₆` and the uniform `X̄ = X^{𝟙} = X₁…X₇`
translate the codewords by two representatives of the same `C₂`-coset — the classical fact behind
their identical action on the Steane codewords (`NC/Ch10/Exercise10_55.lean`). -/
theorem steaneStdLogicalXOriginalSupport_add_one_mem :
    steaneStdLogicalXOriginalSupport + 1 ∈ steaneDualCode := by
  rw [steaneStdLogicalXOriginalSupport_eq]
  have h : (![0, 0, 1, 0, 1, 1, 0] : Fin 7 → ZMod 2) + 1
      = hammingParityCheck 0 + hammingParityCheck 1 + hammingParityCheck 2 := by decide
  rw [h]
  exact add_mem (add_mem (hammingParityCheck_row_mem_steaneDualCode 0)
    (hammingParityCheck_row_mem_steaneDualCode 1)) (hammingParityCheck_row_mem_steaneDualCode 2)

end AxQM.Concrete
