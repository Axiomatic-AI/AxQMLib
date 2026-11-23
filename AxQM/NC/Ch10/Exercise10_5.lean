/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorPhaseSyndrome

/-!
# Nielsen & Chuang, Exercise 10.5 — the Shor-code phase-flip syndrome

Shor code phase-flip syndrome corresponds to measuring X1X2X3X4X5X6 and X4X5X6X7X8X9.

The nine-qubit Shor code is a concatenation (N&C §10.2): the qubit is first encoded with the
three-qubit *phase-flip* code (`|0⟩ ↦ |+++⟩`, `|1⟩ ↦ |−−−⟩`), then each `|±⟩` is encoded with the
three-qubit *bit-flip* code into a **block** of three physical qubits — the cat state
`(|000⟩ ± |111⟩)/√2`. So the nine qubits form three blocks `(q₁q₂q₃)(q₄q₅q₆)(q₇q₈q₉)`, and the sign
`±` of block `b` plays the role the single qubit `|±⟩` played in the bare phase-flip code.

The phase-flip syndrome of the bare code compares the signs of adjacent qubits by measuring `X₁X₂`
and `X₂X₃` (measuring `X₁X₂` gives `+1` on `|+⟩|+⟩` or `|−⟩|−⟩`, `−1` on `|+⟩|−⟩` or `|−⟩|+⟩`). One
level up, the Shor phase-flip syndrome compares the signs of adjacent **blocks**. The elementary
fact behind Exercise 10.5 (proved in `AxQM/Postulates/API/ShorCodeBlock.lean`) is that `X⊗X⊗X` on a
block reads its `±` sign: `(X⊗X⊗X)(|000⟩ ± |111⟩) = ±(|000⟩ ± |111⟩)`. Hence "compare the signs of
blocks 1 and 2" is measuring `(X⊗X⊗X) ⊗ (X⊗X⊗X)` on those blocks, i.e. `X₁X₂X₃X₄X₅X₆`;
"compare blocks 2 and 3" is `X₄X₅X₆X₇X₈X₉`. (The two observables share the block-2 factor `X₄X₅X₆`,
exactly as `X₁X₂` and `X₂X₃` share `X₂` — and as the bit-flip syndrome observables `Z₁Z₂`, `Z₂Z₃`
share `Z₂`.)

## This file

The result is the **joint sign-readout law**: on a three-block product of sign-definite
cat states `shorCatProduct σ₁ σ₂ σ₃`, each syndrome observable acts by the product of the signs of
the two blocks it spans.

* `shorPhaseSyndromeX123456_hasEigenstate_shorCatProduct` /
  `shorPhaseSyndromeX456789_hasEigenstate_shorCatProduct` — `X₁X₂X₃X₄X₅X₆` is an eigen-observable
  with eigenvalue `(−1)^{σ₁+σ₂}`, and `X₄X₅X₆X₇X₈X₉` with eigenvalue `(−1)^{σ₂+σ₃}`. Measuring the
  observable yields exactly this `±1` value with certainty — it *is* the sign comparison of the two
  blocks.
* `shorPhaseSyndromeX123456_hasEigenstate_one_of_eq` /
  `shorPhaseSyndromeX456789_hasEigenstate_one_of_eq` — **no error detected**: when two adjacent
  blocks agree in sign the syndrome observable reads `+1`. In particular a logical codeword
  `shorCatProduct σ σ σ` (`σ = σ₁ = σ₂ = σ₃`; `|0_L⟩` at `σ = 0`, `|1_L⟩` at `σ = 1`) is a `+1`
  eigenstate of both — the no-error syndrome `(+,+)`.
* `shorPhaseSyndromeX123456_hasEigenstate_neg_one_of_ne` /
  `shorPhaseSyndromeX456789_hasEigenstate_neg_one_of_ne` — **phase flip detected**: when two
  adjacent blocks differ in sign (a phase flip occurred on one of them, flipping that block's sign)
  the syndrome observable reads `−1`.

**Localization.** A phase flip on any of block `b`'s three qubits flips `σ_b`, sending a codeword
`shorCatProduct σ σ σ` to `shorCatProduct` with `σ_b` flipped. The two syndrome readings then
localize `b`, by the laws above:

| error            | state (from `σσσ`)          | `X₁X₂X₃X₄X₅X₆` | `X₄X₅X₆X₇X₈X₉` |
| ---------------- | --------------------------- | :------------: | :------------: |
| none             | `shorCatProduct σ σ σ`      |       `+1`      |       `+1`      |
| block 1          | `shorCatProduct (σ+1) σ σ`  |       `−1`      |       `+1`      |
| block 2          | `shorCatProduct σ (σ+1) σ`  |       `−1`      |       `−1`      |
| block 3          | `shorCatProduct σ σ (σ+1)`  |       `+1`      |       `−1`      |

exactly the `X₁X₂` / `X₂X₃` dictionary of the bare phase-flip code, lifted from qubits to blocks —
which is what the exercise asks to show. Each row is an instance of the four `_of_eq` / `_of_ne`
theorems above.

## Supporting definitions

The construction (`shorReg`, the observables `X₁X₂X₃X₄X₅X₆` / `X₄X₅X₆X₇X₈X₉`, their involutivity,
the products `shorCatProduct`, and the vector-level sign-readout computation
`shorPhaseSyndromeX123456_op_shorCatProduct_vec` / `..X456789..`) is in
`AxQM/Postulates/API/ShorPhaseSyndrome.lean`. Compare the bit-flip syndrome of Exercise 10.3
(`AxQM/Postulates/API/BitFlipSyndromeMeasurement.lean` supporting `AxQM/NC/Ch10/Exercise10_3.lean`);
the block lemmas of this item's first half are in `AxQM/Postulates/API/ShorCodeBlock.lean`.
N&C Exercise 10.5, p. 433.
-/

noncomputable section

namespace AxQM

/-- **Exercise 10.5 — `X₁X₂X₃X₄X₅X₆` compares the signs of blocks 1 and 2.** On a three-block
product of sign-definite cat states, `X₁X₂X₃X₄X₅X₆` acts as the observable with eigenvalue
`(−1)^{σ₁+σ₂}`: measuring it yields `+1` iff the first two blocks have the same sign and `−1` iff
they differ. This is the first half of the phase-flip syndrome measurement. -/
theorem shorPhaseSyndromeX123456_hasEigenstate_shorCatProduct (σ₁ σ₂ σ₃ : Fin 2) :
    shorPhaseSyndromeX123456.HasEigenstate ((-1 : ℝ) ^ ((σ₁ : ℕ) + (σ₂ : ℕ)))
      (shorCatProduct σ₁ σ₂ σ₃) :=
  Observable.hasEigenstate_of_smul (one_smul ℂ _).symm (by
    rw [shorPhaseSyndromeX123456_op_shorCatProduct_vec]; congr 1; push_cast; ring)

/-- **Exercise 10.5 — `X₄X₅X₆X₇X₈X₉` compares the signs of blocks 2 and 3.** On a three-block
product of sign-definite cat states, `X₄X₅X₆X₇X₈X₉` acts as the observable with eigenvalue
`(−1)^{σ₂+σ₃}`: measuring it yields `+1` iff the last two blocks have the same sign and `−1` iff
they differ. This is the second half of the phase-flip syndrome measurement. -/
theorem shorPhaseSyndromeX456789_hasEigenstate_shorCatProduct (σ₁ σ₂ σ₃ : Fin 2) :
    shorPhaseSyndromeX456789.HasEigenstate ((-1 : ℝ) ^ ((σ₂ : ℕ) + (σ₃ : ℕ)))
      (shorCatProduct σ₁ σ₂ σ₃) :=
  Observable.hasEigenstate_of_smul (one_smul ℂ _).symm (by
    rw [shorPhaseSyndromeX456789_op_shorCatProduct_vec]; congr 1; push_cast; ring)

/-- **Exercise 10.5 — no phase flip between blocks 1 and 2 ⇒ syndrome `+1`.** When the first two
blocks agree in sign (`σ₁ = σ₂`), `X₁X₂X₃X₄X₅X₆` reads `+1`, since `(−1)^{σ₁+σ₂} = (−1)^{2σ₁} = 1`.
In particular every logical codeword `shorCatProduct σ σ σ` is a `+1` eigenstate — the no-error
syndrome. -/
theorem shorPhaseSyndromeX123456_hasEigenstate_one_of_eq {σ₁ σ₂ σ₃ : Fin 2} (h : σ₁ = σ₂) :
    shorPhaseSyndromeX123456.HasEigenstate 1 (shorCatProduct σ₁ σ₂ σ₃) := by
  have hpow : ((-1 : ℝ) ^ ((σ₁ : ℕ) + (σ₂ : ℕ))) = 1 := by
    rw [h, ← two_mul, pow_mul]; norm_num
  have hev := shorPhaseSyndromeX123456_hasEigenstate_shorCatProduct σ₁ σ₂ σ₃
  rwa [hpow] at hev

/-- **Exercise 10.5 — no phase flip between blocks 2 and 3 ⇒ syndrome `+1`.** When the last two
blocks agree in sign (`σ₂ = σ₃`), `X₄X₅X₆X₇X₈X₉` reads `+1`. -/
theorem shorPhaseSyndromeX456789_hasEigenstate_one_of_eq {σ₁ σ₂ σ₃ : Fin 2} (h : σ₂ = σ₃) :
    shorPhaseSyndromeX456789.HasEigenstate 1 (shorCatProduct σ₁ σ₂ σ₃) := by
  have hpow : ((-1 : ℝ) ^ ((σ₂ : ℕ) + (σ₃ : ℕ))) = 1 := by
    rw [h, ← two_mul, pow_mul]; norm_num
  have hev := shorPhaseSyndromeX456789_hasEigenstate_shorCatProduct σ₁ σ₂ σ₃
  rwa [hpow] at hev

/-- **Exercise 10.5 — a phase flip between blocks 1 and 2 ⇒ syndrome `−1`.** When the first two
blocks differ in sign (`σ₁ ≠ σ₂`, i.e. a phase flip occurred on one of them), `X₁X₂X₃X₄X₅X₆` reads
`−1`, since `(−1)^{σ₁+σ₂} = (−1)^1 = −1`. This is how the syndrome *detects* a phase flip. -/
theorem shorPhaseSyndromeX123456_hasEigenstate_neg_one_of_ne {σ₁ σ₂ σ₃ : Fin 2} (h : σ₁ ≠ σ₂) :
    shorPhaseSyndromeX123456.HasEigenstate (-1) (shorCatProduct σ₁ σ₂ σ₃) := by
  have hsum : (σ₁ : ℕ) + (σ₂ : ℕ) = 1 := by fin_cases σ₁ <;> fin_cases σ₂ <;> simp_all
  have hev := shorPhaseSyndromeX123456_hasEigenstate_shorCatProduct σ₁ σ₂ σ₃
  rwa [hsum, pow_one] at hev

/-- **Exercise 10.5 — a phase flip between blocks 2 and 3 ⇒ syndrome `−1`.** When the last two
blocks differ in sign (`σ₂ ≠ σ₃`), `X₄X₅X₆X₇X₈X₉` reads `−1`. -/
theorem shorPhaseSyndromeX456789_hasEigenstate_neg_one_of_ne {σ₁ σ₂ σ₃ : Fin 2} (h : σ₂ ≠ σ₃) :
    shorPhaseSyndromeX456789.HasEigenstate (-1) (shorCatProduct σ₁ σ₂ σ₃) := by
  have hsum : (σ₂ : ℕ) + (σ₃ : ℕ) = 1 := by fin_cases σ₂ <;> fin_cases σ₃ <;> simp_all
  have hev := shorPhaseSyndromeX456789_hasEigenstate_shorCatProduct σ₁ σ₂ σ₃
  rwa [hsum, pow_one] at hev

end AxQM
