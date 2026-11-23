/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.HammingCode743
import ToMathlib.InformationTheory.Coding.DualCode

/-!
# Concrete: the dual `[7, 3]` Hamming code `C₂ = C⊥` of the Steane construction

This file records the classical code `C₂` and the three orthogonality facts about
the rows of the Hamming parity-check matrix that drive the Steane-code stabilizer verification
(Nielsen & Chuang, Exercise 10.32, formalised in `AxQM.NC.Ch10.Exercise10_32`).

The Steane code is `CSS(C₁, C₂)` with `C₁ = C` the `[7, 4, 3]` Hamming code and `C₂ = C⊥` its dual,
the `[7, 3, 4]` code (N&C §10.4.2). Here `C = LinearCode.ofParityCheck hammingParityCheck` (the
kernel of `H`, eq. (10.76)) and `C₂ = C⊥` is `steaneDualCode`. The eight codewords of `C₂` are the
kets summed in N&C's logical `|0_L⟩` (eq. (10.78)).

## Main results

Writing `hᵢ = hammingParityCheck i` for the `i`-th row of `H` (`i : Fin 3`):

* `steaneDualCode` — the dual code `C₂ = C⊥`.
* `hammingParityCheck_row_mem_code` — each `hᵢ` is a Hamming **codeword** (`hᵢ ∈ C`), i.e.
  `H *ᵥ hᵢ = 0`. This is the **dual-containing** property `C⊥ ⊆ C` at the level of the generators
  (`H Hᵀ = 0`), the fact that makes `CSS(C, C⊥)` a valid CSS code.
* `hammingParityCheck_row_mem_steaneDualCode` — each `hᵢ` lies in the **dual** `C₂ = C⊥` (rows of a
  parity-check matrix are orthogonal to the code): this makes `X^{hᵢ}` an X-type stabilizer.
* `hammingParityCheck_row_dotProduct_steaneDualCode` — each `hᵢ` is orthogonal to every dual
  codeword `y ∈ C₂` (`hᵢ · y = 0`): the **self-orthogonality** of `C₂`, which makes `Z^{hᵢ}` a
  Z-type stabilizer of `|0_L⟩`. It follows from `hᵢ ∈ C` and the definition of the dual.
* `hammingParityCheck_row_dotProduct_one` — each `hᵢ` has **even weight** (`hᵢ · 𝟙 = 0`): this makes
  `Z^{hᵢ}` a Z-type stabilizer of `|1_L⟩ = |𝟙 + C₂⟩` as well.
* `mem_steaneDualCode_or_add_one_mem` — the **two-coset structure** `[C₁ : C₂] = 2`: every Hamming
  codeword `x ∈ C₁` lies in `C₂` or in the nontrivial coset `𝟙 + C₂` (i.e. `x + 𝟙 ∈ C₂`). This is
  the classical fact behind the two logical codewords `|0_L⟩ = |0 + C₂⟩`, `|1_L⟩ = |𝟙 + C₂⟩`, and it
  collapses the code space onto their two-dimensional span. Proved via the decidable row-combination
  presentation `mem_steaneDualCode_iff_exists` (`C₂` is the row span of `H`,
  `steaneDualCode_eq_span_hammingParityCheck`).
-/

namespace AxQM.Concrete

open Matrix

/-- The **dual `[7, 3]` Hamming code** `C₂ = C⊥` of the Steane construction (Nielsen & Chuang,
§10.4.2): the dual of the `[7, 4, 3]` Hamming code `C = ofParityCheck hammingParityCheck` (the
kernel of `H`). Its eight codewords are the kets summed in the Steane `|0_L⟩` (eq. 10.78). -/
noncomputable def steaneDualCode : LinearCode (ZMod 2) (Fin 7) :=
  LinearCode.dual (LinearCode.ofParityCheck hammingParityCheck)

noncomputable instance : DecidablePred (· ∈ steaneDualCode) := Classical.decPred _

/-- **Each row of `H` is a Hamming codeword** (`hᵢ ∈ C`, i.e. `H *ᵥ hᵢ = 0`): the rows of the
parity-check matrix `H` (eq. (10.76)) are annihilated by `H`, which is the matrix identity
`H Hᵀ = 0`. Equivalently the dual `C⊥` is contained in `C` (the code is **dual-containing**), the
constraint `C₂ ⊂ C₁` that makes the Steane `CSS(C, C⊥)` a valid CSS code. -/
theorem hammingParityCheck_row_mem_code (i : Fin 3) :
    hammingParityCheck i ∈ LinearCode.ofParityCheck hammingParityCheck := by
  rw [LinearCode.mem_ofParityCheck_iff]
  fin_cases i <;> decide

/-- **Each row of `H` lies in the dual code** `hᵢ ∈ C₂ = C⊥`: a row `hᵢ` of the parity-check matrix
is orthogonal to every codeword `x ∈ C` because `hᵢ · x = (H *ᵥ x)ᵢ = 0`. This is what makes the
bit-flip string `X^{hᵢ}` a stabilizer of the Steane codewords. -/
theorem hammingParityCheck_row_mem_steaneDualCode (i : Fin 3) :
    hammingParityCheck i ∈ steaneDualCode := by
  rw [steaneDualCode, LinearCode.mem_dual_iff]
  intro x hx
  rw [LinearCode.mem_ofParityCheck_iff] at hx
  rw [dotProduct_comm]
  calc hammingParityCheck i ⬝ᵥ x = (hammingParityCheck *ᵥ x) i := rfl
    _ = 0 := by rw [hx]; rfl

/-- **Self-orthogonality of `C₂`**: each row `hᵢ` is orthogonal to every dual codeword `y ∈ C₂`
(`hᵢ · y = 0`). Since `hᵢ ∈ C` (`hammingParityCheck_row_mem_code`) and `y ∈ C₂ = C⊥`, orthogonality
is the defining property of the dual. This makes the phase-flip string `Z^{hᵢ}` a stabilizer of
`|0_L⟩ = |0 + C₂⟩`. -/
theorem hammingParityCheck_row_dotProduct_steaneDualCode (i : Fin 3) {y : Fin 7 → ZMod 2}
    (hy : y ∈ steaneDualCode) : hammingParityCheck i ⬝ᵥ y = 0 := by
  rw [steaneDualCode, LinearCode.mem_dual_iff] at hy
  exact hy (hammingParityCheck i) (hammingParityCheck_row_mem_code i)

/-- **Each row of `H` has even weight** (`hᵢ · 𝟙 = 0`): the dot product of a row with the all-ones
word is its Hamming weight mod `2`, and every row of `H` has weight `4`. This makes `Z^{hᵢ}` a
stabilizer of `|1_L⟩ = |𝟙 + C₂⟩` as well (the coset representative `𝟙` contributes `hᵢ · 𝟙 = 0`). -/
theorem hammingParityCheck_row_dotProduct_one (i : Fin 3) :
    hammingParityCheck i ⬝ᵥ (1 : Fin 7 → ZMod 2) = 0 := by
  fin_cases i <;> decide

/-- **The all-ones word `𝟙` is a Hamming codeword** (`𝟙 ∈ C₁`, i.e. `H *ᵥ 𝟙 = 0`): every row of the
parity-check matrix `H` (eq. (10.76)) has even weight `4`, so `H *ᵥ 𝟙 = 0`. This is what makes `𝟙`
an eligible representative of the nontrivial coset `𝟙 + C₂` in `C₁ / C₂` (the Steane `|1_L⟩`), and —
being in `C₁ = C₂⊥⊥` — the reason `𝟙` is orthogonal to *every* dual codeword. -/
theorem one_mem_ofParityCheck_hammingParityCheck :
    (1 : Fin 7 → ZMod 2) ∈ LinearCode.ofParityCheck hammingParityCheck := by
  rw [LinearCode.mem_ofParityCheck_iff]
  decide

/-- **Every dual codeword `y ∈ C₂` has even weight** (`𝟙 · y = 0`): the all-ones word `𝟙` lies in
`C₁` (`one_mem_ofParityCheck_hammingParityCheck`) and `C₂ = C₁⊥`, so `𝟙 · y = 0` for every `y ∈ C₂`
by the defining orthogonality of the dual. This is the fact behind `Z̄ = Z^{𝟙}` acting as logical
`Z`: it fixes `|0_L⟩` (all kets even weight, sign `+1`) and negates `|1_L⟩` (all kets odd weight,
sign `−1`) — Nielsen & Chuang, Exercise 10.52. -/
theorem steaneDualCode_dotProduct_one {y : Fin 7 → ZMod 2} (hy : y ∈ steaneDualCode) :
    (1 : Fin 7 → ZMod 2) ⬝ᵥ y = 0 := by
  rw [steaneDualCode, LinearCode.mem_dual_iff] at hy
  exact hy 1 one_mem_ofParityCheck_hammingParityCheck

/-- **`C₂ = C⊥` is spanned by the rows of the parity-check matrix `H`.** The dual of a
parity-check code is its *row space*: `(ker H·ᵥ)⊥ = range(·ᵥ H)` (`LinearCode.dual_ker_mulVecLin`),
and each vector of the row space `y ᵥ* H = ∑ᵢ yᵢ·hᵢ` is a `ZMod 2`-combination of the rows `hᵢ`.
This exhibits the three rows `h₀, h₁, h₂` as a **generating set** of `C₂`, so a state fixed by the
three generators `X^{hᵢ}` (resp. `Z^{hᵢ}`) is fixed by `X^v` (resp. `Z^v`) for *every* `v ∈ C₂`. -/
theorem steaneDualCode_le_span_hammingParityCheck :
    (steaneDualCode : Submodule (ZMod 2) (Fin 7 → ZMod 2)) ≤
      Submodule.span (ZMod 2) (Set.range hammingParityCheck) := by
  intro v hv
  rw [steaneDualCode,
    show LinearCode.ofParityCheck hammingParityCheck = hammingParityCheck.mulVecLin.ker from rfl,
    LinearCode.dual_ker_mulVecLin] at hv
  obtain ⟨y, rfl⟩ := hv
  rw [Matrix.vecMulLinear_apply, Matrix.vecMul_eq_sum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The Steane code is dual-containing**, `C₂ = C⊥ ⊆ C₁ = C`: every dual codeword is a combination
of the rows `hᵢ` (`steaneDualCode_le_span_hammingParityCheck`), and each row `hᵢ` is itself a
Hamming codeword (`hammingParityCheck_row_mem_code`, i.e. `H Hᵀ = 0`). This `C₂ ≤ C₁` inclusion
is the constraint that makes `CSS(C, C⊥)` a valid CSS code (the standing hypothesis of Ex 10.51). -/
theorem steaneDualCode_le_hammingCode :
    (steaneDualCode : Submodule (ZMod 2) (Fin 7 → ZMod 2)) ≤
      LinearCode.ofParityCheck hammingParityCheck :=
  steaneDualCode_le_span_hammingParityCheck.trans <| Submodule.span_le.mpr <| by
    rintro _ ⟨i, rfl⟩; exact hammingParityCheck_row_mem_code i

/-- **`C₂ = C⊥` is exactly the row space of `H`.** The dual is contained in the row span
(`steaneDualCode_le_span_hammingParityCheck`) and conversely each row `hᵢ` is a dual codeword
(`hammingParityCheck_row_mem_steaneDualCode`), so `C₂` equals `span_{ZMod 2}{h₀, h₁, h₂}`. This is
the presentation of `C₂` by its three generators used to make membership decidable
(`mem_steaneDualCode_iff_exists`). -/
theorem steaneDualCode_eq_span_hammingParityCheck :
    (steaneDualCode : Submodule (ZMod 2) (Fin 7 → ZMod 2)) =
      Submodule.span (ZMod 2) (Set.range hammingParityCheck) :=
  le_antisymm steaneDualCode_le_span_hammingParityCheck
    (Submodule.span_le.mpr <| by
      rintro _ ⟨i, rfl⟩; exact hammingParityCheck_row_mem_steaneDualCode i)

/-- **Decidable membership in `C₂`**: `x ∈ C₂ = C⊥` iff `x` is a `ZMod 2`-combination
`∑ᵢ cᵢ hᵢ` of the three parity-check rows (`steaneDualCode_eq_span_hammingParityCheck` with
`Submodule.mem_span_range_iff_exists_fun`). The right-hand side ranges over the eight functions
`c : Fin 3 → ZMod 2`, so it is `Decidable` — the form in which `mem_steaneDualCode_or_add_one_mem`
checks coset membership by `decide` (the dual's own `DecidablePred` is `Classical.decPred`). -/
theorem mem_steaneDualCode_iff_exists {x : Fin 7 → ZMod 2} :
    x ∈ steaneDualCode ↔ ∃ c : Fin 3 → ZMod 2, ∑ i, c i • hammingParityCheck i = x := by
  rw [steaneDualCode_eq_span_hammingParityCheck]
  exact Submodule.mem_span_range_iff_exists_fun _

set_option maxRecDepth 4000 in
/-- **The two cosets of `C₂` in `C₁`, in decidable form.** Every Hamming codeword `x` (`H *ᵥ x = 0`)
either is a `ZMod 2`-combination of the parity-check rows (`x ∈ C₂`) or becomes one after adding the
all-ones word (`x + 𝟙 ∈ C₂`). A finite `decide` over the `128` words `x : Fin 7 → ZMod 2` satisfying
`H *ᵥ x = 0`, each tested against the eight row-combinations. This is the classical index-`2` fact
`[C₁ : C₂] = 2` (`|C₁| = 16`, `|C₂| = 8`) with `𝟙` a representative of the nontrivial coset,
delivered without a cardinality argument. -/
private theorem hammingCode_two_coset (x : Fin 7 → ZMod 2) (hx : hammingParityCheck *ᵥ x = 0) :
    (∃ c : Fin 3 → ZMod 2, ∑ i, c i • hammingParityCheck i = x) ∨
    (∃ c : Fin 3 → ZMod 2, ∑ i, c i • hammingParityCheck i = x + 1) := by
  revert hx; revert x; decide

/-- **The Steane code is the union of two `C₂`-cosets** (index `2`): a Hamming codeword
`x ∈ C₁ = ofParityCheck H` lies either in the dual code `C₂ = C⊥` or in its nontrivial coset
`𝟙 + C₂` (equivalently `x + 𝟙 ∈ C₂`, since `𝟙 = −𝟙` in characteristic two). This is the classical
core of the "two logical codewords" of the Steane code: the two cosets `0 + C₂` and `𝟙 + C₂`
correspond to `|0_L⟩` and `|1_L⟩`, and it is what collapses the `16`-fold span
`span{ |x + C₂⟩ : x ∈ C₁ }` of the code space onto the two-dimensional
`span{ |0_L⟩, |1_L⟩ }`. -/
theorem mem_steaneDualCode_or_add_one_mem {x : Fin 7 → ZMod 2}
    (hx : x ∈ LinearCode.ofParityCheck hammingParityCheck) :
    x ∈ steaneDualCode ∨ x + 1 ∈ steaneDualCode := by
  rw [LinearCode.mem_ofParityCheck_iff] at hx
  exact (hammingCode_two_coset x hx).imp
    mem_steaneDualCode_iff_exists.mpr mem_steaneDualCode_iff_exists.mpr

end AxQM.Concrete
