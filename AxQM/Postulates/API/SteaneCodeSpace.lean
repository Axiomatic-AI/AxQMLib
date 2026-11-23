/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CSSCodeSpace
import AxQM.Concrete.SteaneCode

/-!
# The Steane code space is the joint `+1`-eigenspace of the six Figure-10.6 generators

The Steane `[[7,1,3]]` code is `CSS(C, C⊥)` with `C = ofParityCheck hammingParityCheck` the
`[7,4,3]` Hamming code and `C₂ = C⊥ = steaneDualCode` its `[7,3]` dual (Nielsen & Chuang §10.4.2).
Its six stabilizer generators of Figure 10.6 are the X- and Z-type Pauli strings `X^{hᵢ}`, `Z^{hᵢ}`
on the three rows `hᵢ` of the Hamming parity-check matrix `H`.

This file records the **Steane instantiation of the code-space equality** (Exercise 10.51) in
*generator form*: a state `ψ` fixed by all six generators lies in the Steane code space
`cssCodeSpace C C⊥ = span{ |x + C⊥⟩ : x ∈ C }`. The three rows `hᵢ` generate `C⊥` (they span its
row space, `Concrete.steaneDualCode_le_span_hammingParityCheck`), so fixing under the six
generators already forces fixing under *every* `X^v`/`Z^u` of the check matrix
(`mem_cssCodeSpace_of_span_le`) — no enumeration of the eight dual codewords is needed.

This is the "measuring `g₁,…,g₆` and fixing the signs to `+1` projects into the code" step of the
fault-tolerant `|0_L⟩` construction (`AxQM.NC.Ch10.Exercise10_73_FTencodedState`): the six
generator measurements have their `+1`-eigenspace equal to the two-dimensional Steane code space.
It is stated for the Pauli strings `bitString`/`phaseString`; the `Evolution` family
`steaneStabilizer` is definitionally `bitString`/`phaseString` of the rows.
-/

namespace AxQM

open AxQM.Concrete

/-- **The Steane code space is the six generators' joint `+1`-eigenspace** (Exercise 10.51,
generator form, Steane instantiation). Any state `ψ` fixed by the six Figure-10.6 stabilizer
generators — the X-type `X^{hᵢ} = bitString (hammingParityCheck i)` and the Z-type
`Z^{hᵢ} = phaseString (hammingParityCheck i)`, `i : Fin 3` — lies in the Steane code space
`cssCodeSpace C C⊥` (the ℂ-span of the coset codewords `|x + C⊥⟩`, `x ∈ C`).

The three rows `hᵢ` span the dual code `C⊥ = steaneDualCode`
(`steaneDualCode_le_span_hammingParityCheck`), which is `C₁⊥` for `C₁ = C`; and `C⊥ ⊆ C` is
dual-containing (`steaneDualCode_le_hammingCode`). So `mem_cssCodeSpace_of_span_le` (with
`S = T =` the rows) upgrades "fixed by the six generators" to "fixed by every check operator", i.e.
membership in `V_S = cssCodeSpace C C⊥`. This is the specification of "measuring `g₁,…,g₆` with all
outcomes `+1` projects the register into the Steane code space", the first stage of the
fault-tolerant `|0_L⟩` construction (Exercise 10.73). -/
theorem mem_cssCodeSpace_of_hammingParityCheck_op_eq_self {ψ : (bitReg (Fin 7)).space}
    (hX : ∀ i, (bitString (hammingParityCheck i)).op ψ = ψ)
    (hZ : ∀ i, (phaseString (hammingParityCheck i)).op ψ = ψ) :
    ψ ∈ cssCodeSpace (LinearCode.ofParityCheck hammingParityCheck) steaneDualCode := by
  refine mem_cssCodeSpace_of_span_le (S := Set.range hammingParityCheck)
    (T := Set.range hammingParityCheck) steaneDualCode_le_hammingCode
    steaneDualCode_le_span_hammingParityCheck steaneDualCode_le_span_hammingParityCheck ?_ ?_
  · rintro _ ⟨i, rfl⟩; exact hX i
  · rintro _ ⟨i, rfl⟩; exact hZ i

/-- **The Steane code space collapses onto the two logical codewords.** The full CSS code space
`cssCodeSpace C C⊥ = span{ |x + C⊥⟩ : x ∈ C }`, spanned over the sixteen Hamming codewords `x ∈ C`,
is contained in the two-dimensional span of the standard coset states `|0 + C⊥⟩` and `|𝟙 + C⊥⟩`. The
reason is the index-`2` coset structure (`Concrete.mem_steaneDualCode_or_add_one_mem`): each `x ∈ C`
lies in `C⊥` or in `𝟙 + C⊥`, and by coset invariance of the standard state (`cssStdState_add_mem`)
its codeword `|x + C⊥⟩` equals `|0 + C⊥⟩` (`= |0_L⟩`) or `|𝟙 + C⊥⟩` (`= |1_L⟩`) accordingly. This is
the classical two-logical-codeword count made explicit; combined with the "measuring
`g₁,…,g₆` projects into the code space" fact (`mem_cssCodeSpace_of_hammingParityCheck_op_eq_self`)
it identifies the joint `+1`-eigenspace of the six Figure-10.6 generators with the two-dimensional
`span{ |0_L⟩, |1_L⟩ }` — the Steane code space — which is the `InSteaneCode` predicate of the
fault-tolerant `|0_L⟩` construction (Exercise 10.73). -/
theorem cssCodeSpace_steaneDualCode_le_span :
    cssCodeSpace (LinearCode.ofParityCheck hammingParityCheck) steaneDualCode ≤
      Submodule.span ℂ
        {(cssStdState steaneDualCode 0).vec, (cssStdState steaneDualCode 1).vec} := by
  rw [cssCodeSpace, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  rcases mem_steaneDualCode_or_add_one_mem hx with h | h
  · -- `x ∈ C⊥`: the coset `x + C⊥` is `0 + C⊥`, so `|x + C⊥⟩ = |0_L⟩`.
    have hx0 : cssStdState steaneDualCode x = cssStdState steaneDualCode 0 := by
      have h0 := cssStdState_add_mem steaneDualCode h 0
      rwa [zero_add] at h0
    rw [hx0]
    exact Submodule.subset_span (Set.mem_insert _ _)
  · -- `x + 𝟙 ∈ C⊥`: the coset `x + C⊥` is `𝟙 + C⊥`, so `|x + C⊥⟩ = |1_L⟩`.
    have hx1 : cssStdState steaneDualCode x = cssStdState steaneDualCode 1 := by
      have hkey : (1 : Fin 7 → ZMod 2) + (x + 1) = x := by
        funext i
        have hchar : ∀ a : ZMod 2, (1 : ZMod 2) + (a + 1) = a := by decide
        simpa using hchar (x i)
      have h1 := cssStdState_add_mem steaneDualCode h 1
      rwa [hkey] at h1
    rw [hx1]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

end AxQM
