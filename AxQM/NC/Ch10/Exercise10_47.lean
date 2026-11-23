/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ShorStabilizer

/-!
# Nielsen & Chuang, Exercise 10.47 — the Fig 10.11 generators stabilize the Shor codewords

*(N&C §10.5.6, Fig 10.11, p. 468.)*

Verify generators of Fig 10.11 generate the two Shor-code codewords of (10.13).

## What the exercise asks

The **nine-qubit Shor code** (N&C §10.2) is a concatenation of the three-qubit phase-flip and
bit-flip codes, with the two logical codewords of Equation (10.13)

* `|0_L⟩ = shorCodeword 0 = ((|000⟩ + |111⟩)/√2)^{⊗3}`,
* `|1_L⟩ = shorCodeword 1 = ((|000⟩ − |111⟩)/√2)^{⊗3}`,

on the register `shorReg = bitFlipReg ⊗ (bitFlipReg ⊗ bitFlipReg)`, grouped into three blocks
`(q₁q₂q₃)(q₄q₅q₆)(q₇q₈q₉)`. Figure 10.11 lists eight stabilizer generators — six bit-flip (`Z`-type)
generators comparing adjacent qubits *within* a block, and two phase-flip (`X`-type) generators
comparing the signs of adjacent *blocks*:

| Fig 10.11 | operator       | this file / infrastructure |
| --------- | -------------- | -------------------------- |
| `g₁`      | `Z₁Z₂`         | `shorZ12`                  |
| `g₂`      | `Z₂Z₃`         | `shorZ23`                  |
| `g₃`      | `Z₄Z₅`         | `shorZ45`                  |
| `g₄`      | `Z₅Z₆`         | `shorZ56`                  |
| `g₅`      | `Z₇Z₈`         | `shorZ78`                  |
| `g₆`      | `Z₈Z₉`         | `shorZ89`                  |
| `g₇`      | `X₁X₂X₃X₄X₅X₆` | `shorPhaseSyndromeX123456` |
| `g₈`      | `X₄X₅X₆X₇X₈X₉` | `shorPhaseSyndromeX456789` |

(Figure 10.11 also lists the logical operators `Z̄ = X₁…X₉` and `X̄ = Z₁…Z₉`; these are *not*
stabilizer generators — they map the code space to itself nontrivially — and are the subject of
Exercise 10.48, not this one.) Since the code space `V_S` stabilized by `⟨g₁,…,g₈⟩` is spanned by
the two codewords, "the generators generate the codewords" is verified — following N&C §10.5.1, "to
see that a particular vector is stabilized by a group `S` we need only check that the vector is
stabilized by the generators" — by checking that **each generator fixes each codeword**,
`g |s_L⟩ = |s_L⟩`, i.e. the eigenvalue-`1` eigenstate relation `Observable.HasEigenstate 1`.

## What is proved, and how

`shorStabilizer : Fin 8 → Observable shorReg` collects the eight generators, and
`shorStabilizer_hasEigenstate_one_shorCodeword` is the main result:
**every generator stabilizes both codewords**. The two mechanisms are proved in
`AxQM/Postulates/API/ShorStabilizer.lean`:

* a `Z`-type generator fixes its block's cat state `(|000⟩ ± |111⟩)/√2` (matching bits give parity
  sign `+1`) and the identity fixes the other two blocks, so it fixes the whole codeword;
* an `X`-type generator reads `(−1)^{s+s} = +1` on a codeword, because the two blocks it spans carry
  the *same* sign `s`.

## Fidelity

The statement is the stabilization of the *physical* codewords (`PureState`s) by the *physical*
Pauli generators (`Observable`s), via the relation `Observable.HasEigenstate`. The generator
definitions and per-generator stabilization lemmas are in `AxQM/Postulates/API/ShorStabilizer.lean`;
this file assembles the Figure-10.11 family and states the result. Nothing is weakened: the
generators are exactly the eight of Figure 10.11 and the codewords are exactly (10.13).
-/

namespace AxQM

/-- **The eight stabilizer generators of Figure 10.11**, as a single family
`Fin 8 → Observable shorReg`: the six bit-flip (`Z`-type) generators `g₁,…,g₆` followed by the two
phase-flip (`X`-type) generators `g₇, g₈`. -/
noncomputable def shorStabilizer : Fin 8 → Observable shorReg :=
  ![shorZ12, shorZ23, shorZ45, shorZ56, shorZ78, shorZ89,
    shorPhaseSyndromeX123456, shorPhaseSyndromeX456789]

/-- **Nielsen & Chuang, Exercise 10.47.** Every one of the eight Figure-10.11 generators stabilizes
each Shor logical codeword `|s_L⟩` (eq. (10.13)): `gⱼ |s_L⟩ = |s_L⟩`. Since the two orthonormal
codewords span the code space stabilized by `⟨g₁,…,g₈⟩`, this verifies that the generators "generate
the two codewords". The `Z`-type cases fix each block's cat state; the `X`-type cases read the sign
`(−1)^{s+s} = +1` on a codeword. -/
theorem shorStabilizer_hasEigenstate_one_shorCodeword (s : Fin 2) (i : Fin 8) :
    (shorStabilizer i).HasEigenstate 1 (shorCodeword s) := by
  fin_cases i
  · exact shorZ12_hasEigenstate_one_shorCodeword s
  · exact shorZ23_hasEigenstate_one_shorCodeword s
  · exact shorZ45_hasEigenstate_one_shorCodeword s
  · exact shorZ56_hasEigenstate_one_shorCodeword s
  · exact shorZ78_hasEigenstate_one_shorCodeword s
  · exact shorZ89_hasEigenstate_one_shorCodeword s
  · exact shorPhaseSyndromeX123456_hasEigenstate_one_shorCodeword s
  · exact shorPhaseSyndromeX456789_hasEigenstate_one_shorCodeword s

end AxQM
