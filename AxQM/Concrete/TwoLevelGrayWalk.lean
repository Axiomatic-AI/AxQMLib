/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelSwapChain
import AxQM.Concrete.GrayCode

/-!
# Concrete: the Gray-code swap chain relocates a two-level unitary onto a bit-adjacent pair

(Nielsen & Chuang §4.5.2, first stage.)

Nielsen & Chuang §4.5.2 (p. 191–193) realises a two-level unitary `U` on `n` qubits — one acting
non-trivially only on the two computational basis states `|s⟩` and `|t⟩` (`s ≠ t` two distinct
`n`-bit strings) — as a circuit of single-qubit and `CNOT` gates. The first stage *walks a Gray
code* `g₁ = s, g₂, …, g_m = t` from `s` to `t`: a sequence of basis-state swaps
`|g₁⟩ ↔ |g₂⟩, …, |g_{m-2}⟩ ↔ |g_{m-1}⟩` moves the two active states of `U` from `{s, t}` to
`{g_{m-1}, t}`, **two basis states differing in exactly one bit** (adjacent Gray-code words), at
which point the two-level unitary is a *controlled single-qubit gate* ready for the controlled-`Ũ`
step; the swaps are then undone.

This file assembles that first stage into a single statement, joining the two halves already in the
library:

* the **matrix engine** `swapConj_swapChain_support` (`Concrete/TwoLevelSwapChain.lean`) —
  conjugating a two-level unitary with support `{s', w'}` by the swap chain of a path with head
  `s'`, last entry `e'`, and `w'` off the path relocates the support to `{e', w'}`, *at the raw
  `Fin d` index level*;
* the **combinatorial input** from `Concrete/GrayCode.lean` — for the path
  `(grayCode s t).dropLast = [g₁, …, g_{m-1}]`: its head is `s` (`grayCode_dropLast_head?`), its
  last entry is bit-adjacent to
  `t` (`grayCode_dropLast_getLast?_differsInOneBit`), and `t` lies off it
  (`grayCode_getLast_not_mem_dropLast`).

The bridge is any encoding `enc : (Fin m → Fin 2) ≃ Fin d` of the `m`-bit strings as the
`d = 2 ^ m` computational-basis indices (e.g. `finFunctionFinEquiv`); pushing the Gray-code path
through it turns
the bit-string combinatorics into a `Fin d` path the swap-chain engine consumes. The result,
`swapConj_swapChain_grayCode_support`, is the §4.5.2 first-stage milestone: *conjugating a two-level
unitary supported on `{s, t}` by the Gray-code swap chain yields a two-level unitary supported on a
pair of basis states differing in a single bit.*

## Use

This is the shared §4.5.2 first-stage assembly used by Exercise 4.43's `n`-qubit lift; the
statement of Exercise 4.43 is in `AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The Gray-code swap chain relocates a two-level unitary's active pair onto two basis states
differing in a single bit** — Nielsen & Chuang §4.5.2's first stage (eqs. 4.54–4.57), assembled.

Fix an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of `m`-bit strings as the `d = 2 ^ m` computational
basis indices. If `U` is unitary and acts non-trivially only on the two basis states
`{enc s, enc t}` for distinct bit-strings `s ≠ t`, then conjugating `U` by the swap chain of the
Gray-code path `(grayCode s t).dropLast` (mapped into `Fin d` by `enc`) is again unitary and acts
non-trivially only on `{enc e, enc t}` for some bit-string `e` with `differsInOneBit e t` — i.e. the
relocated active pair `{enc e, enc t}` differs in **exactly one bit**, the form of a *controlled
single-qubit gate*.

The proof reads the three path facts (`grayCode_dropLast_head?`,
`grayCode_dropLast_getLast?_differsInOneBit`, `grayCode_getLast_not_mem_dropLast`) into the
`enc`-image of the path via `List.head?_map` / `List.getLast?_map` / `List.mem_map` and injectivity
of `enc`, then feeds them to the matrix engine `swapConj_swapChain_support`. -/
theorem swapConj_swapChain_grayCode_support {m d : ℕ} (enc : (Fin m → Fin 2) ≃ Fin d)
    {s t : Fin m → Fin 2} (hst : s ≠ t) {U : Matrix (Fin d) (Fin d) ℂ}
    (hunit : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hsupp : ∀ i j : Fin d, (i ≠ enc s ∧ i ≠ enc t) ∨ (j ≠ enc s ∧ j ≠ enc t) →
      U i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j) :
    ∃ e : Fin m → Fin 2, differsInOneBit e t ∧
      swapConj (swapChain ((grayCode s t).dropLast.map enc)) U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        ∀ i j : Fin d, (i ≠ enc e ∧ i ≠ enc t) ∨ (j ≠ enc e ∧ j ≠ enc t) →
          swapConj (swapChain ((grayCode s t).dropLast.map enc)) U i j
            = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  obtain ⟨e, he, hdiff⟩ := grayCode_dropLast_getLast?_differsInOneBit s t hst
  refine ⟨e, hdiff, ?_⟩
  have hhead : ((grayCode s t).dropLast.map enc).head? = some (enc s) := by
    rw [List.head?_map, grayCode_dropLast_head? s t hst]; rfl
  have hlast : ((grayCode s t).dropLast.map enc).getLast? = some (enc e) := by
    rw [List.getLast?_map, he]; rfl
  have hnotmem : enc t ∉ (grayCode s t).dropLast.map enc := by
    rw [List.mem_map]
    rintro ⟨x, hx, hxe⟩
    exact grayCode_getLast_not_mem_dropLast s t (by rwa [enc.injective hxe] at hx)
  exact swapConj_swapChain_support hhead hlast hnotmem hunit hsupp

end AxQM.Concrete
