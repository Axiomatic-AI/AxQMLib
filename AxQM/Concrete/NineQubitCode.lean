/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCommutation

/-!
# Concrete: the nine-qubit Shor code stabilizer generators (Nielsen & Chuang Figure 10.11)

This file gives the eight stabilizer generators of the **nine-qubit Shor code** `[[9,1,3]]`, as
Pauli-string index vectors `Fin 9 → Fin 4` (`I = 0, X = 1, Y = 2, Z = 3`), together with the
structural fact needed to read off its syndrome-measuring circuit — that they pairwise commute (so
they can be measured jointly). The companion five-qubit generator data is
`Concrete.fiveQubitGenIdx`; the two are the inputs to the Figure-10.16-style syndrome circuits of
Nielsen & Chuang Exercise 10.60 (`NC/Ch10/Exercise10_60.lean`).

The generators are the eight operators of Figure 10.11 — six bit-flip (`Z`-type) checks comparing
adjacent qubits *within* each three-qubit block, and two phase-flip (`X`-type) checks comparing the
signs of adjacent *blocks*:

| Fig 10.11 | operator       | `shorGenIdx` row              |
| --------- | -------------- | ----------------------------- |
| `g₁`      | `Z₁Z₂`         | `![3,3,0,0,0,0,0,0,0]`         |
| `g₂`      | `Z₂Z₃`         | `![0,3,3,0,0,0,0,0,0]`         |
| `g₃`      | `Z₄Z₅`         | `![0,0,0,3,3,0,0,0,0]`         |
| `g₄`      | `Z₅Z₆`         | `![0,0,0,0,3,3,0,0,0]`         |
| `g₅`      | `Z₇Z₈`         | `![0,0,0,0,0,0,3,3,0]`         |
| `g₆`      | `Z₈Z₉`         | `![0,0,0,0,0,0,0,3,3]`         |
| `g₇`      | `X₁X₂X₃X₄X₅X₆` | `![1,1,1,1,1,1,0,0,0]`        |
| `g₈`      | `X₄X₅X₆X₇X₈X₉` | `![0,0,0,1,1,1,1,1,1]`        |

(This is the same stabilizer whose stabilization of the codewords is Exercise 10.47, there recorded
as the observable family `shorStabilizer` on the tensor register `shorReg`; here we keep only the
phase-free index data, which is all a syndrome circuit needs.) Everything is stated in terms of
Pauli-string index data (`Fin 9 → Fin 4`, `Concrete.pauliString`).
-/

namespace AxQM.Concrete

/-- The eight **nine-qubit Shor code generators** of Figure 10.11 as Pauli-string index vectors
`Fin 8 → (Fin 9 → Fin 4)` (`I = 0, X = 1, Y = 2, Z = 3`): six `Z`-type bit-flip checks
`Z₁Z₂, Z₂Z₃, Z₄Z₅, Z₅Z₆, Z₇Z₈, Z₈Z₉` and two `X`-type phase-flip checks `X₁⋯X₆, X₄⋯X₉`. -/
def shorGenIdx : Fin 8 → (Fin 9 → Fin 4) :=
  ![![3, 3, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 3, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 3, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 3, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 3, 3],
    ![1, 1, 1, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1, 1, 1]]

/-- The nine-qubit Shor code generators **pairwise commute** (Nielsen & Chuang Exercise 10.33: two
Pauli strings commute iff their symplectic pairing is even). The two `X`-type generators overlap
each `Z`-type generator in an even number of positions (two, when they meet), so every pair
commutes — the prerequisite for measuring all eight generators jointly to obtain the error
syndrome. A finite
`8 × 8` check over the symplectic criterion. -/
theorem shorGenIdx_commute (i j : Fin 8) :
    Commute (pauliString (shorGenIdx i)) (pauliString (shorGenIdx j)) := by
  rw [pauliString_commute_iff]
  fin_cases i <;> fin_cases j <;> decide

end AxQM.Concrete
