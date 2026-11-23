/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix

/-!
# AxQM.Concrete — the three density matrices of Nielsen & Chuang Exercise 11.11

The concrete `2 × 2` density matrices whose von Neumann entropy Nielsen & Chuang Exercise 11.11
asks one to compute, each identified with a Bloch matrix `Concrete.blochMatrix r = ½(I + r⃗·σ⃗)`:

* (11.41) `ρ = !![1, 0; 0, 0] = |0⟩⟨0|`  is  `blochMatrix ![0, 0, 1] = ½(I + Z)`;
* (11.42) `ρ = ½ !![1, 1; 1, 1] = |+⟩⟨+|`  is  `blochMatrix ![1, 0, 0] = ½(I + X)`;
* (11.43) `ρ = ⅓ !![2, 1; 1, 1]`  is  `blochMatrix ![2/3, 0, 1/3] = ½(I + ⅔X + ⅓Z)`.

These are pure matrix identities. Each is a direct instantiation of `Concrete.blochMatrix_eq`. They
are used by the `State.op` identities `entropyExample{Zero,Plus,Mixed}State_op` in
`AxQM/Postulates/API/EntropyExampleStates.lean`, which compose them with `blochState_op` to check
that the Exercise-11.11 states are exactly N&C's matrices (11.41)–(11.43); see
`AxQM/NC/Ch11/Exercise11_11.lean`.
-/

noncomputable section

namespace AxQM.Concrete

/-- **N&C (11.41):** `blochMatrix ![0,0,1] = !![1,0;0,0]`, i.e. `½(I + Z) = |0⟩⟨0|`. -/
theorem blochMatrix_entropyExample1 :
    blochMatrix ![0, 0, 1] = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochMatrix_eq]
  norm_num

/-- **N&C (11.42):** `blochMatrix ![1,0,0] = ½ !![1,1;1,1]`, i.e. `½(I + X) = |+⟩⟨+|`. -/
theorem blochMatrix_entropyExample2 :
    blochMatrix ![1, 0, 0] = !![2⁻¹, 2⁻¹; 2⁻¹, 2⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochMatrix_eq]

/-- **N&C (11.43):** `blochMatrix ![2/3,0,1/3] = ⅓ !![2,1;1,1]`, i.e. `½(I + ⅔X + ⅓Z)`. -/
theorem blochMatrix_entropyExample3 :
    blochMatrix ![2 / 3, 0, 1 / 3] = !![2 / 3, 1 / 3; 1 / 3, 1 / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochMatrix_eq] <;> norm_num

end AxQM.Concrete
