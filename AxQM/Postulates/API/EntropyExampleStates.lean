/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BlochStateEntropy
import AxQM.Concrete.EntropyExampleMatrices

/-!
# AxQM.Postulates.API — the three density matrices of Nielsen & Chuang Exercise 11.11

The three explicit `2 × 2` density matrices of Exercise 11.11, as `State qubit`s, together with the
**machine-checked identification of each with N&C's literal matrix**: `entropyExample…State_op`
proves that the underlying density operator of each state is `Matrix.toEuclideanCLM` of exactly the
matrix N&C writes down, by composing `blochState_op` with the concrete Bloch-matrix identities
`Concrete.blochMatrix_entropyExample{1,2,3}`.

* `entropyExampleZeroState`  = `blochState ![0, 0, 1]`     — N&C (11.41) `!![1,0;0,0] = |0⟩⟨0|`;
* `entropyExamplePlusState`  = `blochState ![1, 0, 0]`     — N&C (11.42) `½!![1,1;1,1] = |+⟩⟨+|`;
* `entropyExampleMixedState` = `blochState ![2/3, 0, 1/3]` — N&C (11.43) `⅓!![2,1;1,1]`.

The von Neumann entropies of these states are the statements of Exercise 11.11, in
`AxQM/NC/Ch11/Exercise11_11.lean`, which uses these states.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

open Matrix

/-- **N&C (11.41):** the density matrix `!![1, 0; 0, 0] = |0⟩⟨0|`, realised as the Bloch state
`blochState ![0, 0, 1] = ½(I + Z)`. Its matrix identity is `entropyExampleZeroState_op`. -/
def entropyExampleZeroState : State qubit :=
  blochState ![0, 0, 1]
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two])

/-- **N&C (11.42):** the density matrix `½ !![1, 1; 1, 1] = |+⟩⟨+|`, realised as the Bloch state
`blochState ![1, 0, 0] = ½(I + X)`. Its matrix identity is `entropyExamplePlusState_op`. -/
def entropyExamplePlusState : State qubit :=
  blochState ![1, 0, 0]
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two])

/-- **N&C (11.43):** the mixed density matrix `⅓ !![2, 1; 1, 1]`, realised as the Bloch state
`blochState ![2/3, 0, 1/3] = ½(I + ⅔X + ⅓Z)`. Matrix identity: `entropyExampleMixedState_op`. -/
def entropyExampleMixedState : State qubit :=
  blochState ![2 / 3, 0, 1 / 3]
    (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two])

/-- **`entropyExampleZeroState` is N&C's matrix (11.41).** Its density operator is
`Matrix.toEuclideanCLM !![1, 0; 0, 0]`, obtained from `blochState_op` and
`Concrete.blochMatrix_entropyExample1`. -/
theorem entropyExampleZeroState_op :
    entropyExampleZeroState.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) !![1, 0; 0, 0] := by
  rw [entropyExampleZeroState, blochState_op, Concrete.blochMatrix_entropyExample1]

/-- **`entropyExamplePlusState` is N&C's matrix (11.42).** Its density operator is
`Matrix.toEuclideanCLM (½ !![1, 1; 1, 1])`, obtained from `blochState_op` and
`Concrete.blochMatrix_entropyExample2`. -/
theorem entropyExamplePlusState_op :
    entropyExamplePlusState.op =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) !![2⁻¹, 2⁻¹; 2⁻¹, 2⁻¹] := by
  rw [entropyExamplePlusState, blochState_op, Concrete.blochMatrix_entropyExample2]

/-- **`entropyExampleMixedState` is N&C's matrix (11.43).** Its density operator is
`Matrix.toEuclideanCLM (⅓ !![2, 1; 1, 1])`, obtained from `blochState_op` and
`Concrete.blochMatrix_entropyExample3`. -/
theorem entropyExampleMixedState_op :
    entropyExampleMixedState.op =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) !![2 / 3, 1 / 3; 1 / 3, 1 / 3] := by
  rw [entropyExampleMixedState, blochState_op, Concrete.blochMatrix_entropyExample3]

end AxQM
