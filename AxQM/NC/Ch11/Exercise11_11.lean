/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyExampleStates
import AxQM.NC.Ch2.Exercise2_72
import AxQM.NC.Ch11.Theorem11_8

/-!
# Nielsen & Chuang, Exercise 11.11 — example calculations of von Neumann entropy

**Exercise 11.11 (Example calculations of entropy).** Compute the von Neumann entropy `S(ρ)` of
the three `2 × 2` density matrices

* (11.41)  `ρ = !![1, 0; 0, 0]`      (`= |0⟩⟨0|`, a pure state),
* (11.42)  `ρ = ½ !![1, 1; 1, 1]`    (`= |+⟩⟨+|`, a pure state),
* (11.43)  `ρ = ⅓ !![2, 1; 1, 1]`    (a genuinely mixed state).

Each is a single-qubit **Bloch state** `½(I + r⃗·σ⃗)`. The three states, and the machine-checked
identification of each with N&C's literal matrix, are `entropyExample{Zero,Plus,Mixed}State` and
`entropyExample{Zero,Plus,Mixed}State_op` in `AxQM/Postulates/API/EntropyExampleStates.lean`:

* (11.41) `= blochState ![0, 0, 1]`      (`½(I + Z)`), `‖r⃗‖ = 1`;
* (11.42) `= blochState ![1, 0, 0]`      (`½(I + X)`), `‖r⃗‖ = 1`;
* (11.43) `= blochState ![2/3, 0, 1/3]`  (`½(I + ⅔X + ⅓Z)`), `‖r⃗‖ = √5/3 < 1`.

## Results (the item's formalisation)

* `vonNeumannEntropy_entropyExampleZeroState`, `vonNeumannEntropy_entropyExamplePlusState` —
  **`S(ρ) = 0`** for (11.41) and (11.42): both have `‖r⃗‖ = 1`, hence are pure
  (`blochState_isPure_iff_norm_one`), and a pure state has zero entropy
  (`State.vonNeumannEntropy_eq_zero_of_isPure`).
* `vonNeumannEntropy_entropyExampleMixedState` — **`S(ρ) = H((3+√5)/6, (3−√5)/6)`** for (11.43):
  its eigenvalues are `(1 ± √5/3)/2 = (3 ± √5)/6`, and the entropy is the binary Shannon entropy of
  that spectrum, via the reusable `blochState_vonNeumannEntropy` (`S(½(I+r⃗·σ⃗)) = H((1±‖r⃗‖)/2)`).

The eigenvalues of (11.43) have no closed form as a rational multiple of `log`, so — exactly as in
N&C — the answer is left as this Shannon entropy of the explicit eigenvalue pair (≈ 0.55 bits).
`Real.entropy` (and hence `State.vonNeumannEntropy`) is the Shannon/von-Neumann entropy in nats;
the identities here are base-independent statements of N&C's content.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **N&C (11.41): `S(|0⟩⟨0|) = 0`.** The state `½(I + Z)` (`= !![1,0;0,0]`, by
`entropyExampleZeroState_op`) has Bloch vector of norm one, hence is pure
(`blochState_isPure_iff_norm_one`), and a pure state has zero von Neumann entropy. -/
theorem vonNeumannEntropy_entropyExampleZeroState :
    entropyExampleZeroState.vonNeumannEntropy = 0 := by
  apply State.vonNeumannEntropy_eq_zero_of_isPure
  unfold entropyExampleZeroState
  rw [blochState_isPure_iff_norm_one]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]

/-- **N&C (11.42): `S(|+⟩⟨+|) = 0`.** The state `½(I + X)` (`= ½!![1,1;1,1]`, by
`entropyExamplePlusState_op`) has Bloch vector of norm one, hence is pure
(`blochState_isPure_iff_norm_one`), and a pure state has zero von Neumann entropy. -/
theorem vonNeumannEntropy_entropyExamplePlusState :
    entropyExamplePlusState.vonNeumannEntropy = 0 := by
  apply State.vonNeumannEntropy_eq_zero_of_isPure
  unfold entropyExamplePlusState
  rw [blochState_isPure_iff_norm_one]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]

/-- **N&C (11.43): `S(⅓ !![2,1;1,1]) = H((3+√5)/6, (3−√5)/6)`.** The mixed qubit state
(`= ⅓!![2,1;1,1]`, by `entropyExampleMixedState_op`) has Bloch vector `(2/3, 0, 1/3)` of norm
`√5/3`, so its eigenvalues are `(1 ± √5/3)/2 = (3 ± √5)/6`, and its entropy is the binary Shannon
entropy of that spectrum, via `blochState_vonNeumannEntropy`. -/
theorem vonNeumannEntropy_entropyExampleMixedState :
    entropyExampleMixedState.vonNeumannEntropy =
      Real.entropy ![(3 + Real.sqrt 5) / 6, (3 - Real.sqrt 5) / 6] := by
  have hsum : (![2 / 3, 0, 1 / 3] : Fin 3 → ℝ) 0 ^ 2 + (![2 / 3, 0, 1 / 3] : Fin 3 → ℝ) 1 ^ 2
      + (![2 / 3, 0, 1 / 3] : Fin 3 → ℝ) 2 ^ 2 = 5 / 9 := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  have hsqrt : Real.sqrt (5 / 9 : ℝ) = Real.sqrt 5 / 3 := by
    rw [show (5 : ℝ) / 9 = 5 * (1 / 3) ^ 2 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    ring
  unfold entropyExampleMixedState
  rw [blochState_vonNeumannEntropy _ _ (by rw [hsum]; norm_num), hsum, hsqrt]
  congr 1
  funext i
  fin_cases i <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one] <;> ring

end AxQM
