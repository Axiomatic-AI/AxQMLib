/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BlochStateMix

/-!
# AxQM.Postulates.API — the mixed qubit state of Nielsen & Chuang Exercise 11.12

Nielsen & Chuang, Exercise 11.12 (*Comparison of quantum and classical entropies*) forms the
one-parameter family of **mixed qubit states**

`ρ(p) = p |0⟩⟨0| + (1 − p) |+⟩⟨+|`,   where `|+⟩ = (|0⟩ + |1⟩)/√2`,

a probabilistic mixture of the two *pure* states `|0⟩⟨0|` and `|+⟩⟨+|` with weights `p` and
`1 − p` (`0 ≤ p ≤ 1`). Its two constituents are exactly the density matrices `!![1, 0; 0, 0]`
(N&C (11.41)) and `½ !![1, 1; 1, 1]` (N&C (11.42)) of Exercise 11.11 — here realised as the Bloch
states `blochState ![0, 0, 1] = ½(I + Z)` and `blochState ![1, 0, 0] = ½(I + X)` (their machine
checked matrix identities are `entropyExampleZeroState_op` / `entropyExamplePlusState_op`).

## Main definitions

* `entropyComparisonState p hp0 hp1` — the state `ρ(p) = p |0⟩⟨0| + (1 − p) |+⟩⟨+|`, as the binary
  mixture `State.mixPair` of the two Bloch pure states.

## Main statements

* `entropyComparisonState_eq_blochState` — **`ρ(p) = blochState ![1 − p, 0, p]`**: the mixture is a
  Bloch state whose Bloch vector `r⃗ = (1 − p, 0, p)` is the convex combination `p (0,0,1) +
  (1 − p) (1,0,0)` of the two constituents' Bloch vectors, via the affine-linearity
  `Concrete.blochMatrix_convex`. This bridge reduces the entropy calculation of
  `AxQM/NC/Ch11/Exercise11_12.lean` to the reusable single-qubit engine
  `blochState_vonNeumannEntropy`.
* `comparison_blochVector_normSq_le_one` — `‖(1 − p, 0, p)‖² ≤ 1`, the ball-membership witness the
  Bloch vector needs (the value `1 − 2p + 2p²`, which is `≤ 1` exactly on `p ∈ [0, 1]`).

The von Neumann entropy value and its comparison to `H(p, 1−p)` are the theorems of
`AxQM/NC/Ch11/Exercise11_12.lean`.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

open Matrix ContinuousLinearMap

/-- **`‖(1 − p, 0, p)‖² ≤ 1` for `p ∈ [0, 1]`.** The squared norm of the Bloch vector of the
Exercise 11.12 state is `(1 − p)² + p² = 1 − 2p + 2p²`, which is `≤ 1` iff `2p(1 − p) ≥ 0`, i.e. on
the unit interval. This is the ball-membership witness passed to `blochState`. -/
theorem comparison_blochVector_normSq_le_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (![1 - p, 0, p] : Fin 3 → ℝ) 0 ^ 2 + (![1 - p, 0, p] : Fin 3 → ℝ) 1 ^ 2
      + (![1 - p, 0, p] : Fin 3 → ℝ) 2 ^ 2 ≤ 1 := by
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  nlinarith [mul_nonneg hp0 (by linarith : (0 : ℝ) ≤ 1 - p)]

/-- **The Nielsen & Chuang Exercise 11.12 state** `ρ(p) = p |0⟩⟨0| + (1 − p) |+⟩⟨+|`: the binary
probabilistic mixture (`State.mixPair`) of the two pure states `|0⟩⟨0| = blochState ![0, 0, 1]` and
`|+⟩⟨+| = blochState ![1, 0, 0]` with weights `p` and `1 − p`. These are exactly the density
matrices `!![1, 0; 0, 0]` (N&C (11.41)) and `½ !![1, 1; 1, 1]` (N&C (11.42)); cf.
`entropyExampleZeroState_op` / `entropyExamplePlusState_op`. -/
def entropyComparisonState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit :=
  State.mixPair hp0 hp1
    (blochState ![0, 0, 1] (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two]))
    (blochState ![1, 0, 0] (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two]))

/-- **`ρ(p) = blochState ![1 − p, 0, p]` (N&C Exercise 11.12).** The mixture
`p |0⟩⟨0| + (1 − p) |+⟩⟨+|` is the Bloch state of the convex combination of the two constituents'
Bloch vectors, `p (0,0,1) + (1 − p) (1,0,0) = (1 − p, 0, p)`. Proved by exposing each summand's
operator (`State.mixPair_op`, `blochState_op`) and recombining through the affine-linearity of the
Bloch matrix (`Concrete.blochMatrix_convex`) and the `ℂ`-linearity of `Matrix.toEuclideanCLM` — the
binary-mixture instance of `blochState_mix`. -/
theorem entropyComparisonState_eq_blochState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entropyComparisonState p hp0 hp1
      = blochState ![1 - p, 0, p] (comparison_blochVector_normSq_le_one p hp0 hp1) := by
  have hvec : (![1 - p, 0, p] : Fin 3 → ℝ) = p • ![0, 0, 1] + (1 - p) • ![1, 0, 0] := by
    funext i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply State.ext
  rw [entropyComparisonState, State.mixPair_op, blochState_op, blochState_op, blochState_op, hvec,
    ← Concrete.blochMatrix_convex ![0, 0, 1] ![1, 0, 0] (by ring : p + (1 - p) = 1),
    map_add, map_smul, map_smul]
  rfl

end AxQM
