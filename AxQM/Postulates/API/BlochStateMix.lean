/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BlochState
import AxQM.Postulates.API.Mixture
import AxQM.Concrete.BlochTraceDistance

/-!
# AxQM.Postulates.API — mixtures of Bloch states

The **two-point Bloch mixture** identity: a convex combination of two qubit Bloch states is the
Bloch state of the convex combination of their Bloch vectors,
`p·blochState a + q·blochState b = blochState (p a + q b)` (for `p + q = 1`). This is the
state-level lift of the matrix affine-linearity `Concrete.blochMatrix_convex`, obtained by
transporting it across `State.mix_op` / `blochState_op` and the `Matrix.toEuclideanCLM` bridge.

`blochState_mix` is the natural shared tool for the Bloch-picture Chapter 9 items (trace
distance, and the depolarizing / bit-flip channel distances of Exercises 9.12–9.13).
-/

open Matrix ContinuousLinearMap

noncomputable section

namespace AxQM

/-- **A two-point mixture of Bloch states is the Bloch state of the averaged Bloch vector.** For
Bloch vectors `a, b` in the closed unit ball and weights `p, q ≥ 0` with `p + q = 1`,
`State.mix ![p, q] _ _ ![blochState a ha, blochState b hb] = blochState (p a + q b) _`. The
state-level form of `Concrete.blochMatrix_convex`: apply `State.mix_op`, expose each summand's
operator via `blochState_op`, then recombine through `blochMatrix_convex` and the `ℂ`-linearity of
`Matrix.toEuclideanCLM`. -/
theorem blochState_mix (a b : Fin 3 → ℝ)
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 ≤ 1) (hb : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 ≤ 1)
    {p q : ℝ} (hp : ∀ i, 0 ≤ ![p, q] i) (hs : ∑ i, ![p, q] i = 1)
    (hab : (p • a + q • b) 0 ^ 2 + (p • a + q • b) 1 ^ 2 + (p • a + q • b) 2 ^ 2 ≤ 1) :
    State.mix ![p, q] hp hs ![blochState a ha, blochState b hb]
      = blochState (p • a + q • b) hab := by
  apply State.ext
  rw [State.mix_op, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, blochState_op]
  rw [← Concrete.blochMatrix_convex a b (by simpa [Fin.sum_univ_two] using hs),
    map_add, map_smul, map_smul]
  rfl

end AxQM
