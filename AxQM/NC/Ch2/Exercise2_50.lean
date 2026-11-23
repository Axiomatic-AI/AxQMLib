/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PolarDecompositionExample

/-!
# Nielsen & Chuang, Exercise 2.50 (Left and right polar decompositions of `[[1,0],[1,1]]`)

Find the left and right polar decompositions of [[1,0],[1,1]].

The operand `A` and its (unique) polar factors are all real, so the computation is carried out
over `ℝ`, with "unitary" the membership `U ∈ Matrix.unitaryGroup (Fin 2) ℝ` — the faithful real
specialisation of N&C's complex polar decomposition (Theorem 2.3). N&C names `A = U J` the
*left* and `A = K U` the *right* polar decomposition.

The formalisation is in `AxQM/Concrete/PolarDecompositionExample.lean`:

* `AxQM.Concrete.polarExampleMat` — the matrix `A = [[1,0],[1,1]]`.
* `AxQM.Concrete.polarExampleUnitary` — the shared unitary factor
  `U = (√5)⁻¹ [[2,-1],[1,2]]`, with `polarExampleUnitary_mem_unitaryGroup` its unitarity.
* `AxQM.Concrete.polarExampleLeftFactor` — `J = √(A†A) = (√5)⁻¹ [[3,1],[1,2]]`, shown
  positive definite (`polarExampleLeftFactor_posDef`) and to satisfy `J² = A†A`
  (`polarExampleLeftFactor_mul_self`), hence `J = √(A†A)` (`polarExampleLeftFactor_eq_sqrt`).
* `AxQM.Concrete.polarExampleRightFactor` — `K = √(A A†) = (√5)⁻¹ [[2,1],[1,3]]`, with
  the analogous `polarExampleRightFactor_posDef` / `_mul_self` / `_eq_sqrt`.
* `AxQM.Concrete.polarExampleMat_eq_left_polar` — the left decomposition `A = U J`.
* `AxQM.Concrete.polarExampleMat_eq_right_polar` — the right decomposition `A = K U`.
-/
