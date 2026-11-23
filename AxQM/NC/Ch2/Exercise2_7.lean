/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.OrthogonalPairExample

/-!
# Nielsen & Chuang, Exercise 2.7 (Orthogonality and normalized forms in `ℂ²`)

Verify (1,1) and (1,-1) are orthogonal; find normalized forms.

Orthogonality is defined (p. 66) as the inner product being zero; the norm is
`‖v⟩‖ ≡ √⟨v|v⟩` (2.16); and the *normalized form* of a nonzero `|v⟩` is
`|v⟩/‖v⟩‖`.

The formalisation is in `AxQM/Concrete/OrthogonalPairExample.lean`,
where `ℂ²` is modelled by `EuclideanSpace ℂ (Fin 2)` with its canonical inner
product (N&C's `(2.14)`) and induced norm:

* `AxQM.Concrete.vecOneOneC2`, `AxQM.Concrete.vecOneNegOneC2` —
  the vectors `(1, 1)` and `(1, -1)`.
* `AxQM.Concrete.inner_vecOneOneC2_vecOneNegOneC2_eq_zero` — **part 1**:
  the two vectors are orthogonal, `⟨(1,1), (1,-1)⟩ = 0`.
* `AxQM.Concrete.norm_vecOneOneC2`,
  `AxQM.Concrete.norm_vecOneNegOneC2` — each has norm `√2` (the divisor
  used to normalize).
* `AxQM.Concrete.unitVecOneOneC2`,
  `AxQM.Concrete.unitVecOneNegOneC2` — **part 2**: the normalized forms
  `(1/√2, 1/√2)` and `(1/√2, -1/√2)`, together with
  `..._eq_norm_inv_smul` (they equal `‖·‖⁻¹ • ·`, i.e. each vector divided by its
  norm) and `norm_unitVecOneOneC2` / `norm_unitVecOneNegOneC2` (they are unit
  vectors, confirming the normalization).
-/
