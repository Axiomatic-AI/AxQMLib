/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.AffineBlochSpecification

/-!
# Nielsen & Chuang, Exercise 8.33 (specifying a quantum process needs ≥ 4 Bloch points)

*(N&C p. 394.)*

Prove that specifying a single-qubit operation by Bloch-point transforms needs ≥4 points.

## The answer

A trace-preserving single-qubit operation `E` acts on the Bloch representation `ρ = ½(I + r·σ)` as
an **affine map** `r ↦ M r + c` (N&C §8.3.2, eq. 8.89), with `M` a real `3 × 3` matrix and
`c ∈ ℝ³`: the `9 + 3 = 12` real parameters of Box 8.5. Describing how one Bloch point `r_k`
transforms records the single vector equation `r_k ↦ M r_k + c` — three real scalar constraints on
`(M, c)`. A set of `N` points therefore imposes only `3N` constraints on the `12`-dimensional
parameter, so pinning `(M, c)` down uniquely needs `3N ≥ 12`, i.e. `N ≥ 4`. Three points give only
`9 < 12` constraints and leave the operation underdetermined; four affinely-independent points (the
Bloch-space origin and the three axis endpoints) suffice, so the bound is tight.

## The formalisation

The formal content of Exercise 8.33 is pure linear algebra about affine maps of `ℝ³`
(`Matrix (Fin 3) (Fin 3) ℝ`, `Matrix.mulVec`, `Finset (Fin 3 → ℝ)`). Compare Exercise 8.16.

The formalisation is in `AxQM/Concrete/AffineBlochSpecification.lean`:

* `AxQM.Concrete.SpecifiesAffineBloch` — the property that a finite set of Bloch points
  "completely specifies" the affine Bloch map `r ↦ M r + c` (two affine maps agreeing on the set
  are equal): the formal reading of N&C's "completely specify by point-transforms".
* `AxQM.Concrete.four_le_card_of_specifiesAffineBloch` — **Exercise 8.33 (the answer):**
  any specifying set of Bloch points contains at least four points.
* `AxQM.Concrete.exists_affine_ne_zero_vanishing` — the underdetermination engine: a set
  of `≤ 3` Bloch points admits a nonzero affine map vanishing on all of them (so `≤ 3`
  point-transforms cannot distinguish it from the zero map). Proved by the rank–nullity count
  `3 · s.card ≤ 9 < 12 = finrank of the parameter space`.
* `AxQM.Concrete.specifiesAffineBloch_stdFour` /
  `AxQM.Concrete.exists_specifiesAffineBloch_card_four` — **four is enough (tightness):**
  the four affinely-independent points `0, e₀, e₁, e₂` do specify the affine Bloch map, so `4` is
  the exact minimum.
* `AxQM.Concrete.OnBlochSphere` /
  `AxQM.Concrete.specifiesAffineBloch_sphereFour` /
  `AxQM.Concrete.exists_specifiesAffineBloch_card_four_onSphere` — **four points *on the
  Bloch sphere* are enough:** matching N&C's wording ("points on the Bloch sphere"), the four unit
  vectors `e₀, -e₀, e₁, e₂` (all pure states) already specify the affine Bloch map, so the tight
  bound `4` is realised on the sphere itself, not merely at interior points such as the origin.

See the module docstring of `AxQM/Concrete/AffineBlochSpecification.lean` for the full argument.
-/
