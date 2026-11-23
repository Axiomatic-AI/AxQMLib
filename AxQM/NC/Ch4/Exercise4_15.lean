/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationComposition

/-!
# Nielsen & Chuang, Exercise 4.15 (composition of two Bloch-sphere rotations)

Compute composition of two Bloch-sphere rotations; simplify special case.

The statement is a `2 × 2` complex-matrix identity: composing the rotation operators
`R_n̂(β) = exp(−iβ n̂·σ/2)` is the quaternion multiplication law for the half-angle
parametrisation `c I − i (s n̂)·σ`, expressed with the concrete `rotAxis`, `pauliDot`, and
`crossProduct`.

**A sign erratum.** As printed, eq. (4.20)/(4.22) have the cross-product term `− s₁s₂ n̂₂×n̂₁`, but
for the "`n̂₁` then `n̂₂`" order stated in the text (product `R_n̂₂(β₂) R_n̂₁(β₁)`) the correct
term is `+ s₁s₂ n̂₂×n̂₁`. The printed sign is precisely the composition law for the
*reversed* order `R_n̂₁(β₁) R_n̂₂(β₂)`. We formalise the corrected law (a faithful reformulation),
also expose the printed formula as the reversed-order law, and formally refute it for the stated
order, so the discrepancy is documented rather than silently repaired. Equation (4.19) for `c₁₂` is
symmetric in the two rotations and is correct as printed.

## The formalisation

All declarations are in `AxQM.Concrete.RotationComposition`
(`AxQM/Concrete/RotationComposition.lean`):

* `AxQM.Concrete.rotComposeCos` / `rotComposeVec` — the composed half-angle cosine `c₁₂`
  (eq. 4.19) and axis-vector `s₁₂ n̂₁₂` (eq. 4.20, corrected sign).
* `AxQM.Concrete.rotAxis_mul_rotAxis` — **part (1)**: the composition law
  `R_n̂₂(β₂) R_n̂₁(β₁) = c₁₂ I − i (s₁₂ n̂₁₂)·σ`, for arbitrary unit axes and angles.
* `AxQM.Concrete.rotComposeCos_self_axisZ` / `rotComposeVec_self_axisZ` — **part (2)**:
  the `β₁ = β₂`, `n̂₁ = ẑ` simplifications (eq. 4.21 and eq. 4.22, corrected sign).
* `AxQM.Concrete.rotAxis_mul_rotAxis_reversed` — the printed eq. (4.20) formula, proved as
  the composition law for the reversed order `R_n̂₁(β₁) R_n̂₂(β₂)`.
* `AxQM.Concrete.rotAxis_mul_rotAxis_stated_order_printed_false` — a formal refutation of
  the printed eq. (4.20) for the stated order, witnessed by `n̂₁ = ẑ, n̂₂ = x̂, β₁ = β₂ = π`.
-/
