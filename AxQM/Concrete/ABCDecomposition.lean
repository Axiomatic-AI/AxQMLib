/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationDecomposition
import AxQM.Concrete.RotationConjugation

/-!
# Concrete: the ABC decomposition of a single-qubit unitary (Nielsen & Chuang, Corollary 4.2)

Building on the Z–Y decomposition `exists_zy_decomposition` (N&C Theorem 4.1,
`Concrete/RotationDecomposition.lean`) and the `X`-conjugation identities
`pauliX_mul_rotY_mul_pauliX`/`pauliX_mul_rotZ_mul_pauliX` (N&C Exercise 4.7,
`Concrete/RotationConjugation.lean`), it proves the **ABC decomposition** — **Nielsen & Chuang,
Corollary 4.2**: every single-qubit unitary `U` can be written

`U = e^{iα} A X B X C`   with   `A B C = I`,

for unitary `A, B, C` and a global phase `α`. This is the algebraic key to implementing controlled
single-qubit operations (N&C §4.3): a controlled-`U` is realised by the `X`-gates being the
control-conditioned pieces while `A, B, C` are applied unconditionally.

## What is formalised

* `rotY_mul_rotY`, `rotZ_mul_rotZ`, `rotY_zero`, `rotZ_zero` — the coordinate specialisations of
  the one-parameter group law `rotAxis_mul_same`/`rotAxis_zero` (`Concrete/Rotation.lean`), used to
  collapse the products of `R_y`/`R_z` rotations that appear in `A B C` and `A X B X C`.
* `exists_abc_decomposition` — **Corollary 4.2 itself**: for `U ∈ Matrix.unitaryGroup (Fin 2) ℂ`
  there exist a real `α` and matrices `A, B, C ∈ Matrix.unitaryGroup (Fin 2) ℂ` with `A B C = 1`
  and `U = e^{iα} • (A X B X C)`, where `X = pauliX`.

## Design notes

* **Statement shape.** "Unitary" is `Matrix.unitaryGroup (Fin 2) ℂ` (`Uᴴ U = I`), matching
  `exists_zy_decomposition` and N&C's own definition of a single-qubit gate; no dimension or
  determinant is fixed, so the statement is Corollary 4.2 in full generality (all of `U(2)`). The
  three matrices `A, B, C`, their unitarity, the relation `A B C = 1`, and the phase-factored
  identity `U = e^{iα} A X B X C` are all recorded (no weakening): the corollary's content is
  exactly this bundle, so it is one existential theorem rather than a monolithic conjunction bolted
  onto an unrelated headline.
* **The witnesses (N&C's proof, eq. 4.14–4.17).** From `exists_zy_decomposition`,
  `U = e^{iα} R_z(β) R_y(γ) R_z(δ)`. Set (N&C's choice)
  `A = R_z(β) R_y(γ/2)`, `B = R_y(-γ/2) R_z(-(δ+β)/2)`, `C = R_z((δ-β)/2)`.
  - `A B C = I`: the two inner `R_y` collapse (`R_y(γ/2) R_y(-γ/2) = R_y(0) = I`) and the `R_z`
    telescope to `R_z(β) R_z(-β) = R_z(0) = I` (eq. 4.14).
  - `X B X = R_y(γ/2) R_z((δ+β)/2)`: insert `X X = I` between `B`'s two factors and apply the
    `X`-conjugation identities `X R_a(θ) X = R_a(-θ)` (eq. 4.15).
  - hence `A X B X C = R_z(β) R_y(γ) R_z(δ)` (eq. 4.16–4.17), giving `U = e^{iα} A X B X C`.
* **Associativity handling.** Matrix multiplication is non-commutative, so the regroupings (moving
  `X X` together, telescoping the rotations) are pure re-associations discharged by `noncomm_ring`
  (which normalises a non-commutative ring expression without reordering factors); the actual
  cancellations are the rotation group law and `pauliX_mul_self` (`X X = I`).

The statement of Corollary 4.2 in `AxQM/NC/Ch4/Corollary4_2.lean` refers to
`exists_abc_decomposition`.
-/

namespace AxQM.Concrete

open Matrix Complex

/-- The one-parameter group law for `R_y`: `R_y(a) R_y(b) = R_y(a+b)` (the coordinate case of
`rotAxis_mul_same`). -/
theorem rotY_mul_rotY (a b : ℝ) : rotY a * rotY b = rotY (a + b) := rotAxis_mul_same _ a b

/-- The one-parameter group law for `R_z`: `R_z(a) R_z(b) = R_z(a+b)` (the coordinate case of
`rotAxis_mul_same`). -/
theorem rotZ_mul_rotZ (a b : ℝ) : rotZ a * rotZ b = rotZ (a + b) := rotAxis_mul_same _ a b

/-- `R_y(0) = I` (the coordinate case of `rotAxis_zero`). -/
theorem rotY_zero : rotY 0 = 1 := rotAxis_zero _

/-- `R_z(0) = I` (the coordinate case of `rotAxis_zero`). -/
theorem rotZ_zero : rotZ 0 = 1 := rotAxis_zero _

/-- **Nielsen & Chuang, Corollary 4.2 (ABC decomposition of a single-qubit unitary).** Every
`2 × 2` unitary `U` (a single-qubit gate, `Uᴴ U = I`) can be written `U = e^{iα} A X B X C` with
`A B C = I`, for a real phase `α`, unitary matrices `A, B, C`, and `X = pauliX`. The witnesses come
from the Z–Y decomposition `U = e^{iα} R_z(β) R_y(γ) R_z(δ)` (Theorem 4.1) via N&C's choice
`A = R_z(β) R_y(γ/2)`, `B = R_y(-γ/2) R_z(-(δ+β)/2)`, `C = R_z((δ-β)/2)` (eq. 4.14–4.17): `A B C`
telescopes to `I`, and conjugating `B` by the two `X` gates (`X R_a(θ) X = R_a(-θ)`, Exercise 4.7)
turns `A X B X C` back into `R_z(β) R_y(γ) R_z(δ)`. -/
theorem exists_abc_decomposition (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (α : ℝ) (A B C : Matrix (Fin 2) (Fin 2) ℂ),
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        C ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ A * B * C = 1 ∧
        U = Complex.exp ((α : ℂ) * Complex.I) • (A * pauliX * B * pauliX * C) := by
  obtain ⟨α, β, γ, δ, hU_eq⟩ := exists_zy_decomposition U hU
  refine ⟨α, rotZ β * rotY (γ / 2), rotY (-(γ / 2)) * rotZ (-((δ + β) / 2)),
    rotZ ((δ - β) / 2), mul_mem (rotZ_mem_unitaryGroup β) (rotY_mem_unitaryGroup (γ / 2)),
    mul_mem (rotY_mem_unitaryGroup (-(γ / 2))) (rotZ_mem_unitaryGroup (-((δ + β) / 2))),
    rotZ_mem_unitaryGroup ((δ - β) / 2), ?_, ?_⟩
  · -- `A B C = 1` (N&C eq. 4.14): the inner `R_y` collapse and the `R_z` telescope.
    calc rotZ β * rotY (γ / 2) * (rotY (-(γ / 2)) * rotZ (-((δ + β) / 2))) * rotZ ((δ - β) / 2)
        = rotZ β * (rotY (γ / 2) * rotY (-(γ / 2)))
            * (rotZ (-((δ + β) / 2)) * rotZ ((δ - β) / 2)) := by noncomm_ring
      _ = 1 := by
        rw [rotY_mul_rotY, rotZ_mul_rotZ, show γ / 2 + -(γ / 2) = 0 by ring,
          show -((δ + β) / 2) + (δ - β) / 2 = -β by ring, rotY_zero, mul_one, rotZ_mul_rotZ,
          show β + -β = 0 by ring, rotZ_zero]
  · -- `U = e^{iα} • (A X B X C)` (N&C eq. 4.15–4.17).
    -- Conjugate `B` by the two `X` gates: `X B X = R_y(γ/2) R_z((δ+β)/2)`.
    have hXBX : pauliX * (rotY (-(γ / 2)) * rotZ (-((δ + β) / 2))) * pauliX
        = rotY (γ / 2) * rotZ ((δ + β) / 2) := by
      calc pauliX * (rotY (-(γ / 2)) * rotZ (-((δ + β) / 2))) * pauliX
          = pauliX * rotY (-(γ / 2)) * (pauliX * pauliX)
              * rotZ (-((δ + β) / 2)) * pauliX := by rw [pauliX_mul_self]; noncomm_ring
        _ = (pauliX * rotY (-(γ / 2)) * pauliX)
              * (pauliX * rotZ (-((δ + β) / 2)) * pauliX) := by noncomm_ring
        _ = rotY (γ / 2) * rotZ ((δ + β) / 2) := by
            rw [pauliX_mul_rotY_mul_pauliX, pauliX_mul_rotZ_mul_pauliX, neg_neg, neg_neg]
    -- Reassemble `A X B X C` into `R_z(β) R_y(γ) R_z(δ)`.
    have hprod : rotZ β * rotY (γ / 2) * pauliX * (rotY (-(γ / 2)) * rotZ (-((δ + β) / 2)))
        * pauliX * rotZ ((δ - β) / 2) = rotZ β * rotY γ * rotZ δ := by
      calc rotZ β * rotY (γ / 2) * pauliX * (rotY (-(γ / 2)) * rotZ (-((δ + β) / 2)))
              * pauliX * rotZ ((δ - β) / 2)
          = rotZ β * rotY (γ / 2)
              * (pauliX * (rotY (-(γ / 2)) * rotZ (-((δ + β) / 2))) * pauliX)
              * rotZ ((δ - β) / 2) := by noncomm_ring
        _ = rotZ β * rotY (γ / 2) * (rotY (γ / 2) * rotZ ((δ + β) / 2))
              * rotZ ((δ - β) / 2) := by rw [hXBX]
        _ = rotZ β * (rotY (γ / 2) * rotY (γ / 2))
              * (rotZ ((δ + β) / 2) * rotZ ((δ - β) / 2)) := by noncomm_ring
        _ = rotZ β * rotY γ * rotZ δ := by
            rw [rotY_mul_rotY, rotZ_mul_rotZ, show γ / 2 + γ / 2 = γ by ring,
              show (δ + β) / 2 + (δ - β) / 2 = δ by ring]
    rw [hU_eq, hprod]

end AxQM.Concrete
