/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Matrix.SVD
import AxQM.Concrete.BlochAffineDecomposition

/-!
# Concrete: SVD of the real `3 × 3` Bloch matrix into `SO(3)` factors

This file supplies the pure linear-algebra content behind the *singular-value decomposition* step
of the qubit converse of **Nielsen & Chuang, Problem 8.3** (p. 396): every real `3 × 3` matrix `M`
factors as

> `M = O₁ · diagonal d · O₂`,   `O₁, O₂ ∈ SO(3)` proper rotations,   `d : Fin 3 → ℝ` real.

## Context in N&C

A unital single-qubit channel acts on the Bloch ball by the *linear* map `r ↦ M r` with `M` a real
`3 × 3` matrix (the affine translation vanishes because the map is unital; this is
`AxQM.exists_channelBlochMatrix`). Problem 8.3's qubit direction reduces the channel
to the *diagonal* case — the Pauli channel `∑ₖ pₖ σₖ ρ σₖ`, whose Bloch action is the diagonal
contraction `rⱼ ↦ mⱼ rⱼ` (`AxQM.pauliChannel_apply_blochState`) — by writing `M = O₁ D O₂`
with `O₁, O₂` **proper rotations** and `D` diagonal, then realising `O₁, O₂` as unitary conjugations
(the `SU(2) → SO(3)` cover) and `D` as a Pauli channel. This file provides the first ingredient, the
`SO(3)`-factored SVD of `M`.

## The construction

Mathlib's singular-value decomposition `Matrix.exists_unitary_mul_diagonal_mul_unitary`, at the base
field `ℝ`, factors `M = U · diagonal s · V` with `U, V` *orthogonal*
(`Matrix.unitaryGroup (Fin 3) ℝ` **is** `Matrix.orthogonalGroup (Fin 3) ℝ` — the latter is an
`abbrev` for the former, since the star on `ℝ` is trivial) and singular values `s ≥ 0`. The
orthogonal factors may be *improper* (`det = -1`). We correct each to a proper rotation by absorbing
its determinant into a **signature matrix**: with `sU = diagonal ![1, 1, det U]` and
`sV = diagonal ![det V, 1, 1]` (each an involution, `sU² = sV² = 1`, because `det U, det V = ±1`),

> `M = U (sU sU) (diagonal s) (sV sV) V = (U sU) · (sU · diagonal s · sV) · (sV V)`,

where `O₁ = U sU` and `O₂ = sV V` are now proper (`det (U sU) = (det U)² = 1`, likewise `O₂`), and
the middle factor `sU · diagonal s · sV = diagonal ![det V · s₀, s₁, det U · s₂]` is again diagonal
(real, now possibly with one negative entry — the sign forced by orientation, exactly as in the
companion `M = O S` decomposition of Exercises 8.12/8.14).

## Related files

This is pure linear algebra. It uses `det_eq_one_or_neg_one_of_mem_orthogonalGroup` from the
polar-decomposition companion `AxQM/Concrete/BlochAffineDecomposition.lean`. The physical reading —
the Bloch matrix of a *unital channel* factoring this way — is not stated here.
-/

namespace AxQM.Concrete

open Matrix

/-- **Singular-value decomposition into proper rotations.** Every real `3 × 3` matrix `M` factors as
`M = O₁ · diagonal d · O₂` with `O₁, O₂ ∈ SO(3)` proper rotations and `d : Fin 3 → ℝ` a real
diagonal. This is the `SO(3)`-refined form of Mathlib's SVD
(`Matrix.exists_unitary_mul_diagonal_mul_unitary`): the orthogonal SVD factors are normalized to
determinant `1` by absorbing their determinants (`±1`) into signature matrices, at the cost of one
diagonal entry possibly turning negative.

This is the singular-value-decomposition ingredient of the qubit converse of Nielsen & Chuang,
Problem 8.3: it reduces a unital qubit channel's Bloch matrix (`r ↦ M r`,
`AxQM.exists_channelBlochMatrix`) to the diagonal case handled by the Pauli channel, with
the rotations `O₁, O₂` to be realised as unitary conjugations via the `SU(2) → SO(3)` cover. -/
theorem exists_specialOrthogonalGroup_diagonal_factor (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ (O₁ O₂ : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ),
      O₁ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧
      O₂ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧
      M = O₁ * Matrix.diagonal d * O₂ := by
  obtain ⟨U, V, s, hU, hV, -, hM⟩ := Matrix.exists_unitary_mul_diagonal_mul_unitary M
  -- Over `ℝ`, `RCLike.ofReal ∘ s = s`, so the SVD reads `M = U · diagonal s · V`.
  rw [show (RCLike.ofReal ∘ s : Fin 3 → ℝ) = s by rw [RCLike.ofReal_real_eq_id]; rfl] at hM
  -- `Matrix.orthogonalGroup (Fin 3) ℝ` is (an `abbrev` for) `Matrix.unitaryGroup (Fin 3) ℝ`.
  have hUo : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ := hU
  have hVo : V ∈ Matrix.orthogonalGroup (Fin 3) ℝ := hV
  set du := U.det with hdu
  set dv := V.det with hdv
  have hdu2 : du * du = 1 :=
    mul_self_eq_one_iff.mpr (det_eq_one_or_neg_one_of_mem_orthogonalGroup hUo)
  have hdv2 : dv * dv = 1 :=
    mul_self_eq_one_iff.mpr (det_eq_one_or_neg_one_of_mem_orthogonalGroup hVo)
  -- Signature matrices that fix the determinants; each squares to `1` since `det = ±1`.
  set sU : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 1, du] with hsU
  set sV : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![dv, 1, 1] with hsV
  have hdetsU : sU.det = du := by rw [hsU, Matrix.det_diagonal, Fin.prod_univ_three]; simp
  have hdetsV : sV.det = dv := by rw [hsV, Matrix.det_diagonal, Fin.prod_univ_three]; simp
  have hsUsU : sU * sU = 1 := by
    rw [hsU, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; fin_cases i <;> simp [hdu2]
  have hsVsV : sV * sV = 1 := by
    rw [hsV, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; fin_cases i <;> simp [hdv2]
  -- The signature matrices are orthogonal (symmetric involutions over `ℝ`).
  have hsU_unit : sU ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff, show star sU = sU by
      rw [hsU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.diagonal_transpose]]
    exact hsUsU
  have hsV_unit : sV ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff, show star sV = sV by
      rw [hsV, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.diagonal_transpose]]
    exact hsVsV
  refine ⟨U * sU, sV * V, ![dv * s 0, s 1, du * s 2], ?_, ?_, ?_⟩
  · -- `O₁ = U · sU ∈ SO(3)`: orthogonal (product) and `det = (det U)² = 1`.
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    refine ⟨mul_mem hU hsU_unit, ?_⟩
    rw [Matrix.det_mul, hdetsU, ← hdu]
    exact hdu2
  · -- `O₂ = sV · V ∈ SO(3)`: orthogonal (product) and `det = (det V)² = 1`.
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    refine ⟨mul_mem hsV_unit hV, ?_⟩
    rw [Matrix.det_mul, hdetsV, ← hdv]
    exact hdv2
  · -- The middle factor `sU · diagonal s · sV` is the claimed real diagonal, and the signatures
    -- cancel: `M = U (sU sU) (diagonal s) (sV sV) V = O₁ · diagonal d · O₂`.
    have hdiag : Matrix.diagonal ![dv * s 0, s 1, du * s 2] = sU * Matrix.diagonal s * sV := by
      rw [hsU, hsV, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp
      ring
    rw [hdiag, hM,
      show U * sU * (sU * Matrix.diagonal s * sV) * (sV * V)
        = U * (sU * sU) * Matrix.diagonal s * (sV * sV) * V by noncomm_ring,
      hsUsU, hsVsV]
    simp

end AxQM.Concrete
