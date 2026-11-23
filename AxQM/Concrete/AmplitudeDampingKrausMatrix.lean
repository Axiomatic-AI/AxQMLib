/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlochMatrix

/-!
# Concrete: the amplitude-damping Kraus matrices and their Bloch action

For a damping parameter `γ` it packages the two `2 × 2` complex **operation elements** of the
single-qubit amplitude-damping channel (Nielsen & Chuang eq. 10.46, §8.3.5)

`E₀ = !![1, 0; 0, √(1-γ)]`,   `E₁ = !![0, √γ; 0, 0] = √γ |0⟩⟨1|`

as concrete matrices — bundled as the `Fin 2`-indexed family `amplitudeDampingKrausMatrix` — and
records the two matrix identities that a *grounded* channel needs:

* `amplitudeDampingKrausMatrix_completeness` — the **completeness relation**
  `∑ₖ Eₖ† Eₖ = I` (`0 ≤ γ ≤ 1`), the trace-preservation condition. Diagonal:
  `E₀† E₀ = diag(1, 1-γ)`, `E₁† E₁ = diag(0, γ)`, summing to `I`.
* `amplitudeDampingKrausMatrix_conj_blochMatrix` — the **Bloch action** `∑ₖ Eₖ ρ Eₖ†` on a Bloch
  matrix `ρ = blochMatrix r = ½(I + r·σ)`: it is again a Bloch matrix, with the **affine** Bloch
  transform `r ↦ (√(1-γ) r₀, √(1-γ) r₁, (1-γ) r₂ + γ)` (`ampDampBlochVec`). This is the concrete
  content of the (non-unital!) amplitude-damping channel's action on the Bloch ball: the `x, y`
  components shrink by `√(1-γ)`, the `z` component contracts toward the ground state `z = +1` by
  `(1-γ)· + γ`.

Both are proved by the direct `2 × 2` computation off the explicit entries (`blochMatrix_eq`,
`Matrix.mul_fin_two`), using only `√(1-γ)² = 1-γ` (`0 ≤ 1-γ`) and `√γ² = γ` (`0 ≤ γ`). The
family is lifted in `AxQM/Postulates/API/` through the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM` to the grounded qubit amplitude-damping channel `State qubit → State qubit`.

(Distinct from `Concrete.ampDampKrausZero`/`ampDampKrausOne` of `Concrete.AmplitudeDampingChannel`,
which are the same operators as *abstract* `H →ₗ[ℂ] H` maps on a chosen basis, used for the Ex 8.20
circuit development; here we want the concrete matrix form matching the `blochMatrix` machinery.)
-/

open Matrix

namespace AxQM.Concrete

/-- The **first amplitude-damping Kraus matrix** `E₀ = !![1, 0; 0, √(1-γ)]` (Nielsen & Chuang
eq. 10.46): it leaves the ground state `|0⟩` fixed and damps the amplitude of `|1⟩` by `√(1-γ)`. -/
noncomputable def ampDampKrausMatrixZero (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, (Real.sqrt (1 - γ) : ℂ)]

/-- The **second amplitude-damping Kraus matrix** `E₁ = !![0, √γ; 0, 0] = √γ |0⟩⟨1|` (Nielsen &
Chuang eq. 10.46): the `|1⟩ → |0⟩` decay with amplitude `√γ`. -/
noncomputable def ampDampKrausMatrixOne (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (Real.sqrt γ : ℂ); 0, 0]

/-- The **amplitude-damping Kraus family** `![E₀, E₁]` (Nielsen & Chuang eq. 10.46), the `Fin 2`
bundle of `ampDampKrausMatrixZero`, `ampDampKrausMatrixOne`. -/
noncomputable def amplitudeDampingKrausMatrix (γ : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => ampDampKrausMatrixZero γ
  | 1 => ampDampKrausMatrixOne γ

/-- The **affine Bloch transform** of the amplitude-damping channel:
`r ↦ (√(1-γ) r₀, √(1-γ) r₁, (1-γ) r₂ + γ)`. The transverse components `r₀, r₁` shrink by `√(1-γ)`
and the longitudinal component `r₂` contracts toward the north pole `+1` (the ground state). Unlike
the isotropic depolarizing shrink, the `+γ` offset makes this map *affine, not linear* — the
amplitude-damping channel is not unital. -/
noncomputable def ampDampBlochVec (γ : ℝ) (r : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt (1 - γ) * r 0, Real.sqrt (1 - γ) * r 1, (1 - γ) * r 2 + γ]

/-- The conjugate transpose of `E₀` is `E₀` itself (`E₀` is Hermitian, being real diagonal). -/
theorem ampDampKrausMatrixZero_conjTranspose (γ : ℝ) :
    (ampDampKrausMatrixZero γ)ᴴ = ampDampKrausMatrixZero γ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ampDampKrausMatrixZero, Matrix.conjTranspose_apply]

/-- The conjugate transpose of `E₁ = √γ |0⟩⟨1|` is `√γ |1⟩⟨0| = !![0, 0; √γ, 0]`. -/
theorem ampDampKrausMatrixOne_conjTranspose (γ : ℝ) :
    (ampDampKrausMatrixOne γ)ᴴ = !![0, 0; (Real.sqrt γ : ℂ), 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ampDampKrausMatrixOne, Matrix.conjTranspose_apply]

/-- **The two-term completeness relation** `E₀† E₀ + E₁† E₁ = I` (`0 ≤ γ ≤ 1`). Since
`E₀† E₀ = diag(1, √(1-γ)²) = diag(1, 1-γ)` and `E₁† E₁ = diag(0, √γ²) = diag(0, γ)`, the sum is
`diag(1, (1-γ)+γ) = I`. -/
theorem ampDampKrausMatrix_completeness_two (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (ampDampKrausMatrixZero γ)ᴴ * ampDampKrausMatrixZero γ
        + (ampDampKrausMatrixOne γ)ᴴ * ampDampKrausMatrixOne γ = 1 := by
  have ht : (↑(Real.sqrt (1 - γ)) : ℂ) * ↑(Real.sqrt (1 - γ)) = 1 - (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hu : (↑(Real.sqrt γ) : ℂ) * ↑(Real.sqrt γ) = (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  rw [ampDampKrausMatrixZero_conjTranspose, ampDampKrausMatrixOne_conjTranspose,
    ampDampKrausMatrixZero, ampDampKrausMatrixOne, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    push_cast
  · ring
  · ring
  · ring
  · linear_combination ht + hu

/-- **The two-term Bloch action** `E₀ ρ E₀† + E₁ ρ E₁† = blochMatrix (ampDampBlochVec γ r)` on a
Bloch matrix `ρ = blochMatrix r` (`0 ≤ γ ≤ 1`). Proved by the direct `2 × 2` computation off the
explicit entries, using `√(1-γ)² = 1-γ` and `√γ² = γ`. -/
theorem ampDampKrausMatrix_conj_blochMatrix_two (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (r : Fin 3 → ℝ) :
    ampDampKrausMatrixZero γ * blochMatrix r * (ampDampKrausMatrixZero γ)ᴴ
        + ampDampKrausMatrixOne γ * blochMatrix r * (ampDampKrausMatrixOne γ)ᴴ
      = blochMatrix (ampDampBlochVec γ r) := by
  have ht : (↑(Real.sqrt (1 - γ)) : ℂ) * ↑(Real.sqrt (1 - γ)) = 1 - (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hu : (↑(Real.sqrt γ) : ℂ) * ↑(Real.sqrt γ) = (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  rw [ampDampKrausMatrixZero_conjTranspose, ampDampKrausMatrixOne_conjTranspose,
    ampDampKrausMatrixZero, ampDampKrausMatrixOne, blochMatrix_eq, blochMatrix_eq,
    Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [ampDampBlochVec, Matrix.add_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.tail_cons] <;>
    push_cast
  · linear_combination (1 / 2 - (r 2 : ℂ) / 2) * hu
  · ring
  · ring
  · linear_combination (1 / 2 - (r 2 : ℂ) / 2) * ht

/-- **The completeness relation** `∑ₖ Eₖ† Eₖ = I` for the amplitude-damping Kraus family
(`0 ≤ γ ≤ 1`), certifying trace preservation — the `Fin 2`-sum form of
`ampDampKrausMatrix_completeness_two`. -/
theorem amplitudeDampingKrausMatrix_completeness (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ∑ i, (amplitudeDampingKrausMatrix γ i)ᴴ * amplitudeDampingKrausMatrix γ i = 1 := by
  rw [Fin.sum_univ_two]
  exact ampDampKrausMatrix_completeness_two γ h0 h1

/-- **The Bloch action** `∑ₖ Eₖ (blochMatrix r) Eₖ† = blochMatrix (ampDampBlochVec γ r)` for the
amplitude-damping Kraus family (`0 ≤ γ ≤ 1`) — the `Fin 2`-sum form of
`ampDampKrausMatrix_conj_blochMatrix_two`. -/
theorem amplitudeDampingKrausMatrix_conj_blochMatrix (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (r : Fin 3 → ℝ) :
    ∑ i, amplitudeDampingKrausMatrix γ i * blochMatrix r * (amplitudeDampingKrausMatrix γ i)ᴴ
      = blochMatrix (ampDampBlochVec γ r) := by
  rw [Fin.sum_univ_two]
  exact ampDampKrausMatrix_conj_blochMatrix_two γ h0 h1 r

end AxQM.Concrete
