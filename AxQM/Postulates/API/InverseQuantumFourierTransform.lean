/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumFourierTransform
import AxQM.Postulates.API.Evolution

/-!
# AxQM.Postulates.API — the inverse quantum Fourier transform as a unitary evolution

The inverse transform for Nielsen & Chuang **Exercise 5.5** ("give a quantum circuit to
perform the inverse quantum Fourier transform"). The quantum Fourier transform `F` is realized as a
unitary `Evolution` (`qftEvolution d`, built for Problem 5.1); its inverse `F⁻¹` is a unitary
transformation too, so it is itself an implementable circuit — the *adjoint* (inverse) gate `F†`.
This file packages `F⁻¹` and computes its action, mirroring the QFT development.

## What is formalised

* `qftInverseEvolution d` — the **inverse QFT as a unitary `Evolution (qudit d)`**, defined as the
  adjoint `(qftEvolution d).adjoint = F†`. Because `Evolution.adjoint` is again a unitary
  `Evolution`, the very existence of this term is the exercise's answer: the inverse transform *is*
  a legitimate quantum circuit, the adjoint of the QFT circuit (which, gate for gate, is the QFT
  circuit run in reverse with each gate daggered — the general reversal principle
  `Evolution.adjoint_comp`).
* `qftInverseEvolution_op_eq` — its operator is `toEuclideanCLM` of the **conjugate-transpose** QFT
  matrix, `F† = toEuclideanCLM (qftMatrix d)ᴴ`, since `Matrix.toEuclideanCLM` is a star-algebra
  equivalence (adjoint of operator ↔ conjugate transpose of matrix).
* `qftInverseEvolution_op_apply_quditBasis` — the **inverse-transform action**
  `F⁻¹|k⟩ = ∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩`: the inverse discrete Fourier transform, the conjugate of
  the forward action `qftEvolution_op_apply_quditBasis`.
* `qftInverseFourierImage d k` — that image state `∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩` as a `PureState`
  (normalized, being the image of a unit vector under the unitary `F†`).
* `qftInverseEvolution_adjoint` — inverting the inverse-QFT circuit recovers the QFT,
  `(qftInverseEvolution d)† = qftEvolution d` (from the adjoint involution).

The pure-state action, the two-sided inversion `F⁻¹ ∘ F = F ∘ F⁻¹ = id`, and the operational
round-trip `F⁻¹(F|ψ⟩) = |ψ⟩` are the statements of Nielsen & Chuang Exercise 5.5 in
`AxQM/NC/Ch5/Exercise5_5.lean`.

## Design notes

* **Adjoint = conjugate transpose.** `Matrix.toEuclideanCLM` is a `StarAlgEquiv`, hence
  star-preserving; the operator adjoint (`star`) of `toEuclideanCLM (qftMatrix d)` is therefore
  `toEuclideanCLM` of the matrix `star`, i.e. the conjugate transpose `(qftMatrix d)ᴴ`. No
  entrywise re-derivation of the inverse matrix is needed. The action is then the `j`-th column of
  `(qftMatrix d)ᴴ` (`Matrix.toEuclideanCLM_apply_single`), whose entry
  `((qftMatrix d)ᴴ)ⱼₖ = conj((qftMatrix d)ₖⱼ) = (1/√d)·e^{−2πijk/d}` is the forward entry
  conjugated.
* **General `d`.** As with the forward transform, everything holds for every dimension `d ≥ 1`.
-/

noncomputable section

namespace AxQM

open AxQM.Concrete
open scoped Matrix

/-- The **inverse quantum Fourier transform on `qudit d`** as a unitary `Evolution`
(Nielsen & Chuang Exercise 5.5), defined as the adjoint (inverse) gate of the QFT evolution:
`F⁻¹ = F† = (qftEvolution d).adjoint`. Since a unitary's adjoint is again unitary, this is a genuine
`Evolution` — an implementable quantum circuit — realizing the inverse transform. At the gate level
it is the QFT circuit run in reverse with each gate daggered (`Evolution.adjoint_comp`). -/
def qftInverseEvolution (d : ℕ) [NeZero d] : Evolution (qudit d) := (qftEvolution d).adjoint

/-- The underlying operator of `qftInverseEvolution d` is the Hilbert-space adjoint of the QFT
operator, `F† = adjoint (toEuclideanCLM (qftMatrix d))`. -/
@[simp]
theorem qftInverseEvolution_op (d : ℕ) [NeZero d] :
    (qftInverseEvolution d).op
      = ContinuousLinearMap.adjoint
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (qftMatrix d)) := rfl

/-- The inverse QFT operator is `toEuclideanCLM` of the **conjugate-transpose** QFT matrix,
`F† = toEuclideanCLM (qftMatrix d)ᴴ`. Because `Matrix.toEuclideanCLM` is a star-algebra equivalence
(`star` on operators is the adjoint, `star` on matrices is the conjugate transpose), the adjoint of
`toEuclideanCLM (qftMatrix d)` is `toEuclideanCLM` of `star (qftMatrix d) = (qftMatrix d)ᴴ`. -/
theorem qftInverseEvolution_op_eq (d : ℕ) [NeZero d] :
    (qftInverseEvolution d).op
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (qftMatrix d)ᴴ := by
  rw [qftInverseEvolution_op, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    Matrix.star_eq_conjTranspose]

/-- **Action of the inverse QFT on a computational-basis state, compact form:**
`F⁻¹|k⟩ = ∑ⱼ (Fᴴ)ⱼₖ |j⟩`, the `k`-th column of the conjugate-transpose matrix `(qftMatrix d)ᴴ`.
The `(quditBasis _).vec`-phrased instance of `Matrix.toEuclideanCLM_apply_single` at the matrix
`(qftMatrix d)ᴴ` (whose associated operator is `F†` by `qftInverseEvolution_op_eq`). -/
theorem qftInverseEvolution_op_apply_quditBasis_matrix (d : ℕ) [NeZero d] (k : Fin d) :
    (qftInverseEvolution d).op (quditBasis k).vec
      = ∑ j : Fin d, ((qftMatrix d)ᴴ j k) • (quditBasis j).vec := by
  rw [qftInverseEvolution_op_eq]
  exact Matrix.toEuclideanCLM_apply_single (qftMatrix d)ᴴ k

/-- **Action of the inverse QFT on a computational-basis state** (Nielsen & Chuang Exercise 5.5, the
inverse of eq. 5.2): `F⁻¹|k⟩ = ∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩`. Each amplitude is the forward QFT
amplitude conjugated, `((qftMatrix d)ᴴ)ⱼₖ = (1/√d)·e^{−2πijk/d}`
(`Concrete.qftMatrix_conjTranspose_apply`). This makes the proof the exact mirror of the forward
`qftEvolution_op_apply_quditBasis`: rewrite the compact column form, then the `Concrete` entry. -/
theorem qftInverseEvolution_op_apply_quditBasis (d : ℕ) [NeZero d] (k : Fin d) :
    (qftInverseEvolution d).op (quditBasis k).vec
      = ∑ j : Fin d, ((Real.sqrt d : ℂ)⁻¹
          * Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d)))
          • (quditBasis j).vec := by
  rw [qftInverseEvolution_op_apply_quditBasis_matrix]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [qftMatrix_conjTranspose_apply]

/-- The **inverse quantum Fourier image state** `F⁻¹|k⟩ = ∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩` of the
computational-basis state `|k⟩`, as a `PureState` of `qudit d` (Nielsen & Chuang Exercise 5.5). It
is normalized because it is the image `(qftInverseEvolution d).op |k⟩` of a unit vector under the
unitary `F†` (`Evolution.norm_op_apply`, `quditBasis` normalized). -/
def qftInverseFourierImage (d : ℕ) [NeZero d] (k : Fin d) : PureState (qudit d) where
  vec := ∑ j : Fin d, ((Real.sqrt d : ℂ)⁻¹
      * Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d))) • (quditBasis j).vec
  normalized := by
    rw [← qftInverseEvolution_op_apply_quditBasis d k, (qftInverseEvolution d).norm_op_apply]
    exact (quditBasis k).normalized

/-- The underlying vector of `qftInverseFourierImage d k` is the explicit inverse-Fourier
superposition `∑ⱼ (1/√d)·e^{−2πijk/d} |j⟩`. -/
@[simp]
theorem qftInverseFourierImage_vec (d : ℕ) [NeZero d] (k : Fin d) :
    (qftInverseFourierImage d k).vec
      = ∑ j : Fin d, ((Real.sqrt d : ℂ)⁻¹
          * Complex.exp (-(2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d)))
          • (quditBasis j).vec :=
  rfl

/-- **The QFT is recovered by inverting the inverse-QFT circuit:**
`(qftInverseEvolution d)† = qftEvolution d`. Since `qftInverseEvolution d = F†` and the adjoint is
an involution (`Evolution.adjoint_adjoint`), `F†† = F`. The two circuits are mutual inverses. -/
theorem qftInverseEvolution_adjoint (d : ℕ) [NeZero d] :
    (qftInverseEvolution d).adjoint = qftEvolution d :=
  Evolution.adjoint_adjoint (qftEvolution d)

end AxQM
