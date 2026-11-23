/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qudit

/-!
# AxQM.Postulates.API — the equal (uniform) superposition state

The **equal superposition** `|s⟩ = N⁻¹ᐟ² ∑ₖ |k⟩` (`N = d`) of the qudit register `qudit d`, as a
pure state. It is the state obtained by giving every computational-basis vector the same amplitude
`N⁻¹ᐟ²`; for `d = 2ⁿ` it is `|+⟩^{⊗n} = H^{⊗n}|0…0⟩`, the standard starting state of the quantum
algorithms of Nielsen & Chuang, Chapters 5–6 (quantum Fourier transform, Deutsch–Jozsa, Grover, …).

* `uniformSuperposition d` — the pure state with vector `N⁻¹ᐟ² ∑ₖ |k⟩`. Its normalisation is the
  computation `‖N⁻¹ᐟ² ∑ₖ |k⟩‖ = N⁻¹ᐟ² · ‖∑ₖ |k⟩‖ = N⁻¹ᐟ² · √N = 1` (the all-ones vector has norm
  `√N`).
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- The **equal (uniform) superposition** `|s⟩ = N⁻¹ᐟ² ∑ₖ |k⟩` (`N = d`) of the qudit register
`qudit d`, as a pure state: every computational-basis vector `|k⟩ = quditBasis k` gets the same
amplitude `N⁻¹ᐟ²`. It is normalised because `‖N⁻¹ᐟ² ∑ₖ |k⟩‖ = N⁻¹ᐟ² · √N = 1` (the all-ones vector
`∑ₖ |k⟩` has norm `√N`). For `d = 2ⁿ` this is `|+⟩^{⊗n} = H^{⊗n}|0…0⟩`. -/
def uniformSuperposition (d : ℕ) [NeZero d] : PureState (qudit d) where
  vec := (Real.sqrt d : ℂ)⁻¹ • ∑ k : Fin d, (quditBasis k).vec
  normalized := by
    change ‖(Real.sqrt d : ℂ)⁻¹ • ∑ k : Fin d, EuclideanSpace.single k (1 : ℂ)‖ = 1
    have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    rw [norm_smul]
    have h1 : ‖(Real.sqrt d : ℂ)⁻¹‖ = (Real.sqrt d)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hcoord : ∀ x : Fin d, (∑ k : Fin d, EuclideanSpace.single k (1 : ℂ)).ofLp x = 1 := by
      intro x; rw [WithLp.ofLp_sum, Finset.sum_apply]; simp [PiLp.single_apply]
    have h2 : ‖∑ k : Fin d, EuclideanSpace.single k (1 : ℂ)‖ = Real.sqrt d := by
      rw [EuclideanSpace.norm_eq]
      simp only [hcoord, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [h1, h2, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hd)]

/-- The underlying vector of `uniformSuperposition d` is `N⁻¹ᐟ² ∑ₖ |k⟩`. -/
@[simp]
theorem uniformSuperposition_vec (d : ℕ) [NeZero d] :
    (uniformSuperposition d).vec
      = (Real.sqrt d : ℂ)⁻¹ • ∑ k : Fin d, (quditBasis k).vec := rfl

/-- **Amplitude of the uniform superposition on a computational-basis state:** `⟨x, ψ⟩ = N⁻¹ᐟ²`.
Every basis state `|x⟩` has the same amplitude `N⁻¹ᐟ²` in `|ψ⟩ = uniformSuperposition d`, by
orthonormality of the computational basis (`quditBasis_inner`): `⟨x, N⁻¹ᐟ² ∑ₖ |k⟩⟩ = N⁻¹ᐟ² ∑ₖ δₓₖ =
N⁻¹ᐟ²`. -/
theorem uniformSuperposition_inner_quditBasis (d : ℕ) [NeZero d] (x : Fin d) :
    inner ℂ (quditBasis x).vec (uniformSuperposition d).vec = (Real.sqrt d : ℂ)⁻¹ := by
  rw [uniformSuperposition_vec, inner_smul_right, inner_sum,
    Finset.sum_congr rfl (fun y _ => quditBasis_inner x y),
    Finset.sum_ite_eq Finset.univ x (fun _ => (1 : ℂ))]
  simp

end AxQM
