/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PolarNormal

/-!
# The dephasing twirl: sign conjugation projects an operator onto its diagonal

Fix an orthonormal basis `b = {bᵢ}` of a finite-dimensional inner product space `E`. For a sign
pattern `ε : ι → Bool` the **sign-diagonal unitary** is the diagonal operator

`signDiagonal ε = ∑ᵢ (-1)^{ε i} • |bᵢ⟩⟨bᵢ|`,

a self-adjoint unitary (each diagonal entry is `±1`). Conjugating an arbitrary operator `A` by all
`2^{|ι|}` sign-diagonal unitaries and summing **projects `A` onto its basis-diagonal**:

`∑_{ε : ι → Bool} (signDiagonal ε) A (signDiagonal ε)† = 2^{|ι|} • ∑ᵢ ⟨bᵢ, A bᵢ⟩ • |bᵢ⟩⟨bᵢ|`.

Equivalently, the **completely dephasing channel** (the uniform average of the sign conjugations)
equals the diagonal projection `A ↦ ∑ᵢ ⟨bᵢ, A bᵢ⟩ • |bᵢ⟩⟨bᵢ|`. Entrywise this is the elementary
character identity `∑_{ε} (-1)^{ε p}(-1)^{ε q} = 2^{|ι|} · [p = q]`: summing the sign phases kills
every off-diagonal entry `⟨b_p, A b_q⟩` (`p ≠ q`) and leaves the diagonal untouched.

This is the **first stage** of the mixed-unitary (twirl) realisation of the completely depolarizing
channel `A ↦ tr(A)·I/d` (Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.19). The dephasing average makes `A` diagonal; a subsequent average over the basis
permutations equalises the diagonal to `tr(A)/d`. Because both averages are convex combinations of
unitary conjugations, the depolarizing channel is a mixed-unitary channel, and monotonicity of the
quantum relative entropy under such channels
(`ContinuousLinearMap.quantumRelativeEntropy_sum_conjStarAlgEquiv_le`) then yields its monotonicity
under the partial trace — the bridge to the strong subadditivity of the von Neumann entropy (N&C
Theorem 11.14).

## Main definitions

* `OrthonormalBasis.signDiagonal` — the sign-diagonal unitary `∑ᵢ (-1)^{ε i} • |bᵢ⟩⟨bᵢ|`.

## Main results

* `OrthonormalBasis.diagonalOperator_apply_self`, `OrthonormalBasis.inner_diagonalOperator`,
  `OrthonormalBasis.ext_inner_basis` — reusable basis-computation helpers for `diagonalOperator`.
* `OrthonormalBasis.signDiagonal_mem_unitary`, `OrthonormalBasis.signDiagonal_adjoint` — the
  sign-diagonal operator is a self-adjoint unitary.
* `OrthonormalBasis.sum_signDiagonal_conj_self` / `OrthonormalBasis.sum_signDiagonal_conj` — the
  dephasing-twirl identity `∑_ε (signDiagonal ε) A (signDiagonal ε)(†) = 2^{|ι|} • (diagonal of A)`.
* `OrthonormalBasis.dephasing_average` — the average form: the completely dephasing channel is the
  diagonal projection.
-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : OrthonormalBasis ι 𝕜 E)

/-- **Action of a diagonal operator on a basis vector**: `(∑ᵢ wᵢ |bᵢ⟩⟨bᵢ|)(b q) = w q • b q`. -/
theorem diagonalOperator_apply_self (w : ι → 𝕜) (q : ι) :
    b.diagonalOperator w (b q) = w q • b q := by
  rw [diagonalOperator, _root_.sum_apply, Finset.sum_eq_single q]
  · rw [_root_.smul_apply, rankOne_apply, b.inner_eq_one, one_smul]
  · intro i _ hi
    rw [_root_.smul_apply, rankOne_apply, b.inner_eq_zero hi, zero_smul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ q) h

/-- **Inner product of a basis vector with a diagonal operator applied to any vector**:
`⟨b p, (∑ᵢ wᵢ |bᵢ⟩⟨bᵢ|) v⟩ = w p · ⟨b p, v⟩`. -/
theorem inner_diagonalOperator (w : ι → 𝕜) (p : ι) (v : E) :
    inner 𝕜 (b p) (b.diagonalOperator w v) = w p * inner 𝕜 (b p) v := by
  rw [diagonalOperator, _root_.sum_apply, inner_sum, Finset.sum_eq_single p]
  · rw [_root_.smul_apply, rankOne_apply, inner_smul_right, inner_smul_right,
      b.inner_eq_one, mul_one]
  · intro i _ hi
    rw [_root_.smul_apply, rankOne_apply, inner_smul_right, inner_smul_right,
      b.inner_eq_zero (Ne.symm hi), mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- **Extensionality via basis matrix entries**: two operators agreeing on every entry
`⟨b p, · (b q)⟩` are equal. -/
theorem ext_inner_basis {S T : E →L[𝕜] E}
    (h : ∀ p q, inner 𝕜 (b p) (S (b q)) = inner 𝕜 (b p) (T (b q))) : S = T := by
  refine ContinuousLinearMap.coe_injective (b.toBasis.ext fun q => ?_)
  have hq : S (b q) = T (b q) := by
    rw [← b.sum_repr' (S (b q)), ← b.sum_repr' (T (b q))]
    simp_rw [h]
  simpa using hq

/-- The **sign-diagonal unitary** for a sign pattern `ε`: `∑ᵢ (-1)^{ε i} • |bᵢ⟩⟨bᵢ|`, the diagonal
operator with `±1` diagonal entries. It is a self-adjoint unitary (`signDiagonal_mem_unitary`,
`signDiagonal_adjoint`), and averaging over all sign patterns dephases (`sum_signDiagonal_conj`). -/
noncomputable def signDiagonal (ε : ι → Bool) : E →L[𝕜] E :=
  b.diagonalOperator (fun i => if ε i then (-1 : 𝕜) else 1)

/-- The sign-diagonal operator acts on `b q` by the scalar `(-1)^{ε q}`. -/
theorem signDiagonal_apply_self (ε : ι → Bool) (q : ι) :
    b.signDiagonal ε (b q) = (if ε q then (-1 : 𝕜) else 1) • b q := by
  simp only [signDiagonal, diagonalOperator_apply_self]

/-- Inner product of a basis vector with the sign-diagonal operator applied to any vector. -/
theorem inner_signDiagonal (ε : ι → Bool) (p : ι) (v : E) :
    inner 𝕜 (b p) (b.signDiagonal ε v) = (if ε p then (-1 : 𝕜) else 1) * inner 𝕜 (b p) v := by
  simp only [signDiagonal, inner_diagonalOperator]

section CompleteSpace

variable [CompleteSpace E]

/-- The sign-diagonal operator is **self-adjoint** (its `±1` diagonal is real). -/
theorem signDiagonal_adjoint (ε : ι → Bool) :
    adjoint (b.signDiagonal ε) = b.signDiagonal ε := by
  simp only [signDiagonal, diagonalOperator_adjoint]
  congr 1
  funext i
  simp only [Pi.star_apply]
  cases ε i <;> simp

/-- The sign-diagonal operator is **unitary** (its diagonal entries have modulus `1`). -/
theorem signDiagonal_mem_unitary (ε : ι → Bool) :
    b.signDiagonal ε ∈ unitary (E →L[𝕜] E) := by
  refine b.diagonalOperator_mem_unitary _ fun i => ?_
  cases ε i <;> simp

end CompleteSpace

section DecidableEq

variable [DecidableEq ι]

/-- **The sign character identity**: `∑_{ε : ι → Bool} (-1)^{ε p} (-1)^{ε q} = 2^{|ι|} · [p = q]`.
For `p = q` every term is `1`; for `p ≠ q` flipping the `p`-th sign is a fixed-point-free involution
negating each term, so the sum vanishes. -/
private theorem sum_sign_mul_sign (p q : ι) :
    ∑ ε : ι → Bool, (if ε p then (-1 : 𝕜) else 1) * (if ε q then (-1 : 𝕜) else 1)
      = if p = q then (2 : 𝕜) ^ Fintype.card ι else 0 := by
  by_cases hpq : p = q
  · subst hpq
    have h1 : ∀ ε : ι → Bool,
        (if ε p then (-1 : 𝕜) else 1) * (if ε p then (-1 : 𝕜) else 1) = 1 := fun ε => by
      cases ε p <;> simp
    rw [Finset.sum_congr rfl fun ε _ => h1 ε, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, ite_eq_left rfl, nsmul_eq_mul, mul_one]
    push_cast
    ring
  · rw [ite_eq_right hpq]
    set g : (ι → Bool) → 𝕜 :=
      fun ε => (if ε p then (-1 : 𝕜) else 1) * (if ε q then (-1 : 𝕜) else 1) with hg
    set f : (ι → Bool) → ι → Bool := fun ε => Function.update ε p (! ε p) with hf
    have hf_inv : Function.Involutive f := by
      intro ε
      funext j
      by_cases hj : j = p
      · subst hj; simp [hf]
      · simp [hf, Function.update_of_ne hj]
    have hswap : ∀ ε, g (f ε) = -(g ε) := by
      intro ε
      have hp : f ε p = ! ε p := by simp [hf]
      have hq : f ε q = ε q := by simp [hf, Function.update_of_ne (Ne.symm hpq)]
      simp only [hg, hp, hq]
      cases ε p <;> cases ε q <;> simp
    have key : (∑ ε : ι → Bool, g ε) = -∑ ε : ι → Bool, g ε :=
      calc (∑ ε, g ε) = ∑ ε, g (f ε) := (Equiv.sum_comp hf_inv.toPerm g).symm
        _ = ∑ ε, -(g ε) := Finset.sum_congr rfl fun ε _ => hswap ε
        _ = -∑ ε, g ε := by rw [Finset.sum_neg_distrib]
    exact self_eq_neg.mp key

/-- **The dephasing twirl projects onto the diagonal (self-adjoint form)**: summing the sign
conjugations `(signDiagonal ε) A (signDiagonal ε)` over all `2^{|ι|}` sign patterns gives
`2^{|ι|}` times the diagonal part `∑ᵢ ⟨bᵢ, A bᵢ⟩ • |bᵢ⟩⟨bᵢ|` of `A`. -/
theorem sum_signDiagonal_conj_self (A : E →L[𝕜] E) :
    ∑ ε : ι → Bool, b.signDiagonal ε ∘L A ∘L b.signDiagonal ε
      = (2 : 𝕜) ^ Fintype.card ι • b.diagonalOperator (fun i => inner 𝕜 (b i) (A (b i))) := by
  refine b.ext_inner_basis fun p q => ?_
  rw [_root_.sum_apply, inner_sum]
  have hterm : ∀ ε : ι → Bool,
      inner 𝕜 (b p) ((b.signDiagonal ε ∘L A ∘L b.signDiagonal ε) (b q))
        = (if ε p then (-1 : 𝕜) else 1) * (if ε q then (-1 : 𝕜) else 1)
            * inner 𝕜 (b p) (A (b q)) := by
    intro ε
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, b.inner_signDiagonal,
      b.signDiagonal_apply_self, map_smul, inner_smul_right]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, sum_sign_mul_sign p q, _root_.smul_apply, inner_smul_right,
    b.inner_diagonalOperator, b.inner_eq_ite]
  by_cases hpq : p = q
  · subst hpq; simp
  · simp [hpq]

end DecidableEq

section Twirl

variable [DecidableEq ι] [CompleteSpace E]

/-- **The dephasing twirl projects onto the diagonal**: summing the unitary conjugations
`(signDiagonal ε) A (signDiagonal ε)†` over all `2^{|ι|}` sign patterns gives `2^{|ι|}` times the
diagonal part `∑ᵢ ⟨bᵢ, A bᵢ⟩ • |bᵢ⟩⟨bᵢ|` of `A`. The genuine mixed-unitary (twirl) form, obtained
from `sum_signDiagonal_conj_self` and self-adjointness of the sign-diagonal unitary. -/
theorem sum_signDiagonal_conj (A : E →L[𝕜] E) :
    ∑ ε : ι → Bool, b.signDiagonal ε ∘L A ∘L adjoint (b.signDiagonal ε)
      = (2 : 𝕜) ^ Fintype.card ι • b.diagonalOperator (fun i => inner 𝕜 (b i) (A (b i))) := by
  simp_rw [b.signDiagonal_adjoint]
  exact b.sum_signDiagonal_conj_self A

/-- **The completely dephasing channel is the diagonal projection.** The uniform average of the
`2^{|ι|}` sign conjugations of `A` equals its basis-diagonal `∑ᵢ ⟨bᵢ, A bᵢ⟩ • |bᵢ⟩⟨bᵢ|`. -/
theorem dephasing_average (A : E →L[𝕜] E) :
    ((2 : 𝕜) ^ Fintype.card ι)⁻¹ •
        ∑ ε : ι → Bool, b.signDiagonal ε ∘L A ∘L adjoint (b.signDiagonal ε)
      = b.diagonalOperator (fun i => inner 𝕜 (b i) (A (b i))) := by
  rw [b.sum_signDiagonal_conj, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : 𝕜) ≠ 0)), one_smul]

end Twirl

end OrthonormalBasis
