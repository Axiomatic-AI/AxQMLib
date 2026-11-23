/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl
public import ToMathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Data.Fintype.Perm

/-!
# The depolarizing twirl: a finite unitary `1`-design

Fix an orthonormal basis `b = {bᵢ}` of a finite-dimensional inner product space `E` of dimension
`d = |ι|`. Averaging an operator `A` over the unitary conjugations by the `2^d · d!` composites
`Pσ ∘ Sε` — where `Sε` is a **sign-diagonal** unitary (`ε : ι → Bool`) and `Pσ` is a **basis
permutation** unitary (`σ : Equiv.Perm ι`) — reproduces the **completely depolarizing channel**

`(2^d · d!)⁻¹ · ∑_{ε, σ} (Pσ Sε) A (Pσ Sε)† = (tr A / d) · I`.

This is the operator content of Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.19: there is a finite family of unitaries `Uⱼ` and a probability distribution `pⱼ`
(here uniform, `pⱼ = (2^d d!)⁻¹`) with `∑ⱼ pⱼ Uⱼ A Uⱼ† = tr(A)·I/d`, i.e. the collection
`{Uⱼ}` is a unitary `1`-design.

The proof composes two averages. The sign average
(`OrthonormalBasis.sum_signDiagonal_conj`, the *dephasing twirl*) projects `A` onto its
basis-diagonal `∑ᵢ ⟨bᵢ, A bᵢ⟩ • |bᵢ⟩⟨bᵢ|`; the permutation average then equalises that diagonal to
its mean `(tr A / d)` on the identity, because conjugating a diagonal operator by a basis
permutation permutes its diagonal entries and averaging a permuted family over the whole symmetric
group is coordinate-independent. Everything is phrased with linear isometry equivalences
(`E ≃ₗᵢ[𝕜] E`) and their conjugation `LinearIsometryEquiv.conjStarAlgEquiv`, so the result feeds
directly into the mixed-unitary monotonicity of the quantum relative entropy
(`ContinuousLinearMap.quantumRelativeEntropy_sum_conjStarAlgEquiv_le`) — the route to monotonicity
of the relative entropy under partial trace and hence to the strong subadditivity of the von
Neumann entropy (N&C Theorem 11.14).

## Main definitions

* `OrthonormalBasis.signDiagonalEquiv` — the sign-diagonal unitary as a `LinearIsometryEquiv`.
* `OrthonormalBasis.depolarizingUnitary` — the family `Pσ ∘ Sε` of `1`-design unitaries.

## Main results

* `OrthonormalBasis.equiv_conjStarAlgEquiv_diagonalOperator` — a basis permutation conjugates a
  diagonal operator to the diagonal operator with permuted entries.
* `OrthonormalBasis.sum_equiv_conjStarAlgEquiv_diagonalOperator` — averaging a diagonal operator
  over all basis permutations yields `(d! / d · ∑ w) • I`.
* `OrthonormalBasis.sum_conjStarAlgEquiv_depolarizingUnitary` — the depolarizing `1`-design
  identity `(2^d d!)⁻¹ • ∑ Uⱼ A Uⱼ† = (tr A / d) • I` (N&C Ex 11.19).
-/

@[expose] public section

open Module InnerProductSpace ContinuousLinearMap

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : OrthonormalBasis ι 𝕜 E)

/-- A diagonal operator with **constant** diagonal `c` is `c` times the identity:
`∑ᵢ c • |bᵢ⟩⟨bᵢ| = c • I`. -/
theorem diagonalOperator_const (c : 𝕜) :
    b.diagonalOperator (fun _ => c) = c • (1 : E →L[𝕜] E) := by
  rw [diagonalOperator, ← b.diagonalOperator_one, diagonalOperator, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

section CompleteSpace

variable [CompleteSpace E]

/-- **A basis permutation conjugates a diagonal operator to a diagonal operator with permuted
entries.** For `σ : Equiv.Perm ι`, conjugating `∑ᵢ wᵢ |bᵢ⟩⟨bᵢ|` by the permutation unitary
`b.equiv b σ` gives `∑ⱼ w(σ⁻¹ j) |bⱼ⟩⟨bⱼ|`. -/
theorem equiv_conjStarAlgEquiv_diagonalOperator (σ : Equiv.Perm ι) (w : ι → 𝕜) :
    (b.equiv b σ).conjStarAlgEquiv (b.diagonalOperator w)
      = b.diagonalOperator (fun j => w (σ⁻¹ j)) := by
  rw [diagonalOperator, map_sum]
  simp_rw [map_smul, rankOne_conjStarAlgEquiv, equiv_apply_basis]
  rw [diagonalOperator, ← Equiv.sum_comp σ fun j => w (σ⁻¹ j) • ((rankOne 𝕜) (b j)) (b j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show σ⁻¹ (σ i) = i from Equiv.symm_apply_apply σ i]

/-- **The permutation average of a diagonal operator is a scalar.** Averaging `∑ᵢ wᵢ |bᵢ⟩⟨bᵢ|`
over all `d!` basis permutations equalises the diagonal to its mean:
`∑_σ Pσ (diag w) Pσ† = (d! / d · ∑ᵢ wᵢ) • I`, where `d = |ι|`. The value is computed from the
coordinate-independence of the permuted diagonal (`Equiv.mulLeft` by a transposition) and the total
`∑ⱼ ∑_σ w(σ⁻¹ j) = d! · ∑ᵢ wᵢ`. -/
theorem sum_equiv_conjStarAlgEquiv_diagonalOperator [Nonempty ι] [DecidableEq ι] (w : ι → 𝕜) :
    ∑ σ : Equiv.Perm ι, (b.equiv b σ).conjStarAlgEquiv (b.diagonalOperator w)
      = (((Fintype.card ι).factorial : 𝕜) / (Fintype.card ι : 𝕜) * ∑ i, w i) •
        (1 : E →L[𝕜] E) := by
  -- The permuted diagonal weight `∑_σ w(σ⁻¹ j)` does not depend on `j`.
  have hconst : ∀ j k : ι, (∑ σ : Equiv.Perm ι, w (σ⁻¹ j)) = ∑ σ : Equiv.Perm ι, w (σ⁻¹ k) := by
    intro j k
    rw [← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap j k)) fun σ => w (σ⁻¹ j)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 1
    rw [Equiv.coe_mulLeft, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
      Equiv.swap_apply_left]
  -- Its total over all coordinates is `d! · ∑ᵢ wᵢ`.
  have hsum : (∑ j, ∑ σ : Equiv.Perm ι, w (σ⁻¹ j))
      = ((Fintype.card ι).factorial : 𝕜) * ∑ i, w i := by
    rw [Finset.sum_comm]
    have hσ : ∀ σ : Equiv.Perm ι, (∑ j, w (σ⁻¹ j)) = ∑ i, w i := fun σ =>
      Equiv.sum_comp (σ⁻¹ : Equiv.Perm ι) w
    simp_rw [hσ]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  -- The permutation sum is the diagonal operator of the (constant) permuted weight.
  have hdiag : ∑ σ : Equiv.Perm ι, (b.equiv b σ).conjStarAlgEquiv (b.diagonalOperator w)
      = b.diagonalOperator (fun j => ∑ σ : Equiv.Perm ι, w (σ⁻¹ j)) := by
    simp_rw [equiv_conjStarAlgEquiv_diagonalOperator, diagonalOperator]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
  rw [hdiag]
  have j₀ : ι := Classical.arbitrary ι
  have hn : (Fintype.card ι : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hgval : (∑ σ : Equiv.Perm ι, w (σ⁻¹ j₀))
      = ((Fintype.card ι).factorial : 𝕜) / (Fintype.card ι : 𝕜) * ∑ i, w i := by
    have hcard : (Fintype.card ι : 𝕜) * (∑ σ : Equiv.Perm ι, w (σ⁻¹ j₀))
        = ((Fintype.card ι).factorial : 𝕜) * ∑ i, w i := by
      rw [← hsum, Finset.sum_congr rfl (fun j _ => hconst j j₀), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    field_simp
    linear_combination hcard
  rw [show (fun j => ∑ σ : Equiv.Perm ι, w (σ⁻¹ j))
      = (fun _ : ι => ∑ σ : Equiv.Perm ι, w (σ⁻¹ j₀)) from funext fun j => hconst j j₀,
    diagonalOperator_const, hgval]

/-- The **sign-diagonal unitary** `Sε = ∑ᵢ (-1)^{ε i} |bᵢ⟩⟨bᵢ|` packaged as a
`LinearIsometryEquiv`, via `Unitary.linearIsometryEquiv` on the self-adjoint unitary
`OrthonormalBasis.signDiagonal`. -/
noncomputable def signDiagonalEquiv (ε : ι → Bool) : E ≃ₗᵢ[𝕜] E :=
  Unitary.linearIsometryEquiv ⟨b.signDiagonal ε, b.signDiagonal_mem_unitary ε⟩

@[simp]
theorem coe_signDiagonalEquiv (ε : ι → Bool) :
    ⇑(b.signDiagonalEquiv ε) = ⇑(b.signDiagonal ε) := by
  have h : ((b.signDiagonalEquiv ε).toContinuousLinearEquiv : E →L[𝕜] E) = b.signDiagonal ε :=
    Unitary.coe_linearIsometryEquiv_apply ⟨b.signDiagonal ε, b.signDiagonal_mem_unitary ε⟩
  ext x
  rw [← LinearIsometryEquiv.coe_toContinuousLinearEquiv, ← ContinuousLinearEquiv.coe_coe, h]

omit [CompleteSpace E] in
/-- The sign-diagonal operator squares to the identity (`(±1)² = 1`). -/
theorem signDiagonal_comp_self (ε : ι → Bool) :
    (b.signDiagonal ε).comp (b.signDiagonal ε) = 1 := by
  rw [signDiagonal, diagonalOperator_comp, ← b.diagonalOperator_one]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.one_apply]
  cases ε i <;> norm_num

theorem coe_signDiagonalEquiv_symm (ε : ι → Bool) :
    ⇑(b.signDiagonalEquiv ε).symm = ⇑(b.signDiagonal ε) := by
  ext x
  apply (b.signDiagonalEquiv ε).injective
  rw [LinearIsometryEquiv.apply_symm_apply, coe_signDiagonalEquiv, ← ContinuousLinearMap.comp_apply,
    signDiagonal_comp_self, one_apply_eq_self]

/-- **Conjugation by the sign-diagonal unitary** as `conjStarAlgEquiv` agrees with the raw
composition `Sε ∘ A ∘ Sε`, bridging `OrthonormalBasis.sum_signDiagonal_conj_self` to the
`LinearIsometryEquiv` form. -/
theorem signDiagonalEquiv_conjStarAlgEquiv (ε : ι → Bool) (A : E →L[𝕜] E) :
    (b.signDiagonalEquiv ε).conjStarAlgEquiv A
      = (b.signDiagonal ε).comp (A.comp (b.signDiagonal ε)) := by
  ext y
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, coe_signDiagonalEquiv_symm,
    coe_signDiagonalEquiv]
  simp only [ContinuousLinearMap.comp_apply]

variable [DecidableEq ι]

/-- The **depolarizing `1`-design unitaries**: the composites `Pσ ∘ Sε` of a sign-diagonal unitary
`Sε` and a basis permutation `Pσ`, indexed by `(ε, σ) : (ι → Bool) × Equiv.Perm ι`. Their uniform
average of conjugations is the completely depolarizing channel
(`sum_conjStarAlgEquiv_depolarizingUnitary`). -/
noncomputable def depolarizingUnitary (p : (ι → Bool) × Equiv.Perm ι) : E ≃ₗᵢ[𝕜] E :=
  (b.signDiagonalEquiv p.1).trans (b.equiv b p.2)

/-- **The completely depolarizing channel as a finite unitary `1`-design** (Nielsen & Chuang,
Exercise 11.19). The uniform average of the `2^d · d!` conjugations of `A` by the depolarizing
unitaries `Pσ Sε` equals `(tr A / d) · I`, where `d = |ι|` is the dimension:

`(2^d d!)⁻¹ • ∑_{ε, σ} (Pσ Sε) A (Pσ Sε)† = (tr A / d) • I`.

Conjugating by `Pσ Sε` first dephases `A` to its basis-diagonal (summing over `ε`,
`sum_signDiagonal_conj_self`) and then uniformises that diagonal (averaging over `σ`,
`sum_equiv_conjStarAlgEquiv_diagonalOperator`); the mean of the diagonal entries is the trace over
the dimension. Since the weights `(2^d d!)⁻¹` are a (uniform) probability distribution and each
conjugation is unitary, this exhibits the depolarizing channel as a mixed-unitary channel. -/
theorem sum_conjStarAlgEquiv_depolarizingUnitary [Nonempty ι] (A : E →L[𝕜] E) :
    ∑ p : (ι → Bool) × Equiv.Perm ι,
        (((2 : 𝕜) ^ Fintype.card ι * (Fintype.card ι).factorial)⁻¹) •
          (b.depolarizingUnitary p).conjStarAlgEquiv A
      = (LinearMap.trace 𝕜 E (A : E →ₗ[𝕜] E) / (Fintype.card ι : 𝕜)) • (1 : E →L[𝕜] E) := by
  rw [← Finset.smul_sum]
  -- Reduce the double average to the permutation average of the dephased (diagonal) operator.
  have hbody : ∑ p : (ι → Bool) × Equiv.Perm ι, (b.depolarizingUnitary p).conjStarAlgEquiv A
      = (2 : 𝕜) ^ Fintype.card ι •
          ∑ σ : Equiv.Perm ι, (b.equiv b σ).conjStarAlgEquiv
            (b.diagonalOperator (fun i => inner 𝕜 (b i) (A (b i)))) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hstep : ∀ ε : ι → Bool, (b.depolarizingUnitary (ε, σ)).conjStarAlgEquiv A
        = (b.equiv b σ).conjStarAlgEquiv
            ((b.signDiagonal ε).comp (A.comp (b.signDiagonal ε))) := fun ε => by
      simp only [depolarizingUnitary, LinearIsometryEquiv.conjStarAlgEquiv_trans,
        StarAlgEquiv.trans_apply, signDiagonalEquiv_conjStarAlgEquiv]
    simp_rw [hstep]
    rw [← map_sum, sum_signDiagonal_conj_self, map_smul]
  rw [hbody, sum_equiv_conjStarAlgEquiv_diagonalOperator, smul_smul, smul_smul,
    LinearMap.trace_eq_sum_inner (A : E →ₗ[𝕜] E) b]
  simp only [ContinuousLinearMap.coe_coe]
  have hn : (Fintype.card ι : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfac : ((Fintype.card ι).factorial : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (2 : 𝕜) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ two_ne_zero
  congr 1
  field_simp

end CompleteSpace

end OrthonormalBasis

namespace LinearIsometryEquiv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- **There is a finite unitary `1`-design realising the completely depolarizing channel**
(Nielsen & Chuang, Exercise 11.19, existential form). On any nontrivial finite-dimensional inner
product space of dimension `d = finrank 𝕜 E`, there exist a finite family of unitaries
`Uⱼ : E ≃ₗᵢ[𝕜] E` and a probability distribution `pⱼ` such that for **every** operator `A`,

`∑ⱼ pⱼ Uⱼ A Uⱼ† = (tr A / d) • I`.

This is the "show that there exists a set of unitary matrices `Uⱼ` and a probability distribution
`pⱼ` such that `∑ⱼ pⱼ Uⱼ A Uⱼ† = tr(A) I/d`" of the exercise. The witness is the depolarizing
`1`-design `{Pσ Sε}` of `OrthonormalBasis.sum_conjStarAlgEquiv_depolarizingUnitary` for the standard
orthonormal basis, with the uniform weights `pⱼ = (2^d d!)⁻¹`. -/
theorem exists_conjStarAlgEquiv_oneDesign [Nontrivial E] :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → (E ≃ₗᵢ[𝕜] E)) (p : ι → ℝ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
        ∀ A : E →L[𝕜] E, ∑ i, (p i : 𝕜) • (U i).conjStarAlgEquiv A
          = (LinearMap.trace 𝕜 E (A : E →ₗ[𝕜] E) / (Module.finrank 𝕜 E : 𝕜)) • (1 : E →L[𝕜] E) := by
  classical
  set d := Module.finrank 𝕜 E with hd
  have hpos : 0 < d := Module.finrank_pos
  have : Nonempty (Fin d) := ⟨⟨0, hpos⟩⟩
  set b := stdOrthonormalBasis 𝕜 E with hb
  have hcard : Fintype.card ((Fin d → Bool) × Equiv.Perm (Fin d)) = 2 ^ d * d.factorial := by
    simp [Fintype.card_perm]
  refine ⟨(Fin d → Bool) × Equiv.Perm (Fin d), inferInstance, b.depolarizingUnitary,
    fun _ => ((2 : ℝ) ^ d * d.factorial)⁻¹, fun _ => by positivity, ?_, ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    have : ((2 : ℝ) ^ d * d.factorial) ≠ 0 := by positivity
    push_cast
    field_simp
  · intro A
    have htw := b.sum_conjStarAlgEquiv_depolarizingUnitary A
    rw [Fintype.card_fin] at htw
    rw [← htw]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    push_cast
    ring

end LinearIsometryEquiv
