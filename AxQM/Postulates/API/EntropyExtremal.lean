/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EntropyComposite

/-!
# AxQM — the equality case of the von Neumann entropy bound

Nielsen & Chuang, Theorem 11.8, part (2): in a `d`-dimensional space the von Neumann entropy
satisfies `S(ρ) ≤ log d`, **with equality if and only if `ρ` is the maximally mixed state `I/d`**.
The `≤` bound (`State.vonNeumannEntropy_le_log_finrank`) and the value at the maximally mixed state
(`State.vonNeumannEntropy_maximallyMixed`, `S(I/d) = log d`) are in
`AxQM/Postulates/API/Entropy.lean` and `AxQM/Postulates/API/EntropyComposite.lean`. This file
supplies the **converse / uniqueness** half — a state saturating the bound *is* the maximally
mixed state — hence the full "equality iff maximally mixed" characterization.

## Proof

Diagonalize `ρ.op` in its canonical orthonormal eigenbasis with eigenvalue spectrum `λ`
(`IsSelfAdjoint.eigenvectorBasis` / `eigenvalues`). Then `λ` is a probability distribution
(`IsDensityOp.eigenvalues_nonneg` / `eigenvalues_sum_eq_one`) and `S(ρ) = H(λ)`
(`ContinuousLinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq`). The Shannon-entropy
equality case `Real.entropy_eq_log_card_iff` forces the uniform spectrum `λᵢ = 1/d`, so the spectral
reconstruction `IsSelfAdjoint.spectral_sum` together with `OrthonormalBasis.sum_rankOne_eq_id`
(`∑ᵢ |eᵢ⟩⟨eᵢ| = I`) collapses `ρ.op` to `(1/d) • I`, i.e. `ρ = maximallyMixedState S`
(`maximallyMixedState_op`).

## Main results

* `AxQM.State.eq_maximallyMixed_of_vonNeumannEntropy_eq_log_finrank` — the converse
  direction `S(ρ) = log d ⇒ ρ = I/d`.
* `AxQM.State.vonNeumannEntropy_eq_log_finrank_iff_eq_maximallyMixed` — the full equality
  characterization `S(ρ) = log d ↔ ρ = I/d`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Equality case of the von Neumann entropy bound** (Nielsen & Chuang, Theorem 11.8, part (2),
converse direction): a state whose entropy attains the maximum `S(ρ) = log d` (`d = dim S.space`)
is the maximally mixed state `I/d`.

The eigenvalues of `ρ.op` form a probability distribution whose Shannon entropy equals `S(ρ)`; the
equality case `Real.entropy_eq_log_card_iff` forces them to be uniform (`= 1/d`), and spectral
reconstruction gives `ρ.op = (1/d) • I = (maximallyMixedState S).op`. -/
theorem State.eq_maximallyMixed_of_vonNeumannEntropy_eq_log_finrank [Nontrivial S.space]
    (ρ : State S) (h : ρ.vonNeumannEntropy = Real.log (Module.finrank ℂ S.space : ℝ)) :
    ρ = maximallyMixedState S := by
  have hsa : IsSelfAdjoint ρ.op := ρ.isDensity.isPositive.isSelfAdjoint
  have hfin : Module.finrank ℂ S.space = Module.finrank ℂ S.space := rfl
  have : Nonempty (Fin (Module.finrank ℂ S.space)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  -- The canonical spectrum is a probability distribution.
  have hnonneg : ∀ i, 0 ≤ hsa.isSymmetric.eigenvalues hfin i :=
    fun i => ρ.isDensity.eigenvalues_nonneg hfin i
  have hsum : ∑ i, hsa.isSymmetric.eigenvalues hfin i = 1 :=
    ρ.isDensity.eigenvalues_sum_eq_one hfin
  have hcard : Fintype.card (Fin (Module.finrank ℂ S.space)) = Module.finrank ℂ S.space :=
    Fintype.card_fin _
  -- `S(ρ)` is the Shannon entropy of the spectrum, so the value `log d` forces uniformity.
  have hent : Real.entropy (fun i => hsa.isSymmetric.eigenvalues hfin i)
      = Real.log (Fintype.card (Fin (Module.finrank ℂ S.space)) : ℝ) := by
    rw [← ContinuousLinearMap.vonNeumannEntropy_eq_entropy_eigenvalues_of_finrank_eq
      hsa.isSymmetric hfin, ← State.vonNeumannEntropy_def, h, hcard]
  have huniform : ∀ i, hsa.isSymmetric.eigenvalues hfin i
      = (Fintype.card (Fin (Module.finrank ℂ S.space)) : ℝ)⁻¹ :=
    (Real.entropy_eq_log_card_iff hnonneg hsum).mp hent
  -- Spectral reconstruction: `ρ.op = ∑ λᵢ |eᵢ⟩⟨eᵢ| = (1/d) • ∑ |eᵢ⟩⟨eᵢ| = (1/d) • I`.
  refine State.ext ?_
  rw [maximallyMixedState_op, hsa.spectral_sum hfin]
  simp_rw [huniform, hcard]
  rw [← Finset.smul_sum, OrthonormalBasis.sum_rankOne_eq_id]
  push_cast
  rw [← ContinuousLinearMap.one_def]

/-- **Full equality characterization of the von Neumann entropy bound** (Nielsen & Chuang,
Theorem 11.8, part (2)): the entropy of a state attains its maximum `S(ρ) = log d`
(`d = dim S.space`) if and only if `ρ` is the maximally mixed state `I/d`. The forward direction is
`State.eq_maximallyMixed_of_vonNeumannEntropy_eq_log_finrank`; the backward direction is the value
`State.vonNeumannEntropy_maximallyMixed`. -/
theorem State.vonNeumannEntropy_eq_log_finrank_iff_eq_maximallyMixed [Nontrivial S.space]
    (ρ : State S) :
    ρ.vonNeumannEntropy = Real.log (Module.finrank ℂ S.space : ℝ) ↔ ρ = maximallyMixedState S := by
  refine ⟨ρ.eq_maximallyMixed_of_vonNeumannEntropy_eq_log_finrank, ?_⟩
  rintro rfl
  exact State.vonNeumannEntropy_maximallyMixed S

end AxQM
