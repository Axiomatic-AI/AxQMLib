/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelityTwirl
public import ToMathlib.Analysis.InnerProductSpace.Orthonormal

/-! # Subspace fidelity controls the entanglement fidelity (Nielsen & Chuang, Problem 9.3)

This file assembles **fact (5)** of Nielsen & Chuang §9.3 — the content of *Problem 9.3*: if a
trace-preserving quantum operation preserves every pure state in the support of a density operator
`ρ` to fidelity at least `1 − η`, then it preserves `ρ`'s entanglement to fidelity at least
`1 − 3η/2`.

Concretely, write `ρ = Σₐ pₐ |bₐ⟩⟨bₐ|` in a spectral eigenbasis (`b` an orthonormal basis, `p` a
probability vector). A unit vector `ψ` lies in the **support** of `ρ` exactly when it has no
component along the zero-weight eigenvectors, `⟨bₐ, ψ⟩ = 0` whenever `pₐ = 0`. The hypothesis is
that `⟨ψ| E(|ψ⟩⟨ψ|) |ψ⟩ ≥ 1 − η` for every such `ψ`, and the conclusion is
`F(ρ, E) ≥ 1 − 3η/2` (`ContinuousLinearMap.entanglementFidelity_ge_one_sub_of_subspace_fidelity`).

The proof combines the two halves developed in `EntanglementFidelityBound` and
`EntanglementFidelityTwirl`:

* the **phase-diagonal-twirl reduction** `1 − F(ρ, E) ≤ η + S_off`
  (`ContinuousLinearMap.one_sub_entanglementFidelity_le_offDiagCoherenceSum`), whose per-`θ`
  hypothesis is discharged here because every phase-twirl state `ψ_θ` is a *unit vector in the
  support of `ρ`* (`ContinuousLinearMap.norm_phaseTwirlState`, plus the vanishing of its zero-weight
  components), so the physical fidelity hypothesis applies to it via
  `ContinuousLinearMap.re_inner_krausSumₗ_rankOne_self`;
* the **off-diagonal coherence bound** `S_off ≤ η/2`
  (`ContinuousLinearMap.offDiagCoherenceSum_le_of_pos`), a support-aware refinement of
  `offDiagCoherenceSum_le`: the doubly `p`-weighted off-diagonal sum only sees columns with
  `pₐ > 0`, whose eigenvectors *are* in the support, so a per-column fidelity budget is needed only
  there.

Combining, `F(ρ, E) ≥ 1 − η − S_off ≥ 1 − η − η/2 = 1 − 3η/2`. The `η/2` (rather than `η`) is the
tight constant of fact (5); it comes from `weighted_offDiag_sum_le_half`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §9.3 (Problem 9.3, fact (5)).
-/

open scoped InnerProductSpace ComplexConjugate

open InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]

omit [FiniteDimensional ℂ H] [CompleteSpace H] [DecidableEq ι] in
/-- **The phase-twirl state is a unit vector.** For an orthonormal basis `b` and a probability
vector `p` (`0 ≤ p`, `∑ p = 1`), the phase-twirl state `ψ_θ = Σₐ √pₐ · stdAddChar(θₐ) · bₐ` has
`‖ψ_θ‖ = 1`. By orthonormality `‖ψ_θ‖² = Σₐ ‖√pₐ · stdAddChar(θₐ)‖² = Σₐ pₐ = 1`, using that the
character values lie on the unit circle (`Circle.norm_coe`) and `√pₐ² = pₐ`. -/
theorem norm_phaseTwirlState (b : OrthonormalBasis ι ℂ H) (p : ι → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (N : ℕ) [NeZero N] (θ : ι → ZMod N) :
    ‖phaseTwirlState b p N θ‖ = 1 := by
  have hsq : ‖phaseTwirlState b p N θ‖ ^ 2 = 1 := by
    rw [phaseTwirlState, b.orthonormal.norm_sum_smul_sq, ← hp1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_mul, mul_pow, ZMod.stdAddChar_apply, Circle.norm_coe, one_pow, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hp0 a)]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]

omit [DecidableEq ι] in
/-- **Fact (5) of Nielsen & Chuang §9.3 (Problem 9.3).** Let `ρ = Σₐ pₐ |bₐ⟩⟨bₐ|` be a density
operator written in a spectral eigenbasis (`b` an orthonormal basis, `p` a probability vector), and
let `E` be a trace-preserving quantum operation (operation elements `Eⱼ`, `Σⱼ Eⱼ† Eⱼ = 1`). If
every pure state `|ψ⟩` in the support of `ρ` — i.e. every unit vector `ψ` with `⟨bₐ, ψ⟩ = 0` for all
`a` with `pₐ = 0` — is preserved to fidelity at least `1 − η`,
`⟨ψ| E(|ψ⟩⟨ψ|) |ψ⟩ ≥ 1 − η`, then the entanglement fidelity obeys `F(ρ, E) ≥ 1 − 3η/2`.

The proof reads the physical hypothesis through `re_inner_krausSumₗ_rankOne_self`
(`⟨ψ|E(|ψ⟩⟨ψ|)|ψ⟩ = Σⱼ |⟨ψ, Eⱼ ψ⟩|²`) and applies it to two families of support vectors: every
phase-twirl state `ψ_θ` (a unit vector whose zero-weight components vanish), giving the twirl
reduction `1 − F(ρ, E) ≤ η + S_off`; and every positive-weight eigenvector `bₐ`, giving
`S_off ≤ η/2`. Their sum is `1 − 3η/2`. The twirl uses the modulus `N = 3`. -/
theorem entanglementFidelity_ge_one_sub_of_subspace_fidelity (b : OrthonormalBasis ι ℂ H)
    (p : ι → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (E : κ → H →L[ℂ] H)
    (hE : ∑ j, adjoint (E j) * E j = 1) {η : ℝ}
    (hfid : ∀ ψ : H, ‖ψ‖ = 1 → (∀ a, p a = 0 → inner ℂ (b a) ψ = 0) →
      1 - η ≤ RCLike.re (inner ℂ ψ (krausSumₗ E (rankOne ℂ ψ ψ) ψ))) :
    1 - 3 * η / 2 ≤ entanglementFidelity (∑ a, (p a : ℂ) • rankOne ℂ (b a) (b a)) E := by
  classical
  -- The physical hypothesis, read through `re_inner_krausSumₗ_rankOne_self`.
  have hfid' : ∀ ψ : H, ‖ψ‖ = 1 → (∀ a, p a = 0 → inner ℂ (b a) ψ = 0) →
      1 - η ≤ ∑ j, ‖inner ℂ ψ (E j ψ)‖ ^ 2 := by
    intro ψ hψ hsupp
    have h := hfid ψ hψ hsupp
    rwa [re_inner_krausSumₗ_rankOne_self] at h
  -- A positive-weight eigenvector lies in `supp ρ`, so its fidelity is `≥ 1 − η`.
  have hfid_eig : ∀ a, 0 < p a → 1 - η ≤ ∑ j, ‖inner ℂ (b a) (E j (b a))‖ ^ 2 := by
    intro a ha
    refine hfid' (b a) (b.orthonormal.1 a) fun c hc => ?_
    have hca : c ≠ a := fun h => by rw [h] at hc; exact (ha.ne' hc)
    exact b.orthonormal.2 hca
  -- There is a positive-weight index (probabilities sum to `1`).
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < p a := by
    by_contra h
    have hle : ∑ a, p a ≤ 0 := Finset.sum_nonpos fun a _ => not_lt.mp (not_exists.mp h a)
    rw [hp1] at hle
    norm_num at hle
  -- `η ≥ 0`: the fidelity of `b a₀` is `≤ 1`.
  have hη : 0 ≤ η := by
    linarith [hfid_eig a₀ ha₀, sum_normSq_inner_self_le_one (b.orthonormal.1 a₀) E hE]
  -- Off-diagonal coherence bound `S_off ≤ η/2`.
  have hSoff : offDiagCoherenceSum (⇑b) p E ≤ η / 2 :=
    offDiagCoherenceSum_le_of_pos b p hp0 hp1 E hE hη hfid_eig
  -- Twirl reduction `1 − F ≤ η + S_off`: each phase-twirl state is a unit support vector.
  have htwirl : ∀ θ : ι → ZMod 3,
      1 - η ≤ ∑ j, ‖inner ℂ (phaseTwirlState b p 3 θ) (E j (phaseTwirlState b p 3 θ))‖ ^ 2 := by
    intro θ
    refine hfid' (phaseTwirlState b p 3 θ) (norm_phaseTwirlState b p hp0 hp1 3 θ) fun a ha => ?_
    rw [phaseTwirlState, Orthonormal.inner_right_fintype b.orthonormal, ha, Real.sqrt_zero]
    push_cast
    ring
  have hred : 1 - entanglementFidelity (∑ a, (p a : ℂ) • rankOne ℂ (b a) (b a)) E
      ≤ η + offDiagCoherenceSum (⇑b) p E :=
    one_sub_entanglementFidelity_le_offDiagCoherenceSum b p hp0 3 (by norm_num) E htwirl
  linarith [hred, hSoff]

end ContinuousLinearMap
