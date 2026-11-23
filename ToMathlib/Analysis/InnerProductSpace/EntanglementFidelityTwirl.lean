/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.EntanglementFidelityBound
public import ToMathlib.Analysis.Fourier.ZModUnitary

/-! # The phase-diagonal twirl reduction for the entanglement fidelity

This file carries out the **phase-diagonal-twirl reduction** at the heart of Nielsen & Chuang's
*Problem 9.3* (fact (5): if `⟨ψ|E(|ψ⟩⟨ψ|)|ψ⟩ ≥ 1 − η` for every unit `ψ` in the support of `ρ`,
then `F(ρ, E) ≥ 1 − 3η/2`).

Write a density operator in a spectral eigenbasis, `ρ = Σₐ pₐ |eₐ⟩⟨eₐ|`. For a "phase vector"
`θ : ι → ZMod N` the **phase-twirl state** is the unit vector in `supp(ρ)`
`ψ_θ = Σₐ √pₐ · e^{2πi θₐ/N} |eₐ⟩` (`ContinuousLinearMap.phaseTwirlState`). Averaging the pure-state
fidelities `Σⱼ |⟨ψ_θ, Eⱼ ψ_θ⟩|²` over the finite phase group `(ZMod N)^ι` (each mode independently,
`N ≥ 3`) kills the cross terms with different phases and returns *exactly* the entanglement fidelity
plus the off-diagonal coherence,
`(1/Nᶜ) Σ_θ Σⱼ |⟨ψ_θ, Eⱼ ψ_θ⟩|² = F(ρ, E) + S_off`
(`ContinuousLinearMap.sum_phaseTwirl_normSq_inner_eq`, where `c = card ι`). Since every summand is
`≥ 1 − η` by hypothesis, the average is `≥ 1 − η`, giving the reduction `1 − F(ρ, E) ≤ η + S_off`
(`ContinuousLinearMap.one_sub_entanglementFidelity_le_offDiagCoherenceSum`).
Combined with `ContinuousLinearMap.offDiagCoherenceSum_le` (`S_off ≤ η/2`, from
`EntanglementFidelityBound`) this is fact (5): `F(ρ, E) ≥ 1 − η − S_off ≥ 1 − 3η/2`.

The engine of the twirl is the **finite-Fourier orthogonality** on the group `(ZMod N)^ι`: the sum
of the standard additive character over a nontrivial linear phase vanishes
(`ZMod.sum_stdAddChar_sum_mul`), so only the phase configurations satisfying a two-element
**matching condition** survive (`ZMod.sum_stdAddChar_sub_add_sub`); the surviving terms reassemble
into `F(ρ, E) + S_off`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §9.3 (Problem 9.3, fact (5)).
-/

open scoped InnerProductSpace ComplexConjugate

open InnerProductSpace

@[expose] public section

private theorem addChar_map_finsetSum {A M ι : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ψ.map_add_eq_mul, ih]

namespace ZMod

/-- **Finite-Fourier orthogonality on `(ZMod N)^ι`.** For a coefficient vector `g : ι → ZMod N`,
the sum over all phase vectors `θ : ι → ZMod N` of the standard additive character at the linear
phase `∑ₖ gₖ θₖ` is `Nᶜ` (with `c = card ι`) if `g = 0` and `0` otherwise:
`∑_θ stdAddChar (∑ₖ gₖ θₖ) = if (∀ k, gₖ = 0) then Nᶜ else 0`.

The character of the linear phase factorises over the modes (`addChar_map_finsetSum`), the sum over
`(ZMod N)^ι` becomes a product of per-mode sums (`Finset.prod_univ_sum`), and each per-mode sum is
`ZMod.sum_stdAddChar_mul`, i.e. `N` if `gₖ = 0` and `0` otherwise. -/
theorem sum_stdAddChar_sum_mul {N : ℕ} [NeZero N] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ZMod N) :
    ∑ θ : ι → ZMod N, ZMod.stdAddChar (∑ k, g k * θ k)
      = if (∀ k, g k = 0) then (N : ℂ) ^ (Fintype.card ι) else 0 := by
  have h1 : ∀ θ : ι → ZMod N,
      ZMod.stdAddChar (∑ k, g k * θ k) = ∏ k, ZMod.stdAddChar (g k * θ k) :=
    fun θ => addChar_map_finsetSum ZMod.stdAddChar Finset.univ (fun k => g k * θ k)
  have h2 : ∏ k : ι, (∑ t : ZMod N, ZMod.stdAddChar (g k * t))
      = ∑ θ : ι → ZMod N, ∏ k, ZMod.stdAddChar (g k * θ k) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [h1, ← h2, ZMod.sum_stdAddChar_mul]
  by_cases h : ∀ k, g k = 0
  · rw [ite_eq_left h, Finset.prod_congr rfl (fun k _ => ite_eq_left (h k)), Finset.prod_const,
      Finset.card_univ]
  · rw [ite_eq_right h]
    rw [not_forall] at h
    obtain ⟨k, hk⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)

/-- The **matching condition** of the phase twirl. In `ZMod N` with `N ≥ 3`, the per-mode
coefficient `[k=d] − [k=a] + [k=a'] − [k=c']` vanishes for every `k` iff the two-element multisets
`{d, a'}` and `{a, c'}` agree, i.e. `(d = a ∧ a' = c') ∨ (d = c' ∧ a' = a)`. The `N ≥ 3` bound makes
the residues `0, 1, 2` distinct in `ZMod N`, so the mod-`N` equation lifts to `ℕ`. -/
private theorem matching_iff {N : ℕ} [NeZero N] (hN : 3 ≤ N) {ι : Type*} [DecidableEq ι]
    (a d a' c' : ι) :
    (∀ k : ι, (if k = d then (1 : ZMod N) else 0) - (if k = a then 1 else 0)
        + (if k = a' then 1 else 0) - (if k = c' then 1 else 0) = 0)
      ↔ ((d = a ∧ a' = c') ∨ (d = c' ∧ a' = a)) := by
  constructor
  · intro H
    have Hnat : ∀ k : ι, (if k = d then 1 else 0) + (if k = a' then 1 else 0)
        = (if k = a then 1 else 0) + (if k = c' then (1 : ℕ) else 0) := by
      intro k
      have hk := H k
      have hcast : (((if k = d then 1 else 0) + (if k = a' then 1 else 0) : ℕ) : ZMod N)
          = (((if k = a then 1 else 0) + (if k = c' then 1 else 0) : ℕ) : ZMod N) := by
        push_cast
        linear_combination hk
      have hpb : (if k = d then 1 else 0) + (if k = a' then 1 else 0) < N := by
        split_ifs <;> omega
      have hmb : (if k = a then 1 else 0) + (if k = c' then 1 else 0) < N := by
        split_ifs <;> omega
      have hv := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hpb, Nat.mod_eq_of_lt hmb] at hv
    have hd := Hnat d
    rw [ite_eq_left rfl] at hd
    have key : d = a ∨ d = c' := by
      by_contra hcon
      rw [not_or] at hcon
      rw [ite_eq_right hcon.1, ite_eq_right hcon.2] at hd
      simp at hd
    rcases key with hda | hdc'
    · left
      refine ⟨hda, ?_⟩
      have ha' := Hnat a'
      rw [ite_eq_left rfl, hda] at ha'
      by_contra hac
      rw [ite_eq_right hac] at ha'
      omega
    · right
      refine ⟨hdc', ?_⟩
      have ha' := Hnat a'
      rw [ite_eq_left rfl, ← hdc'] at ha'
      by_contra haa
      rw [ite_eq_right haa] at ha'
      omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) k <;> ring

/-- **The phase-difference character sum.** For fixed indices `a d a' c'` in a finite type
(`N ≥ 3`), summing the standard additive character of `θd − θa + θa' − θc'` over all phase vectors
`θ : ι → ZMod N` gives `Nᶜ` (`c = card ι`) exactly when the matching condition holds:
`∑_θ stdAddChar (θd − θa + θa' − θc') = if (d = a ∧ a' = c') ∨ (d = c' ∧ a' = a) then Nᶜ else 0`.

This is `ZMod.sum_stdAddChar_sum_mul` at the indicator coefficient
`gₖ = [k=d] − [k=a] + [k=a'] − [k=c']`, whose vanishing is `matching_iff`. -/
theorem sum_stdAddChar_sub_add_sub {N : ℕ} [NeZero N] (hN : 3 ≤ N) {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (a d a' c' : ι) :
    (∑ θ : ι → ZMod N, ZMod.stdAddChar (θ d - θ a + θ a' - θ c'))
      = if ((d = a ∧ a' = c') ∨ (d = c' ∧ a' = a)) then (N : ℂ) ^ (Fintype.card ι) else 0 := by
  set g : ι → ZMod N := fun k => (if k = d then 1 else 0) - (if k = a then 1 else 0)
    + (if k = a' then 1 else 0) - (if k = c' then 1 else 0) with hgdef
  have hg : ∀ θ : ι → ZMod N, θ d - θ a + θ a' - θ c' = ∑ k, g k * θ k := by
    intro θ
    simp only [hgdef, sub_mul, add_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  calc (∑ θ : ι → ZMod N, ZMod.stdAddChar (θ d - θ a + θ a' - θ c'))
      = ∑ θ : ι → ZMod N, ZMod.stdAddChar (∑ k, g k * θ k) := by simp_rw [hg]
    _ = if (∀ k, g k = 0) then (N : ℂ) ^ (Fintype.card ι) else 0 := sum_stdAddChar_sum_mul g
    _ = if ((d = a ∧ a' = c') ∨ (d = c' ∧ a' = a)) then (N : ℂ) ^ (Fintype.card ι) else 0 := by
        refine if_congr ?_ rfl rfl
        simp only [hgdef]
        exact matching_iff hN a d a' c'

end ZMod

/-- **The phase-twirl character-orthogonality identity (abstract combinatorial core).** For real
amplitudes `w : ι → ℝ` and a complex matrix-element array `M : ι → ι → ℂ`, averaging over all phase
vectors `θ : ι → ZMod N` (`N ≥ 3`) the squared modulus of the sesquilinear form
`∑ₐ ∑_d wₐ e^{-2πiθₐ/N} · w_d e^{2πiθ_d/N} · M a d` collapses — by finite-Fourier orthogonality
(`ZMod.sum_stdAddChar_sub_add_sub`) and inclusion–exclusion — to `Nᶜ` (`c = card ι`) times the
diagonal square plus off-diagonal weight:
`∑_θ ‖∑ₐ ∑_d …‖² = Nᶜ · (‖∑ₐ wₐ² Mₐₐ‖² + ∑_d ∑_{a≠d} wₐ² w_d² ‖M a d‖²)`.

Only the phase configurations `(a, d, a', c')` with `(d = a ∧ a' = c') ∨ (d = c' ∧ a' = a)` survive
the `θ`-average; the first branch reassembles the diagonal square `‖∑ₐ wₐ² Mₐₐ‖²`, the second the
full weighted `∑_{a,d}`, and their overlap (removed once) is the diagonal, leaving the off-diagonal
`∑_{a≠d}`. This is the engine of the phase-diagonal twirl in Nielsen & Chuang's *Problem 9.3*. -/
private theorem sum_char_twirl_normSq {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (M : ι → ι → ℂ) :
    ∑ θ : ι → ZMod N,
        ‖∑ a, ∑ d, ((w a : ℂ) * conj (ZMod.stdAddChar (θ a)))
          * ((w d : ℂ) * ZMod.stdAddChar (θ d)) * M a d‖ ^ 2
      = (N : ℝ) ^ Fintype.card ι
        * (‖∑ a, ((w a ^ 2 : ℝ) : ℂ) * M a a‖ ^ 2
          + ∑ d, ∑ a ∈ Finset.univ.erase d, (w a ^ 2 * w d ^ 2) * ‖M a d‖ ^ 2) := by
  classical
  -- `↑‖z‖² = z · conj z`, and the finite-Fourier inclusion–exclusion identity.
  have hnorm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    intro z; rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  have hIE : ∀ (P Q : Prop) [Decidable P] [Decidable Q] (z : ℂ),
      (if (P ∨ Q) then z else 0)
        = (if P then z else 0) + (if Q then z else 0) - (if (P ∧ Q) then z else 0) := by
    intro P Q _ _ z; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  -- the phase-combination identity `conj χθa · χθd · χθa' · conj χθc' = χ(θd − θa + θa' − θc')`.
  have hconj : ∀ x : ZMod N, conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) :=
    fun x => (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm
  have hchar : ∀ (θ : ι → ZMod N) (a d a' c' : ι),
      conj (ZMod.stdAddChar (θ a)) * ZMod.stdAddChar (θ d)
          * ZMod.stdAddChar (θ a') * conj (ZMod.stdAddChar (θ c'))
        = ZMod.stdAddChar (θ d - θ a + θ a' - θ c') := by
    intro θ a d a' c'
    rw [hconj (θ a), hconj (θ c'),
      show θ d - θ a + θ a' - θ c' = θ d + -θ a + θ a' + -θ c' by ring,
      ZMod.stdAddChar.map_add_eq_mul, ZMod.stdAddChar.map_add_eq_mul,
      ZMod.stdAddChar.map_add_eq_mul]
    ring
  -- per-quadruple `θ`-sum: character orthogonality picks out the matched configurations.
  have hquad : ∀ a d a' c' : ι,
      (∑ θ : ι → ZMod N,
          (((w a : ℂ) * conj (ZMod.stdAddChar (θ a))) * ((w d : ℂ) * ZMod.stdAddChar (θ d)) * M a d)
            * conj (((w a' : ℂ) * conj (ZMod.stdAddChar (θ a')))
              * ((w c' : ℂ) * ZMod.stdAddChar (θ c')) * M a' c'))
        = ((w a : ℂ) * (w d : ℂ) * (w a' : ℂ) * (w c' : ℂ)) * (M a d * conj (M a' c'))
          * (if ((d = a ∧ a' = c') ∨ (d = c' ∧ a' = a)) then (N : ℂ) ^ Fintype.card ι else 0) := by
    intro a d a' c'
    have hterm : ∀ θ : ι → ZMod N,
        (((w a : ℂ) * conj (ZMod.stdAddChar (θ a))) * ((w d : ℂ) * ZMod.stdAddChar (θ d)) * M a d)
            * conj (((w a' : ℂ) * conj (ZMod.stdAddChar (θ a')))
              * ((w c' : ℂ) * ZMod.stdAddChar (θ c')) * M a' c')
          = (((w a : ℂ) * (w d : ℂ) * (w a' : ℂ) * (w c' : ℂ)) * (M a d * conj (M a' c')))
            * ZMod.stdAddChar (θ d - θ a + θ a' - θ c') := by
      intro θ
      rw [← hchar θ a d a' c']
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [Finset.sum_congr rfl (fun θ _ => hterm θ), ← Finset.mul_sum,
      ZMod.sum_stdAddChar_sub_add_sub hN]
  -- collapse of the three inclusion–exclusion sums over the matched configurations.
  have collapseP : ∀ G : ι → ι → ι → ι → ℂ,
      (∑ a, ∑ a', ∑ d, ∑ c', if (d = a ∧ a' = c') then G a a' d c' else 0)
        = ∑ a, ∑ a', G a a' a a' := by
    intro G
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have collapseQ : ∀ G : ι → ι → ι → ι → ℂ,
      (∑ a, ∑ a', ∑ d, ∑ c', if (d = c' ∧ a' = a) then G a a' d c' else 0)
        = ∑ a, ∑ d, G a a d d := by
    intro G
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have collapsePQ : ∀ G : ι → ι → ι → ι → ℂ,
      (∑ a, ∑ a', ∑ d, ∑ c', if ((d = a ∧ a' = c') ∧ (d = c' ∧ a' = a)) then G a a' d c' else 0)
        = ∑ a, G a a a a := by
    intro G
    refine Finset.sum_congr rfl fun a _ => ?_
    have hcond : ∀ a' d c' : ι,
        (((d = a ∧ a' = c') ∧ (d = c' ∧ a' = a)) : Prop) ↔ (d = a ∧ a' = a ∧ c' = a) := by
      intro a' d c'; constructor
      · rintro ⟨⟨hda, hac'⟩, _, ha'a⟩; exact ⟨hda, ha'a, hac'.symm.trans ha'a⟩
      · rintro ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩
    simp only [hcond, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  -- diagonal-square and off-diagonal repackaging of the surviving configurations.
  have hDsum : (∑ a, ((w a : ℂ) * (w a : ℂ)) * M a a) = ∑ a, ((w a ^ 2 : ℝ) : ℂ) * M a a :=
    Finset.sum_congr rfl fun a _ => by push_cast; ring
  have hSP : (∑ a, ∑ a',
        ((w a : ℂ) * (w a : ℂ) * (w a' : ℂ) * (w a' : ℂ)) * (M a a * conj (M a' a')))
      = ((‖∑ a, ((w a ^ 2 : ℝ) : ℂ) * M a a‖ ^ 2 : ℝ) : ℂ) := by
    rw [hnorm, ← hDsum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    simp only [map_mul, Complex.conj_ofReal]; ring
  have hSQPQ : (∑ a, ∑ d,
          ((w a : ℂ) * (w d : ℂ) * (w a : ℂ) * (w d : ℂ)) * (M a d * conj (M a d)))
        - ∑ a, ((w a : ℂ) * (w a : ℂ) * (w a : ℂ) * (w a : ℂ)) * (M a a * conj (M a a))
      = ((∑ d, ∑ a ∈ Finset.univ.erase d, (w a ^ 2 * w d ^ 2) * ‖M a d‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.ofReal_sum, Finset.sum_erase_eq_sub (Finset.mem_univ d)]
    congr 1
    · exact Finset.sum_congr rfl fun a _ => by rw [Complex.ofReal_mul, hnorm]; push_cast; ring
    · rw [Complex.ofReal_mul, hnorm]; push_cast; ring
  -- lift to `ℂ`, expand the squared modulus, sum over `θ`, and evaluate the matched sum.
  refine Complex.ofReal_injective ?_
  calc ((∑ θ : ι → ZMod N, ‖∑ a, ∑ d, ((w a : ℂ) * conj (ZMod.stdAddChar (θ a)))
              * ((w d : ℂ) * ZMod.stdAddChar (θ d)) * M a d‖ ^ 2 : ℝ) : ℂ)
      = ∑ θ : ι → ZMod N, (∑ a, ∑ d, ((w a : ℂ) * conj (ZMod.stdAddChar (θ a)))
              * ((w d : ℂ) * ZMod.stdAddChar (θ d)) * M a d)
            * conj (∑ a, ∑ d, ((w a : ℂ) * conj (ZMod.stdAddChar (θ a)))
              * ((w d : ℂ) * ZMod.stdAddChar (θ d)) * M a d) := by
        rw [Complex.ofReal_sum]; exact Finset.sum_congr rfl fun θ _ => hnorm _
    _ = ∑ θ : ι → ZMod N, ∑ a, ∑ a', ∑ d, ∑ c',
          (((w a : ℂ) * conj (ZMod.stdAddChar (θ a))) * ((w d : ℂ) * ZMod.stdAddChar (θ d)) * M a d)
            * conj (((w a' : ℂ) * conj (ZMod.stdAddChar (θ a')))
              * ((w c' : ℂ) * ZMod.stdAddChar (θ c')) * M a' c') := by
        refine Finset.sum_congr rfl fun θ _ => ?_
        simp only [map_sum]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ a, ∑ a', ∑ d, ∑ c', ∑ θ : ι → ZMod N,
          (((w a : ℂ) * conj (ZMod.stdAddChar (θ a))) * ((w d : ℂ) * ZMod.stdAddChar (θ d)) * M a d)
            * conj (((w a' : ℂ) * conj (ZMod.stdAddChar (θ a')))
              * ((w c' : ℂ) * ZMod.stdAddChar (θ c')) * M a' c') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a, ∑ a', ∑ d, ∑ c',
          ((w a : ℂ) * (w d : ℂ) * (w a' : ℂ) * (w c' : ℂ)) * (M a d * conj (M a' c'))
            * (if ((d = a ∧ a' = c') ∨ (d = c' ∧ a' = a))
                then (N : ℂ) ^ Fintype.card ι else 0) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c' _ => ?_
        exact hquad a d a' c'
    _ = (N : ℂ) ^ Fintype.card ι * ∑ a, ∑ a', ∑ d, ∑ c',
          (if ((d = a ∧ a' = c') ∨ (d = c' ∧ a' = a))
            then ((w a : ℂ) * (w d : ℂ) * (w a' : ℂ) * (w c' : ℂ)) * (M a d * conj (M a' c'))
            else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c' _ => ?_
        split_ifs <;> ring
    _ = (N : ℂ) ^ Fintype.card ι
          * ((∑ a, ∑ a',
                ((w a : ℂ) * (w a : ℂ) * (w a' : ℂ) * (w a' : ℂ)) * (M a a * conj (M a' a')))
            + (∑ a, ∑ d,
                ((w a : ℂ) * (w d : ℂ) * (w a : ℂ) * (w d : ℂ)) * (M a d * conj (M a d)))
            - ∑ a, ((w a : ℂ) * (w a : ℂ) * (w a : ℂ) * (w a : ℂ)) * (M a a * conj (M a a))) := by
        congr 1
        simp only [hIE ((_ = _) ∧ (_ = _)) ((_ = _) ∧ (_ = _))]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        rw [collapseP (fun a a' d c' => ((w a : ℂ) * (w d : ℂ) * (w a' : ℂ) * (w c' : ℂ))
              * (M a d * conj (M a' c'))),
          collapseQ (fun a a' d c' => ((w a : ℂ) * (w d : ℂ) * (w a' : ℂ) * (w c' : ℂ))
              * (M a d * conj (M a' c'))),
          collapsePQ (fun a a' d c' => ((w a : ℂ) * (w d : ℂ) * (w a' : ℂ) * (w c' : ℂ))
              * (M a d * conj (M a' c')))]
    _ = ((N : ℝ) ^ Fintype.card ι
          * (‖∑ a, ((w a ^ 2 : ℝ) : ℂ) * M a a‖ ^ 2
            + ∑ d, ∑ a ∈ Finset.univ.erase d, (w a ^ 2 * w d ^ 2) * ‖M a d‖ ^ 2) : ℝ) := by
        rw [hSP, add_sub_assoc, hSQPQ]
        push_cast
        ring

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]

/-- **The phase-twirl state.** For an orthonormal (eigen)basis `b`, a probability vector `p`, a
modulus `N`, and a phase vector `θ : ι → ZMod N`, this is the unit vector
`ψ_θ = Σₐ √pₐ · stdAddChar (θₐ) · bₐ = Σₐ √pₐ e^{2πi θₐ/N} |bₐ⟩` in the support of
`ρ = Σₐ pₐ |bₐ⟩⟨bₐ|`. Averaging its pure-state fidelities over `θ` is the phase-diagonal twirl of
Nielsen & Chuang's *Problem 9.3*. -/
noncomputable def phaseTwirlState (b : OrthonormalBasis ι ℂ H) (p : ι → ℝ) (N : ℕ) [NeZero N]
    (θ : ι → ZMod N) : H :=
  ∑ a, ((Real.sqrt (p a) : ℂ) * ZMod.stdAddChar (θ a)) • b a

omit [FiniteDimensional ℂ H] [CompleteSpace H] [DecidableEq ι] [Fintype κ] in
/-- **The matrix elements of an operation element in the phase-twirl state.**
`⟨ψ_θ, Eⱼ ψ_θ⟩ = Σₐ Σ_d √pₐ conj(e^{2πiθₐ/N}) · √p_d e^{2πiθ_d/N} · ⟨bₐ, Eⱼ b_d⟩`. Just the
sesquilinearity of the inner product applied to the definition of `phaseTwirlState`. -/
theorem inner_phaseTwirlState (b : OrthonormalBasis ι ℂ H) (p : ι → ℝ) (N : ℕ) [NeZero N]
    (E : κ → H →L[ℂ] H) (θ : ι → ZMod N) (j : κ) :
    inner ℂ (phaseTwirlState b p N θ) (E j (phaseTwirlState b p N θ))
      = ∑ a, ∑ d, ((Real.sqrt (p a) : ℂ) * conj (ZMod.stdAddChar (θ a)))
          * ((Real.sqrt (p d) : ℂ) * ZMod.stdAddChar (θ d)) * inner ℂ (b a) (E j (b d)) := by
  have hE : E j (phaseTwirlState b p N θ)
      = ∑ d, ((Real.sqrt (p d) : ℂ) * ZMod.stdAddChar (θ d)) • E j (b d) := by
    rw [phaseTwirlState, map_sum]; simp only [map_smul]
  rw [hE, phaseTwirlState, sum_inner]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [inner_smul_right, map_mul, Complex.conj_ofReal]
  ring

omit [CompleteSpace H] in
/-- **The phase-twirl average identity.** Averaging the pure-state fidelities `∑ⱼ |⟨ψ_θ, Eⱼ ψ_θ⟩|²`
of the phase-twirl states `ψ_θ` over the phase group `(ZMod N)^ι` (`N ≥ 3`) returns exactly `Nᶜ`
(`c = card ι`) times the entanglement fidelity of `ρ = Σₐ pₐ |bₐ⟩⟨bₐ|` plus its off-diagonal
coherence:
`∑_θ ∑ⱼ |⟨ψ_θ, Eⱼ ψ_θ⟩|² = Nᶜ · (F(ρ, E) + S_off)`
(Nielsen & Chuang, *Problem 9.3*, fact (5)). The `θ`-average kills the cross terms carrying a
nontrivial phase, leaving the diagonal square (which reassembles `F(ρ, E)` via
`entanglementFidelity_sum_rankOne`) and the off-diagonal weight `offDiagCoherenceSum`. The
combinatorial engine is `sum_char_twirl_normSq`, applied per operation element `Eⱼ` with amplitudes
`√pₐ` and matrix elements `⟨bₐ, Eⱼ b_d⟩`; `√pₐ² = pₐ` uses `0 ≤ pₐ`. -/
theorem sum_phaseTwirl_normSq_inner_eq (b : OrthonormalBasis ι ℂ H) (p : ι → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (N : ℕ) [NeZero N] (hN : 3 ≤ N) (E : κ → H →L[ℂ] H) :
    ∑ θ : ι → ZMod N,
        ∑ j, ‖inner ℂ (phaseTwirlState b p N θ) (E j (phaseTwirlState b p N θ))‖ ^ 2
      = (N : ℝ) ^ Fintype.card ι
        * (entanglementFidelity (∑ a, (p a : ℂ) • rankOne ℂ (b a) (b a)) E
          + offDiagCoherenceSum (⇑b) p E) := by
  rw [Finset.sum_comm]
  have hj : ∀ j,
      (∑ θ : ι → ZMod N, ‖inner ℂ (phaseTwirlState b p N θ) (E j (phaseTwirlState b p N θ))‖ ^ 2)
        = (N : ℝ) ^ Fintype.card ι
          * (‖∑ a, (p a : ℂ) * inner ℂ (b a) (E j (b a))‖ ^ 2
            + ∑ d, ∑ a ∈ Finset.univ.erase d,
                (p a * p d) * ‖inner ℂ (b a) (E j (b d))‖ ^ 2) := by
    intro j
    simp_rw [inner_phaseTwirlState b p N E _ j]
    rw [sum_char_twirl_normSq hN (fun a => Real.sqrt (p a))
      (fun a d => inner ℂ (b a) (E j (b d)))]
    simp_rw [Real.sq_sqrt (hp0 _)]
  simp_rw [hj]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [entanglementFidelity_sum_rankOne]
  · rw [offDiagCoherenceSum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]

omit [CompleteSpace H] in
/-- **The phase-diagonal-twirl reduction of the entanglement infidelity.** If every phase-twirl
state `ψ_θ` (a unit vector in the support of `ρ = Σₐ pₐ |bₐ⟩⟨bₐ|`) has pure-state fidelity at least
`1 − η` under the operation elements `E`, i.e. `1 − η ≤ ∑ⱼ |⟨ψ_θ, Eⱼ ψ_θ⟩|²` for all `θ`, then the
entanglement infidelity is bounded by `η` plus the off-diagonal coherence:
`1 − F(ρ, E) ≤ η + S_off`  (Nielsen & Chuang, *Problem 9.3*, fact (5)).

Averaging the hypothesis over the `Nᶜ` phase vectors and using the twirl identity
`sum_phaseTwirl_normSq_inner_eq` gives `1 − η ≤ F(ρ, E) + S_off`, which rearranges to the claim. The
count `Fintype.card (ι → ZMod N) = Nᶜ` (`Fintype.card_fun`, `ZMod.card`) cancels since it is
positive. Combined with `offDiagCoherenceSum_le` (`S_off ≤ η/2`) this is fact (5)'s
`F(ρ, E) ≥ 1 − 3η/2`. -/
theorem one_sub_entanglementFidelity_le_offDiagCoherenceSum (b : OrthonormalBasis ι ℂ H)
    (p : ι → ℝ) (hp0 : ∀ a, 0 ≤ p a) (N : ℕ) [NeZero N] (hN : 3 ≤ N) (E : κ → H →L[ℂ] H) {η : ℝ}
    (hfid : ∀ θ : ι → ZMod N,
      1 - η ≤ ∑ j, ‖inner ℂ (phaseTwirlState b p N θ) (E j (phaseTwirlState b p N θ))‖ ^ 2) :
    1 - entanglementFidelity (∑ a, (p a : ℂ) • rankOne ℂ (b a) (b a)) E
      ≤ η + offDiagCoherenceSum (⇑b) p E := by
  have hcard : (Fintype.card (ι → ZMod N) : ℝ) = (N : ℝ) ^ Fintype.card ι := by
    rw [Fintype.card_fun, ZMod.card]; push_cast; ring
  have hpos : (0 : ℝ) < (N : ℝ) ^ Fintype.card ι := by positivity
  have hle : ∑ θ : ι → ZMod N, (1 - η)
      ≤ ∑ θ : ι → ZMod N,
          ∑ j, ‖inner ℂ (phaseTwirlState b p N θ) (E j (phaseTwirlState b p N θ))‖ ^ 2 :=
    Finset.sum_le_sum fun θ _ => hfid θ
  rw [sum_phaseTwirl_normSq_inner_eq b p hp0 N hN E, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hcard] at hle
  have := le_of_mul_le_mul_left hle hpos
  linarith

end ContinuousLinearMap
