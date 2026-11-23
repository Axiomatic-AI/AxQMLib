/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerCodeProjector
import AxQM.Concrete.StabilizerCodeDimension
import ToMathlib.GroupTheory.Subgroup.Centralizer
import ToMathlib.Analysis.InnerProductSpace.QuantumErrorCorrection
import ToMathlib.Analysis.CStarAlgebra.Matrix

/-!
# Concrete: error-correction conditions for stabilizer codes (Nielsen & Chuang, Theorem 10.8)

This file completes the formalisation of Nielsen & Chuang **Theorem 10.8** (the *error-correction
conditions for stabilizer codes*, p. 466) begun in `AxQM/Concrete/StabilizerCodeProjector.lean`.
Everything here is stated for the abstract Pauli group `PauliGroup n`, its subgroups, and raw
matrices / operators.

## The theorem

Stabilizer QEC conditions: {Ej} with Ej-dag Ek not in N(S)-S for all j,k is a correctable error set
for C(S).

N&C's proof shows the projector `P` onto `C(S)` and the errors satisfy the **Knill–Laflamme /
quantum error-correction conditions** of Theorem 10.1 (eq. (10.16)): `P Eⱼ† Eₖ P = αⱼₖ P` for a
Hermitian matrix `α`; then, since `C(S)` is a code (`P ≠ 0`, which is exactly what the stabilizer
hypothesis `-I ∉ S` guarantees), Theorem 10.1's sufficiency direction produces a recovery operation
correcting `{Eⱼ}`. Both halves are proved here.

Errors are modelled as elements `E : ι → PauliGroup n` of the Pauli group `Gₙ` (N&C: "operators in
`Gₙ`"). For group elements the adjoint is the inverse (`PauliGroup.toMat_inv`:
`(toMat p)ᴴ = toMat p⁻¹`), so `Eⱼ† Eₖ` is the operator of the single group element `Eⱼ⁻¹ Eₖ`, and
the hypothesis `Eⱼ† Eₖ ∉ N(S) − S` reads `¬ (Eⱼ⁻¹ Eₖ ∈ N(S) ∧ Eⱼ⁻¹ Eₖ ∉ S)` (i.e.
`Eⱼ⁻¹ Eₖ ∉ N(S) \ S`) with `N(S)` the group-theoretic normalizer `Subgroup.normalizer S`.

## What is proved

* `codeProjector_conj_toMat_eq_self` / `codeProjector_conj_toMat_eq_zero` — the two cases of N&C's
  proof: `p ∈ S ⟹ P (toMat p) P = P` (absorption + idempotence) and, when `p` anticommutes with
  some `g ∈ S`, `P (toMat p) P = 0` (`P = P·toMat g`, `toMat p · toMat g = -(toMat g · toMat p)`,
  `toMat g · P = P` force `P (toMat p) P = -(P (toMat p) P)`, hence `0`).
* `codeProjector_conj_toMat` — the two cases assembled: for `p ∉ N(S) \ S`,
  `P (toMat p) P = 1_S(p) • P` (`1_S` the indicator of `S`), using the operator commute/anticommute
  dichotomy (`PauliGroup.toMat_anticomm_of_ne_mul_comm`) and `Subgroup.centralizer_le_normalizer`.
* `stabilizerKLCoeff` / `stabilizerKLCoeff_isHermitian` — the Hermitian coefficient matrix
  `αⱼₖ = 1_S(Eⱼ⁻¹ Eₖ)` (`S` closed under inverse; `(Eⱼ⁻¹ Eₖ)⁻¹ = Eₖ⁻¹ Eⱼ`).
* `codeProjector_satisfiesKL` — the Knill–Laflamme conditions `P Eⱼ† Eₖ P = αⱼₖ P` (N&C eq. (10.16))
  at the matrix level, holding for **any** finite stabilizer subgroup (no `-I ∉ S` needed).
* `codeProjector_satisfiesKLConditions` — the same, transported through the `*`-algebra isomorphism
  `Matrix.toEuclideanCLM` into the exact predicate `ContinuousLinearMap.SatisfiesKLConditions` of
  Theorem 10.1.
* `codeProjector_ne_zero` — for a genuine stabilizer (`-I ∉ S`) the code projector is nonzero
  (`tr P = |S|⁻¹ · 2ⁿ ≠ 0`, as the only stabilizer element with a nonzero-trace operator is `I`).
* `codeProjector_isCorrectableErrorSet` — **Theorem 10.8**: for `-I ∉ S` and `Eⱼ⁻¹ Eₖ ∉ N(S) \ S`,
  a trace-preserving recovery `R` (`∑ₒ Rₒ† Rₒ = 1`) corrects `{Eⱼ}`, obtained by feeding the five
  hypotheses (`IsSelfAdjoint P`, `P² = P`, `P ≠ 0`, Hermitian `α`, KL conditions) into
  `ContinuousLinearMap.corrects_of_satisfiesKLConditions`.
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The two cases of Theorem 10.8's proof -/

/-- **Case `p ∈ S`.** `P (toMat p) P = P`: `toMat p` is absorbed by `P` (`toMat_mul_codeProjector`)
and `P` is idempotent (`codeProjector_mul_self`). N&C's `P Eⱼ† Eₖ P = P` when `Eⱼ† Eₖ ∈ S`. -/
theorem codeProjector_conj_toMat_eq_self {S : Subgroup (PauliGroup n)} [Fintype S]
    {p : PauliGroup n} (hp : p ∈ S) :
    codeProjector S * p.toMat * codeProjector S = codeProjector S := by
  rw [mul_assoc, toMat_mul_codeProjector hp, codeProjector_mul_self]

/-- **Case `p` anticommutes with some `g ∈ S`.** `P (toMat p) P = 0`. Writing `a = toMat p`,
`b = toMat g`, the two-sided absorption `b · P = P = P · b` and the anticommutation `a · b =
-(b · a)` give `P · a · P = P · a · (b · P) = P · (a · b) · P = -(P · b · a · P) = -(P · a · P)`, so
`2 (P a P) = 0` and `P a P = 0`. This is N&C's `P Eⱼ† Eₖ P = 0` when `Eⱼ† Eₖ ∈ Gₙ − N(S)`
(anticommuting with a generator `g₁ ∈ S`). -/
theorem codeProjector_conj_toMat_eq_zero {S : Subgroup (PauliGroup n)} [Fintype S]
    {p g : PauliGroup n} (hg : g ∈ S)
    (hanti : p.toMat * g.toMat = -(g.toMat * p.toMat)) :
    codeProjector S * p.toMat * codeProjector S = 0 := by
  have h1 : g.toMat * codeProjector S = codeProjector S := toMat_mul_codeProjector hg
  have h2 : codeProjector S * g.toMat = codeProjector S := codeProjector_mul_toMat hg
  set P := codeProjector S
  set a := p.toMat
  set b := g.toMat
  have key : P * a * P = -(P * a * P) :=
    calc P * a * P
        = P * a * (b * P) := by rw [h1]
      _ = P * (a * b) * P := by noncomm_ring
      _ = P * (-(b * a)) * P := by rw [hanti]
      _ = -(P * b * a * P) := by noncomm_ring
      _ = -(P * a * P) := by rw [h2]
  have hsum : P * a * P + P * a * P = 0 := by
    nth_rewrite 2 [key]; exact add_neg_cancel _
  have h2x : (2 : ℂ) • (P * a * P) = 0 := by rw [two_smul]; exact hsum
  exact (smul_eq_zero.mp h2x).resolve_left two_ne_zero

/-! ### Theorem 10.8: the code projector satisfies the Knill–Laflamme conditions -/

/-- **Single-element form of Theorem 10.8.** For a Pauli-group element `p ∉ N(S) \ S` (written
`¬ (p ∈ N(S) ∧ p ∉ S)`), `P (toMat p) P = 1_S(p) • P` where `1_S` is the indicator of `S`. The
hypothesis splits into `p ∈ S` (`codeProjector_conj_toMat_eq_self`) and `p ∉ N(S)`, where — `p`
failing to commute with some `g ∈ S` (the contrapositive of `Subgroup.centralizer_le_normalizer`)
and the resulting operator anticommutation (`PauliGroup.toMat_anticomm_of_ne_mul_comm`) —
`codeProjector_conj_toMat_eq_zero` applies. -/
theorem codeProjector_conj_toMat {S : Subgroup (PauliGroup n)} [Fintype S] {p : PauliGroup n}
    (hp : ¬ (p ∈ Subgroup.normalizer S ∧ p ∉ S)) :
    codeProjector S * p.toMat * codeProjector S
      = Set.indicator (↑S) (fun _ => (1 : ℂ)) p • codeProjector S := by
  by_cases hmem : p ∈ S
  · rw [Set.indicator_of_mem (SetLike.mem_coe.2 hmem), one_smul]
    exact codeProjector_conj_toMat_eq_self hmem
  · rw [Set.indicator_of_notMem (by simpa using hmem), zero_smul]
    have hnotnorm : p ∉ Subgroup.normalizer S := fun hn => hp ⟨hn, hmem⟩
    -- `p ∉ N(S)` gives a `g ∈ S` failing to commute with `p`, hence anticommuting operators.
    obtain ⟨g, hg, hne⟩ : ∃ g ∈ S, p * g ≠ g * p := by
      by_contra hcon
      refine hnotnorm (Subgroup.centralizer_le_normalizer (S : Set (PauliGroup n)) ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      by_contra hne
      exact hcon ⟨g, hg, fun h => hne h.symm⟩
    exact codeProjector_conj_toMat_eq_zero hg (PauliGroup.toMat_anticomm_of_ne_mul_comm p g hne)

/-- The **Knill–Laflamme coefficient matrix** of a stabilizer code for an error family
`E : ι → Gₙ`: `αⱼₖ = 1_S(Eⱼ⁻¹ Eₖ)` — the indicator of `S`, i.e. `1` if `Eⱼ⁻¹ Eₖ ∈ S` and `0`
otherwise. This is N&C's `α` in eq. (10.16): `1` on the errors that differ by a stabilizer, `0` on
those that anticommute with `S`. -/
noncomputable def stabilizerKLCoeff {ι : Type*} (S : Subgroup (PauliGroup n))
    (E : ι → PauliGroup n) : Matrix ι ι ℂ :=
  fun j k => Set.indicator (↑S) (fun _ => (1 : ℂ)) ((E j)⁻¹ * E k)

/-- **The Knill–Laflamme coefficient matrix is Hermitian** (N&C requires `α` Hermitian). Its entries
are real (`0`/`1`), and `Eₖ⁻¹ Eⱼ = (Eⱼ⁻¹ Eₖ)⁻¹` lies in `S` exactly when `Eⱼ⁻¹ Eₖ` does (`S` is
closed under inverse), so `αₖⱼ = αⱼₖ`. -/
theorem stabilizerKLCoeff_isHermitian {ι : Type*} (S : Subgroup (PauliGroup n))
    (E : ι → PauliGroup n) : (stabilizerKLCoeff S E).IsHermitian := by
  ext j k
  rw [Matrix.conjTranspose_apply]
  simp only [stabilizerKLCoeff]
  have hiff : (E k)⁻¹ * E j ∈ S ↔ (E j)⁻¹ * E k ∈ S := by
    rw [← Subgroup.inv_mem_iff (x := (E j)⁻¹ * E k), _root_.mul_inv_rev, inv_inv]
  by_cases h : (E k)⁻¹ * E j ∈ S
  · rw [Set.indicator_of_mem (SetLike.mem_coe.2 h),
      Set.indicator_of_mem (SetLike.mem_coe.2 (hiff.mp h)), star_one]
  · rw [Set.indicator_of_notMem (by simpa using h),
      Set.indicator_of_notMem (by simpa using (fun hc => h (hiff.mpr hc))), star_zero]

/-- The **Knill–Laflamme conditions** for a stabilizer code (Nielsen & Chuang, Theorem 10.8, eq.
(10.16)). For Pauli errors `E : ι → Gₙ` with `Eⱼ⁻¹ Eₖ ∉ N(S) \ S` — N&C's `Eⱼ† Eₖ ∉ N(S) − S`,
since `(toMat Eⱼ)ᴴ = toMat Eⱼ⁻¹` (`PauliGroup.toMat_inv`) — the code projector `P = codeProjector S`
satisfies `P (toMat Eⱼ)ᴴ (toMat Eₖ) P = αⱼₖ • P` with the Hermitian `α = stabilizerKLCoeff S E`
(`stabilizerKLCoeff_isHermitian`). This is the QEC-conditions half of Theorem 10.8; it holds for any
finite stabilizer subgroup (no `-I ∉ S` needed). Each entry is `codeProjector_conj_toMat` applied to
`Eⱼ⁻¹ Eₖ` (using `(toMat Eⱼ)ᴴ · toMat Eₖ = toMat (Eⱼ⁻¹ Eₖ)`). -/
theorem codeProjector_satisfiesKL {ι : Type*} {S : Subgroup (PauliGroup n)} [Fintype S]
    (E : ι → PauliGroup n)
    (hE : ∀ j k, ¬ ((E j)⁻¹ * E k ∈ Subgroup.normalizer S ∧ (E j)⁻¹ * E k ∉ S)) (j k : ι) :
    codeProjector S * ((E j).toMat)ᴴ * (E k).toMat * codeProjector S
      = stabilizerKLCoeff S E j k • codeProjector S := by
  have hprod : ((E j).toMat)ᴴ * (E k).toMat = ((E j)⁻¹ * E k).toMat := by
    rw [PauliGroup.toMat_mul, PauliGroup.toMat_inv]
  rw [mul_assoc (codeProjector S) (((E j).toMat)ᴴ) ((E k).toMat), hprod,
    codeProjector_conj_toMat (hE j k)]
  rfl

/-- The Knill–Laflamme conditions of `codeProjector_satisfiesKL`, transported through the
`*`-algebra isomorphism `Matrix.toEuclideanCLM`
(`Matrix n n ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)`, intertwining `·ᴴ`↦`adjoint`,
`*`↦`comp`), into the exact predicate `ContinuousLinearMap.SatisfiesKLConditions` of Theorem 10.1:
the code projector `P` and the errors `E` — as continuous linear maps on the qubit Hilbert space —
satisfy `SatisfiesKLConditions` with the Hermitian coefficient matrix `stabilizerKLCoeff S E`. This
supplies two of the five hypotheses `corrects_of_satisfiesKLConditions` needs (the fifth, `P ≠ 0`,
requires `-I ∉ S`); `codeProjector_isCorrectableErrorSet` assembles them into correctability. -/
theorem codeProjector_satisfiesKLConditions {ι : Type*} {S : Subgroup (PauliGroup n)} [Fintype S]
    (E : ι → PauliGroup n)
    (hE : ∀ j k, ¬ ((E j)⁻¹ * E k ∈ Subgroup.normalizer S ∧ (E j)⁻¹ * E k ∉ S)) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).SatisfiesKLConditions
      (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (E i).toMat)
      (stabilizerKLCoeff S E) := by
  intro i j
  have hadj := (Matrix.toEuclideanCLM_conjTranspose_eq_adjoint (𝕜 := ℂ) (n := Fin n → Fin 2)
    (E i).toMat).symm
  rw [hadj]
  simp only [← ContinuousLinearMap.mul_def, ← map_mul, ← map_smul]
  congr 1
  rw [← codeProjector_satisfiesKL E hE i j]
  noncomm_ring

/-! ### The code projector is nonzero, and `{Eⱼ}` is correctable -/

/-- **The code projector of a genuine stabilizer is nonzero.** For `S` with `-I ∉ S`,
`tr P = |S|⁻¹ · 2ⁿ ≠ 0`: expanding `tr(∑_{s∈S} toMat s)`, a summand `tr(iˢ P_a) = iˢ · [a = 0] · 2ⁿ`
is nonzero only when the string index is `0`, and the only such element of `S` is the identity `I`
(`eq_one_of_checkRowHom_eq_zero_of_negOne_notMem`, using `-I ∉ S`), contributing `tr I = 2ⁿ`; hence
`P ≠ 0`. (For `-I ∈ S` the group average is `0` — `C(S)` is trivial — so `-I ∉ S` is essential.) -/
theorem codeProjector_ne_zero {S : Subgroup (PauliGroup n)} [Fintype S]
    (hS : PauliGroup.negOne n ∉ S) :
    codeProjector S ≠ 0 := by
  have hsum : (stabilizerSum S).trace = (2 : ℂ) ^ n := by
    rw [stabilizerSum_eq, Matrix.trace_sum,
      Finset.sum_eq_single_of_mem (1 : S) (Finset.mem_univ _)]
    · rw [OneMemClass.coe_one, PauliGroup.toMat_one,
        show (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) = pauliString 0 from
          pauliString_const_zero.symm, pauliString_trace, ite_eq_left rfl]
    · intro t _ hne
      rw [PauliGroup.toMat, Matrix.trace_smul, pauliString_trace, smul_eq_mul, ite_eq_right,
          mul_zero]
      intro h0
      exact hne (Subtype.ext ((PauliGroup.eq_one_of_checkRowHom_eq_zero_of_negOne_notMem hS t.2
        ((PauliGroup.checkRowHom_eq_zero_iff _).mpr h0)).trans (OneMemClass.coe_one S).symm))
  intro hP
  have hQ : stabilizerSum S = 0 :=
    (smul_eq_zero.mp hP).resolve_left (inv_ne_zero (card_stabilizer_ne_zero S))
  rw [hQ, Matrix.trace_zero] at hsum
  exact pow_ne_zero n two_ne_zero hsum.symm

/-- **A nonzero common `+1`-eigenvector forces `-I ∉ ⟨g⟩`** (the genuine-stabilizer criterion). For
a phase-free generator family `g : Fin m → 𝔽₄ⁿ`, if the simultaneous `+1`-eigenspace
`stabilizedSubspace g` (the code space `V_S`) is nonzero, then `-I` is not in the group
`S = ⟨(0, gᵢ)⟩` generated by the corresponding phase-`+1` Pauli-group elements. `-I` is a commutator
of `Gₙ`, so it survives no abelian quotient — the argument goes through the faithful representation:
pick `v ≠ 0` fixed by every `toMat (gᵢ) = pauliString (gᵢ)`; the set `H = {p | toMat p ·ᵥ v = v}` is
a subgroup containing every generator, hence `S ≤ H`, while `toMat (-I) ·ᵥ v = -v ≠ v`. The
companion of `codeProjector_ne_zero` (`-I ∉ S ⟹ P ≠ 0`) in the reverse direction, and the reusable
engine
behind the `-I ∉ S` obligation of Theorem 10.8 for a concrete code whose code space is known nonzero
(e.g. via Proposition 10.5, `stabilizedSubspace_finrank`). -/
theorem negOne_notMem_closure_of_ne_bot {n m : ℕ} {g : Fin m → (Fin n → Fin 4)}
    (hbot : stabilizedSubspace g ≠ ⊥) :
    PauliGroup.negOne n ∉ Subgroup.closure (Set.range (fun i => (⟨0, g i⟩ : PauliGroup n))) := by
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hvfix : ∀ i, (pauliString (g i)).mulVec v = v := mem_stabilizedSubspace.mp hvmem
  -- `H = {p | toMat p ·ᵥ v = v}` is a subgroup of `Gₙ`.
  let H : Subgroup (PauliGroup n) :=
    { carrier := {p | p.toMat.mulVec v = v}
      one_mem' := by simp only [Set.mem_ofPred_eq, PauliGroup.toMat_one, Matrix.one_mulVec]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [PauliGroup.toMat_mul, ← Matrix.mulVec_mulVec, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [Matrix.mulVec_mulVec, ← PauliGroup.toMat_mul, inv_mul_cancel,
          PauliGroup.toMat_one, Matrix.one_mulVec] }
  -- every generator fixes `v`, hence `⟨(0, gᵢ)⟩ = closure (range …) ≤ H`.
  have hsub : Subgroup.closure (Set.range (fun i => (⟨0, g i⟩ : PauliGroup n))) ≤ H := by
    refine (Subgroup.closure_le H).mpr ?_
    rintro _ ⟨i, rfl⟩
    change ((⟨0, g i⟩ : PauliGroup n)).toMat.mulVec v = v
    have hg : ((⟨0, g i⟩ : PauliGroup n)).toMat = pauliString (g i) := by
      simp only [PauliGroup.toMat, zmod4Pow_zero, one_smul]
    rw [hg]; exact hvfix i
  -- if `-I` were in the group it would fix `v`, but `toMat (-I) ·ᵥ v = -v`, forcing `v = 0`.
  intro hmem
  have hfix : (PauliGroup.negOne n).toMat.mulVec v = v := hsub hmem
  have hneg : (PauliGroup.negOne n).toMat.mulVec v = -v := by
    have hz : pauliString (0 : Fin n → Fin 4) = 1 := pauliString_const_zero
    have h1 : (PauliGroup.negOne n).toMat
        = (-1 : ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
      simp only [PauliGroup.toMat, PauliGroup.negOne, zmod4Pow_two, hz]
    rw [h1, Matrix.smul_mulVec, Matrix.one_mulVec, neg_one_smul]
  rw [hneg] at hfix
  exact hvne (neg_eq_self.mp hfix)

/-- **The code projector, as a Euclidean continuous linear map, is self-adjoint.** `toEuclideanCLM`
is a `*`-algebra isomorphism intertwining `·ᴴ` with `adjoint`, and `codeProjector S` is Hermitian
(`codeProjector_isHermitian`). One of the three standing hypotheses of Theorem 10.1 that both
stabilizer correctability theorems (`codeProjector_isCorrectableErrorSet` and the below-distance
variant `codeProjector_isCorrectableErrorSet_of_weight_lt`) feed to
`corrects_of_satisfiesKLConditions`. -/
theorem isSelfAdjoint_toEuclideanCLM_codeProjector {S : Subgroup (PauliGroup n)} [Fintype S] :
    IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)) := by
  rw [isSelfAdjoint_iff, ← map_star]
  congr 1
  rw [Matrix.star_eq_conjTranspose]
  exact codeProjector_isHermitian

/-- **The code projector, as a Euclidean continuous linear map, is idempotent.** `toEuclideanCLM` is
multiplicative and `codeProjector S` is idempotent (`codeProjector_mul_self`). The projector
hypothesis `P² = P` of Theorem 10.1 shared by both stabilizer correctability theorems. -/
theorem toEuclideanCLM_codeProjector_comp_self {S : Subgroup (PauliGroup n)} [Fintype S] :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).comp
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S))
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S) := by
  rw [← ContinuousLinearMap.mul_def, ← map_mul, codeProjector_mul_self]

/-- **The code projector, as a Euclidean continuous linear map, is nonzero** for a genuine
stabilizer (`-I ∉ S`): `toEuclideanCLM` is injective and `codeProjector S ≠ 0`
(`codeProjector_ne_zero`, where
`-I ∉ S` enters). The `P ≠ 0` hypothesis of Theorem 10.1 shared by both stabilizer correctability
theorems. -/
theorem toEuclideanCLM_codeProjector_ne_zero {S : Subgroup (PauliGroup n)} [Fintype S]
    (hS : PauliGroup.negOne n ∉ S) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S) ≠ 0 := fun h =>
  codeProjector_ne_zero hS ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2)).injective
    (by rw [map_zero]; exact h))

/-- **Nielsen & Chuang, Theorem 10.8** (error-correction conditions for stabilizer codes). Let `S`
be a stabilizer (`-I ∉ S`) and `P = codeProjector S` the projector onto its code space `C(S)`. If a
family of Pauli errors `E : ι → Gₙ` satisfies `Eⱼ⁻¹ Eₖ ∉ N(S) \ S` for all `j, k` (N&C's
`Eⱼ† Eₖ ∉ N(S) − S`), then `{Eⱼ}` is a **correctable set of errors** for `C(S)`: there is a
trace-preserving recovery operation `R` (`∑ₒ Rₒ† Rₒ = 1`) that corrects `{Eⱼ}`. This is exactly the
sufficiency half of Theorem 10.1 (`ContinuousLinearMap.corrects_of_satisfiesKLConditions`), fed the
five hypotheses: `P` (as a CLM) is self-adjoint (`isSelfAdjoint_toEuclideanCLM_codeProjector`),
idempotent (`toEuclideanCLM_codeProjector_comp_self`), nonzero
(`toEuclideanCLM_codeProjector_ne_zero`, where `-I ∉ S` enters), the coefficient matrix is Hermitian
(`stabilizerKLCoeff_isHermitian`), and the KL conditions hold
(`codeProjector_satisfiesKLConditions`). -/
theorem codeProjector_isCorrectableErrorSet {ι : Type} [Fintype ι]
    {S : Subgroup (PauliGroup n)} [Fintype S] (hS : PauliGroup.negOne n ∉ S) (E : ι → PauliGroup n)
    (hE : ∀ j k, ¬ ((E j)⁻¹ * E k ∈ Subgroup.normalizer S ∧ (E j)⁻¹ * E k ∉ S)) :
    ∃ (κ : Type) (_ : Fintype κ)
      (R : κ → EuclideanSpace ℂ (Fin n → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin n → Fin 2)),
      (∑ o, (ContinuousLinearMap.adjoint (R o)).comp (R o) = 1) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (codeProjector S)).Corrects
        (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n → Fin 2) (E i).toMat) R :=
  ContinuousLinearMap.corrects_of_satisfiesKLConditions
    isSelfAdjoint_toEuclideanCLM_codeProjector toEuclideanCLM_codeProjector_comp_self
    (toEuclideanCLM_codeProjector_ne_zero hS)
    (stabilizerKLCoeff_isHermitian S E) (codeProjector_satisfiesKLConditions E hE)

end AxQM.Concrete
