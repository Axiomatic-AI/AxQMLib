/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.OperatorSumFreedom
public import ToMathlib.Analysis.InnerProductSpace.OperatorSumComposition
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.RingTheory.Idempotents

/-! # The Knill–Laflamme quantum error-correction conditions

This file develops the **Knill–Laflamme quantum error-correction conditions** (Nielsen & Chuang,
*Quantum Computation and Quantum Information*, **Theorem 10.1**) as general operator theory on a
complex inner product space `H`, alongside the operator-sum (Kraus) representation
(`ContinuousLinearMap.krausSumₗ`).

For a code with projector `P : H →L[ℂ] H` and a noise process with operation elements
`E : ι → H →L[ℂ] H`, the conditions read `P Eᵢ† Eⱼ P = αᵢⱼ P` for a matrix `α`. Following the proof
of Theorem 10.1, the first step is to *diagonalise* the conditions: since `α` is Hermitian it can
be diagonalised by a unitary `u`, and the correspondingly recombined operation elements
`Fₖ = ∑ᵢ uᵢₖ Eᵢ` are still a set of operation elements for the same operation (they induce the same
`krausSumₗ` map — N&C's use of Theorem 8.2) and satisfy the *simplified* conditions
`P Fₖ† Fₗ P = dₖₗ P` with `d` real and diagonal (N&C eqs. (10.17)–(10.18)).

## Main definitions

* `ContinuousLinearMap.SatisfiesKLConditions P E α` — the Knill–Laflamme conditions
  `P Eᵢ† Eⱼ P = αᵢⱼ P` for the code projector `P`, operation elements `E`, and coefficient matrix
  `α` (N&C eq. (10.16)).

## Main results

* `ContinuousLinearMap.SatisfiesKLConditions.recombine` — under a linear recombination
  `Fₖ = ∑ᵢ uᵢₖ Eᵢ` of the operation elements, the conditions are transported to the conjugated
  matrix `uᴴ α u` (N&C eq. (10.17)).
* `ContinuousLinearMap.krausSumₗ_recombine_col` — such a recombination by a **unitary** `u` leaves
  the operator-sum map unchanged, `krausSumₗ F = krausSumₗ E` (the `⟸` direction of N&C Theorem
  8.2, in the column-recombination form used by Theorem 10.1).
* `ContinuousLinearMap.SatisfiesKLConditions.exists_recombine_diagonal` — **the reduction to the
  simplified conditions** (N&C eq. (10.18)): if `α` is Hermitian then there is a recombination `F`
  of `E` with the same operator-sum map that satisfies the diagonalised conditions
  `SatisfiesKLConditions P F (diagonal d)` with `d` the (real) eigenvalues of `α`.
* `ContinuousLinearMap.satisfiesKLConditions_of_corrects` — **necessity** of the conditions (N&C
  eqs. (10.27)–(10.30)): a trace-preserving recovery `R` correcting `E` on the code forces
  `P Eᵢ† Eⱼ P = αᵢⱼ P` for a Hermitian `α`.
* `ContinuousLinearMap.qecSyndromeProjector` and `qecSyndromeProjector_isSelfAdjoint`,
  `qecSyndromeProjector_isStarProjection`, `qecSyndromeProjector_comp_eq_zero` — **the syndrome
  projectors** of the sufficiency construction, `Pₖ = dₖₖ⁻¹ Fₖ P Fₖ†`, shown to be
  `IsStarProjection`s (self-adjoint idempotents) onto mutually orthogonal subspaces (N&C
  eq. (10.19)).
-/

@[expose] public section

open scoped InnerProductSpace Matrix
open Finset

noncomputable section

/-- **Pointwise-proportional linear maps are globally proportional.** If two `𝕜`-linear maps
`f g : V →ₗ[𝕜] W` over a field `𝕜` satisfy `f v = c • g v` for a *per-vector* scalar `c` at every
`v`, and `g ≠ 0`, then a *single* scalar `c` works for all `v`: `∃ c, ∀ v, f v = c • g v`.

This is the linear-algebra content of Nielsen & Chuang's remark that in the necessity half of
Theorem 10.1 "the proportionality factor must be a constant `c`, not depending on `ρ`, if both
right and left hand sides are to be linear": `f` is the (linear) map `ρ ↦ (R ∘ E)(P ρ P)` and `g`
is `ρ ↦ P ρ P`. -/
theorem _root_.LinearMap.exists_forall_eq_smul_of_forall_exists_eq_smul
    {𝕜 V W : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    {f g : V →ₗ[𝕜] W} (hg : g ≠ 0) (h : ∀ v, ∃ c : 𝕜, f v = c • g v) :
    ∃ c : 𝕜, ∀ v, f v = c • g v := by
  obtain ⟨v₀, hv₀⟩ := DFunLike.ne_iff.mp hg
  simp only [LinearMap.zero_apply] at hv₀
  obtain ⟨c₀, hc₀⟩ := h v₀
  refine ⟨c₀, fun v => ?_⟩
  obtain ⟨c, hc⟩ := h v
  by_cases hgv : g v = 0
  · rw [hc, hgv, smul_zero, smul_zero]
  by_cases hdep : ∃ lam : 𝕜, g v = lam • g v₀
  · -- `g v` is a multiple `lam • g v₀`; then `w := v - lam • v₀` has `g w = 0`, so `f w = 0`,
    -- forcing `f v = lam • f v₀ = c₀ • g v`.
    obtain ⟨lam, hlam⟩ := hdep
    obtain ⟨cw, hcw⟩ := h (v - lam • v₀)
    have hgw : g (v - lam • v₀) = 0 := by rw [map_sub, map_smul, hlam, sub_self]
    have hfw : f (v - lam • v₀) = 0 := by rw [hcw, hgw, smul_zero]
    rw [map_sub, map_smul, sub_eq_zero] at hfw
    rw [hfw, hc₀, hlam, smul_smul, smul_smul, mul_comm]
  · -- `g v` and `g v₀` are independent; comparing `f (v + v₀)` two ways forces `c = c₀`.
    obtain ⟨c2, hc2⟩ := h (v + v₀)
    rw [map_add, map_add, hc, hc₀, smul_add] at hc2
    have key : (c - c2) • g v = (c2 - c₀) • g v₀ := by
      rw [sub_smul, sub_smul]; linear_combination (norm := module) hc2
    have hcc2 : c = c2 := by
      by_contra hne
      exact hdep ⟨(c - c2)⁻¹ * (c2 - c₀), by
        rw [mul_smul, ← key, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]⟩
    rw [hcc2, sub_self, zero_smul] at key
    have hc2c₀ : c2 - c₀ = 0 := by
      rcases smul_eq_zero.mp key.symm with h1 | h1
      · exact h1
      · exact absurd h1 hv₀
    rw [hc, hcc2, sub_eq_zero.mp hc2c₀]

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

/-- **The Knill–Laflamme quantum error-correction conditions** (Nielsen & Chuang, Theorem 10.1,
eq. (10.16)). For a code projector `P : H →L[ℂ] H` and a finite family of operation elements
`E : ι → H →L[ℂ] H`, the family satisfies the conditions with coefficient matrix `α` when
`P Eᵢ† Eⱼ P = αᵢⱼ P` for all `i, j`, where `Eᵢ† = adjoint (E i)`. N&C additionally require `α` to be
Hermitian; that hypothesis is supplied where it is used (e.g. `exists_recombine_diagonal`). -/
def SatisfiesKLConditions (P : H →L[ℂ] H) (E : ι → H →L[ℂ] H) (α : Matrix ι ι ℂ) : Prop :=
  ∀ i j, P ∘L adjoint (E i) ∘L E j ∘L P = α i j • P

variable {P : H →L[ℂ] H} {E F : ι → H →L[ℂ] H} {α : Matrix ι ι ℂ} {d : ι → ℝ}

omit [Fintype ι] in
/-- **Unfolding lemma for the Knill–Laflamme conditions.** `SatisfiesKLConditions P E α` is by
definition the family of identities `P Eᵢ† Eⱼ P = αᵢⱼ P`; this `iff` exposes that content as the
API for using the predicate (rather than unfolding the `def`). -/
theorem satisfiesKLConditions_iff :
    SatisfiesKLConditions P E α ↔ ∀ i j, P ∘L adjoint (E i) ∘L E j ∘L P = α i j • P := Iff.rfl

omit [Fintype ι] in
/-- **The Knill–Laflamme conditions from the codewords and their error images** — the
direct-verification route (Nielsen & Chuang, Exercises 10.7–10.10). Let `v : κ → H` be a family of
codewords and `P = ∑ₐ |vₐ⟩⟨vₐ|` the projector onto their span (`∑ a, rankOne ℂ (v a) (v a)`; for an
orthonormal `v` this is the genuine code projector). If the errors' matrix elements between
codewords depend only on the error indices and are diagonal in the codewords,
`⟪Eᵢ vₐ, Eⱼ v_b⟫ = αᵢⱼ · δ_{a,b}`, then `P` satisfies the Knill–Laflamme conditions
`P Eᵢ† Eⱼ P = αᵢⱼ P` with coefficient matrix `α`. This packages the standard "verify the conditions
on the codeword basis" computation:
`P Eᵢ† Eⱼ P = ∑_{a,b} ⟪Eᵢ vₐ, Eⱼ v_b⟫ |vₐ⟩⟨v_b| = ∑ₐ αᵢⱼ |vₐ⟩⟨vₐ| = αᵢⱼ P`.
No orthonormality of `v` is needed for the algebraic identity itself. -/
theorem satisfiesKLConditions_of_inner_error_images {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : κ → H) (E : ι → H →L[ℂ] H) (α : Matrix ι ι ℂ)
    (h : ∀ (i j : ι) (a b : κ),
      ⟪E i (v a), E j (v b)⟫_ℂ = α i j * (if a = b then (1 : ℂ) else 0)) :
    SatisfiesKLConditions (∑ a, InnerProductSpace.rankOne ℂ (v a) (v a)) E α := by
  rw [satisfiesKLConditions_iff]
  intro i j
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [comp_apply, smul_apply, _root_.sum_apply, InnerProductSpace.rankOne_apply, map_sum,
    map_smul, adjoint_inner_right, h, mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun x _ => (smul_comm _ _ _)

/-- **Recombination of the operation elements transports the Knill–Laflamme conditions to the
conjugated matrix** (Nielsen & Chuang, Theorem 10.1, eq. (10.17)). If `E` satisfies the conditions
with matrix `α`, then the recombined family `Fₖ = ∑ᵢ uᵢₖ Eᵢ` (column `k` of `u`) satisfies them with
the conjugated matrix `uᴴ α u`. The recombination `u : Matrix ι κ ℂ` may also *change the index
type* (`κ ≠ ι`, e.g. producing more members than `E`): this is Nielsen & Chuang's discretization
principle at the level of the error-correction *conditions* — an error set whose members are linear
combinations of a correctable error set is itself correctable, whatever its size. No unitarity of
`u` is needed for this algebraic identity. -/
theorem SatisfiesKLConditions.recombine {κ : Type*}
    (hE : SatisfiesKLConditions P E α) (u : Matrix ι κ ℂ) :
    SatisfiesKLConditions P (fun k => ∑ i, u i k • E i) (uᴴ * α * u) := by
  have hE' := satisfiesKLConditions_iff.1 hE
  intro k l
  simp only [map_sum, map_smulₛₗ, finsetSum_comp, comp_finsetSum, smul_comp, comp_smul,
    Finset.smul_sum, smul_smul, hE', ← Finset.sum_smul]
  congr 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, starRingEnd_apply,
    mul_comm, mul_left_comm]

/-- **Unitary recombination of the operation elements preserves the operator-sum map**, in the
column form `Fₖ = ∑ᵢ uᵢₖ Eᵢ` used by Nielsen & Chuang, Theorem 10.1 (the `⟸` direction of Theorem
8.2). If `u` is unitary then `krausSumₗ F = krausSumₗ E`. -/
theorem krausSumₗ_recombine_col [DecidableEq ι] {u : Matrix ι ι ℂ}
    (hu : u ∈ Matrix.unitaryGroup ι ℂ) {F : ι → H →L[ℂ] H} (hF : ∀ k, F k = ∑ i, u i k • E i) :
    krausSumₗ F = krausSumₗ E := by
  have hut : uᵀ ∈ Matrix.unitaryGroup ι ℂ := Matrix.transpose_mem_unitaryGroup_iff.2 hu
  refine krausSumₗ_eq_of_mem_unitaryGroup hut (fun k => ?_)
  simp only [hF, Matrix.transpose_apply]

/-- **Reduction of the Knill–Laflamme conditions to the diagonalised (simplified) conditions**
(Nielsen & Chuang, Theorem 10.1, eqs. (10.17)–(10.18)). If the operation elements `E` satisfy the
conditions with a **Hermitian** matrix `α`, there is a recombination `F` of `E` that

* induces the same operator-sum map, `krausSumₗ F = krausSumₗ E` (so `F` is another set of operation
  elements for the same operation), and
* satisfies the *diagonalised* conditions `SatisfiesKLConditions P F (diagonal d)` with
  `d = RCLike.ofReal ∘ hα.eigenvalues` the (real) eigenvalues of `α`.

The recombination is `Fₖ = ∑ᵢ uᵢₖ Eᵢ` with `u = hα.eigenvectorUnitary` the unitary of eigenvectors;
`uᴴ α u = diagonal d` is the matrix spectral theorem
(`Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary`). -/
theorem SatisfiesKLConditions.exists_recombine_diagonal [DecidableEq ι]
    (hE : SatisfiesKLConditions P E α) (hα : α.IsHermitian) :
    ∃ F : ι → H →L[ℂ] H, krausSumₗ F = krausSumₗ E ∧
      SatisfiesKLConditions P F (Matrix.diagonal (RCLike.ofReal ∘ hα.eigenvalues)) := by
  set U : Matrix ι ι ℂ := ↑hα.eigenvectorUnitary with hU
  have hUmem : U ∈ Matrix.unitaryGroup ι ℂ := by rw [hU]; exact hα.eigenvectorUnitary.2
  have hdiag : Uᴴ * α * U = Matrix.diagonal (RCLike.ofReal ∘ hα.eigenvalues) := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, ← hU] using hα.conjStarAlgAut_star_eigenvectorUnitary
  refine ⟨fun k => ∑ i, U i k • E i, krausSumₗ_recombine_col hUmem (fun _ => rfl), ?_⟩
  rw [← hdiag]
  exact hE.recombine U

/-- **A recovery operation `R` corrects the errors `E` on the code with projector `P`** (Nielsen &
Chuang, Theorem 10.1, eq. (10.15)). The combined noise-then-recovery operation
`ρ ↦ (R ∘ E)(ρ) = krausSumₗ R (krausSumₗ E ρ)` returns every operator `ρ` supported on the code
(`P ρ P = ρ`) to a scalar multiple of itself. The scalar is allowed to depend on `ρ` (`∝`, N&C's
eq. (10.15)); that it is in fact a single nonnegative real constant is *derived*, not assumed
(`Corrects.exists_nonneg_forall_eq_smul`). -/
def Corrects (P : H →L[ℂ] H) (E : ι → H →L[ℂ] H) {κ : Type*} [Fintype κ]
    (R : κ → H →L[ℂ] H) : Prop :=
  ∀ ρ : H →L[ℂ] H, P ∘L ρ ∘L P = ρ → ∃ c : ℂ, krausSumₗ R (krausSumₗ E ρ) = c • ρ

omit [CompleteSpace H] in
/-- **A real scalar multiple of a nonzero orthogonal projection that is positive has a nonnegative
scalar.** If `P ∘L P = P`, `P ≠ 0`, and `(c : ℂ) • P` is a positive operator for a real `c`, then
`0 ≤ c`. Evaluating the positivity `0 ≤ re ⟪(c • P) x, x⟫` at a code vector `x = P y ≠ 0` gives
`0 ≤ c ‖P y‖²`, and `‖P y‖² > 0`. This packages the nonnegativity argument shared by the two places
in Theorem 10.1 where a positive `c • P` fixes the sign of `c`: the necessity constant
(`Corrects.exists_nonneg_forall_eq_smul`) and the diagonalised Knill–Laflamme coefficients
(`qecSyndromeProjector_diagonal_nonneg`). -/
theorem nonneg_of_smul_isPositive {P : H →L[ℂ] H} (hPidem : P ∘L P = P) (hP0 : P ≠ 0) {c : ℝ}
    (hpos : ((c : ℂ) • P).IsPositive) : 0 ≤ c := by
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hP0
  rw [_root_.zero_apply] at hy
  have hPv : P (P y) = P y := by rw [← ContinuousLinearMap.comp_apply, hPidem]
  have hnn := hpos.re_inner_nonneg_left (P y)
  rw [_root_.smul_apply, hPv, inner_smul_left, Complex.conj_ofReal] at hnn
  set w := inner ℂ (P y) (P y) with hw
  have hii_re : w.re = ‖P y‖ ^ 2 := by rw [hw]; simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (P y)
  have hii_im : w.im = 0 := Complex.conj_eq_iff_im.mp (inner_conj_symm (P y) (P y))
  rw [show RCLike.re ((c : ℂ) * w) = (c : ℂ).re * w.re - (c : ℂ).im * w.im from Complex.mul_re _ w,
    Complex.ofReal_re, Complex.ofReal_im, hii_re, hii_im, zero_mul, sub_zero] at hnn
  exact (mul_nonneg_iff_of_pos_right (pow_pos (norm_pos_iff.mpr hy) 2)).mp hnn

/-- **The proportionality constant in the correction condition is a single nonnegative real**
(the first step of the necessity half of Nielsen & Chuang, Theorem 10.1; N&C's remark following
eq. (10.27) that "the proportionality factor must be a constant `c`, not depending on `ρ`, if both
right and left hand sides are to be linear", together with eq. (10.28)). If `P` is a nonzero
orthogonal projection and `R` corrects `E` on the code, then there is one nonnegative real `c` with
`(R ∘ E)(P σ P) = c • (P σ P)` for *every* operator `σ` — the operator-form of N&C eq. (10.28).

The uniformity is `LinearMap.exists_forall_eq_smul_of_forall_exists_eq_smul` applied to the linear
maps `σ ↦ (R ∘ E)(P σ P)` and `σ ↦ P σ P`; the nonnegativity is because `(R ∘ E)(P) = c • P` is a
positive operator (`krausSumₗ` preserves positivity) and `P` is a nonzero projection. -/
theorem Corrects.exists_nonneg_forall_eq_smul {P : H →L[ℂ] H} {E : ι → H →L[ℂ] H}
    {κ : Type*} [Fintype κ] {R : κ → H →L[ℂ] H}
    (hP : IsSelfAdjoint P) (hPidem : P ∘L P = P) (hP0 : P ≠ 0) (hcorr : Corrects P E R) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ σ : H →L[ℂ] H,
      krausSumₗ R (krausSumₗ E (P ∘L σ ∘L P)) = (c : ℂ) • (P ∘L σ ∘L P) := by
  have hPadj : adjoint P = P := by rw [← star_eq_adjoint]; exact hP
  have hPv : ∀ y, P (P y) = P y := fun y => by rw [← comp_apply, hPidem]
  -- `g σ = P σ P`, `f σ = (R ∘ E)(P σ P)`, both `ℂ`-linear in `σ`.
  set g : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) := krausSumₗ (fun _ : Fin 1 => P) with hg_def
  have hg_apply : ∀ ρ, g ρ = P ∘L ρ ∘L P := fun ρ => by
    rw [hg_def, krausSumₗ_apply, Fintype.sum_unique, hPadj]
  set f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
    (krausSumₗ R).comp ((krausSumₗ E).comp g) with hf_def
  have hf_apply : ∀ ρ, f ρ = krausSumₗ R (krausSumₗ E (P ∘L ρ ∘L P)) := fun ρ => by
    rw [hf_def, LinearMap.comp_apply, LinearMap.comp_apply, hg_apply]
  have hfix : ∀ ρ : H →L[ℂ] H, P ∘L (P ∘L ρ ∘L P) ∘L P = P ∘L ρ ∘L P := fun ρ => by
    ext x; simp only [comp_apply, hPv]
  -- pointwise proportionality from `Corrects`, uniformised.
  have hpt : ∀ ρ, ∃ c : ℂ, f ρ = c • g ρ := fun ρ => by
    obtain ⟨c, hc⟩ := hcorr (P ∘L ρ ∘L P) (hfix ρ)
    exact ⟨c, by rw [hf_apply, hg_apply, hc]⟩
  have hg_ne : g ≠ 0 := by
    intro h0
    apply hP0
    have hgP := hg_apply P
    rw [h0, LinearMap.zero_apply, hPidem, hPidem] at hgP
    exact hgP.symm
  obtain ⟨c, hc⟩ := LinearMap.exists_forall_eq_smul_of_forall_exists_eq_smul hg_ne hpt
  -- `(R ∘ E)(P) = c • P` is positive, forcing `c` to be a nonnegative real.
  have hPpos : P.IsPositive := by
    have := isPositive_adjoint_comp_self P; rwa [hPadj, hPidem] at this
  have hcP : krausSumₗ R (krausSumₗ E P) = c • P := by
    have h1 := hc P
    rw [hf_apply, hg_apply] at h1
    rwa [show P ∘L P ∘L P = P by rw [hPidem, hPidem]] at h1
  have hcPpos : ((c : ℂ) • P).IsPositive :=
    hcP ▸ krausSumₗ_isPositive R (krausSumₗ_isPositive E hPpos)
  -- `c` is real (from self-adjointness of `c • P`).
  have hreal : star c = c := by
    have hsa : star ((c : ℂ) • P) = (c : ℂ) • P := hcPpos.isSelfAdjoint
    rw [star_smul, hP] at hsa
    have h2 : (star c - c) • P = 0 := by rw [sub_smul, hsa, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hP0
  obtain ⟨cr, hcr⟩ : ∃ cr : ℝ, (cr : ℂ) = c := ⟨c.re, Complex.conj_eq_iff_re.mp hreal⟩
  -- nonnegativity: `cr • P = c • P` is positive, so `0 ≤ cr` (`nonneg_of_smul_isPositive`).
  refine ⟨cr, nonneg_of_smul_isPositive hPidem hP0 (by rw [hcr]; exact hcPpos), fun σ => ?_⟩
  rw [← hf_apply σ, hc σ, hg_apply σ, hcr]

/-- **Single-operation-element rigidity of the operator-sum representation** (the special case of
Nielsen & Chuang, Theorem 8.2, used in the necessity half of Theorem 10.1). If a finite family
`A : J → H →L[ℂ] H` induces the *same* operator-sum map as a **single** operation element `M`, i.e.
`∑ⱼ Aⱼ σ Aⱼ† = M σ M†` for every `σ`, then each `Aⱼ` is a scalar multiple of `M`: there are scalars
`c : J → ℂ` with `Aⱼ = cⱼ • M`.

This is `krausSumₗ_eq_iff_exists_mem_unitaryGroup` (Theorem 8.2) applied to `A` and the family that
is `M` at one padding index `j₀` and `0` elsewhere; the `j₀`-th column of the resulting unitary
matrix supplies the scalars. (N&C's "the quantum operation with operation elements `{RⱼEᵢ}` is
identical to the quantum operation with a single operation element `√c P`.") -/
theorem exists_forall_eq_smul_of_krausSumₗ_apply_eq [FiniteDimensional ℂ H] {J : Type*} [Fintype J]
    [Nonempty J] {A : J → H →L[ℂ] H} {M : H →L[ℂ] H}
    (h : ∀ σ : H →L[ℂ] H, krausSumₗ A σ = M ∘L σ ∘L adjoint M) :
    ∃ c : J → ℂ, ∀ j, A j = c j • M := by
  classical
  obtain ⟨j₀⟩ := (inferInstance : Nonempty J)
  set B : J → H →L[ℂ] H := Function.update (fun _ => 0) j₀ M with hB
  have hBj₀ : B j₀ = M := by rw [hB, Function.update_self]
  have hBne : ∀ q, q ≠ j₀ → B q = 0 := fun q hq => by rw [hB, Function.update_of_ne hq]
  have hAB : krausSumₗ A = krausSumₗ B := by
    ext σ
    rw [h σ, krausSumₗ_apply,
      Fintype.sum_eq_single j₀ (fun q hq => by rw [hBne q hq]; simp), hBj₀]
  rw [krausSumₗ_eq_iff_exists_mem_unitaryGroup] at hAB
  obtain ⟨u, -, hu⟩ := hAB
  refine ⟨fun j => u j j₀, fun j => ?_⟩
  rw [hu j, Fintype.sum_eq_single j₀ (fun q hq => by rw [hBne q hq, smul_zero]), hBj₀]

/-- **Necessity of the Knill–Laflamme quantum error-correction conditions** (Nielsen & Chuang,
Theorem 10.1, the `⟹` direction). If `P` is a nonzero orthogonal projection onto the code, `R` is a
**trace-preserving** recovery operation (`∑ₖ Rₖ† Rₖ = 1`) that corrects the errors `E` on the code
(`Corrects P E R`), then the errors satisfy the Knill–Laflamme conditions `P Eᵢ† Eⱼ P = αᵢⱼ P` for a
**Hermitian** matrix `α`.

Following N&C's proof:
* `Corrects.exists_nonneg_forall_eq_smul` (necessity part 1) gives a single nonnegative real `c`
  with `(R ∘ E)(P σ P) = c • (P σ P)` for all `σ` (N&C eqs. (10.27)–(10.28));
* rewriting the combined map as the operator-sum map of the family `Fₖᵢ = Rₖ Eᵢ P` (via
  `krausSumₗ_comp`), this says `Fₖᵢ` has the same operator-sum map as the single element `√c P`, so
  `exists_forall_eq_smul_of_krausSumₗ_apply_eq` (Theorem 8.2) yields scalars with
  `Rₖ Eᵢ P = cₖᵢ P` (N&C eq. (10.29));
* taking adjoints gives `P Eᵢ† Rₖ† = c̄ₖᵢ P`, so `P Eᵢ† Rₖ† Rₖ Eⱼ P = c̄ₖᵢ cₖⱼ P`; summing over `k`
  and using `∑ₖ Rₖ† Rₖ = 1` gives `P Eᵢ† Eⱼ P = αᵢⱼ P` with `αᵢⱼ = ∑ₖ c̄ₖᵢ cₖⱼ` (N&C eq. (10.30)),
  a Gram matrix `α = cᴴ c`, hence Hermitian.

The `FiniteDimensional ℂ H` hypothesis (absent from `SatisfiesKLConditions`/`Corrects`) is genuinely
needed for the operator-sum-freedom step (Theorem 8.2); N&C works throughout in finite dimension. -/
theorem satisfiesKLConditions_of_corrects [FiniteDimensional ℂ H] {P : H →L[ℂ] H}
    {E : ι → H →L[ℂ] H} {κ : Type*} [Fintype κ] {R : κ → H →L[ℂ] H}
    (hP : IsSelfAdjoint P) (hPidem : P ∘L P = P) (hP0 : P ≠ 0)
    (hR : ∑ k, adjoint (R k) ∘L R k = 1) (hcorr : Corrects P E R) :
    ∃ α : Matrix ι ι ℂ, α.IsHermitian ∧ SatisfiesKLConditions P E α := by
  classical
  have hPadj : adjoint P = P := by rw [← star_eq_adjoint]; exact hP
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- No errors: the conditions hold vacuously.
    exact ⟨0, Matrix.isHermitian_zero, fun i => isEmptyElim i⟩
  -- `H` is nontrivial (`P ≠ 0`), so `κ` is nonempty (`∑ₖ Rₖ† Rₖ = 1 ≠ 0`).
  obtain ⟨y₀, hy₀⟩ := DFunLike.ne_iff.mp hP0
  rw [_root_.zero_apply] at hy₀
  have : Nontrivial H := nontrivial_of_ne (P y₀) 0 hy₀
  have : Nonempty κ := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have := hcon
    have hz : (1 : H →L[ℂ] H) = 0 := by rw [← hR, Finset.univ_eq_empty, Finset.sum_empty]
    exact one_ne_zero hz
  -- Necessity part 1: a single nonnegative real constant `c` (N&C eqs. (10.27)–(10.28)).
  obtain ⟨c, hc0, hc⟩ := hcorr.exists_nonneg_forall_eq_smul hP hPidem hP0
  set M : H →L[ℂ] H := (Real.sqrt c : ℂ) • P with hM
  have hMadj : adjoint M = M := by
    rw [hM, ← star_eq_adjoint, star_smul, show star P = P from hP]
    congr 1
    rw [← starRingEnd_apply, Complex.conj_ofReal]
  -- `∑ᵢ (Eᵢ P) σ (Eᵢ P)† = ∑ᵢ Eᵢ (P σ P) Eᵢ†`.
  have hE'σ : ∀ σ : H →L[ℂ] H,
      krausSumₗ (fun i => E i ∘L P) σ = krausSumₗ E (P ∘L σ ∘L P) := by
    intro σ
    rw [krausSumₗ_apply, krausSumₗ_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [adjoint_comp, hPadj]
    ext x
    simp only [ContinuousLinearMap.comp_apply]
  -- `M σ M† = c • (P σ P)`.
  have hMσ : ∀ σ : H →L[ℂ] H, M ∘L σ ∘L adjoint M = (c : ℂ) • (P ∘L σ ∘L P) := by
    intro σ
    rw [hMadj, hM]
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc0]
  -- The combined family `Fₖᵢ = Rₖ Eᵢ P` has the same operator-sum map as the single element `M`.
  have hGeq : krausSumₗ (fun p : κ × ι => R p.1 ∘L (E p.2 ∘L P))
      = krausSumₗ R ∘ₗ krausSumₗ (fun i => E i ∘L P) := (krausSumₗ_comp (fun i => E i ∘L P) R).symm
  have hGM : ∀ σ : H →L[ℂ] H,
      krausSumₗ (fun p : κ × ι => R p.1 ∘L (E p.2 ∘L P)) σ = M ∘L σ ∘L adjoint M := by
    intro σ
    rw [hGeq, LinearMap.comp_apply, hE'σ σ, hc σ, hMσ σ]
  -- Theorem 8.2 (single-element rigidity): the scalars `cₖᵢ` of N&C eq. (10.29).
  obtain ⟨cc, hcc⟩ := exists_forall_eq_smul_of_krausSumₗ_apply_eq hGM
  set d : κ → ι → ℂ := fun k i => cc (k, i) * (Real.sqrt c : ℂ) with hd_def
  have hd : ∀ k i, R k ∘L E i ∘L P = d k i • P := by
    intro k i
    rw [hd_def]
    have hki : R k ∘L (E i ∘L P) = cc (k, i) • M := hcc (k, i)
    rw [hki, hM, smul_smul]
  -- Adjoint form: `P Eᵢ† Rₖ† = c̄ₖᵢ P` (N&C eq. (10.29) adjointed).
  have hdadj : ∀ k i, P ∘L adjoint (E i) ∘L adjoint (R k) = star (d k i) • P := by
    intro k i
    have h1 := congrArg adjoint (hd k i)
    rw [adjoint_comp, adjoint_comp, hPadj,
      show adjoint (d k i • P) = star (d k i) • P by
        rw [← star_eq_adjoint, star_smul, show star P = P from hP]] at h1
    -- h1 : (P ∘L adjoint (E i)) ∘L adjoint (R k) = star (d k i) • P
    rw [← ContinuousLinearMap.comp_assoc]
    exact h1
  -- Assemble: `P Eᵢ† Eⱼ P = (∑ₖ c̄ₖᵢ cₖⱼ) P` (N&C eq. (10.30)).
  refine ⟨(Matrix.of d)ᴴ * Matrix.of d, Matrix.isHermitian_conjTranspose_mul_self _, ?_⟩
  rw [satisfiesKLConditions_iff]
  intro i j
  have hαij : ((Matrix.of d)ᴴ * Matrix.of d) i j = ∑ k, star (d k i) * d k j := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [hαij, Finset.sum_smul]
  -- Insert `1 = ∑ₖ Rₖ† Rₖ` and reduce term-by-term.
  have hsum : P ∘L adjoint (E i) ∘L E j ∘L P
      = ∑ k, (P ∘L adjoint (E i) ∘L adjoint (R k)) ∘L (R k ∘L E j ∘L P) := by
    ext x
    simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply, ← map_sum]
    congr 2
    have hone := congrArg (fun T : H →L[ℂ] H => T (E j (P x))) hR
    simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply,
      one_apply_eq_self] at hone
    exact hone.symm
  rw [hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hdadj k i, hd k j, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, hPidem]

/-! ### Sufficiency: the syndrome projectors

Given the diagonalised conditions `P Fₗ† Fₖ P = dₗₖ P` (with `d` real), Nielsen & Chuang construct
the syndrome measurement from the polar decomposition `Fₖ P = √dₖₖ Uₖ P`, whose projectors are
`Pₖ ≡ Uₖ P Uₖ†` (Theorem 10.1, following eq. (10.18)). Since `Fₖ P Fₖ† = √dₖₖ Uₖ P · √dₖₖ P Uₖ† =
dₖₖ (Uₖ P Uₖ†)`, these projectors are exactly `dₖₖ⁻¹ Fₖ P Fₖ†`, which we take as the definition:
this expresses `Pₖ` directly in terms of the (diagonalised) operation elements, so the whole
construction stays elementary and never invokes the polar-decomposition isometry `Uₖ`. -/

omit [Fintype ι] in
/-- **The syndrome blocks `Fₖ P Fₖ†` compose according to the coefficient matrix.** If `F` satisfies
the Knill–Laflamme conditions `P Fₗ† Fₖ P = αₗₖ P` with matrix `α`, then the (unnormalised) syndrome
blocks `Fₗ P Fₗ†` and `Fₖ P Fₖ†` multiply as `(Fₗ P Fₗ†)(Fₖ P Fₖ†) = αₗₖ (Fₗ P Fₖ†)` — the middle
factor `P Fₗ† Fₖ P` collapses to `αₗₖ P`. When `α` is diagonal this vanishes off the diagonal, which
is what makes the syndrome subspaces orthogonal (Nielsen & Chuang, Theorem 10.1, eq. (10.19)). -/
theorem SatisfiesKLConditions.errorBlock_comp (hF : SatisfiesKLConditions P F α) (l k : ι) :
    (F l ∘L P ∘L adjoint (F l)) ∘L (F k ∘L P ∘L adjoint (F k))
      = α l k • (F l ∘L P ∘L adjoint (F k)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply]
  have hlk := DFunLike.congr_fun (hF l k) (adjoint (F k) x)
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply] at hlk
  rw [hlk, map_smul]

/-- **The syndrome projector `Pₖ = dₖₖ⁻¹ Fₖ P Fₖ†`** of Nielsen & Chuang, Theorem 10.1. It is the
projector `Pₖ ≡ Uₖ P Uₖ†` onto the `k`-th syndrome subspace `Fₖ(C)`, written directly in terms of
the diagonalised operation elements `F` (with real diagonal `d`) instead of the polar-decomposition
isometry `Uₖ`. Under the diagonalised conditions `P Fₗ† Fₖ P = dₗₖ P` these are orthogonal
projections onto mutually orthogonal subspaces (the projectors of the syndrome measurement).

The normalisation `(d k : ℂ)⁻¹` uses the field convention `0⁻¹ = 0`, so on an index `k` with
`dₖₖ = 0` — where the error `Fₖ` annihilates the code — the projector is `0`. -/
def qecSyndromeProjector (P : H →L[ℂ] H) (F : ι → H →L[ℂ] H) (d : ι → ℝ) (k : ι) : H →L[ℂ] H :=
  ((d k : ℂ))⁻¹ • (F k ∘L P ∘L adjoint (F k))

omit [Fintype ι] in
/-- The syndrome projectors `qecSyndromeProjector P F d k` are **self-adjoint** — half of being
orthogonal projections (Nielsen & Chuang, Theorem 10.1). Needs only that the code projector `P` is
self-adjoint and the diagonal `d` is real. -/
theorem qecSyndromeProjector_isSelfAdjoint (hP : IsSelfAdjoint P) (k : ι) :
    IsSelfAdjoint (qecSyndromeProjector P F d k) := by
  -- `Fₖ P Fₖ†` is the `IsSelfAdjoint.conjugate` of `P`; scalar `dₖₖ⁻¹` via `IsSelfAdjoint.smul`.
  have hsa : IsSelfAdjoint ((d k : ℂ)⁻¹) := by
    rw [isSelfAdjoint_iff, star_inv₀, ← starRingEnd_apply, Complex.conj_ofReal]
  have h := hP.conjugate (F k)
  rw [star_eq_adjoint] at h
  simp only [qecSyndromeProjector]
  exact hsa.smul (by simpa only [mul_def, comp_assoc] using h)

omit [Fintype ι] in
/-- The syndrome projectors are **orthogonal (star) projections** — self-adjoint idempotents
(Nielsen & Chuang, Theorem 10.1). Bundled as `IsStarProjection`, so the raw self-adjoint /
idempotent facts are recovered via `.isSelfAdjoint` / `.isIdempotentElem`, and the family plugs
straight into Mathlib's orthogonal-projection API — `IsStarProjection.add` (with the orthogonality
`qecSyndromeProjector_comp_eq_zero`), `ContinuousLinearMap.IsPositive.of_isStarProjection`,
`CompleteOrthogonalIdempotents` — that the recovery-channel assembly consumes.

Idempotency is `(Fₖ P Fₖ†)(Fₖ P Fₖ†) = dₖₖ (Fₖ P Fₖ†)` (`errorBlock_comp`) together with the scalar
identity `dₖₖ⁻¹ dₖₖ⁻¹ dₖₖ = dₖₖ⁻¹` (valid also at `dₖₖ = 0` under the `0⁻¹ = 0` convention). -/
theorem qecSyndromeProjector_isStarProjection [DecidableEq ι] (hP : IsSelfAdjoint P)
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) (k : ι) :
    IsStarProjection (qecSyndromeProjector P F d k) := by
  have hs : (((d k : ℂ))⁻¹ * ((d k : ℂ))⁻¹) * (d k : ℂ) = ((d k : ℂ))⁻¹ := by
    rcases eq_or_ne (d k : ℂ) 0 with h | h
    · simp [h]
    · rw [mul_assoc, inv_mul_cancel₀ h, mul_one]
  have hidem : qecSyndromeProjector P F d k ∘L qecSyndromeProjector P F d k
      = qecSyndromeProjector P F d k := by
    simp only [qecSyndromeProjector, smul_comp, comp_smul]
    rw [hF.errorBlock_comp k k, Matrix.diagonal_apply_eq, smul_smul, smul_smul, hs]
  rw [isStarProjection_iff]
  exact ⟨hidem, qecSyndromeProjector_isSelfAdjoint hP k⟩

omit [Fintype ι] in
/-- **Orthogonality of distinct syndrome projectors**, `Pₗ Pₖ = 0` for `l ≠ k` (Nielsen & Chuang,
Theorem 10.1, eq. (10.19)): the error subspaces `Fₗ(C)` and `Fₖ(C)` are orthogonal, so the syndrome
measurement can reliably distinguish which error occurred. Immediate from the off-diagonal vanishing
`(Fₗ P Fₗ†)(Fₖ P Fₖ†) = dₗₖ (Fₗ P Fₖ†) = 0`. -/
theorem qecSyndromeProjector_comp_eq_zero [DecidableEq ι]
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) {l k : ι} (hlk : l ≠ k) :
    qecSyndromeProjector P F d l ∘L qecSyndromeProjector P F d k = 0 := by
  simp only [qecSyndromeProjector, smul_comp, comp_smul]
  rw [hF.errorBlock_comp l k, Matrix.diagonal_apply_ne _ hlk, zero_smul, smul_zero, smul_zero]

/-! ### Sufficiency: the trace-preserving recovery operation

With the syndrome projectors `Pₖ = dₖₖ⁻¹ Fₖ P Fₖ†` in hand, Nielsen & Chuang assemble the recovery
operation `R(σ) = ∑ₖ Uₖ† Pₖ σ Pₖ Uₖ` from the recovery operation elements `Rₖ = Uₖ† Pₖ`. Because
`Fₖ P = √dₖₖ Uₖ P`, one has `Rₖ = Uₖ† Pₖ = P Uₖ† = (√dₖₖ)⁻¹ P Fₖ†` — like the syndrome projectors,
this is expressible directly from the diagonalised operation elements `F`, with no
polar-decomposition isometry `Uₖ`. Here we build that recovery family and show it is a genuine
(trace-preserving) quantum operation: N&C's "augmented by an additional projector … to satisfy the
completeness relation `∑ₖ Pₖ = I`" is realised by adjoining the complementary projector
`1 - ∑ₖ Pₖ`, after which `∑ₒ Rₒ† Rₒ = 1`. That this recovery in fact *corrects* `E` on the code
(N&C eqs. (10.20)–(10.26)) is developed separately. -/

/-- **A recovery operation element `Rₖ = (√dₖₖ)⁻¹ P Fₖ†`** of the sufficiency construction (Nielsen
& Chuang, Theorem 10.1). This is N&C's `Rₖ = Uₖ† Pₖ = P Uₖ†` rewritten without the
polar-decomposition isometry `Uₖ`, using `P Fₖ† = √dₖₖ P Uₖ†`; applied after detecting syndrome `k`
it rotates the `k`-th error subspace back onto the code. The `(√dₖₖ)⁻¹` normalisation uses the field
convention `0⁻¹ = 0`, so `Rₖ = 0` on an index `k` with `dₖₖ = 0`, where the error `Fₖ` annihilates
the code. -/
def qecRecoveryElement (P : H →L[ℂ] H) (F : ι → H →L[ℂ] H) (d : ι → ℝ) (k : ι) : H →L[ℂ] H :=
  (Real.sqrt (d k) : ℂ)⁻¹ • (P ∘L adjoint (F k))

/-- **The recovery operation of the sufficiency construction** (Nielsen & Chuang, Theorem 10.1), as
a family of operation elements indexed by `ι ⊕ Unit`. The `Sum.inl k` elements are the recovery
elements `Rₖ = (√dₖₖ)⁻¹ P Fₖ†` (`qecRecoveryElement`); the single `Sum.inr` element is the
completion projector `1 - ∑ₖ Pₖ` onto the orthogonal complement of the syndrome subspaces — N&C's
"additional projector … to satisfy the completeness relation `∑ₖ Pₖ = I`" — which makes the whole
family trace-preserving (`qecRecovery_adjoint_comp_self_sum`). -/
def qecRecovery (P : H →L[ℂ] H) (F : ι → H →L[ℂ] H) (d : ι → ℝ) : ι ⊕ Unit → H →L[ℂ] H :=
  Sum.elim (qecRecoveryElement P F d) fun _ => 1 - ∑ k, qecSyndromeProjector P F d k

omit [Fintype ι] in
/-- **The diagonalised Knill–Laflamme coefficients are nonnegative**, `0 ≤ dₖ`, whenever the code
projector `P` is nonzero (Nielsen & Chuang, Theorem 10.1). The simplified conditions give
`P Fₖ† Fₖ P = dₖ P`, and `P Fₖ† Fₖ P = (Fₖ P)† (Fₖ P)` is a positive operator; evaluating the
positivity of `dₖ • P` at a code vector (`nonneg_of_smul_isPositive`) forces `dₖ ≥ 0`. Physically
`α`, being (unitarily equivalent to) the Gram matrix of the errors restricted to the code, is
positive semidefinite; the hypothesis `P ≠ 0` is what a genuine (nonzero) code always satisfies. It
is `0 ≤ dₖ` that makes the `(√dₖₖ)⁻¹` normalisation of the recovery elements meaningful. -/
theorem qecSyndromeProjector_diagonal_nonneg [DecidableEq ι] (hP : IsSelfAdjoint P)
    (hPidem : P ∘L P = P) (hP0 : P ≠ 0)
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) (k : ι) : 0 ≤ d k := by
  have hPadj : adjoint P = P := by rw [← star_eq_adjoint]; exact hP
  have hkey : P ∘L adjoint (F k) ∘L F k ∘L P = (d k : ℂ) • P := by
    have h := hF k k; rwa [Matrix.diagonal_apply_eq] at h
  refine nonneg_of_smul_isPositive hPidem hP0 ?_
  rw [← hkey]
  have h := isPositive_adjoint_comp_self (F k ∘L P)
  rwa [adjoint_comp, hPadj, comp_assoc] at h

omit [Fintype ι] in
/-- **Each recovery element satisfies `Rₖ† Rₖ = Pₖ`** (Nielsen & Chuang, Theorem 10.1): the effect
`Rₖ† Rₖ` of the recovery element for syndrome `k` is exactly the `k`-th syndrome projector. With
`Rₖ = (√dₖ)⁻¹ P Fₖ†` and `P` self-adjoint idempotent, `Rₖ† Rₖ = ((√dₖ)⁻¹)² Fₖ P Fₖ†`, which equals
`dₖ⁻¹ Fₖ P Fₖ† = Pₖ` because `(√dₖ)² = dₖ` (`Real.mul_self_sqrt`, needing `0 ≤ dₖ`; the identity
survives `dₖ = 0` under `0⁻¹ = 0`). Summed over the syndromes this yields the completeness
`∑ₖ Rₖ† Rₖ = ∑ₖ Pₖ`. -/
theorem qecRecoveryElement_adjoint_comp_self (hP : IsSelfAdjoint P) (hPidem : P ∘L P = P) (k : ι)
    (hdk : 0 ≤ d k) :
    adjoint (qecRecoveryElement P F d k) ∘L qecRecoveryElement P F d k
      = qecSyndromeProjector P F d k := by
  have hPstar : star P = P := hP
  have hidem : P * P = P := hPidem
  have hstar : star ((Real.sqrt (d k) : ℂ)⁻¹) = (Real.sqrt (d k) : ℂ)⁻¹ := by
    rw [star_inv₀, ← starRingEnd_apply, Complex.conj_ofReal]
  have hsqrt : (Real.sqrt (d k) : ℂ)⁻¹ * (Real.sqrt (d k) : ℂ)⁻¹ = ((d k : ℂ))⁻¹ := by
    rw [← mul_inv_rev, ← Complex.ofReal_mul, Real.mul_self_sqrt hdk]
  simp only [qecRecoveryElement, qecSyndromeProjector, ← mul_def, ← star_eq_adjoint]
  rw [star_smul, hstar, star_mul, star_star, hPstar, smul_mul_assoc, mul_smul_comm, smul_smul,
    hsqrt]
  congr 1
  rw [mul_assoc (F k) P, ← mul_assoc P P, hidem]

omit [Fintype ι] in
/-- **The syndrome projectors form an orthogonal family of idempotents**
(`OrthogonalIdempotents`; Nielsen & Chuang, Theorem 10.1): each `Pₖ` is idempotent
(`qecSyndromeProjector_isStarProjection`) and the family is pairwise orthogonal, `Pₖ Pₗ = 0` for
`k ≠ l` (`qecSyndromeProjector_comp_eq_zero`, N&C eq. (10.19)). Packaging the family this way feeds
Mathlib's idempotents API directly — `OrthogonalIdempotents.isIdempotentElem_sum` for
`qecSyndromeProjector_sum_isStarProjection`, and `OrthogonalIdempotents.option` for the recovery's
completion by `1 - ∑ₖ Pₖ` in the trace-preservation and correction steps. -/
theorem qecSyndromeProjector_orthogonalIdempotents [DecidableEq ι] (hP : IsSelfAdjoint P)
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) :
    OrthogonalIdempotents (qecSyndromeProjector P F d) :=
  ⟨fun k => (qecSyndromeProjector_isStarProjection hP hF k).isIdempotentElem,
    fun _ _ hlk => qecSyndromeProjector_comp_eq_zero hF hlk⟩

/-- **The sum of the syndrome projectors is an orthogonal projection** (Nielsen & Chuang, Theorem
10.1): `∑ₖ Pₖ` projects onto the direct sum of the mutually orthogonal syndrome subspaces. It is
self-adjoint (`isSelfAdjoint_sum`) and idempotent — the syndrome projectors are an orthogonal family
of idempotents (`qecSyndromeProjector_orthogonalIdempotents`), so
`OrthogonalIdempotents.isIdempotentElem_sum` gives `(∑ₖ Pₖ)² = ∑ₖ Pₖ`. This is what lets the
recovery be completed to a trace-preserving operation by adjoining `1 - ∑ₖ Pₖ`
(`qecRecovery_adjoint_comp_self_sum`). -/
theorem qecSyndromeProjector_sum_isStarProjection [DecidableEq ι] (hP : IsSelfAdjoint P)
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) :
    IsStarProjection (∑ k, qecSyndromeProjector P F d k) :=
  ⟨(qecSyndromeProjector_orthogonalIdempotents hP hF).isIdempotentElem_sum,
    isSelfAdjoint_sum _ fun k _ => qecSyndromeProjector_isSelfAdjoint hP k⟩

/-- **The recovery operation is trace-preserving**, `∑ₒ Rₒ† Rₒ = 1` (Nielsen & Chuang, Theorem
10.1): `qecRecovery` is a genuine (trace-preserving) quantum operation. Over `ι ⊕ Unit` the sum
splits (`Fintype.sum_sum_type`) into the syndrome part `∑ₖ Rₖ† Rₖ = ∑ₖ Pₖ`
(`qecRecoveryElement_adjoint_comp_self`) and the completion part `Q† Q = Q` for the projection
`Q = 1 - ∑ₖ Pₖ` (`qecSyndromeProjector_sum_isStarProjection` + `IsStarProjection.one_sub`), and
`∑ₖ Pₖ + (1 - ∑ₖ Pₖ) = 1`. The nonzero-code hypothesis `P ≠ 0` enters through the nonnegativity of
the `dₖ` (`qecSyndromeProjector_diagonal_nonneg`), needed for `Rₖ† Rₖ = Pₖ`. -/
theorem qecRecovery_adjoint_comp_self_sum [DecidableEq ι] (hP : IsSelfAdjoint P)
    (hPidem : P ∘L P = P) (hP0 : P ≠ 0)
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) :
    ∑ o, adjoint (qecRecovery P F d o) ∘L qecRecovery P F d o = 1 := by
  have hQ : IsStarProjection (1 - ∑ k, qecSyndromeProjector P F d k) :=
    (qecSyndromeProjector_sum_isStarProjection hP hF).one_sub
  have hQadj : adjoint (1 - ∑ k, qecSyndromeProjector P F d k)
      = 1 - ∑ k, qecSyndromeProjector P F d k := by rw [← star_eq_adjoint]; exact hQ.isSelfAdjoint
  have hQidem : (1 - ∑ k, qecSyndromeProjector P F d k) ∘L (1 - ∑ k, qecSyndromeProjector P F d k)
      = 1 - ∑ k, qecSyndromeProjector P F d k := hQ.isIdempotentElem
  rw [Fintype.sum_sum_type]
  simp only [qecRecovery, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
      qecRecoveryElement_adjoint_comp_self hP hPidem k
        (qecSyndromeProjector_diagonal_nonneg hP hPidem hP0 hF k), hQadj, hQidem]
  abel

/-! ### Sufficiency: the recovery corrects the errors on the code

The final step of the sufficiency half (Nielsen & Chuang, Theorem 10.1, eqs. (10.20)–(10.26)): the
trace-preserving recovery `qecRecovery P F d` in fact *corrects* the diagonalised errors `F` on the
code, `Corrects P F (qecRecovery P F d)`. The engine is the family of **detection identities** for
`Rₒ Fₗ P` (recovery element `Rₒ` applied to an error `Fₗ` on the code): the syndrome-`k` element
`Rₖ` sends the `l`-th error subspace to `√dₖ P` when `k = l` and to `0` otherwise
(`qecRecoveryElement_comp_error_comp_proj`, eqs. (10.20)–(10.23)), while the completion element
`Q = 1 - ∑ₖ Pₖ` annihilates every error subspace (from
`qecSyndromeProjector_comp_error_comp_proj`). Feeding these into the combined operator-sum map
`(R ∘ F)(ρ)` collapses the double sum to `(∑ₖ dₖ) • ρ` for `ρ` supported on the code (eqs.
(10.24)–(10.26)). The proportionality constant `∑ₖ dₖ` (`= 1` when the errors are trace-preserving)
is allowed to be any scalar by `Corrects`, matching N&C's `∝` in eq. (10.15). -/

omit [Fintype ι] in
/-- **An error element annihilates the code when its diagonal coefficient vanishes**, `Fₗ P = 0`
whenever `dₗ = 0` (Nielsen & Chuang, Theorem 10.1). Under the diagonalised conditions the operator
`(Fₗ P)† (Fₗ P) = P Fₗ† Fₗ P = dₗ • P` is `0`, and a continuous linear map with `T† T = 0` vanishes
(`adjoint_comp_self_eq_zero_iff`). This is what makes the `0⁻¹ = 0` convention in the syndrome
projector and recovery element on such an index give the physically correct value `0`. -/
theorem errorElement_eq_zero_of_diag_zero [DecidableEq ι] (hP : IsSelfAdjoint P)
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) {l : ι} (hl : d l = 0) :
    F l ∘L P = 0 := by
  have hPadj : adjoint P = P := by rw [← star_eq_adjoint]; exact hP
  rw [← adjoint_comp_self_eq_zero_iff, adjoint_comp, hPadj]
  have h := hF l l
  rw [Matrix.diagonal_apply_eq, hl, Complex.ofReal_zero, zero_smul] at h
  rw [comp_assoc, h]

omit [Fintype ι] in
/-- **Detection identity for the recovery elements** (Nielsen & Chuang, Theorem 10.1, eqs.
(10.20)–(10.23)): the syndrome-`k` recovery element `Rₖ = (√dₖ)⁻¹ P Fₖ†` applied to the `l`-th error
on the code is `√dₖ P` when `k = l` and `0` otherwise. Indeed `Rₖ Fₗ P = (√dₖ)⁻¹ (P Fₖ† Fₗ P) =
(√dₖ)⁻¹ dₖₗ P`, and `(√dₖ)⁻¹ dₖ = dₖ / √dₖ = √dₖ` (`Real.div_sqrt`, which holds unconditionally,
including at `dₖ = 0`, under the `0⁻¹ = 0` convention). This identity rotates the detected error
subspace back onto the code. -/
theorem qecRecoveryElement_comp_error_comp_proj [DecidableEq ι]
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) (k l : ι) :
    qecRecoveryElement P F d k ∘L (F l ∘L P)
      = if k = l then (Real.sqrt (d k) : ℂ) • P else 0 := by
  have hkl := hF k l
  simp only [qecRecoveryElement, smul_comp]
  rw [comp_assoc, hkl, smul_smul]
  by_cases h : k = l
  · subst h
    rw [ite_eq_left rfl, Matrix.diagonal_apply_eq, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      show (Real.sqrt (d k))⁻¹ * d k = Real.sqrt (d k) from by
        rw [mul_comm, ← div_eq_mul_inv, Real.div_sqrt]]
  · rw [ite_eq_right h, Matrix.diagonal_apply_ne _ h, mul_zero, zero_smul]

omit [Fintype ι] in
/-- **Detection identity for the syndrome projectors** (Nielsen & Chuang, Theorem 10.1): the `k`-th
syndrome projector `Pₖ = dₖ⁻¹ Fₖ P Fₖ†` fixes the `l`-th error on the code when `k = l` and
annihilates it otherwise, `Pₖ Fₗ P = if k = l then Fₗ P else 0`. From `Pₖ Fₗ P =
dₖ⁻¹ Fₖ (P Fₖ† Fₗ P) = dₖ⁻¹ dₖₗ (Fₖ P)`: off the diagonal `dₖₗ = 0`; on it `dₖ⁻¹ dₖ = 1` when
`dₖ ≠ 0`, while at `dₖ = 0` both `dₖ⁻¹ dₖ = 0` and `Fₖ P = 0` (`errorElement_eq_zero_of_diag_zero`),
so `Pₖ Fₖ P = Fₖ P` regardless. This is the orthogonality that lets the completion element
`1 - ∑ₖ Pₖ` annihilate every error subspace. -/
theorem qecSyndromeProjector_comp_error_comp_proj [DecidableEq ι] (hP : IsSelfAdjoint P)
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) (k l : ι) :
    qecSyndromeProjector P F d k ∘L (F l ∘L P) = if k = l then F l ∘L P else 0 := by
  have hkl := hF k l
  simp only [qecSyndromeProjector, smul_comp]
  rw [comp_assoc, comp_assoc, hkl]
  by_cases h : k = l
  · subst h
    rw [ite_eq_left rfl, Matrix.diagonal_apply_eq, comp_smul, smul_smul]
    rcases eq_or_ne (d k) 0 with h0 | h0
    · rw [errorElement_eq_zero_of_diag_zero hP hF h0, smul_zero]
    · rw [inv_mul_cancel₀ (by exact_mod_cast h0), one_smul]
  · rw [ite_eq_right h, Matrix.diagonal_apply_ne _ h, zero_smul, comp_zero, smul_zero]

/-- **The completion element annihilates every error on the code**, `(1 - ∑ₖ Pₖ) Fₗ P = 0` (Nielsen
& Chuang, Theorem 10.1): the error `Fₗ` maps the code into the syndrome subspaces, so the projector
`∑ₖ Pₖ` onto their span fixes `Fₗ P` and the complementary projector `Q = 1 - ∑ₖ Pₖ` kills it. From
the syndrome detection `Pₖ Fₗ P = if k = l then Fₗ P else 0`, the sum `∑ₖ Pₖ Fₗ P` collapses to the
single surviving term `Fₗ P`, so `Q Fₗ P = Fₗ P - Fₗ P = 0`. -/
theorem qecRecoveryCompletion_comp_error_comp_proj [DecidableEq ι] (hP : IsSelfAdjoint P)
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) (l : ι) :
    (1 - ∑ k, qecSyndromeProjector P F d k) ∘L (F l ∘L P) = 0 := by
  have hsum : ∑ k, qecSyndromeProjector P F d k ∘L (F l ∘L P) = F l ∘L P := by
    rw [Finset.sum_congr rfl fun k _ => qecSyndromeProjector_comp_error_comp_proj hP hF k l]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sub_comp, finsetSum_comp, hsum]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, sub_self]

/-- **Sufficiency: the recovery corrects the diagonalised errors on the code** (Nielsen & Chuang,
Theorem 10.1, eqs. (10.20)–(10.26)). If `P` is a nonzero self-adjoint code projector and the
operation elements `F` satisfy the *diagonalised* Knill–Laflamme conditions
`P Fₖ† Fₗ P = dₖₗ P` (`d` real), then the trace-preserving recovery `qecRecovery P F d` corrects `F`
on the code: for every `ρ` supported on the code (`P ρ P = ρ`), `(R ∘ F)(ρ) = (∑ₖ dₖ) • ρ ∝ ρ`.

The proof computes the combined operator-sum map `krausSumₗ R (krausSumₗ F ρ)`. Writing
`ρ = P ρ P` absorbs the code projector into the errors (`krausSumₗ F ρ =
krausSumₗ (Fₗ P) ρ`), and `krausSumₗ_comp` combines the two Kraus maps into the single family
`(o, l) ↦ Rₒ Fₗ P`. The recovery-element detection identity
(`qecRecoveryElement_comp_error_comp_proj`) makes each such term `(√dₖ P) ρ (√dₖ P)† = dₖ • ρ` on
the diagonal `o = Sum.inl k, l = k` and `0` off it, while the completion element gives `0`
(`qecRecoveryCompletion_comp_error_comp_proj`); summing leaves `(∑ₖ dₖ) • ρ`. No
finite-dimensionality of `H` is needed — the construction is explicit, unlike the necessity half. -/
theorem corrects_of_satisfiesKLConditions_diagonal [DecidableEq ι] (hP : IsSelfAdjoint P)
    (hPidem : P ∘L P = P) (hP0 : P ≠ 0)
    (hF : SatisfiesKLConditions P F (Matrix.diagonal fun i => (d i : ℂ))) :
    Corrects P F (qecRecovery P F d) := by
  have hPadj : adjoint P = P := by rw [← star_eq_adjoint]; exact hP
  intro ρ hρ
  refine ⟨∑ k, (d k : ℂ), ?_⟩
  set R := qecRecovery P F d with hR
  -- Absorb the code projector into the errors: `krausSumₗ F ρ = krausSumₗ (fun l => Fₗ P) ρ`.
  have hFρ : krausSumₗ F ρ = krausSumₗ (fun l => F l ∘L P) ρ := by
    rw [krausSumₗ_apply, krausSumₗ_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [adjoint_comp, hPadj,
      show (F l ∘L P) ∘L ρ ∘L (P ∘L adjoint (F l)) = F l ∘L (P ∘L ρ ∘L P) ∘L adjoint (F l) from by
        simp only [comp_assoc], hρ]
  -- Combine the two Kraus maps into the single family `(o, l) ↦ Rₒ (Fₗ P)`.
  rw [hFρ, ← LinearMap.comp_apply, krausSumₗ_comp, krausSumₗ_apply, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  -- The `Sum.inr` (completion) block vanishes; the `Sum.inl k` block gives `dₖ • ρ` at `l = k`.
  have hcompl : ∀ u : Unit,
      ∑ l, (R (Sum.inr u) ∘L (F l ∘L P)) ∘L ρ ∘L adjoint (R (Sum.inr u) ∘L (F l ∘L P)) = 0 := by
    intro u
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hR, qecRecovery, Sum.elim_inr, qecRecoveryCompletion_comp_error_comp_proj hP hF l]
    simp
  have hrec : ∀ k : ι,
      ∑ l, (R (Sum.inl k) ∘L (F l ∘L P)) ∘L ρ ∘L adjoint (R (Sum.inl k) ∘L (F l ∘L P))
        = (d k : ℂ) • ρ := by
    intro k
    have hdk : 0 ≤ d k := qecSyndromeProjector_diagonal_nonneg hP hPidem hP0 hF k
    have hadjM : adjoint ((Real.sqrt (d k) : ℂ) • P) = (Real.sqrt (d k) : ℂ) • P := by
      rw [← star_eq_adjoint, star_smul, show star P = P from hP, ← starRingEnd_apply,
        Complex.conj_ofReal]
    rw [Fintype.sum_eq_single k fun l hlk => ?_]
    · rw [hR, qecRecovery, Sum.elim_inl,
        qecRecoveryElement_comp_error_comp_proj hF k k, ite_eq_left rfl, hadjM]
      simp only [smul_comp, comp_smul, smul_smul]
      rw [hρ]
      congr 1
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hdk]
    · rw [hR, qecRecovery, Sum.elim_inl,
        qecRecoveryElement_comp_error_comp_proj hF k l, ite_eq_right (Ne.symm hlk)]
      simp
  rw [Finset.sum_congr rfl fun k _ => hrec k, Finset.sum_congr rfl fun u _ => hcompl u,
    Finset.sum_const_zero, add_zero, ← Finset.sum_smul]

universe u

/-- **Sufficiency of the Knill–Laflamme quantum error-correction conditions** (Nielsen & Chuang,
Theorem 10.1, the `⟸` direction). If `P` is a nonzero self-adjoint code projector and the operation
elements `E` satisfy the conditions `P Eᵢ† Eⱼ P = αᵢⱼ P` for a **Hermitian** matrix `α`, then there
is a **trace-preserving** recovery operation `R` (`∑ₒ Rₒ† Rₒ = 1`) that **corrects** the errors `E`
on the code (`Corrects P E R`).

The recovery is Nielsen & Chuang's explicit syndrome-measure-then-rotate operation: diagonalise the
conditions (`SatisfiesKLConditions.exists_recombine_diagonal`) to recombined elements `F` with the
same operator-sum map and real diagonal `d`, then take `R = qecRecovery P F d` — the syndrome
recovery elements `(√dₖ)⁻¹ P Fₖ†` completed by `1 - ∑ₖ Pₖ`. It is trace-preserving
(`qecRecovery_adjoint_comp_self_sum`) and corrects `E` because it corrects `F`
(`corrects_of_satisfiesKLConditions_diagonal`) and `krausSumₗ F = krausSumₗ E`. Unlike the necessity
half this needs **no** `FiniteDimensional ℂ H`: the recovery is constructed explicitly. The
existential over the index `κ` (here `ι ⊕ Unit`) matches the shape consumed by the necessity theorem
`satisfiesKLConditions_of_corrects`, so the two directions assemble into the biconditional. -/
theorem corrects_of_satisfiesKLConditions {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type u} [Fintype ι]
    {P : H →L[ℂ] H} {E : ι → H →L[ℂ] H} {α : Matrix ι ι ℂ}
    (hP : IsSelfAdjoint P) (hPidem : P ∘L P = P) (hP0 : P ≠ 0)
    (hα : α.IsHermitian) (hE : SatisfiesKLConditions P E α) :
    ∃ (κ : Type u) (_ : Fintype κ) (R : κ → H →L[ℂ] H),
      (∑ o, adjoint (R o) ∘L R o = 1) ∧ Corrects P E R := by
  classical
  obtain ⟨F, hFE, hFdiag⟩ := hE.exists_recombine_diagonal hα
  have hFdiag' : SatisfiesKLConditions P F (Matrix.diagonal fun i => (hα.eigenvalues i : ℂ)) :=
    hFdiag
  refine ⟨ι ⊕ Unit, inferInstance, qecRecovery P F hα.eigenvalues,
    qecRecovery_adjoint_comp_self_sum hP hPidem hP0 hFdiag', fun ρ hρ => ?_⟩
  obtain ⟨c, hc⟩ := corrects_of_satisfiesKLConditions_diagonal hP hPidem hP0 hFdiag' ρ hρ
  exact ⟨c, by rw [← hFE]; exact hc⟩

/-- **The Knill–Laflamme quantum error-correction conditions** (Nielsen & Chuang, Theorem 10.1) —
the biconditional. For a nonzero orthogonal code projector `P` and a finite family of operation
elements `E` (the noise) on a finite-dimensional complex inner product space, there exists a
**trace-preserving** recovery operation `R` (`∑ₒ Rₒ† Rₒ = 1`) that **corrects** `E` on the code
(`Corrects P E R`) **iff** the errors satisfy `P Eᵢ† Eⱼ P = αᵢⱼ P` for a **Hermitian** matrix `α`.

This assembles the two halves proved above:
* `⟹` is `satisfiesKLConditions_of_corrects` (necessity, N&C eqs. (10.27)–(10.30));
* `⟸` is `corrects_of_satisfiesKLConditions` (sufficiency, N&C eqs. (10.17)–(10.26), the explicit
  syndrome-measure-then-rotate recovery).

The two directions use the *same* existential shape for the recovery (a Kraus family with the
completeness relation `∑ₒ Rₒ† Rₒ = 1`), so they combine into a single `Iff`. `FiniteDimensional ℂ H`
is needed only for the `⟹` direction (the operator-sum-freedom step, N&C Theorem 8.2); the recovery
in `⟸` is constructed explicitly. -/
theorem satisfiesKLConditions_iff_exists_correction {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H] {ι : Type u} [Fintype ι]
    {P : H →L[ℂ] H} {E : ι → H →L[ℂ] H}
    (hP : IsSelfAdjoint P) (hPidem : P ∘L P = P) (hP0 : P ≠ 0) :
    (∃ (κ : Type u) (_ : Fintype κ) (R : κ → H →L[ℂ] H),
        (∑ o, adjoint (R o) ∘L R o = 1) ∧ Corrects P E R) ↔
      ∃ α : Matrix ι ι ℂ, α.IsHermitian ∧ SatisfiesKLConditions P E α := by
  constructor
  · rintro ⟨κ, _, R, hR, hcorr⟩
    exact satisfiesKLConditions_of_corrects hP hPidem hP0 hR hcorr
  · rintro ⟨α, hα, hE⟩
    exact corrects_of_satisfiesKLConditions hP hPidem hP0 hα hE

end ContinuousLinearMap
