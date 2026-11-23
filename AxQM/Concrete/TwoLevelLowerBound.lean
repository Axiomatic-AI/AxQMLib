/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QFTTwoLevel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Module

/-!
# Concrete: a `d × d` unitary needing `≥ d − 1` two-level factors (N&C Ex 4.38)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 4.38 (p. 191):

There is a d × d unitary needing at least d − 1 two-level unitaries in any decomposition.

This complements §4.5.1 / Exercise 4.37 (`AxQM.Concrete.QFTTwoLevel`), which shows every
`d × d` unitary *does* factor into two-level unitaries (`≤ d(d−1)/2` of them): the `d − 1` lower
bound here shows that count cannot in general be pushed below `d − 1`.

## The argument (a connectivity / dimension count)

A two-level unitary (`IsTwoLevelUnitary`, from Ex 4.37) agrees with the identity outside a single
`{p, q} × {p, q}` block. Associate to a factor `V` the space `diffSpan V` spanned by the difference
vectors `eₐ − e_b` over the *nonzero* entries `Vₐ_b`; for a two-level `V` this is contained in the
line `ℂ ∙ (e_p − e_q)`, so `finrank (diffSpan V) ≤ 1`.

For a product `L.prod = V₁ ⋯ V_k`, a Gaussian-elimination-free induction on `L` shows
`(L.prod)ₐ_b ≠ 0 → eₐ − e_b ∈ edgeSpan L`, where `edgeSpan L = ⨆ diffSpan Vᵢ` has
`finrank (edgeSpan L) ≤ k = L.length`. (A nonzero `(a,b)` entry means `a` and `b` are joined through
the factors — the graph-connectivity form of the standard proof, phrased here as membership in the
span of the factors' edge vectors.)

The witness is the **all-ones reflection** `allOnesReflection d = 1 − (2/d) • J` (the Householder
reflection through the hyperplane orthogonal to `(1,…,1)`; a real symmetric involution, hence
unitary). Its `0`-th column has every off-diagonal entry equal to `−2/d ≠ 0`, so
`eᵢ − e₀ ∈ edgeSpan L` for all `i ≠ 0`. These `d − 1` vectors are linearly independent, giving
`d − 1 ≤ finrank (edgeSpan L) ≤ L.length`. Thus no product of fewer than `d − 1` two-level unitaries
equals this `U`.

## Design notes

* **Only the two-level structure is used** — not unitarity of the factors — but the statement keeps
  `IsTwoLevelUnitary` on each factor, so it is the faithful N&C claim (a lower bound proved from a
  weaker property is still a lower bound for the stated one).
* **Choice-free bookkeeping.** `edgeSpan`/`diffSpan` are defined canonically from the matrices
  (spans over their nonzero-entry difference vectors), never by extracting the existential `{p, q}`
  into data; the two-level hypothesis enters only in the `finrank (diffSpan V) ≤ 1` bound.
* **Statement.** The statement of Exercise 4.38 is in `AxQM/NC/Ch4/Exercise4_38.lean`. This file
  reuses `IsTwoLevelUnitary` from the Ex 4.37 file.
-/

namespace AxQM.Concrete

open Matrix Module

variable {d : ℕ}

/-- The `i`-th standard basis vector of `Fin d → ℂ` (value `1` at `i`, `0` elsewhere). -/
def stdVec (i : Fin d) : Fin d → ℂ := Pi.single i 1

@[simp] lemma stdVec_self (i : Fin d) : stdVec i i = 1 := Pi.single_eq_same _ _

lemma stdVec_of_ne {i j : Fin d} (h : j ≠ i) : stdVec i j = 0 := Pi.single_eq_of_ne h _

/-- The standard basis vectors of `Fin d → ℂ` are self-conjugate: `star (stdVec i) = stdVec i`. -/
lemma star_stdVec (i : Fin d) : star (stdVec i) = stdVec i := by
  rw [stdVec, Pi.star_single, star_one]

/-- The span of the difference vectors `eₐ − e_b` over the nonzero entries `Mₐ_b` of `M`. For a
two-level matrix this is contained in a single line `ℂ ∙ (e_p − e_q)`. -/
def diffSpan (M : Matrix (Fin d) (Fin d) ℂ) : Submodule ℂ (Fin d → ℂ) :=
  Submodule.span ℂ {v | ∃ a b, M a b ≠ 0 ∧ v = stdVec a - stdVec b}

/-- The edge span of a list of factors: the join of the individual `diffSpan`s. Its dimension is at
most the number of factors (each contributes at most one dimension). -/
def edgeSpan : List (Matrix (Fin d) (Fin d) ℂ) → Submodule ℂ (Fin d → ℂ)
  | [] => ⊥
  | M :: rest => diffSpan M ⊔ edgeSpan rest

/-- Core connectivity lemma: if the ordered product of a list of matrices has a nonzero `(a, b)`
entry, then the difference vector `eₐ − e_b` lies in the edge span of the list. Proved by induction
on the list (needs no two-level hypothesis). -/
lemma stdVec_sub_mem_edgeSpan_of_prod_apply_ne_zero :
    ∀ (L : List (Matrix (Fin d) (Fin d) ℂ)) (a b : Fin d),
      L.prod a b ≠ 0 → stdVec a - stdVec b ∈ edgeSpan L
  | [], a, b, h => by
      rw [List.prod_nil, Matrix.one_apply] at h
      by_cases hab : a = b
      · subst hab; simp [edgeSpan]
      · exact absurd (ite_eq_right hab) h
  | M :: rest, a, b, h => by
      rw [List.prod_cons, Matrix.mul_apply] at h
      obtain ⟨c, hc⟩ : ∃ c, M a c * rest.prod c b ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        exact h (Finset.sum_eq_zero fun c _ => hcon c)
      have hMc : M a c ≠ 0 := fun h0 => hc (by rw [h0, zero_mul])
      have hrest : rest.prod c b ≠ 0 := fun h0 => hc (by rw [h0, mul_zero])
      have h1 : stdVec a - stdVec c ∈ edgeSpan (M :: rest) :=
        Submodule.mem_sup_left (Submodule.subset_span ⟨a, c, hMc, rfl⟩)
      have h2 : stdVec c - stdVec b ∈ edgeSpan (M :: rest) :=
        Submodule.mem_sup_right
          (stdVec_sub_mem_edgeSpan_of_prod_apply_ne_zero rest c b hrest)
      have hadd := Submodule.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at hadd

/-- For a two-level matrix, the edge-difference span is at most one-dimensional: it lies inside the
line spanned by `e_p − e_q` (the block indices). -/
lemma finrank_diffSpan_le_one {M : Matrix (Fin d) (Fin d) ℂ} (hM : IsTwoLevelUnitary M) :
    finrank ℂ (diffSpan M) ≤ 1 := by
  obtain ⟨_, p, q, hpq⟩ := hM
  have hsub : diffSpan M ≤ Submodule.span ℂ {stdVec p - stdVec q} := by
    rw [diffSpan, Submodule.span_le]
    rintro v ⟨a, b, hab, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    by_cases hab' : a = b
    · exact ⟨0, by rw [hab']; simp⟩
    -- a nonzero off-diagonal entry forces both indices into `{p, q}`
    have ha : a = p ∨ a = q := by
      by_contra hcon; rw [not_or] at hcon
      exact hab (by rw [hpq a b (Or.inl ⟨hcon.1, hcon.2⟩), Matrix.one_apply, ite_eq_right hab'])
    have hb : b = p ∨ b = q := by
      by_contra hcon; rw [not_or] at hcon
      exact hab (by rw [hpq a b (Or.inr ⟨hcon.1, hcon.2⟩), Matrix.one_apply, ite_eq_right hab'])
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact ⟨0, by rw [ha, hb]; simp⟩
    · exact ⟨1, by rw [ha, hb]; module⟩
    · exact ⟨-1, by rw [ha, hb]; module⟩
    · exact ⟨0, by rw [ha, hb]; simp⟩
  calc finrank ℂ (diffSpan M)
        ≤ finrank ℂ (Submodule.span ℂ {stdVec p - stdVec q}) := Submodule.finrank_mono hsub
    _ ≤ ({stdVec p - stdVec q} : Set (Fin d → ℂ)).toFinset.card := finrank_span_le_card _
    _ ≤ 1 := by simp

/-- The edge span of a list of two-level unitaries has dimension at most the length of the list. -/
lemma finrank_edgeSpan_le_length :
    ∀ (L : List (Matrix (Fin d) (Fin d) ℂ)), (∀ M ∈ L, IsTwoLevelUnitary M) →
      finrank ℂ (edgeSpan L) ≤ L.length
  | [], _ => by
      simp only [edgeSpan, List.length_nil]
      exact le_of_eq
        (Module.finrank_zero_of_subsingleton : finrank ℂ (⊥ : Submodule ℂ (Fin d → ℂ)) = 0)
  | M :: rest, hL => by
      have hM : IsTwoLevelUnitary M := hL M (by simp)
      have hrest : ∀ N ∈ rest, IsTwoLevelUnitary N :=
        fun N hN => hL N (List.mem_cons.mpr (Or.inr hN))
      calc finrank ℂ (edgeSpan (M :: rest))
            ≤ finrank ℂ (diffSpan M) + finrank ℂ (edgeSpan rest) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ 1 + rest.length :=
            Nat.add_le_add (finrank_diffSpan_le_one hM) (finrank_edgeSpan_le_length rest hrest)
        _ = (M :: rest).length := by rw [List.length_cons]; omega

/-! ### The witness: the all-ones reflection `1 − (2/d) • J` -/

/-- The `d × d` all-ones matrix `J` (every entry `1`), over `ℂ`. -/
def allOnes : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun _ _ => 1

/-- The all-ones reflection `U = 1 − (2/d) • J`: the Householder reflection through the hyperplane
orthogonal to `(1,…,1)`. A real symmetric involution, hence unitary; it is the witness for
Exercise 4.38. -/
noncomputable def allOnesReflection (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  1 - (2 / d : ℂ) • allOnes

lemma allOnes_mul_allOnes : (allOnes : Matrix (Fin d) (Fin d) ℂ) * allOnes = (d : ℂ) • allOnes := by
  ext i j
  simp only [allOnes, Matrix.mul_apply, Matrix.of_apply, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.smul_apply, smul_eq_mul]

lemma star_allOnesReflection : star (allOnesReflection d) = allOnesReflection d := by
  have hJ : (allOnes : Matrix (Fin d) (Fin d) ℂ)ᴴ = allOnes := by
    ext i j; simp [allOnes, Matrix.conjTranspose_apply]
  have hstarc : star (2 / (d : ℂ)) = 2 / (d : ℂ) := by simp [star_div₀]
  rw [Matrix.star_eq_conjTranspose]
  unfold allOnesReflection
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hJ, hstarc]

lemma allOnesReflection_mul_self :
    allOnesReflection d * allOnesReflection d = 1 := by
  have hscalar : -(2 * (2 / (d : ℂ))) + (2 / (d : ℂ)) ^ 2 * (d : ℂ) = 0 := by
    rcases eq_or_ne (d : ℂ) 0 with hd | hd
    · simp [hd]
    · field_simp; ring
  have hexpand : allOnesReflection d * allOnesReflection d
      = 1 + (-(2 * (2 / (d : ℂ))) + (2 / (d : ℂ)) ^ 2 * (d : ℂ)) • allOnes := by
    simp only [allOnesReflection, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, allOnes_mul_allOnes, smul_smul]
    match_scalars <;> ring
  rw [hexpand, hscalar, zero_smul, add_zero]

/-- The all-ones reflection is a unitary matrix. -/
lemma allOnesReflection_mem_unitaryGroup :
    allOnesReflection d ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_allOnesReflection, allOnesReflection_mul_self]

/-- Every off-diagonal entry of the `0`-th column of the all-ones reflection is `−2/d ≠ 0`. -/
lemma allOnesReflection_apply_zero_ne_zero [NeZero d] (a : Fin d) (ha : a ≠ 0) :
    allOnesReflection d a 0 ≠ 0 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  unfold allOnesReflection
  simp only [allOnes, Matrix.sub_apply, Matrix.one_apply, ite_eq_right ha, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_one, zero_sub, neg_ne_zero]
  exact div_ne_zero two_ne_zero hd

/-! ### Main theorem -/

/-- **Nielsen & Chuang, Exercise 4.38.** For every `d`, there is a `d × d` unitary matrix that
cannot be written as a product of fewer than `d − 1` two-level unitary matrices: the all-ones
reflection `allOnesReflection d` witnesses this — any list of two-level unitaries whose product
equals it has length at least `d − 1`. -/
theorem exists_unitary_two_level_decomposition_length_ge (d : ℕ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin d) ℂ,
      ∀ L : List (Matrix (Fin d) (Fin d) ℂ),
        (∀ V ∈ L, IsTwoLevelUnitary V) → L.prod = U → d - 1 ≤ L.length := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    exact ⟨allOnesReflection 0, allOnesReflection_mem_unitaryGroup, fun L _ _ => Nat.zero_le _⟩
  have : NeZero d := ⟨hdpos.ne'⟩
  refine ⟨allOnesReflection d, allOnesReflection_mem_unitaryGroup, ?_⟩
  intro L hL hprod
  -- the `d − 1` difference vectors `eᵢ − e₀` (`i ≠ 0`) all lie in the edge span
  have hmem : ∀ i : Fin d, i ≠ 0 → stdVec i - stdVec (0 : Fin d) ∈ edgeSpan L := by
    intro i hi
    apply stdVec_sub_mem_edgeSpan_of_prod_apply_ne_zero
    rw [hprod]
    exact allOnesReflection_apply_zero_ne_zero i hi
  -- and they are linearly independent
  have hLI : LinearIndependent ℂ
      (fun i : {i : Fin d // i ≠ 0} => stdVec i.1 - stdVec (0 : Fin d)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hgi := congrFun hg i.1
    rw [Finset.sum_apply] at hgi
    simp only [Pi.zero_apply] at hgi
    rw [Finset.sum_eq_single i] at hgi
    · rw [Pi.smul_apply, Pi.sub_apply, stdVec_self, stdVec_of_ne i.2, sub_zero, smul_eq_mul,
        mul_one] at hgi
      exact hgi
    · intro k _ hk
      have hki : i.1 ≠ k.1 := fun heq => hk (Subtype.ext heq.symm)
      rw [Pi.smul_apply, Pi.sub_apply, stdVec_of_ne hki, stdVec_of_ne i.2, sub_zero, smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  -- lift the independent family into the edge-span submodule
  have hLI' : LinearIndependent ℂ
      (fun i : {i : Fin d // i ≠ 0} =>
        (⟨stdVec i.1 - stdVec (0 : Fin d), hmem i.1 i.2⟩ : edgeSpan L)) :=
    LinearIndependent.of_comp (edgeSpan L).subtype (by simpa [Function.comp_def] using hLI)
  -- count: `d − 1 = card {i ≠ 0} ≤ finrank (edgeSpan L) ≤ L.length`
  have hcard : Fintype.card {i : Fin d // i ≠ 0} = d - 1 := by
    simp only [ne_eq]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  calc d - 1 = Fintype.card {i : Fin d // i ≠ 0} := hcard.symm
    _ ≤ finrank ℂ (edgeSpan L) := hLI'.fintype_card_le_finrank
    _ ≤ L.length := finrank_edgeSpan_le_length L hL

end AxQM.Concrete
