/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LinearOpticalElement
import AxQM.Concrete.TwoLevelDecomposition
import AxQM.Concrete.TwoLevelControlledIdentification

/-!
# Concrete: beamsplitters and phase shifters generate every unitary (N&C Problem 7.2.1, assembly)

Nielsen & Chuang, Problem 7.2 (p. 346), *Computing with linear optics*, Part 1: with the **unary**
mode encoding (a single photon in one of `d = 2ⁿ` optical modes), an arbitrary `n`-qubit gate is a
`d × d` unitary on the mode amplitudes, and the task is to build it from only **beamsplitters** and
**phase shifters**. `AxQM/Concrete/LinearOpticalElement.lean` supplies
the atomic step — every *embedded* two-level unitary `twoLevelEmbed p q G` is a finite product of
linear-optical elements (`exists_linearOpticalList_prod_eq_twoLevelEmbed`). This file assembles that
into the full matrix-level statement.

## The two steps

* **Extraction** (`exists_twoLevelEmbed_of_isTwoLevelUnitary`). The §4.5.1 headline
  `exists_twoLevelUnitaryList_prod_eq` decomposes an arbitrary `d × d` unitary into a list of
  `IsTwoLevelUnitary` factors, but each factor is only *given* as a two-level unitary — a matrix
  agreeing with the identity outside some `{p, q} × {p, q}` block — not in the concrete
  `twoLevelEmbed p q G` shape that result consumes. This lemma bridges the two: for `2 ≤ d`, any
  `IsTwoLevelUnitary M` equals `twoLevelEmbed p q G` for some `p ≠ q` and some `G ∈ U(2)`, obtained
  by reading `M`'s `{p, q}`-block into a `2 × 2` matrix. The degenerate one-level case `p = q` (a
  single phase on mode `p`) is handled by pairing `p` with a spare mode `r ≠ p` (which exists since
  `2 ≤ d`) and embedding `diag(M p p, 1)`.

* **Assembly** (`exists_linearOpticalList_prod_eq`). Feed each two-level factor through the
  extraction and then that file's block decomposition, concatenating the resulting linear-optical
  lists.
  Because `List.prod` is multiplicative over `++`, the concatenated list's product is the original
  unitary.

The headline `exists_linearOpticalList_prod_eq` is the matrix-level content of Problem 7.2 Part 1;
the reading of these matrices as `Evolution (qudit d)` gates, and universality for such gates,
are stated in `AxQM/NC/Ch7/Problem7_2.lean`.

## Design notes

* **Why `2 ≤ d`.** Two distinct modes are needed even to name a beamsplitter, and the one-level case
  of the extraction needs a spare index. In dimensions `0` and `1` the only unitaries are (up to
  phase) the identity, and there are no genuine two-mode elements, so the honest statement is
  dimension `≥ 2`.
* **Reusing the shared block API.** Both the "read off the block" and "the block is unitary" steps
  of the extraction are exactly the reusable §4.5.2 support machinery of
  `Concrete/TwoLevelControlledIdentification.lean`: `eq_twoLevelEmbed_of_support` re-embeds a matrix
  supported on `{p, q}` as `twoLevelEmbed p q (twoLevelBlock M p q)`, and
  `twoLevelBlock_mem_unitaryGroup` shows that block is in `U(2)`. The two-level unitary's own
  support hypothesis (the `∀ i j, … → M i j = 1 i j` clause of `IsTwoLevelUnitary`) feeds both; the
  one-level case reuses the same two lemmas at the pair `(p, r)`, where the `{p}`-support is a
  fortiori a `{p, r}`-support.

-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-! ### Extracting the embedded form of a two-level unitary -/

/-- **Every two-level unitary is an embedded `2 × 2` unitary** (in dimension `d ≥ 2`). For
`IsTwoLevelUnitary M` there are distinct modes `p ≠ q` and a `2 × 2` unitary `G` with
`M = twoLevelEmbed p q G`. The two-index (`p ≠ q`) case reads `M`'s `{p, q}`-block off with the
shared `eq_twoLevelEmbed_of_support` / `twoLevelBlock_mem_unitaryGroup`; the one-index case `p = q`
(a single phase on mode `p`) pairs `p` with a spare mode `r` and applies the same two lemmas at
`(p, r)`, where the block `twoLevelBlock M p r` is `diag(M p p, 1)`. -/
theorem exists_twoLevelEmbed_of_isTwoLevelUnitary (hd : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) ℂ} (hM : IsTwoLevelUnitary M) :
    ∃ (p q : Fin d) (G : Matrix (Fin 2) (Fin 2) ℂ),
      p ≠ q ∧ G ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ M = twoLevelEmbed p q G := by
  obtain ⟨hMU, p, q, hpq_id⟩ := hM
  by_cases hpq : p = q
  · -- one-level (phase-only) case: pair `p` with a spare mode `r`
    subst hpq
    have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
    obtain ⟨r, hr⟩ := exists_ne p
    have hpr : p ≠ r := Ne.symm hr
    -- the `{p}`-support of the one-level unitary is a fortiori a `{p, r}`-support
    have hsupp : ∀ i j : Fin d, (i ≠ p ∧ i ≠ r) ∨ (j ≠ p ∧ j ≠ r) →
        M i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
      rintro i j (⟨hip, _⟩ | ⟨hjp, _⟩)
      · exact hpq_id i j (Or.inl ⟨hip, hip⟩)
      · exact hpq_id i j (Or.inr ⟨hjp, hjp⟩)
    exact ⟨p, r, twoLevelBlock M p r, hpr, twoLevelBlock_mem_unitaryGroup hpr hMU hsupp,
      eq_twoLevelEmbed_of_support hpr hsupp⟩
  · -- genuine two-index case: read off the `{p, q}`-block
    exact ⟨p, q, twoLevelBlock M p q, hpq, twoLevelBlock_mem_unitaryGroup hpq hMU hpq_id,
      eq_twoLevelEmbed_of_support hpq hpq_id⟩

/-! ### Assembling the linear-optical realization -/

/-- **A single two-level unitary is a product of linear-optical elements** (dimension `d ≥ 2`):
chain the extraction with `LinearOpticalElement.lean`'s block decomposition. -/
theorem exists_linearOpticalList_prod_eq_of_isTwoLevelUnitary (hd : 2 ≤ d)
    {M : Matrix (Fin d) (Fin d) ℂ} (hM : IsTwoLevelUnitary M) :
    ∃ L : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ V ∈ L, IsLinearOpticalElement V) ∧ L.prod = M := by
  obtain ⟨p, q, G, hpq, hG, rfl⟩ := exists_twoLevelEmbed_of_isTwoLevelUnitary hd hM
  exact exists_linearOpticalList_prod_eq_twoLevelEmbed hpq hG

/-- **A list of two-level unitaries rewrites to a list of linear-optical elements with the same
product** (dimension `d ≥ 2`): decompose each factor and concatenate. -/
theorem exists_linearOpticalList_prod_eq_of_forall_isTwoLevelUnitary (hd : 2 ≤ d) :
    ∀ L : List (Matrix (Fin d) (Fin d) ℂ), (∀ M ∈ L, IsTwoLevelUnitary M) →
      ∃ L' : List (Matrix (Fin d) (Fin d) ℂ),
        (∀ V ∈ L', IsLinearOpticalElement V) ∧ L'.prod = L.prod := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], by simp, by simp⟩
  | cons M rest ih =>
    intro hL
    obtain ⟨LM, hLM, hLMprod⟩ :=
      exists_linearOpticalList_prod_eq_of_isTwoLevelUnitary hd (hL M (by simp))
    obtain ⟨Lrest, hLrest, hLrestprod⟩ := ih (fun M' hM' => hL M' (by simp [hM']))
    refine ⟨LM ++ Lrest, ?_, ?_⟩
    · intro V hV
      rcases List.mem_append.mp hV with hVM | hVrest
      · exact hLM V hVM
      · exact hLrest V hVrest
    · rw [List.prod_append, hLMprod, hLrestprod, List.prod_cons]

/-- **Universality of linear optics at the matrix level (Nielsen & Chuang, Problem 7.2.1).** For
`d ≥ 2`, every `d × d` unitary `U` is the product of a finite list of linear-optical elements —
beamsplitters and phase shifters. Chaining the §4.5.1 two-level decomposition
(`exists_twoLevelUnitaryList_prod_eq`) with the extraction and the Reck–Zeilinger realization of
each two-level factor (`exists_linearOpticalList_prod_eq_twoLevelEmbed`) proves that the two passive
optical elements suffice to realize an arbitrary unitary on the unary-encoded single-photon system,
with no nonlinear media. -/
theorem exists_linearOpticalList_prod_eq (hd : 2 ≤ d)
    {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ L : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ V ∈ L, IsLinearOpticalElement V) ∧ L.prod = U := by
  obtain ⟨L, hL, hLprod⟩ := exists_twoLevelUnitaryList_prod_eq U hU
  obtain ⟨L', hL', hL'prod⟩ := exists_linearOpticalList_prod_eq_of_forall_isTwoLevelUnitary hd L hL
  exact ⟨L', hL', hL'prod.trans hLprod⟩

end AxQM.Concrete
