/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.Convex.Majorization

/-!
# Entanglement catalysis — the majorization data (Nielsen & Chuang, Exercise 12.21)

Nielsen & Chuang, Exercise 12.21, exhibits *entanglement catalysis*: bipartite pure states

* `|ψ⟩ = √0.4|00⟩ + √0.4|11⟩ + √0.1|22⟩ + √0.1|33⟩` (two four-level systems),
* `|φ⟩ = √0.5|00⟩ + √0.25|11⟩ + √0.25|22⟩`,
* a catalyst pair of qubits `|c⟩ = √0.6|00⟩ + √0.4|11⟩`,

for which `|ψ⟩` **cannot** be converted to `|φ⟩` by LOCC, yet `|ψ⟩|c⟩` **can** be converted to
`|φ⟩|c⟩` by LOCC — the borrowed entanglement `|c⟩` is returned unchanged.

By Nielsen's theorem (N&C Theorem 12.15, formalised as
`AxQM.State.loccConvertible_iff_majorize`), LOCC-convertibility of a bipartite pure state
is equivalent to *majorization* of the reduced-state eigenvalue vectors — the **squared Schmidt
coefficients**. So both physical claims are, mathematically, statements about the majorization order
`Majorize` (`ToMathlib/Analysis/Convex/Majorization.lean`) on these concrete spectra:

* `λ_ψ = (0.4, 0.4, 0.1, 0.1)` is **not** majorized by `λ_φ = (0.5, 0.25, 0.25, 0)` — because the
  two largest entries sum to `0.8 > 0.75` (`catalysisPsiSpec_not_majorize`); hence no LOCC
  conversion `|ψ⟩ → |φ⟩`;
* the tensor `λ_ψ ⊗ λ_c` **is** majorized by `λ_φ ⊗ λ_c` on the eight product outcomes
  (`catalysisTensorSpec_majorize`); hence the catalysed conversion `|ψ⟩|c⟩ → |φ⟩|c⟩` succeeds.

This file provides that mathematical core, using only `ℝ`, `Fin` and the majorization order; the
physics statement for states is assembled in `AxQM/NC/Ch12/Exercise12_21.lean` on top of these facts
and Nielsen's theorem.

## Main definitions

* `catalysisPsiSpec`, `catalysisPhiSpec` : `Fin 4 → ℝ`, and `catalysisCatSpec` : `Fin 2 → ℝ` — the
  three squared-Schmidt spectra (exact rationals). Each is a probability vector
  (`_nonneg`, `_sum_eq_one`).
* `catalysisPsiTensorSpec`, `catalysisPhiTensorSpec` : `Fin 4 × Fin 2 → ℝ` — the product spectra
  `λ_ψ ⊗ λ_c` and `λ_φ ⊗ λ_c`.

## Main statements

* `catalysisPsiSpec_not_majorize` : `¬ Majorize catalysisPsiSpec catalysisPhiSpec`.
* `catalysisTensorSpec_majorize` : `Majorize catalysisPsiTensorSpec catalysisPhiTensorSpec`.
-/

open Finset

namespace AxQM.Concrete

/-! ### The three squared-Schmidt spectra -/

/-- Squared Schmidt coefficients of `|ψ⟩ = √0.4|00⟩ + √0.4|11⟩ + √0.1|22⟩ + √0.1|33⟩`, the source
state of the catalysis example (N&C Exercise 12.21): `λ_ψ = (0.4, 0.4, 0.1, 0.1)`. -/
noncomputable def catalysisPsiSpec : Fin 4 → ℝ := ![2/5, 2/5, 1/10, 1/10]

/-- Squared Schmidt coefficients of `|φ⟩ = √0.5|00⟩ + √0.25|11⟩ + √0.25|22⟩`, the target state of
the catalysis example (N&C Exercise 12.21): `λ_φ = (0.5, 0.25, 0.25, 0)`. -/
noncomputable def catalysisPhiSpec : Fin 4 → ℝ := ![1/2, 1/4, 1/4, 0]

/-- Squared Schmidt coefficients of the catalyst `|c⟩ = √0.6|00⟩ + √0.4|11⟩` (N&C Exercise 12.21):
`λ_c = (0.6, 0.4)`. -/
noncomputable def catalysisCatSpec : Fin 2 → ℝ := ![3/5, 2/5]

lemma catalysisPsiSpec_nonneg (i : Fin 4) : 0 ≤ catalysisPsiSpec i := by
  fin_cases i <;> simp [catalysisPsiSpec] <;> norm_num

lemma catalysisPhiSpec_nonneg (i : Fin 4) : 0 ≤ catalysisPhiSpec i := by
  fin_cases i <;> simp [catalysisPhiSpec]

lemma catalysisCatSpec_nonneg (i : Fin 2) : 0 ≤ catalysisCatSpec i := by
  fin_cases i <;> simp [catalysisCatSpec] <;> norm_num

lemma catalysisPsiSpec_sum_eq_one : ∑ i, catalysisPsiSpec i = 1 := by
  simp [catalysisPsiSpec, Fin.sum_univ_four]; norm_num

lemma catalysisPhiSpec_sum_eq_one : ∑ i, catalysisPhiSpec i = 1 := by
  simp [catalysisPhiSpec, Fin.sum_univ_four]; norm_num

lemma catalysisCatSpec_sum_eq_one : ∑ i, catalysisCatSpec i = 1 := by
  simp [catalysisCatSpec, Fin.sum_univ_two]; norm_num

/-! ### The tensor (product) spectra `λ ⊗ λ_c` -/

/-- The spectrum of `|ψ⟩|c⟩`: the outer product `λ_ψ ⊗ λ_c` on the eight product outcomes,
`(catalysisPsiTensorSpec) (i, j) = λ_ψ(i) · λ_c(j)`. Its multiset of values is
`{0.24, 0.24, 0.16, 0.16, 0.06, 0.06, 0.04, 0.04}`. -/
noncomputable def catalysisPsiTensorSpec : Fin 4 × Fin 2 → ℝ :=
  fun ij => catalysisPsiSpec ij.1 * catalysisCatSpec ij.2

/-- The spectrum of `|φ⟩|c⟩`: the outer product `λ_φ ⊗ λ_c` on the eight product outcomes,
`(catalysisPhiTensorSpec) (i, j) = λ_φ(i) · λ_c(j)`. Its multiset of values is
`{0.30, 0.20, 0.15, 0.15, 0.10, 0.10, 0, 0}`. -/
noncomputable def catalysisPhiTensorSpec : Fin 4 × Fin 2 → ℝ :=
  fun ij => catalysisPhiSpec ij.1 * catalysisCatSpec ij.2

/-! ### Non-convertibility: `λ_ψ` is not majorized by `λ_φ` -/

/-- **No LOCC conversion `|ψ⟩ → |φ⟩`** (majorization form): `λ_ψ = (0.4, 0.4, 0.1, 0.1)` is *not*
majorized by `λ_φ = (0.5, 0.25, 0.25, 0)`. Majorization would force the two largest entries of
`λ_ψ` to sum to at most the two largest of `λ_φ`, i.e. `0.8 ≤ 0.75`, which is false; witnessed by
the two-element subset `{0, 1}`. With Nielsen's theorem this is the impossibility of the direct
transformation in N&C Exercise 12.21. -/
theorem catalysisPsiSpec_not_majorize : ¬ Majorize catalysisPsiSpec catalysisPhiSpec := by
  rintro ⟨_, h⟩
  have hφanti : Antitone catalysisPhiSpec := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [catalysisPhiSpec] <;> norm_num
  have key := h ({0, 1} : Finset (Fin 4))
  have hcard : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  rw [hcard, largestKSum_eq_sum_prefix_of_antitone hφanti 2 (by norm_num)] at key
  norm_num [catalysisPsiSpec, catalysisPhiSpec, Finset.sum_filter, Fin.sum_univ_succ] at key

/-! ### Catalysis: `λ_ψ ⊗ λ_c` is majorized by `λ_φ ⊗ λ_c`

The proof reduces the product spectra on `Fin 4 × Fin 2` to explicitly sorted vectors on `Fin 8`
through reindexing equivalences (majorization is invariant under reindexing,
`largestKSum_comp_equiv` / `Equiv.sum_comp`), then checks the majorization on the sorted vectors by
the antitone prefix-sum formula `largestKSum_eq_sum_prefix_of_antitone`. -/

/-- `λ_ψ ⊗ λ_c`, its eight values sorted in decreasing order:
`(0.24, 0.24, 0.16, 0.16, 0.06, 0.06, 0.04, 0.04)`. -/
noncomputable def catalysisPsiTensorSorted : Fin 8 → ℝ :=
  ![6/25, 6/25, 4/25, 4/25, 3/50, 3/50, 1/25, 1/25]

/-- `λ_φ ⊗ λ_c`, its eight values sorted in decreasing order:
`(0.30, 0.20, 0.15, 0.15, 0.10, 0.10, 0, 0)`. -/
noncomputable def catalysisPhiTensorSorted : Fin 8 → ℝ :=
  ![3/10, 1/5, 3/20, 3/20, 1/10, 1/10, 0, 0]

/-- The reindexing of the eight product outcomes that sorts `λ_ψ ⊗ λ_c` into decreasing order:
`catalysisPsiTensorSpec ∘ catalysisPsiSortEquiv = catalysisPsiTensorSorted`. -/
noncomputable def catalysisPsiSortEquiv : Fin 8 ≃ Fin 4 × Fin 2 :=
  Equiv.ofBijective ![(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (3, 0), (2, 1), (3, 1)] (by decide)

/-- The reindexing of the eight product outcomes that sorts `λ_φ ⊗ λ_c` into decreasing order:
`catalysisPhiTensorSpec ∘ catalysisPhiSortEquiv = catalysisPhiTensorSorted`. -/
noncomputable def catalysisPhiSortEquiv : Fin 8 ≃ Fin 4 × Fin 2 :=
  Equiv.ofBijective ![(0, 0), (0, 1), (1, 0), (2, 0), (1, 1), (2, 1), (3, 0), (3, 1)] (by decide)

lemma catalysisPsiTensorSpec_comp_sortEquiv :
    catalysisPsiTensorSpec ∘ catalysisPsiSortEquiv = catalysisPsiTensorSorted := by
  funext k
  fin_cases k <;>
    simp [catalysisPsiTensorSpec, catalysisPsiTensorSorted, catalysisPsiSpec, catalysisCatSpec,
      catalysisPsiSortEquiv] <;> norm_num

lemma catalysisPhiTensorSpec_comp_sortEquiv :
    catalysisPhiTensorSpec ∘ catalysisPhiSortEquiv = catalysisPhiTensorSorted := by
  funext k
  fin_cases k <;>
    simp [catalysisPhiTensorSpec, catalysisPhiTensorSorted, catalysisPhiSpec, catalysisCatSpec,
      catalysisPhiSortEquiv] <;> norm_num

lemma catalysisPsiTensorSorted_antitone : Antitone catalysisPsiTensorSorted := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [catalysisPsiTensorSorted] <;> norm_num

lemma catalysisPhiTensorSorted_antitone : Antitone catalysisPhiTensorSorted := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [catalysisPhiTensorSorted] <;> norm_num

/-- The sorted spectrum of `|ψ⟩|c⟩` is majorized by that of `|φ⟩|c⟩`: for every `k`, the sum of the
`k` largest values of `λ_ψ ⊗ λ_c` is at most that of `λ_φ ⊗ λ_c`, and the totals agree (both `1`).
Checked prefix by prefix using the antitone prefix-sum formula. -/
lemma catalysisTensorSorted_majorize :
    Majorize catalysisPsiTensorSorted catalysisPhiTensorSorted := by
  rw [majorize_iff_forall_largestKSum]
  refine ⟨?_, fun k => ?_⟩
  · simp [catalysisPsiTensorSorted, catalysisPhiTensorSorted, Fin.sum_univ_eight]; norm_num
  by_cases hk : k ≤ 8
  · rw [largestKSum_eq_sum_prefix_of_antitone catalysisPsiTensorSorted_antitone k hk,
        largestKSum_eq_sum_prefix_of_antitone catalysisPhiTensorSorted_antitone k hk]
    interval_cases k <;>
      simp only [catalysisPsiTensorSorted, catalysisPhiTensorSorted, Finset.sum_filter,
        Fin.sum_univ_eight, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val] <;>
      norm_num
  · have hk' : Fintype.card (Fin 8) < k := by simpa using Nat.not_le.mp hk
    rw [largestKSum_eq_zero _ hk', largestKSum_eq_zero _ hk']

/-- **Catalysed LOCC conversion `|ψ⟩|c⟩ → |φ⟩|c⟩`** (majorization form): the product spectrum
`λ_ψ ⊗ λ_c` is majorized by `λ_φ ⊗ λ_c` on the eight product outcomes. Together with
`catalysisPsiSpec_not_majorize` and Nielsen's theorem, this is entanglement catalysis (N&C Exercise
12.21): the direct conversion is impossible, but tensoring both states with the catalyst `λ_c`
restores majorization, so the conversion becomes possible. Reduces to
`catalysisTensorSorted_majorize` by reindexing the product outcomes into sorted order. -/
theorem catalysisTensorSpec_majorize :
    Majorize catalysisPsiTensorSpec catalysisPhiTensorSpec := by
  have hsorted := catalysisTensorSorted_majorize
  rw [majorize_iff_forall_largestKSum] at hsorted ⊢
  obtain ⟨hs, hl⟩ := hsorted
  refine ⟨?_, fun k => ?_⟩
  · have e1 : ∑ i, catalysisPsiTensorSpec i = ∑ i, catalysisPsiTensorSorted i := by
      rw [← Equiv.sum_comp catalysisPsiSortEquiv catalysisPsiTensorSpec]
      exact Finset.sum_congr rfl fun i _ => congrFun catalysisPsiTensorSpec_comp_sortEquiv i
    have e2 : ∑ i, catalysisPhiTensorSpec i = ∑ i, catalysisPhiTensorSorted i := by
      rw [← Equiv.sum_comp catalysisPhiSortEquiv catalysisPhiTensorSpec]
      exact Finset.sum_congr rfl fun i _ => congrFun catalysisPhiTensorSpec_comp_sortEquiv i
    rw [e1, e2]; exact hs
  · rw [← largestKSum_comp_equiv catalysisPsiTensorSpec catalysisPsiSortEquiv k,
        ← largestKSum_comp_equiv catalysisPhiTensorSpec catalysisPhiSortEquiv k,
        catalysisPsiTensorSpec_comp_sortEquiv, catalysisPhiTensorSpec_comp_sortEquiv]
    exact hl k

end AxQM.Concrete
