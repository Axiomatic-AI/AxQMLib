/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.BlockDiagonalPeel
import AxQM.Concrete.TwoLevelColumnClear

/-!
# Concrete: every `d × d` unitary is a product of two-level unitaries (N&C §4.5.1 headline)

Nielsen & Chuang §4.5.1 (p. 189–191) proves that **an arbitrary `d × d` unitary matrix `U` can be
written as a product of two-level unitaries** — the structural fact that reduces universality to the
single-qubit + `CNOT` case. This file assembles that result from the lemmas
proved in the files it imports, by an induction on the dimension.

## The induction (N&C eqs. 4.44–4.51)

The statement is `exists_twoLevelUnitaryList_prod_eq`: for every unitary `U` there is a list `L` of
two-level unitaries with `L.prod = U`. Induction on `d`:

* **`d = 0`.** `Matrix (Fin 0) (Fin 0) ℂ` is a subsingleton, so `U = 1 = [].prod`; the empty list
  works.
* **`d + 1`.** Three steps, each already available:
  1. **Column-clear** (`exists_twoLevelUnitaryList_clear_first_column`): a list `L₀` of two-level
     unitaries with `W := L₀.prod * U` having its first column a multiple of `e₀`. `L₀.prod` is
     unitary (a product of unitaries, `list_prod_mem`), hence so is `W`.
  2. **Block-diagonal peel** (`exists_phaseShift_mul_blockOne_of_clearFirstColumn`): unitarity turns
     the cleared first column into `W = phaseShift c * blockOne C` with `|c| = 1` and `C` a `d × d`
     unitary corner.
  3. **Recurse** on `C`: the induction hypothesis gives `C = M.prod` for a two-level list `M`. Since
     `blockOne` is a homomorphism (`prod_map_blockOne`), `blockOne C = (M.map blockOne).prod`, each
     factor two-level (`isTwoLevelUnitary_blockOne`); with `phaseShift c` two-level
     (`isTwoLevelUnitary_phaseShift`) this exhibits `W` as a product of two-level unitaries.

  Finally `U = (L₀.prod)ᴴ * W`: prepending the *reversed conjugate transposes* of `L₀` —
  `(L₀.map conjTranspose).reverse`, whose product is `(L₀.prod)ᴴ` by
  `Matrix.conjTranspose_list_prod` and each of whose entries `Wᴴ` is again a two-level unitary
  (`IsTwoLevelUnitary.conjTranspose`) —
  cancels `L₀.prod` (`(L₀.prod)ᴴ * L₀.prod = 1`, unitarity), leaving `U`. No matrix inverse is
  needed: the conjugate transpose *is* the inverse of a unitary, and it is again two-level, so the
  whole assembled list stays inside the two-level class.

Two small reusable lemmas support the assembly:

* `IsTwoLevelUnitary.conjTranspose` — the conjugate transpose of a two-level unitary is a two-level
  unitary (same distinguished pair `{p, q}`).
* `prod_map_blockOne` — `blockOne` carries a list product to the product of the embedded factors,
  `(L.map blockOne).prod = blockOne L.prod` (the list form of the `blockOne_one`/`blockOne_mul`
  homomorphism laws).

## Use

This is the shared §4.5.1 result used across the two-level items (Ex 4.37/4.38 and
Exercise 4.43's `n`-qubit lift); the statement of Exercise 4.43 is in
`AxQM/NC/Ch4/Exercise4_43.lean`.

## Not formalised here

This completes N&C §4.5.1. The remaining Exercise 4.43 work is the **`n`-qubit lift**: each
two-level unitary is realised by `CNOT` + single-qubit gates (Exercise 4.39), the single-qubit gates
are approximable by the reachable set (`exists_phase_smul_mem_closure_reachableRotations`, already
in the library), and together with `CNOT` this gives universality on any number of qubits. The
top-level `n`-qubit universality statement — the item's headline theorem — is not formalised here.
-/

namespace AxQM.Concrete

open Matrix

variable {d : ℕ}

/-- **The conjugate transpose of a two-level unitary is a two-level unitary**, with the same
distinguished pair `{p, q}`. Unitarity of `Uᴴ` is closure of the unitary group under `ᴴ`; the
off-`{p,q}` entries of `Uᴴ` are the conjugated off-`{p,q}` entries of `U` (with `(i,j)` reading
`U`'s `(j,i)`), which agree with the (real, symmetric) identity. Used to invert the column-clearing
factors while staying inside the two-level class. -/
theorem IsTwoLevelUnitary.conjTranspose {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : IsTwoLevelUnitary U) : IsTwoLevelUnitary Uᴴ := by
  obtain ⟨hunit, p, q, hpq⟩ := hU
  refine ⟨?_, p, q, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hunit
  · intro i j h
    rw [Matrix.conjTranspose_apply, hpq j i h.symm, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : j = i
    · subst hij; simp
    · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), star_zero]

/-- **`blockOne` carries a list product to the product of the embedded factors**:
`(L.map blockOne).prod = blockOne L.prod`. The list form of the `blockOne_one`/`blockOne_mul`
homomorphism laws, letting the inductive step embed the corner's decomposition
`C = M.prod` as `blockOne C = (M.map blockOne).prod`. -/
theorem prod_map_blockOne (M : List (Matrix (Fin d) (Fin d) ℂ)) :
    (M.map blockOne).prod = blockOne M.prod := by
  induction M with
  | nil => simp [blockOne_one]
  | cons a M ih => simp only [List.map_cons, List.prod_cons, ih, blockOne_mul]

/-- **Every `d × d` unitary is a product of two-level unitaries (Nielsen & Chuang §4.5.1).** For any
`U ∈ U(d)` there is a list `L` of two-level unitaries with `L.prod = U`. Proved by induction on `d`:
column-clearing (`exists_twoLevelUnitaryList_clear_first_column`) then the block-diagonal peel
(`exists_phaseShift_mul_blockOne_of_clearFirstColumn`) reduces `U` to a `phaseShift` factor times a
`blockOne` of a `d × d` corner unitary, whose decomposition the induction hypothesis supplies; the
column-clearing factors are undone by their conjugate transposes (`IsTwoLevelUnitary.conjTranspose`,
`Matrix.conjTranspose_list_prod`), which are themselves two-level. This is the structural input to
the §4.5.2 reduction of universality to single-qubit gates and `CNOT`. -/
theorem exists_twoLevelUnitaryList_prod_eq {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ L : List (Matrix (Fin d) (Fin d) ℂ),
      (∀ V ∈ L, IsTwoLevelUnitary V) ∧ L.prod = U := by
  induction d with
  | zero => exact ⟨[], by simp, by ext i; exact i.elim0⟩
  | succ d ih =>
    obtain ⟨L₀, hL₀, hcol⟩ := exists_twoLevelUnitaryList_clear_first_column U
    have hL₀prod : L₀.prod ∈ Matrix.unitaryGroup (Fin (d + 1)) ℂ :=
      list_prod_mem (fun M hM => (hL₀ M hM).1)
    have hWunit : (L₀.prod * U) ∈ Matrix.unitaryGroup (Fin (d + 1)) ℂ := mul_mem hL₀prod hU
    obtain ⟨c, C, hc, hCunit, hWeq⟩ :=
      exists_phaseShift_mul_blockOne_of_clearFirstColumn hWunit hcol
    obtain ⟨M, hM, hMprod⟩ := ih C hCunit
    refine ⟨(L₀.map Matrix.conjTranspose).reverse ++ (phaseShift c :: M.map blockOne), ?_, ?_⟩
    · -- every factor is a two-level unitary
      intro V hV
      rcases List.mem_append.mp hV with hV | hV
      · -- the undoing factors `Wᴴ` for `W ∈ L₀`
        rw [List.mem_reverse, List.mem_map] at hV
        obtain ⟨W, hWL₀, rfl⟩ := hV
        exact (hL₀ W hWL₀).conjTranspose
      · rcases List.mem_cons.mp hV with hV | hV
        · exact hV ▸ isTwoLevelUnitary_phaseShift hc
        · -- the embedded corner factors `blockOne N` for `N ∈ M`
          rw [List.mem_map] at hV
          obtain ⟨N, hNM, rfl⟩ := hV
          exact isTwoLevelUnitary_blockOne (hM N hNM)
    · -- the product telescopes to `U`
      rw [List.prod_append, ← Matrix.conjTranspose_list_prod, List.prod_cons, prod_map_blockOne,
        hMprod, ← hWeq, ← Matrix.mul_assoc]
      have h1 : (L₀.prod)ᴴ * L₀.prod = 1 := by
        rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hL₀prod
      rw [h1, Matrix.one_mul]

end AxQM.Concrete
